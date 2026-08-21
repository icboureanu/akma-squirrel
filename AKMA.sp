(* AKMA -- disproving privacy (linkability via desynchronisation).
   Ported to current  Squirrel (commit 1ce3981, June 2026).


   * A `mutex db_lock` guards the shared AKID/KAKMA databases. The current
     process semantics reject a `try find` over mutable state that another
     parallel process writes concurrently (exception Cannot_cut). Locking the
     state, inspired by  examples/stateful/yubikey.sp does, removes the
     read/write conflict. 

     As a side effect the core's AKMA action is split into
     ntw_kaf (request + guard), ntw_kaf1 (find-success), ntw_kaf2 (find-fail),
     ntw_kaf3 (outer else); 

   *  The only
     cryptographic assumptions used are int-ctxt of the symmetric encryption
     (built-in `intctxt`) and the standard correctness equation dec(enc)=plain. *)

include Core.
set timeout = 12.

(* key-derivation functions *)
abstract fAKID  : index * message -> message. (* AKID derivation *)
abstract fKAKMA : index * message -> message. (* K_AKMA derivation *)
hash fKAF.                                     (* K_AF derivation *)
abstract kausf  : index * message -> message.
abstract key_creation : message -> message.

(* error / success codes for the last protocol step *)
abstract ok : message.
abstract ko : message.
axiom [any] ok_not_ko : ok <> ko.

(* per-SUPI databases for AKIDs and K_AKMA, rewritten on every Registration *)
mutable db_akid (SUPI:index) : message = zero.
mutable db_kakma(SUPI:index) : message = zero.

(* mutex protecting the shared databases (required so that the core's
   try-find over db_akid can be cut despite concurrent registration writes). *)
mutex db_lock : 0.

(* type-conversion functors between AF identifiers as indices vs. messages *)
abstract af_id_index_to_message : index -> message.
abstract af_id_message_to_index : message -> index.
abstract supi_index_to_message  : index -> message.
axiom [any] af_id_conv (x:message) :
  af_id_index_to_message(af_id_message_to_index(x)) = x.

(* symmetric keys + encryption *)
name key_shared : index -> message.   (* UE <-> Core, e.g. K_AMF *)
senc enc,dec.

(* correctness equation of symmetric encryption (distinct from its security,
   which is captured by senc + intctxt). *)
axiom [any] dec_enc_ok (x,y,k:message) : dec(enc(x,y,k),k) = x.
name core_key : message.
name AF_key   : index -> message.      (* AF <-> Core, request leg *)
name AF_key2  : index -> message.      (* AF <-> Core, response leg *)

(* channels *)
channel Cregistr.
channel Cone.    (* insecure Ua*: UE -> AF *)
channel Ctwo.    (* secure: AF -> Core *)
channel Csix.    (* secure: Core -> AF *)
channel Cseven.  (* insecure Ua*: AF -> UE (attacker-injectable) *)
channel Cdummy.

(* ---------- Registration ---------- *)
process Core_initial (SUPI:index) =
  new r; new ausf_rand;
  let k_ausf = kausf(SUPI,ausf_rand) in
  let K_AKMA = fKAKMA(SUPI,k_ausf) in
  out(Cregistr, enc(<k_ausf,K_AKMA>, r, key_shared(SUPI))).

process UE_initial (SUPI:index) =
  in(Cregistr, registration);
  if (dec(registration, key_shared(SUPI)) <> fail) then (
    let K_AKMA = snd(dec(registration, key_shared(SUPI))) in
    let AKID = fAKID(SUPI, K_AKMA) in
    lock db_lock;
    db_akid(SUPI)  := AKID;
    db_kakma(SUPI) := K_AKMA;
    unlock db_lock
  ).

(* ---------- AKMA: UE side ---------- *)
process UE_KAF (SUPI:index, af_id:index) =
  lock db_lock;
  let akid_snapshot = db_akid(SUPI) in
  unlock db_lock;
  ue_one  : out(Cone, <akid_snapshot, af_id_index_to_message(af_id)>);
  ue_seven: in(Cseven, x).

(* ---------- AKMA: AF side ---------- *)
process AF (AF_ID:index) =
  new r;
  in(Cone, msg);
  if (af_id_message_to_index(snd(msg)) = AF_ID) then (
    let msg2 = enc(<fst(msg), af_id_index_to_message(AF_ID)>, r, AF_key(AF_ID)) in
    af_two: out(Ctwo, msg2);
    in(Csix, x);
    if (fst(dec(x, AF_key2(AF_ID))) = ok) then (
      let K_AF = snd(dec(x, AF_key2(AF_ID))) in
      af_seven_ok: out(Cseven, ok)
    ) else (
      af_seven_ko: out(Cseven, ko)
    )
  ).

(* ---------- AKMA: Core side (K_AF generation) ---------- *)
process Core_KAF (AF_ID:index) =
  in(Ctwo, x);
  new r;
  let msg  = dec(x, AF_key(AF_ID)) in
  let AKID = fst(msg) in
  if (msg <> fail && AF_ID = af_id_message_to_index(snd(msg))) then (
    lock db_lock;
    try find SUPI such that (db_akid(SUPI) = AKID) in (
      out(Csix, enc(<ok, fKAF(db_kakma(SUPI), af_id_index_to_message(AF_ID))>, r, AF_key2(AF_ID)));
      unlock db_lock
    ) else (
      out(Csix, enc(<ko,ko>, r, AF_key2(AF_ID)));
      unlock db_lock
    )
  ) else (
    out(Cdummy, ko)
  ).

(* The active "desynchronisation" attacker: it can output ko on the insecure
   Ua* channel that the UE reads its last message from. *)
process desync_attacker (j:index) =
  out(Cseven, ko).

system akma_desync = (
  !_j desync_attacker(j) |
  !_supi (
    phone_init : UE_initial(supi)   |
    ntw_init   : Core_initial(supi) |
    !_af_id (phone_kaf : UE_KAF(supi, af_id))
  ) |
  !_af_id (
    ntw_kaf : Core_KAF(af_id) |
    af      : AF(af_id)
  )
).

(* ===================================================================== *)
(*  1. Weak agreement for Registration: whenever the phone finishes      *)
(*     Registration with a message that decrypts, that message was       *)
(*     produced by the core. Proved by int-ctxt on key_shared.           *)
(* ===================================================================== *)
lemma [akma_desync] reachability_init (supi:index) :
  happens(phone_init(supi)) =>
  (dec(input@phone_init(supi), key_shared(supi)) <> fail) =>
  exists (ntw_supi:index),
    ntw_init(ntw_supi) < phone_init(supi) &&
    output@ntw_init(ntw_supi) = input@phone_init(supi).
Proof.
  intro Hap Hdec.
  intctxt Hdec.
  intro [H1 H2].
  exists supi.
  split; auto.
Qed.

(* ===================================================================== *)
(*  2. Weak agreement for K_AF: whenever the core's request action        *)
(*     ntw_kaf has its guard satisfied (a well-formed request for this    *)
(*     AF), some AF actually emitted exactly that request earlier.        *)
(*     Proved by int-ctxt on AF_key                                 *)
(* ===================================================================== *)
lemma [akma_desync] kaf_reachability (af_id:index) :
  happens(ntw_kaf(af_id)) && cond@ntw_kaf(af_id)
  =>
  exists (af_id2:index),
    af_two(af_id2) < ntw_kaf(af_id) &&
    output@af_two(af_id2) = input@ntw_kaf(af_id).
Proof.
  intro [Hap Hcond].
  expand cond.
  destruct Hcond as [Hneq Hidx].
  intctxt Hneq.
  intro H. by exists af_id.
Qed.

(* ===================================================================== *)
(*  3. Helper: if the AF's last input is the core's success response      *)
(*     (output of ntw_kaf1), then the AF takes the OK branch.             *)
(*     Proved from dec(enc)=plaintext. *)
(* ===================================================================== *)
lemma [akma_desync] if_ok_then_ok (af_id, supi:index) :
  happens(af_seven_ok(af_id)) &&
  happens(ntw_kaf1(af_id, supi)) &&
  input@af_seven_ok(af_id) = output@ntw_kaf1(af_id, supi)
  =>
  cond@af_seven_ok(af_id).
Proof.
  intro [Hok [Hntw Heq]].
  expand cond.
  rewrite Heq. expand output.
  rewrite dec_enc_ok. simpl. auto.
Qed.

(* ===================================================================== *)
(*  4. Desynchronisation: an honest UE and AF that ran AKMA together can  *)
(*     diverge -- the AF sends OK while the UE's final input is ko,       *)
(*     because the active attacker injected ko on the Ua* channel.        *)
(*     *)
(* ===================================================================== *)
lemma [akma_desync] desynchronisation (supi, af_id, j:index) :
  happens(ue_seven(supi, af_id)) &&
  happens(af_seven_ok(af_id)) &&
  happens(desync_attacker(j)) &&
  input@ue_seven(supi, af_id) = output@desync_attacker(j)
  =>
  input@ue_seven(supi, af_id) = ko.
Proof.
  intro [Hue [Hok [Hj Heq]]].
  rewrite Heq. expand output. auto.
Qed.

(* ===================================================================== *)
(*  5. Explicit linkability (the privacy attack): in one run,            *)
(*     (1) the AF succeeds (sends OK),                                    *)
(*     (2) the attacker has read the UE's <AKID, AF_ID> message on the    *)
(*         insecure Ua* channel, i.e. links THIS UE to THIS AF, and       *)
(*     (3) the UE is nonetheless desynchronised: its final input is ko.   *)
(*                  *)
(* ===================================================================== *)
lemma [akma_desync] explicit_linkability (supi, af_id, supi2, j:index) :
  happens(ue_seven(supi, af_id)) &&
  happens(af(af_id)) &&
  happens(af_seven_ok(af_id)) &&
  happens(ntw_kaf1(af_id, supi2)) &&
  input@af_seven_ok(af_id) = output@ntw_kaf1(af_id, supi2) &&
  happens(desync_attacker(j)) &&
  input@ue_seven(supi, af_id) = output@desync_attacker(j)
  =>
  cond@af_seven_ok(af_id) &&
  input@af(af_id) = att(frame@pred(af(af_id))) &&
  input@ue_seven(supi, af_id) = ko.
Proof.
  intro [Hue [Haf [Hok [Hntw [Heq [Hj Hinj]]]]]].
  split.
  + by apply if_ok_then_ok af_id supi2.
  + split.
    - expand input. auto.
    - rewrite Hinj. expand output. auto.
Qed.
