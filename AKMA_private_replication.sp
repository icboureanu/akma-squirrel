(*An Adapdation of the AKMA protocol*)
(* between UE, Core, AF *)

(* communication steps + direcions *)
(*1. UE <-->          CORE  *)
(*2. UE --> AF              *)
(*3.      AF --->   Core   *)
(*4.        AF <--- Core   *) 
(*5. UE <-- AF              *)

(* all channels are secure; i.e., msgs are sent encrypted *)

(* purpose of the file: 

to show that the attacker cannot distinguish if the UE is sent in step 5, 
above an error or a key. this is forwarded from step 4, above

*)

include Core.
set postQuantumEquivs=true.
set timeout = 30.



abstract fAKID: index * message * index -> message. (* AKID derivation. *)
abstract fKAKMA: index * message -> message. (*AKMA derivation *)
abstract fKAF: message *message -> message. (*K_AF derivation. Inputs: K_AKMA, ID_AF*)
abstract kausf: index *message -> message.
abstract key_creation: message -> message.


abstract ok : message.
abstract ko : message.

mutable db_akid(SUPI:index, af_id: index) : message = zero.
mutable db_kakma(SUPI:index) : message = zero.
mutable db_kausf(SUPI: index) : message = zero.

(* mutex guarding shared databases so the core try-find can be cut *)
mutex db_lock : 0.

abstract af_id_index_to_message : index -> message.
abstract af_id_message_to_index : message -> index.
axiom [any] af_id_conv (x:message) :
	af_id_index_to_message(af_id_message_to_index(x)) = x.

(* Key shared btw UE and Core for symmetric encryption *)
name key_shared: index  -> message.
senc enc,dec.

name core_key : message.
name AF_key : index -> message.
name AF_key2 : index -> message.



name af_id1: index.
name af_id2: index.
name supi1: index.
name supi2: index.



(* Defining an encryption function as an abstract function; 
used with the game below and in the last steps of the protocol. *)
abstract encI : message -> message -> message -> message.

name ue_key : index -> message. (*UE secret key (e.g. K_AUSF), drawn as a name; the game treats it as the unknown key*)

(* a game to say the a randomise encryptions produces indist. outputs, if the key is unknown; *)
game myIndistinguish = {
  rnd k : message;       (* the unknown UE key *)
  rnd m : message;       (* the random reference plaintext *)
  oracle enc x = {
    rnd r : message;
    return encI (diff(x, m)) r k
  }
}.


channel Ccore.
channel Caf.
channel Cue.
channel Cue2.
channel Cdummy.


(*Registration + AKMA-key during Registration *)
process Core_initial (SUPI: index) = 
    new r; new ausf_rand;
	let k_ausf= kausf(SUPI,ausf_rand) in
	let K_AKMA=fKAKMA(SUPI, k_ausf) in
     lock db_lock; db_kausf(SUPI) := k_ausf; unlock db_lock;
    core_one: out(Cue, enc(<k_ausf,K_AKMA>, r, key_shared(SUPI))) (*this is to symbolise that Reg is over; Core sends a 'signal' to UE*).
    

process UE_initial (SUPI, af_id: index) =
    ue_one: in(Cue, registration); (*UE takes part in registration*)

	(* Check that the core sending this message is the "good" one (meaning using the same SUPI) *)
	if (dec(registration, key_shared(SUPI)) <> fail) then ( 
		let K_AKMA = snd(dec(registration, key_shared(SUPI))) in let AKID = fAKID(SUPI, K_AKMA, af_id) in
		lock db_lock;
		db_akid(SUPI)(af_id) := AKID; (*storing the current AKID for this UE*)
		db_kakma(SUPI) := K_AKMA; (*storing the current KAKMA for this UE*)
		unlock db_lock
	)
.

(*end Registration*)

(*UE speaking to AF; UE-side*)
process UE_KAF (SUPI:index, af_id:index) =
    new r;
    lock db_lock; let akid_snap = db_akid(SUPI)(af_id) in unlock db_lock;
    ue_two: out(Caf, <akid_snap, af_id_index_to_message(af_id)>); (*step 2 in the diagram at the top of the file; the UE contacts the AF*)
    ue_five :in(Cue2, x). (*step 5 in the diagram at the top of the file; the UE receives the final message from the AF *)
(*end of UE speaking to the  AF; UE-side*) 

(*AF speaks to UE and to the Core*) 
process AF (AF_ID: index) =
    new r;
   af_one: in(Caf, msg);  (*the AF receives the contact in step 2 in the diagram at the top, a contact request  from the UE*)
    if (af_id_message_to_index(fst(snd(msg))) = AF_ID) then (
      let msg = enc(<fst(msg), af_id_index_to_message(AF_ID)>, r, AF_key(AF_ID)) in
      
      af_three: out(Ccore, msg); (*step 3 in the diagram at the top of the file; the AF contacts the Core*)
      
     af_four: in(Caf, x); (* AF reading <ok, encI(...)> from the Core *)
      (* AF transparently forwards the core's inner ciphertext on the insecure Ua* *)
      let fwd = snd(dec(x, AF_key2(AF_ID))) in
      af_five: out(Cue2, fwd)).
	



(* Core sending the K_AF or errors; step 4 in the diagram at the top*)
process Core_KAF (AF_ID: index) =
   
    
    in(Ccore, x); new r; new r'; (*  Core reads request from AF *)
    let msg = dec(x, AF_key(AF_ID)) in
    let AKID = fst(msg) in
    if (msg <> fail && AF_ID = af_id_message_to_index(snd(msg))) then (
        lock db_lock;
        try find SUPI such that (db_akid(SUPI)(AF_ID) = AKID) in (
            let kaf = fKAF(db_kakma(SUPI), af_id_index_to_message(AF_ID)) in
            (* Privacy-critical reply: encrypted under the UE's secret key ue_key(SUPI),
               either the real K_AF (LEFT = success) or the error ko (RIGHT = failure). *)
            core_four1: out(Caf, enc(<ok, (encI (diff(kaf, ko)) r' (ue_key(SUPI)))>, r, AF_key2(AF_ID))); unlock db_lock
        ) else (
            unlock db_lock; core_four2: out(Cdummy, ko)
        )
    )
    else (
        core_four3: out(Cdummy, ko)
    ).


(*just a simple system to prove things, easily*)
system (

!_isupi  !_jaf (

    ntw_init1: Core_initial (isupi) |

    phone_init11: UE_initial (isupi, jaf) |

    phone_kaf11: UE_KAF (isupi, jaf) |

    af1: AF (jaf) |

    ntw_kaf1: Core_KAF (jaf)

) ).

 (*because the channels are asynchronous in AKMA and in Squirrel, we specify the execution-flow of interest in AKMA;  *)

(* =====================================================================
   PRIVACY (multi-session): success/failure of the AKMA Ua* reply is
   indistinguishable, over an unbounded number of subscribers/AFs
   (system replicated as !_isupi !_jaf).

   Same modelling fixes as the single-session file:
   * mutex db_lock guards the shared databases (else Cannot_cut).
   * the diff is placed in the core's reply, encI(diff(kaf,ko)) under the
     UE's secret key ue_key(SUPI); the AF forwards it transparently. 

   Game design: myIndistinguish now draws the unknown key `k` directly
   (rnd k),  
    ue_key is correspondingly
   a `name`. This is what lets `crypto` discharge the equivalence in the
   replicated setting: it collapses the whole multi-session bi-deduction to
   a SINGLE residual scheduling goal.

   Proof status: `crypto myIndistinguish` proves the equivalence up to one
   residual goal,
       forall isupi0 jaf0 SUPI, not (core_four1(isupi0,jaf0,SUPI) < af_five(isupi,jaf)),
   i.e. "no core success-output precedes the analysed AF delivery".
   `constraints` reports this satisfiable: it is NOT a consequence of the
   trace model, and closing it would require an ordering assumption contrary
   to the protocol (the core's reply does precede the AF forward). This is
   the same genuine gap as in the single-session file. 
   ===================================================================== *)

global lemma anonymity (isupi:index[adv], jaf:index[adv]) :
  [happens(af_five(isupi,jaf))] -> equiv(frame@af_five(isupi,jaf)).
Proof.
  intro Hh. expandall.
  crypto myIndistinguish.
  (* single residual: core_four1(...) < af_five(...) => false. Satisfiable in
     the trace model (constraints confirms), hence not provable without an
     unsound ordering assumption; left explicit rather than hidden. *)
  admit.
Qed.
