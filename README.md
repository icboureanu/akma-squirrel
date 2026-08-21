# Computational Privacy Proofs of 5G AKMA in Squirrel

This repository contains [Squirrel](https://squirrel-prover.github.io/) proof
scripts that analyse the privacy of the 5G **AKMA** (Authentication and Key
Management for Applications) protocol in the **computational** model.

The work ports the symbolic (Dolev–Yao / Tamarin) privacy analysis of AKMA by
Boureanu et al. (*A Systematic Study of Practical & Formal Privacy in the 5G
AKMA Procedure*, IEEE EuroS&P 2025, DOI
[10.1109/EuroSP63326.2025.00010](https://doi.org/10.1109/EuroSP63326.2025.00010))
into Squirrel, which reasons in the computational model on top of the
Computationally-Complete Symbolic Attacker (CCSA) logic of Bana and Comon.

Two things are done here:

1. **Disprove** privacy on unpatched AKMA — an active attacker can desynchronise
   an honest UE and AF and, in doing so, link a specific UE (via its AKID) to a
   specific AF.
2. **Prove** privacy of a patched AKMA — the success/failure indication in the
   last protocol step is encrypted under a UE-only key and forwarded opaquely by
   the AF, so an attacker cannot distinguish success from failure.

---

## Files

| File | Purpose | Proof style | Status |
|------|---------|-------------|--------|
| `AKMA.sp` | Model of **unpatched** AKMA; disproves privacy via a reachability/linkability witness. | Reachability (built-in tactics) | **Closes fully — 0 admits** |
| `AKMA_private.sp` | Model of the **patched** AKMA; single-session privacy of the last-step reply. | Equivalence via a user-defined `crypto` game | Closes **up to 2 explicit `admit`s** |
| `AKMA_private_replication.sp` | Same patched privacy property, **replicated** over unboundedly many subscribers/AFs. | Equivalence via a user-defined `crypto` game | Closes **up to 1 explicit `admit`** |

All three files begin with `include Core.` and were developed and checked
against a Squirrel binary **built from source at commit `1ce3981` (June 2026)**.

---

## Requirements

- A Squirrel binary built from source at commit `1ce3981` (June 2026) or a
  nearby revision. The scripts use current syntax; in particular they rely on:
  - `mutex` declarations and `lock`/`unlock` for shared mutable state;
  - `set postQuantumEquivs=true.` (the modern replacement for the removed
    `PostQuantumSound` option) in the equivalence files;
  - user-defined `game { ... }` blocks and the `crypto` tactic.
- The standard `Core` library that ships with Squirrel (`include Core.`).

> **Note on building Squirrel.** In our environment Squirrel was built from
> source with the inline-test PPX dependencies stripped for OCaml 4
> compatibility. Consult the upstream Squirrel build instructions for your
> platform.

---

## Running the proofs

From the repository root, check each file with your Squirrel binary, e.g.:

```sh
squirrel AKMA.sp
squirrel AKMA_private.sp
squirrel AKMA_private_replication.sp
```

- `AKMA.sp` should report all lemmas proved with **no** admits.
- `AKMA_private.sp` and `AKMA_private_replication.sp` complete **modulo the
  explicit `admit`s** documented below; Squirrel will report the admitted goals.

Timeouts are set per file (`set timeout = 12.` in `AKMA.sp`, `= 30.` in the two
privacy files); increase them if your machine is slower.

---

## What each file models and proves

### `AKMA.sp` — disproving privacy (linkability via desynchronisation)

**Model.** Four roles — registration on the core and UE side (`Core_initial`,
`UE_initial`), the UE and AF running the AKMA key phase (`UE_KAF`, `AF`), and the
core issuing `K_AF` or an error (`Core_KAF`). The `Ua*` channel (UE↔AF) is
modelled as **insecure**; the registration and core↔AF channels are secure. The
last-step indication is abstracted to constants `ok`/`ko` (with axiom
`ok_not_ko`). An explicit `desync_attacker` process outputs `ko` on the same
`Ua*` channel the UE reads its final message from, making the attacker's
capability visible and trackable in proofs.

**Lemmas.**
- `reachability_init` — weak agreement for Registration (proved by `intctxt` on
  the UE↔core shared key).
- `kaf_reachability` — weak agreement between the AF and the core over the
  `K_AF` request (proved by `intctxt` on `AF_key`).
- `if_ok_then_ok` — helper: if the AF's last input is the core's success
  response, the AF takes the OK branch (proved from `dec(enc)=plaintext`).
- `desynchronisation` — an honest UE and AF that ran together can diverge (AF
  sends `ok`, UE's final input is `ko`), because the attacker injected `ko`.
- `explicit_linkability` — **the privacy attack**: in one run the AF succeeds,
  the attacker has read the UE's `<AKID, AF_ID>` on the insecure `Ua*` (formally
  `input@af(af_id) = att(frame@pred(af(af_id)))`, i.e. the attacker links this
  UE to this AF), and the UE is nonetheless desynchronised (`ko`).

**Assumptions used.** Only integrity of ciphertexts (`intctxt`) and the
encryption-correctness equation `dec(enc(x,y,k),k)=x` (`dec_enc_ok`). No unsound
axioms.

### `AKMA_private.sp` — single-session privacy of the patched reply

**Patch modelled.** The core encrypts the last-step indication under a UE-only
key (`ue_key(SUPI)`); the AF forwards the inner ciphertext transparently on the
insecure `Ua*` and cannot tell success from failure.

**Game.** A user-defined game `myIndistinguish` states that a randomised
encryption of a fixed message or a chosen message is indistinguishable to an
attacker who does not hold the key. The `diff` lives **inside the core's reply**:

```
encI (diff(kaf, ko)) r' (ue_key(supi1))
```

LEFT = real `K_AF` (success), RIGHT = error `ko` (failure).

**Lemma.** `anonymity` — `equiv(frame@af_five)`, proved by
`crypto myIndistinguish`. Five residual scheduling side-conditions are
discharged by honest, single-session, non-interleaving `flow_*` facts. **Two**
residual goals remain as explicit `admit`s (see below).

### `AKMA_private_replication.sp` — replicated (multi-session) privacy

Same patch and property, but the system is replicated `!_isupi !_jaf` over
unboundedly many subscribers and AFs. The game draws the unknown key **directly**
(`rnd k : message`, with `ue_key` declared a `name`), following the upstream
`examples/crypto-usenix-26/kdf.sp` idiom. This collapses the whole multi-session
bi-deduction to a **single** residual scheduling goal, left as one explicit
`admit`.

---

## Repository layout

```
.
├── AKMA.sp                        # unpatched AKMA: disproves privacy (0 admits)
├── AKMA_private.sp                # patched AKMA: single-session privacy (2 admits)
├── AKMA_private_replication.sp    # patched AKMA: multi-session privacy (1 admit)
└── README.md
```

---

## Citing / related work

- I. Boureanu, S. Wesemeyer, F. Rajaona, S. Schneider, H. Treharne.
  *A Systematic Study of Practical & Formal Privacy in the 5G AKMA Procedure.*
  IEEE EuroS&P 2025. DOI: 10.1109/EuroSP63326.2025.00010 — the symbolic
  (Tamarin) analysis these files port to the computational model.
- D. Baelde, S. Delaune, C. Jacomme, A. Koutsos, J. Lallemand.
  *The Squirrel Prover and its Logic.* ACM SIGLOG News 11(2), 2024.
- D. Baelde, A. Koutsos, J. Sauvage.
  *Foundations for Cryptographic Reductions in CCSA Logics.* CCS 2024 — the
  `crypto` / user-defined game mechanism.
- 3GPP TS 33.535 — the AKMA specification.

---

## License

No license is set yet. Add one (e.g. MIT, Apache-2.0, or CC-BY-4.0 for the proof
scripts and documentation) before publishing.
