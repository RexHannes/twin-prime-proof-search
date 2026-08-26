/-
# Gate 1B safe algebra bank — §12: what deliberately remains UNFORMALIZED.

This file contains **no declarations at all**: no `def`, no `theorem`, no
`axiom`, no `Prop` that could later be inhabited by accident.  Each item below
is an *external analytic or source obligation*.  Nothing in the `Gate1B`
namespace asserts, assumes, or implies any of them, and none of them may be
used as a hypothesis of a Gate1B theorem without being written out in full at
the point of use.

* `MAM45` — external analytic obligation.  Mixed all-moment 4–5 input.  Not
  formalized, not assumed, not implied by the character-saturation theorems of
  `Gate1B/CharacterSaturation.lean`: those are tautologies at every tensor
  power and produce no moment bound.

* `SIGNED_C45` — external analytic obligation.  Any *signed* (cancellation)
  statement about the C45 defect over a family.  Only the exact divisibility
  algebra of `Gate1B/C45.lean` is banked; no cancellation is claimed.

* `ASPE45` — external analytic obligation.  Averaged shifted-phase estimate.
  Not formalized.

* `PSC45` — external analytic obligation.  Prime-square collision *counting*
  over a family.  `Gate1B/PrimeSquareLift.lean` and `Gate1B/CRTProduct.lean`
  give the pointwise equivalences only; no count over `q`, `ℓ`, `v` or over the
  primes is asserted.

* `ADDITIVE_PSQ_C45` — external analytic obligation.  Any statement that the
  additive coordinate of `Gate1B/AdditiveCoordinate.lean` equidistributes, or
  that summing over it saves.  The banked material is the exact coordinate
  identity `R ∣ D ↔ q₁ − 2ℓ₁⁻¹ ≡ q₂ − 2ℓ₂⁻¹ (mod R)` and nothing more.

* `ZHAO_SQUARE_MODULUS_LARGE_SIEVE` — external analytic input.  Not
  formalized, not assumed anywhere in this library.

* `E(q)` — external source object (the per-modulus error term).  Undefined
  here.

* `Z_E(q)` — external source object (the zero-mode / expected term attached to
  `E(q)`).  Undefined here.  No main-term formula is supplied.

* `KAPPA4` — external analytic obligation (fourth-moment constant).  Not
  formalized.

* `FIXED_SWITCHED_REASSEMBLY` — external assembly obligation.  Not formalized.

Additional standing prohibitions recorded for later research, all of which are
*not* consequences of anything in this library:

* `PSQ-SYNC45 PASS` is **not** banked.  The exact mistake it rested on — the
  replacement of an on-shell relation by the Cartesian product of its
  projections — is refuted by `Gate1B.shell_sum_ne_cartesian_sum`.
* No independence between the four local prime-square conditions may be
  inferred from the CRT factorisation; see
  `Gate1B.local_conditions_not_independent`.
* Gate 1B closure is **not** claimed, formalized, or implied.
-/
