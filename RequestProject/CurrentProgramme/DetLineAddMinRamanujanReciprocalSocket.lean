import Mathlib
import RequestProject.CurrentProgramme.AddMinRamanujanReciprocity

/-!
# Gate 1B · the Ramanujan-reciprocal crosspair socket (append-only)

`DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45 : ANALYTIC_OPEN / UNINHABITED`.

The reciprocal normal form of `AddMinRamanujanReciprocity` removes the quotient
`[ℓ(dp − uh) − 2]/(uA)` from the rough coefficient, but it does **not** remove
the source coupling.  The residual analytic statement is exposed here as an
**uninhabited** interface which retains every actual source slot:

* the finite lift `e`, the conductor `c` and `ℓ = c e`;
* the modulus `q_ℓ = ℓ M`;
* the additive-minor frequency `m` and the actual `ρ̂(m)`;
* the source variables `u`, `A`;
* the moving Ramanujan divisor `rRam ∣ u A` and the unit `x mod rRam`;
* the inverses `(uA)⁻¹ mod q_ℓ` and `(uA)⁻¹ mod M`;
* the effective phase `Θ = m (uA)⁻¹ / M + x ℓ / rRam`;
* the literal `μ(d)`, `log p`, `κ(h)` rough transform.

It is *not* replaced by arbitrary `L²` vectors, and it is **never inhabited**.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AddMinRamanujanSocket

open Finset ArithmeticFunction FiniteLiftLocalTwist AddMinRamanujan

/-! ## 1. The source-preserving configuration -/

/-- **The Ramanujan-reciprocal source configuration.**  Every slot of the
research statement is an explicit field. -/
structure RamanujanReciprocalConfig (ι : Type*) where
  /-- The finite lift `e`. -/
  e : ℕ
  /-- The conductor `c`. -/
  c : ℕ
  /-- `ℓ = c · e`. -/
  ell : ℕ
  /-- `ℓ` really is `c e`. -/
  ell_eq : ell = c * e
  /-- The prime modulus `M`. -/
  M : ℕ
  /-- `M` is prime (the physical conductor prime). -/
  M_prime : Nat.Prime M
  /-- `q_ℓ = ℓ M`. -/
  qell : ℕ
  /-- `q_ℓ` really is `ℓ M`. -/
  qell_eq : qell = ell * M
  /-- The additive-minor frequency `m`. -/
  m : ℤ
  /-- The additive-minor transform `ρ̂(m)` — the *actual* source value. -/
  rhoHat : ℤ → ℂ
  /-- The source variable `u`. -/
  u : ℕ
  /-- The source variable `A`. -/
  A : ℕ
  /-- `u A > 0`. -/
  uA_pos : 0 < u * A
  /-- The integer inverse of `uA` modulo `q_ℓ`. -/
  invQ : ℤ
  /-- The integer inverse of `uA` modulo `M`. -/
  invM : ℤ
  /-- `uA · invQ ≡ 1 (mod q_ℓ)`. -/
  invQ_spec : (qell : ℤ) ∣ ((u * A : ℕ) : ℤ) * invQ - 1
  /-- `uA · invM ≡ 1 (mod M)`. -/
  invM_spec : (M : ℤ) ∣ ((u * A : ℕ) : ℤ) * invM - 1
  /-- The literal rough source (`μ(d)`, `log p`, `κ(h)`, `u`, `W`). -/
  R : RoughSource ι
  /-- The rough source uses the same `u`. -/
  R_u : R.u = (u : ℤ)

variable {ι : Type*}

/-- The companion DFT after Ramanujan reciprocity: a sum over the moving divisor
`rRam ∣ uA` and the units `x mod rRam` of the reciprocal phase times the rough
transform evaluated at the shared `Θ`. -/
noncomputable def reciprocalCompanion (P : RamanujanReciprocalConfig ι) : ℂ :=
  ∑ rRam ∈ (P.u * P.A).divisors, ∑ x ∈ unitsMod rRam,
    ezExp P.qell (-2 * (P.m * P.invQ)) * ezExp rRam (-2 * (x : ℤ)) *
      roughTransform P.R P.M rRam (P.m * P.invM) (x : ℤ) (P.ell : ℤ)

/-- The additive-minor crosspair in the reciprocal representation: the source
`ρ̂(m)` paired with the reciprocal companion, normalised by `1/(uA)`. -/
noncomputable def ramanujanReciprocalCrossPair (P : RamanujanReciprocalConfig ι) : ℂ :=
  P.rhoHat P.m * (((P.u * P.A : ℕ) : ℂ))⁻¹ * reciprocalCompanion P

/-! ## 2. The analytic socket (UNINHABITED) -/

/-- **`DetLineAddMinRamanujanReciprocalCrosspairInput` — UNINHABITED.**

`DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45`: the first exact research
residual.  The interface adds only the (unproved) arbitrary-log analytic bound
on top of the source-preserving configuration; it is never constructed in this
repository. -/
structure DetLineAddMinRamanujanReciprocalCrosspairInput
    (P : RamanujanReciprocalConfig ι) where
  /-- The declared arbitrary-log budget. -/
  budget : ℝ
  /-- The analytic assertion.  **NOT SUPPLIED.** -/
  bound : ‖ramanujanReciprocalCrossPair P‖ ≤ budget

/-- The socket is an assumption, not a theorem: all it yields is its own declared
bound. -/
theorem crosspair_input_is_an_assumption {P : RamanujanReciprocalConfig ι}
    (I : DetLineAddMinRamanujanReciprocalCrosspairInput P) :
    ‖ramanujanReciprocalCrossPair P‖ ≤ I.budget := I.bound

/-- **Non-claim.**  A declared budget carries no saving by itself: an instance
with an arbitrarily large budget exists for *any* configuration only if one
assumes it, and the trivial bound obtainable here is the natural-scale one. -/
theorem socket_budget_is_not_a_saving {P : RamanujanReciprocalConfig ι}
    (I : DetLineAddMinRamanujanReciprocalCrosspairInput P) (C : ℝ) (hC : I.budget ≤ C) :
    ‖ramanujanReciprocalCrossPair P‖ ≤ C := le_trans I.bound hC

/-! ## 3. Source-slot firewall -/

/-- **The socket keeps the physical source.**  The reciprocal companion is
literally a sum over the moving divisors of `uA` and the units mod `rRam` of the
reciprocal phase times the `μ(d) log p κ(h)` rough transform: no `L²`
abstraction has been substituted. -/
theorem reciprocalCompanion_keeps_source (P : RamanujanReciprocalConfig ι) :
    reciprocalCompanion P
      = ∑ rRam ∈ (P.u * P.A).divisors, ∑ x ∈ unitsMod rRam,
          ezExp P.qell (-2 * (P.m * P.invQ)) * ezExp rRam (-2 * (x : ℤ)) *
            ∑ t ∈ P.R.T, ((ArithmeticFunction.moebius (P.R.dNat t) : ℤ) : ℂ) *
              ((Real.log (P.R.pNat t) : ℝ) : ℂ) * P.R.kappa (P.R.hVar t) * P.R.W t *
                thetaPhase P.M rRam (P.m * P.invM) (x : ℤ) (P.ell : ℤ) (P.R.Tval t) := rfl

/-- **The coprimality routing is genuinely used.**  From the configuration's
inverse data the reduction `invQ ≡ invM (mod M)` is kernel-proved, which is what
licenses writing the `Θ`-phase with `invM`. -/
theorem config_inv_reduction (P : RamanujanReciprocalConfig ι) :
    (P.M : ℤ) ∣ (P.invQ - P.invM) := by
  refine inv_unique_mod_M (N := ((P.u * P.A : ℕ) : ℤ)) ?_ P.invM_spec
  refine inv_reduction_qell_to_M ?_ P.invQ_spec
  exact ⟨(P.ell : ℤ), by rw [P.qell_eq]; push_cast; ring⟩

end AddMinRamanujanSocket
end CurrentProgramme
end TwinPrimeProject
