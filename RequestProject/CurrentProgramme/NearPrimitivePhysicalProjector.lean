import Mathlib
import RequestProject.CurrentProgramme.FiniteLiftLocalTwistCompression

/-!
# Gate 1B · near-primitive physical projector algebra (append-only delta layer)

`DETLINE-NEARPRIM-PRIMITIVE-TO-PHYSICAL45`.

**Kernel-proved here: exact finite projector algebra only.**  No asymptotic
statement is proved; in particular neither `S/c = Y^{-3/2+o(1)}` nor any
`O_A(X (log X)^{-A})` conclusion is formalised.  Those are exposed as the
uninhabited interfaces `SmallProjectorLargeLiftClosureInput`,
`ProjectorWeightErrorEstimateInput` and
`NearPrimitiveToPhysicalAnalyticInput`.

## Kernel content

* `projKernel c d = ∑_{r ∣ c, r ∣ d} φ(r) μ(c/r)` — the right-hand side of the
  primitive-character projector identity
  `∑_{χ* mod c primitive} χ*(s₁) conj χ*(s₂) = ∑_{r ∣ c, r ∣ s₁-s₂} φ(r) μ(c/r)`.
  The identity itself relates this to an *external* character sum and is kept as
  the uninhabited interface `PrimitiveProjectorIdentityInput`.
* `eq_of_dvd_of_abs_le` — the **pure order lemma**: `r > 2S`, `r ∣ s₁-s₂`,
  `|sᵢ| ≤ S` force `s₁ = s₂`.
* `largeProjector` / `smallProjector`, `Omega`, `phiStar`, their exact splits,
  and the **exact physicalisation identity** `projectorKernel = weighted physical
  diagonal + small-projector routed part`.
* `induced_lift` — `e' = e·(c/r) = ℓ/r` for `ℓ = c·e`, `r ∣ c`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace NearPrimitiveProjector

open Finset

/-! ## 0. Möbius bound -/

theorem abs_moebius_le_one (n : ℕ) : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
  rcases ArithmeticFunction.moebius_eq_or n with h | h | h <;>
    simp [h]

/-! ## 1. The projector weight `Ω_c(S)` and the primitive count `φ*(c)` -/

/-- `φ*(c) = ∑_{r ∣ c} μ(c/r) φ(r)`: the number of primitive characters mod `c`,
written in the divisor form used throughout this layer. -/
def phiStar (c : ℕ) : ℤ :=
  ∑ r ∈ c.divisors, (Nat.totient r : ℤ) * ArithmeticFunction.moebius (c / r)

/-- `Ω_c(S) = ∑_{q ∣ c, c/q > 2S} μ(q) φ(c/q)`, written in the reindexed form
`r = c/q`, i.e. `∑_{r ∣ c, r > 2S} φ(r) μ(c/r)`. -/
def Omega (c S : ℕ) : ℤ :=
  ∑ r ∈ c.divisors.filter (fun r => 2 * S < r),
    (Nat.totient r : ℤ) * ArithmeticFunction.moebius (c / r)

/-- The complementary (small-projector) weight `∑_{r ∣ c, r ≤ 2S} φ(r) μ(c/r)`. -/
def OmegaSmall (c S : ℕ) : ℤ :=
  ∑ r ∈ c.divisors.filter (fun r => ¬ 2 * S < r),
    (Nat.totient r : ℤ) * ArithmeticFunction.moebius (c / r)

/-- **Exact decomposition.**  `φ*(c) = Ω_c(S) + ∑_{r ∣ c, r ≤ 2S} μ(c/r) φ(r)`,
equivalently `Ω_c(S) = φ*(c) − ∑_{r ∣ c, r ≤ 2S} μ(c/r) φ(r)`. -/
theorem phiStar_eq_omega_add (c S : ℕ) : phiStar c = Omega c S + OmegaSmall c S := by
  classical
  rw [phiStar, Omega, OmegaSmall, Finset.sum_filter_add_sum_filter_not]

theorem omega_eq_phiStar_sub (c S : ℕ) : Omega c S = phiStar c - OmegaSmall c S := by
  rw [phiStar_eq_omega_add c S]; ring

/-- **Projector-weight error, elementary form.**
`|Ω_c(S) − φ*(c)| ≤ ∑_{r ∣ c, r ≤ 2S} φ(r)`. -/
theorem omega_sub_phiStar_abs_le (c S : ℕ) :
    |(Omega c S : ℝ) - (phiStar c : ℝ)|
      ≤ ∑ r ∈ c.divisors.filter (fun r => ¬ 2 * S < r), (Nat.totient r : ℝ) := by
  classical
  have h : (Omega c S : ℝ) - (phiStar c : ℝ) = -((OmegaSmall c S : ℤ) : ℝ) := by
    rw [omega_eq_phiStar_sub c S]; push_cast; ring
  rw [h, abs_neg]
  have h1 : |((OmegaSmall c S : ℤ) : ℝ)|
      ≤ ∑ r ∈ c.divisors.filter (fun r => ¬ 2 * S < r),
          |(Nat.totient r : ℝ) * (ArithmeticFunction.moebius (c / r) : ℝ)| := by
    rw [OmegaSmall]
    push_cast
    exact Finset.abs_sum_le_sum_abs _ _
  refine h1.trans (Finset.sum_le_sum fun r _ => ?_)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient r : ℝ))]
  calc (Nat.totient r : ℝ) * |(ArithmeticFunction.moebius (c / r) : ℝ)|
      ≤ (Nat.totient r : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (abs_moebius_le_one _) (by positivity)
    _ = (Nat.totient r : ℝ) := by ring

/-- **Projector-weight error, divisor form.**  `|Ω_c(S) − φ*(c)| ≤ 2S · τ(c)`,
using only `φ(r) ≤ r ≤ 2S`. -/
theorem omega_sub_phiStar_abs_le_divisor (c S : ℕ) :
    |(Omega c S : ℝ) - (phiStar c : ℝ)| ≤ 2 * S * c.divisors.card := by
  classical
  refine (omega_sub_phiStar_abs_le c S).trans ?_
  have hterm : ∀ r ∈ c.divisors.filter (fun r => ¬ 2 * S < r),
      (Nat.totient r : ℝ) ≤ 2 * S := by
    intro r hr
    rw [Finset.mem_filter] at hr
    have hle : r ≤ 2 * S := by omega
    calc (Nat.totient r : ℝ) ≤ (r : ℝ) := by exact_mod_cast Nat.totient_le r
      _ ≤ 2 * S := by exact_mod_cast hle
  calc ∑ r ∈ c.divisors.filter (fun r => ¬ 2 * S < r), (Nat.totient r : ℝ)
      ≤ ∑ _r ∈ c.divisors.filter (fun r => ¬ 2 * S < r), (2 * S : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (c.divisors.filter (fun r => ¬ 2 * S < r)).card * (2 * S : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (c.divisors.card : ℝ) * (2 * S : ℝ) := by
        have := Finset.card_filter_le c.divisors (fun r => ¬ 2 * S < r)
        have h2 : (0 : ℝ) ≤ 2 * S := by positivity
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast this) h2
    _ = 2 * S * c.divisors.card := by ring

/-! ## 2. The projector kernel and the pure order lemma -/

/-- `projKernel c d = ∑_{r ∣ c, r ∣ d} φ(r) μ(c/r)`: the arithmetic right-hand
side of the primitive-character projector identity, at difference `d = s₁ − s₂`. -/
noncomputable def projKernel (c : ℕ) (d : ℤ) : ℤ :=
  ∑ r ∈ c.divisors.filter (fun r : ℕ => (r : ℤ) ∣ d),
    (Nat.totient r : ℤ) * ArithmeticFunction.moebius (c / r)

/-- The large-projector part `r > 2S`. -/
noncomputable def largeProjector (c S : ℕ) (d : ℤ) : ℤ :=
  ∑ r ∈ (c.divisors.filter (fun r : ℕ => (r : ℤ) ∣ d)).filter (fun r => 2 * S < r),
    (Nat.totient r : ℤ) * ArithmeticFunction.moebius (c / r)

/-- The small-projector part `r ≤ 2S`. -/
noncomputable def smallProjector (c S : ℕ) (d : ℤ) : ℤ :=
  ∑ r ∈ (c.divisors.filter (fun r : ℕ => (r : ℤ) ∣ d)).filter (fun r => ¬ 2 * S < r),
    (Nat.totient r : ℤ) * ArithmeticFunction.moebius (c / r)

theorem projKernel_split (c S : ℕ) (d : ℤ) :
    projKernel c d = largeProjector c S d + smallProjector c S d := by
  classical
  rw [projKernel, largeProjector, smallProjector, Finset.sum_filter_add_sum_filter_not]

/-- **PURE ORDER LEMMA.**  On the physical support `|s| ≤ S`, a modulus larger
than `2S` cannot identify two distinct points. -/
theorem eq_of_dvd_of_abs_le {r : ℕ} {S : ℕ} {s₁ s₂ : ℤ}
    (hr : 2 * S < r) (hdvd : (r : ℤ) ∣ s₁ - s₂)
    (h₁ : |s₁| ≤ S) (h₂ : |s₂| ≤ S) : s₁ = s₂ := by
  by_contra hne
  have hne' : s₁ - s₂ ≠ 0 := sub_ne_zero.2 hne
  have hle : (r : ℤ) ≤ |s₁ - s₂| := Int.le_of_dvd (abs_pos.2 hne') ((dvd_abs _ _).2 hdvd)
  obtain ⟨ha, hb⟩ := abs_le.1 h₁
  obtain ⟨hc, hd⟩ := abs_le.1 h₂
  have hsm : |s₁ - s₂| ≤ 2 * (S : ℤ) := abs_le.2 ⟨by linarith, by linarith⟩
  have hr' : (2 * S : ℤ) < r := by exact_mod_cast hr
  push_cast at hr'
  linarith

/-- **Large projectors give the physical diagonal (off-diagonal half).**  For
distinct physical points the whole large-projector part vanishes. -/
theorem largeProjector_eq_zero_of_ne (c S : ℕ) {s₁ s₂ : ℤ}
    (h₁ : |s₁| ≤ S) (h₂ : |s₂| ≤ S) (hne : s₁ ≠ s₂) :
    largeProjector c S (s₁ - s₂) = 0 := by
  classical
  refine Finset.sum_eq_zero fun r hr => ?_
  rw [Finset.mem_filter, Finset.mem_filter] at hr
  exact absurd (eq_of_dvd_of_abs_le hr.2 hr.1.2 h₁ h₂) hne

/-- **Large projectors give the physical diagonal (diagonal half).**  At a
coincident pair the large-projector part is exactly the projector weight
`Ω_c(S)`. -/
theorem largeProjector_eq_omega (c S : ℕ) :
    largeProjector c S 0 = Omega c S := by
  classical
  rw [largeProjector, Omega, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun r _ => ?_) fun _ _ => rfl
  simp

/-- **EXACT PHYSICALISATION IDENTITY.**  On the physical support `|s| ≤ S`,

```
projKernel c (s₁-s₂) = [s₁ = s₂] · Ω_c(S)  +  smallProjector c S (s₁-s₂),
```

i.e. *primitive-projector packet = weighted physical diagonal + small-projector
routed terms*.  Kernel-proved; no analytic input. -/
theorem physicalisation_split (c S : ℕ) {s₁ s₂ : ℤ}
    (h₁ : |s₁| ≤ S) (h₂ : |s₂| ≤ S) :
    projKernel c (s₁ - s₂)
      = (if s₁ = s₂ then Omega c S else 0) + smallProjector c S (s₁ - s₂) := by
  classical
  rw [projKernel_split c S]
  congr 1
  by_cases h : s₁ = s₂
  · subst h
    rw [if_pos rfl, sub_self, largeProjector_eq_omega]
  · rw [if_neg h, largeProjector_eq_zero_of_ne c S h₁ h₂ h]

/-! ## 3. Induced lifts for small projectors -/

/-- **Induced lift.**  With `ℓ = c·e`, `r ∣ c`, `q = c/r`, the routed child lift
is `e' = e·q = ℓ/r`. -/
theorem induced_lift {c r : ℕ} (e : ℕ) (hr : r ∣ c) : e * (c / r) = (c * e) / r := by
  obtain ⟨k, rfl⟩ := hr
  rcases Nat.eq_zero_or_pos r with rfl | hpos
  · simp
  · rw [Nat.mul_div_cancel_left k hpos,
      show r * k * e = r * (k * e) by ring, Nat.mul_div_cancel_left _ hpos]
    ring

/-! ## 4. Uninhabited analytic interfaces -/

/-- **`PrimitiveProjectorIdentityInput` — UNINHABITED here.**

The primitive-character projector identity

```
∑_{χ* mod c primitive} χ*(s₁) conj(χ*(s₂)) = ∑_{r ∣ c, r ∣ s₁-s₂} φ(r) μ(c/r)
```

for admissible *clean units* `s₁, s₂`.  The right-hand side is the kernel-level
`projKernel` defined above; the left-hand side is supplied abstractly, so this
structure asserts exactly the identity and nothing else. -/
structure PrimitiveProjectorIdentityInput (c : ℕ) where
  /-- The admissibility ("clean unit") predicate. -/
  cleanUnit : ℤ → Prop
  /-- The primitive-character sum `∑_{χ*} χ*(s₁) conj χ*(s₂)`. -/
  primCharSum : ℤ → ℤ → ℂ
  /-- The identity.  NOT SUPPLIED here. -/
  identity : ∀ s₁ s₂, cleanUnit s₁ → cleanUnit s₂ →
    primCharSum s₁ s₂ = ((projKernel c (s₁ - s₂) : ℤ) : ℂ)

/-- **Transport of the exact physicalisation split to the character side.**
Conditional compiler: *given* the primitive-projector identity, the character
sum splits as weighted physical diagonal plus small-projector routed terms. -/
theorem physicalisation_split_of_identity {c S : ℕ} (I : PrimitiveProjectorIdentityInput c)
    {s₁ s₂ : ℤ} (hc₁ : I.cleanUnit s₁) (hc₂ : I.cleanUnit s₂)
    (h₁ : |s₁| ≤ S) (h₂ : |s₂| ≤ S) :
    I.primCharSum s₁ s₂
      = ((if s₁ = s₂ then Omega c S else 0 : ℤ) : ℂ)
        + ((smallProjector c S (s₁ - s₂) : ℤ) : ℂ) := by
  rw [I.identity s₁ s₂ hc₁ hc₂, physicalisation_split c S h₁ h₂]
  push_cast
  ring

/-- **`SmallProjectorLargeLiftClosureInput` — UNINHABITED.**

The previously banked research estimate: every routed child whose induced lift
`e'` exceeds the large-lift threshold is already closed. -/
structure SmallProjectorLargeLiftClosureInput where
  /-- The large-lift threshold. -/
  liftThreshold : ℕ
  /-- "The child at induced lift `e'` is closed." -/
  childClosed : ℕ → Prop
  /-- The (unproved) research closure. -/
  closure : ∀ e', liftThreshold ≤ e' → childClosed e'

/-- **Conditional routing compiler.**  A small projector `r ≤ 2S` dividing `c`,
together with the size hypothesis on its induced lift and the large-lift closure
input, routes to a closed child at lift `ℓ/r`. -/
theorem small_projector_routed_closed (I : SmallProjectorLargeLiftClosureInput)
    {c r S e : ℕ} (hr : r ∈ c.divisors) (_hsmall : r ≤ 2 * S)
    (hsize : I.liftThreshold ≤ e * (c / r)) :
    I.childClosed ((c * e) / r) := by
  have hdvd : r ∣ c := (Nat.mem_divisors.1 hr).1
  rw [← induced_lift e hdvd]
  exact I.closure _ hsize

/-- **`ProjectorWeightErrorEstimateInput` — UNINHABITED.**

The analytic projector-weight conclusion (`S/c = Y^{-3/2+o(1)}` and its power
saving) is *not* formalised; only its abstract consequence, an error budget for
`Ω_c(S)` against `φ*(c)`, is exposed. -/
structure ProjectorWeightErrorEstimateInput (c S : ℕ) where
  /-- The declared error budget. -/
  budget : ℝ
  /-- The (unproved) analytic estimate. -/
  error_le : |(Omega c S : ℝ) - (phiStar c : ℝ)| ≤ budget

/-! ## 5. The weighted physicalisation compiler -/

/-- The weighted physical coefficient `w_{c,e} = Ω_c(S)/φ(c e)`. -/
noncomputable def physicalWeight (c e S : ℕ) : ℝ :=
  (Omega c S : ℝ) / (Nat.totient (c * e) : ℝ)

/-- **`NearPrimitivePhysicalCorrelationTarget`** — the granular conclusion of the
weighted physicalisation: every small projector routes to a closed child, the
projector weight is within budget, and the finite local-twist summation is
within budget. -/
def NearPrimitivePhysicalCorrelationTarget (c e S liftRange : ℕ)
    (childClosed : ℕ → Prop) (weightBudget twistBudget : ℝ) : Prop :=
  (∀ r ∈ c.divisors, r ≤ 2 * S → childClosed ((c * e) / r)) ∧
  |(Omega c S : ℝ) - (phiStar c : ℝ)| ≤ weightBudget ∧
  (∑ f ∈ Finset.Icc 1 liftRange, (f.divisors.card : ℝ)) ≤ twistBudget

/-- **`NearPrimitiveToPhysicalAnalyticInput` — UNINHABITED.**

Granular analytic inputs of `DETLINE-NEARPRIM-PRIMITIVE-TO-PHYSICAL45`:
small-projector child closure, projector-weight error closure, and finite
local-twist summation. -/
structure NearPrimitiveToPhysicalAnalyticInput (c e S : ℕ) where
  /-- Small-projector child closure. -/
  childClosure : SmallProjectorLargeLiftClosureInput
  /-- Projector-weight error closure. -/
  weightError : ProjectorWeightErrorEstimateInput c S
  /-- Finite local-twist summation. -/
  twistSummation : FiniteLiftLocalTwist.LocalTwistDivisorSummationInput
  /-- Every small projector's induced lift clears the large-lift threshold. -/
  smallProjector_lift_large :
    ∀ r ∈ c.divisors, r ≤ 2 * S → childClosure.liftThreshold ≤ e * (c / r)

/-- **CONDITIONAL COMPILER.**  The analytic input yields the weighted
physicalisation target.  This is an implication only: nothing here inhabits
`NearPrimitiveToPhysicalAnalyticInput`. -/
theorem nearPrimitive_to_physical_of_input {c e S : ℕ}
    (I : NearPrimitiveToPhysicalAnalyticInput c e S) :
    NearPrimitivePhysicalCorrelationTarget c e S I.twistSummation.liftBound
      I.childClosure.childClosed I.weightError.budget I.twistSummation.budget := by
  refine ⟨?_, I.weightError.error_le, I.twistSummation.divisorSum_le⟩
  intro r hr hsmall
  exact small_projector_routed_closed I.childClosure hr hsmall
    (I.smallProjector_lift_large r hr hsmall)

end NearPrimitiveProjector
end CurrentProgramme
end TwinPrimeProject
