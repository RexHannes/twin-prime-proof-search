import Gate1B.HStarTwoAnchorCounterguards

/-!
# Gate 1B · one-`T` versus two-`T`, and the exact-square / Cauchy firewall

## Contents

* §1 (namespace `OneT`) the **one-`T` specialisation** `T₁ = T₂ = T`: under a
  unit hypothesis for `T` modulo `g` the two Ford primes are congruent mod `g`,
  `g ∣ π₁ − π₂`, and after `π₁ − π₂ = g h`, `q i = g r i`, the length relation
  `r₁ℓ₁ − r₂ℓ₂ = T h` holds;
* §2 the **one-`T` / two-`T` firewall**: a general two-`T` physical source only
  gives `T₁π₁ ≡ T₂π₂ (mod g)`; the prime congruence `π₁ ≡ π₂ (mod g)` does
  **not** follow.  The counterexample is an actual inhabitant of the physical
  source type (`witnessSource`), so the failure is not vacuous;
* §3 the **Cauchy firewall** at the finite complex-sum level: the one-`T`
  majorant `(∑‖Γ‖²)(∑‖F‖²)` and the two-`T` exact square
  `∑_{T₁,T₂} Γ(T₁) conj Γ(T₂) F(T₁) conj F(T₂)` are separate named objects, both
  proved, and they are provably different constructions.  **No theorem in this
  bank transports phase information from `Γ` through the Cauchy majorant.**
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTwoAnchor

open Finset

/-! ## 1. The one-`T` specialisation -/

namespace OneT

/-- **ONE-`T`.**  With a single Perron variable `T`, moduli `q i = g r i` and
the two `+2` anchors `q i ℓ i = T π i + 2`, if `T` is a unit modulo `g` then the
two Ford primes are congruent modulo `g`.

This rigidity is a *one-`T`* phenomenon; see
`twoT_congruence_does_not_imply_prime_congruence`. -/
theorem oneT_prime_congruence {g r1 r2 ell1 ell2 T pi1 pi2 : ℤ}
    (hcop : IsCoprime g T)
    (h1 : g * r1 * ell1 = T * pi1 + 2)
    (h2 : g * r2 * ell2 = T * pi2 + 2) :
    g ∣ pi1 - pi2 := by
  refine hcop.dvd_of_dvd_mul_left ⟨r1 * ell1 - r2 * ell2, ?_⟩
  linarith [h1, h2]

/-- **ONE-`T`.**  Once `π₁ − π₂ = g h`, the length relation
`r₁ℓ₁ − r₂ℓ₂ = T h` follows (`g ≠ 0`). -/
theorem oneT_length_relation {g r1 r2 ell1 ell2 T pi1 pi2 h : ℤ}
    (hg : g ≠ 0)
    (h1 : g * r1 * ell1 = T * pi1 + 2)
    (h2 : g * r2 * ell2 = T * pi2 + 2)
    (hh : pi1 - pi2 = g * h) :
    r1 * ell1 - r2 * ell2 = T * h := by
  refine mul_left_cancel₀ hg ?_
  have : T * (pi1 - pi2) = T * (g * h) := by rw [hh]
  nlinarith [h1, h2, this]

/-- **ONE-`T`, packaged.**  Unit `T` modulo `g` plus the two one-`T` anchors
give both the prime congruence and, for the resulting `h`, the length
relation. -/
theorem oneT_rigidity {g r1 r2 ell1 ell2 T pi1 pi2 : ℤ}
    (hg : g ≠ 0) (hcop : IsCoprime g T)
    (h1 : g * r1 * ell1 = T * pi1 + 2)
    (h2 : g * r2 * ell2 = T * pi2 + 2) :
    ∃ h : ℤ, pi1 - pi2 = g * h ∧ r1 * ell1 - r2 * ell2 = T * h := by
  obtain ⟨h, hh⟩ := oneT_prime_congruence hcop h1 h2
  exact ⟨h, hh, oneT_length_relation hg h1 h2 hh⟩

end OneT

/-! ## 2. The one-`T` / two-`T` firewall -/

/-- **Two-`T` source congruence.**  A general physical two-anchor source gives
exactly `g ∣ T₁π₁ − T₂π₂`, i.e. `T₁π₁ ≡ T₂π₂ (mod g)`. -/
theorem twoT_congruence (S : HStarTwoAnchorSource) :
    (S.g : ℤ) ∣ (S.T1 : ℤ) * S.pi1 - (S.T2 : ℤ) * S.pi2 :=
  ⟨(S.e1 : ℤ) * S.wp1 * S.ell1 - (S.e2 : ℤ) * S.wp2 * S.ell2,
    (S.physical_difference_system).1⟩

/-- **BANKED FIREWALL.**  `twoT_congruence_does_not_imply_prime_congruence`.

There is an *actual physical two-anchor source* (both Vaughan primes and both
Ford primes genuine primes, all anchors literal) for which
`T₁π₁ ≡ T₂π₂ (mod g)` holds — as it always does — while
`π₁ ≢ π₂ (mod g)`.  One-`T` rigidity therefore may not be transported into the
pre-Cauchy, two-`T` Perron source. -/
theorem twoT_congruence_does_not_imply_prime_congruence :
    ∃ S : HStarTwoAnchorSource,
      ((S.g : ℤ) ∣ (S.T1 : ℤ) * S.pi1 - (S.T2 : ℤ) * S.pi2) ∧
        ¬ ((S.g : ℤ) ∣ (S.pi1 : ℤ) - (S.pi2 : ℤ)) := by
  refine ⟨witnessSource, twoT_congruence _, ?_⟩
  simp only [witnessSource]
  decide

/-- The same failure stated as the refutation of the forbidden implication. -/
theorem no_prime_congruence_from_twoT_source :
    ¬ ∀ S : HStarTwoAnchorSource, (S.g : ℤ) ∣ (S.pi1 : ℤ) - (S.pi2 : ℤ) := by
  obtain ⟨S, _, hS⟩ := twoT_congruence_does_not_imply_prime_congruence
  exact fun h => hS (h S)

/-! ## 3. The Cauchy firewall -/

section Cauchy

variable {ι : Type*} [Fintype ι]

/-- The finite complex sum `V = ∑_T Γ(T) F(T)`. -/
noncomputable def sumV (Gam F : ι → ℂ) : ℂ := ∑ T : ι, Gam T * F T

/-- **`OneTCauchyMajorant`.**  The one-`T` (energy) majorant
`(∑_T ‖Γ(T)‖²)(∑_T ‖F(T)‖²)`.  It is a *real* number and it retains no phase
information about `Γ`. -/
noncomputable def OneTCauchyMajorant (Gam F : ι → ℂ) : ℝ :=
  (∑ T : ι, ‖Gam T‖ ^ 2) * (∑ T : ι, ‖F T‖ ^ 2)

/-- **`TwoTExactSquare`.**  The exact expansion of `|V|²` as a two-`T` double
sum `∑_{T₁,T₂} Γ(T₁) conj Γ(T₂) F(T₁) conj F(T₂)`.  It is a *complex*
expression in which the `Γ`-phases are still present. -/
noncomputable def TwoTExactSquare (Gam F : ι → ℂ) : ℂ :=
  ∑ T1 : ι, ∑ T2 : ι,
    Gam T1 * (starRingEnd ℂ) (Gam T2) * (F T1 * (starRingEnd ℂ) (F T2))

/-- **Exact square.**  `V · conj V` equals the two-`T` double sum. -/
theorem sumV_mul_conj_eq_twoTExactSquare (Gam F : ι → ℂ) :
    sumV Gam F * (starRingEnd ℂ) (sumV Gam F) = TwoTExactSquare Gam F := by
  simp only [sumV, TwoTExactSquare, map_sum, map_mul, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun T1 _ => Finset.sum_congr rfl fun T2 _ => ?_
  ring

/-- **Standard Cauchy–Schwarz.**  `|V|² ≤ (∑‖Γ‖²)(∑‖F‖²)`. -/
theorem sumV_norm_sq_le_majorant (Gam F : ι → ℂ) :
    ‖sumV Gam F‖ ^ 2 ≤ OneTCauchyMajorant Gam F := by
  have h1 : ‖sumV Gam F‖ ≤ ∑ T : ι, ‖Gam T‖ * ‖F T‖ := by
    refine (norm_sum_le _ _).trans ?_
    exact Finset.sum_le_sum fun T _ => le_of_eq (norm_mul _ _)
  have h2 : (∑ T : ι, ‖Gam T‖ * ‖F T‖) ^ 2 ≤ OneTCauchyMajorant Gam F :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun T => ‖Gam T‖) (fun T => ‖F T‖)
  exact le_trans (by nlinarith [norm_nonneg (sumV Gam F), h1,
    Finset.sum_nonneg (fun T (_ : T ∈ Finset.univ) =>
      mul_nonneg (norm_nonneg (Gam T)) (norm_nonneg (F T)))]) h2

end Cauchy

/-- **BANKED FIREWALL.**  The one-`T` Cauchy majorant and the two-`T` exact
square are *different constructions*: for `Γ = (1,−1)`, `F = (1,1)` the exact
square is `0` while the majorant is `4`.  The majorant has destroyed the
`Γ`-phase cancellation that the exact square records. -/
theorem oneTCauchyMajorant_ne_twoTExactSquare :
    ∃ Gam F : Fin 2 → ℂ,
      TwoTExactSquare Gam F = 0 ∧ OneTCauchyMajorant Gam F = 4 := by
  refine ⟨![1, -1], ![1, 1], ?_, ?_⟩
  · norm_num [TwoTExactSquare, Fin.sum_univ_two]
  · norm_num [OneTCauchyMajorant, Fin.sum_univ_two]

/-- No phase transport: the exact square is not determined by the majorant. -/
theorem majorant_does_not_determine_exactSquare :
    ¬ ∀ Gam F Gam' F' : Fin 2 → ℂ,
        OneTCauchyMajorant Gam F = OneTCauchyMajorant Gam' F' →
          TwoTExactSquare Gam F = TwoTExactSquare Gam' F' := by
  intro h
  obtain ⟨Gam, F, hzero, hmaj⟩ := oneTCauchyMajorant_ne_twoTExactSquare
  have hmaj' : OneTCauchyMajorant (![1, 1] : Fin 2 → ℂ) ![1, 1] = 4 := by
    norm_num [OneTCauchyMajorant, Fin.sum_univ_two]
  have := h Gam F ![1, 1] ![1, 1] (by rw [hmaj, hmaj'])
  rw [hzero] at this
  have h4 : TwoTExactSquare (![1, 1] : Fin 2 → ℂ) ![1, 1] = 4 := by
    norm_num [TwoTExactSquare, Fin.sum_univ_two]
  rw [h4] at this
  norm_num at this

end HStarTwoAnchor
end CurrentProgramme
end TwinPrimeProject
