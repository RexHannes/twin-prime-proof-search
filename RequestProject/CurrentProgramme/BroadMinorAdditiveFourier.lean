import Mathlib
import RequestProject.CurrentProgramme.FiniteLineFourier

/-!
# Gate 1B · broad-minor additive Fourier law (append-only delta layer)

`BROADMINOR-INTERNAL-MAJOR-ORTHOGONALITY45`.

**Kernel-proved: exact finite Fourier algebra.**  The analytic transition
estimate is *not* proved; it is exposed as the uninhabited
`BroadMinorTransitionEstimateInput`.

## Convention

On `ZMod q` we use the `+`-signed transform

```
fhat(m) = ∑_s f(s) e_q(m s),      f(s) = (1/q) ∑_m fhat(m) e_q(-m s),
```

realised as `dftPlus f m = ∑ s, e_q(m s) f(s)`.  This is the repository's
`ZMod.dft` at `-m`, so the exact Parseval identity of
`FiniteLineFourier.dft_inner` is reused rather than reproved.

## Firewall

A smooth multiplier `Π` is **not** automatically an orthogonal projection.  The
exact pairing identity carries the factor `Π(1-Π)`, which vanishes only under
idempotence `Π² = Π`.  See
`smooth_multiplier_is_not_automatically_an_orthogonal_projection`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace BroadMinorFourier

open Finset ZMod

variable {q : ℕ} [NeZero q]

/-! ## 1. The `+`-signed transform and Parseval -/

/-- `fhat(m) = ∑_s f(s) e_q(m s)`. -/
noncomputable def dftPlus (f : ZMod q → ℂ) (m : ZMod q) : ℂ :=
  ∑ s : ZMod q, (ZMod.stdAddChar (m * s)) * f s

theorem dftPlus_eq_dft (f : ZMod q → ℂ) (m : ZMod q) : dftPlus f m = 𝓕 f (-m) := by
  simp only [dftPlus, ZMod.dft_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 2
  ring

/-- `dftPlus` is additive in the function argument. -/
theorem dftPlus_sub (f g : ZMod q → ℂ) (m : ZMod q) :
    dftPlus (fun s => f s - g s) m = dftPlus f m - dftPlus g m := by
  simp only [dftPlus, mul_sub, Finset.sum_sub_distrib]

/-- **Exact Parseval for the `+`-signed transform.**
`∑_m fhat(m) conj(ghat(m)) = q ∑_s f(s) conj(g(s))`. -/
theorem dftPlus_inner (f g : ZMod q → ℂ) :
    ∑ m : ZMod q, dftPlus f m * (starRingEnd ℂ) (dftPlus g m)
      = (q : ℂ) * ∑ s : ZMod q, f s * (starRingEnd ℂ) (g s) := by
  have hre : ∑ m : ZMod q, dftPlus f m * (starRingEnd ℂ) (dftPlus g m)
      = ∑ k : ZMod q, 𝓕 f k * (starRingEnd ℂ) (𝓕 g k) := by
    rw [← Fintype.sum_equiv (Equiv.neg (ZMod q))
      (fun m => dftPlus f m * (starRingEnd ℂ) (dftPlus g m))
      (fun k => 𝓕 f k * (starRingEnd ℂ) (𝓕 g k))]
    intro m
    simp [dftPlus_eq_dft, Equiv.neg]
  rw [hre, FiniteLineFourier.dft_inner]

/-- **Exact Parseval pairing.**  `⟨f, g⟩ = (1/q) ∑_m fhat(m) conj(ghat(m))`. -/
theorem pairing_eq (f g : ZMod q → ℂ) :
    ∑ s : ZMod q, f s * (starRingEnd ℂ) (g s)
      = ((q : ℂ))⁻¹ * ∑ m : ZMod q, dftPlus f m * (starRingEnd ℂ) (dftPlus g m) := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne q)
  rw [dftPlus_inner, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]

/-! ## 2. The broad-minor multiplier law -/

/-- **`rhohat = (1-Π) deltahat`.**  If `lambdahat(m) = Π(m) deltahat(m)` and
`ρ = δ - λ`, then `ρhat(m) = (1 - Π(m)) deltahat(m)`.  Exact. -/
theorem rhohat_eq (delta lambda : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (hlam : ∀ m, dftPlus lambda m = (Pi m : ℂ) * dftPlus delta m) (m : ZMod q) :
    dftPlus (fun s => delta s - lambda s) m = (1 - (Pi m : ℂ)) * dftPlus delta m := by
  rw [dftPlus_sub, hlam m]; ring

/-- **Exact Parseval pairing for `ρ`.**
`⟨ρ, F⟩ = (1/q) ∑_m (1-Π(m)) deltahat(m) conj(Fhat(m))`. -/
theorem rho_pairing (delta lambda F : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (hlam : ∀ m, dftPlus lambda m = (Pi m : ℂ) * dftPlus delta m) :
    ∑ s : ZMod q, (delta s - lambda s) * (starRingEnd ℂ) (F s)
      = ((q : ℂ))⁻¹ * ∑ m : ZMod q,
          (1 - (Pi m : ℂ)) * dftPlus delta m * (starRingEnd ℂ) (dftPlus F m) := by
  rw [pairing_eq (fun s => delta s - lambda s) F]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rhohat_eq delta lambda Pi hlam m]

/-! ## 3. The non-idempotence firewall -/

/-- **Exact pairing against a multiplier operator.**  If `P` is the multiplier
operator with `Fourier(P F)(m) = Π(m) Fhat(m)`, then

```
⟨ρ, P F⟩ = (1/q) ∑_m Π(m)(1-Π(m)) deltahat(m) conj(Fhat(m)).
```

The factor `Π(1-Π)` is **not** dropped. -/
theorem rho_pairing_multiplier (delta lambda F PF : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (hlam : ∀ m, dftPlus lambda m = (Pi m : ℂ) * dftPlus delta m)
    (hPF : ∀ m, dftPlus PF m = (Pi m : ℂ) * dftPlus F m) :
    ∑ s : ZMod q, (delta s - lambda s) * (starRingEnd ℂ) (PF s)
      = ((q : ℂ))⁻¹ * ∑ m : ZMod q,
          (Pi m : ℂ) * (1 - (Pi m : ℂ)) * dftPlus delta m *
            (starRingEnd ℂ) (dftPlus F m) := by
  rw [pairing_eq (fun s => delta s - lambda s) PF]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [rhohat_eq delta lambda Pi hlam m, hPF m, map_mul, Complex.conj_ofReal]
  ring

/-- **Exact orthogonality under idempotence.**  If `Π(m)² = Π(m)` for every `m`
then the multiplier really is an orthogonal projection and `⟨ρ, P F⟩ = 0`. -/
theorem rho_pairing_multiplier_eq_zero_of_idempotent
    (delta lambda F PF : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (hlam : ∀ m, dftPlus lambda m = (Pi m : ℂ) * dftPlus delta m)
    (hPF : ∀ m, dftPlus PF m = (Pi m : ℂ) * dftPlus F m)
    (hidem : ∀ m, Pi m ^ 2 = Pi m) :
    ∑ s : ZMod q, (delta s - lambda s) * (starRingEnd ℂ) (PF s) = 0 := by
  rw [rho_pairing_multiplier delta lambda F PF Pi hlam hPF]
  have hz : ∀ m : ZMod q,
      (Pi m : ℂ) * (1 - (Pi m : ℂ)) * dftPlus delta m *
        (starRingEnd ℂ) (dftPlus F m) = 0 := by
    intro m
    have hr : Pi m * (1 - Pi m) = 0 := by nlinarith [hidem m]
    have hc : (Pi m : ℂ) * (1 - (Pi m : ℂ)) = 0 := by
      have := congrArg (fun x : ℝ => (x : ℂ)) hr
      push_cast at this
      linear_combination this
    rw [hc]; ring
  rw [Finset.sum_congr rfl fun m _ => hz m]
  simp

/-- **`smooth_multiplier_is_not_automatically_an_orthogonal_projection`.**

A literal countermodel on the two-element cyclic group: `Π ≡ 1/2` takes values
in `[0,1]`, yet the exact pairing functional
`(1/q) ∑_m Π(1-Π) deltahat conj(Fhat)` is nonzero.  Hence there is no
unconditional theorem `⟨ρ, P_Π F⟩ = 0`. -/
theorem smooth_multiplier_is_not_automatically_an_orthogonal_projection :
    ∃ (Pi : ZMod 2 → ℝ) (dhat Fhat : ZMod 2 → ℂ),
      (∀ m, Pi m ∈ Set.Icc (0 : ℝ) 1) ∧ (¬ ∀ m, Pi m ^ 2 = Pi m) ∧
      ((2 : ℂ))⁻¹ * ∑ m : ZMod 2,
          (Pi m : ℂ) * (1 - (Pi m : ℂ)) * dhat m * (starRingEnd ℂ) (Fhat m) ≠ 0 := by
  refine ⟨fun _ => 1 / 2, fun _ => 1, fun _ => 1, fun m => by norm_num, ?_, ?_⟩
  · intro h
    have := h 0
    norm_num at this
  · simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    norm_num

/-! ## 4. Plateau / transition / minor split -/

/-- The additive-major **plateau**: the frequencies where `Π = 1`. -/
noncomputable def plateau (Pi : ZMod q → ℝ) : Finset (ZMod q) :=
  Finset.univ.filter (fun m => Pi m = 1)

/-- The **transition** region `T = {m : 0 < Π(m) < 1}`. -/
noncomputable def transition (Pi : ZMod q → ℝ) : Finset (ZMod q) :=
  Finset.univ.filter (fun m => 0 < Pi m ∧ Pi m < 1)

/-- The **additive minor** region: the frequencies where `Π = 0`. -/
noncomputable def additiveMinor (Pi : ZMod q → ℝ) : Finset (ZMod q) :=
  Finset.univ.filter (fun m => Pi m = 0)

/-- The three regions are pairwise disjoint. -/
theorem regions_disjoint (Pi : ZMod q → ℝ) :
    Disjoint (plateau Pi) (transition Pi) ∧
    Disjoint (plateau Pi) (additiveMinor Pi) ∧
    Disjoint (transition Pi) (additiveMinor Pi) := by
  classical
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [Finset.disjoint_left] <;>
    intro m hm hm' <;>
    simp only [plateau, transition, additiveMinor, Finset.mem_filter,
      Finset.mem_univ, true_and] at hm hm' <;>
    first
      | (rw [hm] at hm'; linarith [hm'.2])
      | (rw [hm] at hm'; norm_num at hm')
      | (rw [hm'] at hm; linarith [hm.1])

/-- Under `0 ≤ Π ≤ 1` the three regions cover every frequency. -/
theorem regions_cover (Pi : ZMod q → ℝ) (hPi : ∀ m, Pi m ∈ Set.Icc (0 : ℝ) 1) (m : ZMod q) :
    m ∈ plateau Pi ∨ m ∈ transition Pi ∨ m ∈ additiveMinor Pi := by
  classical
  obtain ⟨h0, h1⟩ := hPi m
  simp only [plateau, transition, additiveMinor, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases eq_or_lt_of_le h0 with h | h
  · exact Or.inr (Or.inr h.symm)
  · rcases eq_or_lt_of_le h1 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl ⟨h, h'⟩)

/-- **MAJOR PLATEAU: EXACT ZERO.**  On the plateau `Π = 1`, so `ρhat = 0` and the
plateau contribution to the pairing vanishes identically. -/
theorem plateau_contribution_zero (delta lambda F : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (hlam : ∀ m, dftPlus lambda m = (Pi m : ℂ) * dftPlus delta m) :
    ∑ m ∈ plateau Pi,
        dftPlus (fun s => delta s - lambda s) m * (starRingEnd ℂ) (dftPlus F m) = 0 := by
  classical
  refine Finset.sum_eq_zero fun m hm => ?_
  simp only [plateau, Finset.mem_filter] at hm
  rw [rhohat_eq delta lambda Pi hlam m, hm.2]
  simp

/-! ## 5. The transition analytic socket (uninhabited) -/

/-- **`BroadMinorTransitionEstimateInput` — UNINHABITED.**

The research assumptions for the transition region: a density budget for
`#T/q`, a Fourier bound on `deltahat` over `T`, a companion global bound, and
the resulting arbitrary-log pairing budget.  Never inhabited here. -/
structure BroadMinorTransitionEstimateInput (q : ℕ) [NeZero q]
    (delta F : ZMod q → ℂ) (Pi : ZMod q → ℝ) where
  /-- `#T_ℓ / q_ℓ ≤ density`. -/
  density : ℝ
  /-- The transition Fourier bound on the companion source. -/
  deltaBound : ℝ
  /-- The companion global bound (`L²`-energy derived). -/
  companionBound : ℝ
  /-- The declared arbitrary-log transition pairing budget. -/
  budget : ℝ
  /-- Density hypothesis. -/
  density_le : ((transition Pi).card : ℝ) ≤ density * q
  /-- Transition Fourier bound. -/
  delta_le : ∀ m ∈ transition Pi, ‖dftPlus delta m‖ ≤ deltaBound
  /-- Companion bound. -/
  companion_le : ∀ m ∈ transition Pi, ‖dftPlus F m‖ ≤ companionBound
  /-- Nonnegativity of the declared sizes. -/
  deltaBound_nonneg : 0 ≤ deltaBound
  /-- Nonnegativity of the declared sizes. -/
  companionBound_nonneg : 0 ≤ companionBound
  /-- The budget dominates the product. -/
  budget_ge : density * (deltaBound * companionBound) ≤ budget
  /-- `Π` is a genuine `[0,1]`-multiplier. -/
  Pi_mem : ∀ m, Pi m ∈ Set.Icc (0 : ℝ) 1

/-- The transition pairing, `(1/q) ∑_{m ∈ T} ρhat(m) conj(Fhat(m))`. -/
noncomputable def transitionPairing (delta lambda F : ZMod q → ℂ) (Pi : ZMod q → ℝ) : ℂ :=
  ((q : ℂ))⁻¹ * ∑ m ∈ transition Pi,
    dftPlus (fun s => delta s - lambda s) m * (starRingEnd ℂ) (dftPlus F m)

/-- `TransitionPairingNegligible B` : the transition pairing is at most `B`. -/
def TransitionPairingNegligible (delta lambda F : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (B : ℝ) : Prop :=
  ‖transitionPairing delta lambda F Pi‖ ≤ B

/-- **CONDITIONAL COMPILER.**  The transition input bounds the transition
pairing by its declared budget.  Implication only: the input is never
inhabited. -/
theorem transition_pairing_negligible_of_input
    (delta lambda F : ZMod q → ℂ) (Pi : ZMod q → ℝ)
    (hlam : ∀ m, dftPlus lambda m = (Pi m : ℂ) * dftPlus delta m)
    (I : BroadMinorTransitionEstimateInput q delta F Pi) :
    TransitionPairingNegligible delta lambda F Pi I.budget := by
  classical
  have hq : (0 : ℝ) < q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hterm : ∀ m ∈ transition Pi,
      ‖dftPlus (fun s => delta s - lambda s) m * (starRingEnd ℂ) (dftPlus F m)‖
        ≤ I.deltaBound * I.companionBound := by
    intro m hm
    rw [rhohat_eq delta lambda Pi hlam m, norm_mul, norm_mul, RCLike.norm_conj]
    obtain ⟨h0, h1⟩ := I.Pi_mem m
    have hle : ‖(1 : ℂ) - (Pi m : ℂ)‖ ≤ 1 := by
      have hcast : ((1 : ℂ) - (Pi m : ℂ)) = ((1 - Pi m : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
      linarith
    calc ‖(1 : ℂ) - (Pi m : ℂ)‖ * ‖dftPlus delta m‖ * ‖dftPlus F m‖
        ≤ 1 * I.deltaBound * I.companionBound := by
          refine mul_le_mul (mul_le_mul hle (I.delta_le m hm) (norm_nonneg _) zero_le_one)
            (I.companion_le m hm) (norm_nonneg _) ?_
          rw [one_mul]; exact I.deltaBound_nonneg
      _ = I.deltaBound * I.companionBound := by ring
  have hsum : ‖∑ m ∈ transition Pi,
      dftPlus (fun s => delta s - lambda s) m * (starRingEnd ℂ) (dftPlus F m)‖
      ≤ ((transition Pi).card : ℝ) * (I.deltaBound * I.companionBound) := by
    calc ‖∑ m ∈ transition Pi, _‖
        ≤ ∑ m ∈ transition Pi,
            ‖dftPlus (fun s => delta s - lambda s) m * (starRingEnd ℂ) (dftPlus F m)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _m ∈ transition Pi, I.deltaBound * I.companionBound :=
          Finset.sum_le_sum hterm
      _ = ((transition Pi).card : ℝ) * (I.deltaBound * I.companionBound) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hprod : (0 : ℝ) ≤ I.deltaBound * I.companionBound :=
    mul_nonneg I.deltaBound_nonneg I.companionBound_nonneg
  rw [TransitionPairingNegligible, transitionPairing, norm_mul, norm_inv, Complex.norm_natCast]
  have hstep : (q : ℝ)⁻¹ * ‖∑ m ∈ transition Pi,
      dftPlus (fun s => delta s - lambda s) m * (starRingEnd ℂ) (dftPlus F m)‖
      ≤ (q : ℝ)⁻¹ * (((transition Pi).card : ℝ) * (I.deltaBound * I.companionBound)) :=
    mul_le_mul_of_nonneg_left hsum (by positivity)
  refine hstep.trans (le_trans ?_ I.budget_ge)
  have : (q : ℝ)⁻¹ * (((transition Pi).card : ℝ) * (I.deltaBound * I.companionBound))
      ≤ (q : ℝ)⁻¹ * ((I.density * q) * (I.deltaBound * I.companionBound)) := by
    have := mul_le_mul_of_nonneg_right I.density_le hprod
    exact mul_le_mul_of_nonneg_left this (by positivity)
  refine this.trans (le_of_eq ?_)
  field_simp

end BroadMinorFourier
end CurrentProgramme
end TwinPrimeProject
