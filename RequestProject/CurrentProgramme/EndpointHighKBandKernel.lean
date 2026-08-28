import Mathlib

/-!
# Phase D/E · finite band kernel, exact band-to-shift identity, anti-`K`-decay
firewall

Everything in this module is **exact finite Fourier algebra**.  No decay
theorem, no smooth Poisson summation, no analytic estimate is proved or assumed.

Setting.  `M` is a finite Fourier modulus, phases are given by an abstract
additive phase datum

```
e : ZMod M → ℂ,   e(x+y) = e(x)·e(y),   conj(e x) = e(-x),
```

which is exactly what a standard additive character supplies.  For a band weight
`ω : ZMod M → ℂ` the band kernel is

```
D(r) = (1/M) ∑_k ω(k) e(-k r),
```

and for sequences `Z, B` the DFTs are `Ẑ(k) = ∑_t Z(t) e(-k t)`.

Banked here:

* `bandPairing_eq_shiftKernelSum` — the exact identity
  `(1/M) ∑_k ω(k) Ẑ(k) conj(B̂(k)) = ∑_{t₁,t₂} Z(t₁) conj(B(t₂)) D(t₁-t₂)`;
* `shiftKernelSum_regroup` / `bandPairing_eq_shiftSum` — regrouping by
  `r = t₁ - t₂` into `∑_r D(r) C(r)`;
* `zeroShift_survives` — the `r = 0` packet is present with coefficient `D(0)`;
* `phaseVariation_alone_does_not_force_decay` — a finite counterguard: varying
  phases alone give no cancellation when the coefficients correlate with them;
* `BandKernelLocalizationInput` — the *uninhabited* analytic localisation
  interface, with an explicit `L¹` budget field;
* the shift-length ledger `S_K = H/K` and the Mid-`k` / Top-`k` partition
  metadata, all with an abstract positive `shiftBudget` (no fake logarithms).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace BandKernel

open Finset

/-! ## 1. Phase data -/

/-- An abstract additive phase on `ZMod M`: multiplicative under addition and
conjugation-inverting.  A standard additive character satisfies these two laws;
they are the only properties used below. -/
structure AddPhase (M : ℕ) where
  /-- The phase function. -/
  e : ZMod M → ℂ
  /-- Additivity. -/
  e_add : ∀ x y, e (x + y) = e x * e y
  /-- Conjugation is reflection. -/
  e_conj : ∀ x, (starRingEnd ℂ) (e x) = e (-x)

namespace AddPhase

variable {M : ℕ} (P : AddPhase M)

theorem e_zero_sq : P.e 0 * P.e 0 = P.e 0 := by
  have := P.e_add 0 0
  simpa using this.symm

/-- The trivial phase, showing the datum is non-vacuous. -/
def trivial (M : ℕ) : AddPhase M where
  e := fun _ => 1
  e_add := by intro x y; simp
  e_conj := by intro x; simp

end AddPhase

/-! ## 2. DFT, band kernel and shift correlations -/

variable {M : ℕ} [NeZero M]

/-- The discrete Fourier transform `Ẑ(k) = ∑_t Z(t) e(-k t)`. -/
noncomputable def dft (P : AddPhase M) (Z : ZMod M → ℂ) (k : ZMod M) : ℂ :=
  ∑ t : ZMod M, Z t * P.e (-(k * t))

/-- The band kernel `D(r) = (1/M) ∑_k ω(k) e(-k r)`. -/
noncomputable def bandKernel (P : AddPhase M) (omega : ZMod M → ℂ) (r : ZMod M) : ℂ :=
  (M : ℂ)⁻¹ * ∑ k : ZMod M, omega k * P.e (-(k * r))

/-- The shift correlation `C(r) = ∑_t Z(t + r) conj(B(t))`. -/
noncomputable def shiftCorrelation (Z B : ZMod M → ℂ) (r : ZMod M) : ℂ :=
  ∑ t : ZMod M, Z (t + r) * (starRingEnd ℂ) (B t)

/-! ## 3. The exact band-to-shift identity -/

/-- Pointwise expansion of a DFT pairing. -/
theorem dft_pair_expand (P : AddPhase M) (Z B : ZMod M → ℂ) (k : ZMod M) :
    dft P Z k * (starRingEnd ℂ) (dft P B k)
      = ∑ t₁ : ZMod M, ∑ t₂ : ZMod M,
          Z t₁ * (starRingEnd ℂ) (B t₂) * P.e (-(k * (t₁ - t₂))) := by
  rw [dft, dft, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
  rw [map_mul, P.e_conj]
  have hphase : P.e (-(k * t₁)) * P.e (- -(k * t₂)) = P.e (-(k * (t₁ - t₂))) := by
    rw [← P.e_add]
    congr 1
    ring
  calc Z t₁ * P.e (-(k * t₁)) * ((starRingEnd ℂ) (B t₂) * P.e (- -(k * t₂)))
      = Z t₁ * (starRingEnd ℂ) (B t₂) * (P.e (-(k * t₁)) * P.e (- -(k * t₂))) := by ring
    _ = Z t₁ * (starRingEnd ℂ) (B t₂) * P.e (-(k * (t₁ - t₂))) := by rw [hphase]

/-- **`bandPairing_eq_shiftKernelSum`.**  The exact finite identity

`(1/M) ∑_k ω(k) Ẑ(k) conj(B̂(k)) = ∑_{t₁,t₂} Z(t₁) conj(B(t₂)) D(t₁-t₂)`.

No decay assumption of any kind. -/
theorem bandPairing_eq_shiftKernelSum (P : AddPhase M) (omega Z B : ZMod M → ℂ) :
    (M : ℂ)⁻¹ * ∑ k : ZMod M, omega k * (dft P Z k * (starRingEnd ℂ) (dft P B k))
      = ∑ t₁ : ZMod M, ∑ t₂ : ZMod M,
          Z t₁ * (starRingEnd ℂ) (B t₂) * bandKernel P omega (t₁ - t₂) := by
  have hL : (M : ℂ)⁻¹ * ∑ k : ZMod M, omega k * (dft P Z k * (starRingEnd ℂ) (dft P B k))
      = ∑ k : ZMod M, ∑ t₁ : ZMod M, ∑ t₂ : ZMod M,
          (M : ℂ)⁻¹ * (omega k *
            (Z t₁ * (starRingEnd ℂ) (B t₂) * P.e (-(k * (t₁ - t₂))))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dft_pair_expand P Z B k, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t₁ _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
  have hR : ∑ t₁ : ZMod M, ∑ t₂ : ZMod M,
        Z t₁ * (starRingEnd ℂ) (B t₂) * bandKernel P omega (t₁ - t₂)
      = ∑ t₁ : ZMod M, ∑ t₂ : ZMod M, ∑ k : ZMod M,
          (M : ℂ)⁻¹ * (omega k *
            (Z t₁ * (starRingEnd ℂ) (B t₂) * P.e (-(k * (t₁ - t₂))))) := by
    refine Finset.sum_congr rfl fun t₁ _ => Finset.sum_congr rfl fun t₂ _ => ?_
    rw [bandKernel, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  rw [hL, hR]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [Finset.sum_comm]

/-- Regrouping the double sum by `r = t₁ - t₂`. -/
theorem shiftKernelSum_regroup (P : AddPhase M) (omega Z B : ZMod M → ℂ) :
    ∑ t₁ : ZMod M, ∑ t₂ : ZMod M,
        Z t₁ * (starRingEnd ℂ) (B t₂) * bandKernel P omega (t₁ - t₂)
      = ∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r := by
  rw [Finset.sum_comm]
  have hinner : ∀ t₂ : ZMod M,
      ∑ t₁ : ZMod M, Z t₁ * (starRingEnd ℂ) (B t₂) * bandKernel P omega (t₁ - t₂)
        = ∑ r : ZMod M,
            bandKernel P omega r * (Z (t₂ + r) * (starRingEnd ℂ) (B t₂)) := by
    intro t₂
    refine (Fintype.sum_equiv (Equiv.addLeft t₂) _ _ ?_).symm
    intro r
    simp only [Equiv.coe_addLeft]
    have : t₂ + r - t₂ = r := by ring
    rw [this]
    ring
  calc ∑ t₂ : ZMod M, ∑ t₁ : ZMod M,
        Z t₁ * (starRingEnd ℂ) (B t₂) * bandKernel P omega (t₁ - t₂)
      = ∑ t₂ : ZMod M, ∑ r : ZMod M,
          bandKernel P omega r * (Z (t₂ + r) * (starRingEnd ℂ) (B t₂)) :=
        Finset.sum_congr rfl fun t₂ _ => hinner t₂
    _ = ∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [shiftCorrelation, Finset.mul_sum]

/-- **Band-to-shift, final form.**  The band pairing is exactly a weighted sum of
shift correlations. -/
theorem bandPairing_eq_shiftSum (P : AddPhase M) (omega Z B : ZMod M → ℂ) :
    (M : ℂ)⁻¹ * ∑ k : ZMod M, omega k * (dft P Z k * (starRingEnd ℂ) (dft P B k))
      = ∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r :=
  (bandPairing_eq_shiftKernelSum P omega Z B).trans
    (shiftKernelSum_regroup P omega Z B)

/-! ## 4. Zero-shift firewall -/

/-- **`zeroShift_survives`.**  The shift decomposition always contains the
`r = 0` packet with coefficient `D(0)`; the remaining shifts are separated. -/
theorem zeroShift_survives (P : AddPhase M) (omega Z B : ZMod M → ℂ) :
    ∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r
      = bandKernel P omega 0 * shiftCorrelation Z B 0
        + ∑ r ∈ Finset.univ.erase (0 : ZMod M),
            bandKernel P omega r * shiftCorrelation Z B r := by
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod M))]

/-- If the band kernel is supported at `0`, the whole band pairing *is* the
native (zero-shift) packet.  Generic Fourier phase variation therefore cannot
remove the native source. -/
theorem zeroShift_isolated (P : AddPhase M) (omega Z B : ZMod M → ℂ)
    (hsupp : ∀ r : ZMod M, r ≠ 0 → bandKernel P omega r = 0) :
    ∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r
      = bandKernel P omega 0 * shiftCorrelation Z B 0 := by
  rw [zeroShift_survives P omega Z B]
  have : ∑ r ∈ Finset.univ.erase (0 : ZMod M),
      bandKernel P omega r * shiftCorrelation Z B r = 0 := by
    refine Finset.sum_eq_zero fun r hr => ?_
    rw [hsupp r (Finset.ne_of_mem_erase hr), zero_mul]
  rw [this, add_zero]

/-- The zero-shift term is genuinely nonzero whenever both factors are. -/
theorem zeroShift_nonzero (P : AddPhase M) (omega Z B : ZMod M → ℂ)
    (hD : bandKernel P omega 0 ≠ 0) (hC : shiftCorrelation Z B 0 ≠ 0) :
    bandKernel P omega 0 * shiftCorrelation Z B 0 ≠ 0 :=
  mul_ne_zero hD hC

/-! ## 5. Anti-`K`-decay counterguard -/

/-- **`phaseVariation_alone_does_not_force_decay`.**  If the coefficients are
allowed to correlate with the phase (take them to be the conjugate phase), a sum
of `N` unit-modulus phases has full size `N`.  Varying phases alone therefore
carry no cancellation. -/
theorem phaseVariation_alone_does_not_force_decay {ι : Type*} [Fintype ι]
    (f : ι → ℂ) (hf : ∀ i, ‖f i‖ = 1) :
    ∑ i : ι, (starRingEnd ℂ) (f i) * f i = (Fintype.card ι : ℂ) := by
  have hterm : ∀ i : ι, (starRingEnd ℂ) (f i) * f i = 1 := by
    intro i
    rw [mul_comm, Complex.mul_conj]
    have : Complex.normSq (f i) = 1 := by
      rw [Complex.normSq_eq_norm_sq, hf i]; norm_num
    rw [this]
    norm_num
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hterm i]
  simp [Finset.card_univ]

/-- Non-vacuity of the counterguard: the phases really do vary in the example
`f(k) = i^k` on `ZMod 4`, yet the correlated sum is full size. -/
theorem phaseVariation_counterguard_nonvacuous :
    ∃ f : Fin 4 → ℂ, (∀ i, ‖f i‖ = 1) ∧ (∃ i j, f i ≠ f j) ∧
      ∑ i : Fin 4, (starRingEnd ℂ) (f i) * f i = 4 := by
  refine ⟨fun i => Complex.I ^ (i : ℕ), ?_, ⟨0, 1, ?_⟩, ?_⟩
  · intro i
    rw [norm_pow, Complex.norm_I, one_pow]
  · simp [Complex.ext_iff]
  · have h := phaseVariation_alone_does_not_force_decay
      (fun i : Fin 4 => Complex.I ^ (i : ℕ)) (by
        intro i; rw [norm_pow, Complex.norm_I, one_pow])
    rw [h]
    norm_num

/-! ## 6. Analytic localisation interface (uninhabited) -/

/-- **`BandKernelLocalizationInput`.**  The external analytic fact that the band
kernel is localised at short shifts, together with an explicit `L¹` budget.

`OPEN_ANALYTIC` — never inhabited in this repository.  In particular no
`K`-decay of the *pairing* is claimed: the interface only bounds the kernel. -/
structure BandKernelLocalizationInput (M : ℕ) [NeZero M] where
  /-- The phase datum. -/
  phase : AddPhase M
  /-- The band weight. -/
  omega : ZMod M → ℂ
  /-- The band width. -/
  K : ℝ
  /-- The decay exponent. -/
  A : ℕ
  /-- The abstract shift size `|r|`. -/
  shiftSize : ZMod M → ℝ
  /-- Shift sizes are nonnegative. -/
  shiftSize_nonneg : ∀ r, 0 ≤ shiftSize r
  /-- The localisation bound. -/
  localisation : ∀ r, ‖bandKernel phase omega r‖
    ≤ (K / M) / (1 + K * shiftSize r / M) ^ A
  /-- The `L¹` budget of the kernel. -/
  kernelL1Budget : ℝ
  /-- The `L¹` bound. -/
  l1_bound : ∑ r : ZMod M, ‖bandKernel phase omega r‖ ≤ kernelL1Budget

/-- Any `L¹` budget in the interface is nonnegative; in particular the interface
is empty for a negative budget, so it cannot be manufactured. -/
theorem bandKernelLocalization_budget_nonneg (I : BandKernelLocalizationInput M) :
    0 ≤ I.kernelL1Budget :=
  le_trans (Finset.sum_nonneg fun _ _ => norm_nonneg _) I.l1_bound

/-- **`bandKernelLocalization_not_automatic`.**  For a negative `L¹` budget the
localisation interface is provably empty. -/
theorem bandKernelLocalization_not_automatic :
    IsEmpty {I : BandKernelLocalizationInput M // I.kernelL1Budget = -1} := by
  constructor
  rintro ⟨I, hI⟩
  have := bandKernelLocalization_budget_nonneg I
  rw [hI] at this
  norm_num at this

/-- **`kernelL1_does_not_give_K_decay`.**  An `L¹` budget alone yields only the
trivial bound `|∑_r D(r) C(r)| ≤ budget · max|C|`; no `K`-power saving follows.
This is the exact logical content of the retired frequency-gain lane. -/
theorem kernelL1_gives_only_trivial_bound (P : AddPhase M) (omega Z B : ZMod M → ℂ)
    (budget cmax : ℝ) (hbudget : ∑ r : ZMod M, ‖bandKernel P omega r‖ ≤ budget)
    (hcmax : ∀ r, ‖shiftCorrelation Z B r‖ ≤ cmax) (hcmax0 : 0 ≤ cmax) :
    ‖∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r‖ ≤ budget * cmax := by
  calc ‖∑ r : ZMod M, bandKernel P omega r * shiftCorrelation Z B r‖
      ≤ ∑ r : ZMod M, ‖bandKernel P omega r * shiftCorrelation Z B r‖ :=
        norm_sum_le _ _
    _ = ∑ r : ZMod M, ‖bandKernel P omega r‖ * ‖shiftCorrelation Z B r‖ := by
        refine Finset.sum_congr rfl fun r _ => norm_mul _ _
    _ ≤ ∑ r : ZMod M, ‖bandKernel P omega r‖ * cmax := by
        refine Finset.sum_le_sum fun r _ => ?_
        exact mul_le_mul_of_nonneg_left (hcmax r) (norm_nonneg _)
    _ = (∑ r : ZMod M, ‖bandKernel P omega r‖) * cmax := by rw [Finset.sum_mul]
    _ ≤ budget * cmax := mul_le_mul_of_nonneg_right hbudget hcmax0

end BandKernel

/-! ## 7. Shift-length ledger and the Mid-`k` / Top-`k` partition -/

namespace ShiftLedger

/-- The shift length `S_K = H/K`. -/
noncomputable def shiftLength (H K : ℝ) : ℝ := H / K

/-- **Monotonicity of the shift length.**  Wider bands mean shorter shifts. -/
theorem shiftLength_antitone (H K₁ K₂ : ℝ) (hH : 0 ≤ H) (hK₁ : 0 < K₁) (h : K₁ ≤ K₂) :
    shiftLength H K₂ ≤ shiftLength H K₁ :=
  div_le_div_of_nonneg_left hH hK₁ h

/-- Abstract thresholds and shift budget for the frequency split.  Nothing here
is logarithmic: `shiftBudget` is an abstract positive parameter. -/
structure FrequencySplit where
  /-- Total frequency length. -/
  H : ℝ
  /-- The small-`k` threshold. -/
  Ksmall : ℝ
  /-- The abstract shift budget separating mid from top. -/
  shiftBudget : ℝ
  /-- Positivity of `H`. -/
  H_pos : 0 < H
  /-- Positivity of the small threshold. -/
  Ksmall_pos : 0 < Ksmall
  /-- Positivity of the shift budget. -/
  shiftBudget_pos : 0 < shiftBudget

namespace FrequencySplit

variable (F : FrequencySplit)

/-- The mid-`k` band: above the small threshold, with shift length at least the
budget. -/
def MidK (K : ℝ) : Prop := F.Ksmall < K ∧ K ≤ F.H / F.shiftBudget

/-- The top-`k` band: shift length at most the budget. -/
def TopK (K : ℝ) : Prop := F.H / F.shiftBudget < K ∧ K ≤ F.H

/-- Mid-`k` metadata: shift length is at least the budget. -/
theorem midK_shift_ge (K : ℝ) (hK : 0 < K) (h : F.MidK K) :
    F.shiftBudget ≤ shiftLength F.H K := by
  obtain ⟨-, hle⟩ := h
  rw [shiftLength, le_div_iff₀ hK]
  rw [le_div_iff₀ F.shiftBudget_pos] at hle
  linarith [hle]

/-- Top-`k` metadata: shift length is at most the budget. -/
theorem topK_shift_le (K : ℝ) (hK : 0 < K) (h : F.TopK K) :
    shiftLength F.H K ≤ F.shiftBudget := by
  obtain ⟨hlt, -⟩ := h
  rw [shiftLength, div_le_iff₀ hK]
  rw [div_lt_iff₀ F.shiftBudget_pos] at hlt
  linarith [hlt]

/-- The two high bands are disjoint. -/
theorem midK_topK_disjoint (K : ℝ) : ¬ (F.MidK K ∧ F.TopK K) := by
  rintro ⟨⟨-, hmid⟩, ⟨htop, -⟩⟩
  linarith

/-- The two high bands exhaust the range above the small threshold. -/
theorem midK_topK_exhaustive (K : ℝ) (h1 : F.Ksmall < K) (h2 : K ≤ F.H) :
    F.MidK K ∨ F.TopK K := by
  by_cases hc : K ≤ F.H / F.shiftBudget
  · exact Or.inl ⟨h1, hc⟩
  · exact Or.inr ⟨lt_of_not_ge hc, h2⟩

end FrequencySplit

end ShiftLedger
end CurrentProgramme
end TwinPrimeProject
