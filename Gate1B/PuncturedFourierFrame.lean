import Mathlib

/-!
# Gate 1B · punctured finite Fourier frame and the product-Fourier operator

**Everything in this module is exact finite linear algebra over `ZMod M`.**
No analytic estimate is proved here, none is assumed, and no analytic
interface is inhabited.

## Contents

* §0 the standard additive character `e_M` and its punctured character sum;
* §1 the **punctured Fourier frame** `V(r,k) = e_M(k r)`, `r ∈ I`, `k ≠ 0`,
  its Gram identity `V Vᴴ = M·1 − J`, positivity for `#I < M`, full row rank,
  surjectivity and the minimal-norm coefficient bound
  `‖c‖² · (M − #I) ≤ ‖F‖²`;
* §2 the **unit-dilated frame** `V_ℓ(r,k) = e_M(k ℓ r)`, whose Gram is
  identical to the undilated one;
* §5 the **finite product-Fourier operator** `T_λ(r,s) = e_M(λ r s)` and its
  exact orthogonality `T_λᴴ T_λ = M·1`.

The analytic consequence `‖T_λ‖ = √M` of §5 is *not* formalised here; only the
exact Gram identity and the exact Plancherel identity are.  (`√M` is recorded
in the report as an analytic consequence, not as a Lean theorem.)
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace PuncturedFourier

open Finset
open scoped Matrix

variable {M : ℕ} [NeZero M]

/-! ## 0. The standard additive character and the punctured character sum -/

/-- The standard additive character `e_M` of `ZMod M`. -/
noncomputable def eM (M : ℕ) [NeZero M] : AddChar (ZMod M) ℂ := ZMod.stdAddChar

@[simp] theorem eM_zero : eM M 0 = 1 := by simp [eM]

theorem eM_add (x y : ZMod M) : eM M (x + y) = eM M x * eM M y :=
  AddChar.map_add_eq_mul _ _ _

theorem eM_conj (x : ZMod M) : (starRingEnd ℂ) (eM M x) = eM M (-x) :=
  (AddChar.map_neg_eq_conj _ _).symm

/-- Complete additive-character orthogonality on `ZMod M`. -/
theorem full_char_sum (b : ZMod M) :
    ∑ k : ZMod M, eM M (k * b) = (if b = 0 then (M : ℂ) else 0) := by
  classical
  rw [eM, AddChar.sum_mulShift b (ZMod.isPrimitive_stdAddChar M)]
  split <;> simp [ZMod.card]

/-- The set of **nonzero** frequencies mod `M`. -/
def nzFreq (M : ℕ) [NeZero M] : Finset (ZMod M) := Finset.univ.erase 0

@[simp] theorem mem_nzFreq {k : ZMod M} : k ∈ nzFreq M ↔ k ≠ 0 := by
  simp [nzFreq]

/-- **Punctured character sum.**  Removing the zero frequency costs exactly `1`. -/
theorem punctured_char_sum (b : ZMod M) :
    ∑ k ∈ nzFreq M, eM M (k * b) = (if b = 0 then (M : ℂ) else 0) - 1 := by
  classical
  rw [nzFreq, Finset.sum_erase_eq_sub (Finset.mem_univ (0 : ZMod M)), full_char_sum]
  simp

/-! ## 1. The punctured Fourier frame -/

/-- **`puncturedFourier_gram`.**  The Gram entry of the punctured frame:

`(V Vᴴ)(r,r') = M·1_{r=r'} − 1`. -/
theorem puncturedFourier_gram (r r' : ZMod M) :
    ∑ k ∈ nzFreq M, eM M (k * r) * (starRingEnd ℂ) (eM M (k * r'))
      = (if r = r' then (M : ℂ) else 0) - 1 := by
  classical
  have h : ∀ k : ZMod M,
      eM M (k * r) * (starRingEnd ℂ) (eM M (k * r')) = eM M (k * (r - r')) := by
    intro k
    rw [eM_conj, ← eM_add]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => h k), punctured_char_sum]
  simp [sub_eq_zero]

/-- The analysis operator of the punctured frame:
`c(k) = ∑_{r ∈ I} y(r) · conj e_M(k r)`. -/
noncomputable def anal (I : Finset (ZMod M)) (y : ZMod M → ℂ) (k : ZMod M) : ℂ :=
  ∑ r ∈ I, y r * (starRingEnd ℂ) (eM M (k * r))

/-- Synthesis after analysis reproduces `M·y(r) − ∑ y` exactly (this is the
`M·1 − J` Gram identity in operator form). -/
theorem synth_anal (I : Finset (ZMod M)) (y : ZMod M → ℂ) {r : ZMod M} (hr : r ∈ I) :
    ∑ k ∈ nzFreq M, anal I y k * eM M (k * r) = (M : ℂ) * y r - ∑ r' ∈ I, y r' := by
  classical
  have expand : ∀ k : ZMod M, anal I y k * eM M (k * r)
      = ∑ r' ∈ I, y r' * (eM M (k * r) * (starRingEnd ℂ) (eM M (k * r'))) := by
    intro k
    simp only [anal, Finset.sum_mul]
    exact Finset.sum_congr rfl fun r' _ => by ring
  rw [Finset.sum_congr rfl (fun k _ => expand k), Finset.sum_comm]
  have step : ∀ r' ∈ I,
      ∑ k ∈ nzFreq M, y r' * (eM M (k * r) * (starRingEnd ℂ) (eM M (k * r')))
        = (if r = r' then (M : ℂ) else 0) * y r' - y r' := by
    intro r' _
    rw [← Finset.mul_sum, puncturedFourier_gram r r']
    ring
  rw [Finset.sum_congr rfl step, Finset.sum_sub_distrib]
  congr 1
  simp [Finset.sum_ite_eq I r (fun r' => (M : ℂ) * y r'), hr]

/-- **Exact frame energy identity** (complex form):
`∑_{k≠0} |c(k)|² = M ∑_{r∈I} |y(r)|² − |∑_{r∈I} y(r)|²`. -/
theorem frame_energy_identity (I : Finset (ZMod M)) (y : ZMod M → ℂ) :
    ∑ k ∈ nzFreq M, anal I y k * (starRingEnd ℂ) (anal I y k)
      = (M : ℂ) * (∑ r ∈ I, y r * (starRingEnd ℂ) (y r))
        - (∑ r ∈ I, y r) * (starRingEnd ℂ) (∑ r ∈ I, y r) := by
  classical
  have expand : ∀ k : ZMod M, anal I y k * (starRingEnd ℂ) (anal I y k)
      = ∑ r ∈ I, ∑ r' ∈ I, (y r * (starRingEnd ℂ) (y r')) *
          ((starRingEnd ℂ) (eM M (k * r)) * eM M (k * r')) := by
    intro k
    simp only [anal, map_sum, map_mul, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => by ring
  rw [Finset.sum_congr rfl (fun k _ => expand k), Finset.sum_comm]
  have inner : ∀ r ∈ I, ∑ k ∈ nzFreq M, ∑ r' ∈ I, (y r * (starRingEnd ℂ) (y r')) *
        ((starRingEnd ℂ) (eM M (k * r)) * eM M (k * r'))
      = ∑ r' ∈ I, (y r * (starRingEnd ℂ) (y r')) * ((if r' = r then (M : ℂ) else 0) - 1) := by
    intro r _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun r' _ => ?_
    rw [← Finset.mul_sum]
    congr 1
    rw [← puncturedFourier_gram r' r]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl inner]
  have step : ∀ r ∈ I,
      ∑ r' ∈ I, (y r * (starRingEnd ℂ) (y r')) * ((if r' = r then (M : ℂ) else 0) - 1)
        = (M : ℂ) * (y r * (starRingEnd ℂ) (y r))
          - y r * (starRingEnd ℂ) (∑ r' ∈ I, y r') := by
    intro r hr
    have h : ∀ r' ∈ I, (y r * (starRingEnd ℂ) (y r')) * ((if r' = r then (M : ℂ) else 0) - 1)
        = (if r' = r then (M : ℂ) * (y r * (starRingEnd ℂ) (y r')) else 0)
          - y r * (starRingEnd ℂ) (y r') := by
      intro r' _
      by_cases hrr : r' = r <;> (simp [hrr]; try ring)
    rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_ite_eq' I r
      (fun r' => (M : ℂ) * (y r * (starRingEnd ℂ) (y r')))]
    simp [hr, map_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl step, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- Casting a real square-norm sum into `ℂ`. -/
theorem ofReal_sum_normSq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ((∑ i ∈ s, ‖f i‖ ^ 2 : ℝ) : ℂ) = ∑ i ∈ s, f i * (starRingEnd ℂ) (f i) := by
  push_cast
  exact Finset.sum_congr rfl fun i _ => (Complex.mul_conj' (f i)).symm

/-- **Exact frame energy identity** (real form). -/
theorem frame_energy_real (I : Finset (ZMod M)) (y : ZMod M → ℂ) :
    ∑ k ∈ nzFreq M, ‖anal I y k‖ ^ 2
      = (M : ℝ) * (∑ r ∈ I, ‖y r‖ ^ 2) - ‖∑ r ∈ I, y r‖ ^ 2 := by
  have h := frame_energy_identity I y
  rw [← ofReal_sum_normSq, ← ofReal_sum_normSq, Complex.mul_conj'] at h
  exact_mod_cast h

omit [NeZero M] in
/-- Cauchy–Schwarz on a finite set. -/
theorem normSq_sum_le_card_mul (I : Finset (ZMod M)) (F : ZMod M → ℂ) :
    ‖∑ r ∈ I, F r‖ ^ 2 ≤ I.card * ∑ r ∈ I, ‖F r‖ ^ 2 := by
  have h1 : ‖∑ r ∈ I, F r‖ ≤ ∑ r ∈ I, ‖F r‖ := norm_sum_le _ _
  calc ‖∑ r ∈ I, F r‖ ^ 2 ≤ (∑ r ∈ I, ‖F r‖) ^ 2 := by gcongr
    _ ≤ I.card * ∑ r ∈ I, ‖F r‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- **`puncturedFourier_posDef`.**  On a set `I` with `#I < M` the punctured
Gram matrix `M·1 − J` is positive definite, in the quantitative form

`(M − #I) ‖y‖² ≤ ∑_{k ≠ 0} |c(k)|²`. -/
theorem puncturedFourier_posDef (I : Finset (ZMod M)) (y : ZMod M → ℂ) :
    ((M : ℝ) - I.card) * (∑ r ∈ I, ‖y r‖ ^ 2) ≤ ∑ k ∈ nzFreq M, ‖anal I y k‖ ^ 2 := by
  rw [frame_energy_real]
  have := normSq_sum_le_card_mul I y
  nlinarith [this]

/-- The source form of the positivity statement: under `2·#I < M` the punctured
Gram form dominates `(M/2)‖y‖²`. -/
theorem puncturedFourier_posDef_of_two_card_lt (I : Finset (ZMod M))
    (h : 2 * I.card < M) (y : ZMod M → ℂ) :
    ((M : ℝ) / 2) * (∑ r ∈ I, ‖y r‖ ^ 2) ≤ ∑ k ∈ nzFreq M, ‖anal I y k‖ ^ 2 := by
  have hle := puncturedFourier_posDef I y
  have hcard : 2 * (I.card : ℝ) < M := by exact_mod_cast h
  have hnn : (0 : ℝ) ≤ ∑ r ∈ I, ‖y r‖ ^ 2 :=
    Finset.sum_nonneg fun r _ => by positivity
  nlinarith [hle, hcard, hnn]

/-- Strict positivity: if some coordinate of `y` on `I` is nonzero and `#I < M`,
the punctured frame energy is strictly positive. -/
theorem puncturedFourier_posDef_strict (I : Finset (ZMod M)) (hI : I.card < M)
    (y : ZMod M → ℂ) {r₀ : ZMod M} (hr₀ : r₀ ∈ I) (hy : y r₀ ≠ 0) :
    0 < ∑ k ∈ nzFreq M, ‖anal I y k‖ ^ 2 := by
  have hpos : 0 < ((M : ℝ) - I.card) := by
    have : (I.card : ℝ) < M := by exact_mod_cast hI
    linarith
  have hsum : 0 < ∑ r ∈ I, ‖y r‖ ^ 2 := by
    refine Finset.sum_pos' (fun r _ => by positivity) ⟨r₀, hr₀, ?_⟩
    have : ‖y r₀‖ ≠ 0 := norm_ne_zero_iff.2 hy
    positivity
  exact lt_of_lt_of_le (by positivity) (puncturedFourier_posDef I y)

/-! ### The minimal-norm coefficient theorem -/

private theorem algebra_sum_step (Mc S D n : ℂ) (hM : Mc ≠ 0) (hD : D ≠ 0)
    (hn : n = Mc - D) : (S + n * (S / D)) / Mc = S / D := by
  subst hn; field_simp; ring

private theorem algebra_energy_step (Mc Q S Sc D n : ℂ) (hM : Mc ≠ 0) (hD : D ≠ 0)
    (hn : n = Mc - D) :
    Mc * ((Q + (Sc / D) * S + (S / D) * Sc + n * ((S / D) * (Sc / D))) / (Mc * Mc))
        - (S / D) * (Sc / D)
      = Q / Mc + S * Sc / (Mc * D) := by
  subst hn; field_simp; ring

/-- **`puncturedFourier_minNorm_coeff_bound`.**

For every `F` defined on `I` with `#I < M` there is a coefficient vector `c`
supported on the **nonzero** frequencies with

* `F(r) = ∑_{k ≠ 0} c(k) e_M(k r)` for every `r ∈ I`, and
* `‖c‖₂² · (M − #I) ≤ ‖F‖₂²`,

i.e. `‖c‖₂² ≤ ‖F‖₂² / (M − #I)`.  The bound is stated in the multiplied-out
form to avoid a division; the divided form is `puncturedFourier_minNorm_div`. -/
theorem puncturedFourier_minNorm_coeff_bound (I : Finset (ZMod M)) (hI : I.card < M)
    (F : ZMod M → ℂ) :
    ∃ c : ZMod M → ℂ, c 0 = 0 ∧
      (∀ r ∈ I, ∑ k ∈ nzFreq M, c k * eM M (k * r) = F r) ∧
      (∑ k ∈ nzFreq M, ‖c k‖ ^ 2) * ((M : ℝ) - I.card) ≤ ∑ r ∈ I, ‖F r‖ ^ 2 := by
  classical
  obtain ⟨D, hDdef⟩ : ∃ D : ℂ, D = (M : ℂ) - (I.card : ℂ) := ⟨_, rfl⟩
  have hMne : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne M)
  have hDne : D ≠ 0 := by
    rw [hDdef, sub_ne_zero]
    exact_mod_cast (Nat.ne_of_lt hI).symm
  have hnD : ((I.card : ℂ)) = (M : ℂ) - D := by rw [hDdef]; ring
  obtain ⟨S, hSdef⟩ : ∃ S : ℂ, S = ∑ r ∈ I, F r := ⟨_, rfl⟩
  obtain ⟨y, hydef⟩ : ∃ y : ZMod M → ℂ, y = fun r => (F r + S / D) / M := ⟨_, rfl⟩
  have hsumy : ∑ r ∈ I, y r = S / D := by
    have h1 : ∑ r ∈ I, y r = (S + (I.card : ℂ) * (S / D)) / M := by
      simp only [hydef, ← Finset.sum_div]
      rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← hSdef]
    rw [h1, algebra_sum_step (M : ℂ) S D (I.card : ℂ) hMne hDne hnD]
  obtain ⟨c, hcdef⟩ : ∃ c : ZMod M → ℂ, c = fun k => if k = 0 then 0 else anal I y k :=
    ⟨_, rfl⟩
  have hcnz : ∀ k ∈ nzFreq M, c k = anal I y k := by
    intro k hk
    have hk0 : k ≠ 0 := mem_nzFreq.1 hk
    simp [hcdef, hk0]
  refine ⟨c, by simp [hcdef], ?_, ?_⟩
  · intro r hr
    rw [Finset.sum_congr rfl (fun k hk => by rw [hcnz k hk]), synth_anal I y hr, hsumy]
    simp only [hydef]
    field_simp
    ring
  · -- the exact energy identity, then Cauchy–Schwarz
    have hconjD : (starRingEnd ℂ) D = D := by rw [hDdef]; simp
    have hSc : ∑ r ∈ I, (starRingEnd ℂ) (F r) = (starRingEnd ℂ) S := by
      rw [hSdef, map_sum]
    have hexpand : ∑ r ∈ I, y r * (starRingEnd ℂ) (y r)
        = ((∑ r ∈ I, F r * (starRingEnd ℂ) (F r)) + ((starRingEnd ℂ) S / D) * S
            + (S / D) * (starRingEnd ℂ) S
            + (I.card : ℂ) * ((S / D) * ((starRingEnd ℂ) S / D))) / ((M : ℂ) * M) := by
      have hterm : ∀ r : ZMod M, y r * (starRingEnd ℂ) (y r)
          = ((F r + S / D) * ((starRingEnd ℂ) (F r) + (starRingEnd ℂ) S / D))
              / ((M : ℂ) * M) := by
        intro r
        simp only [hydef, map_div₀, map_add, Complex.conj_natCast, hconjD]
        ring
      rw [Finset.sum_congr rfl (fun r _ => hterm r), ← Finset.sum_div]
      congr 1
      simp only [add_mul, mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
        Finset.sum_const, nsmul_eq_mul, hSc, ← hSdef]
      ring
    have hEC : ∑ k ∈ nzFreq M, c k * (starRingEnd ℂ) (c k)
        = (∑ r ∈ I, F r * (starRingEnd ℂ) (F r)) / M
            + S * (starRingEnd ℂ) S / ((M : ℂ) * D) := by
      rw [Finset.sum_congr rfl (fun k hk => by rw [hcnz k hk]), frame_energy_identity,
        hsumy, hexpand, map_div₀, hconjD]
      exact algebra_energy_step (M : ℂ) (∑ r ∈ I, F r * (starRingEnd ℂ) (F r)) S
        ((starRingEnd ℂ) S) D (I.card : ℂ) hMne hDne hnD
    -- pass to the real identity
    have hreal : ∑ k ∈ nzFreq M, ‖c k‖ ^ 2
        = (∑ r ∈ I, ‖F r‖ ^ 2) / M + ‖S‖ ^ 2 / ((M : ℝ) * ((M : ℝ) - I.card)) := by
      have hc2 : ((∑ k ∈ nzFreq M, ‖c k‖ ^ 2 : ℝ) : ℂ)
          = ((((∑ r ∈ I, ‖F r‖ ^ 2) / M + ‖S‖ ^ 2 / ((M : ℝ) * ((M : ℝ) - I.card))) : ℝ) : ℂ) := by
        rw [ofReal_sum_normSq, hEC]
        push_cast
        rw [hDdef, Complex.mul_conj',
          Finset.sum_congr rfl (fun r (_ : r ∈ I) => Complex.mul_conj' (F r))]
      exact_mod_cast hc2
    have hMpos : (0 : ℝ) < M := by
      have := NeZero.pos M
      exact_mod_cast this
    have hdpos : (0 : ℝ) < (M : ℝ) - I.card := by
      have : (I.card : ℝ) < M := by exact_mod_cast hI
      linarith
    have hCS : ‖S‖ ^ 2 ≤ (I.card : ℝ) * ∑ r ∈ I, ‖F r‖ ^ 2 := by
      rw [hSdef]; exact normSq_sum_le_card_mul I F
    have key : ((∑ r ∈ I, ‖F r‖ ^ 2) / M + ‖S‖ ^ 2 / ((M : ℝ) * ((M : ℝ) - I.card)))
          * ((M : ℝ) - I.card)
        = ((∑ r ∈ I, ‖F r‖ ^ 2) * ((M : ℝ) - I.card) + ‖S‖ ^ 2) / M := by
      field_simp
    rw [hreal, key, div_le_iff₀ hMpos]
    nlinarith [hCS]

/-- The divided form of the minimal-norm coefficient bound. -/
theorem puncturedFourier_minNorm_div (I : Finset (ZMod M)) (hI : I.card < M)
    (F : ZMod M → ℂ) :
    ∃ c : ZMod M → ℂ, c 0 = 0 ∧
      (∀ r ∈ I, ∑ k ∈ nzFreq M, c k * eM M (k * r) = F r) ∧
      (∑ k ∈ nzFreq M, ‖c k‖ ^ 2) ≤ (∑ r ∈ I, ‖F r‖ ^ 2) / ((M : ℝ) - I.card) := by
  obtain ⟨c, hc0, hrec, hbd⟩ := puncturedFourier_minNorm_coeff_bound I hI F
  refine ⟨c, hc0, hrec, ?_⟩
  have hdpos : (0 : ℝ) < (M : ℝ) - I.card := by
    have : (I.card : ℝ) < M := by exact_mod_cast hI
    linarith
  rw [le_div_iff₀ hdpos]
  exact hbd

/-- **`puncturedFourier_surjective`.**  Every function on `I` is realised by
frequencies away from `0`. -/
theorem puncturedFourier_surjective (I : Finset (ZMod M)) (hI : I.card < M)
    (F : ZMod M → ℂ) :
    ∃ c : ZMod M → ℂ, c 0 = 0 ∧ ∀ r ∈ I, ∑ k ∈ nzFreq M, c k * eM M (k * r) = F r := by
  obtain ⟨c, hc0, hrec, -⟩ := puncturedFourier_minNorm_coeff_bound I hI F
  exact ⟨c, hc0, hrec⟩

/-! ### Matrix form: `V Vᴴ = M·1 − J` -/

/-- The punctured Fourier matrix `V(r,k) = e_M(k r)`, rows indexed by `I`,
columns by the nonzero frequencies. -/
noncomputable def puncturedMatrix (I : Finset (ZMod M)) :
    Matrix I (nzFreq M) ℂ :=
  Matrix.of fun r k => eM M ((k : ZMod M) * (r : ZMod M))

/-- The all-ones matrix `J`. -/
def onesMatrix (I : Finset (ZMod M)) : Matrix I I ℂ := Matrix.of fun _ _ => 1

/-- **`V Vᴴ = M·1 − J`.** -/
theorem puncturedFourier_gram_matrix (I : Finset (ZMod M)) :
    puncturedMatrix I * (puncturedMatrix I)ᴴ
      = (M : ℂ) • (1 : Matrix I I ℂ) - onesMatrix I := by
  classical
  ext r r'
  rw [Matrix.mul_apply]
  have hcast : ∑ k : (nzFreq M), puncturedMatrix I r k * (puncturedMatrix I)ᴴ k r'
      = ∑ k ∈ nzFreq M, eM M (k * (r : ZMod M)) * (starRingEnd ℂ) (eM M (k * (r' : ZMod M))) := by
    rw [← Finset.sum_coe_sort (nzFreq M)]
    rfl
  rw [hcast, puncturedFourier_gram]
  by_cases h : (r : ZMod M) = (r' : ZMod M)
  · have : r = r' := Subtype.ext h
    subst this
    simp [onesMatrix]
  · have hne : r ≠ r' := fun hh => h (by rw [hh])
    simp [onesMatrix, h, hne]

/-- The matrix `V` has full row rank `#I` as soon as `#I < M`. -/
theorem puncturedFourier_fullRowRank (I : Finset (ZMod M)) (hI : I.card < M) :
    (puncturedMatrix I).rank = I.card := by
  classical
  have hsurj : Function.Surjective (puncturedMatrix I).mulVecLin := by
    intro G
    obtain ⟨c, -, hrec⟩ :=
      puncturedFourier_surjective I hI (fun r => if h : r ∈ I then G ⟨r, h⟩ else 0)
    refine ⟨fun k => c (k : ZMod M), ?_⟩
    funext r
    have hr : (r : ZMod M) ∈ I := r.2
    have := hrec (r : ZMod M) hr
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, puncturedMatrix, Matrix.of_apply,
      dotProduct]
    rw [← Finset.sum_coe_sort (nzFreq M)] at this
    rw [show (∑ k : (nzFreq M), eM M ((k : ZMod M) * (r : ZMod M)) * c (k : ZMod M))
        = ∑ k : (nzFreq M), c (k : ZMod M) * eM M ((k : ZMod M) * (r : ZMod M)) from
      Finset.sum_congr rfl fun k _ => by ring]
    rw [this]
    simp [hr]
  rw [Matrix.rank, LinearMap.range_eq_top.2 hsurj, finrank_top]
  simp

/-! ## 2. The unit-dilated frame -/

/-- The dilated punctured frame `V_ℓ(r,k) = e_M(k ℓ r)`. -/
noncomputable def dilatedMatrix (I : Finset (ZMod M)) (l : ZMod M) :
    Matrix I (nzFreq M) ℂ :=
  Matrix.of fun r k => eM M ((k : ZMod M) * (l * (r : ZMod M)))

/-- **`puncturedFourier_unitDilate_gram`.**  For a unit `ℓ` the dilated frame
has exactly the same Gram as the undilated one. -/
theorem puncturedFourier_unitDilate_gram (l : ZMod M) (hl : IsUnit l) (r r' : ZMod M) :
    ∑ k ∈ nzFreq M, eM M (k * (l * r)) * (starRingEnd ℂ) (eM M (k * (l * r')))
      = (if r = r' then (M : ℂ) else 0) - 1 := by
  classical
  have h : ∀ k : ZMod M,
      eM M (k * (l * r)) * (starRingEnd ℂ) (eM M (k * (l * r'))) = eM M (k * (l * (r - r'))) := by
    intro k
    rw [eM_conj, ← eM_add]
    ring_nf
  rw [Finset.sum_congr rfl (fun k _ => h k), punctured_char_sum]
  have hiff : l * (r - r') = 0 ↔ r = r' := by
    constructor
    · intro h0
      obtain ⟨u, hu⟩ := hl
      have : r - r' = 0 := by
        have := congrArg (fun x => (↑u⁻¹ : ZMod M) * x) h0
        simpa [← hu, ← mul_assoc, ZMod.inv_mul_of_unit] using this
      exact sub_eq_zero.1 this
    · intro h0; simp [h0]
  simp [hiff]

/-- The dilated Gram matrix is literally the undilated one. -/
theorem puncturedFourier_unitDilate_gram_matrix (I : Finset (ZMod M)) (l : ZMod M)
    (hl : IsUnit l) :
    dilatedMatrix I l * (dilatedMatrix I l)ᴴ
      = (M : ℂ) • (1 : Matrix I I ℂ) - onesMatrix I := by
  classical
  ext r r'
  rw [Matrix.mul_apply]
  have hcast : ∑ k : (nzFreq M), dilatedMatrix I l r k * (dilatedMatrix I l)ᴴ k r'
      = ∑ k ∈ nzFreq M, eM M (k * (l * (r : ZMod M)))
          * (starRingEnd ℂ) (eM M (k * (l * (r' : ZMod M)))) := by
    rw [← Finset.sum_coe_sort (nzFreq M)]
    rfl
  rw [hcast, puncturedFourier_unitDilate_gram l hl]
  by_cases h : (r : ZMod M) = (r' : ZMod M)
  · have : r = r' := Subtype.ext h
    subst this
    simp [onesMatrix]
  · have hne : r ≠ r' := fun hh => h (by rw [hh])
    simp [onesMatrix, h, hne]

/-- The dilated Gram matrix is literally the undilated Gram matrix. -/
theorem puncturedFourier_unitDilate_gram_eq (I : Finset (ZMod M)) (l : ZMod M)
    (hl : IsUnit l) :
    (dilatedMatrix I l) * (dilatedMatrix I l)ᴴ = puncturedMatrix I * (puncturedMatrix I)ᴴ := by
  rw [puncturedFourier_unitDilate_gram_matrix I l hl, puncturedFourier_gram_matrix I]

/-- Surjectivity of the dilated punctured frame. -/
theorem puncturedFourier_unitDilate_surjective (I : Finset (ZMod M)) (hI : I.card < M)
    (l : ZMod M) (hl : IsUnit l) (F : ZMod M → ℂ) :
    ∃ c : ZMod M → ℂ, c 0 = 0 ∧
      ∀ r ∈ I, ∑ k ∈ nzFreq M, c k * eM M (k * (l * r)) = F r := by
  classical
  obtain ⟨u, hu⟩ := hl
  have hinj : Set.InjOn (fun r : ZMod M => l * r) I := by
    intro a _ b _ hab
    have := congrArg (fun x => ((↑u⁻¹ : ZMod M) * x)) hab
    simpa [← hu, ← mul_assoc, ZMod.inv_mul_of_unit] using this
  have hcard : (I.image (fun r : ZMod M => l * r)).card = I.card :=
    Finset.card_image_of_injOn hinj
  obtain ⟨c, hc0, hrec⟩ :=
    puncturedFourier_surjective (I.image (fun r : ZMod M => l * r)) (by rw [hcard]; exact hI)
      (fun s => F ((↑u⁻¹ : ZMod M) * s))
  refine ⟨c, hc0, fun r hr => ?_⟩
  have hmem : l * r ∈ I.image (fun r : ZMod M => l * r) := Finset.mem_image_of_mem _ hr
  have hval := hrec (l * r) hmem
  have hid : ((↑u⁻¹ : ZMod M) * (l * r)) = r := by
    simp [← hu, ← mul_assoc]
  rw [hid] at hval
  exact hval

/-- **`puncturedFourier_unitDilate_rank`.**  The dilated frame has the same full
row rank `#I`. -/
theorem puncturedFourier_unitDilate_rank (I : Finset (ZMod M)) (hI : I.card < M)
    (l : ZMod M) (hl : IsUnit l) :
    (dilatedMatrix I l).rank = I.card := by
  classical
  have hsurj : Function.Surjective (dilatedMatrix I l).mulVecLin := by
    intro G
    obtain ⟨c, -, hrec⟩ :=
      puncturedFourier_unitDilate_surjective I hI l hl
        (fun r => if h : r ∈ I then G ⟨r, h⟩ else 0)
    refine ⟨fun k => c (k : ZMod M), ?_⟩
    funext r
    have hr : (r : ZMod M) ∈ I := r.2
    have hval := hrec (r : ZMod M) hr
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dilatedMatrix, Matrix.of_apply,
      dotProduct]
    rw [← Finset.sum_coe_sort (nzFreq M)] at hval
    rw [show (∑ k : (nzFreq M), eM M ((k : ZMod M) * (l * (r : ZMod M))) * c (k : ZMod M))
        = ∑ k : (nzFreq M), c (k : ZMod M) * eM M ((k : ZMod M) * (l * (r : ZMod M))) from
      Finset.sum_congr rfl fun k _ => by ring]
    rw [hval]
    simp [hr]
  rw [Matrix.rank, LinearMap.range_eq_top.2 hsurj, finrank_top]
  simp

/-! ## 5. The finite product-Fourier operator -/

/-- The product-Fourier kernel `T_λ(r,s) = e_M(λ r s)`. -/
noncomputable def prodFourier (M : ℕ) [NeZero M] (lam : ZMod M) :
    Matrix (ZMod M) (ZMod M) ℂ :=
  Matrix.of fun r s => eM M (lam * r * s)

/-- **`productFourier_orthogonality`.**  For a unit `λ` the columns of `T_λ`
are exactly orthogonal, with squared norm `M`. -/
theorem productFourier_orthogonality (lam : ZMod M) (hl : IsUnit lam) (s s' : ZMod M) :
    ∑ r : ZMod M, (starRingEnd ℂ) (eM M (lam * r * s)) * eM M (lam * r * s')
      = (if s = s' then (M : ℂ) else 0) := by
  classical
  have h : ∀ r : ZMod M,
      (starRingEnd ℂ) (eM M (lam * r * s)) * eM M (lam * r * s') = eM M (r * (lam * (s' - s))) := by
    intro r
    rw [eM_conj, ← eM_add]
    ring_nf
  rw [Finset.sum_congr rfl (fun r _ => h r), full_char_sum]
  have hiff : lam * (s' - s) = 0 ↔ s = s' := by
    constructor
    · intro h0
      obtain ⟨u, hu⟩ := hl
      have : s' - s = 0 := by
        have := congrArg (fun x => (↑u⁻¹ : ZMod M) * x) h0
        simpa [← hu, ← mul_assoc, ZMod.inv_mul_of_unit] using this
      exact (sub_eq_zero.1 this).symm
    · intro h0; simp [h0]
  simp [hiff]

/-- **`productFourier_gram`.**  `T_λᴴ T_λ = M · 1`. -/
theorem productFourier_gram (lam : ZMod M) (hl : IsUnit lam) :
    (prodFourier M lam)ᴴ * (prodFourier M lam) = (M : ℂ) • (1 : Matrix (ZMod M) (ZMod M) ℂ) := by
  classical
  ext s s'
  rw [Matrix.mul_apply]
  have : ∑ r : ZMod M, (prodFourier M lam)ᴴ s r * (prodFourier M lam) r s'
      = ∑ r : ZMod M, (starRingEnd ℂ) (eM M (lam * r * s)) * eM M (lam * r * s') := rfl
  rw [this, productFourier_orthogonality lam hl]
  by_cases h : s = s' <;> simp [h]

/-- **`productFourier_norm_sq`.**  Exact Plancherel identity for `T_λ`:
`∑_s |∑_r c(r) e_M(λ r s)|² = M ∑_r |c(r)|²`.

The analytic consequence `‖T_λ‖ = √M` is *not* claimed in Lean. -/
theorem productFourier_norm_sq (lam : ZMod M) (hl : IsUnit lam) (c : ZMod M → ℂ) :
    ∑ s : ZMod M, ‖∑ r : ZMod M, c r * eM M (lam * r * s)‖ ^ 2
      = (M : ℝ) * ∑ r : ZMod M, ‖c r‖ ^ 2 := by
  classical
  have hC : ∑ s : ZMod M, (∑ r : ZMod M, c r * eM M (lam * r * s))
        * (starRingEnd ℂ) (∑ r : ZMod M, c r * eM M (lam * r * s))
      = (M : ℂ) * ∑ r : ZMod M, c r * (starRingEnd ℂ) (c r) := by
    have expand : ∀ s : ZMod M, (∑ r : ZMod M, c r * eM M (lam * r * s))
          * (starRingEnd ℂ) (∑ r : ZMod M, c r * eM M (lam * r * s))
        = ∑ r : ZMod M, ∑ r' : ZMod M, (c r * (starRingEnd ℂ) (c r')) *
            (eM M (lam * r * s) * (starRingEnd ℂ) (eM M (lam * r' * s))) := by
      intro s
      simp only [map_sum, map_mul]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun r' _ => by ring
    rw [Finset.sum_congr rfl (fun s _ => expand s), Finset.sum_comm]
    have inner : ∀ r : ZMod M, ∑ s : ZMod M, ∑ r' : ZMod M,
          (c r * (starRingEnd ℂ) (c r')) *
            (eM M (lam * r * s) * (starRingEnd ℂ) (eM M (lam * r' * s)))
        = ∑ r' : ZMod M, (c r * (starRingEnd ℂ) (c r')) * (if r' = r then (M : ℂ) else 0) := by
      intro r
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r' _ => ?_
      rw [← Finset.mul_sum]
      congr 1
      rw [← productFourier_orthogonality lam hl r' r]
      exact Finset.sum_congr rfl fun s _ => by
        rw [eM_conj, eM_conj, ← eM_add, ← eM_add]
        ring_nf
    rw [Finset.sum_congr rfl (fun r _ => inner r)]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_eq_single r]
    · simp; ring
    · intro r' _ hr'; simp [hr']
    · intro h; simp at h
  have hL : ((∑ s : ZMod M, ‖∑ r : ZMod M, c r * eM M (lam * r * s)‖ ^ 2 : ℝ) : ℂ)
      = ((((M : ℝ) * ∑ r : ZMod M, ‖c r‖ ^ 2 : ℝ)) : ℂ) := by
    rw [ofReal_sum_normSq, hC]
    push_cast
    congr 1
    exact Finset.sum_congr rfl fun r _ => Complex.mul_conj' (c r)
  exact_mod_cast hL

end PuncturedFourier
end CurrentProgramme
end TwinPrimeProject
