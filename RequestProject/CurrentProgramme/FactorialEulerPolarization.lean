import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Phase J1 / J3 · factorial–Euler polarization for the balanced-seven source

## Source note

The repository contains **no** `Erdos287`, `BalancedSeven`, `Omega7`,
`WindowPairSupply` or `Factorial` module (searched).  The Erdős-#287 finite
range check and the `WindowPairSupply ⇒ #287` compiler named in the
continuation prompt are therefore **SOURCE_BLOCKED** here: they are not present
to be preserved or reused, and they are not reconstructed from prose.

What *is* source-independent, and is proved here in full, is the algebra the
prompt identifies as controlling: the **factorial–Euler polarization**, i.e.
the multilinear coefficient extraction

  `[z₁ ⋯ z_n] (∑ᵢ zᵢ ωᵢ)^n = n! · ∏ᵢ ωᵢ`,

which is exactly the cancellation of the `1/e!` in `F_z(p^e) = a_z(p)^e / e!`
for a prime of multiplicity `e = n`.

## What is proved

* `alternating_polarization` — the general identity, any `n`;
* `factorialEulerPolarization_general` — the `1/e!` cancellation, any `n`;
* `factorialEulerPolarization_seven` — the balanced-seven case `n = 7`,
  including the *repeated-prime* case `n = p^7`;
* `no_extra_inverse_factorial_correction` — the **counterguard** against the
  false extra `∏_p 1/e_p!` factor;
* `coeffExtract_linear` — Phase J3 expected-term linearity.

No analytic statement is made, and `M_fac = M_phys` is **not** concluded: that
remains a source identity (see `AnalyticInterfaces.lean`).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FactorialEuler

open Finset

/-! ## 0. Two elementary sign / powerset lemmas -/

private lemma negone_sub (n k : ℕ) (h : k ≤ n) :
    (-1 : ℂ) ^ (n - k) = (-1) ^ n * (-1) ^ k := by
  have h1 : (-1 : ℂ) ^ (n - k) * (-1) ^ k = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel h]
  have h2 : ((-1 : ℂ) ^ k) * ((-1) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  calc (-1 : ℂ) ^ (n - k) = (-1) ^ (n - k) * ((-1) ^ k * (-1) ^ k) := by rw [h2, mul_one]
    _ = ((-1 : ℂ) ^ (n - k) * (-1) ^ k) * (-1) ^ k := by ring
    _ = (-1) ^ n * (-1) ^ k := by rw [h1]

private lemma powerset_alt_complex {α : Type*} [DecidableEq α] (x : Finset α) :
    ∑ C ∈ x.powerset, (-1 : ℂ) ^ C.card = if x = ∅ then 1 else 0 := by
  have hz : ((∑ C ∈ x.powerset, (-1 : ℤ) ^ C.card : ℤ) : ℂ)
      = ((if x = ∅ then (1 : ℤ) else 0 : ℤ) : ℂ) := by
    rw [Finset.sum_powerset_neg_one_pow_card]
  push_cast at hz
  exact hz

/-- Möbius/inclusion–exclusion over the supersets of a fixed set. -/
private lemma sum_supersets_alt {n : ℕ} (T : Finset (Fin n)) :
    ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => T ⊆ A), (-1 : ℂ) ^ (n - A.card)
      = if T = Finset.univ then 1 else 0 := by
  classical
  have hTn : T.card ≤ n := by
    have := Finset.card_le_univ T; simpa using this
  have hcompl : Tᶜ.card + T.card = n := by
    rw [Finset.card_compl, Fintype.card_fin]; omega
  have key :
      ∑ A ∈ Finset.univ.filter (fun A : Finset (Fin n) => T ⊆ A), (-1 : ℂ) ^ (n - A.card)
        = ∑ C ∈ Tᶜ.powerset, (-1 : ℂ) ^ (n - (C.card + T.card)) := by
    refine Finset.sum_nbij' (fun A => A \ T) (fun C => C ∪ T) ?_ ?_ ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter] at hA
      simp only [Finset.mem_powerset]
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simpa using hx.2
    · intro C hC
      simp only [Finset.mem_powerset] at hC
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.subset_union_right
    · intro A hA
      simp only [Finset.mem_filter] at hA
      exact Finset.sdiff_union_of_subset hA.2
    · intro C hC
      simp only [Finset.mem_powerset] at hC
      have hd : Disjoint C T := by
        rw [Finset.disjoint_left]
        intro x hxC hxT
        have := hC hxC
        simp at this
        exact this hxT
      simp [Finset.union_sdiff_right, Finset.sdiff_eq_self_of_disjoint hd]
    · intro A hA
      simp only [Finset.mem_filter] at hA
      have hc := Finset.card_sdiff_add_card_eq_card hA.2
      simp only
      rw [hc]
  rw [key]
  have hstep : ∀ C ∈ Tᶜ.powerset, (-1 : ℂ) ^ (n - (C.card + T.card))
      = (-1 : ℂ) ^ n * ((-1) ^ (C.card) * (-1) ^ (T.card)) := by
    intro C hC
    simp only [Finset.mem_powerset] at hC
    have h1 : C.card ≤ Tᶜ.card := Finset.card_le_card hC
    have hle : C.card + T.card ≤ n := by omega
    rw [negone_sub n _ hle, pow_add]
  rw [Finset.sum_congr rfl hstep, ← Finset.mul_sum, ← Finset.sum_mul,
    powerset_alt_complex]
  by_cases hT : T = Finset.univ
  · subst hT
    simp only [Finset.compl_univ, Finset.card_univ, Fintype.card_fin, if_true,
      one_mul]
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  · rw [if_neg hT]
    have hne : Tᶜ ≠ ∅ := by
      intro h
      exact hT (by simpa [Finset.compl_eq_empty_iff] using h)
    rw [if_neg hne]
    ring

/-! ## 1. The polarization identity -/

/-- **J1 core.**  Classical polarization / inclusion–exclusion:

  `∑_{A ⊆ [n]} (-1)^(n-|A|) (∑_{i ∈ A} wᵢ)^n = n! ∏ᵢ wᵢ`.

This *is* the multilinear coefficient extraction `[z₁ ⋯ z_n]` applied to
`(∑ᵢ zᵢ wᵢ)^n`, evaluated on the `0/1` corners of the `z`-cube. -/
theorem alternating_polarization (n : ℕ) (w : Fin n → ℂ) :
    ∑ A : Finset (Fin n), (-1 : ℂ) ^ (n - A.card) * (∑ i ∈ A, w i) ^ n
      = (n.factorial : ℂ) * ∏ i, w i := by
  classical
  have hexp : ∀ A : Finset (Fin n), (∑ i ∈ A, w i) ^ n
      = ∑ p : Fin n → Fin n, (if (∀ i, p i ∈ A) then ∏ i, w (p i) else 0) := by
    intro A
    have h1 : ∑ i ∈ A, w i = ∑ i : Fin n, (if i ∈ A then w i else 0) := by
      rw [Finset.sum_ite_mem]; simp
    rw [h1, Fintype.sum_pow]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : ∀ i, p i ∈ A
    · simp [h]
    · push_neg at h
      obtain ⟨j, hj⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj])]
      rw [if_neg (by push_neg; exact ⟨j, hj⟩)]
  simp only [hexp, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ p : Fin n → Fin n,
      ∑ A : Finset (Fin n),
          (-1 : ℂ) ^ (n - A.card) * (if (∀ i, p i ∈ A) then ∏ i, w (p i) else 0)
        = (if Finset.image p Finset.univ = Finset.univ then ∏ i, w (p i) else 0) := by
    intro p
    have hcond : ∀ A : Finset (Fin n),
        (∀ i, p i ∈ A) ↔ Finset.image p Finset.univ ⊆ A := by
      intro A
      constructor
      · intro h x hx
        simp only [Finset.mem_image, Finset.mem_univ, true_and] at hx
        obtain ⟨i, rfl⟩ := hx; exact h i
      · intro h i; exact h (by simp)
    calc ∑ A : Finset (Fin n),
            (-1 : ℂ) ^ (n - A.card) * (if (∀ i, p i ∈ A) then ∏ i, w (p i) else 0)
        = ∑ A : Finset (Fin n), (if Finset.image p Finset.univ ⊆ A then
            (-1 : ℂ) ^ (n - A.card) * ∏ i, w (p i) else 0) := by
          refine Finset.sum_congr rfl fun A _ => ?_
          by_cases h : Finset.image p Finset.univ ⊆ A
          · rw [if_pos ((hcond A).2 h), if_pos h]
          · rw [if_neg (fun hh => h ((hcond A).1 hh)), if_neg h, mul_zero]
      _ = ∑ A ∈ Finset.univ.filter
            (fun A : Finset (Fin n) => Finset.image p Finset.univ ⊆ A),
            (-1 : ℂ) ^ (n - A.card) * ∏ i, w (p i) := by rw [Finset.sum_filter]
      _ = (∑ A ∈ Finset.univ.filter
            (fun A : Finset (Fin n) => Finset.image p Finset.univ ⊆ A),
            (-1 : ℂ) ^ (n - A.card)) * ∏ i, w (p i) := by rw [Finset.sum_mul]
      _ = (if Finset.image p Finset.univ = Finset.univ then ∏ i, w (p i) else 0) := by
          rw [sum_supersets_alt]
          split <;> simp
  rw [Finset.sum_congr rfl (fun p _ => hinner p), ← Finset.sum_filter]
  have hbij : ∀ p : Fin n → Fin n,
      (Finset.image p Finset.univ = Finset.univ) ↔ Function.Bijective p := by
    intro p
    have hsurj : (Finset.image p Finset.univ = Finset.univ) ↔ Function.Surjective p := by
      constructor
      · intro h y
        have : y ∈ Finset.image p Finset.univ := by rw [h]; exact Finset.mem_univ y
        simpa using this
      · intro h
        apply Finset.eq_univ_of_forall
        intro y
        obtain ⟨x, rfl⟩ := h y
        simp
    rw [hsurj]
    exact ⟨fun h => Finite.injective_iff_bijective.mp
      (Finite.injective_iff_surjective.mpr h), fun h => h.2⟩
  rw [Finset.filter_congr (fun p _ => by rw [hbij p])]
  have hc : ∀ p ∈ Finset.univ.filter (fun p : Fin n → Fin n => Function.Bijective p),
      ∏ i, w (p i) = ∏ i, w i := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    exact Equiv.prod_comp (Equiv.ofBijective p hp.2) w
  rw [Finset.sum_congr rfl hc, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have h1 : (Finset.univ.filter (fun f : Fin n → Fin n => Function.Bijective f)).card
      = Fintype.card {f : Fin n → Fin n // Function.Bijective f} := by
    rw [Fintype.card_subtype]
  have e : {f : Fin n → Fin n // Function.Bijective f} ≃ Equiv.Perm (Fin n) :=
    { toFun := fun f => Equiv.ofBijective f.1 f.2
      invFun := fun σ => ⟨σ, σ.bijective⟩
      left_inv := fun f => rfl
      right_inv := fun σ => by ext x; rfl }
  rw [h1, Fintype.card_congr e, Fintype.card_perm, Fintype.card_fin]

/-! ## 2. Coefficient extraction as a functional -/

/-- The `0/1` corner of the `z`-cube indexed by `A`. -/
def corner {n : ℕ} (A : Finset (Fin n)) : Fin n → ℂ :=
  fun i => if i ∈ A then 1 else 0

/-- Multilinear coefficient extraction `[z₁ ⋯ z_n]` realised as the signed sum
over the corners of the `z`-cube.  For a function `G` that is a polynomial of
total degree `≤ n` in `z`, this returns the coefficient of `z₁ ⋯ z_n`. -/
def coeffExtract {n : ℕ} {M : Type*} [AddCommGroup M] [Module ℂ M]
    (G : (Fin n → ℂ) → M) : M :=
  ∑ A : Finset (Fin n), ((-1 : ℂ) ^ (n - A.card)) • G (corner A)

/-- The balanced weight `a_z = (1/n) ∑ᵢ zᵢ ωᵢ`. -/
noncomputable def aOf {n : ℕ} (w z : Fin n → ℂ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ i, z i * w i

theorem aOf_corner {n : ℕ} (w : Fin n → ℂ) (A : Finset (Fin n)) :
    aOf w (corner A) = (n : ℂ)⁻¹ * ∑ i ∈ A, w i := by
  unfold aOf corner
  congr 1
  have hsum : ∀ i : Fin n, (if i ∈ A then (1 : ℂ) else 0) * w i
      = if i ∈ A then w i else 0 := by
    intro i; split <;> simp
  rw [Finset.sum_congr rfl (fun i _ => hsum i), Finset.sum_ite_mem,
    Finset.univ_inter]

/-! ## 3. The factorial cancellation -/

/-- **J1, general `n`.**  With `F_z(p^n) = a_z(p)^n / n!`, the multilinear
coefficient extraction gives

  `n^n · [z₁ ⋯ z_n] (a_z^n / n!) = ∏ᵢ ωᵢ`.

The `n!` produced by the polarization cancels the `1/n!` of the local Euler
factor exactly — this is the essential factorial cancellation, and it holds
**including the repeated-prime case** `n = p^n`, which is what this statement
is. -/
theorem factorialEulerPolarization_general (n : ℕ) (hn : n ≠ 0) (w : Fin n → ℂ) :
    ((n : ℂ) ^ n) * coeffExtract (fun z => (aOf w z) ^ n / (n.factorial : ℂ))
      = ∏ i, w i := by
  have hncast : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero n)
  unfold coeffExtract
  simp only [smul_eq_mul, aOf_corner]
  have hterm : ∀ A : Finset (Fin n),
      ((-1 : ℂ) ^ (n - A.card)) * (((n : ℂ)⁻¹ * ∑ i ∈ A, w i) ^ n / (n.factorial : ℂ))
        = ((n : ℂ) ^ n)⁻¹ * (n.factorial : ℂ)⁻¹ *
            (((-1 : ℂ) ^ (n - A.card)) * (∑ i ∈ A, w i) ^ n) := by
    intro A
    rw [mul_pow, inv_pow]
    field_simp
  rw [Finset.sum_congr rfl (fun A _ => hterm A), ← Finset.mul_sum,
    alternating_polarization n w]
  field_simp

/-- **J1, balanced seven.**  The `n = 7` case: `7^7 · [z₁⋯z₇] F_z(p^7) = ∏ ωᵢ(p)`.

This is the pure prime-power (fully repeated) cell of the balanced-seven
factorial-Euler source: `Ω(n) = 7` with `n = p^7` has exactly one ordered
factorisation `(p,…,p)`, and its contribution is `∏ᵢ ωᵢ(p)`. -/
theorem factorialEulerPolarization_seven (w : Fin 7 → ℂ) :
    ((7 : ℂ) ^ 7) * coeffExtract (fun z => (aOf w z) ^ 7 / ((7).factorial : ℂ))
      = ∏ i, w i := by
  have := factorialEulerPolarization_general 7 (by norm_num) w
  simpa using this

/-- **J1 COUNTERGUARD.**  The false extra `∏_p 1/e_p!` correction must not be
resurrected: with the spurious extra `1/7!` the identity fails.  Witness
`ω ≡ 1`, where the true value is `1` and the spurious value is `1/5040`. -/
theorem no_extra_inverse_factorial_correction :
    ∃ w : Fin 7 → ℂ,
      ((7 : ℂ) ^ 7) * coeffExtract (fun z => (aOf w z) ^ 7 / ((7).factorial : ℂ))
        ≠ ((7).factorial : ℂ)⁻¹ * ∏ i, w i := by
  refine ⟨fun _ => 1, ?_⟩
  rw [factorialEulerPolarization_seven]
  norm_num [Nat.factorial]

/-! ## 4. Phase J3 — expected-term linearity -/

/-- **J3.**  Coefficient extraction commutes with any linear map: for
`E : M →ₗ[ℂ] N`,  `E ([z₁⋯z_n] F) = [z₁⋯z_n] (E ∘ F)`.

This is a *formal* commutation.  It does **not** give `M_fac = M_phys`; that
remains a source identity. -/
theorem coeffExtract_linear {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (E : M →ₗ[ℂ] N) (F : (Fin n → ℂ) → M) :
    E (coeffExtract F) = coeffExtract (fun z => E (F z)) := by
  unfold coeffExtract
  rw [map_sum]
  exact Finset.sum_congr rfl fun A _ => by rw [map_smul]

/-- **J3 firewall.**  Linearity of the extraction says nothing about whether
two *different* expected-term functionals agree: two linear maps can commute
with the extraction and still differ. -/
theorem coeffExtract_linear_does_not_identify_functionals :
    ∃ (E₁ E₂ : ℂ →ₗ[ℂ] ℂ), (∀ F : (Fin 1 → ℂ) → ℂ,
        E₁ (coeffExtract F) = coeffExtract (fun z => E₁ (F z))) ∧
      (∀ F : (Fin 1 → ℂ) → ℂ,
        E₂ (coeffExtract F) = coeffExtract (fun z => E₂ (F z))) ∧ E₁ ≠ E₂ := by
  refine ⟨LinearMap.id, (2 : ℂ) • LinearMap.id, fun F => coeffExtract_linear _ F,
    fun F => coeffExtract_linear _ F, ?_⟩
  intro h
  have := congrArg (fun T : ℂ →ₗ[ℂ] ℂ => T 1) h
  simp at this

end FactorialEuler
end CurrentProgramme
end TwinPrimeProject
