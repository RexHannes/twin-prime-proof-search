/-
# Gate-1A Δv4 §9 / §10 — two-sided S2 retracted, S2-UPPER proved

* **§9** The two-sided statement "source norm ≍ transported norm" is
  permanently retracted.  It is refuted here in the exact form in which it
  was used: scalar (`ℓ¹`) control of a kernel does **not** imply any
  Hilbert–Schmidt / `ℓ²` norm equivalence, with an arbitrarily bad constant.
* **§10** The one-sided upper transport (`S2-UPPER`) is proved directly by
  Minkowski: if `C = ∑_λ c_λ C_λ + Err` with `∑_λ |c_λ| ≤ C₀` and
  `‖C_λ‖ ≤ B` uniformly, then `‖C‖ ≤ C₀ B + ‖Err‖`.

The **critical order rule** of §10 (mode decomposition strictly before TF4
expansion / outer four-cycle / projective energy expansion) is a statement
about *which* theorem is applied where; it is recorded as the explicit
hypothesis `modeDecompositionBeforeTF4` of the Δv4 interface structure in
`Gate1A/Delta4/Interfaces.lean`, and the theorem below is stated on the
original index set `E` precisely so that it can only be used in that order.
-/
import Mathlib

namespace Gate1A

namespace Delta4

open Finset

/-! ## §10 S2-UPPER -/

/-- **§10 (`one_sided_source_transport_l2`).**  Minkowski upper transport on
the original row/index set: no norm equivalence, no lower bound, no
transported-norm comparison. -/
theorem one_sided_source_transport_l2 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Λ : Type*} (s : Finset Λ) (c : Λ → ℂ) (Cmode : Λ → E)
    (C Err : E) (C0 B : ℝ) (hB : 0 ≤ B)
    (hdecomp : C = (∑ lam ∈ s, c lam • Cmode lam) + Err)
    (hc : ∑ lam ∈ s, ‖c lam‖ ≤ C0)
    (hmode : ∀ lam ∈ s, ‖Cmode lam‖ ≤ B) :
    ‖C‖ ≤ C0 * B + ‖Err‖ := by
  have hmain : ‖∑ lam ∈ s, c lam • Cmode lam‖ ≤ C0 * B := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ lam ∈ s, ‖c lam • Cmode lam‖ ≤ ‖c lam‖ * B := by
      intro lam hlam
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left (hmode lam hlam) (norm_nonneg _)
    calc ∑ lam ∈ s, ‖c lam • Cmode lam‖ ≤ ∑ lam ∈ s, ‖c lam‖ * B :=
          Finset.sum_le_sum hterm
      _ = (∑ lam ∈ s, ‖c lam‖) * B := by rw [Finset.sum_mul]
      _ ≤ C0 * B := mul_le_mul_of_nonneg_right hc hB
  rw [hdecomp]
  have := norm_add_le (∑ lam ∈ s, c lam • Cmode lam) Err
  linarith

/-- The same statement in the `ℓ²(E)`-vocabulary of the addendum: with
`E` the original row index set, `C(e) = ∑_λ c_λ C_λ(e) + Err(e)`. -/
theorem one_sided_source_transport_l2_pi {ι : Type*} [Fintype ι]
    {Λ : Type*} (s : Finset Λ) (c : Λ → ℂ) (Cmode : Λ → EuclideanSpace ℂ ι)
    (C Err : EuclideanSpace ℂ ι) (C0 B : ℝ) (hB : 0 ≤ B)
    (hdecomp : C = (∑ lam ∈ s, c lam • Cmode lam) + Err)
    (hc : ∑ lam ∈ s, ‖c lam‖ ≤ C0)
    (hmode : ∀ lam ∈ s, ‖Cmode lam‖ ≤ B) :
    ‖C‖ ≤ C0 * B + ‖Err‖ :=
  one_sided_source_transport_l2 s c Cmode C Err C0 B hB hdecomp hc hmode

/-! ## §9 Two-sided S2 is permanently retracted -/

/-- **§9 countermodel.**  Scalar `ℓ¹` control does not imply `ℓ²`
(Hilbert–Schmidt) norm equivalence: for every constant `C` there are two
finite vectors with *equal* `ℓ¹` mass whose `ℓ²` masses differ by more than
`C`.  Hence no theorem of the form "source norm ≍ transported norm" may be
used in the Gate closure. -/
theorem l1_control_not_l2_equivalence (C : ℝ) :
    ∃ (n : ℕ) (f g : Fin n → ℝ),
      (∑ i, |f i|) = (∑ i, |g i|) ∧
      C * (∑ i, (f i) ^ 2) < (∑ i, (g i) ^ 2) := by
  classical
  set m : ℕ := ⌈C⌉₊ with hm
  have habs : ∀ i : Fin (m + 1),
      |(if i = 0 then ((m : ℝ) + 1) else 0)| = (if i = 0 then ((m : ℝ) + 1) else 0) := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
    positivity
  have hsq : ∀ i : Fin (m + 1),
      (if i = 0 then ((m : ℝ) + 1) else 0) ^ 2 = (if i = 0 then ((m : ℝ) + 1) ^ 2 else 0) := by
    intro i
    by_cases hi : i = 0 <;> simp [hi]
  refine ⟨m + 1, (fun _ => 1), (fun i => if i = 0 then ((m : ℝ) + 1) else 0), ?_, ?_⟩
  · simp [habs]
  · have hC : C ≤ (m : ℝ) := Nat.le_ceil C
    simp only [hsq, one_pow]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add,
      Nat.cast_one]
    nlinarith [hC]

/-- The retraction in operator form: there is no constant `κ` for which
`‖·‖₂` of the transported vector is bounded **below** by `κ⁻¹` times the
`ℓ¹`-controlled source data uniformly in the dimension. -/
theorem no_two_sided_S2_constant :
    ¬ ∃ K : ℝ, ∀ (n : ℕ) (f g : Fin n → ℝ),
        (∑ i, |f i|) = (∑ i, |g i|) →
        (∑ i, (g i) ^ 2) ≤ K * (∑ i, (f i) ^ 2) := by
  rintro ⟨K, hK⟩
  obtain ⟨n, f, g, heq, hlt⟩ := l1_control_not_l2_equivalence K
  exact absurd (hK n f g heq) (not_le.mpr hlt)

end Delta4

end Gate1A
