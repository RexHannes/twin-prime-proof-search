/-
# Gate 1B v12 — the NO-WRAP weighted product energy

**Status: PROVED FINITE (unconditional finite algebra / combinatorics).**

If `α` is supported on `1 ≤ m ≤ M`, `β` on `1 ≤ n ≤ N` and

    M · N ≤ c,

then congruence of products modulo `c` *is* equality of products, so the residue
product energy modulo `c` collapses onto the integer-product fibres and is
controlled by the integer fibre multiplicity:

    ProductResidueEnergy_c(α,β) ≤ (max_k Fibre(k)) · ‖α‖₂² · ‖β‖₂².

**Scope.**  The hypothesis `M·N ≤ c` is load-bearing; see
`WraparoundEnergyCounterguard.lean` for an explicit finite refutation of the
conclusion when it fails.

**CAPACITY COMMENT (not a theorem).**  In the arithmetic application one wants
`max_k Fibre(k) ≤ c^{o(1)}`, which is a divisor-type bound.  No such asymptotic
statement is proved or assumed anywhere in this file: the fibre bound `D` is an
explicit hypothesis of every theorem below.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-! ## Congruence rigidity below the wrap threshold -/

/-- Two naturals in `[1, c]` that agree modulo `c` are equal. -/
theorem eq_of_natCast_eq_of_le {c a b : ℕ} (ha1 : 1 ≤ a) (hb1 : 1 ≤ b)
    (hac : a ≤ c) (hbc : b ≤ c) (h : ((a : ℕ) : ZMod c) = ((b : ℕ) : ZMod c)) : a = b := by
  have hmod : a ≡ b [MOD c] := (ZMod.natCast_eq_natCast_iff a b c).mp h
  rcases le_total a b with hab | hab
  · have hdvd : c ∣ b - a := (Nat.modEq_iff_dvd' hab).mp hmod
    have hlt : b - a < c := by omega
    have h0 := Nat.eq_zero_of_dvd_of_lt hdvd
    omega
  · have hdvd : c ∣ a - b := (Nat.modEq_iff_dvd' hab).mp hmod.symm
    have hlt : a - b < c := by omega
    have h0 := Nat.eq_zero_of_dvd_of_lt hdvd
    omega

/-- **NO-WRAP RIGIDITY.**  For supported tuples, `m·n ≡ m'·n' (mod c)` implies
`m·n = m'·n'`. -/
theorem congruence_eq_of_noWrap {c M N : ℕ} (hMN : M * N ≤ c)
    {m n m' n' : ℕ} (hm : 1 ≤ m) (hmM : m ≤ M) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hm' : 1 ≤ m') (hmM' : m' ≤ M) (hn' : 1 ≤ n') (hnN' : n' ≤ N)
    (h : ((m * n : ℕ) : ZMod c) = ((m' * n' : ℕ) : ZMod c)) : m * n = m' * n' := by
  refine eq_of_natCast_eq_of_le ?_ ?_ ?_ ?_ h
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  · exact Nat.one_le_iff_ne_zero.2 (by positivity)
  · exact le_trans (Nat.mul_le_mul hmM hnN) hMN
  · exact le_trans (Nat.mul_le_mul hmM' hnN') hMN

/-! ## Fibres and the weighted energy -/

/-- The exact **integer-product fibre** of the support rectangle. -/
def integerFibre (A B : Finset ℕ) (k : ℕ) : ℕ :=
  ((A ×ˢ B).filter (fun x => x.1 * x.2 = k)).card

/-- The residue product energy modulo `c` of the weights `α, β` supported on
`A × B`. -/
noncomputable def residueProductEnergy (A B : Finset ℕ) (c : ℕ) [NeZero c]
    (alpha beta : ℕ → ℂ) : ℝ :=
  ∑ r : ZMod c,
    ‖∑ x ∈ (A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r),
      alpha x.1 * beta x.2‖ ^ 2

/-- Finite Cauchy–Schwarz in the form used below. -/
theorem norm_sum_sq_le_card_mul_sum_norm_sq {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ x ∈ s, f x‖ ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := by
  have h1 : ‖∑ x ∈ s, f x‖ ≤ ∑ x ∈ s, ‖f x‖ := norm_sum_le s f
  have h2 : (∑ x ∈ s, ‖f x‖) ^ 2 ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  refine le_trans ?_ h2
  have := mul_self_le_mul_self (norm_nonneg (∑ x ∈ s, f x)) h1
  simpa [sq] using this

/-- **Under no wrap, every residue fibre is an integer fibre.** -/
theorem residue_fibre_card_le {A B : Finset ℕ} {c M N D : ℕ} [NeZero c] (hMN : M * N ≤ c)
    (hA : ∀ m ∈ A, 1 ≤ m ∧ m ≤ M) (hB : ∀ n ∈ B, 1 ≤ n ∧ n ≤ N)
    (hFib : ∀ k : ℕ, integerFibre A B k ≤ D) (r : ZMod c) :
    ((A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r)).card ≤ D := by
  classical
  set S := (A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r) with hS
  rcases Finset.eq_empty_or_nonempty S with hemp | ⟨x₀, hx₀⟩
  · simp [hemp]
  · have hx₀' := hx₀
    rw [hS, Finset.mem_filter, Finset.mem_product] at hx₀'
    obtain ⟨⟨hx₀A, hx₀B⟩, hx₀r⟩ := hx₀'
    have hsub : S ⊆ (A ×ˢ B).filter (fun x => x.1 * x.2 = x₀.1 * x₀.2) := by
      intro y hy
      rw [hS, Finset.mem_filter, Finset.mem_product] at hy
      obtain ⟨⟨hyA, hyB⟩, hyr⟩ := hy
      refine Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨hyA, hyB⟩, ?_⟩
      refine congruence_eq_of_noWrap hMN (hA _ hyA).1 (hA _ hyA).2 (hB _ hyB).1 (hB _ hyB).2
        (hA _ hx₀A).1 (hA _ hx₀A).2 (hB _ hx₀B).1 (hB _ hx₀B).2 ?_
      rw [hyr, hx₀r]
    exact le_trans (Finset.card_le_card hsub) (hFib (x₀.1 * x₀.2))

/-- **NO-WRAP WEIGHTED ENERGY BOUND.**

    ProductResidueEnergy_c(α,β) ≤ D · ‖α‖₂² · ‖β‖₂²,

where `D` bounds the *integer-product* fibres of the support rectangle.  This is
unconditional finite combinatorics; no divisor estimate is used. -/
theorem productResidueEnergy_le_fibre_mul {A B : Finset ℕ} {c M N D : ℕ} [NeZero c]
    (hMN : M * N ≤ c) (hA : ∀ m ∈ A, 1 ≤ m ∧ m ≤ M) (hB : ∀ n ∈ B, 1 ≤ n ∧ n ≤ N)
    (hFib : ∀ k : ℕ, integerFibre A B k ≤ D) (alpha beta : ℕ → ℂ) :
    residueProductEnergy A B c alpha beta
      ≤ (D : ℝ) * ((∑ m ∈ A, ‖alpha m‖ ^ 2) * ∑ n ∈ B, ‖beta n‖ ^ 2) := by
  classical
  have hstep : ∀ r : ZMod c,
      ‖∑ x ∈ (A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r),
          alpha x.1 * beta x.2‖ ^ 2
        ≤ (D : ℝ) * ∑ x ∈ (A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r),
            ‖alpha x.1 * beta x.2‖ ^ 2 := by
    intro r
    refine le_trans (norm_sum_sq_le_card_mul_sum_norm_sq _ _) ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact_mod_cast residue_fibre_card_le hMN hA hB hFib r
  have hsum : residueProductEnergy A B c alpha beta
      ≤ (D : ℝ) * ∑ r : ZMod c,
          ∑ x ∈ (A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r),
            ‖alpha x.1 * beta x.2‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun r _ => hstep r
  have hfiber : ∑ r : ZMod c,
      ∑ x ∈ (A ×ˢ B).filter (fun x => ((x.1 * x.2 : ℕ) : ZMod c) = r),
        ‖alpha x.1 * beta x.2‖ ^ 2
      = ∑ x ∈ A ×ˢ B, ‖alpha x.1 * beta x.2‖ ^ 2 :=
    Finset.sum_fiberwise (A ×ˢ B) (fun x => ((x.1 * x.2 : ℕ) : ZMod c))
      (fun x => ‖alpha x.1 * beta x.2‖ ^ 2)
  have hprod : ∑ x ∈ A ×ˢ B, ‖alpha x.1 * beta x.2‖ ^ 2
      = (∑ m ∈ A, ‖alpha m‖ ^ 2) * ∑ n ∈ B, ‖beta n‖ ^ 2 := by
    rw [Finset.sum_product, Finset.sum_mul]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by rw [norm_mul, mul_pow]
  rw [hfiber, hprod] at hsum
  exact hsum

end Gate1B.SafeAlgebra
