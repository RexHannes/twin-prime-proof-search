/-
# Gate-1A §15: the effective-rank floor

**Layer A** (`rank_floor_from_pointwise_hs`) is the downstream algebra: it
derives the floor from a *pointwise* Schatten hypothesis `u_m² ≤ K d_m` by
Cauchy–Schwarz.

**Layer B** (`rank_floor_hs_of_rank_le`) is the genuine finite-matrix
statement, and it is **proved** here, not assumed: for a complex matrix `T`
of rank at most `K`,

`‖T‖_HS⁴ ≤ K · ‖T Tᴴ‖_HS²`.

The proof goes through the spectral theorem for the positive semidefinite
matrix `P = T Tᴴ`: `‖T‖_HS² = ∑ λ_i`, `‖T Tᴴ‖_HS² = ∑ λ_i²`, and the number
of nonzero `λ_i` equals `rank P = rank T ≤ K`.

**Layer C** is the recombined dimension arithmetic.  Only the *symbolic*
consequence is proved here; the identification of the actual finite domain
dimension `N_new` is deliberately left to the source-interface layer.
-/
import Mathlib
import Gate1A.FourCycle

namespace Gate1A

namespace RankFloor

open Finset Matrix
open scoped ComplexOrder

/-! ### Layer A: the downstream algebra from a pointwise Schatten bound -/

/-- **`rank_floor_from_pointwise_hs`.**  If nonnegative `u_m, d_m` satisfy the
pointwise Schatten inequality `u_m² ≤ K d_m`, then

`(∑_m u_m)² ≤ (#m) · K · ∑_m d_m`. -/
theorem rank_floor_from_pointwise_hs {ι : Type*} (s : Finset ι) (u d : ι → ℝ)
    (K : ℝ) (hpt : ∀ m ∈ s, u m ^ 2 ≤ K * d m) :
    (∑ m ∈ s, u m) ^ 2 ≤ (s.card : ℝ) * K * ∑ m ∈ s, d m := by
  have h1 : (∑ m ∈ s, u m) ^ 2 ≤ (s.card : ℝ) * ∑ m ∈ s, u m ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : (∑ m ∈ s, u m ^ 2) ≤ ∑ m ∈ s, K * d m := Finset.sum_le_sum hpt
  have h3 : (∑ m ∈ s, K * d m) = K * ∑ m ∈ s, d m := by rw [Finset.mul_sum]
  calc (∑ m ∈ s, u m) ^ 2 ≤ (s.card : ℝ) * ∑ m ∈ s, u m ^ 2 := h1
    _ ≤ (s.card : ℝ) * (K * ∑ m ∈ s, d m) :=
        mul_le_mul_of_nonneg_left (h3 ▸ h2) (Nat.cast_nonneg _)
    _ = (s.card : ℝ) * K * ∑ m ∈ s, d m := by ring

/-! ### Layer B: the genuine rank–Schatten inequality -/

open FourCycle

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The trace of `A²` for a Hermitian `A` is the sum of the squares of its
eigenvalues. -/
theorem trace_sq_eq_sum_eigenvalues_sq (A : Matrix n n ℂ) (hA : A.IsHermitian) :
    Matrix.trace (A * A) = ∑ i, ((hA.eigenvalues i : ℂ)) ^ 2 := by
  classical
  conv_lhs => rw [hA.spectral_theorem, ← map_mul]
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.diagonal_mul_diagonal,
    Matrix.trace_diagonal]
  exact Finset.sum_congr rfl fun i _ => by simp [sq]

omit [DecidableEq n] in
/-- Chebyshev/Cauchy on the support of an eigenvalue vector: only the nonzero
eigenvalues contribute to the linear sum. -/
theorem sq_sum_le_card_support_mul_sum_sq (lam : n → ℝ) :
    (∑ i, lam i) ^ 2
      ≤ ((univ.filter (fun i => lam i ≠ 0)).card : ℝ) * ∑ i, lam i ^ 2 := by
  classical
  set S : Finset n := univ.filter (fun i => lam i ≠ 0) with hS
  have hsum : (∑ i, lam i) = ∑ i ∈ S, lam i := by
    rw [hS]
    refine (Finset.sum_filter_ne_zero univ).symm
  have h1 : (∑ i ∈ S, lam i) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, lam i ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : (∑ i ∈ S, lam i ^ 2) ≤ ∑ i, lam i ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun i _ _ => sq_nonneg _)
  rw [hsum]
  exact h1.trans (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))

omit [DecidableEq n] in
/-- **`rank_floor_hs_of_rank_le`.**  The rank–Schatten inequality:
for a complex matrix `T` of rank at most `K`,

`‖T‖_HS⁴ ≤ K · ‖T Tᴴ‖_HS²`. -/
theorem rank_floor_hs_of_rank_le {m : Type*} [Fintype m] [DecidableEq m]
    (T : Matrix m n ℂ) (K : ℕ) (hrank : T.rank ≤ K) :
    hsNormSq T ^ 2 ≤ (K : ℝ) * hsNormSq (T * Tᴴ) := by
  classical
  set P : Matrix m m ℂ := T * Tᴴ with hPdef
  have hPsd : P.PosSemidef := posSemidef_self_mul_conjTranspose T
  have hH : P.IsHermitian := hPsd.isHermitian
  set lam : m → ℝ := hH.eigenvalues with hlam
  -- `‖T‖_HS² = ∑ λ`
  have hT : hsNormSq T = ∑ i, lam i := by
    have h1 : ((hsNormSq T : ℝ) : ℂ) = Matrix.trace (Tᴴ * T) := hsNormSq_eq_trace T
    have h2 : Matrix.trace (Tᴴ * T) = Matrix.trace P := Matrix.trace_mul_comm _ _
    have h3 : Matrix.trace P = ∑ i, ((lam i : ℝ) : ℂ) := hH.trace_eq_sum_eigenvalues
    have : ((hsNormSq T : ℝ) : ℂ) = ((∑ i, lam i : ℝ) : ℂ) := by
      rw [h1, h2, h3]; push_cast; rfl
    exact_mod_cast this
  -- `‖T Tᴴ‖_HS² = ∑ λ²`
  have hP : hsNormSq P = ∑ i, lam i ^ 2 := by
    have h1 : ((hsNormSq P : ℝ) : ℂ) = Matrix.trace (Pᴴ * P) := hsNormSq_eq_trace P
    have h2 : Matrix.trace (Pᴴ * P) = Matrix.trace (P * P) := by rw [hH.eq]
    have h3 : Matrix.trace (P * P) = ∑ i, ((lam i : ℝ) : ℂ) ^ 2 :=
      trace_sq_eq_sum_eigenvalues_sq P hH
    have : ((hsNormSq P : ℝ) : ℂ) = ((∑ i, lam i ^ 2 : ℝ) : ℂ) := by
      rw [h1, h2, h3]; push_cast; rfl
    exact_mod_cast this
  -- the number of nonzero eigenvalues is the rank
  have hcard : ((univ.filter (fun i => lam i ≠ 0)).card : ℕ) = P.rank := by
    rw [hH.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
  have hrk : P.rank = T.rank := Matrix.rank_self_mul_conjTranspose T
  have hle : ((univ.filter (fun i => lam i ≠ 0)).card : ℝ) ≤ (K : ℝ) := by
    have : ((univ.filter (fun i => lam i ≠ 0)).card : ℕ) ≤ K := by
      rw [hcard, hrk]; exact hrank
    exact_mod_cast this
  have hchev := sq_sum_le_card_support_mul_sum_sq lam
  have hnn2 : (0 : ℝ) ≤ ∑ i, lam i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [hT, hP]
  exact hchev.trans (mul_le_mul_of_nonneg_right hle hnn2)

/-! ### Layer C: recombined dimension arithmetic (symbolic only) -/

/-- **`rank_floor_symbolic_new`.**  The purely symbolic consequence of the
recombined dimension: from `(tr A_r)² ≤ MK · D_r` and `MK = L²/H`, and with
the *proposed* new domain dimension `N_new = 2L²`,

`(tr A_r)² / N_new ≤ (1/2) · D_r / H`.

The identification `N_new = 2L²` itself is **not** proved here: it is a field
of the source-interface layer.  The hypothesis `hMK` is exactly the exponent
identity `MK = L²/H`. -/
theorem rank_floor_symbolic_new (trA MK D_r Lsq H : ℝ) (hH : 0 < H) (hL : 0 < Lsq)
    (hMK : MK = Lsq / H) (hbound : trA ^ 2 ≤ MK * D_r) :
    trA ^ 2 / (2 * Lsq) ≤ (1 / 2) * (D_r / H) := by
  rw [div_le_iff₀ (by positivity)]
  have h1 : trA ^ 2 ≤ (Lsq / H) * D_r := by rw [← hMK]; exact hbound
  have h2 : (1 / 2) * (D_r / H) * (2 * Lsq) = (Lsq / H) * D_r := by
    field_simp
  rw [h2]
  exact h1

end RankFloor

end Gate1A
