/-
# Gate1B / R11 : bank, conditional interfaces, coverage firewall (§12, §13)

This module aggregates the canonical-source layer and records:

* the **conditional** low-divisor (Pascadi-type) interface: the analytic estimate is never
  postulated, it is an explicit hypothesis of the compiler theorem;
* the coverage **firewall**: the proposition "the canonical source covers the full physical
  R11 source" is *defined* but never inhabited, and the bank theorem's conclusion mentions
  only the explicitly defined canonical objects.

No `sorry`, no `admit`, no custom axiom, no `native_decide`.
-/
import Gate1B.R11.CanonicalSource
import Gate1B.R11.Card5
import Gate1B.R11.Factor542
import Gate1B.R11.ComparisonTyping
import Gate1B.R11.MobiusLogSplit
import Gate1B.R11.LongMobius
import Gate1B.R11.Determinant

namespace Gate1B.R11

open Finset ArithmeticFunction

/-! ## 1. Residual and long-Möbius tail of the canonical source -/

/-- The R11 residual of a source `Om` against the bracket-local comparison `bLoc B`, at the
fixed shift `2`. -/
noncomputable def R11Residual (s : Finset ℕ) (Om Bc : ℕ → ℝ) : ℝ :=
  (∑ n ∈ s, Om n * vonMangoldt (n + 2)) - ∑ n ∈ s, Om n * bLoc Bc n

/-- The long-Möbius tail in complementary-divisor (reindexed) form. -/
noncomputable def longMobiusTail (s : Finset ℕ) (Om : ℕ → ℝ) (U : ℕ) : ℝ :=
  ∑ n ∈ s, Om n * ∑ k ∈ (n + 2).divisors.filter (fun k => U < (n + 2) / k),
    (moebius ((n + 2) / k) : ℝ) * Real.log (k : ℝ)

/-- The tail in `d`-form and in reindexed `k`-form agree exactly (unconditional). -/
theorem longMobiusTail_eq_sum_longMobiusLog (s : Finset ℕ) (Om : ℕ → ℝ) (U : ℕ) :
    longMobiusTail s Om U = ∑ n ∈ s, Om n * longMobiusLog U (n + 2) := by
  rw [longMobiusTail, weighted_longMobius_reindex s Om U]

/-! ## 2. Conditional low-divisor (Pascadi-type) interface

The analytic theorem is **not** axiomatized.  It appears only as the hypothesis
`LowDivisorDiscrepancyBound`, an explicit real inequality about the truncated (`d ≤ U`)
Möbius–log part of the source. -/

/-- The low-`d` discrepancy bound: the truncated Möbius–log part of the weighted sum is
within `eps` of the declared principal term.  This is an *interface*, not a theorem. -/
def LowDivisorDiscrepancyBound (s : Finset ℕ) (Om : ℕ → ℝ) (U : ℕ) (principal eps : ℝ) :
    Prop :=
  |(∑ n ∈ s, Om n * lowMobiusLog U (n + 2)) - principal| ≤ eps

/-- Named owner predicate for the low-`d` analytic estimate: the owner of a source/range
pair is whoever supplies `LowDivisorDiscrepancyBound` for it.  Nothing inhabits this. -/
def PascadiOwner (s : Finset ℕ) (Om : ℕ → ℝ) (U : ℕ) : Prop :=
  ∃ principal eps : ℝ, LowDivisorDiscrepancyBound s Om U principal eps

/-- **Conditional compiler theorem.**  If the low-`d` analytic discrepancy bound holds and
the low-`d` principal term is exactly the bracket-local comparison sum, then the R11
residual equals the long-Möbius tail up to the same `eps`.  Nothing analytic is proved. -/
theorem r11_low_closed_implies_longMobius_residual
    (s : Finset ℕ) (Om Bc : ℕ → ℝ) (U : ℕ) (principal eps : ℝ)
    (hDisc : LowDivisorDiscrepancyBound s Om U principal eps)
    (hPrinc : principal = ∑ n ∈ s, Om n * bLoc Bc n) :
    |R11Residual s Om Bc - longMobiusTail s Om U| ≤ eps := by
  have hsplit : ∑ n ∈ s, Om n * vonMangoldt (n + 2)
      = (∑ n ∈ s, Om n * lowMobiusLog U (n + 2))
        + ∑ n ∈ s, Om n * longMobiusLog U (n + 2) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by
      rw [vonMangoldt_split U (n + 2)]; ring
  have : R11Residual s Om Bc - longMobiusTail s Om U
      = (∑ n ∈ s, Om n * lowMobiusLog U (n + 2)) - principal := by
    rw [R11Residual, longMobiusTail_eq_sum_longMobiusLog, hsplit, hPrinc]
    ring
  rw [this]
  exact hDisc

/-- Variant carrying an explicitly controlled collision sector: if in addition the free
grouped source differs from the canonical source by a `Λ`-weighted collision contribution of
size at most `eps2`, the free-source residual is within `eps + eps2` of the tail. -/
theorem r11_low_closed_implies_longMobius_residual_with_collision
    (s : Finset ℕ) (OmFree OmCan Bc : ℕ → ℝ) (U : ℕ) (principal eps eps2 : ℝ)
    (hDisc : LowDivisorDiscrepancyBound s OmCan U principal eps)
    (hPrinc : principal = ∑ n ∈ s, OmCan n * bLoc Bc n)
    (hColl : |R11Residual s OmFree Bc - R11Residual s OmCan Bc
        - (longMobiusTail s OmFree U - longMobiusTail s OmCan U)| ≤ eps2) :
    |R11Residual s OmFree Bc - longMobiusTail s OmFree U| ≤ eps + eps2 := by
  have hmain := r11_low_closed_implies_longMobius_residual s OmCan Bc U principal eps hDisc hPrinc
  have hsplit : R11Residual s OmFree Bc - longMobiusTail s OmFree U
      = (R11Residual s OmCan Bc - longMobiusTail s OmCan U)
        + (R11Residual s OmFree Bc - R11Residual s OmCan Bc
            - (longMobiusTail s OmFree U - longMobiusTail s OmCan U)) := by ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hmain hColl)

/-! ## 3. Coverage firewall (§13)

`CanonicalCoversFullR11` is the *future obligation*: that a supplied full physical source
sums to the canonical source on the range considered.  It is defined here purely so that it
can be referred to; it is **never** inhabited or proved, and no theorem of this development
has it as a conclusion. -/

/-- Future obligation, deliberately left uninhabited: the canonical source covers a supplied
full physical source on the range `s`. -/
def CanonicalCoversFullR11 (fullPhysical canonical : ℕ → ℝ) (s : Finset ℕ) : Prop :=
  ∑ n ∈ s, fullPhysical n = ∑ n ∈ s, canonical n

/-- The firewall is real: the internal bank is available for data for which coverage fails,
so no internal identity of this development can entail coverage. -/
theorem internal_bank_does_not_entail_coverage :
    ∃ (fullPhysical canonical : ℕ → ℝ) (s : Finset ℕ),
      ¬ CanonicalCoversFullR11 fullPhysical canonical s := by
  refine ⟨fun _ => 1, fun _ => 0, {0}, ?_⟩
  simp [CanonicalCoversFullR11]

/-! ## 4. Internal bank completeness

The conclusion below mentions only explicitly defined canonical objects: the CARD5 count,
the `4|4|2` allocation count and normalization, the factorial ledger, the exact collision
decomposition, the comparison typing, the Möbius–log split, the long-Möbius reindexing and
the matched determinant algebra.  It says nothing about any historical or full physical
R11 source. -/
theorem canonical_internal_bank_complete
    (L : R11Labels) (Omega : R11Labels → ℝ) (F : Fin 10 → ℝ)
    (OmegaBase Wn Bc : ℕ → ℝ) (U N : ℕ) (hN : N ≠ 0)
    (OmegaFree OmegaSq : ℕ → ℝ)
    (hsf : ∀ n, Squarefree n → OmegaSq n = OmegaFree n)
    (hns : ∀ n, ¬ Squarefree n → OmegaSq n = 0)
    {A B k d : ℕ} (hA : Odd A) (hB : Odd B) (hdet : A * B + 2 = k * d) :
    -- CARD5
    (Nat.choose 10 5 = 252 ∧ card5Selectors.card = 252) ∧
    (∑ _S ∈ card5Selectors, (1 : ℝ) * Omega L = 252 * Omega L) ∧
    -- 5|4|2
    (Alloc442.card = 3150 ∧ Nat.factorial 10 = 3150 * (Nat.factorial 4 * Nat.factorial 4 *
      Nat.factorial 2)) ∧
    (∑ P ∈ Alloc442,
        (∏ i ∈ P.1, F i) * (∏ i ∈ P.2, F i) * ∏ i ∈ Finset.univ \ (P.1 ∪ P.2), F i
      = 3150 * ∏ i, F i) ∧
    (card5Coefficient = 252 ∧ card5Coefficient ≠ 252 * 3150 ∧ (252 : ℚ) / 3150 = 2 / 25) ∧
    -- collisions
    (∀ n, OmegaSq n = OmegaFree n - Ecoll OmegaFree n) ∧
    (4 * 4 + 4 * 2 + 4 * 2 = 32) ∧
    -- comparison typing
    (∀ n, OmegaBase n * bFull Wn Bc n = OmegaCan OmegaBase Wn n * bLoc Bc n) ∧
    -- Möbius–log split and long-Möbius reindexing
    (vonMangoldt N = lowMobiusLog U N + longMobiusLog U N) ∧
    (longMobiusLog U N
      = ∑ κ ∈ N.divisors.filter (fun κ => U < N / κ),
          (moebius (N / κ) : ℝ) * Real.log (κ : ℝ)) ∧
    -- matched determinant
    ((A : ℤ) * (B : ℤ) - (k : ℤ) * (d : ℤ) = -2 ∧
      Nat.gcd A k = 1 ∧ Nat.gcd A d = 1 ∧ Nat.gcd B k = 1 ∧ Nat.gcd B d = 1) := by
  refine ⟨⟨choose_ten_five, card_card5Selectors⟩, card5_equal_n_collapse Omega L,
    ⟨card_Alloc442, factorial_ten_split⟩, factor542_normalization_mul F,
    ⟨card5_outer_coefficient_ledger.1, card5_outer_coefficient_ledger.2, ratio_252_3150⟩,
    fun n => omegaSquarefree_eq_free_sub_collision OmegaFree OmegaSq hsf hns n,
    crossGroupPairs_count,
    fun n => comparison_weight_typing OmegaBase Wn Bc n,
    vonMangoldt_split U N, longMobiusLog_reindex hN U, determinant_eq_neg_two hdet, ?_⟩
  exact determinant_pairwise_cross_coprime hA hB hdet

end Gate1B.R11
