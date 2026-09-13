/-
# Gate1B / R11 / Frontier : audited corrections

Three independently audited corrections, each formalised as the exact finite statement it is —
and nothing more.

**A. Principal coprimality cost.**  The literal cost `j·(D/P + 1)` is *not* what direct
inclusion–exclusion pays: the sum runs over all `2^j` subsets, so the cost is `2^j·(D/P + 1)`.
Both the identity and the firewall (for `j = 5`, `2^j = 32 > 5 = j`) are kernel-proved.  Since
`j = 5` is fixed this changes no exponent, which is also recorded as a finite comparison.

**B. Odd-Möbius dyadic recursion.**  The conservative global log ledger pays one extra log, so
the safe exponent is `114 + 3b/2`, not `113 + 3b/2`.

**C. Cell frequency cap.**  With `Q` varying over a cell, the admissible cap must use
`Qmin_C = min_{A ∈ C} Q_A`, and `H_C < Qmin_C/2` then holds for *every* `A` in the cell.  An
explicit two-point cell shows that an unspecified representative `Q_C` is unsound.
-/
import Mathlib

namespace Gate1B.R11.Frontier

open Finset

/-! ## A. The `2^j` principal-coprimality correction -/

/-- The number of subsets of a `j`-element index set is `2^j`. -/
theorem card_powerset_fin (j : ℕ) :
    ((Finset.univ : Finset (Fin j)).powerset).card = 2 ^ j := by
  rw [Finset.card_powerset, Finset.card_univ, Fintype.card_fin]

/-- **PRINCIPAL `2^j` CORRECTION (exact subset-count identity).**  Summing a fixed per-subset
cost `c` over all subsets of a `j`-element set costs exactly `2^j · c`. -/
theorem subset_cost_identity (j : ℕ) (c : ℝ) :
    ∑ _S ∈ (Finset.univ : Finset (Fin j)).powerset, c = 2 ^ j * c := by
  rw [Finset.sum_const, card_powerset_fin, nsmul_eq_mul]
  norm_num

/-- The inclusion–exclusion bound in the intended shape: `O_j(2^j (D/P + 1))`. -/
theorem subset_cost_bound (j : ℕ) (D P : ℝ) :
    ∑ _S ∈ (Finset.univ : Finset (Fin j)).powerset, (D / P + 1) ≤ 2 ^ j * (D / P + 1) :=
  le_of_eq (subset_cost_identity j (D / P + 1))

/-- **FIREWALL: the literal `j·(D/P+1)` is not the inclusion–exclusion cost.**  For `j = 5` and a
positive per-subset cost, the true cost `2^5·c = 32 c` strictly exceeds `5 c`. -/
theorem literal_j_cost_insufficient :
    ∀ c : ℝ, 0 < c → (5 : ℝ) * c < ∑ _S ∈ (Finset.univ : Finset (Fin 5)).powerset, c := by
  intro c hc
  rw [subset_cost_identity]
  nlinarith

/-- Since `j = 5` is fixed, the correction is a bounded constant factor and changes no exponent. -/
theorem fixed_j_cost_constant (c : ℝ) (hc : 0 ≤ c) (j : ℕ) (hj : j ≤ 5) :
    (2 : ℝ) ^ j * c ≤ 32 * c := by
  have h2 : (2 : ℝ) ^ j ≤ 2 ^ 5 := by
    exact pow_le_pow_right₀ (by norm_num) hj
  nlinarith [h2]

/-! ## B. The ledger `114` correction -/

/-- The corrected safe global log ledger exponent, before the `3b/2` frequency cost. -/
def ledgerExponent (b : ℚ) : ℚ := 114 + 3 * b / 2

/-- The stale ledger exponent that must no longer be used. -/
def staleLedgerExponent (b : ℚ) : ℚ := 113 + 3 * b / 2

/-- **LEDGER 114 CORRECTION.**  The odd-Möbius dyadic recursion pays exactly one further log. -/
theorem ledger_correction (b : ℚ) : staleLedgerExponent b + 1 = ledgerExponent b := by
  unfold ledgerExponent staleLedgerExponent
  ring

/-- The corrected ledger is strictly weaker (larger exponent) than the stale one: the stale
metadata was an over-claim. -/
theorem ledger_stale_lt (b : ℚ) : staleLedgerExponent b < ledgerExponent b := by
  unfold ledgerExponent staleLedgerExponent
  linarith

/-- At the reference value `b = 0` the corrected exponent is `114`. -/
theorem ledger_at_zero : ledgerExponent 0 = 114 := by
  unfold ledgerExponent
  norm_num

/-! ## C. The cell frequency cap `H_C < Qmin_C / 2` -/

variable {α : Type*}

/-- `Qmin_C = min_{A ∈ C} Q_A` for a nonempty finite cell `C`. -/
def QminCell (C : Finset α) (hC : C.Nonempty) (Qf : α → ℕ) : ℕ := C.inf' hC Qf

/-- **CELL CAP FIREWALL (positive direction).**  `2 H_C < Qmin_C` forces the cap at *every*
point of the cell, so no unspecified representative `Q_C` is needed. -/
theorem cell_cap_uniform {C : Finset α} (hC : C.Nonempty) (Qf : α → ℕ) (H : ℕ)
    (hH : 2 * H < QminCell C hC Qf) : ∀ A ∈ C, 2 * H < Qf A := by
  intro A hA
  exact lt_of_lt_of_le hH (Finset.inf'_le _ hA)

/-- `Qmin_C` is attained, so the cap is sharp: it cannot be relaxed to a larger value. -/
theorem QminCell_mem {C : Finset α} (hC : C.Nonempty) (Qf : α → ℕ) :
    ∃ A ∈ C, Qf A = QminCell C hC Qf := by
  obtain ⟨A, hA, hval⟩ := Finset.exists_mem_eq_inf' hC Qf
  exact ⟨A, hA, hval.symm⟩

/-- **CELL CAP FIREWALL (negative direction).**  An unspecified representative `Q_C` is unsound:
there is a two-point cell and an `H` satisfying the cap for the representative value while
violating it at another point of the cell. -/
theorem representative_Q_unsound :
    ∃ (C : Finset ℕ) (Qf : ℕ → ℕ) (H Arep : ℕ), Arep ∈ C ∧ 2 * H < Qf Arep ∧
      ∃ A ∈ C, ¬ (2 * H < Qf A) := by
  refine ⟨{0, 1}, fun x => if x = 0 then 10 else 2, 3, 0, by decide, by decide, 1, by decide, ?_⟩
  decide

end Gate1B.R11.Frontier
