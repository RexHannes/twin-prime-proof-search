import Mathlib

/-! The finite algebraic core of F1 global centering. -/

namespace ShiftedMobiusBank

/-- For finitely many pieces, centering each piece and then aggregating is exactly
centering by the aggregate main term. -/
theorem F1_GLOBAL_CENTERING_IDENTITY {ι N R : Type*}
    [Fintype ι] [Fintype N] [AddCommGroup R]
    (piece mainTerm offDiagonal : ι → N → R) (a b w : N → R)
    (ha : ∀ n, a n = ∑ P, piece P n)
    (hpiece : ∀ P n, piece P n = mainTerm P n + offDiagonal P n)
    (hb : ∀ n, b n = ∑ P, mainTerm P n)
    (hw : ∀ n, w n = a n - b n) :
    ∀ n, w n = ∑ P, offDiagonal P n := by
  intro n
  rw [hw, ha, hb]
  simp_rw [hpiece]
  rw [Finset.sum_add_distrib]
  exact add_sub_cancel_left _ _

/-- Named definitions matching the ledger notation `b_n = Σ_P MT_P(n)` and
`w_n = Σ_P OD_P(n)`. -/
def aggregateMainTerm {ι N R : Type*} [Fintype ι] [AddCommMonoid R]
    (mainTerm : ι → N → R) (n : N) : R := ∑ P, mainTerm P n

def aggregateOffDiagonal {ι N R : Type*} [Fintype ι] [AddCommMonoid R]
    (offDiagonal : ι → N → R) (n : N) : R := ∑ P, offDiagonal P n

end ShiftedMobiusBank
