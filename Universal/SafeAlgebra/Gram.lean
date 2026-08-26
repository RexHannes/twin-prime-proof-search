/-
# Universal safe algebra — Gram / synthesis identities (re-export)

Proved in `UniversalV8/DiagonalBaseline.lean` and `UniversalV8/BlockGram.lean`:
the exact diagonal/off-diagonal decomposition, the quadratic-form version, the genuine
block Gram identity through operator adjoints, and the normalized synthesis bound.

The retracted "Hilbert–Schmidt" identity for arbitrary bounded operators is not stated
anywhere.
-/
import UniversalV8.BlockGram

namespace Universal.SafeAlgebra

export UniversalV8 (gram_expand gram_eq_diag_add_offdiag diagOffDiag_budget
  diagOffDiag_budget_remaining quadraticForm_eq_diag_add_offDiag synthesis
  blockGramIdentity synthesis_norm_sq synthesis_norm_le_sum normalizedSynthesisBound
  actualVectorTransport inner_apply_le_of_apply_norm_le)

end Universal.SafeAlgebra
