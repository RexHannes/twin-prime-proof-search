/-
# Gate 1B v8.3 — Tier-3 zero-mode residual addendum

**Status: PROVED_ALGEBRAIC + COUNTERMODEL.**

Reusing the v8.2 `GlobalZeroMode` bank, we record the exact bookkeeping that
relates the *historical* centred sum (centred at an expected term `E`) to the
*canonical* centred sum (centred at `canonicalMain`), through the source
residual

    R_E(E) = ∑_q λ(q) (E q - canonicalMain q).

Exact sign: `historical = canonical - R_E(E)`.

Firewall: `expectedTerm_not_freely_choosable` shows that whenever some
`λ(q₀) ≠ 0` the residual can be moved by an arbitrary prescribed amount by
changing `E` at the single point `q₀`, while everything else is untouched.  So
`R_E` is a genuine external source interface: it is **not** determined by the
nonzero-frequency data and it is **not** bounded here.
-/
import Mathlib
import Gate1B.SafeAlgebra.GlobalZeroMode

namespace Gate1B.SafeExtensions

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The source residual `R_E(E) = ∑ λ(q) (E q - canonicalMain q)`. -/
noncomputable def RE (lam canonicalMain E : ι → ℂ) : ℂ :=
  ∑ q : ι, lam q * (E q - canonicalMain q)

/-- The historical centred sum, centred at the expected term `E`. -/
noncomputable def historicalCenteredSum (lam F E : ι → ℂ) : ℂ :=
  ∑ q : ι, lam q * (F q - E q)

/-- The canonical centred sum, centred at `canonicalMain`. -/
noncomputable def canonicalCenteredSum (lam F canonicalMain : ι → ℂ) : ℂ :=
  ∑ q : ι, lam q * (F q - canonicalMain q)

/-- **Exact sign identity**: `historical = canonical - R_E(E)`. -/
theorem historical_eq_canonical_sub_residual (lam F canonicalMain E : ι → ℂ) :
    historicalCenteredSum lam F E
      = canonicalCenteredSum lam F canonicalMain - RE lam canonicalMain E := by
  unfold historicalCenteredSum canonicalCenteredSum RE
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun q _ => by ring

/-- **The expected term is not freely choosable.**  If `λ(q₀) ≠ 0`, then for any
prescribed shift `δ` there is an expected term differing from `E` only at `q₀`
whose residual differs by exactly `δ`. -/
theorem expectedTerm_not_freely_choosable (lam canonicalMain E : ι → ℂ) (q0 : ι)
    (hq0 : lam q0 ≠ 0) (delta : ℂ) :
    ∃ E' : ι → ℂ, (∀ q, q ≠ q0 → E' q = E q) ∧
      RE lam canonicalMain E' = RE lam canonicalMain E + delta := by
  classical
  refine ⟨Function.update E q0 (E q0 + delta / lam q0), ?_, ?_⟩
  · intro q hq
    simp [Function.update_of_ne hq]
  · unfold RE
    have hsplit : ∑ q : ι, (lam q * (Function.update E q0 (E q0 + delta / lam q0) q
        - canonicalMain q) - lam q * (E q - canonicalMain q)) = delta := by
      rw [Finset.sum_eq_single q0]
      · simp only [Function.update_self]
        field_simp
        ring
      · intro q _ hq
        simp [Function.update_of_ne hq]
      · intro h; exact absurd (Finset.mem_univ q0) h
    have hdiff : (∑ q : ι, lam q * (Function.update E q0 (E q0 + delta / lam q0) q
        - canonicalMain q)) - (∑ q : ι, lam q * (E q - canonicalMain q)) = delta := by
      rw [← Finset.sum_sub_distrib]; exact hsplit
    linear_combination hdiff

/-- The residual vanishes exactly when the expected term agrees with the
canonical main term in the `λ`-weighted average. -/
theorem RE_eq_zero_of_eq (lam canonicalMain E : ι → ℂ) (h : E = canonicalMain) :
    RE lam canonicalMain E = 0 := by
  subst h
  simp [RE]

end Gate1B.SafeExtensions
