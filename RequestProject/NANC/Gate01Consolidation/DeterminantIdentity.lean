import Mathlib

/-!
# BANK K — the determinant identity

Although the determinant *route* is analytically retired, the exact algebra is
banked here.

With `m n + 2 = q r₀`, `v = n + h q` and `s = r₀ + h m`:

`r₀ v − n s = 2 h`   (**DET**).

Ledger:

```text
DETERMINANT_IDENTITY               = PROVED
DETERMINANT_PIVOT_STRICT_REDUCTION = NOT PROVED
DETERMINANT_PIVOT                  = REFORMULATION_ONLY IN CURRENT AUDIT
```

The last two lines are ledger metadata (encoded in `StatusLedger.lean`), not
Lean theorems.  No analytic theorem is attached to the identity below.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

/-- **DET.**  The exact shifted determinant identity. -/
theorem det_identity {m n q r0 h v s : ℤ} (hq : m * n + 2 = q * r0)
    (hv : v = n + h * q) (hs : s = r0 + h * m) :
    r0 * v - n * s = 2 * h := by
  subst hv; subst hs
  linear_combination (-h) * hq

/-- The same identity in the equivalent "shifted product" form `m n + 2 = q r₀`
read as a divisibility statement: the determinant is the fixed shift `2` times
the shift parameter `h`, never an averaged shift. -/
theorem det_identity_fixed_shift {m n q r0 h : ℤ} (hq : m * n + 2 = q * r0) :
    r0 * (n + h * q) - n * (r0 + h * m) = 2 * h :=
  det_identity hq rfl rfl

end Gate01Consolidation
end TwinPrimeProject
