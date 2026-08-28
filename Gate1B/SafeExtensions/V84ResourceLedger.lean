/-
# Gate 1B v8.4 — anti-loop / resource ledger

**COMMENTS ONLY.  ZERO DECLARATIONS.**

This ledger records which arithmetic resources have already been *spent* by the
v8.4 algebra, so that they are not counted twice later.

| resource | state after v8.4 | where |
|---|---|---|
| `μ(e)` | **SPENT** exactly against the induced Gauss factor: `β(ce) τ_{ce} = ρ(c,e) χ*(e) τ_c`. Not a remaining cancellation resource. | `InducedMuCancellation.lean` |
| `μ(c₀)` | **SPENDABLE / SPENT** by primitive-projector Möbius inversion; in the generic sector `gcd(c₀, A-1) = 1` it disappears entirely, leaving `1/c₀`. Must not be re-counted as an independent sign. | `PrimitiveProjectorMu.lean`, `MuSpentByProjector.lean` |
| `δ₁, …, δ₇` | **UNSPENT** — genuine centered source resources; nothing in v8.4 consumes them. | (source) |
| prime character mod `p` | **COLLAPSED EXACTLY** before Cauchy: `∑_{χ mod p} τ_p(χ) χ(A) = (p-1) e_p(A⁻¹)`, `τ_p(χ₀) = -1`. The `+1` correction is kept as an exact separate term. | `PrimeCharacterCollapse.lean`, `PrimeCharacterCollapseNormalized.lean` |
| `h`-Poisson | **COORDINATE TRANSFORM / POWER RECOVERY** only. It is not itself an arbitrary-log cancellation, and the Poisson step is carried as a hypothesis. | `HybridHPoissonResidue.lean`, `HybridHPoisson.lean` |
| full `d = c₀` projector | **RETURNS THE H7 DETERMINANT SHELL** — anti-loop certificate; no analytic gain. | `H7SelfDuality.lean` |
| dual-window uniqueness | **TRUNCATED WINDOWS ONLY**; the rapid-decay truncation of the infinite Fourier tail remains ANALYTIC_INTERFACE_ONLY. | `DualResidueUniqueness.lean` |
| natural-scale capacity | fixed positive-power deficit reduced to exponent `0`; **no** log saving. | `H7DualDetCapacity.lean`, `H7LogClosureFirewall.lean` |

DOUBLE-COUNTING RULE.  A resource marked SPENT above may not appear again in any
later budget, margin or capacity computation.
-/
import Mathlib
