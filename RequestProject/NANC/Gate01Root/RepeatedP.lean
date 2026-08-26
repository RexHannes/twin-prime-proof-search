import Gate04Root.PPDInterfaces
import RequestProject.NANC.Gate01Root.R4CInterfaces

/-!
# Gate01Root: the repeated-`p` finite inequality

A generic finite inequality: from a pointwise bound `|B e p| ≤ C` and cardinal
bounds `|E| ≤ E₀`, `|P| ≤ P₀`,

`∑_p |G(p,p)|² ≤ P₀ E₀² C⁴`.

The symbolic instantiation `E₀ = M²`, `P₀ = L`, `C = L/H` gives the budget
`M⁴ L⁵ / H⁴`.

**Conditional**: the pointwise input `|B e p| ≤ C` is the analytic B-POINT
statement, which is *not* proved anywhere.  The inequality below is therefore a
conditional bound, never an unconditional numerical claim.
-/

namespace RouteAFibreFrame
namespace Gate01Root

variable {E P : Type*} [Fintype E] [Fintype P]

/-- **Repeated-`p` bound from a pointwise bound.** -/
theorem repeatedP_bound_of_pointwise {B : E → P → ℂ} {C E₀ P₀ : ℝ}
    (hB : ∀ e p, ‖B e p‖ ≤ C)
    (hE : (Fintype.card E : ℝ) ≤ E₀) (hP : (Fintype.card P : ℝ) ≤ P₀) :
    diagColSum B ≤ P₀ * E₀ ^ 2 * C ^ 4 :=
  Gate04Root.repeatedP_bound_of_pointwise hB hE hP

/-- **Symbolic instantiation** `E₀ = M²`, `P₀ = L`, `C = L/H`. -/
theorem repeatedP_symbolic_bound {M L H : ℝ} (hH : H ≠ 0) :
    L * (M ^ 2) ^ 2 * (L / H) ^ 4 = M ^ 4 * L ^ 5 / H ^ 4 :=
  Gate04Root.repeatedP_symbolic_bound hH

/-- The conditional repeated-`p` budget in symbolic form:  under the (unproved)
B-POINT pointwise bound `|B e p| ≤ L/H` and the cardinal bounds `|E| ≤ M²`,
`|P| ≤ L`, the repeated-`p` mass is at most `M⁴ L⁵ / H⁴`. -/
theorem repeatedP_conditional_symbolic {B : E → P → ℂ} {M L H : ℝ} (hH : H ≠ 0)
    (hB : ∀ e p, ‖B e p‖ ≤ L / H)
    (hE : (Fintype.card E : ℝ) ≤ M ^ 2) (hP : (Fintype.card P : ℝ) ≤ L) :
    diagColSum B ≤ M ^ 4 * L ^ 5 / H ^ 4 := by
  have h := repeatedP_bound_of_pointwise hB hE hP
  rwa [repeatedP_symbolic_bound (M := M) (L := L) hH] at h

end Gate01Root
end RouteAFibreFrame
