import RequestProject.NANC.Gate01Consolidation.Centering
import RequestProject.NANC.Gate01Consolidation.AnalyticInterfaces

/-!
# Source interfaces (never inhabited)

Two items of the Tier-A source are **not** available to this development:

* the exact expected density `E(q)` in the discrepancy
  `Δ_{c,E}(q;a) = ∑_{n ≡ a (q)} c n − E(q)` — an **OPEN SOURCE FIELD**;
  in particular neither `E q = totalMass / q` nor `E q = totalMass / φ q`
  is assumed anywhere in this bank;
* the global high-`P₃` routing / exhaustion statement.

Both are recorded as explicit, never-inhabited interfaces.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- **EXPLICIT INTERFACE / OPEN SOURCE.**  The exact source expectation: the
assertion that the (unknown) source expected term `E` approximates the
progression mass of `c` to within `tol` uniformly over the modulus set.  No
formula for `E` is assumed and no inhabitant is produced. -/
def ExpectedDensitySourceInterface (K a : ℕ) (Qset : Finset ℕ) (c E : ℕ → ℝ)
    (tol : ℝ) : Prop :=
  ∀ q ∈ Qset, |finiteDiscrepancy K q a c E| ≤ tol

/-- **EXPLICIT INTERFACE / OPEN SOURCE.**  Global high-`P₃` routing: the claim
that the finitely many routed cells exhaust the high-`P₃` target.  Never
inhabited. -/
def HighP3ExhaustiveRoutingInterface {ι : Type*} (cells : Finset ι) (op : ι → ℝ)
    (total : ℝ) : Prop :=
  total = ∑ i ∈ cells, op i

/-- **Conditional.**  If the routing interface is granted and every routed cell
is bounded, the total is bounded.  Pure triangle inequality: nothing analytic is
proved here. -/
theorem highP3_total_bound_conditional {ι : Type*} {cells : Finset ι} {op : ι → ℝ}
    {total : ℝ} {bnd : ι → ℝ}
    (hroute : HighP3ExhaustiveRoutingInterface cells op total)
    (hcell : ∀ i ∈ cells, |op i| ≤ bnd i) :
    |total| ≤ ∑ i ∈ cells, bnd i := by
  rw [hroute]
  exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum hcell)

/-- **Conditional.**  The source interface, once granted, yields the standard
`λ₃`-weighted bound; this is the only use of `E` made anywhere in the bank, and
it is conditional. -/
theorem source_weighted_bound_conditional {K a : ℕ} {Qset : Finset ℕ} {c E : ℕ → ℝ}
    {w : ℕ → ℝ} {tol W : ℝ}
    (hsrc : ExpectedDensitySourceInterface K a Qset c E tol)
    (hw : ∀ q ∈ Qset, |w q| ≤ W) :
    |∑ q ∈ Qset, w q * finiteDiscrepancy K q a c E| ≤ (Qset.card : ℝ) * (W * tol) := by
  have hstep : ∀ q ∈ Qset, |w q * finiteDiscrepancy K q a c E| ≤ W * tol := by
    intro q hq
    rw [abs_mul]
    have hW : 0 ≤ W := le_trans (abs_nonneg (w q)) (hw q hq)
    exact mul_le_mul (hw q hq) (hsrc q hq) (abs_nonneg _) hW
  calc |∑ q ∈ Qset, w q * finiteDiscrepancy K q a c E|
      ≤ ∑ q ∈ Qset, |w q * finiteDiscrepancy K q a c E| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ Qset, W * tol := Finset.sum_le_sum hstep
    _ = (Qset.card : ℝ) * (W * tol) := by
        rw [Finset.sum_const, nsmul_eq_mul]

end Gate01Consolidation
end TwinPrimeProject
