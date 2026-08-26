import Mathlib

/-!
# Fixed-depth convolution coefficient-majorant (§13.4)

The routing coefficients `λ_q^{(j)} = Σ_{u ∏_{i≠j} w_i = q} γ_u ∏_{i≠j} ψ_i(w_i)`
are a *fixed finite Dirichlet convolution* of divisor-bounded functions.  The exact
analytic weights (`γ` a Heath–Brown convolution, `ψ_i` smooth dyadic) are not
representable directly, so — as the master task permits — we formalize the
**discrete coefficient-majorant theorem**:

*  the Dirichlet convolution of majorant-bounded arithmetic functions is bounded by
   the convolution of the majorants (`maj_mul`);
*  hence a fixed finite convolution of functions each bounded by a common nonneg
   divisor-type majorant `τ` is bounded by `τ^depth` (`maj_fixed_depth`).

This is the exact statement `|λ_q^{(j)}| ≪ τ_{C(r)}(q)`: divisor-boundedness is
preserved, with an exponent (`s.card`) depending only on the depth.
-/

namespace ShiftedMobiusBank

open ArithmeticFunction

/-- `Majorizes F f` says the nonnegative arithmetic function `F` is a pointwise
majorant of `|f|`.  This is the discrete "divisor-bounded by `F`" relation. -/
def Majorizes (F f : ArithmeticFunction ℝ) : Prop :=
  (∀ n, 0 ≤ F n) ∧ ∀ n, |f n| ≤ F n

/-- The coefficient-majorant theorem for a binary Dirichlet convolution:
if `|f| ≤ F` and `|g| ≤ G` with `F, G ≥ 0`, then `|f * g| ≤ F * G`. -/
theorem maj_mul {F f G g : ArithmeticFunction ℝ}
    (hf : Majorizes F f) (hg : Majorizes G g) : Majorizes (F * G) (f * g) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · rw [mul_apply]
    apply Finset.sum_nonneg; intro x _; exact mul_nonneg (hf.1 _) (hg.1 _)
  · rw [mul_apply, mul_apply]
    calc |∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2|
        ≤ ∑ x ∈ n.divisorsAntidiagonal, |f x.1 * g x.2| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x ∈ n.divisorsAntidiagonal, F x.1 * G x.2 := by
          apply Finset.sum_le_sum; intro x _
          rw [abs_mul]
          exact mul_le_mul (hf.2 _) (hg.2 _) (abs_nonneg _) (hf.1 _)

/-- The multiplicative unit `1` majorizes itself (base case for the finite
convolution). -/
theorem maj_one : Majorizes (1 : ArithmeticFunction ℝ) (1 : ArithmeticFunction ℝ) := by
  refine ⟨fun n => ?_, fun n => ?_⟩ <;>
  · simp only [ArithmeticFunction.one_apply]; split <;> simp

/-- Coefficient-majorant for a finite product of Dirichlet convolutions indexed by
a `Finset`: `|∏_{i∈s} f i| ≤ ∏_{i∈s} F i`. -/
theorem maj_finset_prod {ι : Type*} (s : Finset ι) (F f : ι → ArithmeticFunction ℝ)
    (h : ∀ i ∈ s, Majorizes (F i) (f i)) :
    Majorizes (∏ i ∈ s, F i) (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using maj_one
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact maj_mul (h a (by simp)) (ih (fun i hi => h i (by simp [hi])))

/-- §13.4 — **fixed-depth divisor-bound preservation**.  If every factor `f i`
(`i ∈ s`) is divisor-bounded by a common nonnegative majorant `τ`, then the
fixed-depth convolution `∏_{i∈s} f i` is divisor-bounded by `τ^{|s|}`, i.e. the
majorant exponent depends only on the depth `|s|`. -/
theorem maj_fixed_depth {ι : Type*} (s : Finset ι) (tau : ArithmeticFunction ℝ)
    (f : ι → ArithmeticFunction ℝ) (hτ : ∀ n, 0 ≤ tau n)
    (hf : ∀ i ∈ s, ∀ n, |f i n| ≤ tau n) :
    Majorizes (tau ^ s.card) (∏ i ∈ s, f i) := by
  have := maj_finset_prod s (fun _ => tau) f (fun i hi => ⟨hτ, hf i hi⟩)
  simpa [Finset.prod_const] using this

end ShiftedMobiusBank
