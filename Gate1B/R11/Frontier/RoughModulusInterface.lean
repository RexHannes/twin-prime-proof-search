/-
# Gate1B / R11 / Frontier : rough-modulus variance — explicit analytic-input interface

The audited analytic theorem

```
∑_q ∑_a^* |E_q(a; y)|²  ≪_j  D·R + D²/P
```

is **not** claimed here as kernel-proved: the primitive multiplicative large sieve it rests on is
not available as a formal theorem in the imported environment, and this bank does **not** postulate
it as a custom axiom.  Option **B** of the brief is taken instead:

* the primitive large-sieve statement appears as an *explicit hypothesis* `hLargeSieve`
  (per primitive conductor), and the sparse remainder as an explicit hypothesis `hRemainder`;
* the downstream finite reduction — the conductor-wise summation and the comparison against
  `D·R + D²/P` — is kernel-proved conditionally on those hypotheses.

The last section shows the analytic hypothesis is genuinely load-bearing: without it the finite
reduction is false, so nothing here smuggles the analytic content in.

Research-status metadata (not a Lean proof): `ROUGH-MODULUS VARIANCE : OPUS-AUDITED ANALYTIC BANK`.
-/
import Mathlib

namespace Gate1B.R11.Frontier

open Finset

variable {ι : Type*}

/-- **The analytic input, as an explicit hypothesis and never as an axiom.**  For each primitive
conductor `f` in the finite conductor set, the primitive multiplicative large sieve is assumed to
bound the conductor-`f` variance `V f` by `D · R_f`. -/
def PrimitiveLargeSieveInput (Conds : Finset ι) (D : ℝ) (Rf V : ι → ℝ) : Prop :=
  ∀ f ∈ Conds, V f ≤ D * Rf f

/-- The sparse/diagonal remainder input: the non-large-sieve part of the variance is bounded by
`D²/P`. -/
def SparseRemainderInput (Conds : Finset ι) (D P : ℝ) (W : ι → ℝ) : Prop :=
  ∑ f ∈ Conds, W f ≤ D ^ 2 / P

/-- **CONDITIONAL ROUGH-MODULUS VARIANCE BOUND.**  Given the explicit primitive large-sieve input
and the explicit sparse-remainder input, the conductor-wise decomposition of the total variance
satisfies `total ≤ D·R + D²/P`.  Everything except the two named inputs is kernel-proved. -/
theorem rough_modulus_variance_of_input (Conds : Finset ι) (D P R total : ℝ) (Rf V W : ι → ℝ)
    (hLargeSieve : PrimitiveLargeSieveInput Conds D Rf V)
    (hRemainder : SparseRemainderInput Conds D P W)
    (hR : ∑ f ∈ Conds, Rf f = R)
    (hdecomp : total = ∑ f ∈ Conds, (V f + W f)) :
    total ≤ D * R + D ^ 2 / P := by
  have hV : ∑ f ∈ Conds, V f ≤ D * R := by
    calc ∑ f ∈ Conds, V f ≤ ∑ f ∈ Conds, D * Rf f :=
          Finset.sum_le_sum fun f hf => hLargeSieve f hf
      _ = D * ∑ f ∈ Conds, Rf f := (Finset.mul_sum _ _ _).symm
      _ = D * R := by rw [hR]
  rw [hdecomp, Finset.sum_add_distrib]
  exact add_le_add hV hRemainder

/-- The variance target itself, recorded as a proposition so that downstream modules can refer to
it *without* any module ever inhabiting it. -/
def RoughModulusVarianceTarget (D P R total : ℝ) : Prop :=
  total ≤ D * R + D ^ 2 / P

/-- Restatement of the conditional theorem in terms of the named target. -/
theorem roughModulusVarianceTarget_of_input (Conds : Finset ι) (D P R total : ℝ) (Rf V W : ι → ℝ)
    (hLargeSieve : PrimitiveLargeSieveInput Conds D Rf V)
    (hRemainder : SparseRemainderInput Conds D P W)
    (hR : ∑ f ∈ Conds, Rf f = R)
    (hdecomp : total = ∑ f ∈ Conds, (V f + W f)) :
    RoughModulusVarianceTarget D P R total :=
  rough_modulus_variance_of_input Conds D P R total Rf V W hLargeSieve hRemainder hR hdecomp

/-- **The analytic input is load-bearing.**  Dropping the primitive large-sieve hypothesis makes
the finite reduction false: here the decomposition, the remainder input and the `R`-identity all
hold, yet the target fails. -/
theorem largeSieve_input_load_bearing :
    ∃ (Conds : Finset ℕ) (D P R total : ℝ) (Rf V W : ℕ → ℝ),
      0 ≤ D ∧ SparseRemainderInput Conds D P W ∧ (∑ f ∈ Conds, Rf f) = R ∧
        total = ∑ f ∈ Conds, (V f + W f) ∧ ¬ RoughModulusVarianceTarget D P R total := by
  refine ⟨{0}, 1, 1, 0, 100, fun _ => 0, fun _ => 100, fun _ => 0, by norm_num, ?_, ?_, ?_, ?_⟩
  · unfold SparseRemainderInput
    norm_num
  · norm_num
  · norm_num
  · unfold RoughModulusVarianceTarget
    norm_num

end Gate1B.R11.Frontier
