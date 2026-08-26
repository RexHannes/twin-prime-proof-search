/-
# Gate 1B v8.2 — conditional zero-mode compiler

The zero-mode rewriting of the centred residue is available **only** under the
explicit hypothesis `E = MT`.  This file states the compiler in that form, and
the partition-of-unity version, and records that the hypothesis is genuinely
needed (see `Gate1B.SafeAlgebra.countermodel_E_compiler_needs_E_eq_MT`).
-/
import Mathlib
import Gate1B.SafeAlgebra.GlobalZeroMode
import Gate1B.SafeAlgebra.CountermodelsV82

namespace Gate1B.SafeExtensions

open Gate1B.SafeAlgebra

variable {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- **The conditional zero-mode compiler.**  If the physical count agrees with
its expected term, the centred residue vanishes identically, hence so do both
its zero mode and its nonzero part. -/
theorem zeroModeCompiler_of_E_eq_MT (E MT : ι → ℂ) (h : E = MT) :
    (∀ i, E i - MT i = 0) ∧ zeroMode (fun i => E i - MT i) = 0 ∧
      nonzeroPart (fun i => E i - MT i) = 0 := by
  obtain ⟨h1, h2⟩ := zeroMode_rewrite_of_E_eq_MT E MT h
  exact ⟨fun i => by simp [h], h1, h2⟩

omit [Fintype ι] [Nonempty ι] in
/-- **Partition-of-unity version.**  If each piece of a finite partition
satisfies `E = MT`, the assembled residue still vanishes. -/
theorem zeroModeCompiler_partition {J : Type*} [Fintype J]
    (E MT : J → ι → ℂ) (h : ∀ j, E j = MT j) (i : ι) :
    ∑ j, (E j i - MT j i) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [h j]
  ring

/-- The hypothesis is load-bearing: without `E = MT` the compiler's conclusion
can fail. -/
theorem zeroModeCompiler_hypothesis_needed :
    ∃ E MT : Fin 2 → ℂ, zeroMode (fun i => E i - MT i) ≠ 0 :=
  countermodel_E_compiler_needs_E_eq_MT

end Gate1B.SafeExtensions
