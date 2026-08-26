/-
# Gate 1B v8.2 — the global zero mode

Finite Fourier bookkeeping for a centred residue over a nonempty finite index
set: the split into the zero mode (the mean) and the nonzero part, the exact
reconstruction identity, the vanishing of the mean of the nonzero part, and the
invariance of the nonzero part under subtracting a constant expected term.

The conditional rewriting statement `zeroMode_rewrite_of_E_eq_MT` carries the
hypothesis `E = MT` **explicitly**; it is not assumed anywhere.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The zero mode (mean) of a finite family. -/
noncomputable def zeroMode (f : ι → ℂ) : ℂ := (∑ i, f i) / (Fintype.card ι)

/-- The nonzero part of a finite family. -/
noncomputable def nonzeroPart (f : ι → ℂ) : ι → ℂ := fun i => f i - zeroMode f

omit [Nonempty ι] in
/-- **Exact reconstruction**: every value is its zero mode plus its nonzero
part. -/
theorem centeredResidue_eq_zeroMode_add_nonzero (f : ι → ℂ) (i : ι) :
    f i = zeroMode f + nonzeroPart f i := by
  simp [nonzeroPart]

/-- The nonzero part has vanishing mean. -/
theorem sum_nonzeroPart_eq_zero (f : ι → ℂ) : ∑ i, nonzeroPart f i = 0 := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι))
  simp only [nonzeroPart, zeroMode, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  field_simp
  ring

/-- **The nonzero part does not see a constant expected term.** -/
theorem nonzeroPart_independent_expectedTerm (f : ι → ℂ) (c : ℂ) :
    nonzeroPart (fun i => f i - c) = nonzeroPart f := by
  have hcard : (Fintype.card ι : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι))
  funext i
  simp only [nonzeroPart, zeroMode, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, sub_div]
  rw [mul_comm, mul_div_assoc, div_self hcard, mul_one]
  ring

omit [Nonempty ι] in
/-- **Conditional zero-mode rewriting.**  If the physical count equals its
expected term, the centred residue has vanishing zero mode and vanishing
nonzero part.  The hypothesis is explicit: nothing here proves `E = MT`. -/
theorem zeroMode_rewrite_of_E_eq_MT (E MT : ι → ℂ) (h : E = MT) :
    zeroMode (fun i => E i - MT i) = 0 ∧ nonzeroPart (fun i => E i - MT i) = 0 := by
  subst h
  constructor
  · simp [zeroMode]
  · funext i
    simp [nonzeroPart, zeroMode]

end Gate1B.SafeAlgebra
