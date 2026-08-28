/-
# Gate 1B v8.4 — hybrid h-Poisson: the analytic compiler

**Status: CONDITIONAL_FINITE.**

The Poisson identity itself is **not** proved and **not** axiomatised here: it is
carried as the explicit hypothesis `hpoisson`, which states that the smooth
`h`-weight, summed along each residue class of the period `P = p c₀`, equals its
(finite, truncated) dual expansion.  Everything downstream of that hypothesis —
the interchange of summation, the phase recombination, and the appearance of the
finite residue factor of `HybridHPoissonResidue.lean` — is derived.

This is a *coordinate transform*, not an estimate: it is not a Gate estimate and
gives no cancellation by itself (see `CountermodelsV84.lean`, item B, and the
resource ledger).
-/
import Mathlib
import Gate1B.SafeAlgebra.HybridHPoissonResidue

namespace Gate1B.SafeExtensions

open Finset
open Gate1B.SafeAlgebra

/-- **Hybrid `h`-Poisson compiler (conditional).**  Given the dual expansion of
the class-summed weight `W`, the twisted `h`-sum equals the exact dual `m`-sum,
each term carrying the finite residue factor `p · 1_{t = a}` and the `c₀` Gauss
factor. -/
theorem hybrid_hPoisson_conditional {p c0 : ℕ} [NeZero p] [NeZero c0] {ι : Type*}
    (psiP : AddChar (ZMod p) ℂ) (hprim : psiP.IsPrimitive)
    (chiBar psiC0 : ZMod c0 → ℂ)
    (D : Finset ι) (vhat : ι → ℂ) (tfreq : ι → ZMod p) (mfreq : ι → ZMod c0)
    (W : ZMod p × ZMod c0 → ℂ) (P : ℂ) (a : ZMod p)
    (hpoisson : ∀ x : ZMod p × ZMod c0,
      W x = (1 / P) * ∑ i ∈ D, vhat i * (psiP (-(tfreq i) * x.1) * psiC0 (x.2 * mfreq i))) :
    ∑ x : ZMod p × ZMod c0, W x * (chiBar x.2 * psiP (a * x.1))
      = (1 / P) * ∑ i ∈ D,
          vhat i * ((if tfreq i = a then (p : ℂ) else 0)
            * ∑ b : ZMod c0, chiBar b * psiC0 (b * mfreq i)) := by
  classical
  have hphase : ∀ (t : ZMod p) (y : ZMod p),
      psiP ((a - t) * y) = psiP (a * y) * psiP (-(t) * y) := by
    intro t y
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  have step1 : ∀ x : ZMod p × ZMod c0, W x * (chiBar x.2 * psiP (a * x.1))
      = (1 / P) * ∑ i ∈ D,
          vhat i * (chiBar x.2 * (psiP ((a - tfreq i) * x.1) * psiC0 (x.2 * mfreq i))) := by
    intro x
    rw [hpoisson x, mul_assoc, Finset.sum_mul]
    refine congrArg (fun z => (1 / P) * z) (Finset.sum_congr rfl (fun i _ => ?_))
    rw [hphase (tfreq i) x.1]
    ring
  rw [Finset.sum_congr rfl (fun x _ => step1 x), ← Finset.mul_sum, Finset.sum_comm]
  refine congrArg (fun z => (1 / P) * z) (Finset.sum_congr rfl (fun i _ => ?_))
  rw [← Finset.mul_sum,
    hybridResidueTransform psiP hprim chiBar psiC0 a (tfreq i) (mfreq i)]

end Gate1B.SafeExtensions
