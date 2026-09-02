/-
# Universal / D0WP — the large-`rSharp` conditional compiler

**Status of this module: KERNEL_PROVED algebraic implication.**

This is the exact algebraic step

```
(finite Fourier norm sqrt rSharp)  +  (residue-class energy bounds)  +  (D W = Q)
      ⟹
|S| ≤ Q · coefficientNorm² · (rSharp/Q + 1/D + 1/W + 1/rSharp)^{1/2}
```

and nothing more.  The three hypotheses are *explicit real inequalities*: the
Fourier bound in the shape produced by `Kker_bilinear_bound`, and the two energy
bounds in the shape produced by `residue_pushforward_energy`.

**Explicit non-claim.**  No logarithmic saving is asserted here.  Turning the
displayed bound into a `L^{-B}` saving requires the analytic range hypotheses
(`HardP3PhysicalRange`) and is *not* part of this kernel statement.
-/
import Mathlib

namespace Universal.D0WP

/-- **LARGE-`rSharp` COMPILER (kernel-proved).**

`S` is any real quantity dominated by `sqrt rSharp · sqrt EX · sqrt EY` (the
output of the finite Fourier bound), where `EX`, `EY` obey the residue-class
energy bounds with dyadic lengths `D`, `W` and coefficient norm `cN`.  With
`Q = D W` the conclusion is the stated square-root bound.  The bounding
expression is in fact an identity, not a lossy estimate. -/
theorem large_rSharp_compiler
    {S rs D W Q cN EX EY : ℝ}
    (hrs : 0 < rs) (hD : 0 < D) (hW : 0 < W) (hQ : Q = D * W)
    (hEX0 : 0 ≤ EX) (hEY0 : 0 ≤ EY)
    (hS : S ≤ Real.sqrt rs * Real.sqrt EX * Real.sqrt EY)
    (hEX : EX ≤ (1 + D / rs) * (cN ^ 2 * D))
    (hEY : EY ≤ (1 + W / rs) * (cN ^ 2 * W)) :
    S ≤ Q * cN ^ 2 * Real.sqrt (rs / Q + 1 / D + 1 / W + 1 / rs) := by
  have hQ0 : 0 < Q := by rw [hQ]; positivity
  have hfac : (0:ℝ) ≤ Q * cN ^ 2 := by positivity
  have key : rs * EX * EY ≤ (Q * cN ^ 2) ^ 2 * (rs / Q + 1 / D + 1 / W + 1 / rs) := by
    have h1 : rs * EX * EY
        ≤ rs * ((1 + D / rs) * (cN ^ 2 * D)) * ((1 + W / rs) * (cN ^ 2 * W)) := by
      have hpos1 : (0:ℝ) ≤ 1 + D / rs := by positivity
      gcongr
    have h2 : rs * ((1 + D / rs) * (cN ^ 2 * D)) * ((1 + W / rs) * (cN ^ 2 * W))
        = (Q * cN ^ 2) ^ 2 * (rs / Q + 1 / D + 1 / W + 1 / rs) := by
      subst hQ
      field_simp
      ring
    linarith
  calc S ≤ Real.sqrt rs * Real.sqrt EX * Real.sqrt EY := hS
    _ = Real.sqrt (rs * EX * EY) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hrs.le]
    _ ≤ Real.sqrt ((Q * cN ^ 2) ^ 2 * (rs / Q + 1 / D + 1 / W + 1 / rs)) :=
        Real.sqrt_le_sqrt key
    _ = Q * cN ^ 2 * Real.sqrt (rs / Q + 1 / D + 1 / W + 1 / rs) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hfac]

end Universal.D0WP
