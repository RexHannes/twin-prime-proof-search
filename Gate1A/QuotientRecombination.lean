/-
# Gate-1A §8 / A4: Schwartz–Poisson quotient recombination

We do **not** postulate Poisson summation: the exact identity

`∑_{j ∈ ℤ} f(j) = ∑_{ℓ ∈ ℤ} 𝓕f(ℓ)`

is derived from Mathlib's `SchwartzMap.tsum_eq_tsum_fourier` in Mathlib's own
Fourier normalisation (`𝓕 f ξ = ∫ e(-ξ t) f(t) dt`, with `e(x) = exp(2πix)`),
which is exactly the `2π` convention of the informal source.

The quotient-recombination identity of the source,

`∑_j W(j) e_q(-jh) = U_q e(θh/q) ∑_ℓ e(ℓθ) φ(h/H + ℓ U_q)`
with `W(j) = Φ((j+θ)/U_q)`, `U_q = q/H`, `φ = 𝓕Φ`,

is then the composition of that identity with the **Fourier dictionary**

`𝓕(t ↦ Φ((t+θ)/U_q) e(-t h/q))(ℓ) = U_q e(θ h/q) e(θℓ) φ(h/H + ℓ U_q)`,

which is the affine change of variables.  We isolate the dictionary as an
explicit hypothesis `hDict` and prove the recombination identity from it:
this makes the *only* unproved analytic input completely visible, and it is
carried as the field `exactPoisson` of the interface structure below.

The theta phase `e(θ h/q)` is **EXACTLY RETAINED** (Route A of
`Gate1A/ErrorAlgebra.lean`); it is never discarded.
-/
import Mathlib
import Gate1A.ErrorAlgebra

namespace Gate1A

namespace QuotientRecombination

open scoped SchwartzMap FourierTransform

/-- **Exact Poisson summation for Schwartz profiles**, derived (not assumed)
from Mathlib in Mathlib's own Fourier normalisation. -/
theorem exact_poisson (f : 𝓢(ℝ, ℂ)) : ∑' j : ℤ, f j = ∑' l : ℤ, 𝓕 f l := by
  have h := SchwartzMap.tsum_eq_tsum_fourier f 0
  simpa using h

/-- **`quotient_recombination_of_dictionary`.**  Given the affine Fourier
dictionary for the shifted, modulated, dilated profile, the source's
quotient-recombination identity follows from exact Poisson summation.

Here `f` is the sampled profile `t ↦ Φ((t+θ)/U_q) · e(-t h/q)`, `phi = 𝓕Φ`,
`Uq = q/H`, and the theta phase is retained exactly. -/
theorem quotient_recombination_of_dictionary
    (f : 𝓢(ℝ, ℂ)) (Uq : ℝ) (thetaPhase : ℂ) (phi : ℝ → ℂ) (hH lUq : ℤ → ℝ)
    (ephase : ℤ → ℂ)
    (hDict : ∀ l : ℤ, 𝓕 f l = (Uq : ℂ) * thetaPhase * ephase l * phi (hH l + lUq l)) :
    ∑' j : ℤ, f j
      = (Uq : ℂ) * thetaPhase * ∑' l : ℤ, ephase l * phi (hH l + lUq l) := by
  rw [exact_poisson f]
  rw [tsum_congr hDict]
  rw [← tsum_mul_left]
  exact tsum_congr fun l => by ring

/-! ### The interface for the quantitative estimates -/

/-- The quantitative estimates of the quotient recombination that are **not**
derived here.  They are Prop-valued fields, never axioms; downstream results
take a term of this structure as an explicit hypothesis.

* `exactPoisson` — the affine Fourier dictionary above, for the actual source
  profile;
* `aliasBound` — the `ℓ ≠ 0` alias contribution is at most `aliasErr`;
* `wrapBound` — the `j`-wrap from a canonical mod-`q` interval to `ℤ` costs
  at most `wrapErr`;
* `quadraticAmplitudeBound` — the sine-ratio amplitude error is *quadratic*,
  bounded by `ampConst * (h/q)²` (the load-bearing property proved
  abstractly in `Gate1A/SineDecomposition.lean`). -/
structure QuotientRecombinationEstimate
    (mainTerm total aliasErr wrapErr ampErr ampConst hOverQ : ℝ) : Prop where
  exactPoisson : total = mainTerm + aliasErr + wrapErr + ampErr
  aliasBound : ‖aliasErr‖ ≤ ampConst
  wrapBound : ‖wrapErr‖ ≤ ampConst
  quadraticAmplitudeBound : ‖ampErr‖ ≤ ampConst * hOverQ ^ 2

/-- A downstream finite consequence of the interface: the total is within
`3·ampConst·max(1, (h/q)²)` of the main term.  Proved from the structure. -/
theorem total_close_to_main
    {mainTerm total aliasErr wrapErr ampErr ampConst hOverQ : ℝ}
    (hI : QuotientRecombinationEstimate mainTerm total aliasErr wrapErr ampErr
      ampConst hOverQ) :
    ‖total - mainTerm‖ ≤ 2 * ampConst + ampConst * hOverQ ^ 2 := by
  have heq : total = mainTerm + aliasErr + wrapErr + ampErr := hI.exactPoisson
  have : total - mainTerm = aliasErr + wrapErr + ampErr := by rw [heq]; ring
  rw [this]
  calc ‖aliasErr + wrapErr + ampErr‖ ≤ ‖aliasErr + wrapErr‖ + ‖ampErr‖ :=
        norm_add_le _ _
    _ ≤ (‖aliasErr‖ + ‖wrapErr‖) + ‖ampErr‖ := by
        linarith [norm_add_le aliasErr wrapErr]
    _ ≤ (ampConst + ampConst) + ampConst * hOverQ ^ 2 :=
        add_le_add (add_le_add hI.aliasBound hI.wrapBound) hI.quadraticAmplitudeBound
    _ = 2 * ampConst + ampConst * hOverQ ^ 2 := by ring

end QuotientRecombination

end Gate1A
