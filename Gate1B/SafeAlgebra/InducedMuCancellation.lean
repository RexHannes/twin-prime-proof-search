/-
# Gate 1B v8.4 — `μ(e)` cancellation against the induced Gauss factor

**Status: PROVED_ALGEBRAIC.**

Combining

* the lane-C factorisation `β(ce) = μ(e) ρ(c,e)` (`BetaCEPrimeSplit.lean`), and
* the induced Gauss factor `τ_{ce}(χ) = μ(e) χ*(e) τ_c(χ*)`
  (`InducedGaussFactor.lean`),

and using `μ(e)² = 1` for squarefree `e`, gives the exact identity

  `β(ce) · τ_{ce}(χ) = ρ(c,e) · χ*(e) · τ_c(χ*)`.

FIREWALL.  `μ(e)` is **spent** algebraically here.  It is not a remaining
cancellation resource and must not be counted again later (see
`Gate1B/SafeExtensions/V84ResourceLedger.lean`).
-/
import Mathlib
import Gate1B.SafeAlgebra.BetaCEPrimeSplit
import Gate1B.SafeAlgebra.InducedGaussFactor

namespace Gate1B.SafeAlgebra

open Finset
open scoped ArithmeticFunction.Moebius

/-- `μ(e)² = 1` for squarefree `e`, over ℂ. -/
theorem moebius_sq_complex {e : ℕ} (he : Squarefree e) : ((μ e : ℤ) : ℂ) ^ 2 = 1 := by
  have h : (μ e) ^ 2 = 1 := ArithmeticFunction.moebius_sq_eq_one_of_squarefree he
  exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) h

/-- **`μ(e)` cancellation.**  With `β(ce) = μ(e) ρ` and
`τ_{ce} = μ(e) χ*(e) τ_c`, the product is `ρ χ*(e) τ_c`. -/
theorem beta_mul_inducedGauss_cancel_muE {e : ℕ} (he : Squarefree e)
    (beta rho tauCE tauC chiStarE : ℂ)
    (hbeta : beta = (μ e : ℂ) * rho)
    (hgauss : tauCE = (μ e : ℂ) * chiStarE * tauC) :
    beta * tauCE = rho * chiStarE * tauC := by
  have hsq : ((μ e : ℤ) : ℂ) ^ 2 = 1 := moebius_sq_complex he
  rw [hbeta, hgauss]
  have : (μ e : ℂ) * rho * ((μ e : ℂ) * chiStarE * tauC)
      = ((μ e : ℂ) ^ 2) * (rho * chiStarE * tauC) := by ring
  rw [this, hsq, one_mul]

/-- The same statement with the two inputs instantiated at the concrete
restricted source coefficient of `BetaCEPrimeSplit.lean`. -/
theorem betaSource_mul_inducedGauss_cancel_muE
    (physicalSupport : ℕ → ℕ → ℕ → Prop) (logWeight : ℕ → ℂ)
    {c e : ℕ} (hce : Nat.Coprime c e) (he : Squarefree e)
    (tauCE tauC chiStarE : ℂ)
    (hgauss : tauCE = (μ e : ℂ) * chiStarE * tauC) :
    betaSource physicalSupport logWeight c e * tauCE
      = rhoCE physicalSupport logWeight c e * chiStarE * tauC :=
  beta_mul_inducedGauss_cancel_muE he _ _ _ _ _
    (betaCE_laneC_factor physicalSupport logWeight hce) hgauss

end Gate1B.SafeAlgebra
