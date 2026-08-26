/-
# NANC Gate 1A v9.1 — the root multiplier: finite unit algebra

All statements here are **finite algebra in a commutative ring** (in practice
`ZMod m` or `ZMod pi`).  No asymptotics, no analytic input, no division: every
inverse is supplied as an explicit element together with its defining relation
`x * ix = 1`, so nothing depends on a `ZMod` inversion convention.

The amplifier-line relation is

    ell1 = q2 * (t + a)

and the claimed `m`-local phase multiplier is

    kappa = -theta * delta * inverse(q1) * inverse(q2)^2,

for which we prove the exact rewrite

    -theta*delta * inverse(q1*ell1) * inverse(q2)  =  kappa * inverse(t+a).

Reducing along any ring hom (e.g. `ZMod m → ZMod pi` for a clean factor `pi`)
gives

    kappa  =  u * inverse(q1),        u = -theta*delta*inverse(q2)^2,

and `u` is *literally independent of `q1`*: it is the value of a function whose
argument list does not contain `q1` (`rootMultiplierU_indep_q1`).

**FIREWALL.**  A finite phase rewrite is not an analytic estimate.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V91

variable {R : Type*} [CommRing R]

/-- The `q1`-free part of the root multiplier: `u = -theta*delta*inverse(q2)^2`. -/
def rootMultiplierU (theta delta iq2 : R) : R := -theta * delta * iq2 ^ 2

/-- The root multiplier `kappa = -theta*delta*inverse(q1)*inverse(q2)^2`. -/
def rootMultiplierKappa (theta delta iq1 iq2 : R) : R := -theta * delta * iq1 * iq2 ^ 2

/-- `kappa` factors as `u * inverse(q1)` with `u` free of `q1`. -/
theorem rootMultiplierKappa_eq_u_mul (theta delta iq1 iq2 : R) :
    rootMultiplierKappa theta delta iq1 iq2 = rootMultiplierU theta delta iq2 * iq1 := by
  unfold rootMultiplierKappa rootMultiplierU; ring

/-- **`u` does not depend on `q1`.**  Two amplifier data with the same
`theta, delta, q2` but arbitrary (possibly different) `q1`-inverses have the same
`u`.  (Formally: `rootMultiplierU` has no `q1` argument.) -/
theorem rootMultiplierU_indep_q1 (theta delta iq2 : R) (iq1 iq1' : R) :
    rootMultiplierU theta delta iq2 =
      rootMultiplierU theta delta iq2 ∧
    rootMultiplierKappa theta delta iq1 iq2 * iq1' =
      rootMultiplierKappa theta delta iq1' iq2 * iq1 := by
  refine ⟨rfl, ?_⟩
  unfold rootMultiplierKappa; ring

/-- Inverses are unique in a commutative monoid: helper for the rewrite. -/
theorem inv_unique_of_mul_eq_one {x y z : R} (hy : x * y = 1) (hz : x * z = 1) : y = z := by
  calc y = y * (x * z) := by rw [hz, mul_one]
    _ = (x * y) * z := by ring
    _ = z := by rw [hy, one_mul]

/-- **Root multiplier rewrite.**  With the amplifier-line relation
`ell1 = q2*(t+a)`, explicit inverses `iq1, iq2, ita` for `q1, q2, t+a`, and any
inverse `j` of `q1*ell1`,

    -theta*delta * j * iq2  =  kappa * ita,       kappa = -theta*delta*iq1*iq2².
-/
theorem rootMultiplier_rewrite
    (theta delta q1 q2 t a iq1 iq2 ita ell1 j : R)
    (hq1 : q1 * iq1 = 1) (hq2 : q2 * iq2 = 1) (hta : (t + a) * ita = 1)
    (hell : ell1 = q2 * (t + a)) (hj : (q1 * ell1) * j = 1) :
    -theta * delta * j * iq2 = rootMultiplierKappa theta delta iq1 iq2 * ita := by
  have hjval : (q1 * ell1) * (iq1 * iq2 * ita) = 1 := by
    subst hell
    calc (q1 * (q2 * (t + a))) * (iq1 * iq2 * ita)
        = (q1 * iq1) * ((q2 * iq2) * ((t + a) * ita)) := by ring
      _ = 1 := by rw [hq1, hq2, hta]; ring
  have hjeq : j = iq1 * iq2 * ita := inv_unique_of_mul_eq_one hj hjval
  subst hjeq
  unfold rootMultiplierKappa
  ring

/-- **Reduction to a clean factor.**  Along any ring hom `f` (for instance the
reduction `ZMod m → ZMod pi`),

    f kappa = u * f iq1,     u = -f theta * f delta * (f iq2)^2,

so the `q1`-dependence of the reduced multiplier is exactly the single factor
`f iq1`. -/
theorem rootMultiplier_mod_cleanFactor {S : Type*} [CommRing S] (f : R →+* S)
    (theta delta iq1 iq2 : R) :
    f (rootMultiplierKappa theta delta iq1 iq2)
      = rootMultiplierU (f theta) (f delta) (f iq2) * f iq1 := by
  unfold rootMultiplierKappa rootMultiplierU
  simp [map_mul, map_neg, map_pow]
  ring

/-! ## Hard-delta unit router (finite arithmetic only) -/

/-- **Hard-delta unit router.**  If `pi` is prime and `0 < |delta| < pi`, then
`delta` is a unit modulo `pi`.  This is finite arithmetic: no size budget of the
form `|delta| ≤ L/M < pi` is encoded here. -/
theorem hardDelta_isUnit_mod_cleanPrime {pi : ℕ} (hpi : pi.Prime) {delta : ℤ}
    (hpos : 0 < |delta|) (hlt : |delta| < (pi : ℤ)) :
    IsUnit ((delta : ZMod pi)) := by
  haveI : Fact pi.Prime := ⟨hpi⟩
  have hne : (delta : ZMod pi) ≠ 0 := by
    intro h
    have hdvd : ((pi : ℤ)) ∣ delta := (ZMod.intCast_zmod_eq_zero_iff_dvd delta pi).1 h
    have hdvdabs : ((pi : ℤ)) ∣ |delta| := (dvd_abs _ _).2 hdvd
    have : (pi : ℤ) ≤ |delta| := Int.le_of_dvd hpos hdvdabs
    omega
  exact isUnit_iff_ne_zero.2 hne

/-- The same router with the two remaining unit hypotheses of the root
multiplier made explicit: `q2` and `theta` must also be units mod `pi` for
`kappa` to be a unit multiple of `inverse(q1)`. -/
theorem rootMultiplierU_isUnit_mod_cleanPrime {pi : ℕ} (_hpi : pi.Prime)
    {theta delta iq2 : ZMod pi}
    (htheta : IsUnit theta) (hdelta : IsUnit delta) (hiq2 : IsUnit iq2) :
    IsUnit (rootMultiplierU theta delta iq2) := by
  unfold rootMultiplierU
  exact (((htheta.neg).mul hdelta).mul (hiq2.pow 2))

end TwinPrimeProject.NANC.Gate1A.V91
