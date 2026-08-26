/-
# Gate-1A Δv4 §2 / §8 / §14 / §24 — the frozen scale ledger, extended

This module adds to the frozen ledger of `Gate1A/Exponents.lean` exactly the
exponent bookkeeping demanded by the Δv4 addendum:

* §8  error-root capacity      `U⁻¹ ≤ √(H/M)`,  with `U⁻¹/√(H/M) = √(M/D)`;
* §14 axis truncation margins  `M H / L² = M / D < 1` and `H / L² < 1`;
* §24 root depth               `M R^(-1/2) ≤ H`.

Every statement is an ordinary rational-arithmetic theorem about exponents in
the scale `X`; nothing here pretends `X ^ a` is an integer, and no analytic
input is used.  The immutable dictionary is the one already frozen in
`Gate1A/Exponents.lean`:

```
M = X ^ (1/3)         R = X ^ a          L = X ^ b
H = X ^ (a + 2b - 2/3)   K = X ^ (1/3 - a)   D = X ^ (2/3 - a)
U = L / H  ⇒  U⁻¹ = X ^ (a + b - 2/3)
```
-/
import Mathlib
import Gate1A.Exponents

namespace Gate1A

namespace Delta4

open Gate1A

/-! ## §2 exact identities (restated for the Δv4 dictionary) -/

/-- `D · H = L²`. -/
theorem scale_DH (a b : ℚ) : dExp a + hExp a b = 2 * b := gate1a_DH_eq_Lsq a b

/-- `R · K = M`. -/
theorem scale_RK (a : ℚ) : a + kExp a = mExp := gate1a_RK_eq_M a

/-- `M² · H = R · L²`. -/
theorem scale_MsqH (a b : ℚ) : 2 * mExp + hExp a b = a + 2 * b := gate1a_MsqH_eq_RLsq a b

/-- `M · K = L² / H`. -/
theorem scale_MK (a b : ℚ) : mExp + kExp a = 2 * b - hExp a b := by
  simp only [mExp, kExp, hExp]; ring

/-- `U = L / H` in exponents, i.e. `U⁻¹ = X^(a+b-2/3)`. -/
theorem scale_uInv (a b : ℚ) : uInvExp a b = -(b - hExp a b) := by
  simp only [uInvExp, hExp]; ring

/-! ## §8 error-root capacity

The flat-profile error is at *amplitude* level `ε = U⁻¹`.  It may **not** be
compared with `H/M`; the correct comparison is with `√(H/M)`.  The exact
ratio is `U⁻¹ / √(H/M) = √(M/D)`.
-/

/-- The Δv4 error-root margin: `reqExp/2 − uInvExp = 1/6 − a/2`. -/
def errorRootMargin (a : ℚ) : ℚ := 1 / 6 - a / 2

/-- **Exact §8 identity.** `U⁻¹ / √(H/M) = √(M/D)` in exponents:
`uInvExp − reqExp/2 = (mExp − dExp)/2`. -/
theorem uInv_over_sqrt_saving_eq_sqrt_M_over_D (a b : ℚ) :
    uInvExp a b - reqExp a b / 2 = (mExp - dExp a) / 2 := by
  simp only [uInvExp, reqExp, mExp, dExp]; ring

/-- The margin is exactly minus that ratio. -/
theorem errorRootMargin_eq (a b : ℚ) :
    reqExp a b / 2 - uInvExp a b = errorRootMargin a := by
  simp only [uInvExp, reqExp, errorRootMargin]; ring

/-- On the polytope `a ≤ 7/24` (from `b ≥ 1/3` and `a + b ≤ 5/8`). -/
theorem polytope_a_le (a b : ℚ) (h : Polytope a b) : a ≤ 7 / 24 := by
  obtain ⟨ha, hb, hab⟩ := h; linarith

/-- **§8 error-root capacity.** `U⁻¹ ≤ √(H/M)` on the whole frozen polytope,
with the uniform margin `1/48`. -/
theorem error_root_capacity {a b : ℚ} (h : Polytope a b) :
    uInvExp a b ≤ reqExp a b / 2 - 1 / 48 := by
  have := polytope_a_le a b h
  simp only [uInvExp, reqExp]
  linarith

/-- Vertex margin at `V1 = (5/18, 1/3)`: `1/36`. -/
theorem error_root_margin_V1 : errorRootMargin V1.1 = 1 / 36 := by
  norm_num [errorRootMargin, V1]

/-- Vertex margin at `V2 = (5/18, 25/72)`: `1/36`. -/
theorem error_root_margin_V2 : errorRootMargin V2.1 = 1 / 36 := by
  norm_num [errorRootMargin, V2]

/-- Vertex margin at `V3 = (7/24, 1/3)`: `1/48`. -/
theorem error_root_margin_V3 : errorRootMargin V3.1 = 1 / 48 := by
  norm_num [errorRootMargin, V3]

/-! ## §14 axis truncation margins -/

/-- `M H / L² = M / D` in exponents. -/
theorem MH_over_Lsq_eq_M_over_D (a b : ℚ) :
    mExp + hExp a b - 2 * b = mExp - dExp a := by
  simp only [mExp, hExp, dExp]; ring

/-- **§14A truncation margin.** `M H / L² = M / D < 1` on the polytope, with
uniform margin `1/24` in the exponent. -/
theorem MH_over_Lsq_lt_one {a b : ℚ} (h : Polytope a b) :
    mExp + hExp a b - 2 * b ≤ -(1 / 24) := by
  have := polytope_a_le a b h
  simp only [mExp, hExp]
  linarith

/-- **§14B truncation margin.** `H / L² < 1` on the polytope, with uniform
margin `3/8` in the exponent. -/
theorem H_over_Lsq_lt_one {a b : ℚ} (h : Polytope a b) :
    hExp a b - 2 * b ≤ -(3 / 8) := by
  have := polytope_a_le a b h
  simp only [hExp]
  linarith

/-! ## §24 root depth: `M R^(-1/2) ≤ H` -/

/-- The Δv4 root-depth margin `H / (M R^{-1/2}) = X^((3/2)a + 2b − 1)`. -/
def rootDepthMargin (a b : ℚ) : ℚ := 3 / 2 * a + 2 * b - 1

theorem rootDepthMargin_eq (a b : ℚ) :
    hExp a b - (mExp - a / 2) = rootDepthMargin a b := by
  simp only [hExp, mExp, rootDepthMargin]; ring

/-- **§24 root depth.** `M R^(-1/2) ≤ H` on the frozen polytope, with the
uniform margin `1/12`. -/
theorem root_depth_capacity {a b : ℚ} (h : Polytope a b) :
    mExp - a / 2 ≤ hExp a b - 1 / 12 := by
  obtain ⟨ha, hb, _⟩ := h
  simp only [mExp, hExp]
  linarith

theorem root_depth_margin_V1 : rootDepthMargin V1.1 V1.2 = 1 / 12 := by
  norm_num [rootDepthMargin, V1]

theorem root_depth_margin_V2 : rootDepthMargin V2.1 V2.2 = 1 / 9 := by
  norm_num [rootDepthMargin, V2]

theorem root_depth_margin_V3 : rootDepthMargin V3.1 V3.2 = 5 / 48 := by
  norm_num [rootDepthMargin, V3]

/-- **No hidden second root.** The two root-level comparisons of the Δv4
closure — the error root (§8) and the depth root (§24) — are the *only* two
places a square root is taken, and they are compatible: both margins are
strictly positive on the whole polytope simultaneously. -/
theorem both_root_margins_positive {a b : ℚ} (h : Polytope a b) :
    0 < errorRootMargin a ∧ 0 < rootDepthMargin a b := by
  obtain ⟨ha, hb, hab⟩ := h
  constructor
  · have : a ≤ 7 / 24 := polytope_a_le a b ⟨ha, hb, hab⟩
    simp only [errorRootMargin]; linarith
  · simp only [rootDepthMargin]; linarith

end Delta4

end Gate1A
