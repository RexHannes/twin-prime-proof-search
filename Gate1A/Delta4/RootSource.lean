/-
# Gate-1A Δv4 §3 / §4 — authoritative root source: `α` range and root collapse

The canonical physical root data of the addendum is

```
m' = m + k r,          m w₀ ≡ -2 (mod r),   0 ≤ w₀ < r,
r α = m w₀ + 2,        r β = m' w₀ + 2.
```

Two things are proved here, both exactly and from these definitions only
(no guessed range is imported):

* **§3 (`alpha_range`)** `0 ≤ α < m + 2/r`, together with the literal
  Archimedean consequence `H |α| / (p q m) ≤ 3 H / L²` on the source support
  `p, q ≥ L`.
* **§4 (`root_phase_m_component_cancels`)** the exact modular collapse
  `m' α − m β = 2 k`: the root parameter `w₀` cancels identically, so the
  `m`-local component of the source phase is *exactly* `e(2k · –)` and no
  Archimedean approximation is involved.

`α` is an honest integer: divisibility `r ∣ m w₀ + 2` is part of the data
(it is the congruence `m w₀ ≡ -2 (mod r)`), and it is proved, not assumed.
-/
import Mathlib

namespace Gate1A

namespace Delta4

/-! ## §3 The root parameter `α` -/

/-- The canonical root data of §3. -/
structure RootData where
  /-- the moving outer prime scale parameter `r ≥ 1`. -/
  r : ℤ
  /-- the source modulus `m ≥ 1`. -/
  m : ℤ
  /-- the canonical root `w₀`, normalised to `0 ≤ w₀ < r`. -/
  w0 : ℤ
  hr : 0 < r
  hm : 0 < m
  hw0 : 0 ≤ w0
  hw0' : w0 < r
  /-- the defining congruence `m w₀ ≡ -2 (mod r)`. -/
  hcong : (r : ℤ) ∣ m * w0 + 2

/-- `α` is an integer: it is `(m w₀ + 2)/r`, and the congruence makes the
division exact. -/
theorem alpha_is_integer (d : RootData) : ∃ α : ℤ, d.r * α = d.m * d.w0 + 2 := by
  obtain ⟨c, hc⟩ := d.hcong
  exact ⟨c, hc.symm⟩

/-- **§3 (`alpha_range`).**  From the definitions alone, `0 ≤ α` and
`α < m + 2/r`; equivalently `r α < r m + 2`. -/
theorem alpha_range (d : RootData) {α : ℤ} (hα : d.r * α = d.m * d.w0 + 2) :
    0 ≤ α ∧ (α : ℚ) < d.m + 2 / d.r := by
  have hr : (0 : ℤ) < d.r := d.hr
  have hmw : 0 ≤ d.m * d.w0 := mul_nonneg d.hm.le d.hw0
  constructor
  · by_contra hneg
    push_neg at hneg
    have : d.r * α ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hr.le (le_of_lt hneg)
    omega
  · -- `r α = m w₀ + 2 ≤ m (r-1) + 2 < r m + 2`
    have hstep : d.r * α < d.r * d.m + 2 := by
      have h1 : d.m * d.w0 ≤ d.m * (d.r - 1) :=
        mul_le_mul_of_nonneg_left (by linarith [d.hw0']) d.hm.le
      have h2 : d.m * (d.r - 1) < d.r * d.m := by nlinarith [d.hm]
      omega
    have hrQ : (0 : ℚ) < (d.r : ℚ) := by exact_mod_cast hr
    have hQ : ((d.r * α : ℤ) : ℚ) < ((d.r * d.m + 2 : ℤ) : ℚ) := by exact_mod_cast hstep
    push_cast at hQ
    rw [← sub_lt_iff_lt_add', lt_div_iff₀ hrQ]
    nlinarith [hQ]

/-- **§3 Archimedean consequence.**  On the source support `p, q ≥ L > 0`
with `m ≥ 1`, `r ≥ 1` and `0 ≤ α < m + 2/r`, the literal Archimedean phase
coefficient obeys

`H α / (p q m) ≤ 3 · H / L²`.

(The factor `3` replaces the addendum's `X^{o(1)}`: it is an explicit
absolute constant.) -/
theorem archimedean_alpha_bound {H L p q mR rR α : ℝ} (hH : 0 ≤ H) (hL : 0 < L)
    (hp : L ≤ p) (hq : L ≤ q) (hm : 1 ≤ mR) (hr : 1 ≤ rR)
    (hα : α < mR + 2 / rR) :
    H * α / (p * q * mR) ≤ 3 * (H / L ^ 2) := by
  have hp0 : 0 < p := lt_of_lt_of_le hL hp
  have hq0 : 0 < q := lt_of_lt_of_le hL hq
  have hm0 : 0 < mR := lt_of_lt_of_le zero_lt_one hm
  have hr0 : 0 < rR := lt_of_lt_of_le zero_lt_one hr
  have hinv : 2 / rR ≤ 2 := by
    rw [div_le_iff₀ hr0]; nlinarith
  have hα' : α ≤ 3 * mR := by nlinarith
  have hnum : H * α ≤ H * (3 * mR) := mul_le_mul_of_nonneg_left hα' hH
  have hden : L ^ 2 * mR ≤ p * q * mR := by
    have : L ^ 2 ≤ p * q := by nlinarith
    exact mul_le_mul_of_nonneg_right this hm0.le
  have hden0 : 0 < L ^ 2 * mR := by positivity
  calc H * α / (p * q * mR) ≤ (H * (3 * mR)) / (L ^ 2 * mR) := by
        apply div_le_div₀ (by positivity) hnum hden0 hden
    _ = 3 * (H / L ^ 2) := by field_simp

/-! ## §4 Root collapse: the `m`-local component cancels exactly -/

/-- **§4 (`root_phase_m_component_cancels`).**  With `m' = m + k r`,
`r α = m w₀ + 2` and `r β = m' w₀ + 2`, the root parameter `w₀` cancels
*identically*:

`m' α − m β = 2 k`.

This is an exact integer identity, not an Archimedean approximation. -/
theorem root_phase_m_component_cancels {r m k w0 α β : ℤ} (hr : r ≠ 0)
    (hα : r * α = m * w0 + 2) (hβ : r * β = (m + k * r) * w0 + 2) :
    (m + k * r) * α - m * β = 2 * k := by
  have key : r * ((m + k * r) * α - m * β) = r * (2 * k) := by
    have h1 : r * ((m + k * r) * α - m * β)
        = (m + k * r) * (r * α) - m * (r * β) := by ring
    rw [h1, hα, hβ]; ring
  exact mul_left_cancel₀ hr key

/-- The phase form of §4: for any modulus, the `m`-local phase of the
source depends only on `2k`, not on the root `w₀`. -/
theorem root_phase_m_component_cancels_zmod {r m k w0 α β : ℤ} (hr : r ≠ 0)
    (hα : r * α = m * w0 + 2) (hβ : r * β = (m + k * r) * w0 + 2) (n : ℕ) :
    ((((m + k * r) * α - m * β : ℤ)) : ZMod n) = ((2 * k : ℤ) : ZMod n) := by
  rw [root_phase_m_component_cancels hr hα hβ]

/-- The same statement at the level of the additive character `e(x) = exp(2πix)`:
the `m`-component of the source phase equals the pure `2k` phase, exactly. -/
theorem root_phase_m_component_cancels_exp {r m k w0 α β : ℤ} (hr : r ≠ 0)
    (hα : r * α = m * w0 + 2) (hβ : r * β = (m + k * r) * w0 + 2) (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * t * (((m + k * r) * α - m * β : ℤ) : ℂ))
      = Complex.exp (2 * Real.pi * Complex.I * t * ((2 * k : ℤ) : ℂ)) := by
  rw [root_phase_m_component_cancels hr hα hβ]

end Delta4

end Gate1A
