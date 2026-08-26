/-
# Gate 1B v8.2 — CRT / additive reciprocity shell (exact arithmetic)

* `crt_inverse_sum_eq_one_mod_product` — if `a` inverts `q` mod `M` and `b`
  inverts `M` mod `q`, and `gcd(M,q) = 1`, then `M*q ∣ q*a + M*b − 1`.
* `crt_inverse_sum_witness` — the same statement with the explicit witness `z`.
* `additive_reciprocity_rational_identity` — the rational form
  `h*a/M + h*b/q = h/(M*q) + h*z`.
* `physicalShell_inverse_mod` — `M*x − q*ℓ = −2` forces `M*x = −2` in `ZMod q`,
  and `x = −2 * M⁻¹` when `M` is a unit there.
* `reciprocity_archimedean_tax_le_invX` — the flat size certificate
  `|h|/(M q) ≤ 1/X` for `X = R q`, `|h| ≤ M/R`.

**FIREWALL.**  No complex exponential theorem is asserted; the identity above is
the algebraic core of `e_M(ha) e_q(hb) = e(h/(Mq))`, not that statement itself.
-/
import Mathlib

namespace Gate1B.SafeExtensions

/-- **CRT inverse sum.**  With `q*a ≡ 1 (mod M)` and `M*b ≡ 1 (mod q)` and
`M, q` coprime, the product `M*q` divides `q*a + M*b − 1`. -/
theorem crt_inverse_sum_eq_one_mod_product {M q a b : ℤ} (hcop : IsCoprime M q)
    (ha : M ∣ q * a - 1) (hb : q ∣ M * b - 1) :
    M * q ∣ q * a + M * b - 1 := by
  have hM : M ∣ q * a + M * b - 1 := by
    obtain ⟨k, hk⟩ := ha
    exact ⟨k + b, by linarith [hk]⟩
  have hq : q ∣ q * a + M * b - 1 := by
    obtain ⟨k, hk⟩ := hb
    exact ⟨a + k, by linarith [hk]⟩
  exact hcop.mul_dvd hM hq

/-- The same statement in witness form: `q*a + M*b = 1 + z*M*q`. -/
theorem crt_inverse_sum_witness {M q a b : ℤ} (hcop : IsCoprime M q)
    (ha : M ∣ q * a - 1) (hb : q ∣ M * b - 1) :
    ∃ z : ℤ, q * a + M * b = 1 + z * (M * q) := by
  obtain ⟨z, hz⟩ := crt_inverse_sum_eq_one_mod_product hcop ha hb
  exact ⟨z, by linarith [hz]⟩

/-- **Additive reciprocity, rational form.**  From the CRT witness identity one
gets `h*a/M + h*b/q = h/(M*q) + h*z` for every integer `h`. -/
theorem additive_reciprocity_rational_identity {M q a b z : ℤ} (hM : (M : ℚ) ≠ 0)
    (hq : (q : ℚ) ≠ 0) (h : ℤ) (hz : q * a + M * b = 1 + z * (M * q)) :
    (h : ℚ) * a / M + (h : ℚ) * b / q = (h : ℚ) / (M * q) + h * z := by
  have hz' : (q : ℚ) * a + (M : ℚ) * b = 1 + (z : ℚ) * ((M : ℚ) * q) := by
    exact_mod_cast congrArg (fun n : ℤ => (n : ℚ)) hz
  field_simp
  linear_combination (h : ℚ) * hz'

/-- **Physical shell congruence.**  `M*x − q*ℓ = −2` gives `M*x = −2` in
`ZMod q`. -/
theorem physicalShell_mod (q : ℕ) {M x ell : ℤ} (h : M * x - (q : ℤ) * ell = -2) :
    (M : ZMod q) * (x : ZMod q) = -2 := by
  have := congrArg (fun n : ℤ => (n : ZMod q)) h
  push_cast at this
  simpa using this

/-- **Physical shell inverse form.**  If moreover `M` is a unit mod `q`, then
`x = −2 * M⁻¹` in `ZMod q`. -/
theorem physicalShell_inverse_mod (q : ℕ) {M x ell : ℤ} (h : M * x - (q : ℤ) * ell = -2)
    (hu : IsUnit (M : ZMod q)) :
    (x : ZMod q) = -2 * (M : ZMod q)⁻¹ := by
  have hmul : (M : ZMod q) * (x : ZMod q) = -2 := physicalShell_mod q h
  have hinv : (M : ZMod q) * (M : ZMod q)⁻¹ = 1 := ZMod.mul_inv_of_unit _ hu
  calc (x : ZMod q) = ((M : ZMod q) * (M : ZMod q)⁻¹) * (x : ZMod q) := by rw [hinv, one_mul]
    _ = ((M : ZMod q) * (x : ZMod q)) * (M : ZMod q)⁻¹ := by ring
    _ = -2 * (M : ZMod q)⁻¹ := by rw [hmul]

/-- **Archimedean reciprocity tax.**  With `X = R*q` and `|h| ≤ M/R`, the
reciprocity correction is flat: `|h|/(M*q) ≤ 1/X`. -/
theorem reciprocity_archimedean_tax_le_invX {M R q X h : ℝ} (hM : 0 < M) (hR : 0 < R)
    (hq : 0 < q) (hX : X = R * q) (hh : |h| ≤ M / R) :
    |h| / (M * q) ≤ 1 / X := by
  have h1 : |h| * R ≤ M := (le_div_iff₀ hR).mp hh
  have hMq : 0 < M * q := mul_pos hM hq
  rw [hX, div_le_div_iff₀ hMq (by positivity)]
  nlinarith [abs_nonneg h, hq.le]

end Gate1B.SafeExtensions
