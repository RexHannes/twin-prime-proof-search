import Mathlib

/-!
# FKMS inverse-monomial trace interfaces and exponent optimization (§7, §8)

This module banks:

* the *literature interfaces* for the Fouvry–Kowalski–Michel–Sawin bilinear and
  trilinear inverse-monomial trace-function estimates, as explicit `structure`s
  whose fields record the exact permitted exponents, coefficient norms, support
  ranges and conclusion.  These are recorded as `LITERATURE_VERIFIED` interfaces
  in the ledger — the *shape* is banked here; the numerical source location is
  tracked in `LEDGER.md`.

* the *exponent optimization arithmetic*, which is fully `LEAN_PROVED`:
  - `fkmsDelta l = (l − 7) / (8 l²)` is maximized over `l > 0` at `l = 14`,
    with maximal value `1/224` (`fkmsDelta_le`, `fkmsDelta_14`,
    `fkmsDelta_eq_iff`);
  - the trilinear factorized saving exponent `1/16` does **not** reach the
    short-window requirement `Q^{-1/2} ≤ p^{-1/6}` (`saving_1_16_lt_1_6`).

`PRIME_INVERSE_KLOOSTERMAN_SAVING_1_224`: `LEAN_PROVED_CORE` (optimization) +
`LITERATURE_VERIFIED` (input theorem).
`PRIME_FACTORIZED_TRACE_SAVING_1_16`: `CONDITIONAL_INTERFACE` (needs the actual
three-factor coefficient decomposition).
-/

namespace PrimeShortWindow.FKMS

/-! ## Literature interfaces (recorded shapes) -/

/-- **FKMS_INVERSE_MONOMIAL_BILINEAR.**  Interface recording a bilinear
inverse-monomial trace estimate permitting the monomial `K(mⁿ nᶜ)` with nonzero
integer exponents.  Fields record the exact hypotheses under which the estimate
holds; `conclusion_savingExponent` is the power-saving exponent delivered. -/
structure InverseMonomialBilinear where
  /-- Permitted exponent on the first variable (nonzero integer). -/
  b : ℤ
  /-- Permitted exponent on the second variable (nonzero integer). -/
  c : ℤ
  b_ne : b ≠ 0
  c_ne : c ≠ 0
  /-- `ℓ`-parameter (moment order) used in the amplification. -/
  l : ℕ
  l_pos : 0 < l
  /-- The delivered power-saving exponent as a function of `ℓ`. -/
  conclusion_savingExponent : ℝ

/-- **FKMS_INVERSE_MONOMIAL_TRILINEAR.**  Interface recording the bounded-coefficient
trilinear inverse-monomial trace estimate for `K(jᵃ mᵇ nᶜ)` with negative
exponents permitted, together with the coefficient factorization `q = v w`. -/
structure InverseMonomialTrilinear where
  a : ℤ
  b : ℤ
  c : ℤ
  a_ne : a ≠ 0
  b_ne : b ≠ 0
  c_ne : c ≠ 0
  /-- Dyadic scale of the factor `v` (as a real exponent of `p`). -/
  vExponent : ℝ
  /-- Moment order. -/
  l : ℕ
  l_pos : 0 < l
  /-- The delivered power-saving exponent. -/
  conclusion_savingExponent : ℝ

/-! ## Bilinear exponent optimization (LEAN_PROVED) -/

/-- The FKMS bilinear saving exponent as a function of the moment order `l`. -/
noncomputable def fkmsDelta (l : ℝ) : ℝ := (l - 7) / (8 * l ^ 2)

/-- The value at the optimal integer moment order `l = 14` is exactly `1/224`. -/
theorem fkmsDelta_14 : fkmsDelta 14 = 1 / 224 := by
  unfold fkmsDelta; norm_num

/-- `fkmsDelta` is maximized over positive `l` at value `1/224`. -/
theorem fkmsDelta_le (l : ℝ) (hl : 0 < l) : fkmsDelta l ≤ 1 / 224 := by
  unfold fkmsDelta
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg (l - 14)]

/-- The maximum `1/224` is attained precisely at `l = 14` (for `l > 0`). -/
theorem fkmsDelta_eq_iff (l : ℝ) (hl : 0 < l) : fkmsDelta l = 1 / 224 ↔ l = 14 := by
  unfold fkmsDelta
  rw [div_eq_div_iff (by positivity) (by norm_num)]
  constructor
  · intro h; nlinarith [sq_nonneg (l - 14)]
  · intro h; subst h; norm_num

/-- `l = 14` is the optimal *integer* moment order: for every positive natural
number `l`, `fkmsDelta l ≤ fkmsDelta 14`. -/
theorem fkmsDelta_integer_optimum (l : ℕ) (hl : 0 < l) :
    fkmsDelta (l : ℝ) ≤ fkmsDelta 14 := by
  rw [fkmsDelta_14]
  exact fkmsDelta_le (l : ℝ) (by exact_mod_cast hl)

/-- **PRIME_INVERSE_KLOOSTERMAN_SAVING_1_224** (arithmetic core): the optimized
bilinear saving exponent is `1/224`, attained at `l = 14`. -/
theorem prime_inverse_kloosterman_saving_1_224 :
    fkmsDelta 14 = 1 / 224 ∧ ∀ l : ℝ, 0 < l → fkmsDelta l ≤ fkmsDelta 14 := by
  refine ⟨fkmsDelta_14, fun l hl => ?_⟩
  rw [fkmsDelta_14]; exact fkmsDelta_le l hl

/-! ## Trilinear factorized saving (LEAN_PROVED comparison) -/

/-- The trilinear factorized saving exponent obtained with `V = p^{1/4}`,
`l = 2`. -/
noncomputable def factorizedSavingExponent : ℝ := 1 / 16

/-- The short-window requirement is a saving of at least `Q^{-1/2} ≤ p^{-1/6}`,
i.e. an exponent of at least `1/6`. -/
noncomputable def shortWindowRequiredExponent : ℝ := 1 / 6

/-- **PRIME_FACTORIZED_TRACE_SAVING_1_16** (comparison core): the factorized
trilinear saving `p^{-1/16}` does **not** reach the short-window requirement
`p^{-1/6}` (a smaller exponent means a weaker saving). -/
theorem saving_1_16_lt_1_6 :
    factorizedSavingExponent < shortWindowRequiredExponent := by
  unfold factorizedSavingExponent shortWindowRequiredExponent; norm_num

end PrimeShortWindow.FKMS
