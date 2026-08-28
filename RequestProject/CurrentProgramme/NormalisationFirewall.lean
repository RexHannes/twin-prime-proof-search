import Mathlib

/-!
# Phase A1 · normalisation firewall for the five-defect `δᵢ`

## Source note

A search of the repository found **no** pre-existing `δᵢ` / five-defect object
(no `Motohashi`, `PURE5`, `RANKONE` module exists).  The physical object is
therefore *not* present as a repository definition.  What is present, and is
literal rather than reconstructed from prose, is Mathlib's von Mangoldt
function `Λ`; the defect below is built from it:

  `defect W Y n = (Λ n - 1) * W (n / Y) / Real.log n`.

This is the object named in the continuation prompt.  It is an honest,
kernel-level definition; anything downstream of it that needs the *physical*
five-defect must still supply the source dictionary (see
`AnalyticInterfaces.lean`).

## The repaired statement

The prior claim `‖δᵢ‖_∞ ≪ (log X)⁻¹` is **FALSE on primes**.  For `p` prime,

  `defect W Y p = (1 - 1 / log p) * W (p / Y)`,

which is of size `O(1)`, not `O(1/log X)`.

* `defect_prime` — the exact prime specialisation identity;
* `defect_prime_ge_half` — quantitative failure at a single prime;
* `prime_defect_refutes_pointwise_log_bound` — the **counterguard**: the
  implication "prime-supported defect ⟹ pointwise `(log X)⁻¹`" is refuted.

No asymptotic `L¹`/`L²` estimate is formalised here; those remain human-level
`EXTERNALLY_AUDITED` metadata, exactly as instructed.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Normalisation

open ArithmeticFunction

/-- The normalised defect `δ(n) = (Λ n - 1) · W(n/Y) / log n`. -/
noncomputable def defect (W : ℝ → ℝ) (Y : ℝ) (n : ℕ) : ℝ :=
  (Λ n - 1) * W ((n : ℝ) / Y) / Real.log n

/-- **A1, exact prime specialisation.**  For `p` prime,
`defect W Y p = (1 - 1 / log p) * W (p / Y)`. -/
theorem defect_prime (W : ℝ → ℝ) (Y : ℝ) {p : ℕ} (hp : p.Prime) :
    defect W Y p = (1 - 1 / Real.log p) * W ((p : ℝ) / Y) := by
  have h1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hlog : Real.log p ≠ 0 := ne_of_gt (Real.log_pos h1)
  simp only [defect, ArithmeticFunction.vonMangoldt_apply_prime hp]
  field_simp

/-- `log 11 > 2`; auxiliary numeric fact used by the counterguard. -/
theorem two_lt_log_eleven : 2 < Real.log 11 := by
  have hexp : Real.exp 2 < 11 := by
    have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
    have h0 : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [h1, h0]
  have h11 : Real.exp (Real.log 11) = 11 := Real.exp_log (by norm_num)
  have : Real.exp 2 < Real.exp (Real.log 11) := by rw [h11]; exact hexp
  exact Real.exp_lt_exp.mp this

/-- **A1, quantitative failure.**  At the prime `11`, with window value `1`,
the defect exceeds `1/2` — an `O(1)` quantity, not `O(1/log X)`. -/
theorem defect_prime_ge_half (W : ℝ → ℝ) (Y : ℝ) (hW : W (((11 : ℕ) : ℝ) / Y) = 1) :
    (1 : ℝ) / 2 < defect W Y 11 := by
  rw [defect_prime W Y (by norm_num), hW, mul_one]
  have h : (2 : ℝ) < Real.log ((11 : ℕ) : ℝ) := by
    have := two_lt_log_eleven
    norm_num at this ⊢
    exact this
  have hpos : (0 : ℝ) < Real.log ((11 : ℕ) : ℝ) := by linarith
  have hinv : 1 / Real.log ((11 : ℕ) : ℝ) < 1 / 2 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]
    linarith
  linarith

/-- **A1 COUNTERGUARD.**  The implication

  "the defect is supported on prime powers ⟹ it is pointwise `≪ (log X)⁻¹`"

is FALSE.  Formally: there is no uniform statement bounding `|defect|` at
primes by `1 / log X` whenever `log X > 2`.  Witness: `X = e³`, `p = 11`.

Consequently no downstream module may use a pointwise `(log X)⁻¹` bound for the
five-defect. -/
theorem prime_defect_refutes_pointwise_log_bound :
    ¬ (∀ (W : ℝ → ℝ) (Y X : ℝ), 2 < Real.log X →
        ∀ p : ℕ, p.Prime → W ((p : ℝ) / Y) = 1 →
          |defect W Y p| ≤ 1 / Real.log X) := by
  intro hbad
  have hX : Real.log (Real.exp 3) = 3 := Real.log_exp 3
  have hlogX : (2 : ℝ) < Real.log (Real.exp 3) := by rw [hX]; norm_num
  have h := hbad (fun _ => 1) 1 (Real.exp 3) hlogX 11 (by norm_num) rfl
  rw [hX] at h
  have hhalf : (1 : ℝ) / 2 < defect (fun _ => 1) 1 11 :=
    defect_prime_ge_half _ _ rfl
  have hle : defect (fun _ => 1) 1 11 ≤ 1 / 3 := le_trans (le_abs_self _) h
  linarith

/-- **A1 firewall, positive form.**  The *only* thing the prime support gives is
the exact identity: the defect at a prime is nonnegative once `log p ≥ 1` and
the window is nonnegative. -/
theorem defect_prime_nonneg {W : ℝ → ℝ} {Y : ℝ} {p : ℕ} (hp : p.Prime)
    (hw : 0 ≤ W ((p : ℝ) / Y)) (hlog : 1 ≤ Real.log p) :
    0 ≤ defect W Y p := by
  rw [defect_prime W Y hp]
  have h1 : (0 : ℝ) < Real.log p := by linarith
  have h2 : 1 / Real.log p ≤ 1 := by rw [div_le_one h1]; exact hlog
  nlinarith

end Normalisation
end CurrentProgramme
end TwinPrimeProject
