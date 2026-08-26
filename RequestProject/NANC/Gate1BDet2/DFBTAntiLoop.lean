import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 10: the DFBT on-shell anti-loop

This module banks the **exact integer algebra** behind the statement labelled
`DFBT_ON_SHELL_ANTI_LOOP_PROVED`.  Everything here is an identity or a
deterministic congruence-lifting step over `ℤ`; there is no positivity
hypothesis, no asymptotics, and no analytic content whatsoever.

The objects are:

* the **Gram invariant** `Δ(x₁,x₂,q₁,q₂) = x₁ q₂ − x₂ q₁`;
* the **physical shell identities** `xᵢ = qᵢ ℓᵢ`;
* a **coherence residue** `r`, given only through a congruence
  `Δ ≡ r q₁ q₂ (mod c)`.

The banked chain is

  on-shell Gram identity  →  congruence lifting (cancel the coprime factor
  `q₁q₂`)  →  integer rigidity (`|r − s| < c` upgrades a congruence to an
  equality)  →  `r = ℓ₁ − ℓ₂`.

**Deliberately not formalized here.**  The claim that a particular smooth
support automatically supplies the size hypothesis `|r − (ℓ₁ − ℓ₂)| < c` is an
analytic statement about the weight; it belongs to the exponent-ledger /
interface layer and is *not* asserted in this module.  Here that hypothesis is
carried explicitly.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. The Gram invariant -/

/-- The basic Gram (determinant) invariant `Δ = x₁ q₂ − x₂ q₁`. -/
def gramDet (x₁ x₂ q₁ q₂ : ℤ) : ℤ := x₁ * q₂ - x₂ * q₁

@[simp] theorem gramDet_def (x₁ x₂ q₁ q₂ : ℤ) :
    gramDet x₁ x₂ q₁ q₂ = x₁ * q₂ - x₂ * q₁ := rfl

/-- The Gram invariant is antisymmetric under swapping the two rows. -/
theorem gramDet_swap (x₁ x₂ q₁ q₂ : ℤ) :
    gramDet x₂ x₁ q₂ q₁ = -gramDet x₁ x₂ q₁ q₂ := by
  unfold gramDet; ring

/-! ## 2. The on-shell identity -/

/-- **DFBT on-shell Gram identity.**  If both physical shell identities
`x₁ = q₁ ℓ₁` and `x₂ = q₂ ℓ₂` hold, then the Gram invariant factors completely:

  `Δ = q₁ q₂ (ℓ₁ − ℓ₂)`.

No positivity, size or asymptotic hypothesis is used. -/
theorem det2_gram_on_shell {x₁ x₂ q₁ q₂ l₁ l₂ : ℤ}
    (h₁ : x₁ = q₁ * l₁) (h₂ : x₂ = q₂ * l₂) :
    gramDet x₁ x₂ q₁ q₂ = q₁ * q₂ * (l₁ - l₂) := by
  subst h₁; subst h₂; unfold gramDet; ring

/-- **On-shell anti-loop, diagonal case.**  On shell with equal complementary
shifts the Gram invariant vanishes identically. -/
theorem det2_gram_on_shell_eq_zero {x₁ x₂ q₁ q₂ l : ℤ}
    (h₁ : x₁ = q₁ * l) (h₂ : x₂ = q₂ * l) :
    gramDet x₁ x₂ q₁ q₂ = 0 := by
  rw [det2_gram_on_shell h₁ h₂]; ring

/-! ## 3. Generic congruence lifting -/

/-- **Cancellation of a coprime factor in a congruence.**  If `a` is invertible
modulo `c` (i.e. `IsCoprime a c`) then `a b ≡ a d (mod c)` gives `b ≡ d`. -/
theorem modEq_cancel_left_of_isCoprime {a b d c : ℤ} (h : IsCoprime a c)
    (h₂ : a * b ≡ a * d [ZMOD c]) : b ≡ d [ZMOD c] := by
  have h₃ : c ∣ a * (b - d) := by
    have := Int.ModEq.dvd h₂.symm
    simpa [mul_sub] using this
  exact Int.ModEq.symm (Int.modEq_iff_dvd.mpr (by simpa using h.symm.dvd_of_dvd_mul_left h₃))

/-- **DFBT congruence lifting.**  Assume the physical shell identities, that
`q₁ q₂` is invertible modulo `c`, and that the coherence residue `r` satisfies
`Δ ≡ r q₁ q₂ (mod c)`.  Then

  `r ≡ ℓ₁ − ℓ₂  (mod c)`. -/
theorem dfbt_residue_congr_on_shell {x₁ x₂ q₁ q₂ l₁ l₂ r c : ℤ}
    (h₁ : x₁ = q₁ * l₁) (h₂ : x₂ = q₂ * l₂)
    (hcop : IsCoprime (q₁ * q₂) c)
    (hcong : gramDet x₁ x₂ q₁ q₂ ≡ r * (q₁ * q₂) [ZMOD c]) :
    r ≡ l₁ - l₂ [ZMOD c] := by
  have hΔ : gramDet x₁ x₂ q₁ q₂ = (q₁ * q₂) * (l₁ - l₂) := det2_gram_on_shell h₁ h₂
  have h : (q₁ * q₂) * r ≡ (q₁ * q₂) * (l₁ - l₂) [ZMOD c] := by
    have : (q₁ * q₂) * (l₁ - l₂) ≡ (q₁ * q₂) * r [ZMOD c] := by
      rw [← hΔ]
      simpa [mul_comm] using hcong
    exact this.symm
  exact modEq_cancel_left_of_isCoprime hcop h

/-! ## 4. Integer rigidity -/

/-- **Elementary integer upgrade.**  A congruence modulo a positive `c` between
two integers whose difference is smaller than `c` in absolute value is an
equality. -/
theorem eq_of_modEq_of_abs_sub_lt {r s c : ℤ} (h : r ≡ s [ZMOD c]) (hc : 0 < c)
    (hlt : |r - s| < c) : r = s := by
  obtain ⟨k, hk⟩ : c ∣ r - s := Int.modEq_iff_dvd.mp h.symm
  rcases eq_or_ne k 0 with rfl | hk0
  · omega
  · exfalso
    have h1 : 1 ≤ |k| := Int.one_le_abs hk0
    have h2 : c ≤ |r - s| := by
      rw [hk, abs_mul, abs_of_pos hc]
      nlinarith
    omega

/-! ## 5. The packaged on-shell anti-loop -/

/-- **`DFBT_ON_SHELL_ANTI_LOOP`, packaged.**  On the physical shell, with
`q₁ q₂` invertible modulo `c > 0`, a coherence residue `r` obeying
`Δ ≡ r q₁ q₂ (mod c)` and the size restriction
`|r − (ℓ₁ − ℓ₂)| < c` is *equal* to the complementary shift difference:

  `r = ℓ₁ − ℓ₂`.

The size restriction is an explicit hypothesis: no smooth-support argument is
formalized here. -/
theorem dfbt_coherence_on_shell_eq_complementary_shift
    {x₁ x₂ q₁ q₂ l₁ l₂ r c : ℤ}
    (h₁ : x₁ = q₁ * l₁) (h₂ : x₂ = q₂ * l₂)
    (hcop : IsCoprime (q₁ * q₂) c) (hc : 0 < c)
    (hcong : gramDet x₁ x₂ q₁ q₂ ≡ r * (q₁ * q₂) [ZMOD c])
    (hsize : |r - (l₁ - l₂)| < c) :
    r = l₁ - l₂ :=
  eq_of_modEq_of_abs_sub_lt (dfbt_residue_congr_on_shell h₁ h₂ hcop hcong) hc hsize

/-- **Anti-loop corollary.**  In the same situation, if in addition the two
complementary shifts agree (`ℓ₁ = ℓ₂`), the coherence residue vanishes: the loop
closes. -/
theorem dfbt_coherence_on_shell_eq_zero
    {x₁ x₂ q₁ q₂ l r c : ℤ}
    (h₁ : x₁ = q₁ * l) (h₂ : x₂ = q₂ * l)
    (hcop : IsCoprime (q₁ * q₂) c) (hc : 0 < c)
    (hcong : gramDet x₁ x₂ q₁ q₂ ≡ r * (q₁ * q₂) [ZMOD c])
    (hsize : |r - 0| < c) :
    r = 0 := by
  have := dfbt_coherence_on_shell_eq_complementary_shift h₁ h₂ hcop hc hcong
    (by simpa using hsize)
  simpa using this

/-! ## 6. Guard -/

/-- **Guard.**  Without the size hypothesis the conclusion genuinely fails: with
`c = 3`, `q₁ = q₂ = 1`, `ℓ₁ = ℓ₂ = 0` and `r = 3` all congruence hypotheses hold
while `r ≠ ℓ₁ − ℓ₂`.  So `dfbt_coherence_on_shell_eq_complementary_shift` is not
a congruence statement in disguise. -/
theorem dfbt_size_hypothesis_is_load_bearing :
    ∃ x₁ x₂ q₁ q₂ l₁ l₂ r c : ℤ,
      x₁ = q₁ * l₁ ∧ x₂ = q₂ * l₂ ∧ IsCoprime (q₁ * q₂) c ∧ 0 < c ∧
      gramDet x₁ x₂ q₁ q₂ ≡ r * (q₁ * q₂) [ZMOD c] ∧ r ≠ l₁ - l₂ := by
  refine ⟨0, 0, 1, 1, 0, 0, 3, 3, by ring, by ring, isCoprime_one_left, by norm_num, ?_, by
    norm_num⟩
  decide

end Gate1BDet2
end TwinPrimeProject
