import Gate1B.HStarTwoAnchorDifferenceAlgebra

/-!
# Gate 1B · the clean **`H = 0` finite arithmetic router**

Exact natural-number arithmetic.  **No asymptotic scale inequality is
formalised** (in particular nothing of the shape `m_i / ℓ_j ≥ x^{4/9−o(1)}`):
the length separation is exposed as an *explicit finite hypothesis*, and the
router is conditional on it.  Its arithmetic conclusion is kernel-proved.

## Contents

* §1 the cross-divisibility lemma: for coprime `m₁, m₂` with `m₁ℓ₁ = m₂ℓ₂` one
  has `m₁ ∣ ℓ₂` and `m₂ ∣ ℓ₁`;
* §2 the finite impossibility lemma: with positive lengths, a *single* length
  inequality `ℓ₂ < m₁` already contradicts `m₁ ∣ ℓ₂`;
* §3 the **conditional physical router**: the `H = 0` off-diagonal source cell
  with coprime multiplicative parts and short lengths is impossible;
* §4 the specialisation to the physical two-anchor source at `H = 0`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarHZero

open TwinPrimeProject.CurrentProgramme.HStarTwoAnchor

/-! ## 1. Cross-divisibility -/

/-- **Cross-divisibility.**  If `m₁` and `m₂` are coprime and `m₁ℓ₁ = m₂ℓ₂`
then `m₁ ∣ ℓ₂` and `m₂ ∣ ℓ₁`. -/
theorem cross_dvd_of_coprime {m1 m2 ell1 ell2 : ℕ} (hcop : Nat.Coprime m1 m2)
    (heq : m1 * ell1 = m2 * ell2) : m1 ∣ ell2 ∧ m2 ∣ ell1 := by
  constructor
  · exact hcop.dvd_of_dvd_mul_left ⟨ell1, heq.symm⟩
  · exact hcop.symm.dvd_of_dvd_mul_left ⟨ell2, heq⟩

/-! ## 2. The finite impossibility lemma -/

/-- **Finite impossibility (sharp form).**  A positive `ℓ₂` strictly below `m₁`
cannot be divisible by `m₁`; hence the coprime equation `m₁ℓ₁ = m₂ℓ₂` is
impossible under that single length inequality.

Only one of the two length inequalities is needed. -/
theorem hZero_impossible_of_short_length {m1 m2 ell1 ell2 : ℕ}
    (hcop : Nat.Coprime m1 m2) (h2 : 0 < ell2) (hlt : ell2 < m1)
    (heq : m1 * ell1 = m2 * ell2) : False := by
  have hdvd : m1 ∣ ell2 := (cross_dvd_of_coprime hcop heq).1
  exact absurd (Nat.le_of_dvd h2 hdvd) (Nat.not_le.2 hlt)

/-- **Finite impossibility (symmetric form as stated in the source).**  With
both length inequalities `ℓ₂ < m₁` and `ℓ₁ < m₂` and positive lengths, the
`H = 0` equation is impossible.  (By the sharp form, one inequality already
suffices; the second is kept because the physical statement supplies both.) -/
theorem hZero_impossible_of_short_lengths {m1 m2 ell1 ell2 : ℕ}
    (hcop : Nat.Coprime m1 m2) (_h1 : 0 < ell1) (h2 : 0 < ell2)
    (hlt2 : ell2 < m1) (_hlt1 : ell1 < m2)
    (heq : m1 * ell1 = m2 * ell2) : False :=
  hZero_impossible_of_short_length hcop h2 hlt2 heq

/-! ## 3. The conditional physical router -/

/-- The **`H = 0` off-diagonal physical cell**: the two multiplicative parts
`m i = e i · wp i`, coprime, with equal products `m₁ℓ₁ = m₂ℓ₂` (that is,
`H = 0`) and with the length separation supplied as *explicit finite
hypotheses*. -/
structure HZeroOffDiagonalCell where
  e1 : ℕ
  e2 : ℕ
  wp1 : ℕ
  wp2 : ℕ
  ell1 : ℕ
  ell2 : ℕ
  ell1_pos : 0 < ell1
  ell2_pos : 0 < ell2
  coprime : Nat.Coprime (e1 * wp1) (e2 * wp2)
  /-- The `H = 0` equation. -/
  hZero : e1 * wp1 * ell1 = e2 * wp2 * ell2
  /-- **Explicit finite length separation** (the finite surrogate of the
  asymptotic scale inequality, which is *not* formalised). -/
  short1 : ell2 < e1 * wp1
  /-- The companion length separation. -/
  short2 : ell1 < e2 * wp2

/-- **BANKED ROUTER.**  The `H = 0` off-diagonal physical source cell is
impossible: the structure has no inhabitant. -/
theorem hZeroOffDiagonalCell_impossible (C : HZeroOffDiagonalCell) : False :=
  hZero_impossible_of_short_lengths C.coprime C.ell1_pos C.ell2_pos C.short1
    C.short2 C.hZero

theorem not_nonempty_hZeroOffDiagonalCell : ¬ Nonempty HZeroOffDiagonalCell :=
  fun ⟨C⟩ => hZeroOffDiagonalCell_impossible C

/-! ## 4. The two-anchor source at `H = 0` -/

/-- **Physical specialisation.**  A physical two-anchor source whose quotient
difference vanishes (`H = 0`), whose multiplicative parts are coprime and whose
second length is below the first multiplicative part, does not exist. -/
theorem hZero_two_anchor_source_impossible (S : HStarTwoAnchorSource)
    (hcop : Nat.Coprime (S.e1 * S.wp1) (S.e2 * S.wp2))
    (hH : (S.e1 : ℤ) * S.wp1 * S.ell1 - (S.e2 : ℤ) * S.wp2 * S.ell2 = 0)
    (hshort : S.ell2 < S.e1 * S.wp1) : False := by
  have hnat : S.e1 * S.wp1 * S.ell1 = S.e2 * S.wp2 * S.ell2 := by
    have : (S.e1 : ℤ) * S.wp1 * S.ell1 = (S.e2 : ℤ) * S.wp2 * S.ell2 := by linarith
    exact_mod_cast this
  exact hZero_impossible_of_short_length hcop S.ell2_pos hshort hnat

end HStarHZero
end CurrentProgramme
end TwinPrimeProject
