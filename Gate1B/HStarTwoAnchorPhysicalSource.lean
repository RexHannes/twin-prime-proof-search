import Mathlib

/-!
# Gate 1B · the exact **two-anchor physical source** for HSTAR `k = 0`, `J = ∅`

**Source data and exact arithmetic only.**  Nothing analytic is proved here,
nothing analytic is assumed, and no interface is inhabited.

The object banked in this module is the *literal physical source* of the
HSTAR `k = 0`, `J = ∅` reconstruction: two determinant anchors carrying the
**fixed shift `+2`**,

```
  g * e₁ * wp₁ * ℓ₁ = T₁ * π₁ + 2        (anchor₁)
  g * e₂ * wp₂ * ℓ₂ = T₂ * π₂ + 2        (anchor₂)
```

with the physical variables kept as separate, named fields:

* `g`      the common (gcd) part of the two moduli;
* `e i`    the Möbius (squarefree) part of the source coefficient;
* `wp i`   the **Vaughan prime**;
* `ell i`  the length/divisor variable;
* `T i`    the Perron/parameter variable;
* `pi i`   the extracted **Ford prime**.

The `+2` is *never* hidden inside a smooth weight: it appears literally in the
two anchor fields, and the derived difference algebra (in
`Gate1B.HStarTwoAnchorDifferenceAlgebra`) is proved as a *consequence*, never
used as a replacement (see `Gate1B.HStarTwoAnchorCounterguards`).

## Contents

* §1 the source structure `HStarTwoAnchorSource`;
* §2 the integer form of the anchors and the two **physical defects**
  `C₁ = C₂ = 2`;
* §3 the two moduli `q i = g * e i * wp i` and the exact `+2` divisibility
  `q i ∣ T i * π i + 2`, i.e. `T i * π i ≡ -2 (mod q i)`;
* §4 an explicit inhabitant (non-vacuity guard): the source type is not empty.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTwoAnchor

/-! ## 1. The physical two-anchor source -/

/-- **The exact physical two-anchor HSTAR source.**

All variables are natural numbers, so the two anchor equations are literal
identities with the fixed shift `+2` on the right-hand side.  The Vaughan
primes `wp i` and the extracted Ford primes `pi i` are kept as *separate named
fields* with their own primality hypotheses; they are never identified (see
`Gate1B.HStarMobiusPrimeSource` for the typing firewall). -/
structure HStarTwoAnchorSource where
  /-- The common part of the two moduli. -/
  g : ℕ
  /-- Möbius (squarefree) part of the first coefficient. -/
  e1 : ℕ
  /-- Möbius (squarefree) part of the second coefficient. -/
  e2 : ℕ
  /-- The first Vaughan prime. -/
  wp1 : ℕ
  /-- The second Vaughan prime. -/
  wp2 : ℕ
  /-- The first length variable. -/
  ell1 : ℕ
  /-- The second length variable. -/
  ell2 : ℕ
  /-- The first Perron/parameter variable. -/
  T1 : ℕ
  /-- The second Perron/parameter variable. -/
  T2 : ℕ
  /-- The first extracted Ford prime. -/
  pi1 : ℕ
  /-- The second extracted Ford prime. -/
  pi2 : ℕ
  g_pos : 0 < g
  e1_pos : 0 < e1
  e2_pos : 0 < e2
  ell1_pos : 0 < ell1
  ell2_pos : 0 < ell2
  T1_pos : 0 < T1
  T2_pos : 0 < T2
  wp1_prime : Nat.Prime wp1
  wp2_prime : Nat.Prime wp2
  pi1_prime : Nat.Prime pi1
  pi2_prime : Nat.Prime pi2
  /-- **BOXED anchor 1.**  The literal `+2` determinant equation. -/
  anchor1 : g * e1 * wp1 * ell1 = T1 * pi1 + 2
  /-- **BOXED anchor 2.**  The literal `+2` determinant equation. -/
  anchor2 : g * e2 * wp2 * ell2 = T2 * pi2 + 2

namespace HStarTwoAnchorSource

variable (S : HStarTwoAnchorSource)

/-! ## 2. Integer form and the physical defects -/

/-- Anchor 1 over `ℤ`. -/
theorem anchor1Z :
    (S.g : ℤ) * S.e1 * S.wp1 * S.ell1 = (S.T1 : ℤ) * S.pi1 + 2 := by
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) S.anchor1

/-- Anchor 2 over `ℤ`. -/
theorem anchor2Z :
    (S.g : ℤ) * S.e2 * S.wp2 * S.ell2 = (S.T2 : ℤ) * S.pi2 + 2 := by
  exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) S.anchor2

/-- The first **physical defect** `C₁ = g e₁ wp₁ ℓ₁ − T₁ π₁`. -/
def defect1 : ℤ := (S.g : ℤ) * S.e1 * S.wp1 * S.ell1 - (S.T1 : ℤ) * S.pi1

/-- The second **physical defect** `C₂ = g e₂ wp₂ ℓ₂ − T₂ π₂`. -/
def defect2 : ℤ := (S.g : ℤ) * S.e2 * S.wp2 * S.ell2 - (S.T2 : ℤ) * S.pi2

/-- **The first defect of a physical source is exactly `2`.** -/
theorem defect1_eq_two : S.defect1 = 2 := by
  have := S.anchor1Z
  simp only [defect1]
  omega

/-- **The second defect of a physical source is exactly `2`.** -/
theorem defect2_eq_two : S.defect2 = 2 := by
  have := S.anchor2Z
  simp only [defect2]
  omega

/-- Both defects agree (and both are `2`). -/
theorem defect1_eq_defect2 : S.defect1 = S.defect2 := by
  rw [S.defect1_eq_two, S.defect2_eq_two]

/-! ## 3. The two moduli and the exact `+2` congruence -/

/-- The first physical modulus `q₁ = g e₁ wp₁`. -/
def q1 : ℕ := S.g * S.e1 * S.wp1

/-- The second physical modulus `q₂ = g e₂ wp₂`. -/
def q2 : ℕ := S.g * S.e2 * S.wp2

theorem q1_pos : 0 < S.q1 :=
  Nat.mul_pos (Nat.mul_pos S.g_pos S.e1_pos) S.wp1_prime.pos

theorem q2_pos : 0 < S.q2 :=
  Nat.mul_pos (Nat.mul_pos S.g_pos S.e2_pos) S.wp2_prime.pos

/-- **Anchor 1 as a `+2` divisibility.**  `q₁ ∣ T₁ π₁ + 2`. -/
theorem q1_dvd : S.q1 ∣ S.T1 * S.pi1 + 2 := ⟨S.ell1, S.anchor1.symm⟩

/-- **Anchor 2 as a `+2` divisibility.**  `q₂ ∣ T₂ π₂ + 2`. -/
theorem q2_dvd : S.q2 ∣ S.T2 * S.pi2 + 2 := ⟨S.ell2, S.anchor2.symm⟩

/-- The `g`-part divides the first modulus. -/
theorem g_dvd_q1 : S.g ∣ S.q1 := ⟨S.e1 * S.wp1, by simp [q1, Nat.mul_assoc]⟩

/-- The `g`-part divides the second modulus. -/
theorem g_dvd_q2 : S.g ∣ S.q2 := ⟨S.e2 * S.wp2, by simp [q2, Nat.mul_assoc]⟩

end HStarTwoAnchorSource

/-! ## 4. Non-vacuity: an explicit physical source -/

/-- An explicit inhabitant of the physical two-anchor source type:

```
  g = 5, e₁ = 1, wp₁ = 7, ℓ₁ = 1, T₁ = 11, π₁ = 3 :  5·1·7·1 = 35 = 11·3 + 2
  g = 5, e₂ = 1, wp₂ = 2, ℓ₂ = 1, T₂ = 4,  π₂ = 2 :  5·1·2·1 = 10 =  4·2 + 2
```

Both Vaughan primes and both Ford primes are genuine primes.  This is the
**non-vacuity guard** for every theorem quantified over
`HStarTwoAnchorSource`. -/
def witnessSource : HStarTwoAnchorSource where
  g := 5
  e1 := 1
  e2 := 1
  wp1 := 7
  wp2 := 2
  ell1 := 1
  ell2 := 1
  T1 := 11
  T2 := 4
  pi1 := 3
  pi2 := 2
  g_pos := by norm_num
  e1_pos := by norm_num
  e2_pos := by norm_num
  ell1_pos := by norm_num
  ell2_pos := by norm_num
  T1_pos := by norm_num
  T2_pos := by norm_num
  wp1_prime := by norm_num
  wp2_prime := by norm_num
  pi1_prime := by norm_num
  pi2_prime := by norm_num
  anchor1 := by norm_num
  anchor2 := by norm_num

/-- **Non-vacuity.**  The physical two-anchor source type is inhabited. -/
theorem hStarTwoAnchorSource_nonempty : Nonempty HStarTwoAnchorSource :=
  ⟨witnessSource⟩

end HStarTwoAnchor
end CurrentProgramme
end TwinPrimeProject
