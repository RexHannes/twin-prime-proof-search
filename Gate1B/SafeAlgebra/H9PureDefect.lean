/-
# Gate 1B v8.3 — H9 pure-defect shell

**Status: PROVED_ALGEBRAIC.**

At defect order nine no model coordinate remains, so the shell degenerates to

    C₉ - q * ℓ = -2,   equivalently   q ℓ = C₉ + 2,   i.e.  q ℓ ≡ 2 (mod C₉).

Elementary consequence: if `C₉` is odd then `q ℓ` is a unit modulo `C₉`.  Both
sign conventions (`C₉ = y + 2` and `y = C₉ + 2`) are recorded, since a common
divisor of `y` and `C₉` divides `2` in either case.

No analytic estimate is declared, and the word "parity" deliberately does not
occur in any theorem name: this is finite divisibility bookkeeping only.
-/
import Mathlib
import Gate1B.SafeAlgebra.HighOrderRegroupGeometry

namespace Gate1B.SafeAlgebra

/-- **H9 pure-defect shell.**  The shell `C₉ - qℓ = -2` says exactly
`qℓ = C₉ + 2`. -/
theorem h9_shell (C9 q ell : ℤ) :
    C9 - q * ell = -2 ↔ q * ell = C9 + 2 := by
  constructor <;> intro h <;> linear_combination -h

/-- The congruence form of the H9 shell: `qℓ ≡ 2 (mod C₉)`. -/
theorem h9_shell_congruence (C9 q ell : ℤ) (h : C9 - q * ell = -2) :
    q * ell ≡ 2 [ZMOD C9] :=
  Int.modEq_iff_dvd.2 ⟨-1, by linear_combination h⟩

/-- **H9 unit condition (`C₉ = y + 2` convention).**  If `C₉` is odd then `y` is
coprime to `C₉`. -/
theorem h9_qell_coprime (C9 y : ℕ) (hodd : Odd C9) (h : C9 = y + 2) :
    Nat.Coprime y C9 := by
  have h1 : Nat.gcd y C9 ∣ y := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd y C9 ∣ C9 := Nat.gcd_dvd_right _ _
  have hd2 : Nat.gcd y C9 ∣ 2 := by
    have := Nat.dvd_sub h2 h1
    simpa [h] using this
  obtain ⟨k, hk⟩ := hodd
  have hle := Nat.le_of_dvd (by norm_num) hd2
  have hne2 : Nat.gcd y C9 ≠ 2 := by
    intro he
    have : (2 : ℕ) ∣ C9 := he ▸ h2
    omega
  have hne0 : Nat.gcd y C9 ≠ 0 := by
    intro he
    have : C9 = 0 := Nat.eq_zero_of_gcd_eq_zero_right he
    omega
  show Nat.gcd y C9 = 1
  omega

/-- **H9 unit condition (shell convention `y = C₉ + 2`).**  This is the case
`y = qℓ` coming from `C₉ - qℓ = -2`. -/
theorem h9_qell_coprime_shell (C9 y : ℕ) (hodd : Odd C9) (h : y = C9 + 2) :
    Nat.Coprime y C9 := by
  have h1 : Nat.gcd y C9 ∣ y := Nat.gcd_dvd_left _ _
  have h2 : Nat.gcd y C9 ∣ C9 := Nat.gcd_dvd_right _ _
  have hd2 : Nat.gcd y C9 ∣ 2 := by
    have := Nat.dvd_sub h1 h2
    simpa [h] using this
  obtain ⟨k, hk⟩ := hodd
  have hle := Nat.le_of_dvd (by norm_num) hd2
  have hne2 : Nat.gcd y C9 ≠ 2 := by
    intro he
    have : (2 : ℕ) ∣ C9 := he ▸ h2
    omega
  have hne0 : Nat.gcd y C9 ≠ 0 := by
    intro he
    have : C9 = 0 := Nat.eq_zero_of_gcd_eq_zero_right he
    omega
  show Nat.gcd y C9 = 1
  omega

/-- Order nine leaves no model coordinate: the shell is pure defect. -/
theorem h9_no_model : remainingModels 9 = 0 := (orderNine_noModel).1

end Gate1B.SafeAlgebra
