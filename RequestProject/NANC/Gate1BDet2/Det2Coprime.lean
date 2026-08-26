import Mathlib
import RequestProject.NANC.Gate1BDet2.ComplementaryDivisorDet2

/-!
# Gate 1B / determinant-2 bank, Module 3: divisor rigidity

From the fixed-shift incidence `u v + 2 = l q` any common divisor of `u` and `l`
(respectively of `v` and `q`) divides the shift `2`.  In the odd sector this
gives outright coprimality, which is what the affine-line parametrisation of
Module 4 needs.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. Divisor rigidity over `ℕ` -/

/-- **Rigidity, `u`–`l` side.**  If `u v + 2 = l q`, then any common divisor of
`u` and `l` divides `2`. -/
theorem dvd_two_of_dvd_u_of_dvd_l {u v q l g : ℕ} (h : u * v + 2 = l * q)
    (hgu : g ∣ u) (hgl : g ∣ l) : g ∣ 2 := by
  have h1 : g ∣ l * q := hgl.mul_right q
  have h2 : g ∣ u * v := hgu.mul_right v
  have h3 : l * q - u * v = 2 := by omega
  simpa [h3] using Nat.dvd_sub h1 h2

/-- **Rigidity, `v`–`q` side.**  If `u v + 2 = l q`, then any common divisor of
`v` and `q` divides `2`. -/
theorem dvd_two_of_dvd_v_of_dvd_q {u v q l g : ℕ} (h : u * v + 2 = l * q)
    (hgv : g ∣ v) (hgq : g ∣ q) : g ∣ 2 := by
  have h1 : g ∣ l * q := Dvd.dvd.mul_left hgq l
  have h2 : g ∣ u * v := Dvd.dvd.mul_left hgv u
  have h3 : l * q - u * v = 2 := by omega
  simpa [h3] using Nat.dvd_sub h1 h2

/-- `gcd u l ∣ 2`. -/
theorem gcd_u_l_dvd_two {u v q l : ℕ} (h : u * v + 2 = l * q) :
    Nat.gcd u l ∣ 2 :=
  dvd_two_of_dvd_u_of_dvd_l h (Nat.gcd_dvd_left u l) (Nat.gcd_dvd_right u l)

/-- `gcd v q ∣ 2`. -/
theorem gcd_v_q_dvd_two {u v q l : ℕ} (h : u * v + 2 = l * q) :
    Nat.gcd v q ∣ 2 :=
  dvd_two_of_dvd_v_of_dvd_q h (Nat.gcd_dvd_left v q) (Nat.gcd_dvd_right v q)

/-! ## 2. Odd-sector coprimality -/

/-- A divisor of `2` dividing an odd number is `1`. -/
theorem eq_one_of_dvd_two_of_dvd_odd {g a : ℕ} (hg : g ∣ 2) (hga : g ∣ a)
    (ha : Odd a) : g = 1 := by
  rcases (Nat.prime_two.eq_one_or_self_of_dvd g hg) with h1 | h2
  · exact h1
  · subst h2
    obtain ⟨k, hk⟩ := hga
    obtain ⟨m, hm⟩ := ha
    omega

/-- **Odd-sector coprimality, `u`–`l` side.**  (The oddness of `l` is listed
because the source statement carries it, but the proof only needs `Odd u`.) -/
theorem coprime_u_l_of_odd {u v q l : ℕ} (h : u * v + 2 = l * q)
    (hu : Odd u) (_hl : Odd l) : Nat.Coprime u l :=
  eq_one_of_dvd_two_of_dvd_odd (gcd_u_l_dvd_two h) (Nat.gcd_dvd_left u l) hu

/-- **Odd-sector coprimality, `v`–`q` side.**  (The oddness of `q` is listed
because the source statement carries it, but the proof only needs `Odd v`.) -/
theorem coprime_v_q_of_odd {u v q l : ℕ} (h : u * v + 2 = l * q)
    (hv : Odd v) (_hq : Odd q) : Nat.Coprime v q :=
  eq_one_of_dvd_two_of_dvd_odd (gcd_v_q_dvd_two h) (Nat.gcd_dvd_left v q) hv

/-! ## 3. Integer versions -/

/-- Rigidity over `ℤ`, `u`–`l` side. -/
theorem int_dvd_two_of_dvd_u_of_dvd_l {u v q l g : ℤ} (h : u * v + 2 = l * q)
    (hgu : g ∣ u) (hgl : g ∣ l) : g ∣ 2 := by
  have h1 : g ∣ l * q := hgl.mul_right q
  have h2 : g ∣ u * v := hgu.mul_right v
  have : (2 : ℤ) = l * q - u * v := by linarith
  rw [this]
  exact dvd_sub h1 h2

/-- Rigidity over `ℤ`, `v`–`q` side. -/
theorem int_dvd_two_of_dvd_v_of_dvd_q {u v q l g : ℤ} (h : u * v + 2 = l * q)
    (hgv : g ∣ v) (hgq : g ∣ q) : g ∣ 2 := by
  have h1 : g ∣ l * q := Dvd.dvd.mul_left hgq l
  have h2 : g ∣ u * v := Dvd.dvd.mul_left hgv u
  have : (2 : ℤ) = l * q - u * v := by linarith
  rw [this]
  exact dvd_sub h1 h2

end Gate1BDet2
end TwinPrimeProject
