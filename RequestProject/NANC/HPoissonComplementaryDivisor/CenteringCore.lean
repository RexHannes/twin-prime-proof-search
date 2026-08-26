import Mathlib

/-!
# HPoissonComplementaryDivisor, Module 5: centering identities and bookkeeping

Finite rational arithmetic only.

* `rho q t = 1_{q ∣ t} − 1/q` is the centered divisor indicator;
* `indicator_eq_rho_add` : `1_{q ∣ t} = ρ_q(t) + 1/q`;
* `rho_mul_coprime` : for coprime `d, p > 0`,
  `ρ_{dp}(t) = ρ_d(t) ρ_p(t) + ρ_d(t)/p + ρ_p(t)/d`.

The second half of the module keeps **four different operations apart**:

1. deleting the `h = 0` frequency;
2. subtracting `1/q`;
3. subtracting an abstract source expected term `E`;
4. restricting to a diagonal `q₁ = q₂`.

Each pair is identified only under an explicit hypothesis, and
`centering_ops_pairwise_distinct` exhibits data on which all four differ.
-/

namespace TwinPrimeProject
namespace HPoissonCD

open Finset

/-! ## 1. The centered divisor indicator -/

/-- The divisor indicator `1_{q ∣ t}`, rational valued. -/
def divIndicator (q : ℕ) (t : ℤ) : ℚ := if (q : ℤ) ∣ t then 1 else 0

/-- The centered divisor indicator `ρ_q(t) = 1_{q ∣ t} − 1/q`. -/
def rho (q : ℕ) (t : ℤ) : ℚ := divIndicator q t - 1 / q

/-- **Centering identity.**  `1_{q ∣ t} = ρ_q(t) + 1/q`. -/
theorem indicator_eq_rho_add (q : ℕ) (t : ℤ) : divIndicator q t = rho q t + 1 / q := by
  simp [rho]

/-- The indicator is multiplicative over coprime moduli. -/
theorem divIndicator_mul_coprime {d p : ℕ} (h : Nat.Coprime d p) (t : ℤ) :
    divIndicator (d * p) t = divIndicator d t * divIndicator p t := by
  have hcop : IsCoprime (d : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  have key : (d : ℤ) * (p : ℤ) ∣ t ↔ ((d : ℤ) ∣ t ∧ (p : ℤ) ∣ t) :=
    ⟨fun hdvd => ⟨(dvd_mul_right (d : ℤ) p).trans hdvd, (dvd_mul_left (p : ℤ) d).trans hdvd⟩,
      fun hh => hcop.mul_dvd hh.1 hh.2⟩
  simp only [divIndicator, Nat.cast_mul, key]
  by_cases h₁ : (d : ℤ) ∣ t <;> by_cases h₂ : (p : ℤ) ∣ t <;> simp [h₁, h₂]

/-- **CRT expansion of the centered indicator.**  For coprime positive `d, p`,
`ρ_{dp}(t) = ρ_d(t) ρ_p(t) + ρ_d(t)/p + ρ_p(t)/d`. -/
theorem rho_mul_coprime {d p : ℕ} (hd : 0 < d) (hp : 0 < p) (h : Nat.Coprime d p) (t : ℤ) :
    rho (d * p) t = rho d t * rho p t + rho d t / p + rho p t / d := by
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  have hp' : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have hmul := divIndicator_mul_coprime h t
  simp only [rho, hmul, Nat.cast_mul]
  field_simp
  ring

/-! ## 2. Four distinct centering operations -/

variable (S : Finset ℤ) (a : ℤ → ℚ)

/-- Operation 1: delete the `h = 0` frequency. -/
def deleteZeroFrequency (S : Finset ℤ) (a : ℤ → ℚ) : ℚ := ∑ h ∈ S.erase 0, a h

/-- Operation 2: subtract `1/q`. -/
def subtractInverseModulus (S : Finset ℤ) (a : ℤ → ℚ) (q : ℕ) : ℚ := (∑ h ∈ S, a h) - 1 / q

/-- Operation 3: subtract an abstract source expected term `E`. -/
def subtractSourceExpected (S : Finset ℤ) (a : ℤ → ℚ) (E : ℚ) : ℚ := (∑ h ∈ S, a h) - E

/-- Operation 4: restrict a two-modulus quantity to the diagonal `q₁ = q₂`. -/
def diagonalRestriction (T : Finset (ℕ × ℕ)) (F : ℕ → ℕ → ℚ) : ℚ :=
  ∑ x ∈ T.filter (fun x => x.1 = x.2), F x.1 x.2

/-- Deleting the zero frequency subtracts exactly the value `a 0`, provided
`0 ∈ S`.  This is the only way operation 1 can be rewritten as a subtraction. -/
theorem deleteZeroFrequency_eq (h0 : (0 : ℤ) ∈ S) :
    deleteZeroFrequency S a = (∑ h ∈ S, a h) - a 0 := by
  rw [deleteZeroFrequency, Finset.sum_erase_eq_sub h0]

/-- **Identification 1 = 3 requires a hypothesis**: `E = a 0`. -/
theorem deleteZero_eq_subtractSource_iff (h0 : (0 : ℤ) ∈ S) (E : ℚ) :
    deleteZeroFrequency S a = subtractSourceExpected S a E ↔ E = a 0 := by
  rw [deleteZeroFrequency_eq S a h0, subtractSourceExpected]
  constructor <;> intro h <;> linarith

/-- **Identification 1 = 2 requires a hypothesis**: `a 0 = 1/q`. -/
theorem deleteZero_eq_subtractInverse_iff (h0 : (0 : ℤ) ∈ S) (q : ℕ) :
    deleteZeroFrequency S a = subtractInverseModulus S a q ↔ a 0 = 1 / q := by
  rw [deleteZeroFrequency_eq S a h0, subtractInverseModulus]
  constructor <;> intro h <;> linarith

/-- **Identification 2 = 3 requires a hypothesis**: `E = 1/q`. -/
theorem subtractInverse_eq_subtractSource_iff (q : ℕ) (E : ℚ) :
    subtractInverseModulus S a q = subtractSourceExpected S a E ↔ E = 1 / q := by
  rw [subtractInverseModulus, subtractSourceExpected]
  constructor <;> intro h <;> linarith

/-- **The diagonal restriction is a genuinely different operation**: it can
differ from the full two-modulus sum. -/
theorem diagonalRestriction_ne_full :
    ∃ (T : Finset (ℕ × ℕ)) (F : ℕ → ℕ → ℚ),
      diagonalRestriction T F ≠ ∑ x ∈ T, F x.1 x.2 := by
  refine ⟨{(1, 2)}, fun _ _ => 1, ?_⟩
  simp [diagonalRestriction]

/-- **No silent identification.**  There are data on which the three
one-variable centering operations take three different values. -/
theorem centering_ops_pairwise_distinct :
    ∃ (S : Finset ℤ) (a : ℤ → ℚ) (q : ℕ) (E : ℚ),
      (0 : ℤ) ∈ S ∧
      deleteZeroFrequency S a ≠ subtractInverseModulus S a q ∧
      deleteZeroFrequency S a ≠ subtractSourceExpected S a E ∧
      subtractInverseModulus S a q ≠ subtractSourceExpected S a E := by
  refine ⟨{0, 1}, fun h => if h = 0 then (3 : ℚ) else 1, 2, 5, by decide, ?_, ?_, ?_⟩ <;>
    · simp [deleteZeroFrequency, subtractInverseModulus, subtractSourceExpected]
      norm_num

end HPoissonCD
end TwinPrimeProject
