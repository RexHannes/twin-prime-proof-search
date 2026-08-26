import RequestProject.TwinPrimeDefinitions

namespace TwinPrimeProject

/-- If an odd prime does not divide `m`, divisibility of `mn+2` is exactly one
residue class, written in `ZMod q` using the inverse of `m`. -/
theorem ShiftedCongruenceIfCoprime {q m n : ℕ} (hq : Nat.Prime q) (hqm : ¬ q ∣ m) :
    q ∣ m * n + 2 ↔
      (n : ZMod q) = -(2 : ZMod q) * (m : ZMod q)⁻¹ := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  have hm_ne : (m : ZMod q) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    exact hqm
  have key : (q : ℕ) ∣ m * n + 2 ↔ (m : ZMod q) * n + 2 = 0 := by
    constructor
    · intro hdiv
      have : ((m * n + 2 : ℕ) : ZMod q) = 0 := by
        erw [ZMod.natCast_eq_zero_iff (a := m * n + 2)]
        simp [hdiv]
      simpa [Nat.cast_add, Nat.cast_mul] using this
    · intro hzero
      have : ((m * n + 2 : ℕ) : ZMod q) = 0 := by simpa [Nat.cast_add, Nat.cast_mul] using hzero
      rwa [ZMod.natCast_eq_zero_iff] at this
  rw [key]
  constructor
  · intro h
    have h2 : (m : ZMod q) * n = -2 := by linear_combination h
    calc (n : ZMod q) = 1 * n := by ring
      _ = ((m : ZMod q) * (m : ZMod q)⁻¹) * n := by rw [mul_inv_cancel₀ hm_ne]
      _ = (m : ZMod q)⁻¹ * ((m : ZMod q) * n) := by ring
      _ = (m : ZMod q)⁻¹ * -2 := by rw [h2]
      _ = -2 * (m : ZMod q)⁻¹ := by ring
  · intro hn
    calc (m : ZMod q) * n + 2 = (m : ZMod q) * (-2 * (m : ZMod q)⁻¹) + 2 := by rw [hn]
      _ = -2 * ((m : ZMod q) * (m : ZMod q)⁻¹) + 2 := by ring
      _ = -2 * 1 + 2 := by rw [mul_inv_cancel₀ hm_ne]
      _ = 0 := by ring

/-- If an odd prime divides `m`, then the shifted product is congruent to `2`, so
that prime forbids no residue class. -/
theorem ShiftedCongruenceVacuousOnDivisor {q m n : ℕ}
    (hq : Nat.Prime q) (hqodd : q ≠ 2) (hqm : q ∣ m) : ¬ q ∣ m * n + 2 := by
  intro h
  have hprod : q ∣ m * n := dvd_mul_of_dvd_left hqm n
  have hq2 : q ∣ 2 := Nat.dvd_add_iff_right hprod |>.mpr h
  rcases (Nat.dvd_prime (by decide : Nat.Prime 2)).mp hq2 with hq1 | hqeq
  · exact hq.ne_one hq1
  · exact hqodd hqeq

/-- The exact two-branch local rule at an odd prime. -/
theorem ResidueAwareLocalRule {q m n : ℕ} (hq : Nat.Prime q) (hqodd : q ≠ 2) :
    (q ∣ m → ¬ q ∣ m * n + 2) ∧
    (¬ q ∣ m → (q ∣ m * n + 2 ↔
      (n : ZMod q) = -(2 : ZMod q) * (m : ZMod q)⁻¹)) :=
  ⟨fun h => ShiftedCongruenceVacuousOnDivisor hq hqodd h,
   fun h => ShiftedCongruenceIfCoprime hq h⟩

end TwinPrimeProject
