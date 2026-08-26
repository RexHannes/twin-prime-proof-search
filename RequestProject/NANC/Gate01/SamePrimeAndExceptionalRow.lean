import RequestProject.NANC.Gate01.HZeroCentering

/-!
# Gate 0–1 finite bank: same-prime, exceptional-row and Ramanujan remainder

Three finite strata are banked here.

* **Same prime, no joint hit.**  If `m' A - m B = 2k` with `k ≠ 0` and the
  modulus `P` satisfies `2|k| < P`, then `P` cannot divide both `A` and `B`.
  Consequently the centered same-prime contribution against a common smooth
  weight is the pure constant `- Ŵ(0) / p²` per prime, so the same-prime main
  term is `- Ŵ(0) ∑_p b_p d_p / p²`.

* **Exceptional row.**  If an odd prime `p'` divides `m' = m + k r`, then
  `r B = m' w + 2 ≡ 2 (mod p')`, hence `p' ∤ B` and `ρ_{p'}(B) = -1/p'`.

* **Ramanujan remainder.**  For a nontrivial additive character `ψ` of `𝔽_p`,
  `∑_{y ≠ 0} ψ(A y)` equals `p - 1` if `A = 0` and `-1` otherwise.

Status labels: `SAME_PRIME_NO_JOINT_HIT_BANKED`,
`EXCEPTIONAL_ROW_NO_HIT_BANKED`, `RAMANUJAN_MINUS_ONE_REMAINDER_BANKED`.
-/

namespace RouteAFibreFrame
namespace Gate01

open Finset

/-! ### 7.1 Same prime: no joint hit -/

/-- A common divisor of `A` and `B` divides the fixed shift `2k`. -/
theorem common_divisor_dvd_two_k {P m mPrime A B k : ℤ}
    (hdet : mPrime * A - m * B = 2 * k) (hA : P ∣ A) (hB : P ∣ B) : P ∣ 2 * k := by
  rw [← hdet]
  exact dvd_sub (hA.mul_left _) (hB.mul_left _)

/-- **Same-prime no joint hit.**  If `2|k| < P` and `k ≠ 0`, the joint event
`P ∣ A ∧ P ∣ B` is empty. -/
theorem same_prime_no_joint_hit {P m mPrime A B k : ℤ} (hk : k ≠ 0) (hP : 2 * |k| < P)
    (hdet : mPrime * A - m * B = 2 * k) (hA : P ∣ A) (hB : P ∣ B) : False := by
  have hdvd : P ∣ 2 * k := common_divisor_dvd_two_k hdet hA hB
  have hne : (2 : ℤ) * k ≠ 0 := by
    simpa using hk
  have hle : P ≤ |2 * k| := Int.le_of_dvd (abs_pos.mpr hne) ((dvd_abs _ _).mpr hdvd)
  have : |2 * k| = 2 * |k| := by rw [abs_mul]; norm_num
  omega

/-- **Centered same-prime local contribution.**  With no joint hit, the four
centered pieces at a single prime `p` collapse to `- Ŵ(0)/p²`. -/
theorem same_prime_centered_local (W0 p : ℚ) (hp : p ≠ 0) :
    (0 : ℚ) - (1 / p) * (W0 / p) - (1 / p) * (W0 / p) + (1 / p) * (1 / p) * W0
      = -(W0 / p ^ 2) := by
  field_simp
  ring

/-- **Banked same-prime main contribution.**  Summing the local contribution
against the coefficients `b_p d_p` gives `- Ŵ(0) ∑_p b_p d_p / p²`. -/
theorem same_prime_main_contribution {ι : Type*} (s : Finset ι) (b d pv : ι → ℚ)
    (W0 : ℚ) (hpv : ∀ i ∈ s, pv i ≠ 0) :
    ∑ i ∈ s, b i * d i *
        ((0 : ℚ) - (1 / pv i) * (W0 / pv i) - (1 / pv i) * (W0 / pv i)
          + (1 / pv i) * (1 / pv i) * W0)
      = -(W0 * ∑ i ∈ s, b i * d i / pv i ^ 2) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' := hpv i hi
  field_simp
  ring

/-! ### 7.2 Exceptional row -/

/-- If `p' ∣ m'` then `r B ≡ 2 (mod p')`. -/
theorem exceptional_row_congruence {pp r mPrime w B : ℤ} (hdvd : pp ∣ mPrime)
    (hB : r * B = mPrime * w + 2) : r * B ≡ 2 [ZMOD pp] := by
  refine Int.modEq_iff_dvd.mpr ?_
  obtain ⟨c, hc⟩ := hdvd
  exact ⟨-(c * w), by rw [hB, hc]; ring⟩

/-- **Exceptional row: no hit.**  An odd prime `p'` dividing `m'` cannot divide
the edge value `B`. -/
theorem exceptional_row_no_hit {pp : ℕ} {r mPrime w B : ℤ} (hp : pp.Prime) (hodd : pp ≠ 2)
    (hdvd : (pp : ℤ) ∣ mPrime) (hB : r * B = mPrime * w + 2) : ¬ ((pp : ℤ) ∣ B) := by
  intro h
  have h1 : (pp : ℤ) ∣ r * B := h.mul_left r
  have h2 : (pp : ℤ) ∣ mPrime * w := hdvd.mul_right w
  have h3 : (pp : ℤ) ∣ (2 : ℤ) := by
    have : (2 : ℤ) = r * B - mPrime * w := by rw [hB]; ring
    rw [this]
    exact dvd_sub h1 h2
  have h4 : pp ∣ 2 := by exact_mod_cast h3
  exact hodd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)

/-- **Exceptional row: centered value.**  On the exceptional row the centered
local factor is the constant `-1/p'`. -/
theorem exceptional_row_rho {pp : ℕ} {r mPrime w B : ℤ} (hp : pp.Prime) (hodd : pp ≠ 2)
    (hdvd : (pp : ℤ) ∣ mPrime) (hB : r * B = mPrime * w + 2) :
    rho (pp : ℚ) (if (pp : ℤ) ∣ B then 1 else 0) = -(1 / (pp : ℚ)) := by
  rw [if_neg (exceptional_row_no_hit hp hodd hdvd hB)]
  simp [rho]

/-! ### 7.3 Ramanujan remainder -/

/-- **Ramanujan remainder.**  For a nontrivial additive character `ψ` of `𝔽_p`,
the sum over the nonzero residues is `p - 1` when `A = 0` and `-1` otherwise. -/
theorem ramanujan_remainder (p : ℕ) [Fact p.Prime] (ψ : AddChar (ZMod p) ℂ) (hψ : ψ ≠ 1)
    (A : ZMod p) :
    ∑ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, ψ (A * y)
      = if A = 0 then (p : ℂ) - 1 else -1 := by
  by_cases hA : A = 0
  · subst hA
    rw [if_pos rfl]
    have h : ∀ y ∈ (Finset.univ : Finset (ZMod p)).erase 0, ψ ((0 : ZMod p) * y) = 1 := by
      intro y _; simp
    rw [Finset.sum_congr rfl h, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ 0), Finset.card_univ, ZMod.card]
    have hp1 : 1 ≤ p := (Fact.out (p := p.Prime)).one_le
    simp [nsmul_eq_mul, Nat.cast_sub hp1]
  · have hall : ∑ y : ZMod p, ψ (A * y) = 0 := by
      rw [Fintype.sum_equiv (Equiv.mulLeft₀ A hA) (fun y => ψ (A * y)) (fun x => ψ x)
        (fun y => by simp [Equiv.mulLeft₀])]
      exact AddChar.sum_eq_zero_of_ne_one hψ
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ 0), hall, if_neg hA]
    simp

end Gate01
end RouteAFibreFrame
