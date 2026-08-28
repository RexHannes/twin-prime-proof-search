import RequestProject.NANC.Gate1B.V11S2GeneratedTwist

/-!
# V11 · Gate 1B — the two-parameter `P±` firewall

**Purpose.**  Permanently prevent a future run from calling all generated twists
"just Mellin".

Control of `n ↦ n^{it}` does **not** imply control of

    n ↦ (P⁻(n) + 1/2)^{it} · P⁺(n)^{it'}.

Two independent firewalls are proved.

1. *Coordinate firewall* — two unimodular coordinate families on a finite index
   set, one with total cancellation against a coefficient vector and one with
   none.  This is the abstract reason: a bound against one unimodular family
   says nothing about another.

2. *Semantic firewall* — relative to **any** supplied realisation, the
   `P±`-twisted weight is constant on the smooth fibre `{4, 8}` (both have
   `P⁻ = P⁺ = 2`), whereas the Mellin twist at `t = π / log 2` separates `4`
   from `8`.  Hence the `P±` weight is not a scalar multiple of that Mellin
   weight.

No realisation is constructed here, and none is assumed to exist.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-! ## 1. The coordinate firewall -/

/-- Two unimodular coordinate families on a finite index set: the Mellin
coordinate and the two-parameter prime-extrema coordinate, abstracted to their
only shared feature — unimodularity. -/
structure TwistCoordinateModel (ι : Type) [Fintype ι] where
  /-- The pure Mellin coordinate. -/
  mellinCoord : ι → ℂ
  /-- The two-parameter prime-extrema coordinate. -/
  extremaCoord : ι → ℂ
  /-- Unimodularity of the Mellin coordinate. -/
  mellin_unimodular : ∀ i, ‖mellinCoord i‖ = 1
  /-- Unimodularity of the extrema coordinate. -/
  extrema_unimodular : ∀ i, ‖extremaCoord i‖ = 1

/-- The transform of a coefficient vector against the Mellin coordinate. -/
noncomputable def TwistCoordinateModel.mellinValue {ι : Type} [Fintype ι]
    (M : TwistCoordinateModel ι) (c : ι → ℂ) : ℂ := ∑ i, c i * M.mellinCoord i

/-- The transform of a coefficient vector against the extrema coordinate. -/
noncomputable def TwistCoordinateModel.extremaValue {ι : Type} [Fintype ι]
    (M : TwistCoordinateModel ι) (c : ι → ℂ) : ℂ := ∑ i, c i * M.extremaCoord i

/-- The explicit separating model on `Fin k × Fin 2`: the Mellin coordinate
alternates in the second factor, the extrema coordinate is constant. -/
def separatingModel (k : ℕ) : TwistCoordinateModel (Fin k × Fin 2) where
  mellinCoord := fun p => if p.2 = 0 then 1 else -1
  extremaCoord := fun _ => 1
  mellin_unimodular := by intro p; by_cases h : p.2 = 0 <;> simp [h]
  extrema_unimodular := by intro p; simp

/-- **THE COORDINATE FIREWALL.**  Total cancellation against the Mellin
coordinate implies nothing about the prime-extrema coordinate: the extrema
transform can be as large as the full ℓ¹ mass. -/
theorem separatingModel_mellinValue_zero (k : ℕ) :
    (separatingModel k).mellinValue (fun _ => 1) = 0 := by
  simp [TwistCoordinateModel.mellinValue, separatingModel, Fintype.sum_prod_type,
    Fin.sum_univ_two]

/-- …while the extrema transform of the same coefficient vector is `2k`. -/
theorem separatingModel_extremaValue (k : ℕ) :
    (separatingModel k).extremaValue (fun _ => 1) = (2 * k : ℕ) := by
  simp [TwistCoordinateModel.extremaValue, separatingModel]
  ring

/-- **THE COORDINATE FIREWALL, negated form.**  No universal implication from
Mellin control to prime-extrema control exists. -/
theorem mellinControl_does_not_imply_primeExtremaControl :
    ¬ ∀ (ι : Type) (_ : Fintype ι) (M : TwistCoordinateModel ι) (c : ι → ℂ),
        (∀ i, ‖c i‖ ≤ 1) → M.mellinValue c = 0 → ‖M.extremaValue c‖ ≤ 1 := by
  intro h
  have hc : ∀ _i : Fin 1 × Fin 2, ‖(1 : ℂ)‖ ≤ 1 := by intro i; simp
  have := h (Fin 1 × Fin 2) inferInstance (separatingModel 1) (fun _ => 1) hc
    (separatingModel_mellinValue_zero 1)
  rw [separatingModel_extremaValue 1] at this
  norm_num at this

/-! ## 2. The semantic firewall -/

/-- Relative to any supplied realisation, a two-parameter `P±` twist is constant
on any pair of integers with the same prime extrema. -/
theorem extremaTwist_constant_on_prime_fibre (E : PrimeExtremaRealisation)
    (a b : PrimeExtremaAtom) (n₁ n₂ : ℕ)
    (hm : E.Pminus n₁ = E.Pminus n₂) (hp : E.Pplus n₁ = E.Pplus n₂) :
    semPrimeExtremaAtom E a n₁ * semPrimeExtremaAtom E b n₁
      = semPrimeExtremaAtom E a n₂ * semPrimeExtremaAtom E b n₂ := by
  cases a <;> cases b <;> simp [semPrimeExtremaAtom, hm, hp]

/-- In any realisation, `P⁻(4) = 2`. -/
theorem Pminus_four (E : PrimeExtremaRealisation) : E.Pminus 4 = 2 := by
  have hp : (E.Pminus 4).Prime := E.Pminus_prime 4 (by norm_num)
  have hd : E.Pminus 4 ∣ 4 := E.Pminus_dvd 4 (by norm_num)
  have hd2 : E.Pminus 4 ∣ 2 ^ 2 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2)

/-- In any realisation, `P⁺(4) = 2`. -/
theorem Pplus_four (E : PrimeExtremaRealisation) : E.Pplus 4 = 2 := by
  have hp : (E.Pplus 4).Prime := E.Pplus_prime 4 (by norm_num)
  have hd : E.Pplus 4 ∣ 4 := E.Pplus_dvd 4 (by norm_num)
  have hd2 : E.Pplus 4 ∣ 2 ^ 2 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2)

/-- In any realisation, `P⁻(8) = 2`. -/
theorem Pminus_eight (E : PrimeExtremaRealisation) : E.Pminus 8 = 2 := by
  have hp : (E.Pminus 8).Prime := E.Pminus_prime 8 (by norm_num)
  have hd : E.Pminus 8 ∣ 8 := E.Pminus_dvd 8 (by norm_num)
  have hd2 : E.Pminus 8 ∣ 2 ^ 3 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2)

/-- In any realisation, `P⁺(8) = 2`. -/
theorem Pplus_eight (E : PrimeExtremaRealisation) : E.Pplus 8 = 2 := by
  have hp : (E.Pplus 8).Prime := E.Pplus_prime 8 (by norm_num)
  have hd : E.Pplus 8 ∣ 8 := E.Pplus_dvd 8 (by norm_num)
  have hd2 : E.Pplus 8 ∣ 2 ^ 3 := by simpa using hd
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd2)

/-- The Mellin twist at `t = π / log 2` separates `4` from `8`: the two values
differ by the factor `2^{it} = −1`. -/
theorem mellinTwist_separates_four_eight :
    semAtom (.mellinTwist (Real.pi / Real.log 2)) 8
      = - semAtom (.mellinTwist (Real.pi / Real.log 2)) 4 := by
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hlogC : ((Real.log 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog
  simp only [semAtom]
  set z : ℂ := Complex.I * ((Real.pi / Real.log 2 : ℝ) : ℂ) with hz
  have hmul : ((((8 : ℕ) : ℝ)) : ℂ) ^ z = ((((4 : ℕ) : ℝ)) : ℂ) ^ z * (((2 : ℝ)) : ℂ) ^ z := by
    rw [show ((8 : ℕ) : ℝ) = (4 : ℝ) * (2 : ℝ) by norm_num, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have htwo : (((2 : ℝ)) : ℂ) ^ z = -1 := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num : (((2 : ℝ)) : ℂ) ≠ 0)]
    rw [← Complex.ofReal_log (by norm_num : (0 : ℝ) ≤ 2), hz]
    have key : ((Real.log 2 : ℝ) : ℂ) * (Complex.I * ((Real.pi / Real.log 2 : ℝ) : ℂ))
        = (Real.pi : ℂ) * Complex.I := by
      rw [show ((Real.pi / Real.log 2 : ℝ) : ℂ) = (Real.pi : ℂ) / ((Real.log 2 : ℝ) : ℂ) by
        push_cast; ring]
      field_simp
    rw [key, Complex.exp_pi_mul_I]
  rw [hmul, htwo]
  ring

/-- The separating Mellin twist does not vanish at `4`. -/
theorem mellinTwist_four_ne_zero :
    semAtom (.mellinTwist (Real.pi / Real.log 2)) 4 ≠ 0 := by
  simp only [semAtom]
  rw [Complex.cpow_def_of_ne_zero (by norm_num : ((((4 : ℕ) : ℝ)) : ℂ) ≠ 0)]
  exact Complex.exp_ne_zero _

/-- **THE SEMANTIC FIREWALL.**  Relative to *any* supplied realisation, the
two-parameter `P±` twist is not a scalar multiple of the Mellin twist at
`t = π / log 2`, unless that scalar is zero. -/
theorem primeExtremaTwist_is_not_a_mellinTwist (E : PrimeExtremaRealisation)
    (a b : PrimeExtremaAtom) (c : ℂ) :
    (fun n => semPrimeExtremaAtom E a n * semPrimeExtremaAtom E b n)
        = (fun n => c * semAtom (.mellinTwist (Real.pi / Real.log 2)) n) → c = 0 := by
  intro hEq
  have hfib := extremaTwist_constant_on_prime_fibre E a b 4 8
    (by rw [Pminus_four, Pminus_eight]) (by rw [Pplus_four, Pplus_eight])
  have h4 := congrFun hEq 4
  have h8 := congrFun hEq 8
  rw [h4, h8, mellinTwist_separates_four_eight] at hfib
  have hzero : c * semAtom (.mellinTwist (Real.pi / Real.log 2)) 4 = 0 := by
    linear_combination hfib / 2
  rcases mul_eq_zero.mp hzero with hc | hm
  · exact hc
  · exact absurd hm mellinTwist_four_ne_zero

end Gate1BV11
end TwinPrimeProject
