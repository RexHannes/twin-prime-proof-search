import Gate1B.PuncturedFourierFrame
import Gate1B.HNEAPIndexCongruence

/-!
# Gate 1B · product-congruence reformulation and the product-residue interface

**Finite algebra only.**  The AP-index relation `d·h ≡ r·s (mod g)` is
reformulated as an equality of two product residues, the resulting bilinear
form is diagonalised over residues, a Cauchy–Schwarz compiler is proved, and
the additive-Fourier form of the congruence indicator is established by reusing
the existing punctured-Fourier character machinery.

The two physical energies are **interfaces only**
(`ProductResidueEnergyDH`, `ProductResidueEnergyRS`): no bound on them is
invented.

## Contents

* §1 product-residue aggregates `A_x`, `B_x` and the exact pairing identity;
* §2 the product-residue Cauchy compiler `|∑_x A_x B_x| ≤ ‖A‖₂‖B‖₂`;
* §3 the two energy interfaces;
* §4 `productCongruence_additiveFourier`: the exact finite-character identity
  and the factorisation of the operator into two bilinear Fourier forms.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HNEProductResidue

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

variable {g : ℕ} {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-! ## 1. Product-residue aggregates -/

/-- `A_x := ∑_{d·h ≡ x} α(d,h)`, for an arbitrary residue map. -/
noncomputable def residueAggregate (P : Finset ι) (cls : ι → ZMod g) (α : ι → ℂ)
    (x : ZMod g) : ℂ :=
  ∑ p ∈ P with cls p = x, α p

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Exact product-congruence pairing.**

```
∑_{cls p = cls q} α(p)·β(q) = ∑_x A_x·B_x.
```
-/
theorem productResidue_pairing [Fintype (ZMod g)] (P : Finset ι) (Q : Finset κ)
    (clsD : ι → ZMod g) (clsR : κ → ZMod g) (α : ι → ℂ) (β : κ → ℂ) :
    ∑ p ∈ P, ∑ q ∈ Q, (if clsD p = clsR q then α p * β q else 0)
      = ∑ x : ZMod g, residueAggregate P clsD α x * residueAggregate Q clsR β x := by
  classical
  have expand : ∀ x : ZMod g,
      residueAggregate P clsD α x * residueAggregate Q clsR β x
        = ∑ p ∈ P with clsD p = x,
            ∑ q ∈ Q, (if clsR q = clsD p then α p * β q else 0) := by
    intro x
    rw [residueAggregate, residueAggregate, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hx : clsD p = x := (Finset.mem_filter.mp hp).2
    rw [hx, Finset.sum_filter]
  calc ∑ p ∈ P, ∑ q ∈ Q, (if clsD p = clsR q then α p * β q else 0)
      = ∑ p ∈ P, ∑ q ∈ Q, (if clsR q = clsD p then α p * β q else 0) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        by_cases h : clsD p = clsR q
        · rw [if_pos h, if_pos h.symm]
        · rw [if_neg h, if_neg (fun hc => h hc.symm)]
    _ = ∑ x : ZMod g, ∑ p ∈ P with clsD p = x,
          ∑ q ∈ Q, (if clsR q = clsD p then α p * β q else 0) :=
        (Finset.sum_fiberwise_of_maps_to (fun p _ => Finset.mem_univ (clsD p)) _).symm
    _ = ∑ x : ZMod g, residueAggregate P clsD α x * residueAggregate Q clsR β x :=
        Finset.sum_congr rfl fun x _ => (expand x).symm

/-! ## 2. The product-residue Cauchy compiler -/

/-- **Cauchy–Schwarz over residues.**  `|∑_x A_x B_x| ≤ ‖A‖₂ · ‖B‖₂`. -/
theorem productResidue_cauchy [Fintype (ZMod g)] (A B : ZMod g → ℂ) :
    ‖∑ x : ZMod g, A x * B x‖
      ≤ Real.sqrt (∑ x : ZMod g, ‖A x‖ ^ 2) * Real.sqrt (∑ x : ZMod g, ‖B x‖ ^ 2) := by
  classical
  have h1 : ‖∑ x : ZMod g, A x * B x‖ ≤ ∑ x : ZMod g, ‖A x‖ * ‖B x‖ := by
    calc ‖∑ x : ZMod g, A x * B x‖ ≤ ∑ x : ZMod g, ‖A x * B x‖ := norm_sum_le _ _
      _ = ∑ x : ZMod g, ‖A x‖ * ‖B x‖ := by simp
  have h2 : (∑ x : ZMod g, ‖A x‖ * ‖B x‖) ^ 2
      ≤ (∑ x : ZMod g, ‖A x‖ ^ 2) * ∑ x : ZMod g, ‖B x‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hA : (0:ℝ) ≤ ∑ x : ZMod g, ‖A x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hB : (0:ℝ) ≤ ∑ x : ZMod g, ‖B x‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have h3 : ∑ x : ZMod g, ‖A x‖ * ‖B x‖
      ≤ Real.sqrt (∑ x : ZMod g, ‖A x‖ ^ 2) * Real.sqrt (∑ x : ZMod g, ‖B x‖ ^ 2) := by
    have hnn : (0:ℝ) ≤ ∑ x : ZMod g, ‖A x‖ * ‖B x‖ :=
      Finset.sum_nonneg fun _ _ => by positivity
    have := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq hnn, Real.sqrt_mul hA] at this
  linarith

/-! ## 3. The two energy interfaces -/

/-- **Interface (not proved).**  The `(d,h)` product-residue energy. -/
def ProductResidueEnergyDH [Fintype (ZMod g)] (P : Finset ι) (cls : ι → ZMod g)
    (α : ι → ℂ) (bound : ℝ) : Prop :=
  ∑ x : ZMod g, ‖residueAggregate P cls α x‖ ^ 2 ≤ bound

/-- **Interface (not proved).**  The `(r,s)` product-residue energy. -/
def ProductResidueEnergyRS [Fintype (ZMod g)] (Q : Finset κ) (cls : κ → ZMod g)
    (β : κ → ℂ) (bound : ℝ) : Prop :=
  ∑ x : ZMod g, ‖residueAggregate Q cls β x‖ ^ 2 ≤ bound

omit [DecidableEq ι] [DecidableEq κ] in
/-- The compiler that consumes both energies.  Its antecedents are supplied
nowhere in this repository. -/
theorem productResidue_bound_of_energies [Fintype (ZMod g)] (P : Finset ι)
    (Q : Finset κ) (clsD : ι → ZMod g) (clsR : κ → ZMod g)
    (α : ι → ℂ) (β : κ → ℂ) (boundA boundB : ℝ)
    (hA : ProductResidueEnergyDH P clsD α boundA)
    (hB : ProductResidueEnergyRS Q clsR β boundB) :
    ‖∑ x : ZMod g, residueAggregate P clsD α x * residueAggregate Q clsR β x‖
      ≤ Real.sqrt boundA * Real.sqrt boundB := by
  have h := productResidue_cauchy (residueAggregate P clsD α) (residueAggregate Q clsR β)
  have hA' : ∑ x : ZMod g, ‖residueAggregate P clsD α x‖ ^ 2 ≤ boundA := hA
  have hB' : ∑ x : ZMod g, ‖residueAggregate Q clsR β x‖ ^ 2 ≤ boundB := hB
  have h1 : Real.sqrt (∑ x : ZMod g, ‖residueAggregate P clsD α x‖ ^ 2)
      ≤ Real.sqrt boundA := Real.sqrt_le_sqrt hA'
  have h2 : Real.sqrt (∑ x : ZMod g, ‖residueAggregate Q clsR β x‖ ^ 2)
      ≤ Real.sqrt boundB := Real.sqrt_le_sqrt hB'
  refine le_trans h ?_
  exact mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-! ## 4. The additive-Fourier form of the congruence -/

variable [NeZero g]

/-- The finite-character indicator: `1_{z=0} = (1/g)∑_a e_g(a z)`. -/
theorem char_indicator (z : ZMod g) :
    ((g : ℂ))⁻¹ * ∑ a : ZMod g, eM g (a * z) = if z = 0 then 1 else 0 := by
  rw [full_char_sum]
  have hg : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne g)
  split_ifs with h
  · field_simp
  · simp

omit [DecidableEq ι] [DecidableEq κ] in
/-- **`productCongruence_additiveFourier`.**  The congruence indicator is the
finite additive-Fourier average, and the product-congruence operator factors
into two independent bilinear Fourier forms. -/
theorem productCongruence_additiveFourier (P : Finset ι) (Q : Finset κ)
    (clsD : ι → ZMod g) (clsR : κ → ZMod g) (α : ι → ℂ) (β : κ → ℂ) :
    ∑ p ∈ P, ∑ q ∈ Q, (if clsD p = clsR q then α p * β q else 0)
      = ((g : ℂ))⁻¹ * ∑ a : ZMod g,
          (∑ p ∈ P, α p * eM g (a * clsD p)) * ∑ q ∈ Q, β q * eM g (-(a * clsR q)) := by
  classical
  have inner : ∀ a : ZMod g,
      (∑ p ∈ P, α p * eM g (a * clsD p)) * (∑ q ∈ Q, β q * eM g (-(a * clsR q)))
        = ∑ p ∈ P, ∑ q ∈ Q, α p * β q * eM g (a * (clsD p - clsR q)) := by
    intro a
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [show a * (clsD p - clsR q) = a * clsD p + -(a * clsR q) by ring, eM_add]
    ring
  have key : ∀ (p : ι) (q : κ),
      ((g : ℂ))⁻¹ * ∑ a : ZMod g, α p * β q * eM g (a * (clsD p - clsR q))
        = if clsD p = clsR q then α p * β q else 0 := by
    intro p q
    rw [← Finset.mul_sum,
      show ((g : ℂ))⁻¹ * (α p * β q * ∑ a : ZMod g, eM g (a * (clsD p - clsR q)))
        = α p * β q * (((g : ℂ))⁻¹ * ∑ a : ZMod g, eM g (a * (clsD p - clsR q))) by ring,
      char_indicator]
    by_cases h : clsD p = clsR q
    · rw [if_pos (sub_eq_zero.mpr h), if_pos h, mul_one]
    · rw [if_neg (sub_ne_zero.mpr h), if_neg h, mul_zero]
  have swap : ∑ a : ZMod g, ∑ p ∈ P, ∑ q ∈ Q,
        α p * β q * eM g (a * (clsD p - clsR q))
      = ∑ p ∈ P, ∑ q ∈ Q, ∑ a : ZMod g,
        α p * β q * eM g (a * (clsD p - clsR q)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_comm
  symm
  rw [Finset.sum_congr rfl fun a _ => inner a, swap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => key p q

end HNEProductResidue
end CurrentProgramme
end TwinPrimeProject
