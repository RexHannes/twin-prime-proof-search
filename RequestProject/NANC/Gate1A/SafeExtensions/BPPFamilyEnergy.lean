/-
# NANC Gate 1A v9.3/v9.4 — the finite BPP compiler

**The main new finite theorem of the BPP route.**  With

    a(r,X) ≥ 0,    A_X  a magnitude with  P · A_X ≤ ∑_r a(r,X),
    S = #rows,     T_abs = ∑_r (∑_X a(r,X))²,

finite Cauchy–Schwarz gives

    (∑_X A_X)²  ≤  (S / P²) · T_abs.                (`envelopeMass_le_of_participation`)

Combined with a pair-codegree certificate `E_off ≤ D · (∑_X A_X)²` this yields

    E_off  ≤  (D · S / P²) · T_abs.                 (`familyEnergy_of_participation`)

The **asymptotic substitution** `D = X^{o(1)}, S = R^{1+o(1)}, P = R^{3/4-o(1)}`,
which turns `D·S/P²` into `R^{-1/2+o(1)}`, is *documentation only*: it appears in
no theorem, is not an axiom, and the exponent bookkeeping is done separately in
exact rational arithmetic (`BPPBudget`).

**RETRACTED.**  The direct implication "few divisors of `Delta_out`" ⟹
`R^{-1}` weighted family energy is *not* used here and is not a closure step;
see `V94Retractions`.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.PrimeParticipationFinite

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

variable {Row State : Type*} [Fintype Row] [Fintype State]

/-- The row-summed source mass. -/
def rowMass (a : Row → State → ℝ) (r : Row) : ℝ := ∑ X, a r X

/-- The absolute family energy `T_abs = ∑_r (∑_X a(r,X))²`. -/
def totalAbsEnergy (a : Row → State → ℝ) : ℝ := ∑ r, (rowMass a r) ^ 2

/-- **Finite BPP compiler, envelope form.**  Participation converts the
envelope mass into the absolute family energy with the factor `S/P²`. -/
theorem envelopeMass_le_of_participation (a : Row → State → ℝ) (A : State → ℝ) (P : ℝ)
    (hP : 0 < P) (ha : ∀ r X, 0 ≤ a r X) (hA : ∀ X, 0 ≤ A X)
    (hpart : ∀ X, P * A X ≤ ∑ r, a r X) :
    (∑ X, A X) ^ 2 ≤ ((Fintype.card Row : ℝ) / P ^ 2) * totalAbsEnergy a := by
  classical
  have hstep : P * ∑ X, A X ≤ ∑ r, rowMass a r := by
    calc P * ∑ X, A X = ∑ X, P * A X := by rw [Finset.mul_sum]
      _ ≤ ∑ X, ∑ r, a r X := Finset.sum_le_sum fun X _ => hpart X
      _ = ∑ r, rowMass a r := by unfold rowMass; rw [Finset.sum_comm]
  have hnn : 0 ≤ P * ∑ X, A X :=
    mul_nonneg (le_of_lt hP) (Finset.sum_nonneg fun X _ => hA X)
  have hsq : (P * ∑ X, A X) ^ 2 ≤ (∑ r, rowMass a r) ^ 2 :=
    pow_le_pow_left₀ hnn hstep 2
  have hcauchy : (∑ r, rowMass a r) ^ 2
      ≤ (Fintype.card Row : ℝ) * totalAbsEnergy a := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Row)) (f := rowMass a)
    simpa [totalAbsEnergy, Finset.card_univ] using this
  have hchain : P ^ 2 * (∑ X, A X) ^ 2 ≤ (Fintype.card Row : ℝ) * totalAbsEnergy a := by
    calc P ^ 2 * (∑ X, A X) ^ 2 = (P * ∑ X, A X) ^ 2 := by ring
      _ ≤ (∑ r, rowMass a r) ^ 2 := hsq
      _ ≤ (Fintype.card Row : ℝ) * totalAbsEnergy a := hcauchy
  have hP2 : (0 : ℝ) < P ^ 2 := by positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hP2]
  calc (∑ X, A X) ^ 2 * P ^ 2 = P ^ 2 * (∑ X, A X) ^ 2 := by ring
    _ ≤ (Fintype.card Row : ℝ) * totalAbsEnergy a := hchain

/-- **Finite BPP compiler, family-energy form.**  A pair-codegree certificate
`E_off ≤ D · (∑_X A_X)²` plus participation gives the controlling family-energy
inequality `E_off ≤ (D·S/P²)·T_abs`. -/
theorem familyEnergy_of_participation (a : Row → State → ℝ) (A : State → ℝ)
    (P D Eoff : ℝ) (hP : 0 < P) (hD : 0 ≤ D)
    (ha : ∀ r X, 0 ≤ a r X) (hA : ∀ X, 0 ≤ A X)
    (hpart : ∀ X, P * A X ≤ ∑ r, a r X)
    (hcodeg : Eoff ≤ D * (∑ X, A X) ^ 2) :
    Eoff ≤ (D * (Fintype.card Row : ℝ) / P ^ 2) * totalAbsEnergy a := by
  refine hcodeg.trans ?_
  have h := envelopeMass_le_of_participation a A P hP ha hA hpart
  calc D * (∑ X, A X) ^ 2
      ≤ D * (((Fintype.card Row : ℝ) / P ^ 2) * totalAbsEnergy a) :=
        mul_le_mul_of_nonneg_left h hD
    _ = (D * (Fintype.card Row : ℝ) / P ^ 2) * totalAbsEnergy a := by ring

/-- The compiler applied to a `PrimeParticipationCertificate`. -/
theorem PrimeParticipationCertificate.familyEnergy
    (C : PrimeParticipationCertificate Row State) (D Eoff : ℝ) (hD : 0 ≤ D)
    (hcodeg : Eoff ≤ D * (∑ X, C.A X) ^ 2) :
    Eoff ≤ (D * (Fintype.card Row : ℝ) / C.P ^ 2) * totalAbsEnergy C.a :=
  familyEnergy_of_participation C.a C.A C.P D Eoff C.P_pos hD C.a_nonneg C.A_nonneg
    C.participation_mass hcodeg

end TwinPrimeProject.NANC.Gate1A.V94
