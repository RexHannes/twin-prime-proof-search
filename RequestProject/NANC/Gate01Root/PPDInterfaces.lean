import RequestProject.NANC.Gate01Root.RepeatedP

/-!
# Gate01Root: PPD and the open analytic interfaces

## Finite content (proved)

* `PPD B T` : the hypothesis `∑_{p₁ ≠ p₂} |G(p₁,p₂)|² ≤ T`;
* `ppd_and_repeatedP_imply_r4c` : `PPD B T` together with `∑_p |G(p,p)|² ≤ U`
  gives `fourthMoment B ≤ T + U` — an exact consequence of the dual split;
* `ppd_and_repeatedP_imply_R4CBound` : the normalised corollary in which the
  repeated-`p` budget is absorbed into the R4C target.

## Open analytic interfaces (definitions only, never inhabited)

`HitPStatement`, `HitStatement`, `BPointStatement`, `BRowStatement`,
`R4CAnalyticStatement`, `PPDAnalyticStatement`, `Gate0CoverageStatement`.

No inhabitant of any of these is constructed anywhere in this development, and
nothing below assumes one.
-/

namespace RouteAFibreFrame
namespace Gate01Root

open Finset

variable {E P : Type*} [Fintype E] [Fintype P]

/-- **PPD hypothesis**: `∑_{p₁ ≠ p₂} |G(p₁,p₂)|² ≤ T`. -/
def PPD (B : E → P → ℂ) [DecidableEq P] (T : ℝ) : Prop := offDiagColSum B ≤ T

/-- **PPD + repeated-`p` ⇒ R4C fourth moment.**  Exact finite consequence of the
column/row duality split. -/
theorem ppd_and_repeatedP_imply_r4c [DecidableEq P] {B : E → P → ℂ} {T U : ℝ}
    (hppd : PPD B T) (hdiag : diagColSum B ≤ U) : fourthMoment B ≤ T + U :=
  Gate04Root.ppd_and_repeatedP_imply_r4c hppd hdiag

/-- Normalised corollary: if the off-diagonal target and the repeated-`p` budget
together fit under `S²`, the R4C bound holds at scale `S`. -/
theorem ppd_and_repeatedP_imply_R4CBound [DecidableEq P] {B : E → P → ℂ}
    {T U S : ℝ} (hppd : PPD B T) (hdiag : diagColSum B ≤ U) (hfit : T + U ≤ S ^ 2) :
    R4CBound B S :=
  Gate04Root.ppd_and_repeatedP_imply_R4CBound hppd hdiag hfit

/-- Power-saving form: if the repeated-`p` budget carries a factor `δ ≤ 1` of the
R4C target and PPD supplies the rest, the R4C bound follows. -/
theorem ppd_absorbs_repeatedP [DecidableEq P] {B : E → P → ℂ} {S delta : ℝ}
    (hppd : PPD B ((1 - delta) * S ^ 2)) (hdiag : diagColSum B ≤ delta * S ^ 2) :
    R4CBound B S :=
  Gate04Root.ppd_and_repeatedP_imply_R4CBound hppd hdiag (by ring_nf; exact le_of_eq (by ring))

/-! ## Open analytic interfaces.  Definitions only — never inhabited. -/

/-- **HIT-p (OPEN ANALYTIC INPUT).**  `Z_{e,p}(λ) ≪ λ L`. -/
def HitPStatement (Z : E → P → ℝ → ℝ) (L C : ℝ) : Prop :=
  ∀ e p lam, 0 ≤ lam → Z e p lam ≤ C * lam * L

/-- **HIT (OPEN ANALYTIC INPUT).**  `Z_e(λ) ≪ λ L²`. -/
def HitStatement (Z : E → ℝ → ℝ) (L C : ℝ) : Prop :=
  ∀ e lam, 0 ≤ lam → Z e lam ≤ C * lam * L ^ 2

/-- **B-POINT (CONDITIONAL ON HIT-p + KERNEL DECAY).**  `|B_d(e,p)| ≪ L/H`. -/
def BPointStatement (B : E → P → ℂ) (L H C : ℝ) : Prop :=
  ∀ e p, ‖B e p‖ ≤ C * L / H

/-- **B-ROW (CONDITIONAL ON B-POINT).**  `∑_p |B_d(e,p)|² ≪ L³/H²`. -/
def BRowStatement (B : E → P → ℂ) (L H C : ℝ) : Prop :=
  ∀ e, ∑ p, ‖B e p‖ ^ 2 ≤ C * L ^ 3 / H ^ 2

/-- **R4C (OPEN ANALYTIC INPUT).**  `FourthMoment(B_d) ≪ (M D L)²`. -/
def R4CAnalyticStatement (B : E → P → ℂ) (M D L C : ℝ) : Prop :=
  fourthMoment B ≤ C * (M * D * L) ^ 2

/-- **PPD (FIRST OPEN ANALYTIC INPUT).**  `∑_{p₁ ≠ p₂} |G_d(p₁,p₂)|² ≪ (M D L)²`. -/
def PPDAnalyticStatement (B : E → P → ℂ) [DecidableEq P] (M D L C : ℝ) : Prop :=
  offDiagColSum B ≤ C * (M * D * L) ^ 2

/-- **G0-COVER (OPEN SOURCE INPUT).**  Exhaustive weighted clean-edge coverage:
every target weight is exactly the sum of the clean-edge weights above it. -/
def Gate0CoverageStatement {N : Type*} (target : N → ℝ) (edgeWeight : E → N → ℝ) : Prop :=
  ∀ n, target n = ∑ e, edgeWeight e n

/-- The finite bridge from the analytic PPD statement to the finite `PPD`
predicate.  (This is a restatement, not a proof of PPD.) -/
theorem ppdAnalytic_gives_PPD [DecidableEq P] {B : E → P → ℂ} {M D L C : ℝ}
    (h : PPDAnalyticStatement B M D L C) : PPD B (C * (M * D * L) ^ 2) := h

end Gate01Root
end RouteAFibreFrame
