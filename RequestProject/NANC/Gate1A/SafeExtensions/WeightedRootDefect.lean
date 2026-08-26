/-
# NANC Gate 1A v9.1 — the weighted root-analysis map and its fibre energy

Finite functional analysis only.  For a finite index set `ι` (in the Gate
application `ι = Alpha × Q × HCoord`), a root map `rho : ι → Root` and weights
`beta : ι → ℂ`, the **weighted root analysis** of `f : ι → ℂ` is

    (A f)(z) = ∑_{i : rho i = z} beta i * f i.

The two public theorems are

* `weightedRootAnalysis_of_fibreBound` — if every root fibre carries
  `beta`-square-mass at most `C`, then `∑_z |A f z|² ≤ C · ∑_i |f i|²`;
* `weightedRootFibre_of_residueMass` — for a root map of the shape
  `rho(alpha,q,h) = u(alpha,q) · hcoord(h)` with `u(alpha,q)` a **unit** of
  `ZMod pi`, a residue-mass hypothesis on the `h`-coordinate (uniform in the
  active labels `alpha, q`) upgrades to a root-fibre bound with the *same*
  constant `C/pi`.  Active `alpha`-labels are summed on both sides: no
  "`alpha` is inert" assumption is used anywhere.

The finite Cauchy–Schwarz step reuses the banked
`Gate1B.SafeExtensions.physicalOuterCauchy`; nothing analytic is added.

**FIREWALL.**  `nonunitMultiplier_collapses_rootFibre` shows that if the
multiplier vanishes mod `pi` the whole mass sits in a single fibre, so the
fibre theorems are vacuous there: **nonunit sectors must be excised before
applying `weightedRootFibre_of_residueMass`.**  This file does not claim that
the actual Gate nonunit sector is analytically closed.
-/
import Mathlib
import Gate1B.SafeExtensions.PhysicalSecondMoment

namespace TwinPrimeProject.NANC.Gate1A.V91

open Finset

section RootAnalysis

variable {ι Root : Type*} [Fintype ι] [DecidableEq Root]

/-- The weighted root-analysis map `(A f)(z) = ∑_{rho i = z} beta i * f i`. -/
noncomputable def rootAnalysis (rho : ι → Root) (beta f : ι → ℂ) (z : Root) : ℂ :=
  ∑ i, if rho i = z then beta i * f i else 0

/-- The `beta`-square-mass of the fibre of `rho` over `z`. -/
noncomputable def fibreMass (rho : ι → Root) (beta : ι → ℂ) (z : Root) : ℝ :=
  ∑ i, if rho i = z then ‖beta i‖ ^ 2 else 0

theorem fibreMass_nonneg (rho : ι → Root) (beta : ι → ℂ) (z : Root) :
    0 ≤ fibreMass rho beta z :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Fibrewise Cauchy–Schwarz for the root-analysis map. -/
theorem rootAnalysis_sq_le (rho : ι → Root) (beta f : ι → ℂ) (z : Root) :
    ‖rootAnalysis rho beta f z‖ ^ 2
      ≤ fibreMass rho beta z * ∑ i, (if rho i = z then ‖f i‖ ^ 2 else 0) := by
  classical
  set a : ι → ℂ := fun i => if rho i = z then beta i else 0 with ha
  set S : ι → ℂ := fun i => if rho i = z then f i else 0 with hS
  have hprod : rootAnalysis rho beta f z = ∑ i, a i * S i := by
    unfold rootAnalysis
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha, hS]
    split_ifs <;> simp
  have hA : ∑ i, ‖a i‖ ^ 2 = fibreMass rho beta z := by
    unfold fibreMass
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [ha]
    split_ifs <;> simp
  have hB : ∑ i, ‖S i‖ ^ 2 = ∑ i, (if rho i = z then ‖f i‖ ^ 2 else 0) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hS]
    split_ifs <;> simp
  have := Gate1B.SafeExtensions.physicalOuterCauchy (Finset.univ : Finset ι) a S
  rw [hprod, ← hA, ← hB]
  exact this

/-- **Weighted root analysis, fibre-bounded form.**  If every root fibre carries
`beta`-square-mass at most `C`, the analysis map has energy bound `C`. -/
theorem weightedRootAnalysis_of_fibreBound [Fintype Root] (rho : ι → Root) (beta f : ι → ℂ)
    (C : ℝ) (hC : ∀ z, fibreMass rho beta z ≤ C) :
    ∑ z, ‖rootAnalysis rho beta f z‖ ^ 2 ≤ C * ∑ i, ‖f i‖ ^ 2 := by
  classical
  have hstep : ∀ z : Root, ‖rootAnalysis rho beta f z‖ ^ 2
      ≤ C * ∑ i, (if rho i = z then ‖f i‖ ^ 2 else 0) := by
    intro z
    refine (rootAnalysis_sq_le rho beta f z).trans ?_
    have hnn : (0:ℝ) ≤ ∑ i, (if rho i = z then ‖f i‖ ^ 2 else 0) :=
      Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
    exact mul_le_mul_of_nonneg_right (hC z) hnn
  calc ∑ z, ‖rootAnalysis rho beta f z‖ ^ 2
      ≤ ∑ z : Root, C * ∑ i, (if rho i = z then ‖f i‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun z _ => hstep z
    _ = C * ∑ z : Root, ∑ i, (if rho i = z then ‖f i‖ ^ 2 else 0) := by rw [Finset.mul_sum]
    _ = C * ∑ i, ‖f i‖ ^ 2 := by
        congr 1
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp

/-- **Weighted root analysis, maximal-fibre form.**  The energy constant may be
taken to be the maximum fibre mass. -/
theorem weightedRootAnalysis_energy [Fintype Root] [Nonempty Root] (rho : ι → Root)
    (beta f : ι → ℂ) :
    ∑ z, ‖rootAnalysis rho beta f z‖ ^ 2
      ≤ (Finset.univ.sup' Finset.univ_nonempty (fibreMass rho beta)) * ∑ i, ‖f i‖ ^ 2 :=
  weightedRootAnalysis_of_fibreBound rho beta f _ fun z =>
    Finset.le_sup' (fibreMass rho beta) (Finset.mem_univ z)

end RootAnalysis

/-! ## Root fibres from a residue-mass hypothesis -/

section ResidueMass

variable {pi : ℕ} [NeZero pi] {Alpha Q HCoord : Type*}
variable [Fintype Alpha] [Fintype Q] [Fintype HCoord]

/-- The Gate-shaped root map `rho(alpha,q,h) = u(alpha,q) · hcoord(h)` with a
**unit** multiplier `u(alpha,q)` of `ZMod pi`. -/
def unitRootMap (mult : Alpha → Q → (ZMod pi)ˣ) (hcoord : HCoord → ZMod pi) :
    Alpha × Q × HCoord → ZMod pi :=
  fun x => ((mult x.1 x.2.1 : (ZMod pi)ˣ) : ZMod pi) * hcoord x.2.2

/-- **Root fibre from residue mass.**  If, for every active label pair
`(alpha, q)` and every residue class `c`, the `h`-square-mass of the class is at
most `C/pi` times the total `h`-square-mass, then every root fibre of the unit
root map carries at most `C/pi` of the **total** mass (all labels summed). -/
theorem weightedRootFibre_of_residueMass (mult : Alpha → Q → (ZMod pi)ˣ)
    (hcoord : HCoord → ZMod pi) (beta : Alpha × Q × HCoord → ℂ) (C : ℝ)
    (hres : ∀ (a : Alpha) (q : Q) (c : ZMod pi),
        ∑ h : HCoord, (if hcoord h = c then ‖beta (a, q, h)‖ ^ 2 else 0)
          ≤ C / pi * ∑ h : HCoord, ‖beta (a, q, h)‖ ^ 2)
    (z : ZMod pi) :
    fibreMass (unitRootMap mult hcoord) beta z ≤ C / pi * ∑ x, ‖beta x‖ ^ 2 := by
  classical
  have hcond : ∀ (a : Alpha) (q : Q) (h : HCoord),
      (unitRootMap mult hcoord (a, q, h) = z)
        ↔ (hcoord h = ((mult a q)⁻¹ : (ZMod pi)ˣ) * z) := by
    intro a q h
    unfold unitRootMap
    constructor
    · intro hh
      rw [← hh, ← mul_assoc]
      simp
    · intro hh
      rw [hh, ← mul_assoc]
      simp
  have hexpand : fibreMass (unitRootMap mult hcoord) beta z
      = ∑ a : Alpha, ∑ q : Q,
          ∑ h : HCoord, (if hcoord h = ((mult a q)⁻¹ : (ZMod pi)ˣ) * z
            then ‖beta (a, q, h)‖ ^ 2 else 0) := by
    unfold fibreMass
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : hcoord h = ((mult a q)⁻¹ : (ZMod pi)ˣ) * z
    · rw [if_pos hh, if_pos ((hcond a q h).2 hh)]
    · rw [if_neg hh, if_neg (fun hc => hh ((hcond a q h).1 hc))]
  have htotal : ∑ x : Alpha × Q × HCoord, ‖beta x‖ ^ 2
      = ∑ a : Alpha, ∑ q : Q, ∑ h : HCoord, ‖beta (a, q, h)‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun a _ => by rw [Fintype.sum_prod_type]
  rw [hexpand, htotal, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun q _ => hres a q _

/-- **NONUNIT FIREWALL.**  If the multiplier vanishes modulo `pi`, the root map
is identically `0`, so the single fibre over `0` contains the full unrestricted
mass and a maximal-fibre theorem carries no information.  Nonunit sectors must
be excised before `weightedRootFibre_of_residueMass` is applied. -/
theorem nonunitMultiplier_collapses_rootFibre (mult : Alpha → Q → ZMod pi)
    (hcoord : HCoord → ZMod pi) (beta : Alpha × Q × HCoord → ℂ)
    (h0 : ∀ a q, mult a q = 0) :
    (∀ x : Alpha × Q × HCoord, (fun x => mult x.1 x.2.1 * hcoord x.2.2) x = 0) ∧
      fibreMass (fun x : Alpha × Q × HCoord => mult x.1 x.2.1 * hcoord x.2.2) beta 0
        = ∑ x, ‖beta x‖ ^ 2 := by
  classical
  have hzero : ∀ x : Alpha × Q × HCoord, mult x.1 x.2.1 * hcoord x.2.2 = 0 := by
    intro x; rw [h0]; ring
  refine ⟨hzero, ?_⟩
  unfold fibreMass
  exact Finset.sum_congr rfl fun x _ => by rw [if_pos (hzero x)]

end ResidueMass

end TwinPrimeProject.NANC.Gate1A.V91
