/-
# NANC Gate 1A v9.4 — the projective (outer) collision frame

Two finite, exact blocks.

**A. Outer projective collisions.**  For a state-indexed pair of coordinates
`(Z, L)` the outer defect is

    DeltaOut X Y = Z X * L Y - Z Y * L X,

and a collision modulo `s` happens exactly when `s ∣ DeltaOut X Y`.  The frame
is projective: rescaling each state's coordinate pair by a nonzero factor
multiplies the defect by the product of the factors, hence does not change the
collision set for units.

**B. The axis sums of the projective kernel.**  Over a prime field the kernel

    S(U,V) = ∑_{x ≠ 0} e_s(U x + V x⁻¹)

satisfies exactly

    S(0,0) = s - 1,     S(U,0) = S(0,V) = -1   (U, V ≠ 0),

and the exact correlation identity

    ∑_V S(U,V) · conj S(U',V) = s² · 1_{U = U'} - s.

The correlation identity is an *exact finite orthogonality computation*: no
Weil bound, no Kloosterman estimate and no analytic input of any kind is used
or claimed.
-/
import Mathlib
import RequestProject.NANC.Gate1BDet2.Det2AdditiveReciprocalFrame

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset
open TwinPrimeProject.Gate1BDet2.Recip

/-! ## A. Outer projective collisions -/

section Outer

variable {State : Type*} (Z L : State → ℤ)

/-- The outer projective defect of two states. -/
def deltaOut (X Y : State) : ℤ := Z X * L Y - Z Y * L X

theorem deltaOut_self (X : State) : deltaOut Z L X X = 0 := by
  unfold deltaOut; ring

theorem deltaOut_antisymm (X Y : State) : deltaOut Z L X Y = -deltaOut Z L Y X := by
  unfold deltaOut; ring

/-- **Outer projective collision criterion.** -/
theorem outerProjectiveCollision_iff_dvd_deltaOut (s : ℤ) (X Y : State) :
    Z X * L Y ≡ Z Y * L X [ZMOD s] ↔ s ∣ deltaOut Z L X Y := by
  constructor
  · intro h
    show s ∣ Z X * L Y - Z Y * L X
    exact h.symm.dvd
  · intro h
    exact (Int.modEq_iff_dvd.mpr (by simpa [deltaOut] using h)).symm

/-- **Projective invariance.**  Rescaling each state's coordinate pair
multiplies the defect by the product of the two scalars; hence the collision
set is unchanged whenever the scalars are units. -/
theorem projectiveCollision_unitEquiv (t : State → ℤ) (X Y : State) :
    deltaOut (fun W => t W * Z W) (fun W => t W * L W) X Y
      = t X * t Y * deltaOut Z L X Y := by
  unfold deltaOut; ring

end Outer

/-! ## B. Axis sums and the exact correlation identity -/

section Axis

variable {s : ℕ} [Fact (Nat.Prime s)]

/-- The nonzero residues modulo `s`. -/
def nz (s : ℕ) [NeZero s] : Finset (ZMod s) := univ.erase 0

theorem mem_nz {x : ZMod s} : x ∈ nz s ↔ x ≠ 0 := by
  simp [nz]

/-- The projective kernel `S(U,V) = ∑_{x ≠ 0} e_s(Ux + Vx⁻¹)`. -/
noncomputable def projAxis (U V : ZMod s) : ℂ :=
  ∑ x ∈ nz s, addPhase s (U * x + V * x⁻¹)

/-- Additive orthogonality over the nonzero residues. -/
theorem sum_nz_phase (t : ZMod s) :
    ∑ x ∈ nz s, addPhase s (t * x) = if t = 0 then (s : ℂ) - 1 else -1 := by
  have h : ∑ x : ZMod s, addPhase s (t * x) = if t = 0 then (s : ℂ) else 0 := by
    simpa [mul_comm] using sum_addPhase_mul (q := s) t
  rw [nz, Finset.sum_erase_eq_sub (mem_univ 0), h, mul_zero, addPhase_zero]
  split_ifs <;> ring

/-- Inversion is an involution of the nonzero residues, so it may be used to
reindex. -/
theorem sum_nz_inv (f : ZMod s → ℂ) : ∑ x ∈ nz s, f x⁻¹ = ∑ x ∈ nz s, f x := by
  refine Finset.sum_nbij' (i := fun x : ZMod s => x⁻¹) (j := fun x : ZMod s => x⁻¹)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha; simpa [mem_nz] using (mem_nz.mp ha)
  · intro a ha; simpa [mem_nz] using (mem_nz.mp ha)
  · intro a _; exact inv_inv a
  · intro a _; exact inv_inv a
  · intro _ _; rfl

theorem projAxis_zero_zero : projAxis (0 : ZMod s) 0 = (s : ℂ) - 1 := by
  have := sum_nz_phase (s := s) 0
  simpa [projAxis] using this

theorem projAxis_axis_U {U : ZMod s} (hU : U ≠ 0) : projAxis U 0 = -1 := by
  have := sum_nz_phase (s := s) U
  simpa [projAxis, hU] using this

theorem projAxis_axis_V {V : ZMod s} (hV : V ≠ 0) : projAxis (0 : ZMod s) V = -1 := by
  have h : projAxis (0 : ZMod s) V = ∑ x ∈ nz s, addPhase s (V * x) := by
    rw [projAxis]
    have := sum_nz_inv (s := s) (fun x => addPhase s (V * x))
    simpa using this
  rw [h, sum_nz_phase, if_neg hV]

/-- The `V`-sum of a single phase. -/
theorem sum_V_phase (a t : ZMod s) :
    ∑ V : ZMod s, addPhase s (a + V * t) = addPhase s a * (if t = 0 then (s : ℂ) else 0) := by
  simp_rw [addPhase_add]
  rw [← Finset.mul_sum]
  congr 1
  simpa using sum_addPhase_mul (q := s) t

theorem conj_addPhase (z : ZMod s) : (starRingEnd ℂ) (addPhase s z) = addPhase s (-z) :=
  (AddChar.map_neg_eq_conj _ z).symm

theorem addPhase_sub (a b : ZMod s) :
    addPhase s a * addPhase s (-b) = addPhase s (a - b) := by
  rw [← addPhase_add, ← sub_eq_add_neg]

/-- **Exact correlation identity for the projective kernel.** -/
theorem projAxis_correlation (U U' : ZMod s) :
    ∑ V : ZMod s, projAxis U V * (starRingEnd ℂ) (projAxis U' V)
      = (s : ℂ) ^ 2 * (if U = U' then 1 else 0) - s := by
  have key : ∀ V : ZMod s, projAxis U V * (starRingEnd ℂ) (projAxis U' V)
      = ∑ x ∈ nz s, ∑ y ∈ nz s, addPhase s ((U * x - U' * y) + V * (x⁻¹ - y⁻¹)) := by
    intro V
    rw [projAxis, projAxis, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [conj_addPhase, addPhase_sub]
    congr 1
    ring
  have step1 : ∑ V : ZMod s, projAxis U V * (starRingEnd ℂ) (projAxis U' V)
      = ∑ x ∈ nz s, ∑ y ∈ nz s, ∑ V : ZMod s,
          addPhase s ((U * x - U' * y) + V * (x⁻¹ - y⁻¹)) := by
    rw [Finset.sum_congr rfl fun V _ => key V, Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have step2 : ∀ x ∈ nz s, ∀ y ∈ nz s,
      (∑ V : ZMod s, addPhase s ((U * x - U' * y) + V * (x⁻¹ - y⁻¹)))
        = addPhase s (U * x - U' * y) * (if x = y then (s : ℂ) else 0) := by
    intro x hx y hy
    rw [sum_V_phase]
    congr 1
    have hxy : (x⁻¹ - y⁻¹ = 0) ↔ (x = y) := by
      constructor
      · intro h
        have : x⁻¹ = y⁻¹ := by linear_combination h
        have := congrArg (fun z : ZMod s => z⁻¹) this
        simpa [inv_inv] using this
      · intro h; simp [h]
    by_cases h : x = y
    · simp [h]
    · rw [if_neg (fun hc => h (hxy.mp hc)), if_neg h]
  rw [step1, Finset.sum_congr rfl fun x hx =>
    Finset.sum_congr rfl fun y hy => step2 x hx y hy]
  have step3 : ∀ x ∈ nz s,
      (∑ y ∈ nz s, addPhase s (U * x - U' * y) * (if x = y then (s : ℂ) else 0))
        = addPhase s ((U - U') * x) * s := by
    intro x hx
    rw [Finset.sum_eq_single x]
    · rw [if_pos rfl]
      have hUx : U * x - U' * x = (U - U') * x := by ring
      rw [hUx]
    · intro y _ hy
      rw [if_neg (fun hc => hy hc.symm), mul_zero]
    · intro hx'; exact absurd hx hx'
  rw [Finset.sum_congr rfl step3, ← Finset.sum_mul, sum_nz_phase]
  by_cases h : U = U'
  · rw [if_pos h, if_pos (by simp [h] : U - U' = (0 : ZMod s))]
    ring
  · have hne : U - U' ≠ 0 := sub_ne_zero.mpr h
    rw [if_neg h, if_neg hne]
    ring

end Axis

end TwinPrimeProject.NANC.Gate1A.V94
