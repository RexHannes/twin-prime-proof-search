/-
# Gate 1B v8.5 — the H7 joint prime packet (finite form)

**Status: PROVED_FINITE (definition + exact finite identities; no bound asserted).**

Abstract finite data:

* a dyadic family of primes `p`, indexed by a finite type;
* for each `p`, a finite family of multiplicative characters `chi mod p`, with a
  distinguished principal character `chi0 p`;
* a defect transform `D p chi` and a long-source transform `B p chi`.

The packet is

    T(P) = ∑_p logWeight p / (p - 1) * ∑_{chi ≠ chi0 p} conj (chi(2)) * D p chi * B p chi.

**No estimate is asserted here.**  Only the definition and exact rearrangement
identities are banked; every bound lives in the compilers, with its analytic
inputs explicit.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- Abstract finite data for the H7 joint prime packet.

`Pi` indexes the dyadic prime family and `Ch` indexes, for each prime, the
character family mod `p`.  Every arithmetic input (`logWeight`, `pMinusOne`,
`chiAt2`, `defect`, `long`) is data: nothing is asserted to be small. -/
structure H7JointPrimeData (Pi : Type*) [Fintype Pi] [DecidableEq Pi]
    (Ch : Type*) [Fintype Ch] [DecidableEq Ch] where
  /-- `logWeight p`, e.g. `log p` on the dyadic family. -/
  logWeight : Pi → ℝ
  /-- `p - 1`, the size of the character group mod `p`. -/
  pMinusOne : Pi → ℝ
  /-- Positivity of `p - 1`. -/
  pMinusOne_pos : ∀ p, 0 < pMinusOne p
  /-- The index of the principal character mod `p`. -/
  chi0 : Pi → Ch
  /-- The value `chi(2)` of the character. -/
  chiAt2 : Pi → Ch → ℂ
  /-- The defect transform `D_p(chi)`. -/
  defect : Pi → Ch → ℂ
  /-- The long-source transform `B_p(chi)`. -/
  long : Pi → Ch → ℂ

namespace H7JointPrimeData

variable {Pi : Type*} [Fintype Pi] [DecidableEq Pi]
variable {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
variable (data : H7JointPrimeData Pi Ch)

/-- The per-prime weight `logWeight p / (p - 1)`. -/
noncomputable def weight (p : Pi) : ℝ := data.logWeight p / data.pMinusOne p

/-- The nonprincipal character set mod `p`. -/
def nonprincipal (p : Pi) : Finset Ch := univ.erase (data.chi0 p)

/-- The dual coefficient `conj (chi(2)) * D_p(chi)` attached to `(p, chi)`. -/
noncomputable def dualCoeff (p : Pi) (c : Ch) : ℂ :=
  (starRingEnd ℂ) (data.chiAt2 p c) * data.defect p c

/-- The per-prime inner packet `∑_{chi ≠ chi0} conj(chi(2)) D_p(chi) B_p(chi)`. -/
noncomputable def innerPacket (p : Pi) : ℂ :=
  ∑ c ∈ data.nonprincipal p, data.dualCoeff p c * data.long p c

/-- **The joint prime packet `T(P)`.**  No bound is asserted. -/
noncomputable def h7JointPrimePacket : ℂ :=
  ∑ p : Pi, (data.weight p : ℂ) * data.innerPacket p

/-- The principal character is excluded from every inner packet. -/
theorem chi0_not_mem_nonprincipal (p : Pi) : data.chi0 p ∉ data.nonprincipal p := by
  simp [nonprincipal]

/-- Exact expansion of the packet as a double sum over `(p, chi)`. -/
theorem h7JointPrimePacket_eq_double_sum :
    data.h7JointPrimePacket =
      ∑ p : Pi, ∑ c ∈ data.nonprincipal p,
        (data.weight p : ℂ) * (data.dualCoeff p c * data.long p c) := by
  unfold h7JointPrimePacket innerPacket
  exact Finset.sum_congr rfl fun p _ => Finset.mul_sum _ _ _

/-- Triangle inequality for the packet (exact, no analytic input). -/
theorem h7JointPrimePacket_norm_le :
    ‖data.h7JointPrimePacket‖ ≤ ∑ p : Pi, |data.weight p| * ‖data.innerPacket p‖ := by
  refine (norm_sum_le _ _).trans_eq ?_
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]

/-- The weight is *not* hidden: `logWeight p / (p - 1)` is compared with the
uniform `logWeight p / P` through `1/(p-1) ≤ 2/p` on the dyadic range `p ≥ 2`. -/
theorem one_div_pred_le_two_div {p : ℝ} (hp : 2 ≤ p) : 1 / (p - 1) ≤ 2 / p := by
  have h1 : (0:ℝ) < p - 1 := by linarith
  have h2 : (0:ℝ) < p := by linarith
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

end H7JointPrimeData

end Gate1B.SafeAlgebra
