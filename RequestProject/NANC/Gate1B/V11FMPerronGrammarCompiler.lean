import RequestProject.NANC.Gate1B.V11FMSieveGenTypeII

/-!
# V11 · Gate 1B — the proof-specific grammar compiler

A **deterministic** compiler: from

* a finite family of supplied generated packets,
* the generated Type-II bound for each packet,
* a supplied total (polylogarithmic) coefficient cost,

it produces the corresponding bound for the assembled family, with the shifted
log exponent computed explicitly.

Nothing here states that Ford–Maynard's Proposition 7.22 has been proved.  The
per-packet bounds are hypotheses.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

variable {N : ℕ}

/-- **A proof-generated packet.**  The packet carries its own FM-SieveGen
configuration, a generated certificate for each factor slot, the selected subset
(inside `data`), the range data (inside `data`), a coefficient cost and a
multiplicity. -/
structure FMProofGeneratedPacket (N : ℕ) where
  /-- The FM-SieveGen configuration of the packet. -/
  data : FMSieveGenData N
  /-- The generated expression realising each factor slot. -/
  factorWitness : Fin N → GenExpr
  /-- Each witness is admissible. -/
  factorAdmissible : ∀ j, (factorWitness j).Admissible
  /-- The coefficient cost of the packet. -/
  coefficientCost : ℝ
  /-- The multiplicity with which the packet occurs. -/
  packetMultiplicity : ℂ

/-- The factor functions of a packet. -/
noncomputable def FMProofGeneratedPacket.factorFun (P : FMProofGeneratedPacket N)
    (j : Fin N) : ℕ → ℂ := semExpr (P.factorWitness j)

/-- The factor functions of a packet are generated. -/
theorem FMProofGeneratedPacket.factorFun_generated (P : FMProofGeneratedPacket N) (j : Fin N) :
    FMPerronGenerated (P.factorFun j) :=
  ⟨P.factorWitness j, P.factorAdmissible j, fun _ => rfl⟩

/-- **A finite family of supplied generated packets.** -/
structure GeneratedPacketFamily (N : ℕ) (ι : Type) [Fintype ι] where
  /-- The packets. -/
  packet : ι → FMProofGeneratedPacket N
  /-- The supplied total coefficient cost. -/
  totalCost : ℝ
  /-- The total cost dominates the ℓ¹ mass of the multiplicities. -/
  totalCost_spec : ∑ i, ‖(packet i).packetMultiplicity‖ ≤ totalCost
  /-- A uniform per-packet target. -/
  packetTarget : ℝ
  /-- The per-packet target is nonnegative. -/
  packetTarget_nonneg : 0 ≤ packetTarget
  /-- Each packet's own target respects the uniform one. -/
  packetTarget_spec : ∀ i, (packet i).data.target ≤ packetTarget

/-- The assembled value of the family at a supplied tuple of factor functions. -/
noncomputable def familyValue {ι : Type} [Fintype ι] (F : GeneratedPacketFamily N ι)
    (x : Fin N → ℕ → ℂ) : ℂ :=
  ∑ i, (F.packet i).packetMultiplicity * sieveGenValue (F.packet i).data x

/-- **THE DETERMINISTIC GRAMMAR COMPILER.**

If every supplied generated packet satisfies its `FMPerronGeneratedTypeIIAtScale`
bound, then the assembled family satisfies the product bound
`totalCost · packetTarget`, for every generated 1-bounded tuple of factor
functions.

This is a finite triangle inequality; the per-packet bounds are the analytic
input and are hypotheses. -/
theorem generatedPacketFamily_bound {ι : Type} [Fintype ι] (F : GeneratedPacketFamily N ι)
    (hpk : ∀ i, FMPerronGeneratedTypeIIAtScale (F.packet i).data)
    (x : Fin N → ℕ → ℂ) (hx : ∀ j, FMPerronGeneratedUnit (x j)) :
    ‖familyValue F x‖ ≤ F.totalCost * F.packetTarget := by
  have hb : ∀ i ∈ (Finset.univ : Finset ι),
      ‖sieveGenValue (F.packet i).data x‖ ≤ F.packetTarget := by
    intro i _
    exact le_trans (hpk i x hx) (F.packetTarget_spec i)
  refine le_trans (norm_finiteSum_le_l1Cost Finset.univ _ _ F.packetTarget hb) ?_
  exact mul_le_mul_of_nonneg_right F.totalCost_spec F.packetTarget_nonneg

/-- **The shifted log exponent, computed.**  A polylogarithmic total cost
`L^C` against a per-packet target `X·L^(−A)` gives `X·L^(C−A)`. -/
theorem shifted_log_budget (X L C A totalCost packetTarget : ℝ)
    (hL : 0 < L) (htarget : 0 ≤ packetTarget)
    (h1 : totalCost ≤ L ^ C) (h2 : packetTarget ≤ X * L ^ (-A)) :
    totalCost * packetTarget ≤ X * L ^ (C - A) := by
  have hLC : (0 : ℝ) ≤ L ^ C := le_of_lt (Real.rpow_pos_of_pos hL C)
  have hstep : totalCost * packetTarget ≤ L ^ C * (X * L ^ (-A)) := by
    exact mul_le_mul h1 h2 htarget hLC
  refine hstep.trans_eq ?_
  rw [Real.rpow_sub hL, Real.rpow_neg (le_of_lt hL)]
  field_simp

/-- The compiler with the log budget substituted. -/
theorem generatedPacketFamily_logBudget {ι : Type} [Fintype ι] (F : GeneratedPacketFamily N ι)
    (hpk : ∀ i, FMPerronGeneratedTypeIIAtScale (F.packet i).data)
    (x : Fin N → ℕ → ℂ) (hx : ∀ j, FMPerronGeneratedUnit (x j))
    (X L C A : ℝ) (hL : 0 < L)
    (h1 : F.totalCost ≤ L ^ C) (h2 : F.packetTarget ≤ X * L ^ (-A)) :
    ‖familyValue F x‖ ≤ X * L ^ (C - A) :=
  le_trans (generatedPacketFamily_bound F hpk x hx)
    (shifted_log_budget X L C A F.totalCost F.packetTarget hL
      F.packetTarget_nonneg h1 h2)

/-! ### Guard -/

/-- **Guard.**  The compiler is not a proof of anything unconditional: with the
toy configuration the per-packet hypothesis is false, so the hypothesis list is
load-bearing. -/
theorem compiler_hypotheses_are_load_bearing :
    ¬ FMPerronGeneratedTypeIIAtScale toyData :=
  fmPerronGeneratedTypeII_toy_fails

end Gate1BV11
end TwinPrimeProject
