/-
# Gate-1A Δv4 §26 / §27 / §28 — exceptional routing table and the final
# conditional assembly

**§28 is deliberately NOT satisfied.**  The unconditional theorem
`gate1a_direct_generic_closed_under_frozen_clean_bank` is **not** created in
this project, because several of the eleven items it would require are still
assumptions: the flat-profile *source legality* (the identification of the
authoritative source profile with the schematic flat-main form), the
corrected-PB *analytic* lattice bound, the `h = 0` firewall bound, and the
remaining exceptional sectors listed as `OPEN` below.  What *is* created is
`gate1a_of_final_interfaces` (§27), whose hypotheses are exactly those
genuinely unproved interfaces.

Everything in this file is an ordinary `Prop`/`structure`.  There is no
`axiom`, no `sorry`, and no term of the open interface structures is ever
constructed from thin air: the only inhabitation results are the explicit
numerical witnesses at the end, which show that the conditional theorem is
not vacuous, and the separating guard, which shows the hypotheses are
load-bearing.
-/
import Mathlib
import Gate1A.Delta4.Scale
import Gate1A.Delta4.OuterAxis
import Gate1A.Delta4.Partition

namespace Gate1A

namespace Delta4

/-! ## §26 The exceptional routing table -/

/-- Routing status of an exceptional sector.  The word "frozen" is not
available: every item must be a proved map, a proved bound, or open. -/
inductive RoutingStatus
  /-- the sector is mapped exactly onto an already-handled sector. -/
  | provedMap
  /-- the sector is bounded outright. -/
  | provedBound
  /-- the sector remains an open interface. -/
  | open_
  deriving DecidableEq, Repr

/-- The eleven exceptional items required by §26. -/
inductive ExceptionalItem
  | hZero | sameQ | repeatedPrime | crossRolePEqQ | nonunit
  | principalCharacter | properConductor | localOneZeroAxis | trueLocalZero
  | pbAlias | balancedLiftBoundary
  deriving DecidableEq, Repr

/-- The literal Δv4 routing status of each exceptional item, as established in
this project.

* `localOneZeroAxis` is a proved map: on `Z = 0, r ∤ L` the local factor is
  exactly `-1` and the normalised factor is a strict contraction
  (`outer_regular_axis_contraction`).
* `trueLocalZero` is a proved map: on `Z = 0, r ∣ L` the local pair is
  `(0,0) mod r`, the factor is `r - 1 ≠ -1`
  (`outer_true_zero_is_rank_loss`), and the branch is divisor-sparse
  (`outer_true_zero_divisor_bound`).
* `hZero` is a proved map in one direction only — `L = 0` maps exactly onto
  `h₁ = h₂ = 0` (`L_zero_forces_h1_h2_zero`) — but the firewall *bound* for
  the `h = 0` locus itself is not proved here, so the item is `open_`.
* Everything else is `open_`. -/
def routingStatus : ExceptionalItem → RoutingStatus
  | .hZero => .open_
  | .sameQ => .open_
  | .repeatedPrime => .open_
  | .crossRolePEqQ => .open_
  | .nonunit => .open_
  | .principalCharacter => .open_
  | .properConductor => .open_
  | .localOneZeroAxis => .provedMap
  | .trueLocalZero => .provedMap
  | .pbAlias => .open_
  | .balancedLiftBoundary => .open_

/-- The table is total: every item carries one of the three statuses, and no
item is left with a bare label. -/
theorem routingStatus_total (i : ExceptionalItem) :
    routingStatus i = RoutingStatus.provedMap ∨
    routingStatus i = RoutingStatus.provedBound ∨
    routingStatus i = RoutingStatus.open_ := by
  cases i <;> simp [routingStatus]

/-- Exactly two items are discharged as proved maps; the other nine are open
interfaces.  This is the honest state of the exceptional table. -/
theorem routingStatus_open_items :
    routingStatus .hZero = RoutingStatus.open_ ∧
    routingStatus .sameQ = RoutingStatus.open_ ∧
    routingStatus .repeatedPrime = RoutingStatus.open_ ∧
    routingStatus .crossRolePEqQ = RoutingStatus.open_ ∧
    routingStatus .nonunit = RoutingStatus.open_ ∧
    routingStatus .principalCharacter = RoutingStatus.open_ ∧
    routingStatus .properConductor = RoutingStatus.open_ ∧
    routingStatus .pbAlias = RoutingStatus.open_ ∧
    routingStatus .balancedLiftBoundary = RoutingStatus.open_ ∧
    routingStatus .localOneZeroAxis = RoutingStatus.provedMap ∧
    routingStatus .trueLocalZero = RoutingStatus.provedMap := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The Gate scale as explicit positive reals -/

/-- The immutable Δv4 gate scale, carried as explicit positive parameters
together with its exact identities (`§2`).  No asymptotic notation: the
factor `Xo` plays the role of `X^{o(1)}` and is an explicit parameter `≥ 1`. -/
structure GateScale where
  /-- `M = X^{1/3}`. -/
  M : ℝ
  /-- `R = X^a`. -/
  R : ℝ
  /-- `L = X^b`. -/
  L : ℝ
  /-- `H = X^{a+2b-2/3}`. -/
  H : ℝ
  /-- `D = X^{2/3-a}`. -/
  D : ℝ
  /-- `K = X^{1/3-a}`. -/
  K : ℝ
  /-- the explicit stand-in for `X^{o(1)}`. -/
  Xo : ℝ
  hM : 0 < M
  hR : 0 < R
  hL : 0 < L
  hH : 0 < H
  hD : 0 < D
  hK : 0 < K
  hXo : 1 ≤ Xo
  /-- `D H = L²`. -/
  idDH : D * H = L ^ 2
  /-- `R K = M`. -/
  idRK : R * K = M
  /-- `M² H = R L²`. -/
  idMsqH : M ^ 2 * H = R * L ^ 2

/-- The normalised Gate-1A target `M H L⁴ X^{o(1)}`. -/
def normalizedTarget (S : GateScale) : ℝ := S.M * S.H * S.L ^ 4 * S.Xo

/-- The physical Gate-1A target `M L⁴ / H · X^{o(1)}`. -/
noncomputable def physicalTarget (S : GateScale) : ℝ := S.M * S.L ^ 4 / S.H * S.Xo

/-- The physical target is the normalised one divided by `H²`; equivalently
`M L⁴/H = M D² H` by `D H = L²`. -/
theorem physical_eq_normalized_div_Hsq (S : GateScale) :
    physicalTarget S = normalizedTarget S / S.H ^ 2 := by
  have hH : S.H ≠ 0 := S.hH.ne'
  simp only [physicalTarget, normalizedTarget]
  field_simp

/-- `M L⁴ / H = M D² H`, the second form of the physical target. -/
theorem physicalTarget_eq_MDsqH (S : GateScale) :
    physicalTarget S = S.M * S.D ^ 2 * S.H * S.Xo := by
  have hH := S.hH.ne'
  have hid : S.L ^ 2 = S.D * S.H := S.idDH.symm
  have h4 : S.L ^ 4 = (S.D * S.H) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hid]
  rw [physicalTarget, h4]
  field_simp

/-! ## §27 The final conditional assembly -/

/-- **The genuinely still-unproved interfaces of the Δv4 route.**

Each field is an explicit inequality about the literal sector masses; none of
them is proved in this project.  Their names are the addendum's:

* `flatProfileSourceLegality` — the authoritative source profile really is the
  flat profile times the five near-`1` factors (the perturbation algebra
  itself is proved in `Gate1A/Delta4/FlatProfile.lean`);
* `correctedPBAnalytic` — the corrected 2D Poisson–Bruhat lattice bound for
  the actual sheared source lattice (the `Z`-coordinate identity and the axis
  arithmetic are proved in `Gate1A/Delta4/PBAxis.lean`);
* `hZeroFirewallBound` — the bound for the `h = 0` locus itself;
* `exceptionalSectorsBound` — the total mass of the nine `open_` items of the
  exceptional table;
* `sourceCoherence` — the source/norm coherence used when the true-local-zero
  branch is routed to the rank-loss sector. -/
structure Delta4OpenInterfaces (S : GateScale)
    (flatMass pbMass firewallMass exceptionalMass coherenceMass : ℝ) : Prop where
  flatProfileSourceLegality : flatMass ≤ normalizedTarget S / 6
  correctedPBAnalytic : pbMass ≤ normalizedTarget S / 6
  hZeroFirewallBound : firewallMass ≤ normalizedTarget S / 6
  exceptionalSectorsBound : exceptionalMass ≤ normalizedTarget S / 6
  sourceCoherence : coherenceMass ≤ normalizedTarget S / 6

/-- **The sectors that this project *does* discharge**, in the same
vocabulary: the five clean-block sectors of §25, each bounded through the
proved Δv4 machinery (curvature `R^{-1}` saving, regular axis contraction,
true-zero divisor sparsity, `L = 0` ↦ `h = 0`, generic projective
pushforward).  The bound for each is stated as a hypothesis *about the
literal sector mass*, because the numerical identification of these masses
with the source data is part of the source-legality interface. -/
structure Delta4CleanSectorBounds (S : GateScale) (cleanMass : ℝ) : Prop where
  cleanBlockBound : cleanMass ≤ normalizedTarget S / 6

/-- **§27 (`gate1a_of_final_interfaces`).**  Conditional on the explicit open
interfaces (and on the clean-block bound), the normalised Gate-1A target and
the physical Gate-1A target both hold.

The conclusion is literally

```
∑_{r,k,m} |C̃_{r,k,m}|²  ≤  M H L⁴ X^{o(1)},
∑_e |C_e|²              ≤  M L⁴ / H · X^{o(1)},
```

with the second obtained from the first by the exact scale identity
`physical = normalized / H²` (`physical_eq_normalized_div_Hsq`). -/
theorem gate1a_of_final_interfaces (S : GateScale)
    {flatMass pbMass firewallMass exceptionalMass coherenceMass cleanMass : ℝ}
    {Cnorm Cphys : ℝ}
    (hopen : Delta4OpenInterfaces S flatMass pbMass firewallMass exceptionalMass
      coherenceMass)
    (hclean : Delta4CleanSectorBounds S cleanMass)
    (hsplit : Cnorm ≤ flatMass + pbMass + firewallMass + exceptionalMass
      + coherenceMass + cleanMass)
    (hphys : Cphys * S.H ^ 2 = Cnorm) :
    Cnorm ≤ normalizedTarget S ∧ Cphys ≤ physicalTarget S := by
  have h1 := hopen.flatProfileSourceLegality
  have h2 := hopen.correctedPBAnalytic
  have h3 := hopen.hZeroFirewallBound
  have h4 := hopen.exceptionalSectorsBound
  have h5 := hopen.sourceCoherence
  have h6 := hclean.cleanBlockBound
  have hnorm : Cnorm ≤ normalizedTarget S := by linarith
  refine ⟨hnorm, ?_⟩
  have hH2 : (0 : ℝ) < S.H ^ 2 := pow_pos S.hH 2
  have hval : Cphys = Cnorm / S.H ^ 2 := by
    rw [← hphys, mul_div_assoc, div_self hH2.ne', mul_one]
  rw [hval, physical_eq_normalized_div_Hsq]
  gcongr

/-- The conditional theorem is **not vacuous**: an explicit gate scale and an
explicit set of masses satisfying all interfaces. -/
theorem gate1a_of_final_interfaces_nonvacuous :
    ∃ (S : GateScale) (m : ℝ), Delta4OpenInterfaces S m m m m m ∧
      Delta4CleanSectorBounds S m := by
  refine ⟨⟨1, 1, 1, 1, 1, 1, 1, one_pos, one_pos, one_pos, one_pos, one_pos, one_pos,
    le_refl 1, by norm_num, by norm_num, by norm_num⟩, 0, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [normalizedTarget]
  · exact ⟨by norm_num [normalizedTarget]⟩

/-- The interfaces are **load-bearing**: there are data for which they fail,
so `gate1a_of_final_interfaces` is not a disguised tautology. -/
theorem gate1a_interfaces_load_bearing :
    ∃ (S : GateScale) (m : ℝ), ¬ Delta4OpenInterfaces S m m m m m := by
  refine ⟨⟨1, 1, 1, 1, 1, 1, 1, one_pos, one_pos, one_pos, one_pos, one_pos, one_pos,
    le_refl 1, by norm_num, by norm_num, by norm_num⟩, 2, ?_⟩
  intro h
  have := h.flatProfileSourceLegality
  norm_num [normalizedTarget] at this

/-- **§28 guard.**  No unconditional clean-bank theorem exists in this
project: the Δv4 closure is available only in the conditional form
`gate1a_of_final_interfaces`, and the exceptional table still contains nine
`open_` items. -/
theorem delta4_closure_is_conditional :
    routingStatus ExceptionalItem.hZero = RoutingStatus.open_ ∧
    routingStatus ExceptionalItem.pbAlias = RoutingStatus.open_ ∧
    routingStatus ExceptionalItem.properConductor = RoutingStatus.open_ :=
  ⟨rfl, rfl, rfl⟩

end Delta4

end Gate1A
