import RequestProject.RoutingThreshold
import RequestProject.MesoscopicParameters

/-!
# Routable long-Möbius F1 migration (§7, §8, §13.6)

An F1 piece
`𝓕 = Σ_{m,n} α_m β_n Σ_{y_1⋯y_a v_1⋯v_b = mn+2} ∏ μ(y_i)φ_i ∏ ρ_k(v_k)`
is **routable** if it contains (1) one genuine Möbius block of mesoscopic-or-longer
length, and (2) one smooth `(1)`-block of exponent `w > w*(μ) + δ`.  A routable
piece migrates into the fixed-depth F3 routing theorem and gains
`𝓕 ≪ X (log X)^{-B}`, using the Möbius cancellation *exactly once* before any
destructive absolute value, and with *no* nonprincipal character acting on the
Möbius block.

This module records:

* the routability hypotheses as an explicit structure (`F1RoutableHyp`);
* the Lean fact that the smooth-block condition `w > w*(μ)+δ` forces the widened
  wedge inequality `122μ + 162θ_j < 1` (`F1RoutableHyp.wedge_holds`);
* the migration as a `CONDITIONAL_INTERFACE`
  (`long_mobius_f1_migration_routable`), deriving the log-saving from an explicit
  routed-F3 provider — never from an axiom;
* the §13.6 conditional ultra-short product bound
  (`ultrashort_product_bound`), and the §8 conditional implication whose premise
  ("*all* long-Möbius F1 pieces migrate") is **not** proved.
-/

namespace ShiftedMobiusBank

/-- §7 — routability hypotheses for a long-Möbius F1 piece. -/
structure F1RoutableHyp where
  /-- outer exponent `μ` (`M = X^μ`). -/
  mu : ℝ
  hmu : 0 ≤ mu
  /-- exponent `w` of a designated smooth `(1)`-block (`V_k = X^{w+o(1)}`). -/
  w : ℝ
  /-- routing margin `δ > 0`. -/
  delta : ℝ
  hdelta : 0 < delta
  /-- the smooth block clears the routing threshold with margin. -/
  hroute : w ≥ wStar mu + delta
  /-- a genuine Möbius block reaches the mesoscopic length `Y_i ≥ Y_mes`. -/
  mesoscopicBlock : Prop
  hMeso : mesoscopicBlock
  /-- the Möbius cancellation is used exactly once, before any absolute value. -/
  singleUseMobius : Prop
  hSingle : singleUseMobius
  /-- no nonprincipal character acts on the Möbius block. -/
  noCharacterOnMobius : Prop
  hNoChar : noCharacterOnMobius

/-- The routability hypotheses imply the widened wedge inequality for the routed
modulus `θ_j = 1/2 - w`: `122μ + 162θ_j < 1`.  (No sign hypothesis on `θ_j` is
needed; the endpoint sign only selects which analytic branch fires.) -/
theorem F1RoutableHyp.wedge_holds (H : F1RoutableHyp) :
    122 * H.mu + 162 * thetaOfW H.w < 1 := by
  rw [thetaOfW, routing_threshold_equiv]
  have : H.w ≥ wStar H.mu + H.delta := H.hroute
  have := H.hdelta
  linarith

/-- §7 — interface for the fixed-depth routed F3 theorem, seen from F1.

`logSaving H` is the target `𝓕 ≪ X (log X)^{-B}` for a routable piece `H`.  The
`provider` supplies it from: the wedge inequality (routability), the mesoscopic
Möbius block, the single-use-Möbius discipline, and the no-character condition.
Nothing here is an axiom; the analytic content lives in the provider field. -/
structure F1MigrationInterface where
  logSaving : F1RoutableHyp → Prop
  provider : ∀ H : F1RoutableHyp,
    (122 * H.mu + 162 * thetaOfW H.w < 1) →
    H.mesoscopicBlock → H.singleUseMobius → H.noCharacterOnMobius →
    logSaving H

/-- §7 (`LONG_MOBIUS_F1_MIGRATION_ROUTABLE_PROVED`) as a `CONDITIONAL_INTERFACE`:
a routable long-Möbius F1 piece migrates into the fixed-depth F3 theorem and gains
log-saving. -/
theorem long_mobius_f1_migration_routable (I : F1MigrationInterface)
    (H : F1RoutableHyp) : I.logSaving H :=
  I.provider H H.wedge_holds H.hMeso H.hSingle H.hNoChar

/-- §13.6 — conditional ultra-short product bound.  For a fixed depth `K`, if every
Heath–Brown block `Y i ≤ Y_mes` (and `Y i ≥ 0`), then `∏_{i<K} Y i ≤ Y_mes^K`.
(Re-exported from `MesoscopicParameters.mesoscopic_finite_product_bound`.) -/
theorem ultrashort_product_bound {K : ℕ} (Ymes : ℝ) (Y : Fin K → ℝ)
    (hnonneg : ∀ i, 0 ≤ Y i) (hbound : ∀ i, Y i ≤ Ymes) :
    ∏ i, Y i ≤ Ymes ^ K :=
  mesoscopic_finite_product_bound Ymes Y hnonneg hbound

/-- §8 — the *conditional* implication whose premise is not proved.

`allPiecesMigrate → totalMobiusMassSmall` is a purely logical bridge: IF every
long-Möbius F1 piece migrates, THEN the aggregate Möbius mass is `X^{o(1)}`.  The
premise `allPiecesMigrate` is **not** currently established, so this does not bank
`F1_ULTRASHORT_CORE_REDUCTION_PROVED`; it only records the implication as an
interface field. -/
theorem full_f1_migration_conditional
    (allPiecesMigrate totalMobiusMassSmall : Prop)
    (bridge : allPiecesMigrate → totalMobiusMassSmall)
    (h : allPiecesMigrate) : totalMobiusMassSmall :=
  bridge h

end ShiftedMobiusBank
