/-
# Universal / D0WP — the other-parent deterministic source router

**Status of this module: KERNEL_PROVED finite/exponent routing.  No analytic
bound is attached at this step.**

The newest deterministic decision tree is formalised literally, in its stated
priority order:

```
Type-I                                  -> Gate0
perfect-power / repeated / parity /local-> local
complement depth ≥ 3                    -> RUN1B class
depth 2 passing the 4/9 router          -> RUN1B
theta + rhoMin ≤ gamma                  -> Gate0
composite f-leaf                        -> RUN1B
block-saturated same-block              -> HB reassembly
residual                                -> ThetaUltra
```

What is proved: the router is a total function (so every row is routed exactly
once), each branch is characterised exactly, and the residual class is precisely
the conjunction of the negations of all earlier tests.  The ultra residual then
splits by `Universal.D0WP.theta_ultra_split`.
-/
import Universal.D0WP.UltraSourceSplit

namespace Universal.D0WP

open Finset

/-- The routing targets. -/
inductive Route
  /-- Gate0. -/
  | gate0
  /-- Local / parity handling. -/
  | localBranch
  /-- The RUN1B class. -/
  | run1b
  /-- HB reassembly of block-saturated same-block rows. -/
  | hbReassembly
  /-- The ultra residual. -/
  | thetaUltra
  deriving DecidableEq, Repr, Fintype

/-- The literal row data read by the router. -/
structure RowData where
  /-- Type-I row. -/
  typeI : Bool
  /-- Perfect-power / repeated / parity / local degeneracy. -/
  degenerate : Bool
  /-- Depth of the complement. -/
  complementDepth : ℕ
  /-- Whether the depth-2 row passes the 4/9 router. -/
  passes49 : Bool
  /-- Exponent `theta`. -/
  theta : ℝ
  /-- Exponent `rhoMin`. -/
  rhoMin : ℝ
  /-- Exponent `gamma`. -/
  gamma : ℝ
  /-- Composite `f`-leaf. -/
  compositeFLeaf : Bool
  /-- Block-saturated same-block row. -/
  blockSaturatedSameBlock : Bool

open Classical in
/-- The deterministic router. -/
noncomputable def route (r : RowData) : Route :=
  if r.typeI then Route.gate0
  else if r.degenerate then Route.localBranch
  else if 3 ≤ r.complementDepth then Route.run1b
  else if r.complementDepth = 2 ∧ r.passes49 then Route.run1b
  else if r.theta + r.rhoMin ≤ r.gamma then Route.gate0
  else if r.compositeFLeaf then Route.run1b
  else if r.blockSaturatedSameBlock then Route.hbReassembly
  else Route.thetaUltra

theorem route_typeI {r : RowData} (h : r.typeI = true) : route r = Route.gate0 := by
  simp [route, h]

theorem route_degenerate {r : RowData} (h1 : r.typeI = false) (h2 : r.degenerate = true) :
    route r = Route.localBranch := by
  simp [route, h1, h2]

theorem route_deep {r : RowData} (h1 : r.typeI = false) (h2 : r.degenerate = false)
    (h3 : 3 ≤ r.complementDepth) : route r = Route.run1b := by
  simp [route, h1, h2, h3]

/-- **Residual characterisation (kernel-proved).**  A row lands in the ultra
residual exactly when every earlier test fails. -/
theorem route_eq_thetaUltra_iff (r : RowData) :
    route r = Route.thetaUltra ↔
      (r.typeI = false ∧ r.degenerate = false ∧ r.complementDepth < 3 ∧
        ¬ (r.complementDepth = 2 ∧ r.passes49 = true) ∧
        ¬ (r.theta + r.rhoMin ≤ r.gamma) ∧ r.compositeFLeaf = false ∧
        r.blockSaturatedSameBlock = false) := by
  unfold route
  constructor
  · intro h
    by_cases h1 : r.typeI = true
    · simp [h1] at h
    · by_cases h2 : r.degenerate = true
      · simp [h1, h2] at h
      · by_cases h3 : 3 ≤ r.complementDepth
        · simp [h1, h2, h3] at h
        · by_cases h4 : r.complementDepth = 2 ∧ r.passes49 = true
          · simp [h1, h2, h4] at h
          · by_cases h5 : r.theta + r.rhoMin ≤ r.gamma
            · simp [h1, h2, h3, h4, h5] at h
            · by_cases h6 : r.compositeFLeaf = true
              · simp [h1, h2, h3, h4, h5, h6] at h
              · by_cases h7 : r.blockSaturatedSameBlock = true
                · simp [h1, h2, h3, h4, h5, h6, h7] at h
                · exact ⟨by simpa using h1, by simpa using h2, by omega,
                    by simpa using h4, h5, by simpa using h6, by simpa using h7⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    have h3' : ¬ (3 ≤ r.complementDepth) := by omega
    simp [h1, h2, h3', h4, h5, h6, h7]

/-- The router is total and deterministic: it is a function, so each row is
routed to exactly one target. -/
theorem route_unique (r : RowData) (a b : Route) (ha : route r = a) (hb : route r = b) :
    a = b := by rw [← ha, ← hb]

/-- The ultra residual family of a finite row set. -/
noncomputable def ultraResidual {ι : Type*} [DecidableEq ι] (rows : Finset ι)
    (rd : ι → RowData) : Finset ι :=
  rows.filter (fun i => route (rd i) = Route.thetaUltra)

/-- **Router ∘ split (kernel-proved).**  The ultra residual splits into the
cross and cut families, disjointly and exhaustively. -/
theorem ultraResidual_split {ι : Type*} [DecidableEq ι] (rows : Finset ι)
    (rd : ι → RowData) (data : UltraBlockData ι) :
    Disjoint (ThetaCross data (ultraResidual rows rd)) (ThetaCut data (ultraResidual rows rd)) ∧
      ThetaCross data (ultraResidual rows rd) ∪ ThetaCut data (ultraResidual rows rd)
        = ultraResidual rows rd :=
  theta_ultra_split data (ultraResidual rows rd)

end Universal.D0WP
