/-
# NANC Gate 1A v9.8 — physical root geometry, the actual Gate 1A Direct energy,
and the generic BPP energy pin

Three things, in order.

## Section 8 — exact physical root geometry

The fibre objects `w0, α, A_e(t), B_e(t)` are **not** re-invented: they are the
fields and definitions of the existing `RouteAFibreFrame.Fibre`
(`RequestProject/NANC/FibreModel.lean`).  For a canonical row `e = (r, k, m)`
realised as the fibre base point `j = 0` and the shifted point `j = k`, the
determinant identity

    (m + k r) · A_e(t) − m · B_e(t) = 2 k

is proved (`direct_determinant_identity`) from the single fibre axiom
`c·w0 + 2 = r·a0`.  The Gate 1A Direct covariance `C_e(b,d)` is then written
with the repository's exact centred divisibility factor
`TwinPrimeProject.CenteredCRTRoot.rho`.

## Sections 9 and 4 — the actual Gate 1A energies, and the common `W_D`

`gate1ADirectAllMNormalizedEnergy` is literally `∑_e |Ctilde_e|²` and
`gate1ADirectAllMPhysicalEnergy` is literally `∑_e |C_e|²`.  The targets
`M H L⁴ · X^o` and `M L⁴/H · X^o` are defined here, not borrowed from any Gate 0
FF4 / D2 interface, and the `H`-normalisation bridge is proved.

The physical weight `W_D` is a **single field** of `PhysicalDirectSource`, with
no row index (`covariance_uses_one_common_weight`,
`physicalWeight_determines_covariance`), while an arbitrary per-row weight is a
strictly more general datum (`exists_rowDependent_weight_not_common`).  That is
the Section 4 A/B distinction at the physical level.

## Section 10 — the generic BPP energy pin

`Gate1ADirectBPPEnergyPin` contains exactly one field: the equation

    GenericBPPBound.normalizedEnergy (toESharpSource K) = gate1ADirectAllMNormalizedEnergy K.

It mentions no `SourceExactPacketDictionary`, no packet multiplicity and no
Gate 0 assembly.  No inhabitant is constructed.  The hostile guards
`energyPin_not_automatic` and `energyPin_not_implied_by_conclusion` show that
the pin is neither free nor obtainable from the bound it is used to transport.
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm
import RequestProject.NANC.FibreModel
import RequestProject.NANC.Gate1A.SafeExtensions.V95ESharpScope
import RequestProject.NANC.Gate1A.SafeExtensions.V96SourceDictionary
import RequestProject.NANC.Gate1A.SafeExtensions.V98CanonicalDirectSource
import RequestProject.NANC.Gate1A.SafeExtensions.V98CanonicalAllMRows

namespace TwinPrimeProject.NANC.Gate1A.V98

open Finset
open TwinPrimeProject.CenteredCRTRoot
open TwinPrimeProject.NANC.Gate1A.V95

/-! ## 1. Exact physical root geometry (Section 8) -/

namespace Fibre

open RouteAFibreFrame

/-- The `A`-edge of a canonical row: the fibre row entry at the base point
`j = 0`, i.e. `A_e(t) = α + m t` with `m = c`. -/
def Aedge (F : RouteAFibreFrame.Fibre) (t : ℤ) : ℤ := F.A 0 t

/-- The `B`-edge of a canonical row with shift `k`: the fibre `B`-edge at the
shifted point `j = k`. -/
def Bedge (F : RouteAFibreFrame.Fibre) (k t : ℤ) : ℤ := F.B k t

/-- The `B`-edge is integral and equals the shifted `A`-row (v9 bank, F3). -/
theorem Bedge_eq (F : RouteAFibreFrame.Fibre) (k t : ℤ) : Bedge F k t = F.A k t :=
  F.fibre_B_eq_A_jprime k t

/-- **The exact determinant identity of the canonical Gate 1A Direct row**:
`(m + k r) A_e(t) − m B_e(t) = 2 k`, with `m = c` the fibre offset. -/
theorem direct_determinant_identity (F : RouteAFibreFrame.Fibre) (k t : ℤ) :
    (F.c + k * F.r) * Aedge F t - F.c * Bedge F k t = 2 * k := by
  rw [Bedge_eq]
  simp only [Aedge, RouteAFibreFrame.Fibre.A, RouteAFibreFrame.Fibre.alpha,
    RouteAFibreFrame.Fibre.m]
  linear_combination (-k) * F.root

end Fibre

/-! ## 2. The physical Gate 1A Direct source and its one common weight -/

/-- The physical (pre-transform) Gate 1A Direct source.  The smoothing weight
`WD` is **one field**: it is not indexed by the row. -/
structure PhysicalDirectSource where
  /-- The canonical row index type. -/
  Row : Type
  [rowFintype : Fintype Row]
  /-- The fibre of each row (supplying `w0`, `α`, `A_e`, `B_e`). -/
  fib : Row → RouteAFibreFrame.Fibre
  /-- The shift `k` of each row. -/
  kk : Row → ℤ
  /-- The `t`-summation index. -/
  T : Type
  [tFintype : Fintype T]
  /-- The value of the summation variable. -/
  tval : T → ℤ
  /-- **The one common physical smoothing weight `W_D`.** -/
  WD : ℤ → ℂ
  /-- The `p ∼ L` index type. -/
  P : Type
  [pFintype : Fintype P]
  /-- The `q ∼ L` index type. -/
  Q : Type
  [qFintype : Fintype Q]
  /-- Prime values. -/
  pval : P → ℤ
  /-- Prime values. -/
  qval : Q → ℤ
  /-- Source coefficients. -/
  b : P → ℂ
  /-- Source coefficients. -/
  d : Q → ℂ

attribute [instance] PhysicalDirectSource.rowFintype PhysicalDirectSource.tFintype
  PhysicalDirectSource.pFintype PhysicalDirectSource.qFintype

namespace PhysicalDirectSource

variable (X : PhysicalDirectSource)

/-- `A_e(t)` of the physical source. -/
def Aedge (e : X.Row) (t : X.T) : ℤ := Fibre.Aedge (X.fib e) (X.tval t)

/-- `B_e(t)` of the physical source. -/
def Bedge (e : X.Row) (t : X.T) : ℤ := Fibre.Bedge (X.fib e) (X.kk e) (X.tval t)

/-- **The canonical Gate 1A Direct covariance**

    C_e(b,d) = ∑_t W_D(t) (∑_p b_p ρ_p(A_e(t))) (∑_q d_q ρ_q(B_e(t))),

with `ρ` the repository's exact centred divisibility factor. -/
noncomputable def covariance (e : X.Row) : ℂ :=
  ∑ t, X.WD (X.tval t) *
    (∑ p, X.b p * ((rho (X.pval p) (X.Aedge e t) : ℚ) : ℂ)) *
    (∑ q, X.d q * ((rho (X.qval q) (X.Bedge e t) : ℚ) : ℂ))

/-- Definitional unfolding of the covariance. -/
theorem covariance_def (e : X.Row) :
    X.covariance e = ∑ t, X.WD (X.tval t) *
      (∑ p, X.b p * ((rho (X.pval p) (X.Aedge e t) : ℚ) : ℂ)) *
      (∑ q, X.d q * ((rho (X.qval q) (X.Bedge e t) : ℚ) : ℂ)) := rfl

/-- Each row of the physical source obeys the exact determinant identity. -/
theorem covariance_determinant (e : X.Row) (t : X.T) :
    ((X.fib e).c + X.kk e * (X.fib e).r) * X.Aedge e t - (X.fib e).c * X.Bedge e t
      = 2 * X.kk e :=
  Fibre.direct_determinant_identity (X.fib e) (X.kk e) (X.tval t)

/-- The row kernel of the physical source: everything in the covariance except
the physical weight. -/
noncomputable def kernel (e : X.Row) (t : X.T) : ℂ :=
  (∑ p, X.b p * ((rho (X.pval p) (X.Aedge e t) : ℚ) : ℂ)) *
    (∑ q, X.d q * ((rho (X.qval q) (X.Bedge e t) : ℚ) : ℂ))

/-- **Common physical weight, pairing form.**  Every row's covariance is the
pairing of the *same* weight function `W_D` with that row's kernel:
`C_e = ∑_t W_D(t) · kernel_e(t)`.  The weight is one datum shared by all rows;
only the kernel is row-dependent. -/
theorem covariance_eq_weight_pairing (e : X.Row) :
    X.covariance e = ∑ t, X.WD (X.tval t) * X.kernel e t := by
  refine Finset.sum_congr rfl fun t _ => ?_
  simp only [kernel]
  ring

/-- Two different rows pair against the identical weight function. -/
theorem common_weight_shared_by_rows (e e' : X.Row) :
    X.covariance e = ∑ t, X.WD (X.tval t) * X.kernel e t ∧
      X.covariance e' = ∑ t, X.WD (X.tval t) * X.kernel e' t :=
  ⟨X.covariance_eq_weight_pairing e, X.covariance_eq_weight_pairing e'⟩

end PhysicalDirectSource

/-- **Rigidity of the common weight.**  Two physical sources that agree on the
weight field and on all remaining data have identical covariances; the
covariance therefore depends on the smoothing datum only through the single
field `WD`. -/
theorem physicalWeight_determines_covariance (X Y : PhysicalDirectSource)
    (hRow : X.Row = Y.Row) (hW : HEq X.WD Y.WD) (hall : HEq X Y) :
    HEq X.covariance Y.covariance := by
  cases hall
  rfl

/-- **Type A is strictly more general than type B.**  A weight chosen freely per
row need not come from any common weight; this is what an arbitrary `W_{D,e}`
would mean, and it is *not* the canonical Direct source. -/
theorem exists_rowDependent_weight_not_common :
    ∃ WDe : Fin 2 → ℤ → ℂ, ¬ ∃ W : ℤ → ℂ, ∀ e, WDe e = W := by
  refine ⟨fun e _ => (e : ℕ), ?_⟩
  rintro ⟨W, hW⟩
  have h0 := congrFun (hW 0) 0
  have h1 := congrFun (hW 1) 0
  rw [← h0] at h1
  norm_num at h1

/-! ## 3. The canonical Direct packet and the actual Gate 1A energies -/

/-- A canonical Gate 1A Direct packet: the authoritative normalized source
together with the canonical all-`m` `E♯` row datum of each of its rows. -/
structure Gate1ADirectPacket where
  /-- The authoritative normalized source. -/
  source : Gate1ADirectCanonicalSource
  /-- The canonical all-`m` row datum of each row. -/
  esharpRow : source.Row → Gate1ADirectAllMRow

namespace Gate1ADirectPacket

variable (K : Gate1ADirectPacket)

/-- **The actual Gate 1A Direct all-`m` normalized energy**, literally
`∑_{e ∈ E♯} |Ctilde_e|²`. -/
noncomputable def normalizedEnergy : ℝ := ∑ e, ‖K.source.ctilde e‖ ^ 2

theorem normalizedEnergy_def : K.normalizedEnergy = ∑ e, ‖K.source.ctilde e‖ ^ 2 := rfl

/-- The normalized energy is non-negative. -/
theorem normalizedEnergy_nonneg : 0 ≤ K.normalizedEnergy :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The canonical packet, viewed as an `E♯` source with the canonical
coefficients. -/
noncomputable def toESharpSource : ESharpSource where
  Row := K.source.Row
  rowFintype := K.source.rowFintype
  row := K.esharpRow
  coeff := fun e => K.source.ctilde e

@[simp] theorem toESharpSource_coeff (e : K.source.Row) :
    K.toESharpSource.coeff e = K.source.ctilde e := rfl

end Gate1ADirectPacket

/-- **The actual Gate 1A Direct all-`m` physical energy**, literally
`∑_{e ∈ E♯} |C_e|²`. -/
noncomputable def gate1ADirectAllMPhysicalEnergy (X : PhysicalDirectSource) : ℝ :=
  ∑ e, ‖X.covariance e‖ ^ 2

theorem gate1ADirectAllMPhysicalEnergy_nonneg (X : PhysicalDirectSource) :
    0 ≤ gate1ADirectAllMPhysicalEnergy X :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-! ## 4. The exact Gate 1A Direct targets and the `H`-normalisation bridge -/

/-- The normalized target `M H L⁴ · X^{o(1)}`. -/
def normalizedDirectTarget (M H L Xo : ℝ) : ℝ := M * H * L ^ 4 * Xo

/-- The physical target `(M L⁴/H) · X^{o(1)}`. -/
noncomputable def physicalDirectTarget (M H L Xo : ℝ) : ℝ := M * L ^ 4 / H * Xo

/-- **The `H`-normalisation bridge**: `M H L⁴ = (M L⁴/H) · H²`. -/
theorem directTarget_bridge (M H L Xo : ℝ) (hH : H ≠ 0) :
    normalizedDirectTarget M H L Xo = physicalDirectTarget M H L Xo * H ^ 2 := by
  unfold normalizedDirectTarget physicalDirectTarget
  field_simp

/-- **Transport of a normalized bound to the physical target**, using the
source normalisation convention `physical = normalized / H²`. -/
theorem physical_of_normalized_bound (K : Gate1ADirectPacket) (X : PhysicalDirectSource)
    (M H L Xo : ℝ) (hH : 0 < H)
    (hconv : gate1ADirectAllMPhysicalEnergy X = K.normalizedEnergy / H ^ 2)
    (hbound : K.normalizedEnergy ≤ normalizedDirectTarget M H L Xo) :
    gate1ADirectAllMPhysicalEnergy X ≤ physicalDirectTarget M H L Xo := by
  have hH2 : (0 : ℝ) < H ^ 2 := by positivity
  rw [hconv, div_le_iff₀ hH2]
  refine hbound.trans ?_
  rw [directTarget_bridge M H L Xo (ne_of_gt hH)]

/-! ## 5. The generic BPP energy pin (Section 10) -/

/-- **`Gate1ADirectBPPEnergyPin`.**  Its single field is the exact equation
pinning the generic engine's energy functional to the actual canonical Gate 1A
Direct all-`m` normalized energy.  No dictionary, no multiplicity, no Gate 0
assembly occurs in the statement. -/
structure Gate1ADirectBPPEnergyPin (G : GenericBPPBound) (K : Gate1ADirectPacket) where
  /-- The pin. -/
  pin : G.normalizedEnergy K.toESharpSource = K.normalizedEnergy

/-- **The pin compiler.**  A pinned generic bound bounds the actual Gate 1A
Direct energy — and nothing weaker would. -/
theorem Gate1ADirectBPPEnergyPin.energy_le (G : GenericBPPBound) (K : Gate1ADirectPacket)
    (p : Gate1ADirectBPPEnergyPin G K) : K.normalizedEnergy ≤ G.genericTarget := by
  rw [← p.pin]
  exact G.bound _

/-- The pinned generic bound reaches the normalized Gate 1A target as soon as
the generic target does. -/
theorem normalizedEnergy_le_target_of_pin (G : GenericBPPBound) (K : Gate1ADirectPacket)
    (p : Gate1ADirectBPPEnergyPin G K) (M H L Xo : ℝ)
    (hT : G.genericTarget ≤ normalizedDirectTarget M H L Xo) :
    K.normalizedEnergy ≤ normalizedDirectTarget M H L Xo :=
  (p.energy_le G K).trans hT

/-! ## 6. A concrete non-trivial packet, for the hostile guards -/

/-- A concrete canonical source with one row, one `p = 2`, one `q = 3`, one
harmonic `h = 0`, unit coefficients and `Ŵ_D ≡ 1`: its `Ctilde` equals `1`. -/
noncomputable def unitSource : Gate1ADirectCanonicalSource where
  scalars := { Hscale := 6, What := fun _ => 1, alph := 0 }
  Row := Fin 1
  row := fun _ => { r := 1, k := 0, m := 1 }
  P := Fin 1
  Q := Fin 1
  Harm := Fin 1
  pval := fun _ => 2
  qval := fun _ => 3
  hval := fun _ => 0
  b := fun _ => 1
  d := fun _ => 1
  inv := fun _ _ _ => 2
  inv_spec := by intro e p q; norm_num

@[simp] theorem unitSource_ctilde (e : unitSource.Row) : unitSource.ctilde e = 1 := by
  simp [Gate1ADirectCanonicalSource.ctilde, Gate1ADirectCanonicalSource.coeffAt,
    Gate1ADirectCanonicalSource.phase, omegaCanonical, unitSource]
  norm_num

/-- The corresponding canonical packet, with the explicit all-`m` witness row. -/
noncomputable def unitPacket : Gate1ADirectPacket where
  source := unitSource
  esharpRow := fun _ => allMRowWitness

@[simp] theorem unitPacket_energy : unitPacket.normalizedEnergy = 1 := by
  simp [Gate1ADirectPacket.normalizedEnergy, unitPacket]
  simp [unitSource]

/-- **Hostile guard 1: the energy pin is not automatic.**  The vacuous generic
bound of v9.6 has zero energy functional, so it does not pin the actual Gate 1A
Direct energy. -/
theorem energyPin_not_automatic :
    ∃ (G : GenericBPPBound) (K : Gate1ADirectPacket),
      G.normalizedEnergy K.toESharpSource ≠ K.normalizedEnergy := by
  refine ⟨V96.trivialGenericBPPBound, unitPacket, ?_⟩
  simp [V96.trivialGenericBPPBound]

/-- **Hostile guard 2: the pin cannot be obtained from its desired
conclusion.**  There is a generic bound whose target already dominates the
actual Gate 1A Direct energy and which nevertheless fails to pin it. -/
theorem energyPin_not_implied_by_conclusion :
    ∃ (G : GenericBPPBound) (K : Gate1ADirectPacket),
      K.normalizedEnergy ≤ G.genericTarget ∧
        G.normalizedEnergy K.toESharpSource ≠ K.normalizedEnergy := by
  refine ⟨{ normalizedEnergy := fun _ => 0, genericTarget := 5,
            bound := fun _ => by norm_num }, unitPacket, ?_, ?_⟩
  · simp
  · simp

/-- **Hostile guard 3: an inhabitant of the pin is exactly the equation.**  The
pin type is non-empty iff the equation holds; it can therefore never manufacture
an estimate. -/
theorem energyPin_nonempty_iff (G : GenericBPPBound) (K : Gate1ADirectPacket) :
    Nonempty (Gate1ADirectBPPEnergyPin G K) ↔
      G.normalizedEnergy K.toESharpSource = K.normalizedEnergy :=
  ⟨fun ⟨p⟩ => p.pin, fun h => ⟨⟨h⟩⟩⟩

end TwinPrimeProject.NANC.Gate1A.V98
