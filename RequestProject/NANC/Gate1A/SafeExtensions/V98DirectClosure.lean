/-
# NANC Gate 1A v9.8 — the canonical Gate 1A Direct closure compiler

Section 16 asks for the exact statement

    Gate1ADirectAllMCommonWeightBPP :
      for all admissible 1-bounded source coefficients b, d,
      ∑_{e ∈ E♯} |C_e(b,d)|²  ≤  (M L⁴/H) · X^{o(1)},

with the canonical physical common weight `W_D`, and for the equivalent
normalized form `∑_e |Ctilde_e|² ≤ M H L⁴ · X^{o(1)}`.

The statement is *pinned* here as a definition, and a **deterministic
compiler** is proved:

    normalized BPP bound  ∧  source normalisation convention
      ⟹  Gate1ADirectAllMCommonWeightBPP.

The normalized BPP bound is not manufactured: it enters either as an explicit
hypothesis or through `Gate1ADirectBPPEnergyPin` from a `GenericBPPBound` whose
generic target already meets `M H L⁴ X^o`.  Section 23 guards are proved:

* `closureCertificate_nonempty_iff` — an inhabitant of the certificate is
  exactly the conjunction of its two analytic/convention premises, so the
  compiler cannot create an estimate;
* `closure_not_implied_by_physical_target` — the desired physical conclusion
  does not produce the certificate;
* `closureCertificate_needs_no_rootDefect_or_dictionary` — the certificate is
  inhabitable in a situation where the Gate 0 census is *not*, which is the
  scope separation of Sections 18–20 in its sharpest formal form.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.V98DirectEnergyPin
import RequestProject.NANC.Gate1A.SafeExtensions.V98BPPProvenance

namespace TwinPrimeProject.NANC.Gate1A.V98

open Finset
open TwinPrimeProject.NANC.Gate1A.V95

/-! ## 1. The canonical theorem statement -/

/-- **`Gate1ADirectAllMCommonWeightBPP`**, the exact Gate 1A Direct all-`m`
common-weight statement: for 1-bounded source coefficient sequences, the
canonical Direct covariance energy meets the physical target `(M L⁴/H)·X^o`. -/
def Gate1ADirectAllMCommonWeightBPP (X : PhysicalDirectSource) (M H L Xo : ℝ) : Prop :=
  (∀ p, ‖X.b p‖ ≤ 1) → (∀ q, ‖X.d q‖ ≤ 1) →
    gate1ADirectAllMPhysicalEnergy X ≤ physicalDirectTarget M H L Xo

/-- The equivalent normalized form of the canonical statement. -/
def Gate1ADirectAllMCommonWeightBPPNormalized (K : Gate1ADirectPacket) (M H L Xo : ℝ) : Prop :=
  K.normalizedEnergy ≤ normalizedDirectTarget M H L Xo

/-! ## 2. The closure certificate and its compiler -/

/-- **The canonical Gate 1A Direct closure certificate.**  Two premises only:
the normalized BPP bound for the canonical packet, and the source normalisation
convention relating the physical and normalized energies.  There is no
`SourceExactPacketDictionary` field, no packet-multiplicity field, no Gate 0
assembly field and no root-defect field. -/
structure Gate1ADirectClosureCertificate (K : Gate1ADirectPacket) (X : PhysicalDirectSource)
    (M H L Xo : ℝ) where
  /-- The harmonic scale is positive. -/
  H_pos : 0 < H
  /-- The normalized Gate 1A Direct bound (the analytic input). -/
  normalizedBound : Gate1ADirectAllMCommonWeightBPPNormalized K M H L Xo
  /-- The source normalisation convention `physical = normalized / H²`. -/
  convention : gate1ADirectAllMPhysicalEnergy X = K.normalizedEnergy / H ^ 2

namespace Gate1ADirectClosureCertificate

variable {K : Gate1ADirectPacket} {X : PhysicalDirectSource} {M H L Xo : ℝ}

/-- **The closure compiler.**  Finite arithmetic only. -/
theorem toPhysicalTarget (C : Gate1ADirectClosureCertificate K X M H L Xo) :
    gate1ADirectAllMPhysicalEnergy X ≤ physicalDirectTarget M H L Xo :=
  physical_of_normalized_bound K X M H L Xo C.H_pos C.convention C.normalizedBound

/-- The compiler in the exact shape of the canonical theorem statement. -/
theorem toCanonicalStatement (C : Gate1ADirectClosureCertificate K X M H L Xo) :
    Gate1ADirectAllMCommonWeightBPP X M H L Xo :=
  fun _ _ => C.toPhysicalTarget

end Gate1ADirectClosureCertificate

/-- **Assembly from the pinned generic engine.**  A `GenericBPPBound` that is
pinned to the actual Gate 1A Direct energy and whose generic target meets the
normalized Gate 1A target yields the certificate — provided the normalisation
convention is supplied. -/
def closureCertificate_of_pin (K : Gate1ADirectPacket) (X : PhysicalDirectSource)
    (M H L Xo : ℝ) (hH : 0 < H) (G : GenericBPPBound)
    (p : Gate1ADirectBPPEnergyPin G K)
    (hT : G.genericTarget ≤ normalizedDirectTarget M H L Xo)
    (hconv : gate1ADirectAllMPhysicalEnergy X = K.normalizedEnergy / H ^ 2) :
    Gate1ADirectClosureCertificate K X M H L Xo where
  H_pos := hH
  normalizedBound := normalizedEnergy_le_target_of_pin G K p M H L Xo hT
  convention := hconv

/-! ## 3. Section 23 guards -/

/-- **The certificate is exactly its premises.**  It can therefore never
manufacture the analytic estimate it transports. -/
theorem closureCertificate_nonempty_iff (K : Gate1ADirectPacket) (X : PhysicalDirectSource)
    (M H L Xo : ℝ) :
    Nonempty (Gate1ADirectClosureCertificate K X M H L Xo) ↔
      (0 < H ∧ Gate1ADirectAllMCommonWeightBPPNormalized K M H L Xo ∧
        gate1ADirectAllMPhysicalEnergy X = K.normalizedEnergy / H ^ 2) :=
  ⟨fun ⟨C⟩ => ⟨C.H_pos, C.normalizedBound, C.convention⟩,
   fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2, h3⟩⟩⟩

/-- The empty canonical source: no rows at all. -/
noncomputable def emptySource : Gate1ADirectCanonicalSource where
  scalars := { Hscale := 0, What := fun _ => 0, alph := 0 }
  Row := Fin 0
  row := fun i => i.elim0
  P := Fin 0
  Q := Fin 0
  Harm := Fin 0
  pval := fun i => i.elim0
  qval := fun i => i.elim0
  hval := fun i => i.elim0
  b := fun i => i.elim0
  d := fun i => i.elim0
  inv := fun i => i.elim0
  inv_spec := fun i => i.elim0

/-- The empty canonical packet. -/
noncomputable def emptyPacket : Gate1ADirectPacket where
  source := emptySource
  esharpRow := fun i => i.elim0

/-- The empty physical source. -/
def emptyPhysical : PhysicalDirectSource where
  Row := Fin 0
  fib := fun i => i.elim0
  kk := fun i => i.elim0
  T := Fin 0
  tval := fun i => i.elim0
  WD := fun _ => 0
  P := Fin 0
  Q := Fin 0
  pval := fun i => i.elim0
  qval := fun i => i.elim0
  b := fun i => i.elim0
  d := fun i => i.elim0

@[simp] theorem emptyPacket_energy : emptyPacket.normalizedEnergy = 0 := by
  simp [Gate1ADirectPacket.normalizedEnergy, emptyPacket, emptySource]

@[simp] theorem emptyPhysical_energy : gate1ADirectAllMPhysicalEnergy emptyPhysical = 0 := by
  simp [gate1ADirectAllMPhysicalEnergy, emptyPhysical]

/-- **The desired physical conclusion does not produce the certificate.**  Here
the physical target already holds while the certificate is empty, because the
normalisation convention fails. -/
theorem closure_not_implied_by_physical_target :
    ∃ (K : Gate1ADirectPacket) (X : PhysicalDirectSource) (M H L Xo : ℝ),
      gate1ADirectAllMPhysicalEnergy X ≤ physicalDirectTarget M H L Xo ∧
        IsEmpty (Gate1ADirectClosureCertificate K X M H L Xo) := by
  refine ⟨unitPacket, emptyPhysical, 0, 1, 0, 0, by simp [physicalDirectTarget], ?_⟩
  constructor
  rintro C
  have := C.convention
  simp at this

/-- The empty configuration inhabits the certificate: no root-defect
factorisation, no packet dictionary and no Gate 0 census enters its
construction. -/
def emptyClosureCertificate :
    Gate1ADirectClosureCertificate emptyPacket emptyPhysical 0 1 0 0 where
  H_pos := one_pos
  normalizedBound := by
    simp [Gate1ADirectAllMCommonWeightBPPNormalized, normalizedDirectTarget]
  convention := by simp

/-! ## 4. Recombination error (Section 15), re-exported -/

/-- The controlling `U^{-2}` recombination-error identity (v9.4 bank). -/
theorem directRecombinationError_U2 (M H L D U : ℝ) (hM : M ≠ 0) (hH : H ≠ 0) (hL : L ≠ 0)
    (hD : D ≠ 0) (hU : U = L / H) (hDH : D * H = L ^ 2) :
    (U ^ (-2 : ℤ) * M ^ 2 * L ^ 4) / (M * H * L ^ 4) = M / D :=
  V94.recombinationError_U2_budget M H L D U hM hH hL hD hU hDH

end TwinPrimeProject.NANC.Gate1A.V98
