import Mathlib

/-!
# Centered CRT-root normal form

A conservative bank for the repaired centered transform.  The finite CRT and
normalization algebra is kernel checked here.  Fourier decay, bounded-variation
estimates, and the D2 large-sieve estimate are not asserted without hypotheses.

There is one important typing correction to the proposed D2 formulation.  The
weight was written as `W_{D,e}`, so its Fourier coefficient, and hence
`c_{p,q,h}`, can depend on `e`.  The usual large-sieve statement with one common
coefficient family therefore applies literally only when that dependence has
been removed (for example, a common weight is used).  An edge-dependent version
is a different structured analytic input and remains open.
-/

namespace TwinPrimeProject.CenteredCRTRoot

open scoped BigOperators

/-- Affine clean-slope data modulo two coprime moduli.  Primality and size are
analytic side conditions and are deliberately not needed for the CRT algebra. -/
structure CleanSlopeData where
  p : ℕ
  q : ℕ
  coprime : p.Coprime q
  alpha : ℤ
  beta : ℤ
  m : ℤ
  mPrime : ℤ
  rootPValue : ZMod p
  rootQValue : ZMod q
  rootP_spec : (alpha : ZMod p) + (m : ZMod p) * rootPValue = 0
  rootQ_spec : (beta : ZMod q) + (mPrime : ZMod q) * rootQValue = 0

namespace CleanSlopeData

/-- The root of `alpha + m*t` modulo `p`. -/
def rootP (d : CleanSlopeData) : ZMod d.p := d.rootPValue

/-- The root of `beta + mPrime*t` modulo `q`. -/
def rootQ (d : CleanSlopeData) : ZMod d.q := d.rootQValue

/-- The unique CRT fusion of the two affine roots. -/
noncomputable def crtRoot (d : CleanSlopeData) : ZMod (d.p * d.q) :=
  (ZMod.chineseRemainder d.coprime).symm (d.rootP, d.rootQ)

/-- The CRT root has the prescribed `p` component. -/
theorem crtRoot_fst (d : CleanSlopeData) :
    (ZMod.chineseRemainder d.coprime d.crtRoot).1 = d.rootP := by
  simp [crtRoot]

/-- The CRT root has the prescribed `q` component. -/
theorem crtRoot_snd (d : CleanSlopeData) :
    (ZMod.chineseRemainder d.coprime d.crtRoot).2 = d.rootQ := by
  simp [crtRoot]

/-- Clean slope makes the first CRT component an actual affine root. -/
theorem affine_at_rootP (d : CleanSlopeData) :
    (d.alpha : ZMod d.p) + (d.m : ZMod d.p) * d.rootP = 0 := by
  exact d.rootP_spec

/-- Clean slope makes the second CRT component an actual affine root. -/
theorem affine_at_rootQ (d : CleanSlopeData) :
    (d.beta : ZMod d.q) + (d.mPrime : ZMod d.q) * d.rootQ = 0 := by
  exact d.rootQ_spec

end CleanSlopeData

/-- Exact centered divisibility factor. -/
def rho (ell n : ℤ) : ℚ := (if ell ∣ n then 1 else 0) - 1 / ell

/-- The exact nonprincipal additive-character identity, represented without
silently importing an analytic theorem: once the complete additive
orthogonality formula is supplied, centering removes exactly its principal
term. -/
theorem centered_character_identity
    (ell n : ℤ) (nonprincipalAverage : ℚ)
    (hComplete : (if ell ∣ n then 1 else 0) = 1 / ell + nonprincipalAverage) :
    rho ell n = nonprincipalAverage := by
  unfold rho
  linarith

/-- Abstract exact harmonic packet.  `phase h T` is the additive character
`e(-hT/Q)` and `fourier h` is the finite Fourier transform of the weight. -/
structure HarmonicPacket where
  Harm : Type
  [harmFintype : Fintype Harm]
  [harmDecidableEq : DecidableEq Harm]
  Q : ℝ
  fourier : Harm → ℂ
  phase : Harm → ℂ
  primitive : Finset Harm

attribute [instance] HarmonicPacket.harmFintype HarmonicPacket.harmDecidableEq

namespace HarmonicPacket

/-- Exact CRT-root harmonic normal form after the finite centering and CRT
bijections have been performed. -/
noncomputable def normalForm (P : HarmonicPacket) : ℂ :=
  (P.Q : ℂ)⁻¹ * ∑ h ∈ P.primitive, P.fourier h * P.phase h

/-- Naming theorem for the exact finite harmonic formula. -/
theorem exact_harmonic_normal_form (P : HarmonicPacket) :
    P.normalForm = (P.Q : ℂ)⁻¹ *
      ∑ h ∈ P.primitive, P.fourier h * P.phase h := rfl

end HarmonicPacket

/-- A finite Fourier coefficient family normalized by `1/Q`. -/
noncomputable def gamma {H : Type*} (Q : ℝ) (fourier : H → ℂ) (h : H) : ℂ :=
  (Q : ℂ)⁻¹ * fourier h

/-- Discrete Parseval immediately gives the coefficient energy after division
by `Q²`.  Parseval itself is kept as an explicit premise so no Fourier
convention is hidden. -/
theorem coefficient_energy_of_parseval
    {H R : Type*} [Fintype H] [Fintype R]
    (Q : ℝ) (hQ : 0 < Q) (fourier : H → ℂ) (residueMass : R → ℂ)
    (hParseval : ∑ h, ‖fourier h‖ ^ 2 = Q * ∑ r, ‖residueMass r‖ ^ 2) :
    ∑ h, ‖gamma Q fourier h‖ ^ 2 = (1 / Q) * ∑ r, ‖residueMass r‖ ^ 2 := by
  have hQ0 : Q ≠ 0 := ne_of_gt hQ
  calc
    ∑ h, ‖gamma Q fourier h‖ ^ 2 = (1 / Q ^ 2) * ∑ h, ‖fourier h‖ ^ 2 := by
      simp [gamma, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hQ, Finset.mul_sum]
      ring_nf
    _ = (1 / Q) * ∑ r, ‖residueMass r‖ ^ 2 := by
      rw [hParseval]
      field_simp

/-- The scaling relation `D*H=L²` converts `D/L²` into `1/H`. -/
theorem energy_scaling (D H L : ℝ) (hD : 0 < D) (hH : 0 < H)
    (hscale : D * H = L ^ 2) : D / L ^ 2 = 1 / H := by
  rw [← hscale]
  field_simp

/-- The frequency scale `L²/D` is exactly `H`. -/
theorem harmonic_scale (D H L : ℝ) (hD : D ≠ 0)
    (hscale : D * H = L ^ 2) : L ^ 2 / D = H := by
  apply (div_eq_iff hD).2
  nlinarith [hscale]

/-- If `D>0` and `H>1`, then the banked scaling forces `D<L²`. -/
theorem D_lt_L2 (D H L : ℝ) (hD : 0 < D) (hH : 1 < H)
    (hscale : D * H = L ^ 2) : D < L ^ 2 := by
  rw [← hscale]
  nlinarith

/-- The calibrated trivial-to-target ratio is `M/H`. -/
theorem trivial_calibration (M D H L : ℝ) (hM : M ≠ 0) (hD : D ≠ 0)
    (hH : H ≠ 0) (hscale : D * H = L ^ 2) :
    (M ^ 2 * D ^ 2) / (M * L ^ 4 / H) = M / H := by
  have hL4 : L ^ 4 = (D * H) ^ 2 := by
    calc
      L ^ 4 = (L ^ 2) ^ 2 := by ring
      _ = (D * H) ^ 2 := by rw [hscale]
  rw [hL4]
  field_simp

/-- Summing a `1/H` energy bound over at most `L²` prime pairs gives total
energy at most `D` under `D*H=L²`. -/
theorem aggregate_coefficient_energy
    {Pair : Type*} [Fintype Pair]
    (D H L Xi : ℝ) (hH : 0 < H) (hXi : 0 ≤ Xi)
    (hscale : D * H = L ^ 2)
    (hPairs : (Fintype.card Pair : ℝ) ≤ L ^ 2)
    (pairEnergy : Pair → ℝ)
    (hEnergy : ∀ a, pairEnergy a ≤ Xi / H) :
    ∑ a, pairEnergy a ≤ D * Xi := by
  calc
    ∑ a, pairEnergy a ≤ ∑ _a : Pair, Xi / H :=
      Finset.sum_le_sum fun a _ => hEnergy a
    _ = (Fintype.card Pair : ℝ) * (Xi / H) := by simp
    _ ≤ L ^ 2 * (Xi / H) := by
      exact mul_le_mul_of_nonneg_right hPairs (div_nonneg hXi (le_of_lt hH))
    _ = D * Xi := by
      rw [← hscale]
      field_simp

/-- Common-coefficient D2 data.  This is the literal type of the normalized
large-sieve target in the checkpoint: the coefficient does not vary with the
outer edge. -/
structure CommonD2Data where
  Edge : Type
  Pair : Type
  Harm : Type
  [edgeFintype : Fintype Edge]
  [pairFintype : Fintype Pair]
  [harmFintype : Fintype Harm]
  M : ℝ
  L : ℝ
  D : ℝ
  H : ℝ
  coeff : Pair → Harm → ℂ
  phase : Edge → Pair → Harm → ℂ

attribute [instance] CommonD2Data.edgeFintype CommonD2Data.pairFintype
  CommonD2Data.harmFintype

namespace CommonD2Data

noncomputable def edgeSum (d : CommonD2Data) (e : d.Edge) : ℂ :=
  ∑ a, ∑ h, d.coeff a h * d.phase e a h

noncomputable def lhs (d : CommonD2Data) : ℝ := ∑ e, ‖d.edgeSum e‖ ^ 2
noncomputable def energy (d : CommonD2Data) : ℝ := ∑ a, ∑ h, ‖d.coeff a h‖ ^ 2

/-- The normalized common-coefficient D2 large-sieve assertion. -/
def LargeSieveTarget (d : CommonD2Data) : Prop :=
  d.lhs ≤ d.M * d.L ^ 2 * d.energy

/-- Correct sufficiency calculation: normalized D2 plus energy `≤ D*Xi`
produces the target `M L² D Xi`. -/
theorem normalized_D2_suffices (d : CommonD2Data)
    (hM : 0 ≤ d.M) (hD2 : d.LargeSieveTarget)
    (Xi : ℝ) (hEnergy : d.energy ≤ d.D * Xi) :
    d.lhs ≤ d.M * d.L ^ 2 * d.D * Xi := by
  calc
    d.lhs ≤ d.M * d.L ^ 2 * d.energy := hD2
    _ ≤ d.M * d.L ^ 2 * (d.D * Xi) := by
      exact mul_le_mul_of_nonneg_left hEnergy (mul_nonneg hM (sq_nonneg d.L))
    _ = d.M * d.L ^ 2 * d.D * Xi := by ring

/-- Under `D*H=L²`, the target is exactly `M*L⁴/H`. -/
theorem target_eq_ML4_over_H (d : CommonD2Data) (hH : d.H ≠ 0)
    (hscale : d.D * d.H = d.L ^ 2) :
    d.M * d.L ^ 2 * d.D = d.M * d.L ^ 4 / d.H := by
  apply (eq_div_iff hH).2
  calc
    d.M * d.L ^ 2 * d.D * d.H = d.M * d.L ^ 2 * (d.D * d.H) := by ring
    _ = d.M * d.L ^ 2 * d.L ^ 2 := by rw [hscale]
    _ = d.M * d.L ^ 4 := by ring

end CommonD2Data

/-- With genuinely edge-dependent weights the coefficients have this type.
It is intentionally distinct from `CommonD2Data`; no ordinary common-vector
large sieve is claimed for it. -/
structure EdgeDependentD2Data where
  Edge : Type
  Pair : Type
  Harm : Type
  [edgeFintype : Fintype Edge]
  [pairFintype : Fintype Pair]
  [harmFintype : Fintype Harm]
  coeff : Edge → Pair → Harm → ℂ
  phase : Edge → Pair → Harm → ℂ

inductive CheckpointStatus where
  | proved
  | conditional
  | corrected
  | open
  | notProved
  deriving DecidableEq, Repr

structure StatusEntry where
  label : String
  status : CheckpointStatus
  note : String := ""
  deriving Repr

/-- Conservative repaired ledger. -/
def statusLedger : List StatusEntry :=
  [ ⟨"CENTERED_CHARACTER_IDENTITY", .proved,
      "Exact after complete additive orthogonality; no hit branch discarded"⟩
  , ⟨"CRT_ROOT_FUSION", .proved, "Kernel-checked CRT root and affine-root identities"⟩
  , ⟨"EXACT_HARMONIC_NORMAL_FORM", .proved, "Exact finite sum"⟩
  , ⟨"HARMONIC_CUTOFF", .conditional, "Requires scale-D smoothness"⟩
  , ⟨"LEMMA_N1", .conditional, "Proved analytically only under BV/smooth regularity"⟩
  , ⟨"COEFFICIENT_ENERGY", .conditional,
      "Kernel-checked consequence of explicitly supplied discrete Parseval and support bounds"⟩
  , ⟨"NORMALIZED_COMMON_COEFFICIENT_D2_TARGET", .proved,
      "Normalization and sufficiency algebra are kernel checked"⟩
  , ⟨"EDGE_DEPENDENT_SPECIAL_COEFFICIENT_FORMULATION", .corrected,
      "W_{D,e} makes c depend on e unless a common-weight reduction is supplied"⟩
  , ⟨"D2_LARGE_SIEVE_INEQUALITY", .open, "No inhabitant or proof is supplied"⟩
  , ⟨"DETERMINANT_RESONANCE_EQUIVALENCE", .notProved, "Heuristic only"⟩
  , ⟨"Z_VARIABLE_ELIMINATION", .notProved, "Not substantively eliminated"⟩
  , ⟨"RPA_CELS_TYPE_II_TWIN_PRIMES", .open, "No downstream closure"⟩
  ]

end TwinPrimeProject.CenteredCRTRoot
