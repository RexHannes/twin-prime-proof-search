import RequestProject.NANC.TwoPhaseCollapse

namespace TwinPrimeProject.NANC.DoubleReciprocityCollapse

/-- Equality of rational phases modulo the integer lattice.  This is exactly
the equality needed before applying `x ↦ exp(2πix)`. -/
def PhaseEq (x y : ℚ) : Prop := ∃ z : ℤ, x - y = z

/-- `x` is an integer representative of the inverse of `a` modulo `n`.
The witness is retained explicitly for algebraic proofs. -/
def InvModSpec (a n x : ℤ) : Prop := ∃ t : ℤ, a * x = 1 + n * t

/-- Congruence represented by an explicit integer quotient. -/
def CongruentSpec (a b n : ℤ) : Prop := ∃ t : ℤ, a = b + n * t

namespace PhaseEq

theorem refl (x : ℚ) : PhaseEq x x := by
  exact ⟨0, by simp⟩

theorem symm {x y : ℚ} (h : PhaseEq x y) : PhaseEq y x := by
  rcases h with ⟨z, hz⟩
  exact ⟨-z, by push_cast; linarith⟩

theorem trans {x y z : ℚ} (hxy : PhaseEq x y) (hyz : PhaseEq y z) : PhaseEq x z := by
  rcases hxy with ⟨a, ha⟩
  rcases hyz with ⟨b, hb⟩
  exact ⟨a + b, by push_cast; linarith⟩

theorem add {x₁ x₂ y₁ y₂ : ℚ} (h₁ : PhaseEq x₁ y₁) (h₂ : PhaseEq x₂ y₂) :
    PhaseEq (x₁ + x₂) (y₁ + y₂) := by
  rcases h₁ with ⟨a, ha⟩
  rcases h₂ with ⟨b, hb⟩
  exact ⟨a + b, by push_cast; linarith⟩

end PhaseEq

/-- Complete division-free input for the four local phases and the collapsed
phase.  Every inverse used in the formulas has an explicit Bézout-style
specification.  In particular there is deliberately no coprimality assumption
between `m` and `mPrime`. -/
structure CollapseData where
  p : ℤ
  q : ℤ
  pPrime : ℤ
  qPrime : ℤ
  r : ℤ
  m : ℤ
  mPrime : ℤ
  k : ℤ
  w0 : ℤ
  h : ℤ
  hPrime : ℤ
  A : ℤ
  B : ℤ
  B0 : ℤ
  N : ℤ
  qInvP : ℤ
  rInvP : ℤ
  mInvP : ℤ
  pInvQ : ℤ
  rInvQ : ℤ
  mPrimeInvQ : ℤ
  qPrimeInvPPrime : ℤ
  rInvPPrime : ℤ
  mInvPPrime : ℤ
  pPrimeInvQPrime : ℤ
  rInvQPrime : ℤ
  mPrimeInvQPrime : ℤ
  rmInvP : ℤ
  rmPrimeInvQ : ℤ
  rInvC : ℤ
  mmPrimeInvP : ℤ
  crInvMPrime : ℤ
  hp : p ≠ 0
  hq : q ≠ 0
  hpPrime : pPrime ≠ 0
  hqPrime : qPrime ≠ 0
  hr : r ≠ 0
  hm : m ≠ 0
  hmPrime : mPrime ≠ 0
  hp_pPrime : IsCoprime p pPrime
  hp_q : IsCoprime p q
  hp_qPrime : IsCoprime p qPrime
  hpPrime_q : IsCoprime pPrime q
  hpPrime_qPrime : IsCoprime pPrime qPrime
  hq_qPrime : IsCoprime q qPrime
  hshift : mPrime = (m : ℤ) + k * r
  hB0 : (r : ℤ) * B0 = mPrime * w0 + 2
  hN : N = (h : ℤ) * pPrime * qPrime - hPrime * p * q
  hAmodP : CongruentSpec A (2 * h * pPrime * qInvP) p
  hAmodPPrime : CongruentSpec A (-2 * hPrime * p * qPrimeInvPPrime) pPrime
  hBmodQ : CongruentSpec B (2 * h * qPrime * pInvQ) q
  hBmodQPrime : CongruentSpec B (-2 * hPrime * q * pPrimeInvQPrime) qPrime
  hqInvP : InvModSpec q p qInvP
  hrInvP : InvModSpec r p rInvP
  hmInvP : InvModSpec m p mInvP
  hpInvQ : InvModSpec p q pInvQ
  hrInvQ : InvModSpec r q rInvQ
  hmPrimeInvQ : InvModSpec mPrime q mPrimeInvQ
  hqPrimeInvPPrime : InvModSpec qPrime pPrime qPrimeInvPPrime
  hrInvPPrime : InvModSpec r pPrime rInvPPrime
  hmInvPPrime : InvModSpec m pPrime mInvPPrime
  hpPrimeInvQPrime : InvModSpec pPrime qPrime pPrimeInvQPrime
  hrInvQPrime : InvModSpec r qPrime rInvQPrime
  hmPrimeInvQPrime : InvModSpec mPrime qPrime mPrimeInvQPrime
  hrmInvP : InvModSpec (r * m) (p * pPrime) rmInvP
  hrmPrimeInvQ : InvModSpec (r * mPrime) (q * qPrime) rmPrimeInvQ
  hrInvC : InvModSpec r (p * pPrime * q * qPrime) rInvC
  hmmPrimeInvP : InvModSpec (m * mPrime) (p * pPrime) mmPrimeInvP
  hcrInvMPrime : InvModSpec (p * pPrime * q * qPrime * r) mPrime crInvMPrime

/-- Sum of the four displayed local CRT-root rational phases. -/
def localPhase (d : CollapseData) : ℚ :=
  d.h * d.qInvP * d.rInvP * (d.w0 + 2 * d.mInvP) / d.p +
  d.h * d.pInvQ * d.rInvQ * (d.w0 + 2 * d.mPrimeInvQ) / d.q -
  d.hPrime * d.qPrimeInvPPrime * d.rInvPPrime *
      (d.w0 + 2 * d.mInvPPrime) / d.pPrime -
  d.hPrime * d.pPrimeInvQPrime * d.rInvQPrime *
      (d.w0 + 2 * d.mPrimeInvQPrime) / d.qPrime

/-- The intermediate phase after CRT fusion into moduli `P=pp'` and `Q=qq'`. -/
def fusedPhase (d : CollapseData) : ℚ :=
  d.A * d.rmInvP / (d.p * d.pPrime) +
  d.B * d.rmPrimeInvQ / (d.q * d.qPrime) +
  d.N * d.w0 * d.rInvC / (d.p * d.pPrime * d.q * d.qPrime)

/-- The claimed final double-reciprocity normal form. -/
def collapsedPhase (d : CollapseData) : ℚ :=
  d.A * d.k * d.mmPrimeInvP / (d.p * d.pPrime) -
  2 * d.N * d.crInvMPrime / d.mPrime +
  d.N * d.B0 / (d.p * d.pPrime * d.q * d.qPrime * d.mPrime)

/-- Proof-carrying interface for the two still-unproved phase identities.
No global inhabitant is supplied. -/
structure CollapseProofs (d : CollapseData) where
  fourLocalPhaseFuses : PhaseEq (localPhase d) (fusedPhase d)
  fusedPhaseDoubleReciprocity : PhaseEq (fusedPhase d) (collapsedPhase d)

/-- Conditional CRT-fusion accessor from explicitly supplied evidence. -/
theorem four_local_phase_fuses (d : CollapseData) (H : CollapseProofs d) :
    PhaseEq (localPhase d) (fusedPhase d) := H.fourLocalPhaseFuses

/-- Conditional reciprocity accessor from explicitly supplied evidence. -/
theorem fused_phase_double_reciprocity (d : CollapseData) (H : CollapseProofs d) :
    PhaseEq (fusedPhase d) (collapsedPhase d) := H.fusedPhaseDoubleReciprocity

/-- Conditional transitive assembly; this does not assert that `CollapseProofs`
is inhabited. -/
theorem double_reciprocity_collapse_verified (d : CollapseData) (H : CollapseProofs d) :
    PhaseEq (localPhase d) (collapsedPhase d) :=
  H.fourLocalPhaseFuses.trans H.fusedPhaseDoubleReciprocity

end TwinPrimeProject.NANC.DoubleReciprocityCollapse
