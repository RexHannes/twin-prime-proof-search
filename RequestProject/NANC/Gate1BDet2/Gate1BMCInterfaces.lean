import RequestProject.NANC.Gate1BDet2.DeltaExponentLedger

/-!
# Gate 1B / determinant-2 bank, Module 17: MC45 / delta-block interfaces

Every proposition in this module is an **interface**: an ordinary `Prop`-valued
definition which this development neither proves nor assumes.  **No `axiom` is
introduced**, and no interface is inhabited.  The only theorems are
deterministic transfers that take interfaces as *hypotheses*.

Interfaces declared here (all open):

`CorrectDeltaCharacterNormalization`, `LowCleanDeltaBlocksClosed`,
`MiddleCleanDeltaBlocksClosed`, `NearTopMC45Bound`,
`PrimeCharacterKaratsubaInput`, `PrimeMC45CovarianceTransfer`,
`NearPrimeCompositeTransfer`, `GeneralCompositeMC45Transfer` (the last two are
declared and never used as conclusions of any theorem),
`NearTopZeroDualIdentified`, `SourceExpectedTermIdentified`,
`Kappa4NormalizationMatched`, `FixedSwitchedPacketReassembled`,
`Gate1BAnalyticCoreClosed`, `Gate1BClosed`.

## The logical distinction that is respected here

A pointwise prime-modulus character estimate is **not** by itself a proof of the
mixed `(c, χ)`-covariance.  Accordingly the implication

  `PrimeCharacterKaratsubaInput → PrimeMC45CovarianceTransfer`

is **not** proved.  It is only available once the missing covariance argument is
supplied explicitly, as the additional hypothesis
`PrimeCovarianceCompatibility`; and `covariance_not_implied_by_pointwise`
exhibits data satisfying the pointwise interface and violating the covariance
target, so the omission is not an oversight.

Full Type II and twin primes are not stated in this module (they are declared,
and left uninhabited, in `Gate1BInterfaces`).
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace MC

/-! ## 1. Delta-block interfaces -/

/-- **EXTERNAL ANALYTIC INTERFACE.**  The delta-symbol character normalisation
is the correct one, up to an error `normError` bounded by `tol`. -/
def CorrectDeltaCharacterNormalization (normError tol : ℝ) : Prop := |normError| ≤ tol

/-- **EXTERNAL ANALYTIC INTERFACE.**  The low clean delta blocks are closed. -/
def LowCleanDeltaBlocksClosed (lowBlocks bound : ℝ) : Prop := |lowBlocks| ≤ bound

/-- **EXTERNAL ANALYTIC INTERFACE.**  The middle clean delta blocks are
closed. -/
def MiddleCleanDeltaBlocksClosed (middleBlocks bound : ℝ) : Prop := |middleBlocks| ≤ bound

/-- **EXTERNAL ANALYTIC INTERFACE.**  The near-top MC45 bound. -/
def NearTopMC45Bound (nearTop bound : ℝ) : Prop := |nearTop| ≤ bound

/-! ## 2. Prime-modulus / composite transfer interfaces -/

/-- **EXTERNAL ANALYTIC INTERFACE.**  A prime-modulus bilinear character-sum
input of Karatsuba type.  The algebraic coordinate change behind it is banked
in `PrimeCharacterReduction`; the *estimate* is not. -/
def PrimeCharacterKaratsubaInput (primeCharSum bound : ℝ) : Prop := |primeCharSum| ≤ bound

/-- **OPEN.**  The mixed `(c, χ)`-covariance transfer at prime moduli. -/
def PrimeMC45CovarianceTransfer (mixedSum bound : ℝ) : Prop := |mixedSum| ≤ bound

/-- **OPEN.**  Transfer from prime to near-prime composite moduli. -/
def NearPrimeCompositeTransfer (nearPrimeSum bound : ℝ) : Prop := |nearPrimeSum| ≤ bound

/-- **OPEN.**  Transfer to general composite moduli. -/
def GeneralCompositeMC45Transfer (compositeSum bound : ℝ) : Prop := |compositeSum| ≤ bound

/-- **THE MISSING COVARIANCE DATUM.**  The mixed `(c, χ)` sum differs from the
pointwise prime-character quantity by at most `tol`.  This is exactly the step
that a pointwise estimate does not supply; it is never proved here. -/
def PrimeCovarianceCompatibility (primeCharSum mixedSum tol : ℝ) : Prop :=
  |mixedSum - primeCharSum| ≤ tol

/-! ## 3. Source / packet interfaces -/

/-- **OPEN SOURCE INTERFACE.**  The near-top zero dual term has been identified
and is bounded by `tol`. -/
def NearTopZeroDualIdentified (zeroDual tol : ℝ) : Prop := |zeroDual| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The source expected term agrees with the banked
centering term up to `tol`. -/
def SourceExpectedTermIdentified (sourceExpected centering tol : ℝ) : Prop :=
  |sourceExpected - centering| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The `κ₄` normalisation has been matched, with
residual error at most `tol`. -/
def Kappa4NormalizationMatched (kappaError tol : ℝ) : Prop := |kappaError| ≤ tol

/-- **OPEN SOURCE INTERFACE.**  The fixed switched packet reassembles the total
out of the analytic core, the near-top zero dual, the expected-term discrepancy
and the `κ₄` residue, up to `rem`. -/
def FixedSwitchedPacketReassembled
    (total core zeroDual sourceExpected centering kappaError rem : ℝ) : Prop :=
  |total - (core + zeroDual + (sourceExpected - centering) + kappaError)| ≤ rem

/-! ## 4. Targets -/

/-- **UNINHABITED TARGET.**  The Gate-1B analytic core is closed. -/
def Gate1BAnalyticCoreClosed (core bound : ℝ) : Prop := |core| ≤ bound

/-- **UNINHABITED TARGET.**  Gate 1B is closed.  Nothing in this development
proves it. -/
def Gate1BClosed (gate1BTotal bound : ℝ) : Prop := |gate1BTotal| ≤ bound

/-! ## 5. Deterministic interface packages -/

/-- **Analytic-core package.**  If the Gate-1B core splits exactly as
low + middle + near-top + normalisation error, and each piece is controlled by
its interface, the core bound follows with the sum of the four tolerances.  None
of the premises is proved here. -/
theorem gate1BAnalyticCoreClosed_of_interfaces
    {core lowBlocks middleBlocks nearTop normError b₁ b₂ b₃ tol : ℝ}
    (hsplit : core = lowBlocks + middleBlocks + nearTop + normError)
    (hlow : LowCleanDeltaBlocksClosed lowBlocks b₁)
    (hmid : MiddleCleanDeltaBlocksClosed middleBlocks b₂)
    (htop : NearTopMC45Bound nearTop b₃)
    (hnorm : CorrectDeltaCharacterNormalization normError tol) :
    Gate1BAnalyticCoreClosed core (b₁ + b₂ + b₃ + tol) := by
  unfold Gate1BAnalyticCoreClosed LowCleanDeltaBlocksClosed
    MiddleCleanDeltaBlocksClosed NearTopMC45Bound
    CorrectDeltaCharacterNormalization at *
  rw [hsplit]
  have a1 : |lowBlocks + middleBlocks + nearTop + normError|
      ≤ |lowBlocks + middleBlocks + nearTop| + |normError| := abs_add_le _ _
  have a2 : |lowBlocks + middleBlocks + nearTop| ≤ |lowBlocks + middleBlocks| + |nearTop| :=
    abs_add_le _ _
  have a3 : |lowBlocks + middleBlocks| ≤ |lowBlocks| + |middleBlocks| := abs_add_le _ _
  linarith

/-- **Closure package.**  Given the analytic core bound, the near-top zero
dual, the source expected term, the `κ₄` normalisation and the packet
reassembly, the Gate-1B total is bounded by the sum of the tolerances.  This is
a pure triangle-inequality transfer: it proves none of its premises, and in
particular does not prove `Gate1BClosed`. -/
theorem gate1BClosed_of_interfaces
    {total core zeroDual sourceExpected centering kappaError b t₁ t₂ t₃ rem : ℝ}
    (hcore : Gate1BAnalyticCoreClosed core b)
    (hdual : NearTopZeroDualIdentified zeroDual t₁)
    (hsrc : SourceExpectedTermIdentified sourceExpected centering t₂)
    (hkappa : Kappa4NormalizationMatched kappaError t₃)
    (hpkt : FixedSwitchedPacketReassembled total core zeroDual sourceExpected centering
      kappaError rem) :
    Gate1BClosed total (b + t₁ + t₂ + t₃ + rem) := by
  unfold Gate1BClosed Gate1BAnalyticCoreClosed NearTopZeroDualIdentified
    SourceExpectedTermIdentified Kappa4NormalizationMatched
    FixedSwitchedPacketReassembled at *
  set S := core + zeroDual + (sourceExpected - centering) + kappaError with hS
  have h1 : |total| ≤ |total - S| + |S| := by
    have := abs_add_le (total - S) S
    simpa using this
  have h2 : |S| ≤ b + t₁ + t₂ + t₃ := by
    have a1 : |S| ≤ |core + zeroDual + (sourceExpected - centering)| + |kappaError| := by
      rw [hS]; exact abs_add_le _ _
    have a2 : |core + zeroDual + (sourceExpected - centering)|
        ≤ |core + zeroDual| + |sourceExpected - centering| := abs_add_le _ _
    have a3 : |core + zeroDual| ≤ |core| + |zeroDual| := abs_add_le _ _
    linarith
  linarith

/-- **Covariance transfer, with the missing datum supplied explicitly.**  A
pointwise prime-character input plus the covariance compatibility datum gives
the mixed transfer.  The compatibility datum is *not* proved anywhere. -/
theorem primeMC45CovarianceTransfer_of_input_of_compatibility
    {primeCharSum mixedSum b tol : ℝ}
    (hin : PrimeCharacterKaratsubaInput primeCharSum b)
    (hcov : PrimeCovarianceCompatibility primeCharSum mixedSum tol) :
    PrimeMC45CovarianceTransfer mixedSum (b + tol) := by
  unfold PrimeMC45CovarianceTransfer PrimeCharacterKaratsubaInput
    PrimeCovarianceCompatibility at *
  have : |mixedSum| ≤ |mixedSum - primeCharSum| + |primeCharSum| := by
    have := abs_add_le (mixedSum - primeCharSum) primeCharSum
    simpa using this
  linarith

/-! ## 6. Guards -/

/-- **Guard (the key logical distinction).**  A pointwise prime-character
estimate does not by itself deliver the mixed `(c, χ)`-covariance: here the
pointwise interface holds with bound `0` while the covariance target fails with
the same bound.  Hence the implication
`PrimeCharacterKaratsubaInput → PrimeMC45CovarianceTransfer` is unprovable
without the compatibility datum. -/
theorem covariance_not_implied_by_pointwise :
    PrimeCharacterKaratsubaInput 0 0 ∧ ¬ PrimeMC45CovarianceTransfer 1 0 := by
  constructor
  · unfold PrimeCharacterKaratsubaInput; norm_num
  · unfold PrimeMC45CovarianceTransfer; norm_num

/-- **Guard.**  The interfaces are not automatically true. -/
theorem nearTopMC45_not_automatic : ¬ NearTopMC45Bound 1 0 := by
  unfold NearTopMC45Bound; norm_num

/-- **Guard.**  Nor are they false: they are satisfiable, hence genuine open
inputs rather than vacuous or contradictory statements. -/
theorem nearTopMC45_satisfiable : NearTopMC45Bound 1 1 := by
  unfold NearTopMC45Bound; norm_num

/-- **Guard.**  The analytic core bound alone does not give Gate-1B closure at
the same numerical bound: without the zero-dual, expected-term, `κ₄` and packet
data the total is unconstrained. -/
theorem closure_needs_more_than_core :
    Gate1BAnalyticCoreClosed 0 1 ∧ ¬ Gate1BClosed 2 1 := by
  constructor
  · unfold Gate1BAnalyticCoreClosed; norm_num
  · unfold Gate1BClosed; norm_num

/-- **Guard.**  Nothing in this module inhabits `Gate1BClosed` unconditionally:
the closure predicate is a genuine constraint, false for suitable data. -/
theorem gate1BClosed_not_automatic : ¬ Gate1BClosed 1 0 := by
  unfold Gate1BClosed; norm_num

end MC
end Gate1BDet2
end TwinPrimeProject
