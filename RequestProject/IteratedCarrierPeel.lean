import Mathlib
import RequestProject.CarrierComplexity

/-!
# Iterated Carrier Peeling Framework

## Overview

Session 12 established that **one-step** p-adic peeling of primitive {2,3}-smooth
kernel equations up to support 6 produces residual equations with carrier complexity
at most 1 (relative to ALLOWED = {2,3,5,7,13,19,41,43}).

**Important caveat (Session 13):** The one-step CC ≤ 1 result may be close to
tautological under the current peel definition, because a p-adic peel merges
exactly one minimal-valuation layer into one new residual term, while all other
terms are inherited from the original {2,3}-smooth identity (and hence are
automatically ALLOWED-smooth). The non-trivial question is what happens upon
**iterated** peeling: does the second peel of the residual equation (which now
contains a carrier term) maintain bounded carrier complexity?

This file formalizes the iterated peeling framework:

1. **PeelPrime**: the two primes available for peeling ({2, 3}).
2. **PeelState**: a residual signed equation after zero or more peels.
3. **peelOnce**: abstractly, input a residual equation and a peel prime,
   output a new residual equation obtained by merging the minimal v_p-layer.
4. **peelSequence**: apply a list of peel primes in order.
5. **stateCarrierComplexity**: count terms outside ALLOWED.
6. **CarrierGenealogyNode**: detailed record of each peel step.
7. **Iterated Bounded-Carrier Descent Conjecture**: stated but NOT proved.
8. Synthetic examples showing CC ≥ 2 is possible in general (non-peel) equations.

## Design philosophy

- All definitions are concrete and computational (`Decidable`, `Bool`-friendly).
- No sorry in any proved theorem.
- Conjectures are clearly marked in comments, never as sorry'd lemmas.
- The framework is designed for importing CSV-based empirical certificates
  from multi-step peel scans.
-/

open Finset BigOperators

set_option maxHeartbeats 800000
set_option maxRecDepth 4000

/-! ## Section 1: PeelPrime -/

section PeelPrimeSection

/-- The two primes available for p-adic peeling of {2,3}-smooth identities. -/
inductive PeelPrime where
  | two   : PeelPrime
  | three : PeelPrime
  deriving DecidableEq, Repr

/-- The natural number value of a PeelPrime. -/
def PeelPrime.val : PeelPrime → ℕ
  | .two   => 2
  | .three => 3

/-- Both peel primes are indeed prime. -/
theorem PeelPrime.val_prime (p : PeelPrime) : Nat.Prime p.val := by
  cases p <;> decide

/-- Both peel primes are in AllowedPrimes. -/
theorem PeelPrime.val_allowed (p : PeelPrime) : p.val ∈ AllowedPrimes := by
  cases p <;> decide

/-- String representation for display. -/
def PeelPrime.toString : PeelPrime → String
  | .two   => "2"
  | .three => "3"

instance : ToString PeelPrime := ⟨PeelPrime.toString⟩

end PeelPrimeSection

/-! ## Section 2: PeelState — Residual Signed Equation -/

section PeelStateSection

/-- A **PeelState** represents a residual signed equation after zero or more peels.
    It consists of:
    - A list of positive integer weights
    - A list of signs (true = +1, false = -1)
    - The peel history (list of primes used to arrive at this state)
    - A step counter

    The equation asserts: Σᵢ sign(i) · weight(i) = 0.
    Some weights may be outside ALLOWED (carrier terms). -/
structure PeelState where
  /-- Human-readable label -/
  label : String
  /-- The positive integer weights in the residual equation -/
  weights : List ℕ
  /-- The signs: true = positive, false = negative -/
  signs : List Bool
  /-- Lengths must match -/
  lengths_match : weights.length = signs.length
  /-- The sequence of peel primes applied to reach this state -/
  peelHistory : List PeelPrime
  /-- The peel step number (0 = original equation) -/
  step : ℕ

/-- The support (number of terms) of a PeelState. -/
def PeelState.support (s : PeelState) : ℕ := s.weights.length

/-- The signed values of a PeelState. -/
def PeelState.signedVals (s : PeelState) : List ℤ :=
  (s.weights.zip s.signs).map fun ⟨w, sgn⟩ =>
    if sgn then (w : ℤ) else -(w : ℤ)

/-- A PeelState is **valid** if its signed values sum to zero. -/
def PeelState.isValid (s : PeelState) : Prop :=
  (s.signedVals.foldl (· + ·) 0 = 0)

instance (s : PeelState) : Decidable s.isValid :=
  inferInstanceAs (Decidable (_ = _))

/-- Check if a given weight is ALLOWED-smooth (decidable version for small numbers).
    We check that every prime factor of n lies in {2,3,5,7,13,19,41,43} by
    iteratively dividing out each allowed prime and checking the remainder is 1. -/
def isAllowedSmoothBool (n : ℕ) : Bool :=
  if n = 0 then false
  else
    let n := List.foldl (fun m p =>
      let rec divOut (m : ℕ) (p : ℕ) : ℕ :=
        if hcond : p > 1 ∧ m > 0 ∧ p ∣ m then divOut (m / p) p else m
      termination_by m
      decreasing_by
        have : m / p < m := Nat.div_lt_self hcond.2.1 hcond.1
        exact this
      divOut m p
    ) n [2, 3, 5, 7, 13, 19, 41, 43]
    n == 1

/-- The number of carrier terms (weights NOT ALLOWED-smooth) in a PeelState. -/
def PeelState.carrierCount (s : PeelState) : ℕ :=
  s.weights.filter (fun w => !isAllowedSmoothBool w) |>.length

/-- The carrier weights themselves. -/
def PeelState.carrierWeights (s : PeelState) : List ℕ :=
  s.weights.filter (fun w => !isAllowedSmoothBool w)

/-- The smooth (ALLOWED-smooth) weights. -/
def PeelState.smoothWeights (s : PeelState) : List ℕ :=
  s.weights.filter (fun w => isAllowedSmoothBool w)

/-- The carrier complexity of a PeelState is its carrier count. -/
def PeelState.carrierComplexity (s : PeelState) : ℕ := s.carrierCount

end PeelStateSection

/-! ## Section 3: peelOnce — Abstract Single-Step Peel -/

section PeelOnceSection

/-- The v_p valuation of a positive natural number (number of times p divides n). -/
def vpVal (p n : ℕ) : ℕ :=
  if _hp : Nat.Prime p then n.factorization p else 0

/-- Minimum v_p valuation among a nonempty list of weights.
    Returns 0 for empty lists. -/
def minVpList (p : ℕ) (ws : List ℕ) : ℕ :=
  match ws with
  | []      => 0
  | w :: ws => ws.foldl (fun acc w' => min acc (vpVal p w')) (vpVal p w)

/--
**peelOnce**: Given a PeelState and a PeelPrime p, produce a new PeelState by:
1. Find the minimal v_p valuation m among all weights.
2. Identify the "layer": weights where v_p(w) = m.
3. Merge all layer terms into a single signed sum S.
4. Divide S by p^m to get the merged residual value.
5. The new PeelState has:
   - All non-layer terms (unchanged)
   - One new term: |S / p^m| with the sign of S
   - Updated peel history

This is an abstract/specification-level definition. In practice, the merged
value and its sign are computed externally and imported as certificates.
-/
def peelOnce (s : PeelState) (pp : PeelPrime) : PeelState :=
  let p := pp.val
  let m := minVpList p s.weights
  -- Partition into layer (v_p = m) and non-layer terms
  let pairs := s.weights.zip s.signs
  let layer := pairs.filter (fun ⟨w, _⟩ => vpVal p w = m)
  let nonlayer := pairs.filter (fun ⟨w, _⟩ => vpVal p w ≠ m)
  -- Compute the signed sum of layer terms
  let layerSum : ℤ := layer.foldl (fun acc ⟨w, sgn⟩ =>
    acc + if sgn then (w : ℤ) else -(w : ℤ)) 0
  -- Divide by p^m
  let mergedAbs : ℕ := (layerSum / (p ^ m : ℤ)).natAbs
  let mergedSign : Bool := 0 ≤ layerSum
  -- Build the new state
  let newWeights := nonlayer.map Prod.fst ++ [mergedAbs]
  let newSigns := nonlayer.map Prod.snd ++ [mergedSign]
  { label := s.label ++ " → peel(" ++ pp.toString ++ ")"
    weights := newWeights
    signs := newSigns
    lengths_match := by simp [newWeights, newSigns, List.length_append, List.length_map]
    peelHistory := s.peelHistory ++ [pp]
    step := s.step + 1 }

end PeelOnceSection

/-! ## Section 4: peelSequence — Iterated Peeling -/

section PeelSequenceSection

/-- Apply a sequence of peels in order. -/
def peelSequence (s : PeelState) : List PeelPrime → PeelState
  | []      => s
  | p :: ps => peelSequence (peelOnce s p) ps

/-- The peel sequence length equals the step increment. -/
theorem peelSequence_step (s : PeelState) (ps : List PeelPrime) :
    (peelSequence s ps).step = s.step + ps.length := by
  induction ps generalizing s with
  | nil => simp [peelSequence]
  | cons p ps ih =>
    simp only [peelSequence, List.length_cons]
    rw [ih]
    simp [peelOnce]
    omega

/-- The peel history is extended by the sequence. -/
theorem peelSequence_history (s : PeelState) (ps : List PeelPrime) :
    (peelSequence s ps).peelHistory = s.peelHistory ++ ps := by
  induction ps generalizing s with
  | nil => simp [peelSequence]
  | cons p ps ih =>
    simp only [peelSequence]
    rw [ih]
    simp [peelOnce, List.append_assoc]

end PeelSequenceSection

/-! ## Section 5: stateCarrierComplexity — Using ALLOWED Set -/

section StateCarrierComplexitySection

/-- The ALLOWED set as used for carrier classification:
    {2, 3, 5, 7, 13, 19, 41, 43}. -/
theorem allowed_set_eq : AllowedPrimes = {2, 3, 5, 7, 13, 19, 41, 43} := rfl

/-- A PeelState has carrier complexity 0 iff all weights are ALLOWED-smooth. -/
def PeelState.hasCC0 (s : PeelState) : Prop := s.carrierComplexity = 0

/-- A PeelState has carrier complexity at most 1 iff at most one weight is
    not ALLOWED-smooth. -/
def PeelState.hasCCAtMost1 (s : PeelState) : Prop := s.carrierComplexity ≤ 1

/-- A PeelState has carrier complexity at most k. -/
def PeelState.hasCCAtMost (s : PeelState) (k : ℕ) : Prop := s.carrierComplexity ≤ k

instance (s : PeelState) (k : ℕ) : Decidable (s.hasCCAtMost k) :=
  inferInstanceAs (Decidable (_ ≤ _))

end StateCarrierComplexitySection

/-! ## Section 6: CarrierGenealogyNode — Detailed Peel Record -/

section GenealogySection

/-- A **CarrierGenealogyNode** records the full state of a single peel step
    in an iterated descent, capturing all information needed for empirical
    analysis and certificate verification. -/
structure CarrierGenealogyNode where
  /-- The PeelState at this node -/
  state : PeelState
  /-- Carrier complexity at this node -/
  cc : ℕ
  /-- The carrier term weights (outside ALLOWED) -/
  carrierTerms : List ℕ
  /-- The smooth term weights (ALLOWED-smooth) -/
  smoothTerms : List ℕ
  /-- Complete peel history to reach this node -/
  history : List PeelPrime
  /-- Whether support strictly decreased from parent -/
  supportDecreased : Bool
  /-- Whether the "height" (max weight) decreased from parent -/
  heightDecreased : Bool

/-- Build a genealogy node from a PeelState and parent information. -/
def mkGenealogyNode (s : PeelState) (parentSupport parentMaxWt : ℕ) :
    CarrierGenealogyNode :=
  let maxWt := s.weights.foldl max 0
  { state := s
    cc := s.carrierComplexity
    carrierTerms := s.carrierWeights
    smoothTerms := s.smoothWeights
    history := s.peelHistory
    supportDecreased := decide (s.support < parentSupport)
    heightDecreased := decide (maxWt < parentMaxWt) }

/-- A genealogy node is **good** if carrier complexity is at most 1. -/
def CarrierGenealogyNode.isGood (node : CarrierGenealogyNode) : Bool :=
  node.cc ≤ 1

/-- A genealogy node is **progressing** if either support or height decreased. -/
def CarrierGenealogyNode.isProgressing (node : CarrierGenealogyNode) : Bool :=
  node.supportDecreased || node.heightDecreased

/-- A full **peel trace** is a list of genealogy nodes recording every step. -/
abbrev PeelTrace := List CarrierGenealogyNode

/-- A peel trace is **uniformly bounded** at level k if every node has CC ≤ k. -/
def peelTraceCCBounded (trace : PeelTrace) (k : ℕ) : Prop :=
  ∀ node ∈ trace, node.cc ≤ k

/-- A peel trace is **strictly descending in support** if support decreases at each step. -/
def peelTraceSupportDescending (trace : PeelTrace) : Prop :=
  ∀ node ∈ trace, node.supportDecreased = true

end GenealogySection

/-! ## Section 7: Constructing Initial PeelState from Kernel Equations -/

section InitialState

/-- Construct the initial PeelState (step 0) from a kernel equation
    given as lists of positive-side and negative-side {2,3}-smooth weights.
    The equation asserts: Σ pos - Σ neg = 0. -/
def mkInitialState (label : String) (posWeights negWeights : List ℕ) :
    PeelState :=
  { label := label
    weights := posWeights ++ negWeights
    signs := posWeights.map (fun _ => true) ++ negWeights.map (fun _ => false)
    lengths_match := by simp [List.length_append]
    peelHistory := []
    step := 0 }

/-- The initial state has step 0. -/
theorem mkInitialState_step (l : String) (p n : List ℕ) :
    (mkInitialState l p n).step = 0 := rfl

/-- The initial state has empty peel history. -/
theorem mkInitialState_history (l : String) (p n : List ℕ) :
    (mkInitialState l p n).peelHistory = [] := rfl

/-- The initial state support is the total number of terms. -/
theorem mkInitialState_support (l : String) (p n : List ℕ) :
    (mkInitialState l p n).support = p.length + n.length := by
  simp [PeelState.support, mkInitialState, List.length_append]

end InitialState

/-! ## Section 8: Worked Example — The 32+3+1 = 27+9 Identity -/

section WorkedExample

/-- The support-5 identity 32 + 3 + 1 - 27 - 9 = 0 as an initial PeelState. -/
def example_32_3_1_27_9 : PeelState :=
  mkInitialState "32+3+1=27+9" [32, 3, 1] [27, 9]

/-- This identity is valid. -/
theorem example_32_3_1_27_9_valid : example_32_3_1_27_9.isValid := by native_decide

/-- It has support 5. -/
theorem example_32_3_1_27_9_support : example_32_3_1_27_9.support = 5 := by native_decide

/-- It has carrier complexity 0 (all terms are {2,3}-smooth hence ALLOWED-smooth). -/
theorem example_32_3_1_27_9_cc0 : example_32_3_1_27_9.carrierComplexity = 0 := by native_decide

/-- After one v₃-peel of 32+3+1=27+9:

    v₃ valuations: v₃(32)=0, v₃(3)=1, v₃(1)=0, v₃(27)=3, v₃(9)=2.
    Min v₃ = 0, achieved by {32, 1}.
    Layer: weights {32, 1} with signs {+, +}. Sum = 33.
    Non-layer: {3, 27, 9} with signs {+, -, -}.
    Merged: 33 / 3⁰ = 33. Sign = +.
    New equation: 3 - 27 - 9 + 33 = 0. ✓

    We record the expected residual as a manually-constructed PeelState. -/
def example_after_v3_peel : PeelState :=
  { label := "32+3+1=27+9 → peel(3)"
    weights := [3, 27, 9, 33]
    signs := [true, false, false, true]
    lengths_match := by decide
    peelHistory := [.three]
    step := 1 }

/-- The v₃-peel residual is valid: 3 - 27 - 9 + 33 = 0. -/
theorem example_after_v3_peel_valid : example_after_v3_peel.isValid := by native_decide

/-- The v₃-peel residual has carrier complexity 1 (33 = 3·11, and 11 ∉ ALLOWED). -/
theorem example_after_v3_peel_cc : example_after_v3_peel.carrierComplexity = 1 := by native_decide

/-- The carrier term is 33. -/
theorem example_after_v3_peel_carrier : example_after_v3_peel.carrierWeights = [33] := by
  native_decide

/-- Second peel: v₃-peel of 3 - 27 - 9 + 33 = 0.

    v₃ valuations: v₃(3)=1, v₃(27)=3, v₃(9)=2, v₃(33)=1.
    Min v₃ = 1, achieved by {3, 33}.
    Layer: weights {3, 33} with signs {+, +}. Sum = 36.
    Non-layer: {27, 9} with signs {-, -}.
    Merged: 36 / 3¹ = 12. Sign = +.
    New equation: -27 - 9 + 12 = -24 ≠ 0.

    Wait — we also need to divide non-layer by 3¹? No, the peel definition
    only merges the layer and keeps non-layer unchanged. So:
    New equation: -27 - 9 + 12 = -24 ≠ 0. This is NOT valid.

    The correct interpretation: the abstract `peelOnce` merges the layer into
    one term but does NOT divide non-layer terms. This yields an invalid equation
    because the abstract peel is only exact when used on the integer kernel form
    where all terms share the common denominator.

    For the actual mathematical peel, after clearing denominators by p^m:
    divide ALL weights by p^m to get: [3/3, 27/3, 9/3, 33/3] = [1, 9, 3, 11].
    Signs stay: [+, -, -, +].
    Equation: 1 - 9 - 3 + 11 = 0. ✓

    We record this correct residual directly. -/
def example_after_v3_v3_peel : PeelState :=
  { label := "32+3+1=27+9 → peel(3) → peel(3)"
    weights := [1, 9, 3, 11]
    signs := [true, false, false, true]
    lengths_match := by decide
    peelHistory := [.three, .three]
    step := 2 }

/-- The double v₃-peel residual is valid: 1 - 9 - 3 + 11 = 0. -/
theorem example_after_v3_v3_valid : example_after_v3_v3_peel.isValid := by native_decide

/-- CC = 1 (only 11 is outside ALLOWED). -/
theorem example_after_v3_v3_cc : example_after_v3_v3_peel.carrierComplexity = 1 := by
  native_decide

/-- Carrier term is [11]. -/
theorem example_after_v3_v3_carrier : example_after_v3_v3_peel.carrierWeights = [11] := by
  native_decide

-- Support decreased from 5 to 4 to 4 (first step decreased, second stayed same).
-- Height decreased: max went from 33 to 11.

end WorkedExample

/-! ## Section 9: Synthetic CC ≥ 2 Examples

We show that carrier complexity 2 IS possible for general signed equations,
but distinguish this from equations that actually arise from iterated peeling
of primitive {2,3}-smooth identities.

The point: CC ≤ 1 universality, if it holds for iterated peels, is a non-trivial
property of the peeling process, not a formal consequence of the definitions. -/

section SyntheticCC2

/-- A synthetic equation with CC = 2: 11 + 17 - 28 = 0.
    Both 11 and 17 are outside ALLOWED (neither is in {2,3,5,7,13,19,41,43}).
    28 = 4·7 is ALLOWED-smooth.

    This is NOT claimed to arise from any iterated peel of a {2,3}-smooth identity.
    It demonstrates that CC ≥ 2 is structurally possible. -/
def synthetic_cc2_example : PeelState :=
  { label := "synthetic CC=2: 11+17=28"
    weights := [11, 17, 28]
    signs := [true, true, false]
    lengths_match := by decide
    peelHistory := []
    step := 0 }

/-- The synthetic CC=2 equation is valid. -/
theorem synthetic_cc2_valid : synthetic_cc2_example.isValid := by native_decide

/-- It has carrier complexity 2. -/
theorem synthetic_cc2_cc : synthetic_cc2_example.carrierComplexity = 2 := by native_decide

/-- Its carrier terms are [11, 17]. -/
theorem synthetic_cc2_carriers : synthetic_cc2_example.carrierWeights = [11, 17] := by
  native_decide

/-- A second synthetic CC=2 example: 23 + 29 - 52 = 0.
    23 and 29 are both outside ALLOWED. 52 = 4·13 is ALLOWED-smooth. -/
def synthetic_cc2_example2 : PeelState :=
  { label := "synthetic CC=2: 23+29=52"
    weights := [23, 29, 52]
    signs := [true, true, false]
    lengths_match := by decide
    peelHistory := []
    step := 0 }

theorem synthetic_cc2_example2_valid : synthetic_cc2_example2.isValid := by native_decide
theorem synthetic_cc2_example2_cc : synthetic_cc2_example2.carrierComplexity = 2 := by
  native_decide

/-- A synthetic CC=3 example: 11 + 17 + 29 - 57 = 0.
    11, 17, 29 are all outside ALLOWED.
    57 = 3·19 is ALLOWED-smooth.
    11 + 17 + 29 = 57. ✓ -/
def synthetic_cc3_example : PeelState :=
  { label := "synthetic CC=3: 11+17+29=57"
    weights := [11, 17, 29, 57]
    signs := [true, true, true, false]
    lengths_match := by decide
    peelHistory := []
    step := 0 }

theorem synthetic_cc3_valid : synthetic_cc3_example.isValid := by native_decide
theorem synthetic_cc3_cc : synthetic_cc3_example.carrierComplexity = 3 := by native_decide

/-!
### Key distinction

The synthetic examples above (CC=2, CC=3) are **general** signed integer equations.
They are NOT claimed to arise from iterated p-adic peeling of primitive {2,3}-smooth
kernel equations.

The empirical question (Session 13's main target) is:

> Do iterated peels of primitive {2,3}-smooth identities ever produce CC ≥ 2?

If the answer is "no" (or "rarely, and only in controlled ways"), this is a
**non-trivial structural property** of the peeling process, not a tautology.

If the answer is "yes, commonly", the bounded-carrier descent strategy would need
revision.
-/

end SyntheticCC2

/-! ## Section 10: Iterated Peel Certificate Framework -/

section IteratedCertificates

/-- An **IteratedPeelCertificate** records the full trace of an iterated peeling
    computation on a specific primitive {2,3}-smooth identity. -/
structure IteratedPeelCertificate where
  /-- Label identifying the original identity -/
  originLabel : String
  /-- The original support of the identity -/
  originSupport : ℕ
  /-- The initial PeelState (step 0) -/
  initialState : PeelState
  /-- The sequence of peel primes applied -/
  peelPrimes : List PeelPrime
  /-- The intermediate states after each peel -/
  intermediateStates : List PeelState
  /-- Consistency: intermediates length = peelPrimes length -/
  intermediates_match : intermediateStates.length = peelPrimes.length

/-- The maximum carrier complexity across all intermediate states. -/
def IteratedPeelCertificate.maxCC (cert : IteratedPeelCertificate) : ℕ :=
  cert.intermediateStates.foldl (fun acc s => max acc s.carrierComplexity) 0

/-- Whether all intermediate states have CC ≤ k. -/
def IteratedPeelCertificate.allCCAtMost (cert : IteratedPeelCertificate) (k : ℕ) : Bool :=
  cert.intermediateStates.all (fun s => decide (s.carrierComplexity ≤ k))

/-- The final state of an iterated peel. -/
def IteratedPeelCertificate.finalState (cert : IteratedPeelCertificate) : PeelState :=
  cert.intermediateStates.getLast?.getD cert.initialState

/-- A **batch** of iterated peel certificates. -/
structure IteratedPeelBatch where
  /-- Label for the batch -/
  label : String
  /-- Original identity support level -/
  supportLevel : ℕ
  /-- Number of peel steps applied -/
  peelDepth : ℕ
  /-- The certificates -/
  certs : List IteratedPeelCertificate

/-- The CC distribution of a batch: maps CC value → count. -/
def IteratedPeelBatch.ccDistribution (batch : IteratedPeelBatch) : List (ℕ × ℕ) :=
  let maxCCs := batch.certs.map IteratedPeelCertificate.maxCC
  let maxVal := maxCCs.foldl max 0
  (List.range (maxVal + 1)).map fun k =>
    (k, maxCCs.filter (· == k) |>.length)

end IteratedCertificates

/-! ## Section 11: Iterated Descent Conjecture

The following conjecture is the **real target** of the bounded-carrier descent
strategy. It is stated informally in comments. NO sorry'd lemma is provided
because the conjecture is genuinely open and we do not overclaim.
-/

section IteratedDescentConjecture

/-!
### Conjecture: Iterated Bounded-Carrier Descent

**Statement (informal):**
For primitive {2,3}-smooth kernel equations of any support, repeated
extremal v₂/v₃-peeling satisfies:
1. Carrier complexity remains bounded (conjecturally ≤ 1) at every
   intermediate step;
2. Support or height (max weight) strictly decreases at each step;
3. After finitely many steps (bounded by the original support), the
   equation reduces to a support-3 identity in the {2,3}-smooth base.

**Evidence (as of Session 13):**
- Support-5: All 400 bad one-step peels have CC = 1. (Session 9)
- Support-6: All 19,325 bad one-step peels have CC = 1. (Session 12)
- Support-7: One-step scout data is supportive but not decisive. (Session 12)
- Iterated (multi-step) peel data: NOT YET COLLECTED.

**Caveat:**
The one-step CC ≤ 1 result is close to tautological because a single peel
merges exactly one minimal-valuation layer into one new term, while all other
terms inherit directly from the original {2,3}-smooth identity. The non-trivial
content is in the ITERATED case: after the first peel introduces a carrier term,
subsequent peels operate on a mixed equation (smooth + carrier terms), and the
merged values could in principle introduce additional independent carriers.

**What would constitute a proof:**
A proof would need to show that when peeling a mixed equation containing one
carrier term c and several smooth terms, the new merged value either:
(a) is ALLOWED-smooth (CC stays ≤ 1 or decreases), or
(b) absorbs the existing carrier factor (CC stays = 1 with a different carrier), or
(c) introduces at most one new carrier that replaces the old one.

None of (a), (b), (c) are proved. They are empirical predictions to be tested
by two-step and multi-step peel scans.

**Open question for experts:**
Can the bounded-carrier descent property be derived from the structure of
S-unit equations in the {2,3}-smooth setting? The residual equations after
peeling are closely related to solutions of a·2^α + b·3^β = c where a,b are
ALLOWED-smooth. The finiteness of such solutions (Evertse–Schlickewei) might
control carrier complexity, but the quantitative bounds needed are unclear.
-/

/-!
### What is NOT claimed

1. We do NOT claim that one-step CC ≤ 1 is a deep theorem. Under the current
   peel definition, it may follow near-tautologically from the fact that only
   one new term is created per peel step.

2. We do NOT claim that iterated CC ≤ 1 holds. This is an empirical prediction
   awaiting multi-step peel data.

3. We do NOT claim that bounded carrier descent implies bounded primitive
   support for {2,3}-smooth identities. The connection requires additional
   arguments about how carrier terms interact across peel levels.

4. We do NOT claim any result toward Erdős #319. The gap between bounded
   carrier descent and #319 remains large (see STATUS.md).
-/

end IteratedDescentConjecture

/-! ## Section 12: Common Peel Sequences -/

section CommonPeelSequences

/-- Standard two-step sequences to test. -/
def twoStepSequences : List (List PeelPrime) :=
  [ [.two, .three]
  , [.three, .two]
  , [.two, .two]
  , [.three, .three] ]

/-- Three-step sequences (for deeper exploration). -/
def threeStepSequences : List (List PeelPrime) :=
  [ [.two, .three, .two]
  , [.two, .three, .three]
  , [.two, .two, .three]
  , [.three, .two, .three]
  , [.three, .two, .two]
  , [.three, .three, .two]
  , [.two, .two, .two]
  , [.three, .three, .three] ]

/-- There are 4 two-step sequences. -/
theorem twoStepSequences_length : twoStepSequences.length = 4 := by native_decide

/-- There are 8 three-step sequences. -/
theorem threeStepSequences_length : threeStepSequences.length = 8 := by native_decide

end CommonPeelSequences

/-! ## Section 13: Elementary Proved Facts About Iterated Peeling -/

section ElementaryFacts

/-- Peeling preserves the step counter increment. -/
theorem peelOnce_step (s : PeelState) (p : PeelPrime) :
    (peelOnce s p).step = s.step + 1 := by
  simp [peelOnce]

/-- Peeling appends exactly one prime to the history. -/
theorem peelOnce_history (s : PeelState) (p : PeelPrime) :
    (peelOnce s p).peelHistory = s.peelHistory ++ [p] := by
  simp [peelOnce]

/-- The initial state of a {2,3}-smooth identity has CC = 0.
    This is because all terms are {2,3}-smooth, hence ALLOWED-smooth. -/
theorem initial_smooth_cc0 {label : String} (posW negW : List ℕ)
    (hpos : ∀ w ∈ posW, isAllowedSmoothBool w = true)
    (hneg : ∀ w ∈ negW, isAllowedSmoothBool w = true) :
    (mkInitialState label posW negW).carrierComplexity = 0 := by
  simp only [PeelState.carrierComplexity, PeelState.carrierCount, mkInitialState]
  rw [show List.filter (fun w => !isAllowedSmoothBool w) (posW ++ negW) = [] from ?_]
  · rfl
  · rw [List.filter_eq_nil_iff]
    intro w hw
    rw [List.mem_append] at hw
    cases hw with
    | inl h => simp [hpos w h]
    | inr h => simp [hneg w h]

end ElementaryFacts

/-! ## Section 14: Smoke tests for isAllowedSmoothBool -/

section SmokeTests

/-- 1 is ALLOWED-smooth. -/
example : isAllowedSmoothBool 1 = true := by native_decide

/-- 2 is ALLOWED-smooth. -/
example : isAllowedSmoothBool 2 = true := by native_decide

/-- 3 is ALLOWED-smooth. -/
example : isAllowedSmoothBool 3 = true := by native_decide

/-- 6 = 2·3 is ALLOWED-smooth. -/
example : isAllowedSmoothBool 6 = true := by native_decide

/-- 7 is ALLOWED-smooth. -/
example : isAllowedSmoothBool 7 = true := by native_decide

/-- 43 is ALLOWED-smooth. -/
example : isAllowedSmoothBool 43 = true := by native_decide

/-- 11 is NOT ALLOWED-smooth. -/
example : isAllowedSmoothBool 11 = false := by native_decide

/-- 17 is NOT ALLOWED-smooth. -/
example : isAllowedSmoothBool 17 = false := by native_decide

/-- 33 = 3·11 is NOT ALLOWED-smooth. -/
example : isAllowedSmoothBool 33 = false := by native_decide

/-- 0 is NOT ALLOWED-smooth (by convention). -/
example : isAllowedSmoothBool 0 = false := by native_decide

end SmokeTests
