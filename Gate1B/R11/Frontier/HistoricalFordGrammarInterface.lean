/-
# Gate1B / R11 / Frontier : the historical realisation interface and the `Q₃`-provenance quotient

Append-only module of the residue-aware / generated-grammar delta.

Three things are recorded, all of them either exact algebra or an explicitly *uninhabited*
interface:

* **§19 Historical realisation.**  The repository's existing `RealFordGrammarCertificate`
  (`V11GeneratedExpression`) is reused, not re-created, and wrapped in
  `RealFordGrammarCertificateData`, which carries the exact extra data the research note demands
  (packet, normalisation, sign, multiplicity, parameter values, evaluation point).  **No
  inhabitant is constructed and no axiom is declared**: `RealFordGrammarObligation` is an open
  obligation.
* **§20 Weighted historical map.**  The source objects `W_hist`, `W_rec` and their difference
  `Δ = W_hist − W_rec`, with the exact linear identities — independent of any analytic smallness.
  The conditional consumer comparison is carried by the `Prop`-valued evidence interface
  `ConditionalConsumerComparison`, never inhabited.
* **§21 `Q₃` provenance quotient.**  `Q₃ Δ` is exactly the part of the historical/canonical
  difference invisible to every already removed residue-aware lower component, and the exact
  reassembly `E(Δ) = E(Δ − Q₃Δ) + E(Q₃Δ)` holds.  The analytic bound for `E(Q₃Δ)` is **not**
  proved.
-/
import Gate1B.R11.Frontier.ResidueAwareTopTelescoping
import Gate1B.R11.Frontier.GeneratedGrammarVariation

namespace Gate1B.R11.Frontier

open Finset TwinPrimeProject.Gate1BV11

/-! ## 1. The historical realisation obligation -/

/-- **The exact data required of a historical realisation certificate.**  It *contains* the
repository's `RealFordGrammarCertificate` (so nothing is re-created) together with the packet,
normalisation, sign, multiplicity, parameter values and evaluation point the research note
requires.

**This structure is deliberately left without an inhabitant.**  Its absence is the formal record
of the historical-provenance gap; it is not an axiom, and nothing downstream assumes it. -/
structure RealFordGrammarCertificateData where
  /-- The underlying grammar certificate for the literal historical coefficients. -/
  certificate : RealFordGrammarCertificate
  /-- The packet index of the historical source. -/
  packet : ℕ
  /-- The normalisation constant attached to the packet. -/
  normalisation : ℂ
  /-- The sign attached to the packet. -/
  sign : ℤ
  /-- The multiplicity with which the packet occurs. -/
  multiplicity : ℕ
  /-- The historical parameter values. -/
  parameters : List ℕ
  /-- The evaluation point at which the realisation is asserted. -/
  evaluationPoint : ℕ
  /-- The sign is a genuine sign. -/
  sign_spec : sign = 1 ∨ sign = -1
  /-- The multiplicity is positive. -/
  multiplicity_pos : 0 < multiplicity

/-- **The open historical-realisation obligation.**  Never inhabited in this repository. -/
def RealFordGrammarObligation : Prop := Nonempty RealFordGrammarCertificateData

/-- If the obligation were discharged, every certified slot would be generated — this is the
*only* consequence drawn from it anywhere in this layer. -/
theorem generated_of_realFordCertificate (data : RealFordGrammarCertificateData)
    (s : data.certificate.Slot) :
    FMPerronGenerated (data.certificate.fordCoefficient s) :=
  data.certificate.grammar.generated s

/-! ## 2. The weighted historical map -/

namespace ResidueProj

section Historical

variable {ι : Type*} [DecidableEq ι] [Fintype ι] {α : ι → Type*} [∀ i, Fintype (α i)]

/-- The historical/canonical difference `Δ = W_hist − W_rec`. -/
def histDelta (Whist Wrec : (∀ i, α i) → ℚ) : (∀ i, α i) → ℚ :=
  fun x => Whist x - Wrec x

omit [DecidableEq ι] [Fintype ι] [(i : ι) → Fintype (α i)] in
/-- Exact linear identity: the historical source is the reconstructed source plus `Δ`. -/
theorem histDelta_reassembly (Whist Wrec : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    Whist x = Wrec x + histDelta Whist Wrec x := by
  unfold histDelta; ring

/-- Exact consumer identity: the selected centered functional of the historical source is the
functional of the reconstructed source plus the functional of `Δ`. -/
theorem selectedCenteredFunctional_hist (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (Whist Wrec : (∀ i, α i) → ℚ) :
    selectedCenteredFunctional lam Ds Ns K Whist
      = selectedCenteredFunctional lam Ds Ns K Wrec
        + selectedCenteredFunctional lam Ds Ns K (histDelta Whist Wrec) := by
  rw [← selectedCenteredFunctional_add]
  refine congrArg _ ?_
  funext x
  exact histDelta_reassembly Whist Wrec x

/-! ## 3. The `Q₃` provenance quotient -/

omit [Fintype ι] in
/-- `Q₃ Δ` is invisible to every already removed residue-aware lower component. -/
theorem resAvg_Q3_histDelta_eq_zero {res : ∀ i, α i → ℕ} {k : ι} {l : List ι} (hl : l.Nodup)
    (hk : k ∈ l) (Whist Wrec : (∀ i, α i) → ℚ) :
    (fun x => resAvg res k (Q3 res l (histDelta Whist Wrec)) x) = fun _ => (0 : ℚ) :=
  resAvg_Q3_eq_zero hl hk _

omit [Fintype ι] in
/-- Exact provenance split of the historical difference: the part already owned by the removed
residue-aware components, and the invisible part `Q₃ Δ`. -/
theorem histDelta_provenance_split {res : ∀ i, α i → ℕ} (l : List ι)
    (Whist Wrec : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    histDelta Whist Wrec x
      = (histDelta Whist Wrec x - Q3 res l (histDelta Whist Wrec) x)
        + Q3 res l (histDelta Whist Wrec) x := by
  ring

/-- Exact consumer reassembly of the provenance split.  No analytic bound is asserted for either
summand. -/
theorem selectedCenteredFunctional_provenance {res : ∀ i, α i → ℕ} (lam : ℕ → ℚ)
    (Ds Ns : Finset ℕ) (K : (∀ i, α i) → ℕ → ℚ) (l : List ι)
    (Whist Wrec : (∀ i, α i) → ℚ) :
    selectedCenteredFunctional lam Ds Ns K (histDelta Whist Wrec)
      = selectedCenteredFunctional lam Ds Ns K
          (fun x => histDelta Whist Wrec x - Q3 res l (histDelta Whist Wrec) x)
        + selectedCenteredFunctional lam Ds Ns K (Q3 res l (histDelta Whist Wrec)) := by
  rw [← selectedCenteredFunctional_add]
  refine congrArg _ ?_
  funext x
  exact histDelta_provenance_split l Whist Wrec x

/-- **`ConditionalConsumerComparison`** — the current analytic report's conditional statement
that the selected consumer difference reduces to `E_λ*(Q₃ Δ)` plus an externally controlled
error.  This is an *evidence object*, a theorem parameter: it is never inhabited here and is not
an axiom. -/
structure ConditionalConsumerComparison {res : ∀ i, α i → ℕ} (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (l : List ι) (Whist Wrec : (∀ i, α i) → ℚ) (err : ℝ) : Prop where
  /-- The already-owned part of the difference is controlled at external analytic scope. -/
  ownedPartControlled :
    |((selectedCenteredFunctional lam Ds Ns K
        (fun x => histDelta Whist Wrec x - Q3 res l (histDelta Whist Wrec) x) : ℚ) : ℝ)| ≤ err

/-- The only consequence of the conditional comparison: the consumer difference is the
`Q₃`-provenance residual up to the externally controlled error. -/
theorem consumer_difference_reduces_to_Q3 {res : ∀ i, α i → ℕ} {lam : ℕ → ℚ} {Ds Ns : Finset ℕ}
    {K : (∀ i, α i) → ℕ → ℚ} {l : List ι} {Whist Wrec : (∀ i, α i) → ℚ} {err : ℝ}
    (h : ConditionalConsumerComparison (res := res) lam Ds Ns K l Whist Wrec err) :
    |((selectedCenteredFunctional lam Ds Ns K (histDelta Whist Wrec) : ℚ) : ℝ)
        - ((selectedCenteredFunctional lam Ds Ns K (Q3 res l (histDelta Whist Wrec)) : ℚ) : ℝ)|
      ≤ err := by
  have hsplit := selectedCenteredFunctional_provenance (res := res) lam Ds Ns K l Whist Wrec
  have hcast : ((selectedCenteredFunctional lam Ds Ns K (histDelta Whist Wrec) : ℚ) : ℝ)
      - ((selectedCenteredFunctional lam Ds Ns K (Q3 res l (histDelta Whist Wrec)) : ℚ) : ℝ)
      = ((selectedCenteredFunctional lam Ds Ns K
          (fun x => histDelta Whist Wrec x - Q3 res l (histDelta Whist Wrec) x) : ℚ) : ℝ) := by
    rw [hsplit]
    push_cast
    ring
  rw [hcast]
  exact h.ownedPartControlled

end Historical

end ResidueProj

end Gate1B.R11.Frontier
