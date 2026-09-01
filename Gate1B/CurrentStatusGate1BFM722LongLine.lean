import Gate1B.CurrentStatusGate1BFM722Kloosterman
import Gate1B.FM722LongLineDiophantine
import Gate1B.FM722OneAtomLongLine
import Gate1B.FM722AtomTypeInterface
import Gate1B.FM722SecondAtomHardOpening
import Gate1B.FM722SecondAtomSoftProjector
import Gate1B.FM722IteratedDeterminantTwo
import Gate1B.FM722LongLineLengthLedger
import Gate1B.FM722LongLineCenteredInterface
import Gate1B.FM722LongLineAnalyticInterface

/-!
# Gate 1B · FM722 **long-line determinant-2** status layer (append-only)

This layer **appends** the FM722 one-atom / two-atom long-line rows on top of
`LedgerGate1BFM722Kloosterman.full`, which is imported and never edited.  Every
older status file is untouched and remains visible in its own module
(`previous_layer_preserved`).

```
KERNEL-PROVED / SAFE (this layer)
  one-atom determinant line          : forward, converse, iff
  odd coprimality                    : odd y | b  =>  gcd(y, ell) = 1
  factor-2 case                      : separate; explicit even countermodel
  hard second opening                : (A y) c1 - ell q1 = -2  (BOXED)
  hard bijection                     : y | b0 + ell s  <->  s in s0 + y Z
  iterated determinant               : slope multiplies by the atom product
  symbolic slope / line-length ledger: rational identities only
  hard-opening capacity firewall     : threshold NOT inherited; line can shorten
  soft divisibility projector        : 1_{y|n} = (1/y) sum_h e_y(h n)
  zero / nonzero h split             : exact, separately typed, no owner
  hard vs soft type firewall         : A y  versus  A + frequency h mod y
  centering linearity                : T(arith - model) = T arith - T model
  atom metadata interface            : tagging type only

OPEN ANALYTIC (never inhabited, never promoted)
  FM722-LONGLINE-ONEATOM-AP-MOBIUSGAMMA45     (current research frontier)
  FM722-LONGLINE-TWOATOM-HARD-BOUND45
  FM722-LONGLINE-TWOATOM-SOFT-BOUND45

RESEARCH STATUS
  HSTAR-K0J0-GATEEXPORT : OPEN
  GLOBAL GATE1B         : OPEN
  TWIN PRIME            : OPEN
```

## Semantic guards recorded by this layer

* determinant preservation is **not** an analytic saving;
* a second-atom opening is **not** an improvement in line length;
* hard and soft openings are **not** interchangeable;
* an atom metadata interface is **not** a physical source realisation;
* a finite additive projector is **not** a cancellation theorem;
* the generated-DFT lane being deprioritised is **not** a Gate 1B failure, and
  the finite Kloosterman theorems of the previous layer are **not** marked
  false.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LedgerGate1BFM722LongLine

open Status

set_option maxRecDepth 40000

/-! ## The appended ledger -/

/-- The FM722 long-line determinant-2 layer, appended on top of
`LedgerGate1BFM722Kloosterman.full`. -/
def full : List LedgerEntry :=
  [ ⟨"FM722-TWOFACTOR-CENTERED-KLOOSTERMAN45", Status.provedAlgebraic,
     "BANKED / VALID (previous layer, preserved unchanged). Exact centred two-factor completion producing a complete Kloosterman sum. No analytic bound attached."⟩,
    ⟨"FM722-PRIMEWP-CRT-GENERATEDDFT-CROSSMOD-SPREAD45", Status.analyticOpen,
     "OPEN, NOT CONTROLLING. No interface inhabited, no bound claimed."⟩,
    ⟨"GENERATED-DFT-LANE45", Status.supersededAsControllingFrontier,
     "VALID REDUCTION; DEPRIORITISED / NONCLOSING UNDER CURRENT CERTIFICATES. This is NOT a refutation: every finite Kloosterman / centred-DFT theorem of the previous layer remains kernel-proved and is untouched."⟩,
    ⟨"FM722-LONGLINE-ONEATOM-DETERMINANT2-NORMALFORM45", Status.provedAlgebraic,
     "RESEARCH PASS at paper level; KERNEL-PROVED ALGEBRA where formalised: A b - ell q = -2 with q = q0 + A s, b = b0 + ell s, forward and (under A != 0, gcd(A,ell) = 1) converse. The one-atom datum A = pi z carries NO analytic field."⟩,
    ⟨"FM722-LONGLINE-ODD-COPRIMALITY45", Status.provedAlgebraic,
     "KERNEL-PROVED. On the determinant line, an odd divisor y of b satisfies gcd(y, ell) = 1. The factor-2 case is kept separate and is REFUTED by an explicit even countermodel (y = 2, ell = 2)."⟩,
    ⟨"FM722-LONGLINE-TWOATOM-HARD-DETERMINANT-PRESERVATION45", Status.provedAlgebraic,
     "KERNEL-PROVED. With y c1 = b0 + ell s0 and q1 = q0 + A s0: (A y) c1 - ell q1 = -2, and the whole opened fibre q = q1 + (A y) r, c = c1 + ell r carries determinant -2. Determinant preservation is NOT an analytic saving."⟩,
    ⟨"FM722-LONGLINE-TWOATOM-HARD-BIJECTION45", Status.provedAlgebraic,
     "KERNEL-PROVED. For gcd(y, ell) = 1 and one opening residue s0, y | b0 + ell s  <->  s in s0 + y Z. The hard reparametrisation is an exact bijective fibre change, not merely an implication."⟩,
    ⟨"FM722-LONGLINE-ITERATED-DETERMINANT245", Status.provedAlgebraic,
     "KERNEL-PROVED by induction on a finite list of opened atoms coprime to ell: the slope multiplies to A * prod(atoms) and the determinant stays -2. NO analytic usefulness is claimed."⟩,
    ⟨"FM722-LONGLINE-SYMBOLIC-LEDGER45", Status.provedFinite,
     "KERNEL-PROVED rational identities: twoAtomLineExp = oneAtomLineExp - yExp, twoAtomSlopeExp = oneAtomSlopeExp + yExp, line + slope = qExp. No asymptotic '~' is encoded as a theorem."⟩,
    ⟨"FM722-LONGLINE-HARD-CAPACITY-FIREWALL45", Status.provedFinite,
     "KERNEL-PROVED COUNTERMODELS. oneAtomSlopeExp < 1/3 does NOT imply twoAtomSlopeExp < 1/3, and for every threshold t there is a long one-atom line whose hard second opening has line exponent below t. A second-atom opening is NOT an improvement in line length."⟩,
    ⟨"FM722-LONGLINE-TWOATOM-SOFT-PROJECTOR45", Status.provedAlgebraic,
     "KERNEL-PROVED. 1_{y|n} = (1/y) sum_{h mod y} e_y(h n) in the C-valued normalisation, its application to n = b0 + ell s in factored phase form, the exact h = 0 / h != 0 split as separately named objects, and the exact source reconstruction of the soft compiler. A finite additive projector is NOT a cancellation theorem and NO analytic owner is assigned to either part."⟩,
    ⟨"FM722-LONGLINE-HARD-VS-SOFT-FIREWALL45", Status.provedAlgebraic,
     "KERNEL-PROVED. Hard and soft openings are distinct types: the hard slope is A y, the soft slope is A, and they differ whenever A != 0 and y != 1; the soft lane instead introduces exactly y frequencies h mod y. They are NOT interchangeable."⟩,
    ⟨"FM722-LONGLINE-CENTERING-LINEARITY45", Status.provedAlgebraic,
     "KERNEL-PROVED. Both openings are linear on the centred packet: T(arithmetic - model) = T(arithmetic) - T(model). Dropping the model before transforming is REFUTED by explicit countermodels for both lanes."⟩,
    ⟨"FM722-LONGLINE-ATOM-METADATA-INTERFACE45", Status.externallyAudited,
     "INTERFACE ONLY, NOT KERNEL-PROVED CONTENT. GammaAtomMetadata is a tagging type; the physical realisation PhysicalGammaAtomFactorisation is UNINHABITED here. An atom metadata interface is NOT a physical source realisation."⟩,
    ⟨"FM722-LONGLINE-TWOATOM-HARD-BOUND45", Status.analyticOpen,
     "OPEN. Recorded as the UNINHABITED interface FM722LongLineTwoAtomHardBound. Only the deterministic transport hardBound -> oneAtomBound (across the exact hard fibre presentation identity) is proved."⟩,
    ⟨"FM722-LONGLINE-TWOATOM-SOFT-BOUND45", Status.analyticOpen,
     "OPEN. Recorded as the UNINHABITED interface FM722LongLineTwoAtomSoftBound. Only the deterministic transport softBound -> oneAtomBound (across the exact projector identity) is proved."⟩,
    ⟨"FM722-LONGLINE-ONEATOM-AP-MOBIUSGAMMA45", Status.analyticOpen,
     "CURRENT RESEARCH ANALYTIC FRONTIER / OPEN. Recorded as the UNINHABITED interface FM722LongLineOneAtomMobiusGammaBound. Never inhabited, never derived."⟩,
    ⟨"FM722-LONGLINE-TWOATOM-STRUCTURAL-CHILD45", Status.open_,
     "NEXT STRUCTURAL CHILD: two-atom hard/soft opening preserving the physical +2 / determinant geometry. The determinant algebra is banked here; the analytic child is open."⟩,
    ⟨"HSTAR-K0J0-GATEEXPORT", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"GLOBAL-GATE1B", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"TWIN-PRIME", Status.open_, "OPEN / NOT PROMOTED."⟩,
    ⟨"GATE1B", Status.open_, "OPEN."⟩ ]

/-! ## Honesty invariants -/

/-- **No row of this layer is closed.**  Nothing is promoted. -/
theorem no_closed_rows : ∀ e ∈ full, e.status ≠ Status.closed := by decide

/-- Every row of this layer is honest. -/
theorem ledger_is_honest : ∀ e ∈ full, e.honest := by
  intro e he hc
  exact absurd hc (no_closed_rows e he)

/-- **The analytic frontier label of this layer.** -/
theorem current_analytic_frontier :
    ∃ e ∈ full,
      e.label = "FM722-LONGLINE-ONEATOM-AP-MOBIUSGAMMA45" ∧
      e.status = Status.analyticOpen := by decide

/-- Every analytic row of this layer is an open obligation. -/
theorem analytic_rows_open :
    ∀ e ∈ full,
      (e.label = "FM722-LONGLINE-ONEATOM-AP-MOBIUSGAMMA45" ∨
        e.label = "FM722-LONGLINE-TWOATOM-HARD-BOUND45" ∨
        e.label = "FM722-LONGLINE-TWOATOM-SOFT-BOUND45" ∨
        e.label = "FM722-PRIMEWP-CRT-GENERATEDDFT-CROSSMOD-SPREAD45") →
      e.status.isOpenObligation = true := by decide

/-- Every exact row of this layer is a kernel-proved status. -/
theorem new_exact_rows_kernel_proved :
    ∀ e ∈ full,
      (e.label = "FM722-LONGLINE-ONEATOM-DETERMINANT2-NORMALFORM45" ∨
        e.label = "FM722-LONGLINE-ODD-COPRIMALITY45" ∨
        e.label = "FM722-LONGLINE-TWOATOM-HARD-DETERMINANT-PRESERVATION45" ∨
        e.label = "FM722-LONGLINE-TWOATOM-HARD-BIJECTION45" ∨
        e.label = "FM722-LONGLINE-ITERATED-DETERMINANT245" ∨
        e.label = "FM722-LONGLINE-SYMBOLIC-LEDGER45" ∨
        e.label = "FM722-LONGLINE-HARD-CAPACITY-FIREWALL45" ∨
        e.label = "FM722-LONGLINE-TWOATOM-SOFT-PROJECTOR45" ∨
        e.label = "FM722-LONGLINE-HARD-VS-SOFT-FIREWALL45" ∨
        e.label = "FM722-LONGLINE-CENTERING-LINEARITY45") →
      e.status.isKernelProved = true := by decide

/-- **The atom metadata row is interface level only.** -/
theorem atom_metadata_row_not_kernel_proved :
    ∃ e ∈ full, e.label = "FM722-LONGLINE-ATOM-METADATA-INTERFACE45" ∧
      e.status.isKernelProved = false := by decide

/-- **The generated-DFT lane is deprioritised, not refuted.** -/
theorem generated_dft_lane_not_false :
    ∃ e ∈ full, e.label = "GENERATED-DFT-LANE45" ∧
      e.status = Status.supersededAsControllingFrontier ∧
      e.status ≠ Status.falseRoute := by decide

/-- **The previous centred-Kloosterman row is preserved as banked.** -/
theorem kloosterman_row_still_banked :
    ∃ e ∈ full, e.label = "FM722-TWOFACTOR-CENTERED-KLOOSTERMAN45" ∧
      e.status.isKernelProved = true := by decide

/-- **HSTAR K0J0 GateExport is not promoted.** -/
theorem hstar_gateexport_open :
    ∃ e ∈ full, e.label = "HSTAR-K0J0-GATEEXPORT" ∧
      e.status.isOpenObligation = true := by decide

/-- **Global Gate 1B is not promoted.** -/
theorem global_gate1B_open :
    ∃ e ∈ full, e.label = "GLOBAL-GATE1B" ∧ e.status.isOpenObligation = true := by decide

/-- **Twin primes are not promoted.** -/
theorem twin_prime_open :
    ∃ e ∈ full, e.label = "TWIN-PRIME" ∧ e.status.isOpenObligation = true := by decide

/-- **The previous layers are preserved unchanged.** -/
theorem previous_layer_preserved :
    (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BFM722Kloosterman.full ∧
      (⟨"GATE1B", Status.open_, "OPEN."⟩ : LedgerEntry) ∈
        LedgerGate1BHStarTwoAnchor.full := by
  exact ⟨by decide, by decide⟩

end LedgerGate1BFM722LongLine
end CurrentProgramme
end TwinPrimeProject
