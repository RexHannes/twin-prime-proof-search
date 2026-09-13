/-
# Gate1B / R11 / Frontier : the prime-extrema realisation is constructible, and the
# historical-certificate obligation as stated is vacuous

Append-only module.  **Exact arithmetic only.**

The field audit of `RealFordGrammarCertificate` (`V11GeneratedExpression`) asked for.  Its fields
are

```
Slot, fordCoefficient, primeExtrema, extremaAtom, fordProvenance, grammar .
```

Two findings, both proved here:

1. **`primeExtrema` is no longer missing.**  `PrimeExtremaRealisation` demands a least and a
   greatest prime factor with their defining properties.  The earlier note recorded that this
   repository contains no such functions.  They exist in `Mathlib` (`Nat.minFac`,
   `Nat.primeFactors`), so the interface is *constructed* here:
   `fordPrimeExtremaRealisation`, and hence `Nonempty PrimeExtremaRealisation`.
   This is a genuine deterministic field, now discharged.

2. **The obligation as stated is vacuously satisfiable.**  `RealFordGrammarObligation` is
   `Nonempty RealFordGrammarCertificateData`, and taking `Slot := Empty` makes every remaining
   field vacuous.  So the obligation is *true* and certifies nothing about the historical
   coefficients — `realFordGrammarObligation_holds_vacuously` proves exactly this.  Nothing
   downstream may be closed by it, and nothing in this repository ever used it.

   The non-vacuous replacement is `RealFordGrammarObligationFor hist`: the certificate must
   supply, for each row of a *given* family of historical coefficients, a slot realising it.
   This proposition is **never inhabited** here and is not an axiom.

The pre-existing declarations are untouched; this module only adds.
-/
import Gate1B.R11.Frontier.HistoricalFordGrammarInterface

namespace Gate1B.R11.Frontier

open TwinPrimeProject.Gate1BV11

/-! ## 1. The greatest prime factor -/

/-- The greatest prime factor of `n`, with junk value `1` when `n` has none. -/
def greatestPrimeFactor (n : ℕ) : ℕ :=
  if h : (Nat.primeFactors n).Nonempty then (Nat.primeFactors n).max' h else 1

theorem greatestPrimeFactor_mem {n : ℕ} (hn : 2 ≤ n) :
    greatestPrimeFactor n ∈ Nat.primeFactors n := by
  have h : (Nat.primeFactors n).Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
  rw [greatestPrimeFactor, dif_pos h]
  exact Finset.max'_mem _ h

theorem greatestPrimeFactor_prime {n : ℕ} (hn : 2 ≤ n) : (greatestPrimeFactor n).Prime :=
  Nat.prime_of_mem_primeFactors (greatestPrimeFactor_mem hn)

theorem greatestPrimeFactor_dvd {n : ℕ} (hn : 2 ≤ n) : greatestPrimeFactor n ∣ n :=
  Nat.dvd_of_mem_primeFactors (greatestPrimeFactor_mem hn)

theorem le_greatestPrimeFactor {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime) (hpd : p ∣ n) :
    p ≤ greatestPrimeFactor n := by
  have hmem : p ∈ Nat.primeFactors n := Nat.mem_primeFactors.mpr ⟨hp, hpd, by omega⟩
  have h : (Nat.primeFactors n).Nonempty := ⟨p, hmem⟩
  rw [greatestPrimeFactor, dif_pos h]
  exact Finset.le_max' _ p hmem

/-! ## 2. The prime-extrema realisation, constructed -/

/-- **The prime-extrema realisation interface, inhabited.**  `P⁻ = Nat.minFac` and `P⁺` is the
greatest prime factor; all seven defining properties are proved. -/
def fordPrimeExtremaRealisation : PrimeExtremaRealisation where
  Pminus := Nat.minFac
  Pplus := greatestPrimeFactor
  Pminus_prime := fun _ hn => Nat.minFac_prime (by omega)
  Pminus_dvd := fun n _ => Nat.minFac_dvd n
  Pminus_least := fun _ _ _ hp hpd => Nat.minFac_le_of_dvd hp.two_le hpd
  Pplus_prime := fun _ hn => greatestPrimeFactor_prime hn
  Pplus_dvd := fun _ hn => greatestPrimeFactor_dvd hn
  Pplus_greatest := fun _ _ hn hp hpd => le_greatestPrimeFactor hn hp hpd

/-- The interface previously recorded as unrealisable in this repository **is** realisable. -/
theorem primeExtremaRealisation_inhabited : Nonempty PrimeExtremaRealisation :=
  ⟨fordPrimeExtremaRealisation⟩

/-! ## 3. The historical obligation as stated is vacuous -/

/-- A certificate with no slots: every remaining field is vacuous. -/
def emptySlotFordCertificate : RealFordGrammarCertificate where
  Slot := Empty
  fordCoefficient := fun s => s.elim
  primeExtrema := fordPrimeExtremaRealisation
  extremaAtom := fun s => s.elim
  fordProvenance := fun s => s.elim
  grammar :=
    { witness := fun s => s.elim
      witness_admissible := fun s => s.elim
      witness_eq := fun s => s.elim }

/-- The corresponding historical data record, with arbitrary bookkeeping values. -/
def emptySlotFordCertificateData : RealFordGrammarCertificateData where
  certificate := emptySlotFordCertificate
  packet := 0
  normalisation := 1
  sign := 1
  multiplicity := 1
  parameters := []
  evaluationPoint := 0
  sign_spec := Or.inl rfl
  multiplicity_pos := Nat.one_pos

/-- **Defect record.**  `RealFordGrammarObligation` is *true*: it is satisfied by the empty-slot
certificate.  Hence inhabiting it certifies nothing about the historical coefficients, and it must
not be used to close any downstream owner. -/
theorem realFordGrammarObligation_holds_vacuously : RealFordGrammarObligation :=
  ⟨emptySlotFordCertificateData⟩

/-- The empty-slot witness really has no slots. -/
theorem emptySlotFordCertificate_isEmpty : IsEmpty emptySlotFordCertificate.Slot :=
  inferInstanceAs (IsEmpty Empty)

/-! ## 4. The non-vacuous replacement -/

/-- **`RealFordGrammarObligationFor hist`** — the non-vacuous historical-realisation obligation:
a certificate together with, for every row `k` of a *given* family of historical coefficients, a
slot whose Ford coefficient is that row.  With a nonempty family this forces nonempty slots, so
the empty-slot witness does not satisfy it.

Never inhabited here, and not an axiom. -/
def RealFordGrammarObligationFor (hist : ℕ → ℕ → ℂ) : Prop :=
  ∃ data : RealFordGrammarCertificateData, ∃ e : ℕ → data.certificate.Slot,
    ∀ k n, data.certificate.fordCoefficient (e k) n = hist k n

/-- The replacement is genuinely stronger: it forces the slot type to be inhabited. -/
theorem nonempty_slot_of_realFordGrammarObligationFor {hist : ℕ → ℕ → ℂ}
    (h : RealFordGrammarObligationFor hist) :
    ∃ data : RealFordGrammarCertificateData, Nonempty data.certificate.Slot := by
  obtain ⟨data, e, -⟩ := h
  exact ⟨data, ⟨e 0⟩⟩

end Gate1B.R11.Frontier
