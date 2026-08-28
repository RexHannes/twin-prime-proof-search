import RequestProject.CurrentProgramme.LichtmanT18Socket

/-!
# Phase F · capacity arithmetic and the explicit J-ledger

## What is banked here

* `rational_signal_66_107` — the **exact rational** fact
  `66/107 − 8/13 = 2/1391 > 0`.

  ```
  ENDPOINT-66107-RATIONAL-SIGNAL45 : PROVED_ALGEBRAIC / CAPACITY_ONLY
  ```

  This is a rational-arithmetic signal **only**.  It is *not* labelled
  `ENDPOINT-66107-CAPACITY45 : PASS`: the headline `66/107` distribution
  exponent is not by itself a literal Theorem-1.8 endpoint capacity
  calculation, and no conversion to an `X`-exponent is asserted, because the
  conversion algebra has not been transcribed into this repository.

* `LichtmanT18Params`, `LichtmanT18JLedger` — algebraic **metadata** for the
  external theorem's `J²` terms.  The literal `J²` formulas are *not* written
  down: they are data fields (`jTerm1`, `jTerm2`), precisely so that a later
  source dictionary can substitute concrete parameters and have Lean verify the
  exponent arithmetic, without this file claiming to know the formulas.

* `endpointMixedLichtmanCapacity_of_inputs` — a purely logical/algebraic
  compiler: *if* a dictionary, *if* valid `b`/`tilde-b` norm data, and *if* the
  substituted J-ledger is below the physical target after every prefactor, then
  the capacity predicate holds.  **No antecedent is inhabited.**
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LichtmanCapacity

open LichtmanSocket

/-! ## 1. The rational signal -/

/-- **`ENDPOINT-66107-RATIONAL-SIGNAL45`.**  Exact rational arithmetic. -/
theorem rational_signal_66_107 : (66 : ℚ) / 107 - 8 / 13 = 2 / 1391 := by
  norm_num

/-- The signal is strictly positive. -/
theorem rational_signal_pos : (0 : ℚ) < 66 / 107 - 8 / 13 := by
  rw [rational_signal_66_107]; norm_num

/-- **Firewall.**  The rational signal is `CAPACITY_ONLY`.  Being a positive
rational gap is strictly weaker than being an endpoint capacity certificate:
positivity of a difference of two rationals carries no analytic content, as the
following trivially different pair shows. -/
theorem rational_signal_is_not_a_capacity_certificate :
    ∃ p q : ℚ, 0 < p - q ∧ p - q = 2 / 1391 ∧ (p, q) ≠ ((66 : ℚ) / 107, 8 / 13) := by
  refine ⟨1 + 66 / 107, 1 + 8 / 13, by norm_num, by norm_num, ?_⟩
  intro h
  have := congrArg Prod.fst h
  norm_num at this

/-! ## 2. The explicit parameter record and J-ledger -/

/-- Parameter record for the external theorem.  Metadata only. -/
structure LichtmanT18Params where
  /-- the parameter `a` -/
  a : ℕ
  /-- the fixed modulus `q₀` -/
  q0 : ℕ
  /-- the `C`-range -/
  C : ℝ
  /-- the `D`-range -/
  D : ℝ
  /-- the `N`-range -/
  N : ℝ
  /-- the `R`-range -/
  R : ℝ
  /-- the `S`-range -/
  S : ℝ
  /-- the exponent parameter `θ` -/
  theta : ℝ

/-- **Algebraic metadata for the `J²` ledger.**

The two `J²` terms are *data fields*, not guessed formulas: the external
theorem has not been transcribed here, so writing an explicit formula would be
a fabricated transcription.  What Lean *does* check is the arithmetic that a
later dictionary would need: `jSq` is the sum of the two terms, and the ledger
can be bounded termwise. -/
structure LichtmanT18JLedger where
  /-- the substituted parameters -/
  params : LichtmanT18Params
  /-- the first `J²` term, as a function of the parameters -/
  jTerm1 : LichtmanT18Params → ℝ
  /-- the second `J²` term, as a function of the parameters -/
  jTerm2 : LichtmanT18Params → ℝ
  /-- the total -/
  jSq : ℝ
  /-- the total is the sum of the two terms at the substituted parameters -/
  jSq_eq : jSq = jTerm1 params + jTerm2 params

/-- The ledger total. -/
def LichtmanT18JLedger.total (L : LichtmanT18JLedger) : ℝ :=
  L.jTerm1 L.params + L.jTerm2 L.params

theorem LichtmanT18JLedger.jSq_eq_total (L : LichtmanT18JLedger) :
    L.jSq = L.total := L.jSq_eq

/-- **Termwise ledger arithmetic.**  Kernel-checked; this is the only J-side
inference that is available without the external theorem. -/
theorem LichtmanT18JLedger.jSq_le_of_terms (L : LichtmanT18JLedger) {T₁ T₂ : ℝ}
    (h₁ : L.jTerm1 L.params ≤ T₁) (h₂ : L.jTerm2 L.params ≤ T₂) :
    L.jSq ≤ T₁ + T₂ := by
  rw [L.jSq_eq]; exact add_le_add h₁ h₂

/-! ## 3. The conditional capacity compiler -/

/-- The capacity predicate: a supplied bound is below the physical target. -/
def EndpointMixedLichtmanCapacitySatisfied (bound target : ℝ) : Prop :=
  bound ≤ target

/-- **UNINHABITED INPUT PACKAGE.**  Bundles the three open antecedents (a valid
dictionary, valid `b`/`tilde-b` norm data, a substituted J-ledger that clears
the physical target after every prefactor) together with the consistency pins
that stop the three from being about different objects. -/
structure EndpointMixedLichtmanInputs where
  /-- the proposed Lichtman source dictionary (OPEN) -/
  dict : LichtmanT18Dictionary
  /-- the `b` / `tilde-b` norm obligations (OPEN) -/
  norms : LichtmanT18CoeffNorms
  /-- the substituted J-ledger -/
  ledger : LichtmanT18JLedger
  /-- the prefactor accumulated before the J-ledger is applied -/
  prefactor : ℝ
  /-- the physical target -/
  target : ℝ
  /-- claimed bound for the first `J²` term -/
  T₁ : ℝ
  /-- claimed bound for the second `J²` term -/
  T₂ : ℝ
  /-- the prefactor is nonnegative -/
  prefactor_nonneg : 0 ≤ prefactor
  /-- the first term clears its bound -/
  term1 : ledger.jTerm1 ledger.params ≤ T₁
  /-- the second term clears its bound -/
  term2 : ledger.jTerm2 ledger.params ≤ T₂
  /-- the substituted ledger clears the physical target after the prefactor -/
  capacity : prefactor * (T₁ + T₂) ≤ target
  /-- consistency: the dictionary's coefficient family is the one the norms
  record is about -/
  bMatch : dict.b = norms.b
  /-- consistency: both are about the same theorem parameter `a` -/
  aMatch : dict.a = norms.a

/-- **CONDITIONAL CAPACITY COMPILER.**  Deterministic implication, no antecedent
inhabited. -/
theorem endpointMixedLichtmanCapacity_of_inputs (I : EndpointMixedLichtmanInputs) :
    EndpointMixedLichtmanCapacitySatisfied (I.prefactor * I.ledger.jSq) I.target := by
  have h := I.ledger.jSq_le_of_terms I.term1 I.term2
  have := mul_le_mul_of_nonneg_left h I.prefactor_nonneg
  exact this.trans I.capacity

/-- **Non-automaticity.**  The compiler consumes a genuine dictionary: from its
input package one can extract a `LichtmanT18Dictionary`, which is exactly the
open source obligation.  There is therefore no route to the capacity predicate
that bypasses the dictionary. -/
def EndpointMixedLichtmanInputs.requiresDictionary
    (I : EndpointMixedLichtmanInputs) : LichtmanT18Dictionary := I.dict

/-- **Non-vacuity.**  The capacity predicate is a real inequality: it fails for
explicit data, so the compiler is not proving something trivially true. -/
theorem capacity_not_automatic :
    ¬ EndpointMixedLichtmanCapacitySatisfied 1 0 := by
  unfold EndpointMixedLichtmanCapacitySatisfied
  norm_num

/-! ## 4. Small-`k` firewall (Phase G) -/

/-- **Small-`k` cost.**  Applying a scalar bound independently to each of
finitely many `k` costs exactly the number of `k`'s.  For the current small-`k`
endpoint, where `|k| ≤ log^C X`, that is a fixed polylogarithmic cost.

This route therefore does **not** require an abstract Hilbert lift, and
`LICHTMAN-T18-HILBERT-LIFT45` is recorded as *not currently required for
small `k`* — it is **not** banked. -/
theorem finite_k_sum_cost {ι : Type*} (Ks : Finset ι) (T : ι → ℂ) (B : ℝ)
    (h : ∀ k ∈ Ks, ‖T k‖ ≤ B) :
    ‖∑ k ∈ Ks, T k‖ ≤ (Ks.card : ℝ) * B := by
  calc ‖∑ k ∈ Ks, T k‖ ≤ ∑ k ∈ Ks, ‖T k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Ks, B := Finset.sum_le_sum h
    _ = (Ks.card : ℝ) * B := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Counterguard.**  The `#Ks` factor in `finite_k_sum_cost` is attained, so
the small-`k` route really does pay the number of `k`'s; linearity alone gives
nothing better, and in particular does not bank a free Hilbert lift. -/
theorem finite_k_cost_is_attained :
    ∃ (Ks : Finset ℕ) (T : ℕ → ℂ) (B : ℝ),
      (∀ k ∈ Ks, ‖T k‖ ≤ B) ∧ ‖∑ k ∈ Ks, T k‖ = (Ks.card : ℝ) * B := by
  refine ⟨{0, 1}, fun _ => 1, 1, ?_, ?_⟩ <;> norm_num

end LichtmanCapacity
end CurrentProgramme
end TwinPrimeProject
