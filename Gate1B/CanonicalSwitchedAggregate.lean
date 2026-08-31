import Gate1B.CanonicalR9Comparison

/-!
# Gate 1B · canonical switched aggregate and the `R_can = 0` identity

**Exact finite algebra only.**

## Contents

* §1 the **switched-modulus type firewall**: `SwitchedModulus` and
  `MajorArcDenominator` are distinct structures, with no coercion between
  them; any identification must be supplied explicitly
  (`switched_local_identification_is_a_choice`);
* §2 the `λ₃` source coefficient in the **ordered divisor-pair** form, its
  equality with the `divisors` form, and an explicit witness that ordered
  multiplicity is retained;
* §3 the canonical switched expected coefficient `ETreeCanSw` over the actual
  finite source set `B_q`, and the canonical aggregate `ZTreeCan`;
* §4 the boxed tautological identity `RCan = 0`
  (`canonicalSwitchedResidual_eq_zero`), together with the explicit statement
  that it holds **only** because the canonical comparison is defined from the
  same `b9Can`, and a countermodel showing that an arbitrary expected
  coefficient does **not** give a vanishing residual;
* §5 the **historical `E` firewall**: `E_hist` is an abstract parameter, is
  never defined by `b9Can`, and is provably not identified with the canonical
  expected coefficient.

The canonical comparison sequence `b9Can` used here is the one defined in
`Gate1B.CanonicalR9Comparison`; nothing in this module estimates it.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CanonicalSwitched

open Finset ArithmeticFunction

/-! ## 1. Switched modulus versus local major-arc denominator -/

/-- A **switched** modulus `q = d·ℓ`.  This is *not* the local major-arc
denominator. -/
structure SwitchedModulus where
  /-- The underlying integer. -/
  val : ℕ
  deriving DecidableEq, Repr

/-- A **local major-arc denominator**.  This is *not* a switched modulus. -/
structure MajorArcDenominator where
  /-- The underlying integer. -/
  val : ℕ
  deriving DecidableEq, Repr

/-- A switched modulus built from an ordered factorisation `q = d·ℓ`. -/
def switchedOf (d ell : ℕ) : SwitchedModulus := ⟨d * ell⟩

@[simp] theorem switchedOf_val (d ell : ℕ) : (switchedOf d ell).val = d * ell := rfl

/-- **Type firewall.**  No coercion `SwitchedModulus → MajorArcDenominator` is
declared anywhere.  If a consumer wants one, it has to *choose* it, and the
value-preserving choice is unique — i.e. identification is an explicit act,
never an implicit one. -/
theorem switched_local_identification_is_a_choice
    (f : SwitchedModulus → MajorArcDenominator)
    (hf : ∀ q, (f q).val = q.val) :
    f = fun q => ⟨q.val⟩ := by
  funext q
  cases h : f q with
  | mk v =>
    have hv := hf q
    rw [h] at hv
    exact congrArg MajorArcDenominator.mk hv

/-- The two wrappers are genuinely different types with independent values: a
switched modulus never carries local-denominator information. -/
theorem switched_val_injective {q q' : SwitchedModulus} (h : q.val = q'.val) : q = q' := by
  cases q; cases q'; simpa using h

/-! ## 2. The `λ₃` source coefficient, ordered divisor pairs -/

/-- `λ₃(U,V,q) = ∑_{dℓ = q, d > U, ℓ > V} μ(d) Λ(ℓ)`, in the **ordered
divisor-pair** form: the sum runs over `Nat.divisorsAntidiagonal`, so the
ordered pair multiplicity is retained.

(The real-valued analogue of this formula also occurs in the top-level module
`VaughanPacketAlgebra`, which lies outside the `Gate1B` library; the complex
form used by the switched aggregate is stated here and proved equal to the
`divisors` form.) -/
noncomputable def lambda3Sw (U V q : ℕ) : ℂ :=
  ∑ p ∈ q.divisorsAntidiagonal,
    if U < p.1 ∧ V < p.2 then (ArithmeticFunction.moebius p.1 : ℂ) *
      (ArithmeticFunction.vonMangoldt p.2 : ℂ) else 0

/-- The ordered-pair form agrees with the `divisors` form `d ↦ (d, q/d)`. -/
theorem lambda3Sw_eq_divisors_form (U V q : ℕ) :
    lambda3Sw U V q =
      ∑ d ∈ q.divisors,
        if U < d ∧ V < q / d then (ArithmeticFunction.moebius d : ℂ) *
          (ArithmeticFunction.vonMangoldt (q / d) : ℂ) else 0 := by
  rw [lambda3Sw]
  exact Nat.sum_divisorsAntidiagonal
    (fun d l => if U < d ∧ V < l then (ArithmeticFunction.moebius d : ℂ) *
      (ArithmeticFunction.vonMangoldt l : ℂ) else 0)

/-- **Ordered multiplicity retained.**  For `q = 6` there are four ordered
divisor pairs, not two unordered ones. -/
theorem divisorsAntidiagonal_ordered_six :
    (Nat.divisorsAntidiagonal 6).card = 4 := by decide

/-! ## 3. The canonical switched expected coefficient and aggregate -/

variable (b : ArithmeticFunction ℂ) (B : ℕ → Finset ℕ)

/-- `ETreeCanSw(q) := ∑_{r ∈ B_q} b9Can(q·r − 2)`, over the **actual finite
source set** `B_q`.  The subtraction is `ℕ`-subtraction, so the shift is the
literal fixed shift `2` (and the terms with `q·r < 2` read the coefficient at
a truncated argument; no averaging over the shift occurs anywhere). -/
noncomputable def ETreeCanSw (q : SwitchedModulus) : ℂ :=
  ∑ r ∈ B q.val, b (q.val * r - 2)

/-- The canonical switched aggregate
`ZTreeCan := ∑_q λ_q · ETreeCanSw(q)`, for a source coefficient `lam`.  The
intended instance is `lam = λ₃(U,V,·)`. -/
noncomputable def ZTreeCan (lam : ℕ → ℂ) (Q : Finset SwitchedModulus) : ℂ :=
  ∑ q ∈ Q, lam q.val * ETreeCanSw b B q

/-- The canonical **comparison** aggregate, defined from the *same* `b9Can`. -/
noncomputable def ZTreeCanExpected (lam : ℕ → ℂ) (Q : Finset SwitchedModulus) : ℂ :=
  ∑ q ∈ Q, lam q.val * ETreeCanSw b B q

/-- The canonical switched aggregate with the actual `λ₃` source coefficient. -/
noncomputable def ZTreeCanLambda3 (U V : ℕ) (Q : Finset SwitchedModulus) : ℂ :=
  ZTreeCan b B (lambda3Sw U V) Q

/-- The canonical switched residual. -/
noncomputable def RCan (lam : ℕ → ℂ) (Q : Finset SwitchedModulus) : ℂ :=
  ZTreeCan b B lam Q - ZTreeCanExpected b B lam Q

/-- **BOXED (§15 of the specification).**  `RCan = 0`.

This is exact and kernel-safe, and it is **tautological**: it holds precisely
because the canonical comparison aggregate is *defined* from the same `b9Can`
as the canonical source aggregate.  It transports no analytic information. -/
theorem canonicalSwitchedResidual_eq_zero (lam : ℕ → ℂ) (Q : Finset SwitchedModulus) :
    RCan b B lam Q = 0 := sub_self _

/-- **Honesty firewall.**  Replace the canonical expected coefficient by an
arbitrary one and the residual is no longer zero: `RCan = 0` is a statement
about the canonical definition, not about the source. -/
theorem residual_ne_zero_for_arbitrary_expected :
    ∃ (b : ArithmeticFunction ℂ) (B : ℕ → Finset ℕ) (lam : ℕ → ℂ)
      (Q : Finset SwitchedModulus) (E' : SwitchedModulus → ℂ),
      ZTreeCan b B lam Q - ∑ q ∈ Q, lam q.val * E' q ≠ 0 := by
  classical
  refine ⟨0, fun _ => ∅, fun _ => 1, {⟨2⟩}, fun _ => -1, ?_⟩
  simp [ZTreeCan, ETreeCanSw]

/-! ## 4. The historical `E` firewall -/

/-- The historical expected coefficient is an **abstract parameter**: it is
never defined by `b9Can`, and no historical/canonical equivalence is encoded.
Its status in the ledger is `SOURCE PIN`. -/
noncomputable def ZTreeHistorical (lam : ℕ → ℂ) (Q : Finset SwitchedModulus)
    (Ehist : SwitchedModulus → ℂ) : ℂ :=
  ∑ q ∈ Q, lam q.val * Ehist q

/-- **Firewall.**  The historical aggregate is not identified with the
canonical one: there are data for which they differ. -/
theorem historical_not_identified_with_canonical :
    ∃ (b : ArithmeticFunction ℂ) (B : ℕ → Finset ℕ) (lam : ℕ → ℂ)
      (Q : Finset SwitchedModulus) (Ehist : SwitchedModulus → ℂ),
      ZTreeHistorical lam Q Ehist ≠ ZTreeCan b B lam Q := by
  classical
  refine ⟨0, fun _ => ∅, fun _ => 1, {⟨2⟩}, fun _ => 1, ?_⟩
  simp [ZTreeHistorical, ZTreeCan, ETreeCanSw]

end CanonicalSwitched
end CurrentProgramme
end TwinPrimeProject
