import Gate1B.FM722LongLineCenteredInterface

/-!
# Gate 1B · FM722 · **long-line analytic interfaces** (all UNINHABITED)

Three analytic interfaces and the deterministic conditional reassembly
theorems that consume them.

* `FM722LongLineOneAtomMobiusGammaBound` — the *current research analytic
  residual* `FM722-LONGLINE-ONEATOM-AP-MOBIUSGAMMA45`;
* `FM722LongLineTwoAtomHardBound` — the two-atom hard-opened analogue;
* `FM722LongLineTwoAtomSoftBound` — the two-atom soft-projector analogue.

**No axiom, no `sorry`, no default inhabitant.**  Nothing in this bank
constructs a term of any of these three types.  Only the deterministic
implications

```
  hardBound → oneAtomBound        (via the exact hard fibre presentation)
  softBound → oneAtomBound        (via the exact soft projector identity)
```

are proved, and both are pure transports of an inequality across an *exact*
identity.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

/-! ## 1. The finite long-line packet -/

/-- A finite long-line packet: two-atom incidence data, an arithmetic weight,
a model weight, and the positive natural presentation of the second atom.
Purely finite; there is no analytic field. -/
structure LongLinePacket where
  /-- The incidence data of the line. -/
  I : TwoAtomIncidenceData
  /-- The arithmetic weight along the line. -/
  weight : ℤ → ℂ
  /-- The principal / model weight along the line. -/
  model : ℤ → ℂ
  /-- The second atom as a positive natural number. -/
  yNat : ℕ
  /-- Positivity of the second atom. -/
  yPos : 0 < yNat
  /-- Compatibility with the integer datum. -/
  yNat_eq : (yNat : ℤ) = I.y

namespace LongLinePacket

variable (P : LongLinePacket)

instance : NeZero P.yNat := ⟨P.yPos.ne'⟩

/-- The centred integrand of the packet. -/
noncomputable def integrand : ℤ → ℂ := centred P.weight P.model

/-- The size parameter of the packet (the number of line parameters). -/
def size : ℝ := (P.I.params.card : ℝ)

/-- **The one-atom value**: the divisibility-restricted centred sum along the
line.  This is the quantity of the open analytic residual. -/
noncomputable def oneAtomValue : ℂ :=
  ∑ s ∈ P.I.params, (if ((P.yNat : ℤ) ∣ P.I.bAt s) then P.integrand s else 0)

/-- **The soft value**: the additive-projector expansion of the same quantity. -/
noncomputable def softValue : ℂ :=
  softTransform P.I.params P.yNat P.I.bAt P.integrand

/-- **The hard value** along a fibre presentation `(s₀ , R)`. -/
noncomputable def hardValue (s0 : ℤ) (R : Finset ℤ) : ℂ :=
  hardTransform R s0 (P.yNat : ℤ) P.integrand

/-- `(s₀ , R)` is a **hard fibre presentation** of the packet: `s₀` is an
opening residue and `R` indexes exactly the admissible line parameters. -/
def IsHardPresentation (s0 : ℤ) (R : Finset ℤ) : Prop :=
  ((P.yNat : ℤ) ∣ P.I.bAt s0) ∧
    P.I.params.filter (fun s => ((P.yNat : ℤ) ∣ P.I.bAt s))
      = R.image (fun r => s0 + (P.yNat : ℤ) * r)

end LongLinePacket

/-! ## 2. The two exact reconstruction identities -/

open LongLinePacket

/-- **Exact soft reconstruction.**  The soft projector expansion *is* the
one-atom value; no estimate is involved. -/
theorem softValue_eq_oneAtomValue (P : LongLinePacket) :
    P.softValue = P.oneAtomValue := by
  simp only [LongLinePacket.softValue, LongLinePacket.oneAtomValue, softTransform]
  exact (compileSoft_reconstruction P.I P.yNat P.integrand).symm

/-- **Exact hard reconstruction.**  Under a hard fibre presentation, the hard
fibre sum *is* the one-atom value. -/
theorem hardValue_eq_oneAtomValue (P : LongLinePacket) (s0 : ℤ) (R : Finset ℤ)
    (hpres : P.IsHardPresentation s0 R) : P.hardValue s0 R = P.oneAtomValue := by
  classical
  have hy : ((P.yNat : ℤ)) ≠ 0 := by
    exact_mod_cast P.yPos.ne'
  have hinj : Set.InjOn (fun r : ℤ => s0 + (P.yNat : ℤ) * r) R := by
    intro a _ b _ hab
    have : (P.yNat : ℤ) * a = (P.yNat : ℤ) * b := by simpa using hab
    exact mul_left_cancel₀ hy this
  have hfilter :
      P.oneAtomValue
        = ∑ s ∈ P.I.params.filter (fun s => ((P.yNat : ℤ) ∣ P.I.bAt s)), P.integrand s := by
    simp [LongLinePacket.oneAtomValue, Finset.sum_filter]
  rw [hfilter, hpres.2, Finset.sum_image (fun a ha b hb h => hinj ha hb h)]
  rfl

/-! ## 3. The three analytic interfaces — never inhabited -/

/-- **`FM722LongLineOneAtomMobiusGammaBound` — UNINHABITED.**  The exact
analytic residual `FM722-LONGLINE-ONEATOM-AP-MOBIUSGAMMA45`: a power saving on
the centred one-atom long-line value, uniformly over finite packets.

No term of this type is ever constructed in this bank. -/
structure FM722LongLineOneAtomMobiusGammaBound where
  /-- The saving exponent. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- **The analytic field.**  The only unproved content of the interface. -/
  oneAtomBound : ∀ P : LongLinePacket, ‖P.oneAtomValue‖ ≤ const * P.size ^ (1 - eta)

/-- **`FM722LongLineTwoAtomHardBound` — UNINHABITED.**  The same saving for the
hard-opened two-atom presentation. -/
structure FM722LongLineTwoAtomHardBound where
  /-- The saving exponent. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- **The analytic field.** -/
  hardBound : ∀ (P : LongLinePacket) (s0 : ℤ) (R : Finset ℤ),
    P.IsHardPresentation s0 R → ‖P.hardValue s0 R‖ ≤ const * P.size ^ (1 - eta)

/-- **`FM722LongLineTwoAtomSoftBound` — UNINHABITED.**  The same saving for the
soft projector expansion. -/
structure FM722LongLineTwoAtomSoftBound where
  /-- The saving exponent. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- **The analytic field.** -/
  softBound : ∀ P : LongLinePacket, ‖P.softValue‖ ≤ const * P.size ^ (1 - eta)

/-! ## 4. Conditional reassembly (deterministic, never unconditional) -/

/-- **softBound → oneAtomBound.**  Transport of the inequality across the exact
soft projector identity.  The soft bound itself is *not* proved. -/
def softBound_to_oneAtomBound (S : FM722LongLineTwoAtomSoftBound) :
    FM722LongLineOneAtomMobiusGammaBound where
  eta := S.eta
  eta_pos := S.eta_pos
  const := S.const
  const_nonneg := S.const_nonneg
  oneAtomBound := by
    intro P
    have := S.softBound P
    rwa [softValue_eq_oneAtomValue P] at this

/-- **hardBound → oneAtomBound**, packetwise: for any packet admitting a hard
fibre presentation, the hard bound gives the one-atom bound.  The hard bound
itself is *not* proved. -/
theorem hardBound_to_oneAtom_packet (H : FM722LongLineTwoAtomHardBound)
    (P : LongLinePacket) (s0 : ℤ) (R : Finset ℤ) (hpres : P.IsHardPresentation s0 R) :
    ‖P.oneAtomValue‖ ≤ H.const * P.size ^ (1 - H.eta) := by
  have h := H.hardBound P s0 R hpres
  rwa [hardValue_eq_oneAtomValue P s0 R hpres] at h

/-- **hardBound → oneAtomBound**, given a supplied family of hard fibre
presentations.  Both inputs are hypotheses: nothing analytic is derived. -/
def hardBound_to_oneAtomBound (H : FM722LongLineTwoAtomHardBound)
    (pres : ∀ P : LongLinePacket, ∃ s0 : ℤ, ∃ R : Finset ℤ, P.IsHardPresentation s0 R) :
    FM722LongLineOneAtomMobiusGammaBound where
  eta := H.eta
  eta_pos := H.eta_pos
  const := H.const
  const_nonneg := H.const_nonneg
  oneAtomBound := by
    intro P
    obtain ⟨s0, R, hpres⟩ := pres P
    exact hardBound_to_oneAtom_packet H P s0 R hpres

/-- **Semantic guard.**  The hard and the soft interface are *different*
inputs: neither is derived from the other in this bank, and the hard lane
additionally needs a fibre presentation, which the soft lane does not. -/
theorem hard_and_soft_interfaces_are_independent_inputs :
    (∀ S : FM722LongLineTwoAtomSoftBound, ∃ O : FM722LongLineOneAtomMobiusGammaBound,
        O.eta = S.eta ∧ O.const = S.const) ∧
      (∀ H : FM722LongLineTwoAtomHardBound,
        (∀ P : LongLinePacket, ∃ s0 : ℤ, ∃ R : Finset ℤ, P.IsHardPresentation s0 R) →
          ∃ O : FM722LongLineOneAtomMobiusGammaBound, O.eta = H.eta ∧ O.const = H.const) := by
  constructor
  · intro S; exact ⟨softBound_to_oneAtomBound S, rfl, rfl⟩
  · intro H pres; exact ⟨hardBound_to_oneAtomBound H pres, rfl, rfl⟩

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
