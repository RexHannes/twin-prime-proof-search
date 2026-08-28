import RequestProject.NANC.Gate1B.V11GeneratedExpression
import Gate1B.SafeAlgebra.FiniteKloosterman

/-!
# V11 · Gate 1B — pair-modulus source-multiplier data

The finite Kloosterman infrastructure is **reused**, not re-created:
`Gate1B.SafeAlgebra.AdditiveCharacterSystem` and its `kloosterman` sum come from
the existing v8.2 bank.

Defined here: the abstract finite data of a pair-modulus source multiplier
family and its value

    pairModFamilyValue = ∑_Θ A(Θ) ∑_{u,v} α(Θ,u) β(Θ,v) S(Θu, v; c).

**No estimate is assumed.**  The only inequality proved is the trivial ℓ¹ one,
which uses no cancellation at all.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset Gate1B.SafeAlgebra

/-- **Abstract finite pair-modulus source-multiplier data** at modulus `c`. -/
structure PairModSourceData (c : ℕ) [NeZero c] (Θ U V : Type) [Fintype Θ] [Fintype U]
    [Fintype V] where
  /-- The supplied additive character system mod `c` (reused v8.2 interface). -/
  charSys : AdditiveCharacterSystem c
  /-- The source multiplier coefficient `A(Θ)`. -/
  A : Θ → ℂ
  /-- The residue carried by the multiplier index `Θ`. -/
  thetaResidue : Θ → ZMod c
  /-- The residue carried by the `u`-variable. -/
  uResidue : U → ZMod c
  /-- The residue carried by the `v`-variable. -/
  vResidue : V → ZMod c
  /-- The `u`-side coefficient `α(Θ,u)`. -/
  alpha : Θ → U → ℂ
  /-- The `v`-side coefficient `β(Θ,v)`. -/
  beta : Θ → V → ℂ

namespace PairModSourceData

variable {c : ℕ} [NeZero c] {Θ U V : Type} [Fintype Θ] [Fintype U] [Fintype V]

/-- The Kloosterman kernel `S(Θu, v; c)` attached to the data. -/
noncomputable def kernel (d : PairModSourceData c Θ U V) (t : Θ) (i : U) (j : V) : ℂ :=
  d.charSys.kloosterman (d.thetaResidue t * d.uResidue i) (d.vResidue j)

/-- The inner (fixed-multiplier) bilinear form at a fixed `Θ`. -/
noncomputable def fixedMultiplierValue (d : PairModSourceData c Θ U V) (t : Θ) : ℂ :=
  ∑ i : U, ∑ j : V, d.alpha t i * d.beta t j * d.kernel t i j

/-- **The pair-modulus source-multiplier family value.** -/
noncomputable def pairModFamilyValue (d : PairModSourceData c Θ U V) : ℂ :=
  ∑ t : Θ, d.A t * d.fixedMultiplierValue t

/-- The family value is the `A`-weighted sum of the fixed-multiplier values —
by definition, recorded as a usable identity. -/
theorem pairModFamilyValue_eq (d : PairModSourceData c Θ U V) :
    d.pairModFamilyValue = ∑ t : Θ, d.A t * d.fixedMultiplierValue t := rfl

/-- **Trivial ℓ¹ bound** — no cancellation whatsoever is used.  This is recorded
precisely so that later work cannot mistake it for a saving. -/
theorem norm_pairModFamilyValue_le (d : PairModSourceData c Θ U V) (K : ℝ)
    (hfix : ∀ t, ‖d.fixedMultiplierValue t‖ ≤ K) :
    ‖d.pairModFamilyValue‖ ≤ (∑ t : Θ, ‖d.A t‖) * K :=
  norm_finiteSum_le_l1Cost Finset.univ _ _ K fun t _ => hfix t

/-- The Kloosterman kernel obeys the unit-reindexing invariance of the existing
bank; nothing analytic is added. -/
theorem kernel_scale (d : PairModSourceData c Θ U V) (A B : ZMod c) (u : (ZMod c)ˣ) :
    d.charSys.kloosterman (A * (u : ZMod c)) (B * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))
      = d.charSys.kloosterman A B :=
  d.charSys.kloosterman_scale A B u

end PairModSourceData

end Gate1BV11
end TwinPrimeProject
