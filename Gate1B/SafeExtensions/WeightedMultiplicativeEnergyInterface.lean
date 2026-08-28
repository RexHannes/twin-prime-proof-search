/-
# Gate 1B v12 — weighted multiplicative energy: exact object, UNINHABITED bound

**Status: definition + exact identities PROVED; bound interface UNINHABITED.**

`ProductResidueEnergy` is the exact finite object

    E(α,β) = ∑_{r mod q} | ∑_{mn ≡ r} α_m β_n |²

already defined in `Gate1B/SafeAlgebra/MovingMultiplierSecondMoment.lean`
(`Gate1B.SafeAlgebra.productResidueEnergy`); it is *reused*, not redefined.

Only finite identities are proved here.  In particular the research inequality

    E(α,β) ≤ p^{o(1)} ‖α‖² ‖β‖²

is **NOT** asserted anywhere: it is carried by the deliberately uninhabited
interface `WeightedMultiplicativeEnergyInput`, whose single field is the exact
inequality with an explicit target.  No inhabitant is constructed in this bank.

Contents:

* `productResidueEnergy_nonneg`;
* `productResidueEnergy_eq_of_second_moment` — the exact identity that expresses
  `p² E` through the moving-`a` second moment;
* `WeightedMultiplicativeEnergyInput` — UNINHABITED interface;
* `weightedMultiplicativeEnergyInput_not_vacuous` — non-vacuity guard.
-/
import Mathlib
import Gate1B.SafeAlgebra.MovingMultiplierSecondMoment

namespace Gate1B.SafeExtensions

open Finset Gate1B.SafeAlgebra

variable {q : ℕ} [NeZero q]

/-- The product-residue energy is a sum of squares, hence nonnegative. -/
theorem productResidueEnergy_nonneg (alpha beta : (ZMod q)ˣ → ℂ) :
    0 ≤ productResidueEnergy alpha beta :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **Exact identity.**  The moving-`a` second moment determines `p² E` exactly;
this is the only link between the energy and the multiplier family that this
bank asserts. -/
theorem productResidueEnergy_eq_of_second_moment {p : ℕ} [Fact p.Prime]
    {Ch : Type*} [Fintype Ch] [DecidableEq Ch]
    (C : AdditiveCharacterSystem p) (S : MulCharSystem (ZMod p)ˣ Ch)
    (c₀ : Ch) (hc₀ : S.IsPrincipal c₀)
    (alpha beta : (ZMod p)ˣ → ℂ) :
    (p : ℝ) ^ 2 * productResidueEnergy alpha beta
      = (∑ a : ZMod p, ‖movingMultiplier C alpha beta a‖ ^ 2)
        + (p : ℝ) * (‖∑ m : (ZMod p)ˣ, alpha m‖ ^ 2 * ‖∑ n : (ZMod p)ˣ, beta n‖ ^ 2) := by
  rw [movingMultiplier_second_moment_all C S c₀ hc₀ alpha beta]
  ring

/-- **UNINHABITED INTERFACE.**  The weighted multiplicative-energy input: the
exact inequality with an explicit target.  No inhabitant is produced anywhere in
this bank, and in particular no `p^{o(1)}` shape is asserted. -/
structure WeightedMultiplicativeEnergyInput (q : ℕ) [NeZero q]
    (alpha beta : (ZMod q)ˣ → ℂ) (target : ℝ) : Prop where
  /-- EXTERNAL ANALYTIC INPUT — never supplied here. -/
  energy_le : productResidueEnergy alpha beta ≤ target

/-- **Non-vacuity guard.**  The interface has real content: it is impossible for
a negative target. -/
theorem weightedMultiplicativeEnergyInput_not_vacuous (alpha beta : (ZMod q)ˣ → ℂ) :
    ¬ WeightedMultiplicativeEnergyInput q alpha beta (-1) := by
  intro h
  have h0 := productResidueEnergy_nonneg alpha beta
  have := h.energy_le
  linarith

/-- Deterministic consequence of the interface, for downstream compilers. -/
theorem energy_le_of_input {alpha beta : (ZMod q)ˣ → ℂ} {target : ℝ}
    (h : WeightedMultiplicativeEnergyInput q alpha beta target) :
    productResidueEnergy alpha beta ≤ target := h.energy_le

end Gate1B.SafeExtensions
