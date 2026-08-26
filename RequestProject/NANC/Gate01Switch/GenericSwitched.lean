import RequestProject.NANC.Gate01Switch.RepeatedPrime

/-!
# Gate01Switch: the generic switched operator and the exact three-way split

`switchedStratum S K c E = ∑_{(d,ℓ) ∈ S} μ(d) Λ(ℓ) ∑_{r ∈ B_{dℓ}} c(dℓr - 2)
                          − ∑_{(d,ℓ) ∈ S} μ(d) Λ(ℓ) E(dℓ)`.

The main theorem is the exact finite equality

`S_sw = S_higherPrimePower + S_repeatedP + S_sw^gen`,

where the three strata are the switched strata of the three pair sets
`higherPrimePowerPart`, `repeatedPart`, `genericPart` of `divisorPairs Qset U V`.
The generic set is characterised by
`U < d`, `V < p`, `p` prime, `p ∤ d`, `dp ∈ Qset`.

The von Mangoldt value at the prime `p` is Mathlib's `Λ p`; no manual
replacement by `Real.log p` is performed (the identity `Λ p = log p` is
available as `ArithmeticFunction.vonMangoldt_apply_prime` and is recorded here
as `genericPart_vonMangoldt_eq_log`).
-/

namespace TwinPrimeProject
namespace Gate01Switch

open ArithmeticFunction Finset

/-- The switched stratum attached to a set of divisor pairs. -/
noncomputable def switchedStratum (S : Finset (ℕ × ℕ)) (K : ℕ) (c E : ℕ → ℝ) : ℝ :=
  pairSum S (coeffWeight K c) - pairSum S (expectedWeight E)

theorem switchedStratum_add (S T : Finset (ℕ × ℕ)) (K : ℕ) (c E : ℕ → ℝ)
    (h : Disjoint S T) :
    switchedStratum (S ∪ T) K c E = switchedStratum S K c E + switchedStratum T K c E := by
  simp only [switchedStratum, pairSum, Finset.sum_union h]
  ring

/-- Membership in the generic pair set: `U < d`, `V < p`, `p` prime, `p ∤ d`
and `dp ∈ Qset`. -/
theorem mem_genericPart_divisorPairs {Qset : Finset ℕ} {U V : ℕ} {x : ℕ × ℕ} :
    x ∈ genericPart (divisorPairs Qset U V) ↔
      U < x.1 ∧ V < x.2 ∧ x.2.Prime ∧ ¬ x.2 ∣ x.1 ∧ x.1 * x.2 ∈ Qset ∧ x.1 * x.2 ≠ 0 := by
  simp only [genericPart, primePart, Finset.mem_filter, mem_divisorPairs]
  tauto

/-- Membership in the repeated-prime pair set. -/
theorem mem_repeatedPart_divisorPairs {Qset : Finset ℕ} {U V : ℕ} {x : ℕ × ℕ} :
    x ∈ repeatedPart (divisorPairs Qset U V) ↔
      U < x.1 ∧ V < x.2 ∧ x.2.Prime ∧ x.2 ∣ x.1 ∧ x.1 * x.2 ∈ Qset ∧ x.1 * x.2 ≠ 0 := by
  simp only [repeatedPart, primePart, Finset.mem_filter, mem_divisorPairs]
  tauto

/-- On the generic (and repeated) branch the von Mangoldt weight is the source
value at a prime, i.e. `Λ p = log p`. -/
theorem genericPart_vonMangoldt_eq_log {S : Finset (ℕ × ℕ)} {x : ℕ × ℕ}
    (hx : x ∈ genericPart S) : Λ x.2 = Real.log x.2 :=
  vonMangoldt_apply_prime (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2

/-- **The canonical generic switched operator `S_sw^gen`.** -/
noncomputable def genericSwitchedOperator (Qset : Finset ℕ) (U V K : ℕ) (c E : ℕ → ℝ) : ℝ :=
  switchedStratum (genericPart (divisorPairs Qset U V)) K c E

/-- The higher-prime-power switched stratum. -/
noncomputable def higherPrimePowerSwitchedOperator (Qset : Finset ℕ) (U V K : ℕ)
    (c E : ℕ → ℝ) : ℝ :=
  switchedStratum (higherPrimePowerPart (divisorPairs Qset U V)) K c E

/-- The repeated-prime switched stratum. -/
noncomputable def repeatedSwitchedOperator (Qset : Finset ℕ) (U V K : ℕ) (c E : ℕ → ℝ) : ℝ :=
  switchedStratum (repeatedPart (divisorPairs Qset U V)) K c E

/-- **The exact three-way decomposition**
`S_sw = S_higherPrimePower + S_repeatedP + S_sw^gen`. -/
theorem switchedOperator_three_way {Qset : Finset ℕ} (U V K : ℕ) (c E : ℕ → ℝ)
    (hQ : ∀ q ∈ Qset, 0 < q) :
    switchedOperator Qset U V K c E =
      higherPrimePowerSwitchedOperator Qset U V K c E
      + repeatedSwitchedOperator Qset U V K c E
      + genericSwitchedOperator Qset U V K c E := by
  have hsw2 := switchedOperator_eq_SW2 (Qset := Qset) U V K c E hQ
  have hsplit1 : ∀ G : ℕ → ℕ → ℝ,
      pairSum (divisorPairs Qset U V) G =
        pairSum (primePart (divisorPairs Qset U V)) G
        + pairSum (higherPrimePowerPart (divisorPairs Qset U V)) G :=
    fun G => pairSum_split_prime _ G
  have hsplit2 : ∀ G : ℕ → ℕ → ℝ,
      pairSum (primePart (divisorPairs Qset U V)) G =
        pairSum (repeatedPart (divisorPairs Qset U V)) G
        + pairSum (genericPart (divisorPairs Qset U V)) G :=
    fun G => pairSum_split_repeated _ G
  rw [hsw2, switchedSW2Coefficient, switchedSW2Expected,
    hsplit1 (coeffWeight K c), hsplit1 (expectedWeight E),
    hsplit2 (coeffWeight K c), hsplit2 (expectedWeight E)]
  simp only [higherPrimePowerSwitchedOperator, repeatedSwitchedOperator,
    genericSwitchedOperator, switchedStratum]
  ring

end Gate01Switch
end TwinPrimeProject
