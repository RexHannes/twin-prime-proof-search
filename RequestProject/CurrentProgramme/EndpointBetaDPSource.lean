import Mathlib
import RequestProject.CurrentProgramme.EndpointCentering
import RequestProject.CurrentProgramme.EndpointTwoByTwoSplit

/-!
# Phase C · the `β = μ_D * Λ_P` source socket (`ENDPOINT-BETA-PHYSICAL-DICTIONARY45`)

## Repository search (recorded)

The literal physical object

  `β_{D,P}(z) = ∑_{d p = z} μ(d) log p`

together with its physical dyadic ranges and line transform is **not present**
in this repository.  A search for `μ_D`, `Λ_P`, `primeWeight`, `muWeight` and
`beta` finds only the *abstract* interface
`Interfaces.EndpointBetaSourceDictionary` (an abstract `beta = muD ⋆ lamP`
factorisation over unspecified supports), which is **not** the physical
dictionary: it pins neither `μ`, nor `log p`, nor the dyadic ranges, nor the
line transform.

Therefore, exactly as instructed, the physical equality is **not invented**.
What is added here is:

* `BetaDPLineSourceData` — a *concrete* data structure in which `μ` and
  `log p` are pinned to Mathlib's `ArithmeticFunction.moebius` and
  `Real.log`, the ranges are dyadic, the prime support is a genuine prime
  support, and the sector predicate is decidable data (**no free `Prop`
  field**);
* `betaLine` — the opened line built from that data and the factor-mod
  discrepancy kernel;
* `BetaDPPhysicalSourceAdapter` — the **uninhabited** adapter whose only
  content is the assertion that the actual physical `Z`-line equals `betaLine`.

Status recorded:

```
ENDPOINT-BETA-PHYSICAL-DICTIONARY45 : SOURCE_OPEN / UNINHABITED.
```

## Firewall

`BetaDPLineSourceData` is deliberately inhabited by an explicitly *empty*
witness (`trivialBetaData`): the data type is finite bookkeeping, it carries no
arithmetic claim.  The content is entirely in the adapter, and
`betaPhysicalAdapter_not_automatic` shows the adapter equality is a genuine
constraint that no construction in this repository supplies.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace BetaDP

open Finset

/-! ## 1. The factor-mod discrepancy kernel `K_{u,ℓ}` -/

open Classical in
/-- The **factor-mod discrepancy kernel** on `ZMod u`:

  `K_{u,ℓ}(x) = 1_{x·ℓ ≡ 2 (u)} − 1_{(x,u)=1} / φ(u)`.

The congruence `x ℓ ≡ 2 (mod u)` is the exact shifted condition of the
programme (fixed shift `2`; nothing is averaged over the shift). -/
noncomputable def factorModKernelZ (u : ℕ) (ell two x : ZMod u) : ℂ :=
  (if x * ell = two then 1 else 0) - (if IsUnit x then 1 else 0) / (u.totient : ℂ)

/-- The unit indicator `1_{(x,u)=1}` at integer level. -/
noncomputable def unitIndicator (x u : ℕ) : ℂ := if Nat.Coprime x u then 1 else 0

/-- The integer-level factor-mod kernel, the pullback of `factorModKernelZ`
along reduction mod `u`. -/
noncomputable def factorModKernel (u ell x : ℕ) : ℂ :=
  factorModKernelZ u (ell : ZMod u) (2 : ZMod u) (x : ZMod u)

/-- On the unit sector the factor-mod kernel **is** the centered residue kernel
of Phase A, evaluated at `(x·ℓ, 2)`.  This is what allows the Phase A character
expansion to be applied to the `β`-line without any new character theory. -/
theorem factorModKernelZ_eq_centeredKernel (u : ℕ) [NeZero u]
    (x ell two : (ZMod u)ˣ) :
    factorModKernelZ u (ell : ZMod u) (two : ZMod u) (x : ZMod u)
      = Centering.centeredKernel u ((x : ZMod u) * (ell : ZMod u)) (two : ZMod u) := by
  unfold factorModKernelZ Centering.centeredKernel
  have h1 : IsUnit ((x : ZMod u) * (ell : ZMod u) * (two : ZMod u)) := by
    rw [← Units.val_mul, ← Units.val_mul]; exact Units.isUnit _
  have h2 : IsUnit (x : ZMod u) := Units.isUnit _
  simp [h1, h2]

/-- **`factorModKernel_principal_centered`.**  The factor-mod kernel has exact
zero mean over the unit residue system: the congruence has exactly one unit
solution `x = 2·ℓ⁻¹`, and the principal term removes exactly that mass. -/
theorem factorModKernel_principal_centered (u : ℕ) [NeZero u] (ell two : (ZMod u)ˣ) :
    ∑ x : (ZMod u)ˣ, factorModKernelZ u (ell : ZMod u) (two : ZMod u) (x : ZMod u) = 0 := by
  classical
  have hcard : (Fintype.card (ZMod u)ˣ : ℂ) = (u.totient : ℂ) := by
    rw [ZMod.card_units_eq_totient u]
  have hpos : 0 < u := Nat.pos_of_ne_zero (NeZero.ne u)
  have htot : (u.totient : ℂ) ≠ 0 := by
    have : 0 < u.totient := Nat.totient_pos.2 hpos
    exact_mod_cast this.ne'
  have hsimp : ∀ x : (ZMod u)ˣ,
      factorModKernelZ u (ell : ZMod u) (two : ZMod u) (x : ZMod u)
        = (if x = two * ell⁻¹ then (1:ℂ) else 0) - 1 / (u.totient : ℂ) := by
    intro x
    have hu : IsUnit (x : ZMod u) := Units.isUnit _
    have hiff : ((x : ZMod u) * (ell : ZMod u) = (two : ZMod u)) ↔ x = two * ell⁻¹ := by
      constructor
      · intro h
        have : x * ell = two := Units.ext (by simpa using h)
        rw [← this, mul_assoc, mul_inv_cancel, mul_one]
      · intro h
        rw [h]
        push_cast
        simp [mul_assoc]
    unfold factorModKernelZ
    by_cases h : x = two * ell⁻¹
    · rw [if_pos (hiff.2 h), if_pos h, if_pos hu]
    · rw [if_neg (fun hc => h (hiff.1 hc)), if_neg h, if_pos hu]
  rw [Finset.sum_congr rfl fun x _ => hsimp x, Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (two * ell⁻¹) (fun _ => (1:ℂ))]
  rw [if_pos (Finset.mem_univ _), Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  field_simp
  ring

/-! ## 2. The concrete `β_{D,P}` line source data -/

/-- **Concrete** `β_{D,P}` line source data.

Every field is data or an equation between concrete objects: `μ` is Mathlib's
`ArithmeticFunction.moebius`, the prime weight is `log p` on primes and `0`
elsewhere, the ranges are dyadic, and the sector predicate is a `Bool` with a
stated arithmetic consequence.  There is **no free `Prop` field**. -/
structure BetaDPLineSourceData where
  /-- Dyadic scale of the `μ`-variable. -/
  D : ℕ
  /-- Dyadic scale of the prime variable. -/
  P : ℕ
  /-- The `d`-support. -/
  Dsupp : Finset ℕ
  /-- The `p`-support. -/
  Psupp : Finset ℕ
  /-- `d ∼ D` dyadically. -/
  dyadicD : ∀ d ∈ Dsupp, D ≤ d ∧ d < 2 * D
  /-- `p ∼ P` dyadically. -/
  dyadicP : ∀ p ∈ Psupp, P ≤ p ∧ p < 2 * P
  /-- The prime variable really runs over primes. -/
  primeSupport : ∀ p ∈ Psupp, Nat.Prime p
  /-- The Möbius weight. -/
  muWeight : ℕ → ℂ
  /-- …pinned to Mathlib's Möbius function. -/
  muWeight_eq : ∀ d, muWeight d = ((ArithmeticFunction.moebius d : ℤ) : ℂ)
  /-- The prime weight. -/
  primeWeight : ℕ → ℂ
  /-- …pinned to `log p` on primes. -/
  primeWeight_eq : ∀ p, primeWeight p = if Nat.Prime p then ((Real.log p : ℝ) : ℂ) else 0
  /-- The convolved coefficient `β`. -/
  beta : ℕ → ℂ
  /-- …pinned to the Dirichlet convolution over the dyadic supports. -/
  beta_eq : ∀ z, beta z =
    ∑ d ∈ Dsupp, ∑ p ∈ Psupp, if d * p = z then muWeight d * primeWeight p else 0
  /-- The smooth line weight, evaluated at the slots `(d, p, ℓ, k)`. -/
  smoothWeight : ℕ → ℕ → ℕ → ℕ → ℂ
  /-- The quotient variable attached to `(z, ℓ)`. -/
  quot : ℕ → ℕ → ℕ
  /-- The clean-sector predicate: decidable data, not a free `Prop`. -/
  cleanSector : ℕ → ℕ → Bool
  /-- Its arithmetic meaning: a clean pair is coprime. -/
  cleanSector_coprime : ∀ z u, cleanSector z u = true → Nat.Coprime z u

namespace BetaDPLineSourceData

variable (S : BetaDPLineSourceData)

/-- The `z`-support of `β`: all products `d·p` from the two dyadic ranges. -/
def Zsupp : Finset ℕ := (S.Dsupp ×ˢ S.Psupp).image fun z => z.1 * z.2

theorem mem_Zsupp {d p : ℕ} (hd : d ∈ S.Dsupp) (hp : p ∈ S.Psupp) :
    d * p ∈ S.Zsupp := by
  rw [Zsupp, Finset.mem_image]
  exact ⟨(d, p), Finset.mem_product.2 ⟨hd, hp⟩, rfl⟩

/-- **`betaDP_open_line`.**  Opening the convolution: testing `β` against any
weight `F` over a covering support is exactly the double `(d,p)`-sum.

Proved by reusing the exact grouping lemma `TwoByTwo.sum_group_one`; no new
combinatorics, and repeated factorisations are counted with exact
multiplicity. -/
theorem betaDP_open_line (F : ℕ → ℂ) :
    ∑ z ∈ S.Zsupp, S.beta z * F z
      = ∑ d ∈ S.Dsupp, ∑ p ∈ S.Psupp, S.muWeight d * S.primeWeight p * F (d * p) := by
  classical
  have hp : ∀ w ∈ S.Dsupp ×ˢ S.Psupp, w.1 * w.2 ∈ S.Zsupp := by
    intro w hw
    rw [Finset.mem_product] at hw
    exact S.mem_Zsupp hw.1 hw.2
  have hgroup := TwoByTwo.sum_group_one (M := ℕ) (S.Dsupp ×ˢ S.Psupp)
      (fun w => w.1 * w.2) (fun w => S.muWeight w.1 * S.primeWeight w.2) S.Zsupp hp F
  have hbeta : ∀ z ∈ S.Zsupp,
      S.beta z = ∑ w ∈ S.Dsupp ×ˢ S.Psupp,
        if w.1 * w.2 = z then S.muWeight w.1 * S.primeWeight w.2 else 0 := by
    intro z _
    rw [S.beta_eq z, Finset.sum_product]
  calc ∑ z ∈ S.Zsupp, S.beta z * F z
      = ∑ z ∈ S.Zsupp, (∑ w ∈ S.Dsupp ×ˢ S.Psupp,
          if w.1 * w.2 = z then S.muWeight w.1 * S.primeWeight w.2 else 0) * F z :=
        Finset.sum_congr rfl fun z hz => by rw [hbeta z hz]
    _ = ∑ w ∈ S.Dsupp ×ˢ S.Psupp, S.muWeight w.1 * S.primeWeight w.2 * F (w.1 * w.2) := hgroup
    _ = ∑ d ∈ S.Dsupp, ∑ p ∈ S.Psupp, S.muWeight d * S.primeWeight p * F (d * p) := by
        rw [Finset.sum_product]

/-- The opened `β`-line against the factor-mod kernel: the *exact* finite
expression that the physical `Z`-line is claimed (but not proved here) to
equal. -/
noncomputable def betaLine (u ell k : ℕ) : ℂ :=
  ∑ d ∈ S.Dsupp, ∑ p ∈ S.Psupp,
    S.muWeight d * S.primeWeight p * S.smoothWeight d p ell k *
      factorModKernel u ell (d * p)

end BetaDPLineSourceData

/-! ## 3. The uninhabited physical adapter -/

/-- **`BetaDPPhysicalSourceAdapter` — SOURCE_OPEN, UNINHABITED.**

Its single mathematical content is: the actual physical `Z`-line
`physicalLine u ℓ k` *equals* the concrete `β_{D,P}` line.  Nothing in this
repository constructs one, and nothing may derive one. -/
structure BetaDPPhysicalSourceAdapter (physicalLine : ℕ → ℕ → ℕ → ℂ) where
  /-- The concrete source data. -/
  data : BetaDPLineSourceData
  /-- The literal identification of the physical line with the `β`-line. -/
  literal : ∀ u ell k, physicalLine u ell k = data.betaLine u ell k

/-! ## 4. Non-vacuity guards -/

/-- The *data* type is inhabited by an explicitly empty witness — so the data
type carries no arithmetic content by itself. -/
noncomputable def trivialBetaData : BetaDPLineSourceData where
  D := 1
  P := 1
  Dsupp := ∅
  Psupp := ∅
  dyadicD := by simp
  dyadicP := by simp
  primeSupport := by simp
  muWeight := fun d => ((ArithmeticFunction.moebius d : ℤ) : ℂ)
  muWeight_eq := fun _ => rfl
  primeWeight := fun p => if Nat.Prime p then ((Real.log p : ℝ) : ℂ) else 0
  primeWeight_eq := fun _ => rfl
  beta := fun _ => 0
  beta_eq := by simp
  smoothWeight := fun _ _ _ _ => 0
  quot := fun _ _ => 0
  cleanSector := fun _ _ => false
  cleanSector_coprime := by simp

/-- The empty witness has identically vanishing line. -/
theorem trivialBetaData_line (u ell k : ℕ) : trivialBetaData.betaLine u ell k = 0 := by
  simp [BetaDPLineSourceData.betaLine, trivialBetaData]

/-- **`betaPhysicalAdapter_not_automatic`.**  The adapter equality is a genuine
constraint: there is a physical line and source data for which the literal
identification is false.  Hence no compiler may manufacture the adapter. -/
theorem betaPhysicalAdapter_not_automatic :
    ∃ (L : ℕ → ℕ → ℕ → ℂ) (S : BetaDPLineSourceData),
      ¬ (∀ u ell k, L u ell k = S.betaLine u ell k) := by
  refine ⟨fun _ _ _ => 1, trivialBetaData, ?_⟩
  intro h
  have := h 1 1 1
  rw [trivialBetaData_line] at this
  exact one_ne_zero this

/-- At modulus `u = 1` the factor-mod kernel vanishes identically (the
congruence indicator and the principal term coincide). -/
theorem factorModKernel_modulus_one (ell x : ℕ) : factorModKernel 1 ell x = 0 := by
  unfold factorModKernel factorModKernelZ
  rw [if_pos (Subsingleton.elim ((x : ZMod 1) * (ell : ZMod 1)) (2 : ZMod 1)),
    if_pos (isUnit_of_subsingleton ((x : ZMod 1)))]
  simp

/-- Consequently every `β`-line vanishes at modulus `1`. -/
theorem betaLine_modulus_one (S : BetaDPLineSourceData) (ell k : ℕ) :
    S.betaLine 1 ell k = 0 := by
  simp [BetaDPLineSourceData.betaLine, factorModKernel_modulus_one]

/-- **Firewall / anti-circularity.**  Possessing the *data* does not give the
adapter.  The data type is inhabited, yet for the constant physical line
`L ≡ 1` the adapter type is **empty**, because every `β`-line vanishes at
modulus `1`.  So the adapter is a genuine, unmet source obligation. -/
theorem betaData_does_not_give_adapter :
    (∃ _S : BetaDPLineSourceData, True) ∧
      IsEmpty (BetaDPPhysicalSourceAdapter (fun _ _ _ => 1)) := by
  refine ⟨⟨trivialBetaData, trivial⟩, ⟨fun A => ?_⟩⟩
  have h1 : (1 : ℂ) = A.data.betaLine 1 1 1 := A.literal 1 1 1
  rw [betaLine_modulus_one] at h1
  exact one_ne_zero h1

end BetaDP
end CurrentProgramme
end TwinPrimeProject
