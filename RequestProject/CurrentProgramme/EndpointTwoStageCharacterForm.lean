import Mathlib
import RequestProject.CurrentProgramme.EndpointCharacterCentering
import RequestProject.CurrentProgramme.EndpointBetaDPSource

/-!
# Phases B & D · character-twisted `2|2` split and the exact two-stage normal form

**Exact finite algebra only.**  No estimate is proved anywhere in this module,
and no analytic or source interface is inhabited.

## Phase B — `twoByTwo_character_twist`

The `2|2` convolution split of `EndpointTwoByTwoSplit` survives a character
twist verbatim, because a character is multiplicative:

  `∑_u a₄(u) χ(u) Z(u,ℓ,k) = ∑_{m,r} α(m) γ(r) χ(m) χ(r) Z(mr,ℓ,k)`.

The multiplicativity is an explicit hypothesis in the generic version
(`twoByTwo_character_twist`) and is *discharged* for genuine Dirichlet
characters in `twoByTwo_dirichlet_twist`.

## Phase D — the two-stage normal form

`CharTwistedFactorModTerm` is the summand with **exactly** the slots demanded by
the programme:

  `α(m) γ(r) χ(m) χ(r) μ(d) log p · W(m,r,d,p,ℓ,k) · K_{mr,ℓ}(d p)`,

`SChar` is its `(m,r,d,p)`-sum, and `TwoStageSquareBundle` is

  `∑_ℓ (1/φ(ℓ)) ∑_{χ ≠ χ₀} |SChar(ℓ,χ,k)|²`.

`twoStage_normalForm_of_adapter` is the **conditional source compiler**: given a
`BetaDPPhysicalSourceAdapter` (which is *not* inhabited anywhere) and the
matching of the coefficient slots, the physical centered bundle equals the
two-stage square bundle.  The comparison/local remainder is carried separately
and is never absorbed: see `comparisonRemainder_not_absorbed`.

Status:

```
ENDPOINT-TWOSTAGE-NORMALFORM45 : PROVED_FINITE / CONDITIONAL_SOURCE_COMPILER
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace TwoStageChar

open Finset CharacterCentering BetaDP

/-! ## 1. Phase B · the character-twisted `2|2` factorisation -/

variable {M : Type*} [CommMonoid M] [DecidableEq M]

/-- **`twoByTwo_character_twist`.**  For any multiplicative weight `chiF`
(in the application: a Dirichlet character composed with reduction), the exact
`2|2` split commutes with the twist.  No estimate and no smoothness. -/
theorem twoByTwo_character_twist (Pm Pr Us : Finset M) (alpha gamma Z chiF : M → ℂ)
    (hchi : ∀ x y : M, chiF (x * y) = chiF x * chiF y)
    (hcov : ∀ m ∈ Pm, ∀ r ∈ Pr, m * r ∈ Us) :
    ∑ u ∈ Us, TwoByTwo.conv2 Pm Pr alpha gamma u * (chiF u * Z u)
      = ∑ m ∈ Pm, ∑ r ∈ Pr, alpha m * gamma r * (chiF m * chiF r * Z (m * r)) := by
  rw [TwoByTwo.sum_conv2_weight Pm Pr Us alpha gamma (fun u => chiF u * Z u) hcov]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
  rw [hchi m r]

/-- A Dirichlet character, pulled back along `ℕ → ZMod n`, is multiplicative. -/
theorem dirichlet_pullback_mul (n : ℕ) (χ : DirichletCharacter ℂ n) (x y : ℕ) :
    χ (((x * y : ℕ) : ZMod n)) = χ ((x : ZMod n)) * χ ((y : ZMod n)) := by
  push_cast
  rw [map_mul]

/-- **`twoByTwo_dirichlet_twist`.**  The Phase B identity for a genuine
Dirichlet character: the multiplicativity hypothesis is discharged. -/
theorem twoByTwo_dirichlet_twist (n : ℕ) (χ : DirichletCharacter ℂ n)
    (Pm Pr Us : Finset ℕ) (alpha gamma Z : ℕ → ℂ)
    (hcov : ∀ m ∈ Pm, ∀ r ∈ Pr, m * r ∈ Us) :
    ∑ u ∈ Us, TwoByTwo.conv2 Pm Pr alpha gamma u * (χ ((u : ZMod n)) * Z u)
      = ∑ m ∈ Pm, ∑ r ∈ Pr,
          alpha m * gamma r * (χ ((m : ZMod n)) * χ ((r : ZMod n)) * Z (m * r)) :=
  twoByTwo_character_twist Pm Pr Us alpha gamma Z (fun x => χ ((x : ZMod n)))
    (dirichlet_pullback_mul n χ) hcov

/-! ## 2. Phase D · the exact two-stage normal form -/

/-- The coefficient data of the two-stage form: the `2|2` coefficients, their
supports, the concrete `β_{D,P}` source data and the smooth weight. -/
structure TwoStageSourceData where
  /-- `m`-support. -/
  Msupp : Finset ℕ
  /-- `r`-support. -/
  Rsupp : Finset ℕ
  /-- The `m`-coefficient. -/
  alpha : ℕ → ℂ
  /-- The `r`-coefficient. -/
  gamma : ℕ → ℂ
  /-- The concrete `β = μ_D ⋆ Λ_P` data (Phase C). -/
  beta : BetaDPLineSourceData
  /-- The smooth weight at the slots `(m,r,d,p,ℓ,k)`. -/
  smooth : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℂ

namespace TwoStageSourceData

variable (S : TwoStageSourceData)

/-- **`CharTwistedFactorModTerm`.**  The summand of the two-stage normal form,
with exactly the prescribed slots. -/
noncomputable def CharTwistedFactorModTerm (ell : ℕ+) (χ : DirichletCharacter ℂ (ell : ℕ))
    (k m r d p : ℕ) : ℂ :=
  S.alpha m * S.gamma r * χ ((m : ZMod (ell : ℕ))) * χ ((r : ZMod (ell : ℕ))) *
    S.beta.muWeight d * S.beta.primeWeight p * S.smooth m r d p (ell : ℕ) k *
    factorModKernel (m * r) (ell : ℕ) (d * p)

/-- `SChar(ℓ,χ,k)` — the character-twisted factor-mod linear form. -/
noncomputable def SChar (ell : ℕ+) (χ : DirichletCharacter ℂ (ell : ℕ)) (k : ℕ) : ℂ :=
  ∑ m ∈ S.Msupp, ∑ r ∈ S.Rsupp, ∑ d ∈ S.beta.Dsupp, ∑ p ∈ S.beta.Psupp,
    S.CharTwistedFactorModTerm ell χ k m r d p

/-- `TwoStageSquareBundle(k)` — the non-principal character square bundle of the
two-stage form, summed over the modulus family `L`. -/
noncomputable def TwoStageSquareBundle (L : Finset ℕ+) (k : ℕ) : ℝ :=
  ∑ ell ∈ L, ((ell : ℕ).totient : ℝ)⁻¹ *
    ∑ χ ∈ nonprincipalChars (ell : ℕ), Complex.normSq (S.SChar ell χ k)

/-- The bundle is a sum of squares, hence nonnegative. -/
theorem twoStageSquareBundle_nonneg (L : Finset ℕ+) (k : ℕ) :
    0 ≤ S.TwoStageSquareBundle L k := by
  refine Finset.sum_nonneg fun ell _ => ?_
  refine mul_nonneg (by positivity) ?_
  exact Finset.sum_nonneg fun χ _ => Complex.normSq_nonneg _

end TwoStageSourceData

/-! ## 3. The physical centered endpoint expression -/

/-- The physical centered endpoint data: the physical `Z`-line, the `2|2`
coefficients, and — carried **separately** — the comparison/local remainder. -/
structure PhysicalCenteredEndpoint where
  /-- The physical line `Z(u,ℓ,k)`. -/
  line : ℕ → ℕ → ℕ → ℂ
  /-- `m`-support. -/
  Msupp : Finset ℕ
  /-- `r`-support. -/
  Rsupp : Finset ℕ
  /-- The `m`-coefficient. -/
  alpha : ℕ → ℂ
  /-- The `r`-coefficient. -/
  gamma : ℕ → ℂ
  /-- The comparison / local main-term remainder.  NOT absorbed anywhere. -/
  comparisonRemainder : ℕ → ℝ

namespace PhysicalCenteredEndpoint

variable (E : PhysicalCenteredEndpoint)

/-- The physical character-twisted linear form, in `2|2` shape. -/
noncomputable def physicalCharForm (ell : ℕ+) (χ : DirichletCharacter ℂ (ell : ℕ))
    (k : ℕ) : ℂ :=
  ∑ m ∈ E.Msupp, ∑ r ∈ E.Rsupp,
    E.alpha m * E.gamma r * χ ((m : ZMod (ell : ℕ))) * χ ((r : ZMod (ell : ℕ))) *
      E.line (m * r) (ell : ℕ) k

/-- The physical centered square bundle. -/
noncomputable def physicalBundle (L : Finset ℕ+) (k : ℕ) : ℝ :=
  ∑ ell ∈ L, ((ell : ℕ).totient : ℝ)⁻¹ *
    ∑ χ ∈ nonprincipalChars (ell : ℕ), Complex.normSq (E.physicalCharForm ell χ k)

end PhysicalCenteredEndpoint

/-! ## 4. The conditional source compiler -/

/-- Slot matching between the physical endpoint data and the two-stage data.
This is bookkeeping, not arithmetic: it says the two descriptions use the same
coefficients, supports and smooth weight. -/
structure SlotMatch (E : PhysicalCenteredEndpoint) (S : TwoStageSourceData)
    (A : BetaDPPhysicalSourceAdapter E.line) : Prop where
  /-- Same `m`-support. -/
  msupp : S.Msupp = E.Msupp
  /-- Same `r`-support. -/
  rsupp : S.Rsupp = E.Rsupp
  /-- Same `m`-coefficient. -/
  alpha : S.alpha = E.alpha
  /-- Same `r`-coefficient. -/
  gamma : S.gamma = E.gamma
  /-- Same `β`-source data. -/
  beta : S.beta = A.data
  /-- The smooth weight of the two-stage form is the source smooth weight
  (which does not depend on `m,r`). -/
  smooth : ∀ m r d p ell k, S.smooth m r d p ell k = A.data.smoothWeight d p ell k

/-- **Two-stage normal form, linear level.**  Given the (uninhabited) physical
`β`-adapter and slot matching, the physical character-twisted form is *exactly*
`SChar`. -/
theorem physicalCharForm_eq_SChar (E : PhysicalCenteredEndpoint) (S : TwoStageSourceData)
    (A : BetaDPPhysicalSourceAdapter E.line) (h : SlotMatch E S A)
    (ell : ℕ+) (χ : DirichletCharacter ℂ (ell : ℕ)) (k : ℕ) :
    E.physicalCharForm ell χ k = S.SChar ell χ k := by
  classical
  rw [PhysicalCenteredEndpoint.physicalCharForm, TwoStageSourceData.SChar,
    h.msupp, h.rsupp]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun r _ => ?_
  rw [A.literal (m * r) (ell : ℕ) k, BetaDPLineSourceData.betaLine, h.beta,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [TwoStageSourceData.CharTwistedFactorModTerm, h.alpha, h.gamma, h.beta,
    h.smooth m r d p (ell : ℕ) k]
  ring

/-- **`ENDPOINT-TWOSTAGE-NORMALFORM45` — the conditional source compiler.**

Given the physical `β`-adapter and slot matching, the physical centered bundle
equals the two-stage square bundle.  The adapter is **not** inhabited anywhere
in this repository, so this is a compiler, not a theorem about the physical
source. -/
theorem twoStage_normalForm_of_adapter (E : PhysicalCenteredEndpoint)
    (S : TwoStageSourceData) (A : BetaDPPhysicalSourceAdapter E.line)
    (h : SlotMatch E S A) (L : Finset ℕ+) (k : ℕ) :
    E.physicalBundle L k = S.TwoStageSquareBundle L k := by
  refine Finset.sum_congr rfl fun ell _ => ?_
  refine congrArg _ (Finset.sum_congr rfl fun χ _ => ?_)
  rw [physicalCharForm_eq_SChar E S A h ell χ k]

/-- **The endpoint with its comparison remainder.**  The remainder is displayed
as a separate summand and is never absorbed into the analytic square. -/
noncomputable def physicalEndpointWithComparison (E : PhysicalCenteredEndpoint)
    (L : Finset ℕ+) (k : ℕ) : ℝ :=
  E.physicalBundle L k + E.comparisonRemainder k

/-- The compiler in the form actually used downstream: bundle **plus** an
explicit comparison remainder. -/
theorem physicalEndpointWithComparison_eq (E : PhysicalCenteredEndpoint)
    (S : TwoStageSourceData) (A : BetaDPPhysicalSourceAdapter E.line)
    (h : SlotMatch E S A) (L : Finset ℕ+) (k : ℕ) :
    physicalEndpointWithComparison E L k
      = S.TwoStageSquareBundle L k + E.comparisonRemainder k := by
  rw [physicalEndpointWithComparison, twoStage_normalForm_of_adapter E S A h L k]

/-! ## 5. Firewalls -/

/-- **The comparison remainder is not absorbed.**  There is endpoint data whose
bundle is `0` while the endpoint-with-comparison is `1`: centering the character
side says nothing about the comparison pin. -/
theorem comparisonRemainder_not_absorbed :
    ∃ (E : PhysicalCenteredEndpoint) (L : Finset ℕ+) (k : ℕ),
      E.physicalBundle L k = 0 ∧ physicalEndpointWithComparison E L k = 1 := by
  refine ⟨⟨fun _ _ _ => 0, ∅, ∅, fun _ => 0, fun _ => 0, fun _ => 1⟩, ∅, 0, ?_, ?_⟩
  · simp [PhysicalCenteredEndpoint.physicalBundle]
  · simp [physicalEndpointWithComparison, PhysicalCenteredEndpoint.physicalBundle]

/-- Witness: the endpoint whose physical line is constantly `1`. -/
noncomputable def constLineEndpoint : PhysicalCenteredEndpoint :=
  ⟨fun _ _ _ => 1, {1}, {1}, fun _ => 1, fun _ => 1, fun _ => 0⟩

/-- Witness: two-stage data built on the empty `β`-source. -/
noncomputable def emptyTwoStage : TwoStageSourceData :=
  ⟨{1}, {1}, fun _ => 1, fun _ => 1, trivialBetaData, fun _ _ _ _ _ _ => 0⟩

theorem constLineEndpoint_charForm (χ : DirichletCharacter ℂ ((3 : ℕ+) : ℕ)) :
    constLineEndpoint.physicalCharForm (3 : ℕ+) χ 0 = 1 := by
  simp [constLineEndpoint, PhysicalCenteredEndpoint.physicalCharForm]

theorem nonprincipalChars_three_card :
    (nonprincipalChars ((3 : ℕ+) : ℕ)).card = 1 := by
  have hcardAll : Fintype.card (DirichletCharacter ℂ ((3 : ℕ+) : ℕ)) = 2 := by
    have := DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ ((3 : ℕ+) : ℕ)
    rw [Nat.card_eq_fintype_card] at this
    simpa using this
  rw [nonprincipalChars, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, hcardAll]

theorem constLineEndpoint_bundle :
    constLineEndpoint.physicalBundle {(3 : ℕ+)} 0 = 1 / 2 := by
  rw [PhysicalCenteredEndpoint.physicalBundle, Finset.sum_singleton,
    Finset.sum_congr rfl fun χ (_ : χ ∈ nonprincipalChars ((3 : ℕ+) : ℕ)) => by
      rw [constLineEndpoint_charForm χ, Complex.normSq_one],
    Finset.sum_const, nonprincipalChars_three_card]
  norm_num [show Nat.totient 3 = 2 from rfl]

theorem emptyTwoStage_bundle :
    emptyTwoStage.TwoStageSquareBundle {(3 : ℕ+)} 0 = 0 := by
  simp [emptyTwoStage, TwoStageSourceData.TwoStageSquareBundle,
    TwoStageSourceData.SChar, trivialBetaData]

/-- **The compiler is not unconditional.**  Without the adapter the conclusion
can fail: the endpoint with constant line has bundle `1/2`, while the two-stage
bundle built on the empty `β`-data vanishes. -/
theorem twoStage_normalForm_not_automatic :
    ∃ (E : PhysicalCenteredEndpoint) (S : TwoStageSourceData) (L : Finset ℕ+) (k : ℕ),
      E.physicalBundle L k ≠ S.TwoStageSquareBundle L k := by
  refine ⟨constLineEndpoint, emptyTwoStage, {(3 : ℕ+)}, 0, ?_⟩
  rw [constLineEndpoint_bundle, emptyTwoStage_bundle]
  norm_num

end TwoStageChar
end CurrentProgramme
end TwinPrimeProject
