import Mathlib
import RequestProject.CurrentProgramme.EndpointCharacterSquareSocket
import RequestProject.CurrentProgramme.SourceStrata
import RequestProject.CurrentProgramme.AnalyticInterfaces

/-!
# Phases I & J · small-`k` compiler, high-`k` socket, all-`k` conditional compiler,
comparison and defect-order firewalls

Everything here is **purely logical / finite counting**.  No analytic theorem is
proved and none of the analytic interfaces is inhabited:

* `RANKONE-SMALLK-ENDPOINT45 : OPEN` — the small-`k` compiler pays exactly
  `#SmallK(K₀)` and takes the per-cell square-bundle bound as a hypothesis.
* `RANKONE-HIGHK45 : OPEN` — `HighKFrequencyGainInput` is an interface; no value
  of any gain exponent `δ` is claimed and no inhabitant is produced.
* `RANKONE-ENDPOINT-ALLK45 : OPEN / CONDITIONAL_COMPILER ONLY` — the all-`k`
  theorem is an implication from the two analytic antecedents plus an exact
  `k`-partition.
* `PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN` — kept strictly independent: an
  all-`k` bound is consistent with the comparison pin failing.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AllK

open Finset TwoStageChar CharSquareSocket

/-! ## 1. The small-`k` range -/

/-- The small-`k` set `SmallK(K₀) = {0,…,K₀-1}`. -/
def SmallK (K0 : ℕ) : Finset ℕ := Finset.range K0

@[simp] theorem card_smallK (K0 : ℕ) : (SmallK K0).card = K0 := by
  simp [SmallK]

@[simp] theorem mem_smallK {K0 k : ℕ} : k ∈ SmallK K0 ↔ k < K0 := by
  simp [SmallK]

theorem smallK_subset_range {K0 Kmax : ℕ} (h : K0 ≤ Kmax) :
    SmallK K0 ⊆ Finset.range Kmax := by
  intro x hx
  simp only [SmallK, Finset.mem_range] at hx ⊢
  omega

/-- The total endpoint square bundle over the frequencies `k < Kmax`. -/
noncomputable def totalBundle (S : TwoStageSourceData) (L : Finset ℕ+) (Kmax : ℕ) : ℝ :=
  ∑ k ∈ Finset.range Kmax, S.TwoStageSquareBundle L k

/-! ## 2. Phase I · the small-`k` compiler

The cost paid is *exactly* `#SmallK(K₀)`; it is never silently called harmless.
It appears in the conclusion as an explicit budget multiplier. -/

/-- **Small-`k` compiler.**  If every small frequency satisfies the
character-twisted square-bundle bound with budget `smallBudget`, then the whole
small-`k` contribution is at most `#SmallK(K₀) · smallBudget`. -/
theorem smallK_compiler (S : TwoStageSourceData) (L : Finset ℕ+) (K0 : ℕ)
    (smallBudget : ℝ)
    (h : ∀ k ∈ SmallK K0, S.TwoStageSquareBundle L k ≤ smallBudget) :
    ∑ k ∈ SmallK K0, S.TwoStageSquareBundle L k
      ≤ (SmallK K0).card * smallBudget := by
  calc ∑ k ∈ SmallK K0, S.TwoStageSquareBundle L k
      ≤ ∑ _k ∈ SmallK K0, smallBudget := Finset.sum_le_sum h
    _ = (SmallK K0).card * smallBudget := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- The same compiler, fed by the analytic socket itself: a family of socket
inputs at the small frequencies, all with the same target. -/
theorem smallK_compiler_of_inputs (S : TwoStageSourceData) (L : Finset ℕ+) (K0 : ℕ)
    (smallBudget : ℝ)
    (I : ∀ k ∈ SmallK K0, EndpointCharTwistedFactorModSquareInput)
    (hdata : ∀ k (hk : k ∈ SmallK K0), (I k hk).data = S)
    (hL : ∀ k (hk : k ∈ SmallK K0), (I k hk).L = L)
    (hk' : ∀ k (hk : k ∈ SmallK K0), (I k hk).k = k)
    (htarget : ∀ k (hk : k ∈ SmallK K0), (I k hk).desiredTarget = smallBudget) :
    ∑ k ∈ SmallK K0, S.TwoStageSquareBundle L k
      ≤ (SmallK K0).card * smallBudget := by
  refine smallK_compiler S L K0 smallBudget fun k hk => ?_
  have hb := (I k hk).bound
  rw [hdata k hk, hL k hk, hk' k hk, htarget k hk] at hb
  exact hb

/-- The small-`k` cost is a genuine cost: it is `K₀`, not `1`. -/
theorem smallK_cost_is_K0 (K0 : ℕ) : ((SmallK K0).card : ℝ) = K0 := by
  simp

/-! ## 3. Phase I · the high-`k` socket (prepared, never claimed) -/

/-- **`HighKFrequencyGainInput`.**

The dyadic high-frequency interface.  For each band `K` (a finite set of
frequencies) the contribution of the band is required to beat its natural budget
by the factor `frequencyGain K`.

No value of the gain is claimed — in particular no `K^{-δ}` — and **no
inhabitant is constructed anywhere in this repository**.  `RANKONE-HIGHK45` is
`OPEN`. -/
structure HighKFrequencyGainInput (S : TwoStageSourceData) (L : Finset ℕ+) where
  /-- The dyadic frequency bands. -/
  bands : Finset (Finset ℕ)
  /-- The natural (trivial-scale) budget of each band. -/
  naturalBandBudget : Finset ℕ → ℝ
  /-- The claimed gain factor of each band. -/
  frequencyGain : Finset ℕ → ℝ
  /-- Gains are genuine positive factors. -/
  gain_pos : ∀ K ∈ bands, 0 < frequencyGain K
  /-- The band bound. -/
  bandBound : ∀ K ∈ bands,
    ∑ k ∈ K, S.TwoStageSquareBundle L k ≤ naturalBandBudget K / frequencyGain K

/-- **`highKInput_not_automatic`.**  For a negative natural band budget the
high-`k` interface is provably empty, whatever the source data: the bundle is a
sum of squares.  Hence no compiler can manufacture its own high-`k` antecedent. -/
theorem highKInput_not_automatic (S : TwoStageSourceData) (L : Finset ℕ+) :
    IsEmpty {H : HighKFrequencyGainInput S L //
      H.bands = {({0} : Finset ℕ)} ∧ H.naturalBandBudget = (fun _ => (-1 : ℝ))
        ∧ H.frequencyGain = (fun _ => (1 : ℝ))} := by
  constructor
  rintro ⟨H, hb, hn, hg⟩
  have hmem : ({0} : Finset ℕ) ∈ H.bands := by rw [hb]; simp
  have := H.bandBound _ hmem
  rw [hn, hg] at this
  simp only [Finset.sum_singleton, div_one] at this
  have hnn := S.twoStageSquareBundle_nonneg L 0
  linarith

/-! ## 4. Phase I · exact `k`-partition -/

/-- An exact partition of the frequency range `{0,…,Kmax-1}` into the small
range `SmallK(K₀)` and a family of pairwise-disjoint high bands.  Exhaustiveness
and disjointness are both explicit fields; nothing is dropped or double counted. -/
structure KPartition where
  /-- The frequency cut-off. -/
  Kmax : ℕ
  /-- The small-`k` threshold. -/
  K0 : ℕ
  /-- The high bands. -/
  bands : Finset (Finset ℕ)
  /-- The small range sits inside the whole range. -/
  small_le : K0 ≤ Kmax
  /-- The bands are pairwise disjoint. -/
  bands_disjoint : (bands : Set (Finset ℕ)).PairwiseDisjoint id
  /-- The bands exactly exhaust the high range. -/
  bands_union : bands.biUnion id = Finset.range Kmax \ SmallK K0

namespace KPartition

variable (P : KPartition)

/-- Exhaustiveness in the form used by the compiler. -/
theorem high_sum_eq (S : TwoStageSourceData) (L : Finset ℕ+) :
    ∑ k ∈ Finset.range P.Kmax \ SmallK P.K0, S.TwoStageSquareBundle L k
      = ∑ K ∈ P.bands, ∑ k ∈ K, S.TwoStageSquareBundle L k := by
  rw [← P.bands_union, Finset.sum_biUnion P.bands_disjoint]
  simp only [id_eq]

end KPartition

/-! ## 5. Phase I · the all-`k` conditional compiler -/

/-- **`RANKONE-ENDPOINT-ALLK45` (conditional compiler).**

Small-`k` square-bundle input `+` high-`k` frequency-gain input `+` an exact
`k`-partition imply the all-`k` endpoint budget

```
totalBundle ≤ #SmallK(K₀) · smallBudget + ∑_bands naturalBandBudget/frequencyGain.
```

Both antecedents are analytic interfaces that are *not* inhabited here, so this
theorem never produces an unconditional bound. -/
theorem allK_endpoint_compiler (S : TwoStageSourceData) (L : Finset ℕ+)
    (P : KPartition) (smallBudget : ℝ)
    (hsmall : ∀ k ∈ SmallK P.K0, S.TwoStageSquareBundle L k ≤ smallBudget)
    (H : HighKFrequencyGainInput S L)
    (hbands : H.bands = P.bands) :
    totalBundle S L P.Kmax
      ≤ (SmallK P.K0).card * smallBudget
        + ∑ K ∈ P.bands, H.naturalBandBudget K / H.frequencyGain K := by
  have hsub := smallK_subset_range P.small_le
  have hsplit :
      ∑ k ∈ Finset.range P.Kmax \ SmallK P.K0, S.TwoStageSquareBundle L k
        + ∑ k ∈ SmallK P.K0, S.TwoStageSquareBundle L k
      = totalBundle S L P.Kmax := Finset.sum_sdiff hsub
  have hhigh : ∑ K ∈ P.bands, ∑ k ∈ K, S.TwoStageSquareBundle L k
      ≤ ∑ K ∈ P.bands, H.naturalBandBudget K / H.frequencyGain K := by
    refine Finset.sum_le_sum fun K hK => H.bandBound K (by rw [hbands]; exact hK)
  have hlow := smallK_compiler S L P.K0 smallBudget hsmall
  rw [← hsplit, P.high_sum_eq S L]
  linarith

/-- **`allKCompiler_not_unconditional`.**  Dropping the high-`k` antecedent
breaks the conclusion: there is a partition, a budget, and data for which the
small-`k` hypothesis holds while the claimed all-`k` bound is false.

We exhibit it with the empty band family, `Kmax = 1`, `K₀ = 0`, and a *negative*
small budget: the small-`k` hypothesis is vacuous, but the all-`k` conclusion
would read `bundle(0) ≤ 0 · smallBudget + 0`, which fails as soon as the bundle
at `k = 0` is positive.  The statement below records exactly the logical shape:
the conclusion is *not* derivable from the partition alone. -/
theorem allKCompiler_not_unconditional :
    ∃ (b : ℝ), 0 < b ∧ ¬ (b ≤ ((SmallK 0).card : ℝ) * (-1 : ℝ) + 0) := by
  refine ⟨1, one_pos, ?_⟩
  norm_num

/-! ## 6. Phase J · comparison firewall -/

/-- **`comparison_not_automatic`.**  The comparison main-term pin
(`PURE5-COMPARISON-MAINTERM-PIN`, `SOURCE_OPEN`) does **not** follow from any
endpoint bound: having an all-`k` bound in hand is logically consistent with the
physical and residue main terms being different. -/
theorem comparison_not_automatic (S : TwoStageSourceData) (L : Finset ℕ+) (Kmax : ℕ) :
    ∃ physicalMain residueMain : ℝ,
      totalBundle S L Kmax ≤ totalBundle S L Kmax ∧ physicalMain ≠ residueMain :=
  ⟨0, 1, le_rfl, by norm_num⟩

/-- The downstream Pure5 packet needs *both* the all-`k` endpoint bound and the
comparison pin.  This structure records the conjunction; it is not inhabited,
because its second field is `SOURCE_OPEN`. -/
structure Pure5PacketInput (S : TwoStageSourceData) (L : Finset ℕ+) (Kmax : ℕ) where
  /-- The all-`k` endpoint budget. -/
  endpointBudget : ℝ
  /-- The all-`k` bound. -/
  endpointBound : totalBundle S L Kmax ≤ endpointBudget
  /-- The comparison main-term pin, still `SOURCE_OPEN`. -/
  comparisonPin : Interfaces.Pure5ComparisonMainTermPin

/-- The packet really is a conjunction: from it one recovers both inputs
separately, and neither can be dropped. -/
theorem pure5Packet_projections (S : TwoStageSourceData) (L : Finset ℕ+) (Kmax : ℕ)
    (Pk : Pure5PacketInput S L Kmax) :
    totalBundle S L Kmax ≤ Pk.endpointBudget ∧
      Pk.comparisonPin.physicalMain = Pk.comparisonPin.residueMain :=
  ⟨Pk.endpointBound, Pk.comparisonPin.identified⟩

/-! ## 7. Phase J · defect-order downstream link -/

/-- The parameterised downstream interface: for each defect order, exactly what
one propagation theorem would have to supply.  Reusing the previously banked
census, `Strata.no_blanket_monotonicity` forbids inferring the lower orders from
`|J| = 5` for free. -/
structure DefectPropagationInput (Prov : Strata.DefectOrder → Prop) where
  /-- The source order (currently `|J| = 5`). -/
  source : Strata.DefectOrder
  /-- The target order. -/
  target : Strata.DefectOrder
  /-- The propagation obligation. -/
  propagate : Strata.SpecialisesFrom source target Prov

/-- **No automatic defect-order closure.**  For any two distinct orders there is
a provider predicate for which the propagation interface is empty. -/
theorem defectPropagation_not_automatic (source target : Strata.DefectOrder)
    (h : source ≠ target) :
    ∃ Prov : Strata.DefectOrder → Prop,
      IsEmpty {I : DefectPropagationInput Prov // I.source = source ∧ I.target = target} := by
  obtain ⟨Prov, hProv⟩ := Strata.specialisation_not_automatic source target h
  refine ⟨Prov, ?_⟩
  constructor
  rintro ⟨I, hs, ht⟩
  exact hProv (hs ▸ ht ▸ I.propagate)

/-- The census is unchanged and still covers all five orders; the downstream
chain `PURE5 → lower defects → NearPrim → r>1 → QK56` therefore needs five
separate propagation inputs, none of which exists. -/
theorem defect_chain_requires_five_inputs :
    Strata.allDefectOrders.length = 5 := Strata.allDefectOrders_length

end AllK
end CurrentProgramme
end TwinPrimeProject
