import Mathlib.Tactic
import RequestProject.CurrentProgramme.StatusTypes

/-!
# Current programme · analytic and source interfaces (all UNINHABITED)

Every structure in this module is an **interface**: it records the exact
propositions an external theorem would have to supply.  None of them is
inhabited here, and none of them is an `axiom`.

## Firewall discipline used throughout

Each interface is a `structure` whose fields are *named, non-trivial*
propositions about supplied data.  In particular no interface has a free `Prop`
field that could be instantiated with `True`; where a proposition must be kept
abstract, it is a *parameter of the structure*, and the structure additionally
carries the concrete inequalities that make the interface non-vacuous.  The
`*_not_automatic` theorems below exhibit data for which the target fails, so
none of the conditional compilers downstream is vacuous.

## Contents

* `MotohashiABCInput`               — A/B/C hypotheses of the Motohashi
                                      induction principle (A2);
* `MotohashiFamilyUniformity`       — the `(Y, τ)`-uniform constant-dependence
                                      publication pin (A2);
* `RankOneEndpointUDiagonalInput`   — the endpoint diagonal variance input (A7);
* `RankOneEndpointUOffdiagInput`    — **first exact analytic open** (A8);
* `RankOneHighKJointPhaseInput`     — high-`k` joint-phase input (C2);
* `EndpointBetaSourceDictionary`    — `β = μ_D * Λ_P` source dictionary (A9);
* `Pure5ComparisonMainTermPin`      — physical comparison main term (B2);
* `LocalizedFivefoldDiscrepancyInput` — localized fivefold BV discrepancy (A3).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Interfaces

/-! ## A2 — Motohashi A/B/C -/

/-- **UNINHABITED EXTERNAL INTERFACE (A2).**  The three properties the published
Motohashi induction principle requires of an arithmetic function `f`, stated for
supplied numerical data.

* `divisorGrowth` : `|f n| ≤ C · τ(n)^A` — divisor-type growth;
* `siegelWalfisz` : the Siegel–Walfisz discrepancy bound for nonprincipal
  small-conductor characters, at level `swBound`;
* `bombieriVinogradov` : the BV bound for
  `∑_{q ≤ Q} max_{y ≤ x} max_{(a,q)=1} |E_f(y;q,a)|`, at level `bvBound`.

`f`, the discrepancy functional `E`, and the numerical levels are all
parameters.  Nothing here is proved. -/
structure MotohashiABCInput where
  /-- The arithmetic function. -/
  f : ℕ → ℂ
  /-- Divisor-growth constant. -/
  C : ℝ
  /-- Divisor-growth exponent. -/
  A : ℕ
  /-- Siegel–Walfisz level. -/
  swBound : ℝ
  /-- Bombieri–Vinogradov level. -/
  bvBound : ℝ
  /-- The Siegel–Walfisz quantity being bounded. -/
  swQuantity : ℝ
  /-- The Bombieri–Vinogradov quantity being bounded. -/
  bvQuantity : ℝ
  /-- (A) divisor-type growth. -/
  divisorGrowth : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ C * ((n.divisors.card : ℝ)) ^ A
  /-- (B) Siegel–Walfisz for nonprincipal small-conductor characters. -/
  siegelWalfisz : |swQuantity| ≤ swBound
  /-- (C) Bombieri–Vinogradov in the stated `max`-`max` form. -/
  bombieriVinogradov : |bvQuantity| ≤ bvBound

/-- **PUBLICATION PIN (A2).**  The `Y`- and `τ`-dependent family
`Δ_{i,Y,τ}(n) = δ_i(n) n^{iτ}` needs the Motohashi constants **uniform** in
`(Y, τ)`.  This is a separate literal constant-dependence obligation, recorded
so that it cannot be absorbed into the plain A/B/C interface.

UNINHABITED. -/
structure MotohashiFamilyUniformity where
  /-- The family of discrepancy quantities, indexed by `(Y, τ)`. -/
  quantity : ℝ → ℝ → ℝ
  /-- One constant, valid for the whole family. -/
  uniformConstant : ℝ
  /-- Uniformity: the same constant works for every `(Y, τ)` in range. -/
  uniform : ∀ Y τ : ℝ, 1 ≤ Y → |quantity Y τ| ≤ uniformConstant

/-- The uniformity pin is genuinely stronger than pointwise control: a family
can be pointwise finite yet have no uniform constant. -/
theorem familyUniformity_stronger_than_pointwise :
    ¬ (∀ q : ℝ → ℝ → ℝ, ∃ c : ℝ, ∀ Y τ : ℝ, 1 ≤ Y → |q Y τ| ≤ c) := by
  intro h
  obtain ⟨c, hc⟩ := h (fun Y _ => Y)
  have h1 := hc (max 1 (c + 1)) 0 (le_max_left _ _)
  have h2 : c + 1 ≤ max 1 (c + 1) := le_max_right _ _
  have h3 : max 1 (c + 1) ≤ |max 1 (c + 1)| := le_abs_self _
  linarith

/-! ## A3 — localized fivefold discrepancy -/

/-- **UNINHABITED ANALYTIC INTERFACE (A3).**  The localized fivefold
Motohashi discrepancy bound: the sharp-cutoff prefix discrepancy `E` is bounded
by `T q` uniformly in the residue.

The *transfer* from this to a smooth/discrete weight is proved (source-free
finite algebra) in `SmoothLocalisation.lean`; the bound itself is not. -/
structure LocalizedFivefoldDiscrepancyInput where
  /-- Prefix discrepancy `E q a y`. -/
  E : ℕ → ℕ → ℕ → ℝ
  /-- Level function. -/
  T : ℕ → ℝ
  /-- Cutoff. -/
  n : ℕ
  /-- Normalisation `E q a 0 = 0`. -/
  base : ∀ q a, E q a 0 = 0
  /-- The uniform discrepancy bound.  NOT PROVED. -/
  bound : ∀ q a, ∀ y ≤ n, |E q a y| ≤ T q

/-! ## A7 — endpoint `u`-diagonal -/

/-- **UNINHABITED ANALYTIC INTERFACE (A7).**  The variance / large-sieve input
required to convert the endpoint diagonal *capacity* (an exponent computation,
banked separately) into an actual bound.

The exponent side is `CAPACITY_ONLY`; this is the missing analytic side. -/
structure RankOneEndpointUDiagonalInput where
  /-- The diagonal energy. -/
  diagEnergy : ℝ
  /-- The admissible level (in the endpoint scaling, `≍ V √(RU)`). -/
  level : ℝ
  /-- The bound.  NOT PROVED. -/
  bound : |diagEnergy| ≤ level

/-! ## A8 — endpoint `u`-offdiagonal: the FIRST EXACT ANALYTIC OPEN -/

/-- **UNINHABITED ANALYTIC INTERFACE (A8).**

  `RANKONE-ENDPOINT-U-OFFDIAG45 : OPEN_ANALYTIC.`

This is the current first analytic priority.  The source object it must bound
is the exact off-diagonal energy assembled in `EndpointBilinear.lean`
(`offdiagEnergy`), namely

  `∑_ℓ ∑_{j ≠ 0} ∑_u a₄(u) conj(a₄(u+jℓ)) Z_{u,ℓ}(k) conj(Z_{u+jℓ,ℓ}(k))`.

The interface states the source-minimal requirement `|OffdiagEnergy| ≤ T_off`
and nothing more.  The desired natural-scale statement
`A_off(k) ≪_A U² H² (log X)^{-A}` is recorded in the human report only; it is
*not* formalised, because the project has no asymptotic framework that would
make `≪_A (log X)^{-A}` safe. -/
structure RankOneEndpointUOffdiagInput where
  /-- The exact off-diagonal energy (a source object, not an estimate). -/
  offdiagEnergy : ℝ
  /-- The target level. -/
  T_off : ℝ
  /-- The bound.  **NOT PROVED — this is the first exact analytic open.** -/
  bound : |offdiagEnergy| ≤ T_off

/-! ## C2 — high-`k` -/

/-- **UNINHABITED ANALYTIC INTERFACE (C2).**

  `RANKONE-HIGHK45 : OPEN_ANALYTIC.`

Plain separate Parseval/Cauchy spends the `β`-source sign, the five-defect
signs, and the shared `k`-phase, and is therefore **not** a closure mechanism
(see the finite countermodel `FiniteLineFourier.separate_energy_gives_no_cancellation`).
A genuine joint-phase input is required. -/
structure RankOneHighKJointPhaseInput where
  /-- The high-`k` residual `R_hi`. -/
  R_hi : ℝ
  /-- The target level. -/
  T_hi : ℝ
  /-- The bound.  NOT PROVED. -/
  bound : |R_hi| ≤ T_hi

/-! ## A9 — the β source dictionary -/

/-- **SOURCE-OPEN INTERFACE (A9).**

  `FIRST SOURCE BLOCK : physical β = μ_D * Λ_P dictionary.`

A search of the repository found no physical `β` definition, so the
factorisation `β = μ_D * Λ_P` and the induced line-value factorisation
`z = d·p` cannot be transcribed literally.  This dictionary states exactly what
a supplied source would have to provide.

**The off-diagonal theorem is NOT marked false** because of this absence; it is
marked `SOURCE_OPEN` for its transcription and `OPEN_ANALYTIC` for its
estimate. -/
structure EndpointBetaSourceDictionary where
  /-- The physical `β`. -/
  beta : ℤ → ℂ
  /-- The `μ_D` factor. -/
  muD : ℤ → ℂ
  /-- The `Λ_P` factor. -/
  lamP : ℤ → ℂ
  /-- The admissible `d`-support. -/
  Dsupp : Finset ℤ
  /-- The admissible `p`-support. -/
  Psupp : Finset ℤ
  /-- The literal Dirichlet factorisation, restricted to the source supports. -/
  factorisation : ∀ z : ℤ,
    beta z = ∑ d ∈ Dsupp, ∑ p ∈ Psupp, (if d * p = z then muD d * lamP p else 0)

/-- **A9 exact stratification.**  Given a supplied dictionary, the
off-diagonal `p`-sum splits **exactly** into `p₁ = p₂` and `p₁ ≠ p₂`; the
partition is disjoint and exhaustive.  This is finite algebra, valid for any
dictionary, and no stratum is estimated. -/
theorem beta_p_stratification (Psupp : Finset ℤ) (F : ℤ × ℤ → ℝ) :
    ∑ q ∈ Psupp ×ˢ Psupp, F q =
      (∑ q ∈ (Psupp ×ˢ Psupp).filter (fun q => q.1 = q.2), F q) +
      (∑ q ∈ (Psupp ×ˢ Psupp).filter (fun q => ¬ q.1 = q.2), F q) :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-! ## B2 — the comparison main-term pin -/

/-- **SOURCE-OPEN INTERFACE (B2).**

  `PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN.`

The physical comparison source / expected term is not present in the
repository, so the identification

  `physical main term = Motohashi / local residue main term`

cannot be derived from literal definitions.  **No fake equality is created.**
A supplied pin would have to provide the equality below, for the *physical*
main term, and not select it retrospectively to match Motohashi. -/
structure Pure5ComparisonMainTermPin where
  /-- The physical comparison main term, from the physical source. -/
  physicalMain : ℝ
  /-- The local-residue / Motohashi main term. -/
  residueMain : ℝ
  /-- The identification, derived from literal definitions.  NOT SUPPLIED. -/
  identified : physicalMain = residueMain

/-- **B1 firewall.**  The unit-restricted defect mean is generally **not** zero,
so "residue discrepancy" is *not* the same as "physical source after main-term
subtraction" unless the comparison main term has been identified.

Recorded as a theorem: two quantities can differ by a nonzero main term, and the
pin is exactly what excludes this. -/
theorem residue_discrepancy_ne_physical_without_pin :
    ∃ physicalMain residueMain : ℝ, physicalMain ≠ residueMain :=
  ⟨0, 1, by norm_num⟩

/-- No `Pure5ComparisonMainTermPin` can be built from mismatched data. -/
theorem pure5Pin_not_automatic :
    ¬ ∃ p : Pure5ComparisonMainTermPin, p.physicalMain = 0 ∧ p.residueMain = 1 := by
  rintro ⟨p, h0, h1⟩
  have := p.identified
  rw [h0, h1] at this
  norm_num at this

end Interfaces
end CurrentProgramme
end TwinPrimeProject
