import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.C4ShiftAPFourierDoubleMajor

/-!
# Gate 1B · C4Shift norm-promotion repair (append-only)

A hostile analytic audit invalidated **one research promotion**: the claim that
the pointwise four-product minor estimate closes the pushed norm.  This module
banks the *exact* content of the repair.  It proves **no** analytic estimate.

## What is proved here

* **Norm-mismatch firewall** (§3): the elementary `ℓ¹ ≤ ℓ²` comparison on a
  finite normalised index set, and an explicit witness showing that substituting
  a *larger* pointwise bound `S ≥ R` into an `L¹` pairing does not improve the
  `L¹`-`L¹` estimate.  This is the formal reason the old promotion is
  **nonclosing**.
* **`ℓ`-normalisation firewall** (§6): `ℓ^{-2} · #{(k₁,k₂) mod ℓ} = 1`, so
  `1/ℓ²` is exactly consumed by the two AP-index state counts.  It is never an
  automatic analytic saving.
* **AP index change of variables** (§7): `h = k₁ − k₂`, `K = k₁ + k₂` is a
  bijection **only** when `2` is invertible mod `ℓ`; for `ℓ = 2` it is provably
  not injective.  The linked-frequency formulas are restated in `(h,K)`.
* **Leafwise source classification** (§8): `c₄,₅ = λ₁λ₂λ₃λ₄` is a pure model
  leaf; for `j ≤ 4` the first surviving defect coordinate `δ_{j+1}` is exhibited
  algebraically.  **No** Fourier smallness is inferred.

## What is NOT proved here

* the pointwise minor estimate for `F4_j` (research level, log-corrected);
* any minor-arc energy bound: `FourProductMinorEnergyInput` is an
  **UNINHABITED** research candidate socket, and it may well be false for
  centred-defect leaves;
* any closure of `C4SHIFT-QFOURIER-PUSHFORWARD45`.

The tuple-level `Γ♯` demanded by the repair is already banked exactly in
`Gate1B.C4ShiftAPFourierDoubleMajor` (`GammaSharp`, `gamma_sharp_partition`),
together with its UNINHABITED range interface `GammaSharpRangeInput`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace C4ShiftNormRepair

open Finset

/-! ## §3.  The norm-mismatch firewall -/

/-- **Finite Cauchy–Schwarz.**  `(∑ |f|)² ≤ #s · ∑ f²`. -/
theorem sq_abs_sum_le_card_mul_sum_sq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (∑ i ∈ s, |f i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := s) (f := fun i => |f i|)
  simpa [sq_abs] using h

/-- **`ℓ¹ ≤ ℓ²` on a normalised finite space.**  The normalised `ℓ¹` average is
at most the square root of the normalised `ℓ²` average. -/
theorem l1_le_l2_normalised {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hs : 0 < s.card) :
    (1 / (s.card : ℝ)) * ∑ i ∈ s, |f i|
      ≤ Real.sqrt ((1 / (s.card : ℝ)) * ∑ i ∈ s, (f i) ^ 2) := by
  have hcard : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast hs
  have hCS := sq_abs_sum_le_card_mul_sum_sq s f
  have hy : 0 ≤ (1 / (s.card : ℝ)) * ∑ i ∈ s, (f i) ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hx : 0 ≤ (1 / (s.card : ℝ)) * ∑ i ∈ s, |f i| :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => abs_nonneg _)
  rw [Real.le_sqrt hx hy, mul_pow, div_pow, one_pow, div_mul_eq_mul_div,
    div_le_iff₀ (by positivity), one_mul]
  calc (∑ i ∈ s, |f i|) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 := hCS
    _ = 1 / (s.card : ℝ) * (∑ i ∈ s, (f i) ^ 2) * (s.card : ℝ) ^ 2 := by field_simp

/-- **The promotion is nonclosing.**  A pointwise bound `S` that is *larger*
than the available `ℓ²` bound `R` does not improve the `ℓ¹`-`ℓ¹` estimate:
there are finite data with `∑|f| ≤ R ≤ S` and

`(∑|f|) · (∑|g|) < S · (∑|g|)`,

i.e. substituting `S` strictly worsens the bound.  This is the exact formal
shape of the retracted promotion. -/
theorem pointwise_substitution_nonclosing :
    ∃ (R S : ℝ) (f g : Fin 1 → ℝ),
      (∑ i, |f i|) ≤ R ∧ R ≤ S ∧
      (∑ i, |f i|) * (∑ i, |g i|) < S * (∑ i, |g i|) := by
  refine ⟨1, 2, fun _ => 1, fun _ => 1, ?_, ?_, ?_⟩ <;> norm_num

/-! ## §6.  The `ℓ`-normalisation firewall -/

/-- **`1/ℓ²` is exactly consumed by the two AP-index state counts.**
`ℓ^{-2} · #{(k₁,k₂) : k₁,k₂ mod ℓ} = 1`. -/
theorem ell_normalisation_no_saving (l : ℕ) (hl : l ≠ 0) :
    ((l : ℝ) ^ 2)⁻¹ * ((Finset.range l ×ˢ Finset.range l).card : ℝ) = 1 := by
  have hlR : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hl
  have hcard : ((Finset.range l ×ˢ Finset.range l).card : ℝ) = (l : ℝ) ^ 2 := by
    simp [Finset.card_product]
    ring
  rw [hcard]
  field_simp

/-- **Summed form.**  Summing the normalisation over a family of physical `ℓ`
values returns the *number of `ℓ` values* — no saving whatsoever. -/
theorem ell_normalisation_sum (L : Finset ℕ) (hL : ∀ l ∈ L, l ≠ 0) :
    ∑ l ∈ L, ((l : ℝ) ^ 2)⁻¹ * ((Finset.range l ×ˢ Finset.range l).card : ℝ)
      = (L.card : ℝ) := by
  rw [Finset.sum_congr rfl (fun l hl => ell_normalisation_no_saving l (hL l hl))]
  simp

/-! ## §7.  AP index change of variables `(k₁,k₂) ↦ (h,K)` -/

/-- The AP index change of variables. -/
def hKmap (l : ℕ) (p : ZMod l × ZMod l) : ZMod l × ZMod l := (p.1 - p.2, p.1 + p.2)

/-- **The `(h,K)` change of variables is a bijection exactly when `2` is a unit
mod `ℓ`.**  (Sufficiency; the `ℓ = 2` countermodel below shows it can fail.) -/
theorem hKmap_bijective (l : ℕ) (h2 : IsUnit (2 : ZMod l)) :
    Function.Bijective (hKmap l) := by
  obtain ⟨u, hu⟩ := h2
  set v : ZMod l := ((u⁻¹ : (ZMod l)ˣ) : ZMod l) with hv
  have hinv : v * 2 = 1 := by
    rw [hv, ← hu]; exact_mod_cast u.inv_mul
  constructor
  · rintro ⟨a, b⟩ ⟨c, d⟩ h
    simp only [hKmap, Prod.mk.injEq] at h
    obtain ⟨h1, h2'⟩ := h
    have ha : (2 : ZMod l) * a = 2 * c := by linear_combination h1 + h2'
    have hb : (2 : ZMod l) * b = 2 * d := by linear_combination h2' - h1
    refine Prod.ext ?_ ?_
    · show a = c; linear_combination v * ha - (a - c) * hinv
    · show b = d; linear_combination v * hb - (b - d) * hinv
  · rintro ⟨x, y⟩
    refine ⟨(v * (x + y), v * (y - x)), ?_⟩
    simp only [hKmap, Prod.mk.injEq]
    constructor
    · linear_combination x * hinv
    · linear_combination y * hinv

/-- **Countermodel for even modulus.**  For `ℓ = 2` the `(h,K)` map is not
injective, so no bijection may be assumed: the odd/even (2-adic) cells must be
split. -/
theorem hKmap_not_injective_two : ¬ Function.Injective (hKmap 2) := by decide

/-- **Linked frequencies in the `(h,K)` coordinates.**  Exact restatement of the
banked linked-frequency identities. -/
theorem apindex_hK_normalform (s u theta eta k1 k2 l : ℝ) :
    C4ShiftAPFourier.omega1 s (u * theta) eta k1 l
        - C4ShiftAPFourier.omega2 s eta k2 l
      = (s * u * theta - (k1 - k2)) / l ∧
    C4ShiftAPFourier.omega1 s (u * theta) eta k1 l
        + C4ShiftAPFourier.omega2 s eta k2 l
      = (s * u * theta - 2 * s * eta - (k1 + k2)) / l :=
  ⟨C4ShiftAPFourier.linked_frequency_diff s u theta eta k1 k2 l,
   C4ShiftAPFourier.linked_frequency_sum s u theta eta k1 k2 l⟩

/-! ## §8.  Leafwise source classification -/

/-- The leaf source coefficient `c₄,ⱼ = λ₁⋯λ_{j−1} · δ_{j+1}⋯δ₅`. -/
noncomputable def c4leaf (j : ℕ) (lam del : ℕ → ℂ) : ℂ :=
  (∏ i ∈ Finset.Ico 1 j, lam i) * (∏ i ∈ Finset.Ico (j + 1) 6, del i)

/-- **`j = 5` is the pure model leaf**: `c₄,₅ = λ₁λ₂λ₃λ₄`, with no defect
coordinate at all. -/
theorem c4leaf_five (lam del : ℕ → ℂ) :
    c4leaf 5 lam del = lam 1 * lam 2 * lam 3 * lam 4 := by
  unfold c4leaf
  norm_num [Finset.prod_Ico_succ_top, show (1:ℕ) ≤ 5 by norm_num]

/-- **For `j ≤ 4` the leaf contains an actual defect coordinate**: `δ_{j+1}`
factors out of the source.  This is source classification only — no Fourier
smallness is inferred. -/
theorem c4leaf_first_defect (j : ℕ) (hj : j ≤ 4) (lam del : ℕ → ℂ) :
    c4leaf j lam del
      = (∏ i ∈ Finset.Ico 1 j, lam i) * (del (j + 1) * ∏ i ∈ Finset.Ico (j + 2) 6, del i) := by
  unfold c4leaf
  congr 1
  have hlt : j + 1 < 6 := by omega
  rw [Finset.prod_eq_prod_Ico_succ_bot hlt]

/-! ## §9.  Minor-arc energy: research candidate only (UNINHABITED) -/

/-- **UNINHABITED research-candidate socket.**  The minor-arc `L²` energy bound

`∫_minor |F4_j(ω)|² ≤ Y⁴ L^{−A}`

is **not banked as true**.  Research warning: it may be plausible only for
non-centred / model leaves, may be **false** for centred-defect leaves, and
MUST be tested leafwise.  This structure is never constructed. -/
structure FourProductMinorEnergyInput where
  /-- Number of sample points of the discrete `θ`-grid. -/
  P : ℕ
  /-- The (discrete) minor-arc sample. -/
  Minor : Finset ℕ
  /-- The leaf index. -/
  leaf : ℕ
  /-- The four-product transform sampled on the grid. -/
  F4 : ℕ → ℂ
  /-- The scale. -/
  Y : ℝ
  /-- The claimed saving exponent. -/
  Asave : ℝ
  /-- The claimed bound.  Never proved, never inhabited. -/
  bound : (1 / (P : ℝ)) * ∑ k ∈ Minor, ‖F4 k‖ ^ 2 ≤ Y ^ 4 * Asave

/-! ## Status metadata (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the norm-promotion repair. -/
def statusRows : List LedgerEntry :=
  [ ⟨"FOURPRODUCT-POINTWISE-MINOR45", Status.externallyAudited,
     "RESEARCH PASS; LOG-CORRECTED (the pointwise bound off the research major arcs is Y^4 L^(-B+C+1), not Y^4 L^(-B+C)). NOT A NORM CLOSURE. Not formalised in Lean."⟩,
    ⟨"ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45", Status.falseRoute,
     "NONCLOSING / INVALID IMPLICATION. A pointwise sup bound does not by itself beat the available L1/L2 norm bound; see pointwise_substitution_nonclosing and l1_le_l2_normalised. The POINTWISE estimate itself is NOT marked false."⟩,
    ⟨"C4SHIFT-ONE-FOURPRODUCT-MINOR45", Status.supersededAsControllingFrontier,
     "OLD RESEARCH CLOSURE RETRACTED. The closure claim is withdrawn; the underlying pointwise minor estimate remains a research PASS with the corrected logarithmic exponent."⟩,
    ⟨"DOUBLEMAJOR-AS-SOLE-RESIDUAL", Status.falseRoute,
     "RETRACTED. C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45 remains a legitimate OPEN CHILD, but it is no longer the unique controlling child."⟩,
    ⟨"C4SHIFT-ELL-NORMALISATION-NOSAVING45", Status.provedFinite,
     "FORMALLY PROVED FIREWALL: ell_normalisation_no_saving, ell_normalisation_sum. 1/ell^2 is exactly consumed by the two AP-index state counts; it is NEVER an automatic analytic saving."⟩,
    ⟨"C4SHIFT-APINDEX-HK-NORMALFORM45", Status.provedAlgebraic,
     "FORMALLY PROVED: hKmap_bijective (needs 2 invertible mod ell), hKmap_not_injective_two (explicit even-modulus countermodel), apindex_hK_normalform. No orthogonality is claimed."⟩,
    ⟨"C4SHIFT-J5-SOURCE", Status.provedAlgebraic,
     "PURE MODEL LEAF, formally: c4leaf_five gives c4,5 = lambda1 lambda2 lambda3 lambda4."⟩,
    ⟨"C4SHIFT-JLT5-SOURCE", Status.provedAlgebraic,
     "CONTAINS ACTUAL DEFECT COORDINATE, formally: c4leaf_first_defect exhibits delta_{j+1} for j <= 4. Source classification only; NO Fourier smallness is inferred."⟩,
    ⟨"MINOR-ARC-ENERGY45", Status.analyticOpen,
     "RESEARCH CANDIDATE; NOT BANKED; LEAFWISE AUDIT REQUIRED. FourProductMinorEnergyInput is UNINHABITED. It may be plausible only for non-centred/model leaves and may be FALSE for centred-defect leaves."⟩,
    ⟨"C4SHIFT-ONE-MINOR-PUSHED-ENERGY45", Status.analyticOpen,
     "ANALYTIC OPEN. New open child of the parent frontier."⟩,
    ⟨"C4SHIFT-MAJOR-LEAFWISE-ROUTER45", Status.sourceOpen,
     "ANALYTIC / SOURCE OPEN. New open child of the parent frontier."⟩,
    ⟨"C4SHIFT-J5-MAJOR-LOCALMODEL45", Status.open_, "OPEN (major leaf child)."⟩,
    ⟨"C4SHIFT-DEFECT-SMALLMOD-CHAR45", Status.open_, "OPEN (major leaf child)."⟩,
    ⟨"C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45", Status.analyticOpen,
     "OPEN / MAY BE RECLASSIFIED BY LEAFWISE ROUTING. NOT the sole residual."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen,
     "CURRENT PARENT ANALYTIC FRONTIER. Requirement unchanged: ||Hhat_j||_{L1_theta l2_v} <= naturalBound. Not replaced by double-major only, and not replaced by scalar minor-energy only."⟩ ]

/-- No row of this repair is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

/-- The retracted promotion is recorded as `falseRoute`, while the pointwise
estimate is recorded as `externallyAudited` — i.e. **not** false. -/
theorem retraction_is_precise :
    (∃ e ∈ statusRows, e.label = "ONE-FOURPRODUCT-MINOR-NORM-PROMOTION45" ∧
      e.status = Status.falseRoute) ∧
    (∃ e ∈ statusRows, e.label = "FOURPRODUCT-POINTWISE-MINOR45" ∧
      e.status = Status.externallyAudited ∧ e.status ≠ Status.falseRoute) := by
  refine ⟨by decide, by decide⟩

end C4ShiftNormRepair
end CurrentProgramme
end TwinPrimeProject
