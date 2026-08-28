import Mathlib
import RequestProject.CurrentProgramme.EndpointCharacterCentering
import RequestProject.CurrentProgramme.EndpointTwoStageCharacterForm

/-!
# Phases E, F, G · natural-scale norm bank, scalarisation tax, Hilbert firewall

**Exact finite algebra and rational exponent arithmetic only.**  Nothing here is
an analytic estimate, and no interface is inhabited.

## Phase E

* `interval_residue_fibre_card_le` — the exact residue-class multiplicity in an
  interval: `#{x ∈ [a,b) : x ≡ v (r)} ≤ 1 + ⌊(b−a)/r⌋`.  No informal `U/ℓ`.
* `characterParseval_real` — the real form of the Phase A Parseval identity.
* `characterBundleEnergy_le_multiplicity` — the **energy compiler**: the
  non-principal bundle is at most the exact fibre multiplicity times the `ℓ²`
  norm of the coefficients.
* `naturalScale_*` — the endpoint scales `U = Y⁴`, `R = Y^{5/2}L^{-1}`,
  `H = Y^{5/2}L`, `Q = U·H = Y^{13/2}L` as **rational `Y`-exponents**; logs are
  *not* pretended to be powers, they are simply absent from the exponent
  ledger.

## Phase F

* `scalarisation_cost` — a scalar cell bound `|S(ℓ,χ,k)| ≤ B` costs the full
  weighted number of character cells.
* `scalarizationEnergyTax`, `scalarizationAmplitudeTax` — the `X`-exponents
  `5/18` and `5/36`.  These are *capacity* records: no analytic theorem is
  claimed to supply `B`.

## Phase G

* `sharedCharacterProduct_not_singleLinearLift` — the shared coordinate
  `χ(m)·χ(r)` is not a function of the `m`-vector alone, so no free
  Hilbert-valued lift is banked.  This is deliberately **not** an impossibility
  statement about all vector-valued theorems.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace BundleNorm

open Finset CharacterCentering

/-! ## 1. Phase E · exact residue-class multiplicity -/

/-- **`interval_residue_fibre_card_le`.**  In the integer interval `[a,b)` the
number of elements in a fixed residue class mod `r` is at most
`1 + ⌊(b−a)/r⌋`.  Exact `Int` statement; no informal `length/ℓ`. -/
theorem interval_residue_fibre_card_le (a b v r : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    (((Finset.Ico a b).filter (fun x => x ≡ v [ZMOD r])).card : ℤ)
      ≤ (b - a) / r + 1 := by
  classical
  have hmap : ∀ x ∈ (Finset.Ico a b).filter (fun x => x ≡ v [ZMOD r]),
      (x - a) / r ∈ Finset.Icc (0 : ℤ) ((b - a) / r) := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_Ico] at hx
    refine Finset.mem_Icc.2 ⟨Int.ediv_nonneg (by omega) (le_of_lt hr), ?_⟩
    exact Int.ediv_le_ediv hr (by omega)
  have hinj : ∀ x ∈ (Finset.Ico a b).filter (fun x => x ≡ v [ZMOD r]),
      ∀ y ∈ (Finset.Ico a b).filter (fun x => x ≡ v [ZMOD r]),
        (x - a) / r = (y - a) / r → x = y := by
    intro x hx y hy hq
    rw [Finset.mem_filter] at hx hy
    have hxy : x ≡ y [ZMOD r] := hx.2.trans hy.2.symm
    have hmod : (x - a) % r = (y - a) % r := (Int.ModEq.sub_right a hxy)
    have hx' := Int.mul_ediv_add_emod (x - a) r
    have hy' := Int.mul_ediv_add_emod (y - a) r
    rw [hq, hmod] at hx'
    omega
  have hcard := Finset.card_le_card_of_injOn (f := fun x : ℤ => (x - a) / r)
    (s := (Finset.Ico a b).filter (fun x => x ≡ v [ZMOD r]))
    (t := Finset.Icc (0 : ℤ) ((b - a) / r))
    (fun x hx => Finset.mem_coe.mpr (hmap x (Finset.mem_coe.mp hx)))
    (fun x hx y hy hxy => hinj x (Finset.mem_coe.mp hx) y (Finset.mem_coe.mp hy) hxy)
  have hIcc : (Finset.Icc (0 : ℤ) ((b - a) / r)).card = ((b - a) / r + 1).toNat := by
    rw [Int.card_Icc]
    congr 1
    omega
  rw [hIcc] at hcard
  have hnn : 0 ≤ (b - a) / r := Int.ediv_nonneg (by omega) hr.le
  omega

/-! ## 2. Phase E · real Parseval and the energy compiler -/

variable (l : ℕ) [NeZero l] {ι : Type*}

/-- **Real form of the Phase A Parseval identity.** -/
theorem characterParseval_real (I : Finset ι) (v : ι → (ZMod l)ˣ) (c : ι → ℂ) :
    (l.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
        Complex.normSq (charForm l I v c χ)
      = ∑ i ∈ I, ∑ j ∈ I,
          (if (v i : ZMod l) = (v j : ZMod l) then (c i * (starRingEnd ℂ) (c j)) else 0).re := by
  classical
  have h := characterParseval_unitSector l I v c
  have hL : ((l.totient : ℂ))⁻¹ * ∑ χ : DirichletCharacter ℂ l,
      (Complex.normSq (charForm l I v c χ) : ℂ)
        = (((l.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
            Complex.normSq (charForm l I v c χ) : ℝ) : ℂ) := by
    push_cast
    rw [Finset.sum_congr rfl fun χ _ => rfl]
  rw [hL] at h
  have := congrArg Complex.re h
  rw [Complex.ofReal_re] at this
  rw [this, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => Complex.re_sum _ _

/-- **`characterBundleEnergy_le_multiplicity` — the energy compiler.**

With `F` an explicit bound for the residue fibre multiplicity of the family
`v`, the non-principal character bundle is at most `F` times the `ℓ²`-norm of
the coefficients.  The multiplicity is kept exact: it is a hypothesis, not an
inserted `U/ℓ`. -/
theorem characterBundleEnergy_le_multiplicity (I : Finset ι) (v : ι → (ZMod l)ˣ)
    (c : ι → ℂ) (F : ℝ)
    (hF : ∀ i ∈ I, ((I.filter (fun j => (v j : ZMod l) = (v i : ZMod l))).card : ℝ) ≤ F) :
    (l.totient : ℝ)⁻¹ * ∑ χ ∈ nonprincipalChars l,
        Complex.normSq (charForm l I v c χ)
      ≤ F * ∑ i ∈ I, Complex.normSq (c i) := by
  classical
  set A : ι → ℝ := fun i => Complex.normSq (c i) with hA
  have hAnonneg : ∀ i, 0 ≤ A i := fun i => Complex.normSq_nonneg _
  -- (1) pass from the non-principal family to the full family
  have hsub : ∑ χ ∈ nonprincipalChars l, Complex.normSq (charForm l I v c χ)
      ≤ ∑ χ : DirichletCharacter ℂ l, Complex.normSq (charForm l I v c χ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_
    intro χ _ _
    exact Complex.normSq_nonneg _
  have htot : (0 : ℝ) ≤ (l.totient : ℝ)⁻¹ := by positivity
  have hstep1 : (l.totient : ℝ)⁻¹ * ∑ χ ∈ nonprincipalChars l,
      Complex.normSq (charForm l I v c χ)
        ≤ (l.totient : ℝ)⁻¹ * ∑ χ : DirichletCharacter ℂ l,
            Complex.normSq (charForm l I v c χ) := by
    exact mul_le_mul_of_nonneg_left hsub htot
  -- (2) Parseval
  rw [characterParseval_real l I v c] at hstep1
  refine hstep1.trans ?_
  -- (3) termwise bound `Re(c_i conj c_j) ≤ (A i + A j)/2`
  have hterm : ∀ i ∈ I, ∀ j ∈ I,
      (if (v i : ZMod l) = (v j : ZMod l) then (c i * (starRingEnd ℂ) (c j)) else 0).re
        ≤ (if (v i : ZMod l) = (v j : ZMod l) then (A i + A j) / 2 else 0) := by
    intro i _ j _
    by_cases h : (v i : ZMod l) = (v j : ZMod l)
    · rw [if_pos h, if_pos h]
      have h1 : (c i * (starRingEnd ℂ) (c j)).re ≤ ‖c i * (starRingEnd ℂ) (c j)‖ :=
        Complex.re_le_norm _
      have h2 : ‖c i * (starRingEnd ℂ) (c j)‖ = ‖c i‖ * ‖c j‖ := by
        rw [norm_mul, RCLike.norm_conj]
      have h3 : ‖c i‖ * ‖c j‖ ≤ (‖c i‖ ^ 2 + ‖c j‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖c i‖ - ‖c j‖)]
      have h4 : A i = ‖c i‖ ^ 2 := by rw [hA]; simp [Complex.normSq_eq_norm_sq]
      have h5 : A j = ‖c j‖ ^ 2 := by rw [hA]; simp [Complex.normSq_eq_norm_sq]
      rw [h4, h5]
      linarith [h1, h2 ▸ h1]
    · rw [if_neg h, if_neg h]
      simp
  have hbound1 : ∑ i ∈ I, ∑ j ∈ I,
      (if (v i : ZMod l) = (v j : ZMod l) then (c i * (starRingEnd ℂ) (c j)) else 0).re
        ≤ ∑ i ∈ I, ∑ j ∈ I,
            (if (v i : ZMod l) = (v j : ZMod l) then (A i + A j) / 2 else 0) := by
    refine Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hterm i hi j hj
  refine hbound1.trans ?_
  -- (4) split the symmetric bound and count fibres
  have hsplit : ∀ i j : ι,
      (if (v i : ZMod l) = (v j : ZMod l) then (A i + A j) / 2 else 0)
        = (if (v i : ZMod l) = (v j : ZMod l) then A i / 2 else 0)
          + (if (v i : ZMod l) = (v j : ZMod l) then A j / 2 else 0) := by
    intro i j
    by_cases h : (v i : ZMod l) = (v j : ZMod l)
    · simp only [h, if_pos]
      ring
    · simp [h]
  have hfilter : ∀ i : ι,
      (I.filter (fun j => (v i : ZMod l) = (v j : ZMod l)))
        = (I.filter (fun j => (v j : ZMod l) = (v i : ZMod l))) := by
    intro i
    exact Finset.filter_congr fun j _ => by rw [eq_comm]
  have hT1 : ∑ i ∈ I, ∑ j ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then A i / 2 else 0)
      ≤ (F / 2) * ∑ i ∈ I, A i := by
    have hstep : ∀ i ∈ I, ∑ j ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then A i / 2 else 0)
        ≤ (F / 2) * A i := by
      intro i hi
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hfilter i]
      have := hF i hi
      have hAi := hAnonneg i
      nlinarith
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.mul_sum]
  have hT2 : ∑ i ∈ I, ∑ j ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then A j / 2 else 0)
      ≤ (F / 2) * ∑ i ∈ I, A i := by
    rw [Finset.sum_comm]
    have hstep : ∀ j ∈ I, ∑ i ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then A j / 2 else 0)
        ≤ (F / 2) * A j := by
      intro j hj
      rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have := hF j hj
      have hAj := hAnonneg j
      nlinarith
    refine (Finset.sum_le_sum hstep).trans ?_
    rw [Finset.mul_sum]
  have : ∑ i ∈ I, ∑ j ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then (A i + A j) / 2 else 0)
      = (∑ i ∈ I, ∑ j ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then A i / 2 else 0))
        + ∑ i ∈ I, ∑ j ∈ I, (if (v i : ZMod l) = (v j : ZMod l) then A j / 2 else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hsplit i j
  rw [this]
  linarith

end BundleNorm

/-! ## 3. Phase E/F · the natural-scale exponent ledger -/

namespace ScaleLedger

/-- The `Y`-exponent of `U = Y⁴`. -/
def expU : ℚ := 4

/-- The `Y`-exponent of `R = Y^{5/2} L^{-1}` (the `L`-factor is *not* an
exponent and is deliberately absent). -/
def expR : ℚ := 5 / 2

/-- The `Y`-exponent of `H = Y^{5/2} L`. -/
def expH : ℚ := 5 / 2

/-- The `Y`-exponent of `Q = U·H`. -/
def expQ : ℚ := expU + expH

theorem expQ_value : expQ = 13 / 2 := by norm_num [expQ, expU, expH]

/-- **`U² H²` has `Y`-exponent `13`.** -/
theorem naturalScale_UH_exponent : 2 * expU + 2 * expH = 13 := by
  norm_num [expU, expH]

/-- **`R · (U/R) · U · H²` has the same `Y`-exponent `13`.** -/
theorem naturalScale_split_exponent : expR + (expU - expR) + expU + 2 * expH = 13 := by
  norm_num [expU, expR, expH]

/-- The two natural-scale routes agree exactly. -/
theorem naturalScale_routes_agree :
    2 * expU + 2 * expH = expR + (expU - expR) + expU + 2 * expH := by
  norm_num [expU, expR, expH]

/-- The endpoint normalisation `X = Y⁹` used by the cost ledger. -/
def expXinY : ℚ := 9

/-- **`ENDPOINT-SCALARIZATION-ENERGY-TAX45` (capacity only).**  The modulus
family `R` has `X`-exponent `5/18`. -/
def scalarizationEnergyTax : ℚ := expR / expXinY

theorem scalarizationEnergyTax_value : scalarizationEnergyTax = 5 / 18 := by
  norm_num [scalarizationEnergyTax, expR, expXinY]

/-- **`ENDPOINT-SCALARIZATION-AMPLITUDE-TAX45` (capacity only).**  The
amplitude tax is `√R`, of `X`-exponent `5/36`. -/
def scalarizationAmplitudeTax : ℚ := scalarizationEnergyTax / 2

theorem scalarizationAmplitudeTax_value : scalarizationAmplitudeTax = 5 / 36 := by
  norm_num [scalarizationAmplitudeTax, scalarizationEnergyTax, expR, expXinY]

/-- Both taxes are strictly positive: a fixed logarithmic saving cannot pay a
positive power.  (Capacity bookkeeping only — no analytic claim.) -/
theorem taxes_pos : 0 < scalarizationEnergyTax ∧ 0 < scalarizationAmplitudeTax := by
  constructor <;> norm_num [scalarizationEnergyTax, scalarizationAmplitudeTax, expR, expXinY]

end ScaleLedger

/-! ## 4. Phase F · the finite scalarisation cost -/

namespace Scalarisation

open Finset CharacterCentering TwoStageChar

/-- **`scalarisation_cost`.**  A scalar cell bound `|S(ℓ,χ,k)| ≤ B` gives the
bundle bound with the *full weighted number of character cells* as the cost.
Pure finite counting; no analytic theorem is claimed to supply `B`. -/
theorem scalarisation_cost (S : TwoStageSourceData) (L : Finset ℕ+) (k : ℕ) (B : ℝ)
    (hB : ∀ ell ∈ L, ∀ χ ∈ nonprincipalChars ((ell : ℕ)), ‖S.SChar ell χ k‖ ≤ B) :
    S.TwoStageSquareBundle L k
      ≤ ∑ ell ∈ L, ((ell : ℕ).totient : ℝ)⁻¹ *
          ((nonprincipalChars ((ell : ℕ))).card : ℝ) * B ^ 2 := by
  classical
  rw [TwoStageSourceData.TwoStageSquareBundle]
  refine Finset.sum_le_sum fun ell hell => ?_
  have hcell : ∑ χ ∈ nonprincipalChars ((ell : ℕ)), Complex.normSq (S.SChar ell χ k)
      ≤ ((nonprincipalChars ((ell : ℕ))).card : ℝ) * B ^ 2 := by
    have : ∀ χ ∈ nonprincipalChars ((ell : ℕ)),
        Complex.normSq (S.SChar ell χ k) ≤ B ^ 2 := by
      intro χ hχ
      have h1 : ‖S.SChar ell χ k‖ ≤ B := hB ell hell χ hχ
      have h2 : Complex.normSq (S.SChar ell χ k) = ‖S.SChar ell χ k‖ ^ 2 := by
        simp [Complex.normSq_eq_norm_sq]
      have h0 : (0 : ℝ) ≤ ‖S.SChar ell χ k‖ := norm_nonneg _
      nlinarith
    calc ∑ χ ∈ nonprincipalChars ((ell : ℕ)), Complex.normSq (S.SChar ell χ k)
        ≤ ∑ _χ ∈ nonprincipalChars ((ell : ℕ)), B ^ 2 := Finset.sum_le_sum this
      _ = ((nonprincipalChars ((ell : ℕ))).card : ℝ) * B ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hpos : (0 : ℝ) ≤ ((ell : ℕ).totient : ℝ)⁻¹ := by positivity
  calc ((ell : ℕ).totient : ℝ)⁻¹ *
        ∑ χ ∈ nonprincipalChars ((ell : ℕ)), Complex.normSq (S.SChar ell χ k)
      ≤ ((ell : ℕ).totient : ℝ)⁻¹ * (((nonprincipalChars ((ell : ℕ))).card : ℝ) * B ^ 2) :=
        mul_le_mul_of_nonneg_left hcell hpos
    _ = ((ell : ℕ).totient : ℝ)⁻¹ * ((nonprincipalChars ((ell : ℕ))).card : ℝ) * B ^ 2 := by
        ring

end Scalarisation

/-! ## 5. Phase G · the Hilbert firewall -/

namespace HilbertFirewall

/-- **`sharedCharacterProduct_not_singleLinearLift`.**

The shared character coordinate enters as the *product* `χ(m)·χ(r)`.  Knowing
the vector `m ↦ (χ(m))_χ` does not determine the product vector: no map at all
— linear or otherwise — from the `m`-vector alone can produce it, as soon as
some residue `a ≠ 1` exists.

This is a firewall against the inference *scalar linear theorem ⇒ free
Hilbert-valued theorem ⇒ shared bilinear character bundle*.  It is **not** a
claim that no vector-valued theorem exists. -/
theorem sharedCharacterProduct_not_singleLinearLift (n : ℕ) [NeZero n] [Nontrivial (ZMod n)]
    (a : ZMod n) (ha : a ≠ 1) :
    ¬ ∃ T : (DirichletCharacter ℂ n → ℂ) → (DirichletCharacter ℂ n → ℂ),
        ∀ m r : ZMod n, (fun χ : DirichletCharacter ℂ n => χ m * χ r) = T (fun χ => χ m) := by
  rintro ⟨T, hT⟩
  have h1 := hT 1 1
  have h2 := hT 1 a
  rw [← h2] at h1
  obtain ⟨χ, hχ⟩ :=
    DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ (n := n) ha
  have := congrFun h1 χ
  simp only [map_one, one_mul, mul_one] at this
  exact hχ this.symm

/-- The firewall is not vacuous: such an `a` exists for every modulus `n ≥ 3`
(e.g. `n = 3`, `a = 2`). -/
theorem sharedCharacterProduct_firewall_nonvacuous :
    ¬ ∃ T : (DirichletCharacter ℂ 3 → ℂ) → (DirichletCharacter ℂ 3 → ℂ),
        ∀ m r : ZMod 3, (fun χ : DirichletCharacter ℂ 3 => χ m * χ r) = T (fun χ => χ m) :=
  sharedCharacterProduct_not_singleLinearLift 3 (2 : ZMod 3) (by decide)

end HilbertFirewall

end CurrentProgramme
end TwinPrimeProject
