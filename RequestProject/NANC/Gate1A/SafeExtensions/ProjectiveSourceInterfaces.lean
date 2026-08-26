/-
# NANC Gate 1A v9.1 — projective crossed convolution, and the zero-projective
# source interface

Finite scalar Hilbert-space algebra.  For finite index types `Zi`, `Li`, a pair
map `pmap : Zi → Li → W` into a finite "product" type `W`, and packets
`A : Zi → ℂ`, `B : Li → ℂ`, the **crossed correlation**

    P = ∑_{pmap z₁ l₂ = pmap z₂ l₁} A z₁ conj(A z₂) · B l₁ conj(B l₂)

equals the **projective energy**

    ∑_w ‖ ∑_{pmap z l = w} A z · conj (B l) ‖².

If every `w` has at most `D` representations then

    projective energy ≤ D · ‖A‖² · ‖B‖².

`ZeroProjectiveSourceFactorization` is an **interface structure** carrying the
literal source coefficient, the row packet, the graph packet, the factorization
equality and the fibre-card hypothesis.  No inhabitant is constructed for any
actual Gate source, so

    ZERO-PROJ-SOURCE-SPLICE1A : OPEN INTERFACE.
-/
import Mathlib
import Gate1B.SafeExtensions.PhysicalSecondMoment

namespace TwinPrimeProject.NANC.Gate1A.V91

open Finset

variable {Zi Li W : Type*} [Fintype Zi] [Fintype Li] [Fintype W] [DecidableEq W]

/-- The projective row packet at a product point `w`. -/
noncomputable def projRow (pmap : Zi → Li → W) (A : Zi → ℂ) (B : Li → ℂ) (w : W) : ℂ :=
  ∑ p : Zi × Li, if pmap p.1 p.2 = w then A p.1 * (starRingEnd ℂ) (B p.2) else 0

/-- The projective energy `∑_w ‖row w‖²`. -/
noncomputable def projEnergy (pmap : Zi → Li → W) (A : Zi → ℂ) (B : Li → ℂ) : ℝ :=
  ∑ w : W, ‖projRow pmap A B w‖ ^ 2

/-- The crossed correlation over colliding quadruples `(z₁,l₂ ; z₂,l₁)`. -/
noncomputable def projCorrelation (pmap : Zi → Li → W) (A : Zi → ℂ) (B : Li → ℂ) : ℂ :=
  ∑ p : Zi × Li, ∑ p' : Zi × Li,
    if pmap p.1 p.2 = pmap p'.1 p'.2 then
      A p.1 * (starRingEnd ℂ) (A p'.1) * (B p'.2 * (starRingEnd ℂ) (B p.2)) else 0

/-- Collapsing the `w`-sum of a product of two fibre indicators. -/
theorem sum_indicator_mul_conj (pmap : Zi → Li → W) (p p' : Zi × Li) (a b : ℂ) :
    ∑ w : W, (if pmap p.1 p.2 = w then a else 0)
        * (starRingEnd ℂ) (if pmap p'.1 p'.2 = w then b else 0)
      = if pmap p.1 p.2 = pmap p'.1 p'.2 then a * (starRingEnd ℂ) b else 0 := by
  classical
  by_cases h : pmap p.1 p.2 = pmap p'.1 p'.2
  · rw [if_pos h, Finset.sum_eq_single (pmap p.1 p.2)]
    · rw [if_pos rfl, if_pos h.symm]
    · intro w _ hw
      rw [if_neg (Ne.symm hw), zero_mul]
    · intro hmem; exact absurd (Finset.mem_univ _) hmem
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun w _ => ?_
    by_cases h1 : pmap p.1 p.2 = w
    · have h2 : pmap p'.1 p'.2 ≠ w := fun hc => h (h1.trans hc.symm)
      rw [if_neg h2]
      simp
    · rw [if_neg h1, zero_mul]

/-- **Projective crossed convolution.**  The crossed correlation over colliding
quadruples is exactly the projective energy. -/
theorem projectiveCrossedConvolution (pmap : Zi → Li → W) (A : Zi → ℂ) (B : Li → ℂ) :
    projCorrelation pmap A B = ((projEnergy pmap A B : ℝ) : ℂ) := by
  classical
  have hE : ((projEnergy pmap A B : ℝ) : ℂ)
      = ∑ w : W, projRow pmap A B w * (starRingEnd ℂ) (projRow pmap A B w) := by
    unfold projEnergy
    push_cast
    exact Finset.sum_congr rfl fun w _ => (Complex.mul_conj' _).symm
  rw [hE]
  have hexpand : ∀ w : W, projRow pmap A B w * (starRingEnd ℂ) (projRow pmap A B w)
      = ∑ p : Zi × Li, ∑ p' : Zi × Li,
          (if pmap p.1 p.2 = w then A p.1 * (starRingEnd ℂ) (B p.2) else 0)
            * (starRingEnd ℂ) (if pmap p'.1 p'.2 = w then A p'.1 * (starRingEnd ℂ) (B p'.2)
              else 0) := by
    intro w
    unfold projRow
    rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun w _ => hexpand w]
  rw [Finset.sum_comm]
  unfold projCorrelation
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p' _ => ?_
  rw [sum_indicator_mul_conj pmap p p']
  by_cases h : pmap p.1 p.2 = pmap p'.1 p'.2
  · rw [if_pos h, if_pos h, map_mul]
    simp only [RingHomCompTriple.comp_apply, RingHom.id_apply, Complex.conj_conj]
    ring
  · rw [if_neg h, if_neg h]

/-- **Bounded-multiplicity corollary.**  If every product point has at most `D`
representations `pmap z l = w`, then the projective energy is at most
`D · ‖A‖² · ‖B‖²`. -/
theorem projectiveCrossedConvolution_of_fibreCard (pmap : Zi → Li → W) (A : Zi → ℂ)
    (B : Li → ℂ) (D : ℝ)
    (hD : ∀ w : W, ((Finset.univ.filter fun p : Zi × Li => pmap p.1 p.2 = w).card : ℝ) ≤ D) :
    projEnergy pmap A B ≤ D * ((∑ z, ‖A z‖ ^ 2) * ∑ l, ‖B l‖ ^ 2) := by
  classical
  have hrow : ∀ w : W, ‖projRow pmap A B w‖ ^ 2
      ≤ D * ∑ p : Zi × Li, (if pmap p.1 p.2 = w then ‖A p.1‖ ^ 2 * ‖B p.2‖ ^ 2 else 0) := by
    intro w
    have hcs := Gate1B.SafeExtensions.physicalOuterCauchy (Finset.univ : Finset (Zi × Li))
      (fun p => if pmap p.1 p.2 = w then (1 : ℂ) else 0)
      (fun p => if pmap p.1 p.2 = w then A p.1 * (starRingEnd ℂ) (B p.2) else 0)
    have hprod : ∀ p : Zi × Li,
        (if pmap p.1 p.2 = w then (1 : ℂ) else 0)
          * (if pmap p.1 p.2 = w then A p.1 * (starRingEnd ℂ) (B p.2) else 0)
          = if pmap p.1 p.2 = w then A p.1 * (starRingEnd ℂ) (B p.2) else 0 := by
      intro p; split_ifs <;> simp
    have hcard : ∑ p : Zi × Li, ‖if pmap p.1 p.2 = w then (1 : ℂ) else 0‖ ^ 2
        = ((Finset.univ.filter fun p : Zi × Li => pmap p.1 p.2 = w).card : ℝ) := by
      rw [Finset.card_filter]
      push_cast
      exact Finset.sum_congr rfl fun p _ => by split_ifs <;> simp
    have hterms : ∑ p : Zi × Li,
        ‖if pmap p.1 p.2 = w then A p.1 * (starRingEnd ℂ) (B p.2) else 0‖ ^ 2
        = ∑ p : Zi × Li, (if pmap p.1 p.2 = w then ‖A p.1‖ ^ 2 * ‖B p.2‖ ^ 2 else 0) := by
      refine Finset.sum_congr rfl fun p _ => ?_
      split_ifs
      · rw [norm_mul, RCLike.norm_conj, mul_pow]
      · simp
    rw [Finset.sum_congr rfl fun p _ => hprod p, hcard, hterms] at hcs
    have hnn : (0:ℝ) ≤ ∑ p : Zi × Li, (if pmap p.1 p.2 = w then ‖A p.1‖ ^ 2 * ‖B p.2‖ ^ 2 else 0) :=
      Finset.sum_nonneg fun p _ => by split_ifs <;> positivity
    refine (le_of_eq (by unfold projRow; rfl)).trans (hcs.trans ?_)
    exact mul_le_mul_of_nonneg_right (hD w) hnn
  calc projEnergy pmap A B
      ≤ ∑ w : W, D * ∑ p : Zi × Li,
          (if pmap p.1 p.2 = w then ‖A p.1‖ ^ 2 * ‖B p.2‖ ^ 2 else 0) :=
        Finset.sum_le_sum fun w _ => hrow w
    _ = D * ∑ p : Zi × Li, ‖A p.1‖ ^ 2 * ‖B p.2‖ ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => by simp
    _ = D * ((∑ z, ‖A z‖ ^ 2) * ∑ l, ‖B l‖ ^ 2) := by
        congr 1
        rw [Fintype.sum_prod_type, Finset.sum_mul]
        exact Finset.sum_congr rfl fun z _ => by rw [Finset.mul_sum]

/-! ## Zero-projective source interface (no inhabitant is constructed) -/

/-- **Interface structure.**  Literal data for a zero-projective source splice:
the source coefficient, the row packet `A`, the graph packet `B`, the
factorization equality, and the fibre-card hypothesis.  No inhabitant is
constructed anywhere in this repository. -/
structure ZeroProjectiveSourceFactorization (Row Graph Prod' : Type*)
    [Fintype Row] [Fintype Graph] [Fintype Prod'] [DecidableEq Prod'] where
  /-- The pair (product) map. -/
  pmap : Row → Graph → Prod'
  /-- Row packet. -/
  A : Row → ℂ
  /-- Graph packet. -/
  B : Graph → ℂ
  /-- The literal source coefficient. -/
  sourceCoeff : Prod' → ℂ
  /-- The factorization equality: the source coefficient *is* the projective row. -/
  factorization : ∀ w, sourceCoeff w = projRow pmap A B w
  /-- Fibre multiplicity bound. -/
  fibreCard : ℝ
  /-- The fibre-card hypothesis. -/
  fibreCard_le : ∀ w : Prod',
    ((Finset.univ.filter fun p : Row × Graph => pmap p.1 p.2 = w).card : ℝ) ≤ fibreCard

/-- **Projective energy bound from the zero-projective interface.** -/
theorem ZeroProjectiveSourceFactorization.bound {Row Graph Prod' : Type*}
    [Fintype Row] [Fintype Graph] [Fintype Prod'] [DecidableEq Prod']
    (S : ZeroProjectiveSourceFactorization Row Graph Prod') :
    ∑ w : Prod', ‖S.sourceCoeff w‖ ^ 2
      ≤ S.fibreCard * ((∑ z, ‖S.A z‖ ^ 2) * ∑ l, ‖S.B l‖ ^ 2) := by
  have hrw : ∑ w : Prod', ‖S.sourceCoeff w‖ ^ 2 = projEnergy S.pmap S.A S.B := by
    unfold projEnergy
    exact Finset.sum_congr rfl fun w _ => by rw [S.factorization w]
  rw [hrw]
  exact projectiveCrossedConvolution_of_fibreCard S.pmap S.A S.B S.fibreCard S.fibreCard_le

end TwinPrimeProject.NANC.Gate1A.V91
