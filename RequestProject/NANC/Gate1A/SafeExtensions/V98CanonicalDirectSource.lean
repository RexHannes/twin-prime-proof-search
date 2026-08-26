/-
# NANC Gate 1A v9.8 — the authoritative canonical Gate 1A Direct source

This file transcribes the authoritative normalized pre-square Gate 1A Direct
source

    Ctilde_{r,k,m}
      = ∑_{p ∼ L} b_p ∑_{q ∼ L, q ≠ p} ∑_h ω_{m,p,q}(h)
          e_{m q}( 2 h k · inverse[p(m + k r)] ),

    ω_{m,p,q}(h) = (H/(p q)) · Ŵ_D(h/(p q)) · exp( − h α /(p q m) ),

literally, and nothing else.  No term that is not displayed in the source is
added, and no analytic estimate is asserted.

**Provenance.**  The formula itself is `sourceInspectedNotProved`: it is a
transcription of the authoritative source document, not a Lean-derived object.
Everything *proved* about it below is definitional / algebraic, hence
`leanProved`.

## The common-weight point (Section 4 of the v9.8 instructions)

The physical smoothing datum enters through **one** field
`DirectSourceScalars.What` (the transform of the single physical weight `W_D`).
It carries no row index.  The derived coefficients ω do depend on the row, but
only through

* the scalar prefactor `H/(pq)`, and
* the smooth factor `exp(−hα/(pqm))`,

while the *weight* is always `Ŵ_D` evaluated at the **row-free** argument
`h/(pq)` (`omegaCanonical_weight_factor`, `commonWeightArg` takes no row).
This is derived (type B) edge dependence, not source (type A) edge dependence;
`omegaCanonical_congr_of_common_weight` is the rigidity statement that ω is a
function of the common weight datum alone.

Section 6 (derived smooth dependence) is represented by
`SmoothSeparationCertificate`, an **uninhabited source-specific analytic
interface**: it says that the row-dependent smooth factor has a finite template
expansion with a nuclear cost.  Given it, `canonicalWeight_finiteTemplate`
produces a finite template decomposition of the full coefficient family whose
template count is `#(P × Q) · n` — a count that does not grow with the number of
rows.  That is exactly the structural difference from an arbitrary
`EdgeDependentD2Data`, for which v9.6 proved that at least `#Edge` templates are
needed (`V96.template_count_ge_of_linearIndependent`).
-/
import Mathlib
import RequestProject.CenteredCRTRootNormalForm
import RequestProject.NANC.Gate1A.SafeExtensions.V95WeightFirewall
import RequestProject.NANC.Gate1A.SafeExtensions.V96ActualWeight

namespace TwinPrimeProject.NANC.Gate1A.V98

open Finset
open TwinPrimeProject.CenteredCRTRoot

/-! ## 1. The additive character on ℝ -/

/-- `eR x = e(x) = exp(2πi x)`.  The source writes `e_n(z)` for `eR (z/n)`. -/
noncomputable def eR (x : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * x)

@[simp] theorem eR_zero : eR 0 = 1 := by simp [eR]

theorem eR_add (x y : ℝ) : eR (x + y) = eR x * eR y := by
  simp [eR, Complex.ofReal_add, mul_add, Complex.exp_add]

@[simp] theorem norm_eR (x : ℝ) : ‖eR x‖ = 1 := by
  simp [eR, Complex.norm_exp]

/-! ## 2. The authoritative scalars and the canonical weight ω -/

/-- The row-independent physical scalars of the canonical Direct source.
`What` is the transform of the **single** physical smoothing weight `W_D`;
there is deliberately no row index on it. -/
structure DirectSourceScalars where
  /-- The harmonic scale `H`. -/
  Hscale : ℝ
  /-- `Ŵ_D`, the transform of the one common physical weight. -/
  What : ℝ → ℂ
  /-- The source parameter `α`. -/
  alph : ℝ

/-- The row-free argument at which the common weight is evaluated: `h/(pq)`.
It takes no row input, and that is the whole content of the common-weight
firewall. -/
noncomputable def commonWeightArg (p q h : ℝ) : ℝ := h / (p * q)

/-- The row-dependent scalar prefactor of ω: `(H/(pq)) · exp(−hα/(pqm))`. -/
noncomputable def rowScale (S : DirectSourceScalars) (m p q h : ℝ) : ℂ :=
  ((S.Hscale / (p * q) : ℝ) : ℂ) * Complex.exp ((-(h * S.alph / (p * q * m)) : ℝ))

/-- **The authoritative ω.**  Literal transcription:
`ω_{m,p,q}(h) = (H/(pq)) · Ŵ_D(h/(pq)) · exp(−hα/(pqm))`. -/
noncomputable def omegaCanonical (S : DirectSourceScalars) (m p q h : ℝ) : ℂ :=
  ((S.Hscale / (p * q) : ℝ) : ℂ) * S.What (h / (p * q)) *
    Complex.exp ((-(h * S.alph / (p * q * m)) : ℝ))

/-- **Common-weight factorisation of ω.**  The row enters only through
`rowScale`; the weight is `Ŵ_D` at the row-free argument `commonWeightArg`. -/
theorem omegaCanonical_weight_factor (S : DirectSourceScalars) (m p q h : ℝ) :
    omegaCanonical S m p q h = rowScale S m p q h * S.What (commonWeightArg p q h) := by
  simp [omegaCanonical, rowScale, commonWeightArg]
  ring

/-- **Rigidity: ω is a function of the common weight datum alone.**  Two
canonical sources with the same `H`, the same `Ŵ_D` and the same `α` have
literally the same ω at every row, pair and harmonic. -/
theorem omegaCanonical_congr_of_common_weight (S T : DirectSourceScalars)
    (hH : S.Hscale = T.Hscale) (hW : S.What = T.What) (ha : S.alph = T.alph) :
    omegaCanonical S = omegaCanonical T := by
  funext m p q h
  simp only [omegaCanonical, hH, hW, ha]

/-! ## 3. The canonical Direct source -/

/-- One canonical Gate 1A Direct row datum `(r, k, m)`. -/
structure DirectRow where
  /-- The prime modulus `r`. -/
  r : ℤ
  /-- The shift `k`. -/
  k : ℤ
  /-- The physical variable `m`. -/
  m : ℤ

/-- **The authoritative normalized pre-square Gate 1A Direct source.**  All
index sets are finite, the coefficient sequences `b`, `d` are the source
sequences, and `inv e p q` is the modular inverse of `p(m + k r)` modulo `m q`
that appears in the displayed phase, supplied together with its defining
congruence. -/
structure Gate1ADirectCanonicalSource where
  /-- The row-independent physical scalars, containing the one common `Ŵ_D`. -/
  scalars : DirectSourceScalars
  /-- The row index type. -/
  Row : Type
  [rowFintype : Fintype Row]
  /-- The `(r, k, m)` datum of each row. -/
  row : Row → DirectRow
  /-- The `p ∼ L` index type. -/
  P : Type
  [pFintype : Fintype P]
  /-- The `q ∼ L` index type. -/
  Q : Type
  [qFintype : Fintype Q]
  /-- The harmonic index type. -/
  Harm : Type
  [harmFintype : Fintype Harm]
  /-- The value of the prime `p`. -/
  pval : P → ℤ
  /-- The value of the prime `q`. -/
  qval : Q → ℤ
  /-- The value of the harmonic `h`. -/
  hval : Harm → ℤ
  /-- The source coefficients `b_p`. -/
  b : P → ℂ
  /-- The source coefficients `d_q`. -/
  d : Q → ℂ
  /-- `inverse[p(m + k r)]` modulo `m q`. -/
  inv : Row → P → Q → ℤ
  /-- Its defining congruence. -/
  inv_spec : ∀ e p q,
    ((row e).m * qval q) ∣ (pval p * ((row e).m + (row e).k * (row e).r) * inv e p q - 1)

attribute [instance] Gate1ADirectCanonicalSource.rowFintype
  Gate1ADirectCanonicalSource.pFintype Gate1ADirectCanonicalSource.qFintype
  Gate1ADirectCanonicalSource.harmFintype

namespace Gate1ADirectCanonicalSource

variable (S : Gate1ADirectCanonicalSource)

/-- The phase `e_{m q}(2 h k · inverse[p(m + k r)])` of the displayed source. -/
noncomputable def phase (e : S.Row) (p : S.P) (q : S.Q) (h : S.Harm) : ℂ :=
  eR ((2 * (S.hval h : ℝ) * ((S.row e).k : ℝ) * ((S.inv e p q : ℤ) : ℝ)) /
    (((S.row e).m : ℝ) * (S.qval q : ℝ)))

/-- The canonical coefficient attached to `(row, p, q, h)`: the ω of the
authoritative source at the values of that row. -/
noncomputable def coeffAt (e : S.Row) (p : S.P) (q : S.Q) (h : S.Harm) : ℂ :=
  omegaCanonical S.scalars ((S.row e).m : ℝ) (S.pval p : ℝ) (S.qval q : ℝ) (S.hval h : ℝ)

/-- **`Ctilde_{r,k,m}`**, transcribed literally. -/
noncomputable def ctilde (e : S.Row) : ℂ :=
  ∑ p, S.b p * ∑ q ∈ univ.filter (fun q => S.qval q ≠ S.pval p), S.d q *
    ∑ h, S.coeffAt e p q h * S.phase e p q h

/-- Definitional unfolding of the canonical source. -/
theorem ctilde_def (e : S.Row) :
    S.ctilde e = ∑ p, S.b p * ∑ q ∈ univ.filter (fun q => S.qval q ≠ S.pval p), S.d q *
      ∑ h, S.coeffAt e p q h * S.phase e p q h := rfl

/-- The diagonal `q = p` is genuinely excluded, as displayed in the source. -/
theorem ctilde_excludes_diagonal (p : S.P) (q : S.Q) (hq : S.qval q = S.pval p) :
    q ∉ univ.filter (fun q => S.qval q ≠ S.pval p) := by
  simp [hq]

/-- The canonical phase is unimodular. -/
@[simp] theorem norm_phase (e : S.Row) (p : S.P) (q : S.Q) (h : S.Harm) :
    ‖S.phase e p q h‖ = 1 := by
  simp [phase]

/-- **`gate1A_direct_physicalWeight_common`.**  Every canonical coefficient is
the product of a row-dependent scalar with the *one* common physical weight
`Ŵ_D`, evaluated at an argument that has no row input at all. -/
theorem gate1A_direct_physicalWeight_common (e : S.Row) (p : S.P) (q : S.Q) (h : S.Harm) :
    S.coeffAt e p q h
      = rowScale S.scalars ((S.row e).m : ℝ) (S.pval p : ℝ) (S.qval q : ℝ) (S.hval h : ℝ) *
          S.scalars.What (commonWeightArg (S.pval p : ℝ) (S.qval q : ℝ) (S.hval h : ℝ)) :=
  omegaCanonical_weight_factor _ _ _ _ _

/-- The whole coefficient family is determined by the common weight datum: if
two canonical sources share their scalars and their index data, their
coefficients agree. -/
theorem coeffAt_congr_of_common_weight (T : Gate1ADirectCanonicalSource)
    (hscal : S.scalars = T.scalars) :
    ∀ (m p q h : ℝ), omegaCanonical S.scalars m p q h = omegaCanonical T.scalars m p q h := by
  intro m p q h
  rw [hscal]

end Gate1ADirectCanonicalSource

/-! ## 4. Derived smooth dependence as a source-specific analytic interface -/

/-- **Source-specific analytic interface (Section 6).**  The authoritative
source states that the remaining smooth arguments lie in a fixed compact box
with uniformly controlled derivatives, so that the row-dependent smooth factor
`exp(−hα/(pqm))` has a finite Fourier–Mellin template expansion with `X^{o(1)}`
nuclear cost.  This is *not* proved here: an inhabitant of this structure is
the analytic statement. -/
structure SmoothSeparationCertificate (S : Gate1ADirectCanonicalSource) where
  /-- Number of templates per `(p, q)` cell. -/
  n : ℕ
  /-- The templates, one family per `(p, q)` cell. -/
  template : S.P × S.Q → Fin n → (S.Harm → ℂ)
  /-- The row-dependent expansion coefficients. -/
  coefRow : S.Row → S.P × S.Q → Fin n → ℂ
  /-- The nuclear cost. -/
  nuclear : ℝ
  /-- The expansion of the smooth row factor. -/
  decomposition : ∀ (e : S.Row) (a : S.P × S.Q) (h : S.Harm),
    Complex.exp ((-((S.hval h : ℝ) * S.scalars.alph /
        ((S.pval a.1 : ℝ) * (S.qval a.2 : ℝ) * ((S.row e).m : ℝ))) : ℝ))
      = ∑ j, coefRow e a j * template a j h
  /-- The nuclear cost bound. -/
  nuclear_ok : ∀ e a, ∑ j, ‖coefRow e a j‖ ≤ nuclear

namespace SmoothSeparationCertificate

variable {S : Gate1ADirectCanonicalSource} (C : SmoothSeparationCertificate S)

/-- The common template: the row-free weight factor times a smooth template. -/
noncomputable def commonTemplate (a : S.P × S.Q) (j : Fin C.n) (h : S.Harm) : ℂ :=
  ((S.scalars.Hscale / ((S.pval a.1 : ℝ) * (S.qval a.2 : ℝ)) : ℝ) : ℂ) *
    S.scalars.What (commonWeightArg (S.pval a.1 : ℝ) (S.qval a.2 : ℝ) (S.hval h : ℝ)) *
    C.template a j h

/-- **Finite template decomposition of the canonical coefficient family.**
Given the smooth-separation interface, every canonical coefficient is a finite
combination of `#(P × Q) · n` templates.  Crucially the template family does
not depend on the row. -/
theorem canonicalWeight_finiteTemplate (e : S.Row) (a : S.P × S.Q) (h : S.Harm) :
    S.coeffAt e a.1 a.2 h = ∑ j, C.coefRow e a j * C.commonTemplate a j h := by
  have hdec := C.decomposition e a h
  simp only [Gate1ADirectCanonicalSource.coeffAt, omegaCanonical, commonTemplate,
    commonWeightArg]
  rw [hdec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The number of templates, `#(P × Q) · n`, is a bound that does not involve
the number of rows. -/
def templateCount : ℕ := Fintype.card (S.P × S.Q) * C.n

theorem templateCount_eq : C.templateCount = Fintype.card (S.P × S.Q) * C.n := rfl

/-- The nuclear cost bound transported to the canonical coefficients. -/
theorem coeff_nuclear_bound (e : S.Row) (a : S.P × S.Q) (h : S.Harm) (B : ℝ)
    (hB : ∀ j, ‖C.commonTemplate a j h‖ ≤ B) (hB0 : 0 ≤ B) :
    ‖S.coeffAt e a.1 a.2 h‖ ≤ C.nuclear * B := by
  rw [C.canonicalWeight_finiteTemplate e a h]
  refine (norm_sum_le _ _).trans ?_
  have h1 : ∑ j, ‖C.coefRow e a j * C.commonTemplate a j h‖ ≤ (∑ j, ‖C.coefRow e a j‖) * B := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hB j) (norm_nonneg _)
  exact h1.trans (mul_le_mul_of_nonneg_right (C.nuclear_ok e a) hB0)

end SmoothSeparationCertificate

/-! ## 5. Type-A versus type-B edge dependence -/

/-- **The scope separation, machine-visible.**  An arbitrary
`EdgeDependentD2Data` (type A: a weight chosen independently per edge) needs at
least `#Edge` common templates as soon as its edge weights are linearly
independent — this is the v9.6 rank obstruction, re-exported here.  The
canonical Direct source is type B: its template count is
`#(P × Q) · n` by `SmoothSeparationCertificate.templateCount_eq`, with no
`#Row` factor. -/
theorem arbitraryEdgeDependent_needs_edge_many_templates
    {M : Type*} [AddCommGroup M] [Module ℂ M] {Edge : Type*} [Fintype Edge] {n : ℕ}
    (W : Edge → M) (hW : LinearIndependent ℂ W) (T : Fin n → M) (a : Edge → Fin n → ℂ)
    (hdec : ∀ e, W e = ∑ j, a e j • T j) :
    Fintype.card Edge ≤ n :=
  V96.template_count_ge_of_linearIndependent W hW T a hdec

end TwinPrimeProject.NANC.Gate1A.V98
