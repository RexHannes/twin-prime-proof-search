import RequestProject.NANC.Gate1B.V11FMPerronGrammar

/-!
# V11 · Gate 1B — generated expressions, deterministic cost, Perron templates

Finite generated expressions over the atoms of `V11FMPerronGrammar.lean`:

* pointwise product,
* finite sum (binary `add`, iterated),
* finite Dirichlet convolution,
* scalar multiplication.

Everything here is **deterministic finite algebra**.  The only inequalities
proved are triangle/divisor inequalities under *explicitly supplied* bounds; no
analytic estimate, no mean-value theorem, no Perron truncation error is claimed
or assumed anywhere.

The `PerronTemplate` structure is a finite template: a finite parameter space,
a coefficient density on it, a generated integrand and a supplied `l1Cost`.  No
improper integral is defined — the repository has no infrastructure that would
make an honest one available here.

Also defined: the class `FMPerronGenerated` and the certificate type
`FMPerronGrammarCertificate`.  The *real* Ford-proof certificate
(`RealFordGrammarCertificate`) is left without an inhabitant, since the Ford
proof objects are not formally represented in this repository.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-! ## 1. Generated expressions -/

/-- Finite generated expressions. -/
inductive GenExpr
  /-- A realisable generated atom. -/
  | atom (a : GenAtom)
  /-- Pointwise product. -/
  | mul (f g : GenExpr)
  /-- Pointwise sum. -/
  | add (f g : GenExpr)
  /-- Scalar multiplication. -/
  | smul (c : ℂ) (f : GenExpr)
  /-- Finite Dirichlet convolution. -/
  | conv (f g : GenExpr)

/-- The finite Dirichlet convolution. -/
noncomputable def dconv (f g : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, f d * g (n / d)

/-- Semantics of a generated expression. -/
noncomputable def semExpr : GenExpr → ℕ → ℂ
  | .atom a => semAtom a
  | .mul f g => fun n => semExpr f n * semExpr g n
  | .add f g => fun n => semExpr f n + semExpr g n
  | .smul c f => fun n => c * semExpr f n
  | .conv f g => dconv (semExpr f) (semExpr g)

/-- Admissibility of a generated expression: every atom it contains is
admissible. -/
def GenExpr.Admissible : GenExpr → Prop
  | .atom a => a.Admissible
  | .mul f g => f.Admissible ∧ g.Admissible
  | .add f g => f.Admissible ∧ g.Admissible
  | .smul _ f => f.Admissible
  | .conv f g => f.Admissible ∧ g.Admissible

/-- The **deterministic cost** of a generated expression, relative to a supplied
uniform divisor bound `D`.  Convolution is the only constructor that pays a
divisor factor. -/
noncomputable def cost (D : ℝ) : GenExpr → ℝ
  | .atom _ => 1
  | .mul f g => cost D f * cost D g
  | .add f g => cost D f + cost D g
  | .smul c f => ‖c‖ * cost D f
  | .conv f g => D * (cost D f * cost D g)

/-- The cost is nonnegative whenever the divisor bound is. -/
theorem cost_nonneg {D : ℝ} (hD : 0 ≤ D) : ∀ e : GenExpr, 0 ≤ cost D e := by
  intro e
  induction e with
  | atom a => simp [cost]
  | mul f g hf hg => exact mul_nonneg hf hg
  | add f g hf hg => exact add_nonneg hf hg
  | smul c f hf => exact mul_nonneg (norm_nonneg c) hf
  | conv f g hf hg => exact mul_nonneg hD (mul_nonneg hf hg)

/-! ## 2. The named finite inequalities -/

/-- **norm_product_le** — pointwise products multiply supplied bounds. -/
theorem norm_product_le {f g : ℕ → ℂ} {Cf Cg : ℝ} {n : ℕ}
    (hf : ‖f n‖ ≤ Cf) (hg : ‖g n‖ ≤ Cg) :
    ‖f n * g n‖ ≤ Cf * Cg := by
  rw [norm_mul]
  exact mul_le_mul hf hg (norm_nonneg _) (le_trans (norm_nonneg _) hf)

/-- **norm_finiteSum_le_l1Cost** — a finite linear combination of uniformly
bounded functions is bounded by its ℓ¹ coefficient cost times the bound. -/
theorem norm_finiteSum_le_l1Cost {ι : Type*} (s : Finset ι) (c : ι → ℂ)
    (v : ι → ℂ) (C : ℝ) (hv : ∀ i ∈ s, ‖v i‖ ≤ C) :
    ‖∑ i ∈ s, c i * v i‖ ≤ (∑ i ∈ s, ‖c i‖) * C := by
  calc ‖∑ i ∈ s, c i * v i‖ ≤ ∑ i ∈ s, ‖c i * v i‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖c i‖ * C := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hv i hi) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖c i‖) * C := by rw [Finset.sum_mul]

/-- **convolution_divisorBound** — the Dirichlet convolution of two uniformly
bounded coefficient sequences costs one divisor factor. -/
theorem convolution_divisorBound (f g : ℕ → ℂ) (Cf Cg : ℝ) (n : ℕ)
    (hf : ∀ m, ‖f m‖ ≤ Cf) (hg : ∀ m, ‖g m‖ ≤ Cg) (hCf : 0 ≤ Cf) :
    ‖dconv f g n‖ ≤ (n.divisors.card : ℝ) * (Cf * Cg) := by
  calc ‖dconv f g n‖ ≤ ∑ d ∈ n.divisors, ‖f d * g (n / d)‖ := norm_sum_le _ _
    _ ≤ ∑ _d ∈ n.divisors, Cf * Cg := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [norm_mul]
        exact mul_le_mul (hf d) (hg _) (norm_nonneg _) hCf
    _ = (n.divisors.card : ℝ) * (Cf * Cg) := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-! ## 3. The uniform cost bound on a window -/

/-- **The deterministic cost theorem.**  On the window `[0, N]`, with a supplied
uniform divisor bound `D`, every admissible generated expression is bounded by
its cost.  All hypotheses are explicit and satisfiable (take `D` to be the
maximal divisor count on the window). -/
theorem norm_semExpr_le_cost (N : ℕ) (hN : 1 ≤ N) (D : ℝ)
    (hD : ∀ n ≤ N, (n.divisors.card : ℝ) ≤ D) :
    ∀ e : GenExpr, e.Admissible → ∀ n ≤ N, ‖semExpr e n‖ ≤ cost D e := by
  have hD0 : (0 : ℝ) ≤ D := by
    have := hD 1 hN
    simp at this
    linarith
  intro e
  induction e with
  | atom a =>
      intro ha n _
      simpa [semExpr, cost] using norm_semAtom_le_one a ha n
  | mul f g hf hg =>
      intro ha n hn
      exact norm_product_le (hf ha.1 n hn) (hg ha.2 n hn)
  | add f g hf hg =>
      intro ha n hn
      calc ‖semExpr f n + semExpr g n‖ ≤ ‖semExpr f n‖ + ‖semExpr g n‖ := norm_add_le _ _
        _ ≤ cost D f + cost D g := add_le_add (hf ha.1 n hn) (hg ha.2 n hn)
  | smul c f hf =>
      intro ha n hn
      simp only [semExpr, cost, norm_mul]
      exact mul_le_mul_of_nonneg_left (hf ha n hn) (norm_nonneg c)
  | conv f g hf hg =>
      intro ha n hn
      have hsub : ∀ d ∈ n.divisors, d ≤ N ∧ n / d ≤ N := by
        intro d hd
        rw [Nat.mem_divisors] at hd
        have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hd.2) hd.1
        exact ⟨le_trans hdn hn, le_trans (Nat.div_le_self n d) hn⟩
      have hstep : ‖dconv (semExpr f) (semExpr g) n‖
          ≤ (n.divisors.card : ℝ) * (cost D f * cost D g) := by
        calc ‖dconv (semExpr f) (semExpr g) n‖
            ≤ ∑ d ∈ n.divisors, ‖semExpr f d * semExpr g (n / d)‖ := norm_sum_le _ _
          _ ≤ ∑ _d ∈ n.divisors, cost D f * cost D g := by
              refine Finset.sum_le_sum fun d hd => ?_
              rw [norm_mul]
              exact mul_le_mul (hf ha.1 d (hsub d hd).1) (hg ha.2 _ (hsub d hd).2)
                (norm_nonneg _) (cost_nonneg hD0 f)
          _ = (n.divisors.card : ℝ) * (cost D f * cost D g) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      refine le_trans hstep ?_
      exact mul_le_mul_of_nonneg_right (hD n hn)
        (mul_nonneg (cost_nonneg hD0 f) (cost_nonneg hD0 g))

/-! ## 4. Perron templates (finite) -/

/-- **A finite Perron template.**  `P` is the (finite) parameter space, the
coefficient density lives on it, the integrand is generated, and the ℓ¹ cost is
supplied together with the inequality that justifies its name.  This is a
finite template, not an improper integral. -/
structure PerronTemplate (P : Type*) [Fintype P] where
  /-- The coefficient density on the parameter space. -/
  coefficientDensity : P → ℂ
  /-- The generated integrand attached to each parameter. -/
  generatedIntegrand : P → GenExpr
  /-- The supplied ℓ¹ cost. -/
  l1Cost : ℝ
  /-- The ℓ¹ cost dominates the density. -/
  l1Cost_spec : ∑ p, ‖coefficientDensity p‖ ≤ l1Cost

/-- The value of a finite Perron template at `n`. -/
noncomputable def templateValue {P : Type*} [Fintype P] (T : PerronTemplate P) (n : ℕ) : ℂ :=
  ∑ p, T.coefficientDensity p * semExpr (T.generatedIntegrand p) n

/-- **finite_template_reassembly** — a finite template is bounded by its ℓ¹ cost
times a uniform bound for its generated integrands. -/
theorem finite_template_reassembly {P : Type*} [Fintype P] (T : PerronTemplate P)
    (C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hInt : ∀ p, ‖semExpr (T.generatedIntegrand p) n‖ ≤ C) :
    ‖templateValue T n‖ ≤ T.l1Cost * C := by
  refine le_trans (norm_finiteSum_le_l1Cost Finset.univ _ _ C fun p _ => hInt p) ?_
  exact mul_le_mul_of_nonneg_right T.l1Cost_spec hC

/-- Every admissible template on the window `[0,N]` is bounded by its ℓ¹ cost
times the largest integrand cost. -/
theorem finite_template_reassembly_of_cost {P : Type*} [Fintype P] (T : PerronTemplate P)
    (N : ℕ) (hN : 1 ≤ N) (D C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ n ≤ N, (n.divisors.card : ℝ) ≤ D)
    (hAdm : ∀ p, (T.generatedIntegrand p).Admissible)
    (hcost : ∀ p, cost D (T.generatedIntegrand p) ≤ C) :
    ∀ n ≤ N, ‖templateValue T n‖ ≤ T.l1Cost * C := by
  intro n hn
  exact finite_template_reassembly T C hC n fun p =>
    le_trans (norm_semExpr_le_cost N hN D hD _ (hAdm p) n hn) (hcost p)

/-! ## 5. The generated class -/

/-- **`FMPerronGenerated f`** — `f` is realised by an admissible finite
generated expression. -/
def FMPerronGenerated (f : ℕ → ℂ) : Prop :=
  ∃ e : GenExpr, e.Admissible ∧ ∀ n, f n = semExpr e n

/-- The generated class together with the 1-boundedness that the Type-II
predicate needs.  (1-boundedness is *not* automatic for a general generated
expression: products of atoms are 1-bounded but sums and convolutions are
not.) -/
def FMPerronGeneratedUnit (f : ℕ → ℂ) : Prop :=
  FMPerronGenerated f ∧ ∀ n, ‖f n‖ ≤ 1

/-- Every admissible atom is generated and 1-bounded. -/
theorem fmPerronGeneratedUnit_atom (a : GenAtom) (ha : a.Admissible) :
    FMPerronGeneratedUnit (semAtom a) :=
  ⟨⟨.atom a, ha, fun _ => rfl⟩, norm_semAtom_le_one a ha⟩

/-- The class is nonempty: the Möbius atom is generated and 1-bounded. -/
theorem fmPerronGeneratedUnit_mobius : FMPerronGeneratedUnit (semAtom .mobius) :=
  fmPerronGeneratedUnit_atom .mobius trivial

/-! ### Closure properties (bounded depth, explicit cost) -/

/-- Closure under pointwise products. -/
theorem FMPerronGenerated.mul {f g : ℕ → ℂ}
    (hf : FMPerronGenerated f) (hg : FMPerronGenerated g) :
    FMPerronGenerated (fun n => f n * g n) := by
  obtain ⟨e, he, hfe⟩ := hf
  obtain ⟨d, hd, hgd⟩ := hg
  exact ⟨.mul e d, ⟨he, hd⟩, fun n => by simp [semExpr, hfe n, hgd n]⟩

/-- Closure under pointwise sums. -/
theorem FMPerronGenerated.add {f g : ℕ → ℂ}
    (hf : FMPerronGenerated f) (hg : FMPerronGenerated g) :
    FMPerronGenerated (fun n => f n + g n) := by
  obtain ⟨e, he, hfe⟩ := hf
  obtain ⟨d, hd, hgd⟩ := hg
  exact ⟨.add e d, ⟨he, hd⟩, fun n => by simp [semExpr, hfe n, hgd n]⟩

/-- Closure under scalar multiplication. -/
theorem FMPerronGenerated.smul {f : ℕ → ℂ} (c : ℂ) (hf : FMPerronGenerated f) :
    FMPerronGenerated (fun n => c * f n) := by
  obtain ⟨e, he, hfe⟩ := hf
  exact ⟨.smul c e, he, fun n => by simp [semExpr, hfe n]⟩

/-- Closure under finite Dirichlet convolution. -/
theorem FMPerronGenerated.conv {f g : ℕ → ℂ}
    (hf : FMPerronGenerated f) (hg : FMPerronGenerated g) :
    FMPerronGenerated (dconv f g) := by
  obtain ⟨e, he, hfe⟩ := hf
  obtain ⟨d, hd, hgd⟩ := hg
  refine ⟨.conv e d, ⟨he, hd⟩, fun n => ?_⟩
  simp only [semExpr, dconv]
  exact Finset.sum_congr rfl fun t _ => by rw [hfe t, hgd (n / t)]

/-- Closure under finite linear combinations, by induction on the index set. -/
theorem FMPerronGenerated.finiteLinearCombination {ι : Type*} (s : Finset ι)
    (c : ι → ℂ) (f : ι → ℕ → ℂ) (hf : ∀ i, FMPerronGenerated (f i)) :
    FMPerronGenerated (fun n => ∑ i ∈ s, c i * f i n) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨.atom (.constant 0), by simp [GenExpr.Admissible, GenAtom.Admissible],
        by simp [semExpr, semAtom]⟩
  | insert a s ha ih =>
      obtain ⟨e, he, hev⟩ := (FMPerronGenerated.smul (c a) (hf a)).add ih
      exact ⟨e, he, fun n => by simpa [Finset.sum_insert ha] using hev n⟩

/-- Products of generated 1-bounded functions are generated and 1-bounded:
bounded-depth product closure of the unit class. -/
theorem FMPerronGeneratedUnit.mul {f g : ℕ → ℂ}
    (hf : FMPerronGeneratedUnit f) (hg : FMPerronGeneratedUnit g) :
    FMPerronGeneratedUnit (fun n => f n * g n) := by
  refine ⟨hf.1.mul hg.1, fun n => ?_⟩
  rw [norm_mul]
  calc ‖f n‖ * ‖g n‖ ≤ 1 * 1 :=
        mul_le_mul (hf.2 n) (hg.2 n) (norm_nonneg _) zero_le_one
    _ = 1 := by ring

/-! ## 6. Grammar certificates -/

/-- **A grammar certificate for a supplied finite family of coefficients.**
Each slot of the family is explicitly identified with a member of
`FMPerronGenerated`, and a cost datum is supplied.  Nothing here asserts that
any *particular* paper's coefficients populate the family. -/
structure FMPerronGrammarCertificate {ι : Type*} (coeff : ι → ℕ → ℂ) where
  /-- The generated expression realising each coefficient slot. -/
  witness : ι → GenExpr
  /-- Each witness is admissible. -/
  witness_admissible : ∀ i, (witness i).Admissible
  /-- Each coefficient slot is the semantics of its witness. -/
  witness_eq : ∀ i n, coeff i n = semExpr (witness i) n

/-- A grammar certificate does exactly what its name says: every certified slot
is generated. -/
theorem FMPerronGrammarCertificate.generated {ι : Type*} {coeff : ι → ℕ → ℂ}
    (cert : FMPerronGrammarCertificate coeff) (i : ι) :
    FMPerronGenerated (coeff i) :=
  ⟨cert.witness i, cert.witness_admissible i, fun n => cert.witness_eq i n⟩

/-- **The REAL Ford-proof grammar certificate.**

This is the object that would be needed to say "the coefficients produced by the
literal Ford–Maynard Proposition-7.22 argument are generated".  It requires

* a formal representation `fordCoefficient` of those coefficients *extracted
  from the formal proof*, witnessed by `fordProvenance` — a datum this
  repository cannot supply, because the Ford proof is not formalised here;
* a grammar certificate for them;
* a realisation of the `P±` twists, which this repository also does not supply.

**No inhabitant is constructed, and none can be constructed from the material
present in this repository.**  Its absence is the formal record of the
provenance gap. -/
structure RealFordGrammarCertificate where
  /-- The index type of the coefficients produced by the literal proof. -/
  Slot : Type
  /-- The coefficients produced by the literal proof. -/
  fordCoefficient : Slot → ℕ → ℂ
  /-- The *provenance* datum: a formal derivation, inside this repository, of
  each coefficient slot from a formalised Ford–Maynard proof.  Represented by a
  realisation of the prime-extrema interface (absent) together with a proof that
  the coefficients are the extrema-twisted ones the argument actually produces. -/
  primeExtrema : PrimeExtremaRealisation
  /-- The extrema atom actually attached to each slot by the proof. -/
  extremaAtom : Slot → PrimeExtremaAtom
  /-- The slot really carries that extrema twist. -/
  fordProvenance : ∀ s n, fordCoefficient s n = semPrimeExtremaAtom primeExtrema (extremaAtom s) n
  /-- …and is nevertheless generated by the realisable grammar. -/
  grammar : FMPerronGrammarCertificate fordCoefficient

end Gate1BV11
end TwinPrimeProject
