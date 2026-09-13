/-
# Gate1B / R11 / Frontier / Latest : external analytic input discipline

Append-only module.  Every external analytic theorem used by the current frontier is recorded
here as a **named proposition**, stated with real quantitative content and **never inhabited**:
there is no `axiom`, no `sorry`, and nothing in this file is marked kernel-proved except the
deterministic adapters, which carry the interfaces as explicit hypotheses.

Interfaces:

* §1 Siegel–Walfisz (`SiegelWalfisz`);
* §2 zero density for a Dirichlet L-function (`ZeroDensityFor`);
* §3 explicit-formula data and its **deterministic adapter** (`ExplicitFormulaData`,
  `counting_close_to_main_of_small_zero_mass`) — the analytic input is a hypothesis, the
  consequence is kernel-proved;
* §4 spectral / Kloosterman inputs: KMS-type, Blomer–Pascadi, Wright (`KMSInput`,
  `BlomerPascadiInput`, `WrightMomentInput`);
* §5 the source-AP bank (`SourceAPBank`);
* §6 the **deterministic half of the source-side affine character estimate**: the `√ℓ` bound for
  a single affine mode, which follows from the Gram identity and is kernel-proved here.
-/
import Gate1B.R11.Frontier.Latest.AffineCharacterGram

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. Siegel–Walfisz -/

/-- The number of primes below `x`. -/
def primeCount (x : ℕ) : ℕ := ((range x).filter Nat.Prime).card

/-- The number of primes below `x` in the progression `a mod q`. -/
def primeCountAP (x q a : ℕ) : ℕ :=
  ((range x).filter (fun n => n.Prime ∧ n % q = a)).card

/-- **Siegel–Walfisz** at level `A`: uniformly for moduli up to `(log x)^A`, the primes are
equidistributed in the reduced classes with error `x (log x)^{-A}`.
EXTERNAL_ANALYTIC — stated, never inhabited. -/
def SiegelWalfisz (A : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x q a : ℕ, 3 ≤ x → 1 ≤ q → (q : ℝ) ≤ (Real.log x) ^ A →
    Nat.Coprime a q →
      |(primeCountAP x q a : ℝ) - (primeCount x : ℝ) / (Nat.totient q : ℝ)|
        ≤ C * (x : ℝ) * (Real.log x) ^ (-A)

/-! ## 2. Zero density -/

/-- The number of zeros of the L-function of `χ` with `Re ρ ≥ σ` and `|Im ρ| ≤ T`. -/
noncomputable def zeroCountFor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (sigma T : ℝ) :
    ℕ :=
  Set.ncard {rho : ℂ | DirichletCharacter.LFunction χ rho = 0 ∧ sigma ≤ rho.re ∧ |rho.im| ≤ T}

/-- **Zero density** for the L-function of `χ`, in the usual `(qT)^{c(1−σ)}` shape.
EXTERNAL_ANALYTIC — stated, never inhabited. -/
def ZeroDensityFor {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (c C : ℝ) : Prop :=
  ∀ sigma T : ℝ, (1 : ℝ) / 2 ≤ sigma → sigma ≤ 1 → 2 ≤ T →
    (zeroCountFor χ sigma T : ℝ)
      ≤ C * ((N : ℝ) * T) ^ (c * (1 - sigma)) * (Real.log ((N : ℝ) * T)) ^ C

/-! ## 3. Explicit formula: data plus deterministic adapter -/

/-- The data supplied by an explicit formula at scale `x`: a counting function, a main term, a
finite set of contributing zeros with their (nonnegative) masses, and the exact identity
`count = main − ∑ zero masses (signed by `sgn`) + error`. -/
structure ExplicitFormulaData where
  /-- The counted quantity at scale `x`. -/
  count : ℝ → ℝ
  /-- The main term at scale `x`. -/
  main : ℝ → ℝ
  /-- The contributing zeros at scale `x`. -/
  zeros : ℝ → Finset ℂ
  /-- The signed contribution of a zero. -/
  contrib : ℝ → ℂ → ℝ
  /-- The error term at scale `x`. -/
  err : ℝ → ℝ
  /-- The exact explicit-formula identity. -/
  formula : ∀ x, count x = main x - ∑ rho ∈ zeros x, contrib x rho + err x

/-- **Deterministic adapter for the explicit formula.**  No analytic input of its own: if the
zero contributions and the error are individually small, the counted quantity is close to the
main term.  Every analytic ingredient stays a hypothesis. -/
theorem counting_close_to_main_of_small_zero_mass (E : ExplicitFormulaData) (x eps delta : ℝ)
    (hzero : |∑ rho ∈ E.zeros x, E.contrib x rho| ≤ eps) (herr : |E.err x| ≤ delta) :
    |E.count x - E.main x| ≤ eps + delta := by
  have h := E.formula x
  have : E.count x - E.main x = -(∑ rho ∈ E.zeros x, E.contrib x rho) + E.err x := by
    rw [h]; ring
  rw [this]
  calc |-(∑ rho ∈ E.zeros x, E.contrib x rho) + E.err x|
      ≤ |-(∑ rho ∈ E.zeros x, E.contrib x rho)| + |E.err x| := abs_add_le _ _
    _ = |∑ rho ∈ E.zeros x, E.contrib x rho| + |E.err x| := by rw [abs_neg]
    _ ≤ eps + delta := add_le_add hzero herr

/-! ## 4. Spectral / Kloosterman inputs -/

/-- **KMS-type spectral input** for a per-mode callable: each mode of a family is bounded by the
stated budget.  EXTERNAL_ANALYTIC — stated, never inhabited.  Note the firewall in
`KloostermanSynthesisEnergy`: a per-mode bound of this shape does *not* close a global
covariance smaller than `N · budget`. -/
def KMSInput (N : ℕ) (a : ℕ → ℝ) (budget : ℝ) : Prop := ∀ i < N, |a i| ≤ budget

/-- **Blomer–Pascadi input**: a saving of size `X^{-eta}` for the stated bilinear form.
EXTERNAL_ANALYTIC — stated, never inhabited. -/
def BlomerPascadiInput (form : ℝ → ℝ) (eta : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X → |form X| ≤ C * X ^ (1 - eta)

/-- **Wright-type moment input** for a family of moments.  EXTERNAL_ANALYTIC — stated, never
inhabited. -/
def WrightMomentInput (moment : ℕ → ℝ → ℝ) (k : ℕ) (C B : ℝ) : Prop :=
  ∀ X : ℝ, 3 ≤ X → |moment k X| ≤ C * X * (Real.log X) ^ B

/-! ## 5. The source-AP bank -/

/-- **Source-AP bank**: equidistribution of the source weights in progressions to the stated
level, with the stated logarithmic precision.  EXTERNAL_ANALYTIC — stated, never inhabited. -/
def SourceAPBank (w : ℕ → ℝ) (level B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ level →
    Nat.Coprime a q →
      |(∑ n ∈ (range ⌈x⌉₊).filter (fun n => n % q = a), w n)
          - (∑ n ∈ range ⌈x⌉₊, w n) / (Nat.totient q : ℝ)|
        ≤ C * x * (Real.log x) ^ (-B)

/-! ## 6. The deterministic half of the affine character estimate -/

/-- **Deterministic `√ℓ` bound for one affine mode.**  A single affine character mode is bounded
by `√(ℓ · source energy)`; this is a consequence of the Gram identity, and needs no analytic
input.  (The frontier's `|V⁻| ≪ U L²⁰ σ_{-1}(k) / (ν √ℓ)` uses this together with the
coefficient-mass bookkeeping, which is *not* claimed here.) -/
theorem affine_mode_bound {l : ℕ} (hl : 0 < l) (f : ℕ → ℂ) {a : ℕ} (ha : a ∈ range l) :
    ‖affineTransform l f a‖ ^ 2 ≤ (l : ℝ) * ∑ x ∈ range l, ‖f x‖ ^ 2 := by
  rw [← affine_parseval hl f]
  refine Finset.single_le_sum (f := fun a => ‖affineTransform l f a‖ ^ 2) ?_ ha
  intro i _
  positivity

end Gate1B.R11.Frontier.Latest
