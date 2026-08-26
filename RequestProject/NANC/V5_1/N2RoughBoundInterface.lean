/-
NANC V5.1 — THE LEMMA-7.18 ROUGH-BOUND INTERFACE AND THE ELEMENTARY
SIGMA ARITHMETIC.

Two strictly separated layers live in this file.

LEAN-PROVED (elementary, no analytic content):

  * `sigma_ge_of_eps_le_nu_div_hundred` :  0 ≤ ε ≤ ν/100 and σ = ν − 2ε  ⟹  σ ≥ (49/50)·ν;
  * `sigma_ge_49_300_of_nu_one_sixth`   :  the ν = 1/6 specialization, σ ≥ 49/300;
  * `rough_cardFactors_le_six`          :  if every prime factor of n > 1 is ≥ n^σ and
                                            σ ≥ 49/300, then Ω(n) ≤ 6
                                            (total number of prime factors *with
                                            multiplicity*, not ω(n)).

UNINHABITED (analytic, external):

  * `FMLemma718RoughBound` — the source-reading statement
        H(n) = (1 ∗ g)(v(n)) · 1_{P⁻(n) ≥ n^σ},   σ = ν − 2ε,   |H(n)| ≤ C_{g,ν};
  * `N2HUniformity`        — sup_{n ∈ N₂(ε)} |H_ε(n)| ≤ C_{g,ν}, uniformly in small ε.

PERMANENT FIREWALLS:

    sigma arithmetic  ≠  proof that Ford–Maynard actually uses this sigma;
    uniform rough factor-count bound  ≠  uniform analytic H bound
      (`uniform_factor_bound_not_H_uniformity`).

The map `FMLemma718RoughBound (for every admissible ε)  →  N2HUniformity` proved
below is a **field projection**, not new mathematics: the uniform bound is one of
the conjuncts of the rough-bound interface.
-/
import Mathlib
import RequestProject.NANC.V5_1.ProvenancePatch

namespace NANC.V5_1

open scoped BigOperators

/-! ### 1. Elementary sigma arithmetic (LEAN-PROVED) -/

/-- With `σ = ν − 2ε` and `0 ≤ ε ≤ ν/100` one has `σ ≥ (49/50)·ν`. -/
theorem sigma_ge_of_eps_le_nu_div_hundred {nu eps sigma : ℚ}
    (h0 : 0 ≤ eps) (h1 : eps ≤ nu / 100) (hs : sigma = nu - 2 * eps) :
    (49 / 50) * nu ≤ sigma := by
  have hnonneg : 0 ≤ eps := h0
  rw [hs]; linarith

/-- The `ν = 1/6` specialization: `σ ≥ 49/300`. -/
theorem sigma_ge_49_300_of_nu_one_sixth {eps sigma : ℚ}
    (h0 : 0 ≤ eps) (h1 : eps ≤ (1 / 6 : ℚ) / 100) (hs : sigma = 1 / 6 - 2 * eps) :
    (49 / 300 : ℚ) ≤ sigma := by
  have hnonneg : 0 ≤ eps := h0
  rw [hs]; linarith

/-- Real-valued form of the previous bound, in the shape used by the roughness
condition. -/
theorem real_sigma_ge_49_300_of_nu_one_sixth {eps sigma : ℝ}
    (h0 : 0 ≤ eps) (h1 : eps ≤ (1 / 6 : ℝ) / 100) (hs : sigma = 1 / 6 - 2 * eps) :
    (49 / 300 : ℝ) ≤ sigma := by
  have hnonneg : 0 ≤ eps := h0
  rw [hs]; linarith

/-! ### 2. The elementary factor-count consequence (LEAN-PROVED) -/

/-- `n` is `σ`-rough: `n > 1` and every prime factor of `n` is at least `n^σ`. -/
def RoughAt (sigma : ℝ) (n : ℕ) : Prop :=
  1 < n ∧ ∀ p ∈ n.primeFactorsList, (n : ℝ) ^ sigma ≤ (p : ℝ)

/-- An auxiliary list bound: a product of reals all at least `c ≥ 0` is at least
`c ^ (length)`. -/
theorem pow_length_le_prod {c : ℝ} (hc : 0 ≤ c) :
    ∀ (l : List ℝ), (∀ x ∈ l, c ≤ x) → c ^ l.length ≤ l.prod := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro h
      have h1 : c ≤ a := h a (by simp)
      have h2 : c ^ t.length ≤ t.prod := ih fun x hx => h x (by simp [hx])
      have h3 : (0 : ℝ) ≤ c ^ t.length := pow_nonneg hc _
      simp only [List.length_cons, List.prod_cons, pow_succ]
      calc c ^ t.length * c ≤ t.prod * a := mul_le_mul h2 h1 hc (le_trans h3 h2)
        _ = a * t.prod := by ring

/-- **The safe factor-count theorem.**  If `n > 1` is `σ`-rough with `σ ≥ 49/300`,
then the number of prime factors of `n` *with multiplicity* is at most `6`. -/
theorem rough_length_primeFactorsList_le_six {n : ℕ} {sigma : ℝ}
    (hs : (49 / 300 : ℝ) ≤ sigma) (hrough : RoughAt sigma n) :
    n.primeFactorsList.length ≤ 6 := by
  obtain ⟨hn, h⟩ := hrough
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn
  have hs0 : (0 : ℝ) < sigma := by linarith
  have hcpos : (0 : ℝ) < (n : ℝ) ^ sigma := Real.rpow_pos_of_pos hn0 _
  set L : List ℝ := n.primeFactorsList.map (fun p : ℕ => (p : ℝ)) with hL
  have hlen : L.length = n.primeFactorsList.length := by simp [hL]
  have hmem : ∀ x ∈ L, (n : ℝ) ^ sigma ≤ x := by
    intro x hx
    rw [hL, List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact h p hp
  have hprod : ((n : ℝ) ^ sigma) ^ L.length ≤ L.prod := pow_length_le_prod hcpos.le L hmem
  have hcast : L.prod = (n : ℝ) := by
    rw [hL, ← Nat.cast_list_prod, Nat.prod_primeFactorsList (by omega)]
  rw [hcast, hlen] at hprod
  set k := n.primeFactorsList.length
  have h2 : (n : ℝ) ^ (sigma * k) ≤ (n : ℝ) := by
    rw [Real.rpow_mul hn0.le, Real.rpow_natCast]
    exact hprod
  have hlog : sigma * k * Real.log n ≤ Real.log n := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hn0 _) h2
    rwa [Real.log_rpow hn0] at this
  have hlogpos : 0 < Real.log n := Real.log_pos hnR
  have hsk : sigma * k ≤ 1 := by nlinarith
  have hk7 : (k : ℝ) < 7 := by nlinarith [Nat.cast_nonneg (α := ℝ) k]
  have : k < 7 := by exact_mod_cast hk7
  omega

/-- The same statement in terms of `Ω`, the total number of prime factors with
multiplicity. -/
theorem rough_cardFactors_le_six {n : ℕ} {sigma : ℝ}
    (hs : (49 / 300 : ℝ) ≤ sigma) (hrough : RoughAt sigma n) :
    ArithmeticFunction.cardFactors n ≤ 6 := by
  rw [ArithmeticFunction.cardFactors_apply]
  exact rough_length_primeFactorsList_le_six hs hrough

/-- Combined form: for the `P_ε` parameters `ν = 1/6`, `σ = 1/6 − 2ε` with
`0 ≤ ε ≤ 1/600`, every `σ`-rough integer has `Ω(n) ≤ 6`. -/
theorem PEpsilon_rough_cardFactors_le_six {n : ℕ} {eps sigma : ℝ}
    (h0 : 0 ≤ eps) (h1 : eps ≤ (1 / 6 : ℝ) / 100) (hsig : sigma = 1 / 6 - 2 * eps)
    (hrough : RoughAt sigma n) : ArithmeticFunction.cardFactors n ≤ 6 :=
  rough_cardFactors_le_six (real_sigma_ge_49_300_of_nu_one_sixth h0 h1 hsig) hrough

/-! ### 3. The Lemma-7.18 rough-bound interface (UNINHABITED) -/

/-- The Dirichlet convolution `(1 ∗ g)(m) = ∑_{d ∣ m} g(d)` in finite form. -/
noncomputable def oneConv (g : ℕ → ℝ) (m : ℕ) : ℝ := ∑ d ∈ m.divisors, g d

open Classical in
/-- The roughness indicator `1_{P⁻(n) ≥ n^σ}`. -/
noncomputable def roughIndicator (sigma : ℝ) (n : ℕ) : ℝ :=
  if RoughAt sigma n then 1 else 0

theorem roughIndicator_eq_one {sigma : ℝ} {n : ℕ} (h : RoughAt sigma n) :
    roughIndicator sigma n = 1 := by
  classical
  simp [roughIndicator, h]

theorem roughIndicator_eq_zero {sigma : ℝ} {n : ℕ} (h : ¬ RoughAt sigma n) :
    roughIndicator sigma n = 0 := by
  classical
  simp [roughIndicator, h]

/-- The finite data the Lemma-7.18 reading speaks about at one scale. -/
structure Lemma718Data where
  /-- The Ford–Maynard exponent `ν`. -/
  nu : ℝ
  /-- The shrinking parameter `ε`. -/
  eps : ℝ
  /-- The roughness exponent `σ`. -/
  sigma : ℝ
  /-- The divisor-type function `g`. -/
  g : ℕ → ℝ
  /-- The reduction `n ↦ v(n)` appearing in the source reading. -/
  v : ℕ → ℕ
  /-- The weight `H`. -/
  H : ℕ → ℝ
  /-- The constant `C_{g,ν}`. -/
  C : ℝ
  /-- The exceptional region `N₂(ε)` at this scale. -/
  region : Finset ℕ

/-- **UNINHABITED external analytic interface — `FMLemma718RoughBound`.**

Its intended content is the source reading

    H(n) = (1 ∗ g)(v(n)) · 1_{P⁻(n) ≥ n^σ},    σ = ν − 2ε,    |H(n)| ≤ C_{g,ν}.

PROVENANCE: `assumedSourceReading` (see `lemma718Entry`) — no readable copy of
the relevant Ford–Maynard passage is present in this repository, so the reading
has not been inspected verbatim.  It is **not** inhabited here. -/
structure FMLemma718RoughBound (D : Lemma718Data) : Prop where
  /-- The roughness exponent of the `P_ε` specialization. -/
  sigma_eq : D.sigma = D.nu - 2 * D.eps
  /-- The convolution shape of `H`. -/
  H_form : ∀ n, D.H n = oneConv D.g (D.v n) * roughIndicator D.sigma n
  /-- The uniform bound `|H(n)| ≤ C_{g,ν}` on the exceptional region. -/
  H_bound : ∀ n ∈ D.region, |D.H n| ≤ D.C

/-- Provenance record for the rough-bound reading: assumed, never inspected. -/
def lemma718Entry : V51Entry where
  name := "FMLemma718RoughBound"
  provenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected
  notes :=
    "H(n) = (1*g)(v n) · 1_{P^-(n) ≥ n^σ} with σ = ν − 2ε and |H(n)| ≤ C_{g,ν}; " ++
    "attributed to the Ford–Maynard manuscript, exact passage NOT inspected in this " ++
    "repository.  UNINHABITED."

theorem lemma718Entry_not_leanEvidence : V51Entry.IsLeanEvidence lemma718Entry = false := rfl

theorem lemma718Entry_provenance_ne_leanProved :
    lemma718Entry.provenance ≠ V51Provenance.leanProved := by decide

theorem lemma718Entry_provenance_ne_externallyPublished :
    lemma718Entry.provenance ≠ V51Provenance.externallyPublished := by decide

theorem lemma718Entry_provenance_ne_sourceSpecificAnalyticPass :
    lemma718Entry.provenance ≠ V51Provenance.sourceSpecificAnalyticPass := by decide

/-! ### 4. `N2HUniformity` (UNINHABITED) and the projection -/

/-- A family of exceptional-region data indexed by the shrinking parameter. -/
structure N2Family where
  /-- The data at parameter `ε`. -/
  data : ℝ → Lemma718Data
  /-- The uniform constant `C_{g,ν}` the family is supposed to obey. -/
  C : ℝ
  /-- The admissibility threshold for `ε`. -/
  epsBound : ℝ

/-- **UNINHABITED analytic assertion — `N2HUniformity`.**

    sup_{n ∈ N₂(ε)} |H_ε(n)| ≤ C_{g,ν}   uniformly for all sufficiently small ε. -/
def N2HUniformity (F : N2Family) : Prop :=
  ∀ eps : ℝ, 0 < eps → eps < F.epsBound → ∀ n ∈ (F.data eps).region, |(F.data eps).H n| ≤ F.C

/-- **Field projection, NOT new mathematics.**  If the rough-bound interface holds
at every admissible `ε` with the family constant, then `N2HUniformity` holds: the
uniform bound is literally the `H_bound` conjunct of `FMLemma718RoughBound`, so
this map is a definitional unfolding / field projection. -/
theorem lemma718_projects_to_N2HUniformity {F : N2Family}
    (hC : ∀ eps : ℝ, (F.data eps).C = F.C)
    (h : ∀ eps : ℝ, 0 < eps → eps < F.epsBound → FMLemma718RoughBound (F.data eps)) :
    N2HUniformity F := by
  intro eps h0 h1 n hn
  have := (h eps h0 h1).H_bound n hn
  rwa [hC eps] at this

/-- Provenance record for `N2HUniformity`: an assumed source reading, uninhabited. -/
def n2HUniformityEntry : V51Entry where
  name := "N2HUniformity"
  provenance := V51Provenance.assumedSourceReading
  inspection := SourceInspection.notInspected
  notes :=
    "sup_{n ∈ N2(ε)} |H_ε(n)| ≤ C_{g,ν} uniformly for small ε.  Obtained from " ++
    "FMLemma718RoughBound by field projection, hence carries the same (assumed) " ++
    "provenance; it is NOT an independent analytic derivation.  UNINHABITED."

theorem n2HUniformityEntry_not_leanEvidence :
    V51Entry.IsLeanEvidence n2HUniformityEntry = false := rfl

/-! ### 5. Firewall: factor-count bound ≠ analytic H-uniformity -/

/-- Sample data used only to separate the elementary factor-count bound from the
analytic `H`-uniformity assertion. -/
noncomputable def separatingData : Lemma718Data where
  nu := 1 / 6
  eps := 0
  sigma := 49 / 300
  g := fun _ => 0
  v := id
  H := fun _ => 1
  C := 0
  region := {5}

/-- `5` is `49/300`-rough. -/
theorem roughAt_five : RoughAt (49 / 300 : ℝ) 5 := by
  refine ⟨by norm_num, ?_⟩
  intro p hp
  have h5 : Nat.primeFactorsList 5 = [5] := Nat.primeFactorsList_prime (by norm_num)
  rw [h5] at hp
  have hp5 : p = 5 := by simpa using hp
  subst hp5
  have : ((5 : ℕ) : ℝ) ^ (49 / 300 : ℝ) ≤ ((5 : ℕ) : ℝ) ^ (1 : ℝ) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  simpa using this

/-- **CG-14 (firewall).**  A uniform *rough factor-count* bound on the exceptional
region does not give the uniform analytic bound `|H| ≤ C`: here every region
element is `σ`-rough (hence has `Ω ≤ 6`), yet `N2HUniformity` fails. -/
theorem uniform_factor_bound_not_H_uniformity :
    ∃ F : N2Family,
      (∀ eps : ℝ, ∀ n ∈ (F.data eps).region,
          RoughAt (F.data eps).sigma n ∧ ArithmeticFunction.cardFactors n ≤ 6) ∧
      ¬ N2HUniformity F := by
  refine ⟨⟨fun _ => separatingData, 0, 1⟩, ?_, ?_⟩
  · intro eps n hn
    have hn5 : n = 5 := by simpa [separatingData] using hn
    subst hn5
    exact ⟨roughAt_five, rough_cardFactors_le_six (by norm_num) roughAt_five⟩
  · intro h
    have := h (1 / 2) (by norm_num) (by norm_num) 5 (by simp [separatingData])
    simp [separatingData] at this
    linarith

end NANC.V5_1
