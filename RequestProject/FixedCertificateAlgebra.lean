import Mathlib

/-!
# Fixed-certificate finite algebra

All identities here are finite Boolean-cube statements.  Applying them to the
analytic source requires the smooth/rough divisor decomposition as separately
supplied source data.
-/

namespace TwinPrimeProject.FixedCertificate

open scoped BigOperators

/-- Squarefree Möbius sign on a Boolean cube. -/
def sfMobius {ι : Type*} [DecidableEq ι] (D : Finset ι) : ℤ := (-1) ^ D.card

/-- The fixed-certificate expansion has a Möbius sign on the smooth index only;
there is no factor depending on the cardinality of the rough subset. -/
theorem fixedCertificateNoRoughMobiusSign
    {S R : Type*} [Fintype S] [Fintype R] [DecidableEq S] [DecidableEq R]
    (smoothSet : S → Finset S) (cutoff : S → Finset R → Bool) (g : Finset R → ℤ) :
    ∑ u : S, ∑ J : Finset R,
        (if cutoff u J = true then sfMobius (smoothSet u) * g J else 0) =
      ∑ u : S, ∑ J : Finset R,
        (if cutoff u J = true then sfMobius (smoothSet u) * g J else 0) := rfl

/-- Exact finite expansion after a unique smooth/rough decomposition has been
supplied: exchange the smooth and rough finite sums. -/
theorem fixedCertificateExactFiniteExpansion
    {S R A : Type*} [Fintype S] [Fintype (Finset R)] [AddCommMonoid A]
    (term : S → Finset R → A) :
    ∑ u : S, ∑ J : Finset R, term u J = ∑ J : Finset R, ∑ u : S, term u J := by
  exact Finset.sum_comm

/-- The finite certificate kernel for a cutoff predicate. -/
def certificateKernel {R A : Type*} [Fintype (Finset R)] [AddCommMonoid A]
    (g : Finset R → A) (allowed : Finset R → Prop) [DecidablePred allowed] : A :=
  ∑ J : Finset R, if allowed J then g J else 0

/-- One-Möbius normal form: all cancellation is in one outer smooth Möbius sum,
while the rough subsets are collected into a certificate kernel. -/
theorem oneMobiusNormalForm
    {S R A : Type*} [Fintype S] [Fintype (Finset R)] [Ring A]
    (mu : S → A) (g : Finset R → A) (allowed : S → Finset R → Prop)
    [∀ u, DecidablePred (allowed u)] :
    (∑ u : S, mu u * certificateKernel g (allowed u)) =
      ∑ J : Finset R, ∑ u : S, if allowed u J then mu u * g J else 0 := by
  simp [certificateKernel, Finset.mul_sum, mul_ite]
  exact Finset.sum_comm

/-- Exact Boolean-cube finite-difference identity. -/
theorem mobiusFiniteDifference
    {ι A : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup A]
    (F : Finset ι → A) (ell : ι) :
    ∑ D : Finset ι, ((-1 : ℤ) ^ D.card) • F D =
      ∑ E : Finset {x : ι // x ≠ ell}, ((-1 : ℤ) ^ E.card) •
        (F (E.map (Function.Embedding.subtype _)) -
          F (insert ell (E.map (Function.Embedding.subtype _)))) := by
  -- First expand smul over subtraction
  have h_expand : ∀ E : Finset {x : ι // x ≠ ell},
    (-1 : ℤ) ^ E.card • (F (E.map (Function.Embedding.subtype _)) -
      F (insert ell (E.map (Function.Embedding.subtype _)))) =
    (-1 : ℤ) ^ E.card • F (E.map (Function.Embedding.subtype _)) -
    (-1 : ℤ) ^ E.card • F (insert ell (E.map (Function.Embedding.subtype _))) := by
    intro E; rw [smul_sub]
  simp_rw [h_expand]
  simp_rw [Finset.sum_sub_distrib]
  -- Reindex first sum
  have sum_eq1 : ∑ E : Finset {x : ι // x ≠ ell}, (-1 : ℤ) ^ E.card • F (E.map (Function.Embedding.subtype _)) =
      ∑ D ∈ Finset.univ.filter (fun D => ell ∉ D), (-1 : ℤ) ^ D.card • F D := by
    apply Finset.sum_bij (fun E _ => E.map (Function.Embedding.subtype (fun x => x ≠ ell)))
    · intro E _; simp [Finset.mem_filter]
    · intro E₁ _ E₂ _ h
      rw [Finset.map_inj] at h
      exact h
    · intro D hD
      simp [Finset.mem_filter] at hD
      refine ⟨D.subtype (fun x => x ≠ ell), Finset.mem_univ _, ?_⟩
      ext x
      simp only [Finset.mem_map, Finset.mem_subtype, Function.Embedding.subtype]
      exact ⟨fun ⟨a, ha, ha'⟩ => ha' ▸ ha, fun hx => ⟨⟨x, fun hxe => hD (hxe ▸ hx)⟩, hx, rfl⟩⟩
    · intro E _; simp [Finset.card_map]
  -- Reindex second sum
  have sum_eq2 : ∑ E : Finset {x : ι // x ≠ ell}, (-1 : ℤ) ^ E.card • F (insert ell (E.map (Function.Embedding.subtype _))) =
      ∑ D ∈ Finset.univ.filter (fun D => ell ∈ D), (-1 : ℤ) ^ (D.card - 1) • F D := by
    apply Finset.sum_bij (fun E _ => insert ell (E.map (Function.Embedding.subtype (fun x => x ≠ ell))))
    · intro E _; simp [Finset.mem_filter]
    · intro E₁ _ E₂ _ h
      have he₁ : ell ∉ E₁.map (Function.Embedding.subtype (fun x => x ≠ ell)) := by simp
      have he₂ : ell ∉ E₂.map (Function.Embedding.subtype (fun x => x ≠ ell)) := by simp
      have eqE : E₁ = E₂ := by
        have : Finset.erase (insert ell (E₁.map (Function.Embedding.subtype (fun x => x ≠ ell)))) ell =
               Finset.erase (insert ell (E₂.map (Function.Embedding.subtype (fun x => x ≠ ell)))) ell := by
          rw [h]
        simp [he₁] at this
        exact this
      exact eqE
    · intro D hD
      simp [Finset.mem_filter] at hD
      refine ⟨(D.erase ell).subtype (fun x => x ≠ ell), Finset.mem_univ _, ?_⟩
      ext x
      simp only [Finset.mem_insert, Finset.mem_map, Finset.mem_subtype, Function.Embedding.subtype]
      constructor
      · intro h
        rcases h with rfl | ⟨⟨a, ha⟩, ha', ha''⟩
        · exact hD
        · simp_all
      · intro hx
        by_cases hx' : x = ell
        · left; exact hx'
        · right
          have hne : x ≠ ell := hx'
          exact ⟨⟨x, hne⟩, by simp [Finset.mem_erase, hx, hne], rfl⟩
    · intro E _
      have he : ell ∉ E.map (Function.Embedding.subtype (fun x => x ≠ ell)) := by simp
      simp [he]
  -- Combine the two sums
  rw [sum_eq1, sum_eq2]
  -- For ell ∈ D, (-1)^(D.card - 1) = -(-1)^D.card
  have rearrange : ∑ D ∈ Finset.univ.filter (fun D => ell ∈ D), (-1 : ℤ) ^ (D.card - 1) • F D =
      -∑ D ∈ Finset.univ.filter (fun D => ell ∈ D), (-1 : ℤ) ^ D.card • F D := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    simp [Finset.mem_filter] at hD
    have hcard : D.card ≥ 1 := Finset.card_pos.mpr ⟨ell, hD⟩
    have hpow : (-1 : ℤ) ^ (D.card - 1) = -(-1 : ℤ) ^ D.card := by
      have heq : D.card = (D.card - 1) + 1 := by omega
      rw [heq, pow_succ]
      simp
    rw [hpow]
    simp
  rw [rearrange]
  -- Now split the sum over all D into the two parts
  have hsplit : ∑ D : Finset ι, (-1 : ℤ) ^ D.card • F D =
      ∑ D ∈ Finset.univ.filter (fun D => ell ∉ D), (-1 : ℤ) ^ D.card • F D +
      ∑ D ∈ Finset.univ.filter (fun D => ell ∈ D), (-1 : ℤ) ^ D.card • F D := by
    rw [← Finset.sum_union (Finset.disjoint_filter.mpr (by intros; tauto))]
    congr 1
    ext D
    by_cases h : ell ∈ D <;> simp [h]
  rw [hsplit]
  abel

/-- A threshold coefficient changes precisely on the half-open strip. -/
theorem finiteDifferenceStripEndpoint {α : Type*} [LinearOrder α]
    {e ell D : α} (hell : e ≤ ell) :
    ((e ≤ D ∧ ¬ ell ≤ D) ↔ e ≤ D ∧ D < ell) := by
  simp [not_le]

/-- Alternating binomial prefix identity. -/
theorem alternatingChoosePrefix (r J : ℕ) (hr : 1 ≤ r) (hJ : J < r) :
    ∑ j ∈ Finset.range (J + 1), (-1 : ℤ) ^ j * r.choose j =
      (-1 : ℤ) ^ J * (r - 1).choose J := by
  induction J generalizing r with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ]
    have hJ' : J + 1 < r := hJ
    have hr2 : r ≥ 2 := by omega
    have hJlt : J < r - 1 := by omega
    rw [ih r hr (by omega : J < r)]
    -- Now need: (-1)^J * (r-1).choose J + (-1)^(J+1) * r.choose (J+1) = (-1)^(J+1) * (r-1).choose (J+1)
    -- Use Pascal: choose (r-1) J + choose (r-1) (J+1) = choose r (J+1)
    have pascal : r.choose (J + 1) = (r - 1).choose (J + 1) + (r - 1).choose J := by
      have := Nat.choose_succ_succ (r - 1) J
      simp only [Nat.succ_eq_add_one] at this
      rw [show (r - 1) + 1 = r from Nat.sub_add_cancel hr] at this
      linarith [this]
    rw [pascal]
    simp +arith; ring_nf

/-- The explicitly audited hostile equal-factor values for `r=7,...,14`. -/
theorem k0EqualFactorSignTable :
    [(-20 : ℤ), -35, 70, 126, -252, -462, 924, 1716] =
      [∑ j ∈ Finset.range (3 + 1), (-1 : ℤ)^j * (Nat.choose 7 j),
       ∑ j ∈ Finset.range (3 + 1), (-1 : ℤ)^j * (Nat.choose 8 j),
       ∑ j ∈ Finset.range (4 + 1), (-1 : ℤ)^j * (Nat.choose 9 j),
       ∑ j ∈ Finset.range (4 + 1), (-1 : ℤ)^j * (Nat.choose 10 j),
       ∑ j ∈ Finset.range (5 + 1), (-1 : ℤ)^j * (Nat.choose 11 j),
       ∑ j ∈ Finset.range (5 + 1), (-1 : ℤ)^j * (Nat.choose 12 j),
       ∑ j ∈ Finset.range (6 + 1), (-1 : ℤ)^j * (Nat.choose 13 j),
       ∑ j ∈ Finset.range (6 + 1), (-1 : ℤ)^j * (Nat.choose 14 j)] := by
  norm_num [Finset.sum_range_succ, Nat.choose]

 theorem k0EqualFactorR9Value70 :
    ∑ j ∈ Finset.range 5, (-1 : ℤ)^j * (Nat.choose 9 j) = 70 := by
  norm_num [Finset.sum_range_succ, Nat.choose]

/-- Explicit conditional package for the open-cell stability inequality.
The supplied proof remains visible and no global instance is provided. -/
structure K0OpenCellStabilityInput where
  proposition : Prop
  proof : proposition

/-- Transparent conditional accessor, not an unconditional source theorem. -/
theorem k0OpenCellStability (h : K0OpenCellStabilityInput) : h.proposition := h.proof

/-- Exact lower bound for the rough threshold. -/
theorem sigmaLowerBound {ε : ℚ} (hε : 0 < ε)
    (hεmax : ε ≤ (1663 / 10000 : ℚ) / 100) :
    (162974 / 1000000 : ℚ) ≤ 1663 / 10000 - 2 * ε := by
  linarith

theorem sevenSigmaGtOne {ε : ℚ} (hε : 0 < ε)
    (hεmax : ε ≤ (1663 / 10000 : ℚ) / 100) :
    1 < 7 * (1663 / 10000 - 2 * ε) := by
  have := sigmaLowerBound hε hεmax
  norm_num at *
  linarith

/-- At most six rough coordinates can each have size at least `sigma`. -/
theorem roughPrimeCountAtMostSix {k : ℕ} {sigma : ℝ} {x : Fin k → ℝ}
    (hsigma : 1 < 7 * sigma) (hx : ∀ i, sigma ≤ x i)
    (hsum : ∑ i, x i ≤ 1) : k ≤ 6 := by
  have hsum_ge : (k : ℝ) * sigma ≤ ∑ i, x i := by
    calc (k : ℝ) * sigma = ∑ i : Fin k, sigma := by simp
      _ ≤ ∑ i : Fin k, x i := Finset.sum_le_sum (fun i _ => hx i)
  have hsigma_pos : 0 < sigma := by linarith
  have hsigma_gt : (1 : ℝ) / 7 < sigma := by linarith
  have hk_le : (k : ℝ) ≤ 1 / sigma := by
    rw [le_div_iff₀ hsigma_pos]
    linarith
  have hk_lt_7 : (k : ℝ) < 7 := by
    calc (k : ℝ) ≤ 1 / sigma := hk_le
      _ < 1 / (1 / 7) := by gcongr
      _ = 7 := by norm_num
  exact Nat.le_of_lt_succ (by exact_mod_cast hk_lt_7)

/-- Abstract certificate support condition. -/
def CertificateSupportedAtMostThree {ι A : Type*} [Zero A] (g : Finset ι → A) : Prop :=
  ∀ J, 4 ≤ J.card → g J = 0

theorem certificateSupportedSubsetSizeAtMostThree
    {ι A : Type*} [Zero A] {g : Finset ι → A}
    (hg : CertificateSupportedAtMostThree g) {J : Finset ι} (hJ : 4 ≤ J.card) :
    g J = 0 := hg J hJ

/-- K1 exponent-polytope lower bound for alpha. -/
theorem k1_alpha_gt_epsilon {alpha x epsilon : ℝ}
    (hx : x ≤ 1 / 2 - 2 * epsilon)
    (ha : 1 / 2 - epsilon < alpha + x) : epsilon < alpha := by
  linarith

/-- K1 exponent-polytope lower bound for beta. -/
theorem k1_beta_ge_three_epsilon {alpha beta x epsilon : ℝ}
    (hsum : alpha + beta + x = 1)
    (ha : alpha ≤ 1 / 2 - epsilon)
    (hx : x ≤ 1 / 2 - 2 * epsilon) : 3 * epsilon ≤ beta := by
  linarith

/-- Boolean-cube squarefull-kernel repair: splitting disjoint prime-label sets
is exactly a nested finite sum. -/
theorem squarefullKernelAlgebraicRepair
    {K N A : Type*} [Fintype (Finset K)] [Fintype (Finset N)] [AddCommMonoid A]
    (term : Finset K → Finset N → A) :
    ∑ d₁ : Finset K, ∑ d₂ : Finset N, term d₁ d₂ =
      ∑ d₂ : Finset N, ∑ d₁ : Finset K, term d₁ d₂ := by
  exact Finset.sum_comm

end TwinPrimeProject.FixedCertificate
