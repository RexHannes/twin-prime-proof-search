/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the exact j = 2 residual operator  (P8)

Append-only module.  All algebra is exact; **exactly one** analytic proposition is created,
`J2ResidualCenteredBound`, and it is never inhabited.

The latest analytic state names the first residual operator as the *centered* `j = 2` operator
`D_B`.  Here it is formalised with its four layers kept apart:

* `pairing`      — the bare pairing of the source against the row kernel;
* `dbRaw`        — the raw `j = 2` operator: the K = 5 rank-2 branch (coefficient `−10`) applied
                   to that pairing;
* `dbPrincipal`  — the principal part: source mass times kernel mean (an exact quantity, owned by
                   no analytic proposition);
* `dbCentered`   — the centered operator `D_B`, the actual residual;
* `dbMasked`     — the packet mask applied to any of the above.

Proved here: the exact splitting `raw = centered + principal`, exactness of the mask split
(no double charge), vanishing of the mean of the centered kernel, the deterministic adapter that
turns a bound on `D_B` into a bound on the raw operator, the **chart-independence theorem** (two
mask charts of the same `j = 2` residual do *not* create two independent analytic owners), and
the **countermodel** proving that the algebra alone does not imply the bound.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.CanonicalRoot
import Gate1B.R11.Frontier.CanonicalRootSync.KFiveAlgebra

namespace Gate1B.R11.Frontier.CanonicalRootSync

open Finset

/-! ## 1. The four layers -/

/-- The bare pairing of the source weight against the row kernel. -/
def pairing (s : Finset ℕ) (g K : ℕ → ℝ) : ℝ := ∑ n ∈ s, g n * K n

/-- The mean of the row kernel over the packet. -/
noncomputable def kernelMean (s : Finset ℕ) (K : ℕ → ℝ) : ℝ := (∑ n ∈ s, K n) / s.card

/-- **The raw `j = 2` operator**: the rank-2 branch of the K = 5 decomposition — coefficient
`hbCoeff 5 2 = −10` — applied to the bare pairing. -/
def dbRaw (s : Finset ℕ) (g K : ℕ → ℝ) : ℝ := (hbCoeff 5 2 : ℝ) * pairing s g K

/-- **The principal part** of the `j = 2` operator: source mass times kernel mean.  This is an
exact quantity; it owns no analytic proposition. -/
noncomputable def dbPrincipal (s : Finset ℕ) (g K : ℕ → ℝ) : ℝ :=
  (hbCoeff 5 2 : ℝ) * ((∑ n ∈ s, g n) * kernelMean s K)

/-- **The centered `j = 2` operator `D_B`**: the raw operator with the kernel mean removed. -/
noncomputable def dbCentered (s : Finset ℕ) (g K : ℕ → ℝ) : ℝ :=
  (hbCoeff 5 2 : ℝ) * ∑ n ∈ s, g n * (K n - kernelMean s K)

/-- **The packet mask** applied to the raw operator. -/
def dbMasked (s : Finset ℕ) (g K : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p] : ℝ :=
  dbRaw (s.filter p) g K

/-- The `j = 2` coefficient is `−10`, exactly as in the K = 5 row. -/
theorem dbRaw_coefficient (s : Finset ℕ) (g K : ℕ → ℝ) :
    dbRaw s g K = -10 * pairing s g K := by
  rw [dbRaw, hbCoeff_five_two]; norm_num

/-! ## 2. The exact algebraic identities -/

/-- **Exact splitting**: raw = centered + principal. -/
theorem dbRaw_eq_centered_add_principal (s : Finset ℕ) (g K : ℕ → ℝ) :
    dbRaw s g K = dbCentered s g K + dbPrincipal s g K := by
  unfold dbRaw dbCentered dbPrincipal pairing
  rw [← mul_add]
  congr 1
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-- **Exact mask split**: the raw operator is the masked part plus the complementary part, with
no double charge. -/
theorem dbRaw_mask_split (s : Finset ℕ) (g K : ℕ → ℝ) (p : ℕ → Prop) [DecidablePred p] :
    dbRaw s g K = dbMasked s g K p + dbMasked s g K (fun n => ¬ p n) := by
  unfold dbMasked dbRaw pairing
  rw [← mul_add, ← Finset.sum_filter_add_sum_filter_not s p]

/-- The centered kernel has mean zero on a nonempty packet: centering is idempotent. -/
theorem sum_centered_kernel (s : Finset ℕ) (K : ℕ → ℝ) (hs : s.Nonempty) :
    ∑ n ∈ s, (K n - kernelMean s K) = 0 := by
  have hcard : (s.card : ℝ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero, Finset.card_eq_zero]
    exact Finset.nonempty_iff_ne_empty.mp hs
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, kernelMean]
  field_simp
  ring

/-- The centered operator is linear in the source weight. -/
theorem dbCentered_add_source (s : Finset ℕ) (g₁ g₂ K : ℕ → ℝ) :
    dbCentered s (fun n => g₁ n + g₂ n) K = dbCentered s g₁ K + dbCentered s g₂ K := by
  unfold dbCentered
  rw [← mul_add, ← Finset.sum_add_distrib]
  exact congrArg _ (Finset.sum_congr rfl fun n _ => by ring)

/-- The principal part vanishes exactly when the source has zero mass or the kernel has zero
mean: it is an exact, owner-free quantity. -/
theorem dbPrincipal_eq_zero_iff (s : Finset ℕ) (g K : ℕ → ℝ) :
    dbPrincipal s g K = 0 ↔ (∑ n ∈ s, g n) = 0 ∨ kernelMean s K = 0 := by
  unfold dbPrincipal
  rw [hbCoeff_five_two]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · norm_num at h'
    · exact mul_eq_zero.mp h'
  · rintro (h | h) <;> simp [h]

/-! ## 3. The single open analytic proposition -/

/-- **`J2ResidualCenteredBound`** — the one open analytic owner surviving inside `j = 2`:
the centered `j = 2` residual family obeys the required logarithmic saving.
EXTERNAL_ANALYTIC / OPEN — stated, never inhabited, not an axiom. -/
def J2ResidualCenteredBound (DB : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget DB (S0 + 2)

/-- **Deterministic adapter.**  A bound on the centered operator plus a bound on the (exact)
principal part gives a bound on the raw operator.  All analytic content stays in the two
hypotheses. -/
theorem raw_budget_of_centered_and_principal {Raw Cen Prin : ℝ → ℝ} {S0 : ℕ}
    (hsplit : ∀ x, Raw x = Cen x + Prin x)
    (hC : J2ResidualCenteredBound Cen S0) (hP : ScalarBudget Prin (S0 + 2)) :
    ScalarBudget Raw (S0 + 2) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hC
  obtain ⟨C₂, hC₂, h₂⟩ := hP
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  calc |Raw x| = |Cen x + Prin x| := by rw [hsplit x]
    _ ≤ |Cen x| + |Prin x| := abs_add_le _ _
    _ ≤ C₁ * x / (Real.log x) ^ (S0 + 2) + C₂ * x / (Real.log x) ^ (S0 + 2) :=
        add_le_add (h₁ x hx) (h₂ x hx)
    _ = (C₁ + C₂) * x / (Real.log x) ^ (S0 + 2) := by ring

/-- **Chart independence: charts do not manufacture owners.**  If the centered residual is
bounded on each of two mask charts whose values add up to the whole, it is bounded on the whole.
Hence splitting `j = 2` into charts creates no second independent analytic owner. -/
theorem charts_do_not_create_owners {Whole Chart₁ Chart₂ : ℝ → ℝ} {S0 : ℕ}
    (hsum : ∀ x, Whole x = Chart₁ x + Chart₂ x)
    (h₁ : J2ResidualCenteredBound Chart₁ S0) (h₂ : J2ResidualCenteredBound Chart₂ S0) :
    J2ResidualCenteredBound Whole S0 := by
  obtain ⟨C₁, hC₁, hb₁⟩ := h₁
  obtain ⟨C₂, hC₂, hb₂⟩ := h₂
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  calc |Whole x| = |Chart₁ x + Chart₂ x| := by rw [hsum x]
    _ ≤ |Chart₁ x| + |Chart₂ x| := abs_add_le _ _
    _ ≤ C₁ * x / (Real.log x) ^ (S0 + 2) + C₂ * x / (Real.log x) ^ (S0 + 2) :=
        add_le_add (hb₁ x hx) (hb₂ x hx)
    _ = (C₁ + C₂) * x / (Real.log x) ^ (S0 + 2) := by ring

/-- **The `j = 2` algebra does not imply the bound.**  The exact identities above hold for every
source and kernel, yet there is a family violating `J2ResidualCenteredBound`: the analytic owner
is load-bearing and may not be upgraded. -/
theorem j2_algebra_does_not_imply_bound :
    (∀ (s : Finset ℕ) (g K : ℕ → ℝ), dbRaw s g K = dbCentered s g K + dbPrincipal s g K)
      ∧ ∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0 :=
  ⟨dbRaw_eq_centered_add_principal, ⟨fun x => x, identity_not_budgeted 1⟩⟩

end Gate1B.R11.Frontier.CanonicalRootSync
