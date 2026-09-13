/-
# Gate1B / R11 / Frontier / Latest : the D2 positive `p | v` branch as a first-class owner

Append-only module.  **Exact algebra and explicit firewalls only.**  The analytic estimate for
this sector is *not* claimed: it is isolated as the never-inhabited proposition
`PositiveBranchMomentBound`.

Contents:

* §1 the sector object `PositiveBranchSector`, carrying the frozen data `(c, p, ν, d)` and the
  retained range;
* §2 the exact facts: `v = p w` (reindexing) and exact `χ(p)` cancellation, both imported from
  `RamanujanKernel`;
* §3 the **capacity firewall**: freezing `p` creates the period `c p ν d`; if the retained range
  is shorter than that period, the complete-period (negative-branch) argument is unavailable —
  proved by an explicit periodic countermodel, not assumed;
* §4 the **source-valid alternative coordinate**, in which `p` is not frozen but remains a
  prime-divisor summation variable;
* §5 the open analytic node `PositiveBranchMomentBound`, together with the proof that the
  deterministic identities of §2 and §4 cannot by themselves imply any bound (they hold for
  arbitrarily large sources).
-/
import Gate1B.R11.Frontier.Latest.RamanujanKernel

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. The sector object -/

/-- The D2 positive `p | v` sector: the frozen auxiliary data `(c, ν, d)`, the prime `p`, and the
length of the retained range in which the residue variable actually moves. -/
structure PositiveBranchSector where
  /-- The frozen prime. -/
  p : ℕ
  /-- The auxiliary conductor factor. -/
  c : ℕ
  /-- The auxiliary source modulus. -/
  nu : ℕ
  /-- The auxiliary denominator. -/
  d : ℕ
  /-- The length of the retained range of the residue variable. -/
  rangeLen : ℕ
  /-- The prime is a prime. -/
  p_prime : p.Prime
  /-- The auxiliary data are positive. -/
  c_pos : 0 < c
  /-- The auxiliary data are positive. -/
  nu_pos : 0 < nu
  /-- The auxiliary data are positive. -/
  d_pos : 0 < d

/-- The period seen by the residue variable once `p` is frozen. -/
def PositiveBranchSector.period (S : PositiveBranchSector) : ℕ :=
  frozenPeriod S.c S.p S.nu S.d

/-- Freezing `p` never shortens the period. -/
theorem PositiveBranchSector.p_le_period (S : PositiveBranchSector) : S.p ≤ S.period :=
  frozenPeriod_ge S.c_pos S.nu_pos S.d_pos

/-! ## 2. The exact facts of the branch -/

/-- On the positive branch the summation variable factors exactly as `v = p w`. -/
theorem positive_branch_reindex {M : Type*} [AddCommMonoid M] (S : PositiveBranchSector)
    (t : ℕ) (F : ℕ → M) :
    ∑ v ∈ (range (S.p * t)).filter (fun v => S.p ∣ v), F v = ∑ w ∈ range t, F (S.p * w) :=
  sum_positive_branch S.p_prime.pos t F

/-- On the positive branch the outer `χ(p)` cancels the conjugate `χ(p)` exactly. -/
theorem positive_branch_chi_cancels {n : ℕ} [NeZero n] (χ : DirichletCharacter ℂ n)
    {a : ZMod n} (ha : IsUnit a) : χ a * (starRingEnd ℂ) (χ a) = 1 :=
  chi_p_cancels χ ha

/-! ## 3. The capacity firewall -/

/-- **Capacity firewall for the frozen-`p` coordinate.**  If the retained range is shorter than
the frozen period, no cancellation follows from periodicity: there is a function with exactly
that period, mean zero over a full period, whose sum over the retained range is `1`.  Hence the
complete-period argument that closes the negative branch is *not available* here. -/
theorem positive_branch_complete_period_unavailable (S : PositiveBranchSector)
    (hlen : 0 < S.rangeLen) (hshort : S.rangeLen < S.period) :
    ∃ f : ℕ → ℤ,
      (∀ v, f (v + S.period) = f v) ∧
      (∑ v ∈ range S.period, f v) = 0 ∧
      (∑ v ∈ range S.rangeLen, f v) ≠ 0 :=
  partial_period_sum_not_forced_zero hlen hshort

/-- The exponent form used at the frontier: a frozen period of exponent `a ∈ [0.69, 0.711]`
strictly exceeds a retained range of any smaller exponent `b`, and is itself at most the upper
endpoint of the frontier's window. -/
theorem positive_branch_exponent_gap {x a b : ℝ} (hx : 1 < x)
    (ha : (0.69 : ℝ) ≤ a) (ha' : a ≤ 0.711) (hb : b < 0.69) :
    x ^ b < x ^ a ∧ x ^ a ≤ x ^ (0.711 : ℝ) :=
  ⟨range_shorter_than_period_of_exponent hx (lt_of_lt_of_le hb ha),
    Real.rpow_le_rpow_of_exponent_le hx.le ha'⟩

/-! ## 4. The source-valid alternative coordinate -/

/-- **The alternative coordinate.**  Instead of freezing `p`, keep it as a prime-divisor
summation variable: the sector sum is then an exact double count with no composite period. -/
theorem positive_branch_prime_divisor_coordinate {M : Type*} [AddCommMonoid M] (Sset P : Finset ℕ)
    (F : ℕ → ℕ → M) :
    ∑ p ∈ P, ∑ v ∈ Sset.filter (fun v => p ∣ v), F p v
      = ∑ v ∈ Sset, ∑ p ∈ P.filter (fun p => p ∣ v), F p v :=
  sum_over_prime_divisor_coordinate Sset P F

/-! ## 5. The open node -/

/-- **The open analytic node of the positive branch**: the zero/source moment of the D2 nonunit
positive `p | v` sector is smaller than `x (log x)^{−B}`.  Never inhabited. -/
def PositiveBranchMomentBound (sector : ℝ → ℝ) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → |sector x| ≤ C * x * (Real.log x) ^ (-B)

/-- **The identities are not an estimate.**  The exact reindexings of §2 and §4 hold for every
source whatsoever, in particular for sources of arbitrarily large mass; so no bound on the
sector follows from them.  The analytic node of §5 is genuinely load-bearing. -/
theorem positive_branch_identities_do_not_bound (target : ℝ) :
    ∃ (Sset P : Finset ℕ) (F : ℕ → ℕ → ℝ),
      (∑ p ∈ P, ∑ v ∈ Sset.filter (fun v => p ∣ v), F p v
        = ∑ v ∈ Sset, ∑ p ∈ P.filter (fun p => p ∣ v), F p v)
      ∧ target < ∑ v ∈ Sset, ∑ p ∈ P.filter (fun p => p ∣ v), F p v := by
  refine ⟨{2}, {2}, fun _ _ => |target| + 1, sum_over_prime_divisor_coordinate _ _ _, ?_⟩
  have : ∑ v ∈ ({2} : Finset ℕ), ∑ _p ∈ ({2} : Finset ℕ).filter (fun p => p ∣ v),
      (|target| + 1) = |target| + 1 := by norm_num [Finset.filter_singleton]
  rw [this]
  have := le_abs_self target
  linarith

end Gate1B.R11.Frontier.Latest
