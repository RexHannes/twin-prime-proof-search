/-
# Gate1B / R11 : long-Möbius divisor reindexing (§9)

The long (`d > U`) Möbius–log tail rewritten through the divisor involution `k = N/d`.
Everything here is exact and pointwise; no asymptotic bound is encoded in these statements.
-/
import Gate1B.R11.MobiusLogSplit

namespace Gate1B.R11

open Finset ArithmeticFunction

variable {N U : ℕ}

/-! ## 1. The divisor involution -/

/-- The divisor involution `d ↦ N/d` maps the long divisors `{d ∣ N : d > U}` bijectively
onto the complementary set `{k ∣ N : N/k > U}`, and is its own inverse there. -/
theorem divisor_involution_bijOn (hN : N ≠ 0) (U : ℕ) :
    Set.BijOn (fun d => N / d) ↑(N.divisors.filter fun d => U < d)
      ↑(N.divisors.filter fun k => U < N / k) := by
  have hmaps : ∀ a ∈ N.divisors.filter (fun d => U < d),
      N / a ∈ N.divisors.filter fun k => U < N / k := by
    intro a ha
    simp only [Finset.mem_filter, Nat.mem_divisors] at ha ⊢
    refine ⟨⟨Nat.div_dvd_of_dvd ha.1.1, hN⟩, ?_⟩
    rw [Nat.div_div_self ha.1.1 hN]
    exact ha.2
  have hmaps' : ∀ a ∈ N.divisors.filter (fun k => U < N / k),
      N / a ∈ N.divisors.filter fun d => U < d := by
    intro a ha
    simp only [Finset.mem_filter, Nat.mem_divisors] at ha ⊢
    exact ⟨⟨Nat.div_dvd_of_dvd ha.1.1, hN⟩, ha.2⟩
  have hinv : ∀ a ∈ N.divisors.filter (fun d => U < d), N / (N / a) = a := by
    intro a ha
    simp only [Finset.mem_filter, Nat.mem_divisors] at ha
    exact Nat.div_div_self ha.1.1 hN
  have hinv' : ∀ a ∈ N.divisors.filter (fun k => U < N / k), N / (N / a) = a := by
    intro a ha
    simp only [Finset.mem_filter, Nat.mem_divisors] at ha
    exact Nat.div_div_self ha.1.1 hN
  refine ⟨fun a ha => hmaps a ha, ?_, fun b hb => ⟨N / b, hmaps' b hb, hinv' b hb⟩⟩
  intro a ha b hb hab
  have ha' : a ∈ N.divisors.filter fun d => U < d := by simpa using ha
  have hb' : b ∈ N.divisors.filter fun d => U < d := by simpa using hb
  calc a = N / (N / a) := (hinv a ha').symm
    _ = N / (N / b) := by rw [show N / a = N / b from hab]
    _ = b := hinv b hb'

/-- General reindexing of a divisor sum along the involution `k = N/d`. -/
theorem sum_long_divisors_reindex (hN : N ≠ 0) (f : ℕ → ℕ → ℝ) :
    ∑ d ∈ N.divisors.filter (fun d => U < d), f d (N / d)
      = ∑ k ∈ N.divisors.filter (fun k => U < N / k), f (N / k) k := by
  refine Finset.sum_nbij' (fun d => N / d) (fun k => N / k) ?_ ?_ ?_ ?_ ?_ <;>
    intro a ha <;> simp only [Finset.mem_filter, Nat.mem_divisors] at ha ⊢
  · refine ⟨⟨Nat.div_dvd_of_dvd ha.1.1, hN⟩, ?_⟩
    rw [Nat.div_div_self ha.1.1 hN]
    exact ha.2
  · exact ⟨⟨Nat.div_dvd_of_dvd ha.1.1, hN⟩, ha.2⟩
  · exact Nat.div_div_self ha.1.1 hN
  · exact Nat.div_div_self ha.1.1 hN
  · rw [Nat.div_div_self ha.1.1 hN]

/-! ## 2. Long-Möbius reindexing -/

/-- **Long-Möbius divisor reindexing.**  Exact pointwise identity
`∑_{d ∣ N, d > U} μ(d) log(N/d) = ∑_{k ∣ N, N/k > U} μ(N/k) log k`. -/
theorem longMobiusLog_reindex (hN : N ≠ 0) (U : ℕ) :
    longMobiusLog U N
      = ∑ k ∈ N.divisors.filter (fun k => U < N / k),
          (moebius (N / k) : ℝ) * Real.log (k : ℝ) := by
  rw [longMobiusLog]
  exact sum_long_divisors_reindex hN
    (fun a b => ((moebius a : ℤ) : ℝ) * Real.log (b : ℝ))

/-- The `k = 1` term of the reindexed sum vanishes, because `log 1 = 0`. -/
theorem reindexed_term_one_eq_zero :
    (moebius (N / 1) : ℝ) * Real.log ((1 : ℕ) : ℝ) = 0 := by simp

/-! ## 3. Parity bookkeeping for odd arguments -/

/-- For odd `N`, both a divisor and its complementary divisor are odd. -/
theorem odd_divisor_and_complement (hN : Odd N) {d : ℕ} (hd : d ∣ N) :
    Odd d ∧ Odd (N / d) :=
  ⟨odd_of_dvd_odd hN hd, odd_of_dvd_odd hN (Nat.div_dvd_of_dvd hd)⟩

/-! ## 4. Generic finitely supported weight -/

/-- **Weighted long-Möbius reindexing.**  For an arbitrary finitely supported weight `Omega`
and the fixed shift `2`, the long tail of the Möbius–log expansion of `Λ(n+2)` is exactly
the complementary-divisor reindexed sum.  Nothing is averaged over the shift. -/
theorem weighted_longMobius_reindex (s : Finset ℕ) (Omega : ℕ → ℝ) (U : ℕ) :
    ∑ n ∈ s, Omega n * longMobiusLog U (n + 2)
      = ∑ n ∈ s, Omega n * ∑ k ∈ (n + 2).divisors.filter (fun k => U < (n + 2) / k),
          (moebius ((n + 2) / k) : ℝ) * Real.log (k : ℝ) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [longMobiusLog_reindex (by omega) U]

end Gate1B.R11
