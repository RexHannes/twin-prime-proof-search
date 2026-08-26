import RequestProject.NANC.Gate01Switch.Lambda3

/-!
# Gate01Switch: the switched operator SW0 and the exact reindexing SW0 → SW1

`SW0`:  `S_sw = ∑_{q ∈ Qset} λ₃(U,V;q) · Δ_{c,E}(q;-2)`.

`SW1`:  the same sum with the inner progression reindexed by the multiplier
`r = (n+2)/q`:

`∑_{n ≤ K, q ∣ n+2} c n = ∑_{r ≥ 1, 2 ≤ qr ≤ K+2} c (qr - 2)`.

Everything here is an exact finite identity; no analytic normalization is
introduced.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open Finset

/-- **(SW0)** — the finite switched operator. -/
noncomputable def switchedOperator (Qset : Finset ℕ) (U V K : ℕ) (c E : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Qset, lambda3 U V q * discrMinusTwo K q c E

/-- `B_q = {r ≥ 1 : 2 ≤ q r ≤ K + 2}`, as an explicit `Finset`. -/
def multiplierSet (K q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (K + 2)).filter (fun r => 2 ≤ q * r ∧ q * r ≤ K + 2)

theorem mem_multiplierSet {K q r : ℕ} (hq : 0 < q) :
    r ∈ multiplierSet K q ↔ 1 ≤ r ∧ 2 ≤ q * r ∧ q * r ≤ K + 2 := by
  simp only [multiplierSet, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, -⟩, h2, h3⟩; exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have : r ≤ q * r := Nat.le_mul_of_pos_left r hq
    exact ⟨⟨h1, by omega⟩, h2, h3⟩

/-- **(RI)** — the exact reindexing of the residue-`-2` progression by the
multiplier `r = (n+2)/q`. -/
theorem sum_residueMinusTwo_eq_sum_multiplier {K q : ℕ} (hq : 0 < q) (c : ℕ → ℝ) :
    ∑ n ∈ residueMinusTwoSet K q, c n = ∑ r ∈ multiplierSet K q, c (q * r - 2) := by
  refine Finset.sum_nbij' (fun n => (n + 2) / q) (fun r => q * r - 2) ?_ ?_ ?_ ?_ ?_
  · intro n hn
    rw [mem_residueMinusTwoSet] at hn
    obtain ⟨hnK, hdvd⟩ := hn
    have hmul : q * ((n + 2) / q) = n + 2 := Nat.mul_div_cancel' hdvd
    refine (mem_multiplierSet hq).mpr ⟨?_, by rw [hmul]; omega, by rw [hmul]; omega⟩
    rcases Nat.eq_zero_or_pos ((n + 2) / q) with h | h
    · rw [h, Nat.mul_zero] at hmul; omega
    · exact h
  · intro r hr
    rw [mem_multiplierSet hq] at hr
    obtain ⟨-, h2, h3⟩ := hr
    refine mem_residueMinusTwoSet.mpr ⟨Nat.sub_le_of_le_add h3, ?_⟩
    rw [Nat.sub_add_cancel h2]
    exact Dvd.intro r rfl
  · intro n hn
    rw [mem_residueMinusTwoSet] at hn
    have hmul : q * ((n + 2) / q) = n + 2 := Nat.mul_div_cancel' hn.2
    show q * ((n + 2) / q) - 2 = n
    rw [hmul]
    omega
  · intro r hr
    rw [mem_multiplierSet hq] at hr
    obtain ⟨-, h2, -⟩ := hr
    show (q * r - 2 + 2) / q = r
    rw [Nat.sub_add_cancel h2, Nat.mul_div_cancel_left _ hq]
  · intro n hn
    rw [mem_residueMinusTwoSet] at hn
    have hmul : q * ((n + 2) / q) = n + 2 := Nat.mul_div_cancel' hn.2
    show c n = c (q * ((n + 2) / q) - 2)
    rw [hmul]
    norm_num

/-- The switched discrepancy in multiplier coordinates. -/
theorem discrMinusTwo_eq_multiplier {K q : ℕ} (hq : 0 < q) (c E : ℕ → ℝ) :
    discrMinusTwo K q c E = (∑ r ∈ multiplierSet K q, c (q * r - 2)) - E q := by
  rw [discrMinusTwo, sum_residueMinusTwo_eq_sum_multiplier hq c]

/-- **(SW1)** — the switched operator in multiplier coordinates.  Exact
equality, not an asymptotic. -/
theorem switchedOperator_eq_multiplier {Qset : Finset ℕ} (U V K : ℕ) (c E : ℕ → ℝ)
    (hQ : ∀ q ∈ Qset, 0 < q) :
    switchedOperator Qset U V K c E =
      ∑ q ∈ Qset, lambda3 U V q * ((∑ r ∈ multiplierSet K q, c (q * r - 2)) - E q) := by
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [discrMinusTwo_eq_multiplier (hQ q hq)]

end Gate01Switch
end TwinPrimeProject
