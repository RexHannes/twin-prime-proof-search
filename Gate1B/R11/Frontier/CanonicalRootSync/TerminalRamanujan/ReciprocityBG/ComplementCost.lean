/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the complement-assembly cost  (B5)

Append-only module.  Exact finite counting plus one genuinely kernel-proved harmonic
inequality; **no asymptotic theorem is invented** and nothing pre-existing is edited.

* §1  exact allocation counting: the allocation index set of `MobiusProvenance.lean` has
  cardinality `τ(a₀) τ(u)`, which for `(a₀,u) = 1` is `d₂(a₀u)`;
* §2  the harmonic ingredients, kernel-proved:
  `∑_{m ≤ R} d₂(m)/m ≤ (∑_{m ≤ R} 1/m)²` and `∑_{m ≤ R} 1/m ≤ 1 + log R`;
* §3  the named budget `ComplementAssemblyBudget` and the theorem deriving it from the exact
  allocation splitting bound `#alloc(Hm) ≤ d₂(H) d₂(m)`:

  ```
  ∑_{m ≤ R} #alloc(Hm)/(Hm)  ≤  (d₂(H)/H) (1 + log R)² .
  ```

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.MobiusProvenance

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Finset

/-! ## 1. Exact allocation counting -/

/-- `d₂(n)`: the number of ordered factorisations `n = a b`. -/
def d2 (n : ℕ) : ℕ := n.divisorsAntidiagonal.card

/-- The number of allocations of the complement `(a₀, u)`: pairs `(d, x)` with `d ∣ a₀`,
`x ∣ u`, i.e. the index set of `allocSum`. -/
def allocCount (a0 u : ℕ) : ℕ := (a0.divisors ×ˢ u.divisors).card

/-- **Exact allocation count**: `#alloc(a₀,u) = τ(a₀) τ(u)`. -/
theorem allocCount_eq_mul (a0 u : ℕ) :
    allocCount a0 u = a0.divisors.card * u.divisors.card :=
  Finset.card_product _ _

/-- `d₂(n) = τ(n)` for `n ≠ 0`: the ordered factorisations are indexed by the divisors. -/
theorem d2_eq_card_divisors {n : ℕ} (hn : n ≠ 0) : d2 n = n.divisors.card := by
  unfold d2
  refine Finset.card_bij' (fun p _ => p.1) (fun X _ => (X, n / X)) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    exact Nat.mem_divisors.mpr ⟨⟨p.2, hp.1.symm⟩, hn⟩
  · intro X hX
    rw [Nat.mem_divisors] at hX
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨Nat.mul_div_cancel' hX.1, hn⟩
  · intro p hp
    rw [Nat.mem_divisorsAntidiagonal] at hp
    have hp1 : 0 < p.1 := by
      rcases Nat.eq_zero_or_pos p.1 with h | h
      · exact absurd hp.1 (by rw [h]; simpa using fun hc => hn hc.symm)
      · exact h
    have hq : n / p.1 = p.2 := by rw [← hp.1, Nat.mul_div_cancel_left p.2 hp1]
    show (p.1, n / p.1) = p
    rw [hq]
  · intro X _
    rfl

/-- **The allocation count is a `d₂`-value**: for `(a₀,u) = 1` the complement `a₀u` has exactly
`#alloc(a₀,u)` allocations. -/
theorem allocCount_eq_d2 {a0 u : ℕ} (hco : Nat.Coprime a0 u) (ha0 : a0 ≠ 0) (hu : u ≠ 0) :
    allocCount a0 u = d2 (a0 * u) := by
  rw [allocCount_eq_mul, d2_eq_card_divisors (mul_ne_zero ha0 hu), hco.card_divisors_mul]

/-! ## 2. The harmonic ingredients -/

/-- The finite harmonic sum `∑_{m ≤ R} 1/m`. -/
noncomputable def harmR (R : ℕ) : ℝ := ∑ m ∈ Finset.Icc 1 R, (1 : ℝ) / (m : ℝ)

theorem harmR_nonneg (R : ℕ) : 0 ≤ harmR R :=
  Finset.sum_nonneg fun m _ => by positivity

/-- `∑_{m ≤ R} 1/m ≤ 1 + log R`, from the Mathlib harmonic-number bound. -/
theorem harmR_le_one_add_log (R : ℕ) : harmR R ≤ 1 + Real.log R := by
  have h : ((harmonic R : ℚ) : ℝ) ≤ 1 + Real.log R := harmonic_le_one_add_log R
  have heq : ((harmonic R : ℚ) : ℝ) = harmR R := by
    rw [harmonic_eq_sum_Icc, harmR]
    push_cast
    exact Finset.sum_congr rfl fun m _ => by rw [one_div]
  rwa [heq] at h

/-- **The divisor-pair harmonic inequality** `∑_{m ≤ R} d₂(m)/m ≤ (∑_{m ≤ R} 1/m)²`, proved by
expanding `d₂` into ordered factorisations and enlarging the range to the full square. -/
theorem sum_d2_div_le_harmR_sq (R : ℕ) :
    ∑ m ∈ Finset.Icc 1 R, (d2 m : ℝ) / (m : ℝ) ≤ (harmR R) ^ 2 := by
  classical
  set S : Finset (ℕ × ℕ) :=
    (Finset.Icc 1 R ×ˢ Finset.Icc 1 R).filter (fun p => p.1 * p.2 ≤ R) with hS
  have hmaps : ∀ p ∈ S, p.1 * p.2 ∈ Finset.Icc 1 R := by
    intro p hp
    rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    rw [Finset.mem_Icc]
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)), hp.2⟩
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps (fun p => (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ))
  have hfiber : ∀ m ∈ Finset.Icc 1 R,
      (S.filter (fun p => p.1 * p.2 = m)) = m.divisorsAntidiagonal := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    ext p
    rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
      Finset.mem_Icc, Nat.mem_divisorsAntidiagonal]
    constructor
    · rintro ⟨-, hpm⟩
      exact ⟨hpm, by omega⟩
    · rintro ⟨hpm, hm0⟩
      have hp1 : 1 ≤ p.1 := by
        rcases Nat.eq_zero_or_pos p.1 with h | h
        · exact absurd hpm (by rw [h]; simpa using fun hc => hm0 hc.symm)
        · exact h
      have hp2 : 1 ≤ p.2 := by
        rcases Nat.eq_zero_or_pos p.2 with h | h
        · exact absurd hpm (by rw [h]; simpa using fun hc => hm0 hc.symm)
        · exact h
      have hb1 : p.1 ≤ R := by
        have : p.1 ≤ p.1 * p.2 := Nat.le_mul_of_pos_right _ hp2
        omega
      have hb2 : p.2 ≤ R := by
        have : p.2 ≤ p.1 * p.2 := Nat.le_mul_of_pos_left _ hp1
        omega
      exact ⟨⟨⟨⟨hp1, hb1⟩, hp2, hb2⟩, by omega⟩, hpm⟩
  have hleft : ∑ m ∈ Finset.Icc 1 R, (d2 m : ℝ) / (m : ℝ) = ∑ p ∈ S, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) := by
    rw [← hfib]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [hfiber m hm]
    have hm0 : m ≠ 0 := by
      rw [Finset.mem_Icc] at hm; omega
    have : ∀ p ∈ m.divisorsAntidiagonal, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) = 1 / (m : ℝ) := by
      intro p hp
      rw [Nat.mem_divisorsAntidiagonal] at hp
      rw [hp.1]
    rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, d2]
    ring
  have hsubset : S ⊆ Finset.Icc 1 R ×ˢ Finset.Icc 1 R := Finset.filter_subset _ _
  have hle : ∑ p ∈ S, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)
      ≤ ∑ p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun p _ _ => by positivity)
  have hsq : ∑ p ∈ Finset.Icc 1 R ×ˢ Finset.Icc 1 R, (1 : ℝ) / ((p.1 * p.2 : ℕ) : ℝ)
      = (harmR R) ^ 2 := by
    rw [Finset.sum_product, harmR, sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    push_cast
    rw [div_mul_div_comm, one_mul]
  rw [hleft]
  exact hle.trans (le_of_eq hsq)

/-! ## 3. The named complement-assembly budget -/

/-- **`ComplementAssemblyBudget`** — the finite complement-assembly cost inequality
`∑_{m ≤ R} #alloc(Hm)/(Hm) ≤ (d₂(H)/H)(1 + log R)²`. -/
def ComplementAssemblyBudget (cnt : ℕ → ℕ) (H R : ℕ) : Prop :=
  ∑ m ∈ Finset.Icc 1 R, (cnt (H * m) : ℝ) / ((H * m : ℕ) : ℝ)
    ≤ (d2 H : ℝ) / (H : ℝ) * (1 + Real.log R) ^ 2

/-- **The complement-assembly budget from the exact allocation splitting bound.**  If the
allocation count of `Hm` splits as `#alloc(Hm) ≤ d₂(H) d₂(m)`, then the assembly cost obeys the
budget.  The only analytic input is the harmonic bound `∑_{m≤R} 1/m ≤ 1 + log R`, itself
kernel-proved. -/
theorem complementAssemblyBudget_of_split {cnt : ℕ → ℕ} {H R : ℕ} (hH : 0 < H)
    (hsplit : ∀ m ∈ Finset.Icc 1 R, cnt (H * m) ≤ d2 H * d2 m) :
    ComplementAssemblyBudget cnt H R := by
  have hH0 : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH
  have hstep1 : ∑ m ∈ Finset.Icc 1 R, (cnt (H * m) : ℝ) / ((H * m : ℕ) : ℝ)
      ≤ ∑ m ∈ Finset.Icc 1 R, (d2 H : ℝ) / (H : ℝ) * ((d2 m : ℝ) / (m : ℝ)) := by
    refine Finset.sum_le_sum fun m hm => ?_
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm1
    have hcast : ((H * m : ℕ) : ℝ) = (H : ℝ) * (m : ℝ) := by push_cast; ring
    have hnum : (cnt (H * m) : ℝ) ≤ (d2 H : ℝ) * (d2 m : ℝ) := by
      exact_mod_cast hsplit m hm
    have hden : (0 : ℝ) < (H : ℝ) * (m : ℝ) := by positivity
    rw [hcast, div_mul_div_comm]
    exact (div_le_div_iff_of_pos_right hden).mpr hnum
  have hstep2 : ∑ m ∈ Finset.Icc 1 R, (d2 H : ℝ) / (H : ℝ) * ((d2 m : ℝ) / (m : ℝ))
      = (d2 H : ℝ) / (H : ℝ) * ∑ m ∈ Finset.Icc 1 R, (d2 m : ℝ) / (m : ℝ) :=
    (Finset.mul_sum _ _ _).symm
  have hfac : (0 : ℝ) ≤ (d2 H : ℝ) / (H : ℝ) := by positivity
  have hlog : (harmR R) ^ 2 ≤ (1 + Real.log R) ^ 2 := by
    have h1 := harmR_nonneg R
    have h2 := harmR_le_one_add_log R
    nlinarith
  calc ∑ m ∈ Finset.Icc 1 R, (cnt (H * m) : ℝ) / ((H * m : ℕ) : ℝ)
      ≤ (d2 H : ℝ) / (H : ℝ) * ∑ m ∈ Finset.Icc 1 R, (d2 m : ℝ) / (m : ℝ) := by
        rw [← hstep2]; exact hstep1
    _ ≤ (d2 H : ℝ) / (H : ℝ) * (harmR R) ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_d2_div_le_harmR_sq R) hfac
    _ ≤ (d2 H : ℝ) / (H : ℝ) * (1 + Real.log R) ^ 2 :=
        mul_le_mul_of_nonneg_left hlog hfac

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
