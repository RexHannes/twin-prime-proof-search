import Mathlib

/-!
# Gate 1B · FM722 · **balanced coagulation**: the finite exponent lemma

Pure finite real arithmetic.  No analytic input, no asymptotics.

Given a finite ordered family of *atom exponents* `α_j` with

```
  0 ≤ α_j ≤ σ,      σ < 1/6,      ∑_j α_j = 1 − ρ,      0 ≤ ρ < 1/6,
```

there is a **whole-atom** subfamily `A` — realised literally as the ordered
*first-crossing prefix*, so that **no atom is split** — with

```
  1/3 ≤ α_A < 1/3 + σ < 1/2,
```

and whose complement `C` (the corresponding suffix) satisfies

```
  1/3 < α_C ≤ 2/3.
```

The atom family is encoded as a `List ℝ`, which records the order used by the
first-crossing argument; the subfamily is `L.take k` and its complement is
`L.drop k`, so the split is by whole atoms only.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

/-- One step of the prefix-sum sequence. -/
theorem prefix_sum_step (L : List ℝ) (n : ℕ) :
    (L.take (n + 1)).sum = (L.take n).sum + (L[n]?).getD 0 := by
  rw [List.take_add_one, List.sum_append]
  congr 1
  cases L[n]? <;> simp

/-- Every step of the prefix-sum sequence is at most `σ`. -/
theorem prefix_step_le (L : List ℝ) (n : ℕ) (sigma : ℝ) (hb : ∀ x ∈ L, x ≤ sigma)
    (hs : 0 ≤ sigma) : (L[n]?).getD 0 ≤ sigma := by
  cases h : L[n]? with
  | none => simpa using hs
  | some x =>
      simp only [Option.getD_some]
      exact hb x (List.mem_of_getElem? h)

/-- **FM722-GAMMA-BALANCED-COAGULATION45 (finite exponent lemma).**

The first-crossing prefix `A = L.take k` is a whole-atom subfamily with
`1/3 ≤ α_A < 1/3 + σ`, and its complement satisfies `1/3 < α_C ≤ 2/3`.

The hypothesis `0 ≤ α_j` is part of the source statement and is kept, although
the proof below does not use it: only the upper bounds `α_j ≤ σ`, `σ < 1/6`,
`0 ≤ ρ < 1/6` and the total mass are needed. -/
theorem balanced_coagulation (L : List ℝ) (sigma rho : ℝ)
    (hnonneg : ∀ x ∈ L, 0 ≤ x) (hbound : ∀ x ∈ L, x ≤ sigma)
    (hsigma0 : 0 ≤ sigma) (hsigma : sigma < 1 / 6)
    (hrho0 : 0 ≤ rho) (hrho : rho < 1 / 6)
    (hsum : L.sum = 1 - rho) :
    ∃ k, k ≤ L.length ∧
      1 / 3 ≤ (L.take k).sum ∧ (L.take k).sum < 1 / 3 + sigma ∧
      1 / 3 < (L.drop k).sum ∧ (L.drop k).sum ≤ 2 / 3 := by
  classical
  have hex : ∃ k, 1 / 3 ≤ (L.take k).sum := by
    refine ⟨L.length, ?_⟩
    rw [List.take_length, hsum]
    linarith
  set k := Nat.find hex with hk
  have hPk : 1 / 3 ≤ (L.take k).sum := Nat.find_spec hex
  have hkle : k ≤ L.length := Nat.find_le (by rw [List.take_length, hsum]; linarith)
  have hk0 : k ≠ 0 := by
    intro h
    rw [h] at hPk
    simp at hPk
    linarith
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hprev : ¬ (1 / 3 ≤ (L.take m).sum) := Nat.find_min hex (by omega)
  push_neg at hprev
  have hstep : (L.take k).sum = (L.take m).sum + (L[m]?).getD 0 := by
    rw [hm, prefix_sum_step]
  have hupper : (L.take k).sum < 1 / 3 + sigma := by
    have hle := prefix_step_le L m sigma hbound hsigma0
    rw [hstep]
    linarith
  have hsplit : (L.take k).sum + (L.drop k).sum = L.sum := List.sum_take_add_sum_drop L k
  refine ⟨k, hkle, hPk, hupper, ?_, ?_⟩
  · have : (L.drop k).sum = L.sum - (L.take k).sum := by linarith
    rw [this, hsum]; linarith
  · have : (L.drop k).sum = L.sum - (L.take k).sum := by linarith
    rw [this, hsum]; linarith

/-- The crossing window is strictly below `1/2`. -/
theorem coagulation_window_lt_half (sigma : ℝ) (hsigma : sigma < 1 / 6) :
    1 / 3 + sigma < 1 / 2 := by linarith

end FM722
end CurrentProgramme
end TwinPrimeProject
