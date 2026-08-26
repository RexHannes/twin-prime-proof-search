/-
# Gate 1B safe algebra bank — §11: the explicit anti-Cartesian lemma.

A relation `R ⊆ Q × V` is **not** its own Cartesian product of projections.
Summing a function over the shell relation is therefore not the same as summing
it over `π_Q R × π_V R`.

This is the formal guard against the exact mistake that invalidated
`PSQ-SYNC45 PASS`: replacing an on-shell (correlated) double sum by an
independent double sum over the two projections.
-/
import Mathlib

namespace Gate1B

open Finset

/-- **Anti-Cartesian lemma (schema).**  For any two points `(q₁, v₁)`,
`(q₂, v₂)` with `q₁ ≠ q₂` and `v₁ ≠ v₂`, there is an explicit weight `F` whose
sum over the two-point relation differs from its sum over the Cartesian product
of the projections. -/
theorem shell_sum_ne_cartesian_sum {Q V : Type*} [DecidableEq Q] [DecidableEq V]
    (q1 q2 : Q) (v1 v2 : V) (hq : q1 ≠ q2) (hv : v1 ≠ v2) :
    ∃ F : Q → V → ℤ,
      ∑ p ∈ ({(q1, v1), (q2, v2)} : Finset (Q × V)), F p.1 p.2
        ≠ ∑ q ∈ ({q1, q2} : Finset Q), ∑ v ∈ ({v1, v2} : Finset V), F q v := by
  classical
  refine ⟨fun q v => if q = q1 ∧ v = v2 then (1 : ℤ) else 0, ?_⟩
  have hpair : ((q1, v1) : Q × V) ≠ (q2, v2) := by simp [Prod.ext_iff, hq]
  rw [Finset.sum_insert (by simpa using hpair), Finset.sum_singleton,
      Finset.sum_insert (by simpa using hq), Finset.sum_singleton,
      Finset.sum_insert (by simpa using hv), Finset.sum_singleton,
      Finset.sum_insert (by simpa using hv), Finset.sum_singleton]
  simp [hv, Ne.symm hq]

/-- **Anti-Cartesian lemma (explicit numerical instance).**  With
`R = {(0,0), (1,1)} ⊆ ℤ × ℤ` and `F(q, v) = 1` exactly at `(0, 1)`, the shell
sum is `0` while the Cartesian sum is `1`. -/
theorem shell_sum_ne_cartesian_sum_explicit :
    ∑ p ∈ ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ))} : Finset (ℤ × ℤ)),
        (if p.1 = 0 ∧ p.2 = 1 then (1 : ℤ) else 0)
      ≠ ∑ q ∈ ({(0 : ℤ), 1} : Finset ℤ), ∑ v ∈ ({(0 : ℤ), 1} : Finset ℤ),
        (if q = 0 ∧ v = 1 then (1 : ℤ) else 0) := by
  rw [Finset.sum_pair (by norm_num : ((0 : ℤ), (0 : ℤ)) ≠ ((1 : ℤ), (1 : ℤ))),
      Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1),
      Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1),
      Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1)]
  norm_num

/-- The two sums in the explicit instance, evaluated: `0` and `1`. -/
theorem shell_sum_explicit_values :
    (∑ p ∈ ({((0 : ℤ), (0 : ℤ)), ((1 : ℤ), (1 : ℤ))} : Finset (ℤ × ℤ)),
        (if p.1 = 0 ∧ p.2 = 1 then (1 : ℤ) else 0)) = 0 ∧
    (∑ q ∈ ({(0 : ℤ), 1} : Finset ℤ), ∑ v ∈ ({(0 : ℤ), 1} : Finset ℤ),
        (if q = 0 ∧ v = 1 then (1 : ℤ) else 0)) = 1 := by
  constructor
  · rw [Finset.sum_pair (by norm_num : ((0 : ℤ), (0 : ℤ)) ≠ ((1 : ℤ), (1 : ℤ)))]
    norm_num
  · rw [Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1),
        Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1),
        Finset.sum_pair (by norm_num : (0 : ℤ) ≠ 1)]
    norm_num

end Gate1B
