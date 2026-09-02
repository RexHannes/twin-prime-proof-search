/-
# Universal / D0WP — finite packet compilers

**Status of this module: KERNEL_PROVED finite algebra.**

These are the only "compiler" lemmas used by the conditional RUN1B / ULTRA /
OTHER45 / HSTAR layers.  They are pure finite statements: a finite sum of
provider-eligible packets is bounded by the number of packets times the packet
bound, and a finite family partitioned by an owner map decomposes exactly once
(no analytic saving is spent twice).

No analytic estimate is proved here, and no analytic estimate is a field of any
structure in this module.
-/
import Mathlib

namespace Universal.D0WP

open Finset

/-- **Finite packet compiler (kernel-proved).**  A finite sum of packets, each
bounded by `B`, is bounded by `card · B`. -/
theorem finite_packet_bound {ι : Type*} (s : Finset ι) (f : ι → ℂ) (B : ℝ)
    (hb : ∀ i ∈ s, ‖f i‖ ≤ B) : ‖∑ i ∈ s, f i‖ ≤ (s.card : ℝ) * B := by
  calc ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
    _ ≤ ∑ _i ∈ s, B := Finset.sum_le_sum hb
    _ = (s.card : ℝ) * B := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- **Owner decomposition (kernel-proved).**  A finite family decomposes exactly
once along its owner map: every row belongs to exactly one owner class, and the
total is the sum of the owner totals. -/
theorem owner_decomposition {ι κ : Type*} [DecidableEq κ] [Fintype κ] [DecidableEq ι]
    (s : Finset ι) (owner : ι → κ) (f : ι → ℂ) :
    ∑ i ∈ s, f i = ∑ k : κ, ∑ i ∈ s.filter (fun i => owner i = k), f i :=
  (Finset.sum_fiberwise s owner f).symm

/-- **No double spending (kernel-proved).**  Distinct owner classes have
disjoint row sets. -/
theorem owner_classes_disjoint {ι κ : Type*} [DecidableEq κ] [DecidableEq ι]
    (s : Finset ι) (owner : ι → κ) {k k' : κ} (h : k ≠ k') :
    Disjoint (s.filter (fun i => owner i = k)) (s.filter (fun i => owner i = k')) := by
  refine Finset.disjoint_filter.2 ?_
  intro i _ hk hk'
  exact h (hk ▸ hk')

/-- Owner-wise bound assembly (kernel-proved). -/
theorem owner_bound_assembly {ι κ : Type*} [DecidableEq κ] [Fintype κ] [DecidableEq ι]
    (s : Finset ι) (owner : ι → κ) (f : ι → ℂ) (B : κ → ℝ)
    (hB : ∀ k : κ, ‖∑ i ∈ s.filter (fun i => owner i = k), f i‖ ≤ B k) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ k : κ, B k := by
  rw [owner_decomposition s owner f]
  calc ‖∑ k : κ, ∑ i ∈ s.filter (fun i => owner i = k), f i‖
      ≤ ∑ k : κ, ‖∑ i ∈ s.filter (fun i => owner i = k), f i‖ := norm_sum_le _ _
    _ ≤ ∑ k : κ, B k := Finset.sum_le_sum (fun k _ => hB k)

end Universal.D0WP
