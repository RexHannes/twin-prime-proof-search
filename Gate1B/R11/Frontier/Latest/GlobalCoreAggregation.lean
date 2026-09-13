/-
# Gate1B / R11 / Frontier / Latest : exact global-core aggregation

Append-only module.  **Exact finite algebra only**: every statement here is an identity, no
estimate is asserted and no open proposition is inhabited.

The current analytic frontier writes the global core as

```
R_j  =  ∑_M  g(M - 2) · H_j(M)                                    (global core aggregation)
```

and then splits the pair sum over *all gcd classes*.  This module supplies the deterministic
layer for both:

* §1 `globalCore` and its exact linearity / mask / support / reindexing identities;
* §2 the exact **all-gcd-class covariance identity**: any pair sum equals the sum over gcd
  classes of the corresponding coprime-residual sums, with the residual variables genuinely
  coprime (`gcd_class_coprime`);
* §3 the *signed* `(ν, k) → m` reassembly: a divisor double sum equals the single sum over `m`
  of the divisor-reassembled coefficient, symmetric in the two factors.
-/
import Mathlib

namespace Gate1B.R11.Frontier.Latest

open Finset

/-! ## 1. The global core -/

section Core

variable {R : Type*} [CommRing R]

/-- The global core aggregation `R_j = ∑_{M ∈ S} g(M-2) H_j(M)`.  `S` is the finite family of
admissible `M`, `g` the (shifted) source weight and `H` the row profile. -/
def globalCore (S : Finset ℕ) (g H : ℕ → R) : R := ∑ M ∈ S, g (M - 2) * H M

/-- The global core is additive in the row profile: aggregating a finite family of rows is the
same as aggregating each row and summing.  (`R = ∑_j R_j`.) -/
theorem globalCore_sum {ι : Type*} (S : Finset ℕ) (g : ℕ → R) (J : Finset ι) (H : ι → ℕ → R) :
    globalCore S g (fun M => ∑ j ∈ J, H j M) = ∑ j ∈ J, globalCore S g (H j) := by
  unfold globalCore
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun M _ => by rw [Finset.mul_sum]

/-- Additivity of the global core in the source weight. -/
theorem globalCore_add_source (S : Finset ℕ) (g₁ g₂ H : ℕ → R) :
    globalCore S (fun n => g₁ n + g₂ n) H = globalCore S g₁ H + globalCore S g₂ H := by
  unfold globalCore
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun M _ => by ring

/-- **Exact mask split.**  For any decidable mask `p`, the core splits into the masked part and
the rest, with no double charge. -/
theorem globalCore_mask_split (S : Finset ℕ) (g H : ℕ → R) (p : ℕ → Prop) [DecidablePred p] :
    globalCore S g H
      = globalCore (S.filter p) g H + globalCore (S.filter (fun M => ¬ p M)) g H := by
  unfold globalCore
  exact (Finset.sum_filter_add_sum_filter_not S p _).symm

/-- The masked part and the rest are supported on disjoint sets: nothing is charged twice. -/
theorem mask_disjoint (S : Finset ℕ) (p : ℕ → Prop) [DecidablePred p] :
    Disjoint (S.filter p) (S.filter (fun M => ¬ p M)) :=
  Finset.disjoint_filter_filter_not S S p

/-- A row supported off the aggregation family contributes exactly zero. -/
theorem globalCore_eq_zero_of_offSupport (S : Finset ℕ) (g H : ℕ → R)
    (h : ∀ M ∈ S, H M = 0) : globalCore S g H = 0 :=
  Finset.sum_eq_zero fun M hM => by rw [h M hM, mul_zero]

/-- Reindexing the core by the shift `M = m + 2`: the shifted source weight is evaluated at the
plain index. -/
theorem globalCore_shift (T : Finset ℕ) (g H : ℕ → R) :
    globalCore (T.image (fun m => m + 2)) g H = ∑ m ∈ T, g m * H (m + 2) := by
  unfold globalCore
  rw [Finset.sum_image (by intro a _ b _ h; simpa using h)]
  exact Finset.sum_congr rfl fun m _ => by norm_num

end Core

/-! ## 2. The exact all-gcd-class covariance identity -/

section GcdClass

variable {R : Type*} [CommRing R]

/-- **All-gcd-class covariance identity.**  Any finite pair sum decomposes exactly into the sum
over gcd classes, provided the class list `G` contains every occurring gcd. -/
theorem sum_pairs_by_gcd (s : Finset (ℕ × ℕ)) (G : Finset ℕ)
    (hG : ∀ q ∈ s, Nat.gcd q.1 q.2 ∈ G) (F : ℕ × ℕ → R) :
    ∑ q ∈ s, F q = ∑ d ∈ G, ∑ q ∈ s.filter (fun q => Nat.gcd q.1 q.2 = d), F q :=
  (Finset.sum_fiberwise_of_maps_to hG F).symm

/-- Inside a gcd class the residual variables really are coprime: if `gcd q₁ q₂ = d` with
`d ≠ 0` then `q₁ = d q₁'`, `q₂ = d q₂'` with `gcd q₁' q₂' = 1`. -/
theorem gcd_class_coprime {a b d : ℕ} (hd : d ≠ 0) (h : Nat.gcd a b = d) :
    ∃ a' b' : ℕ, a = d * a' ∧ b = d * b' ∧ Nat.Coprime a' b' := by
  refine ⟨a / d, b / d, ?_, ?_, ?_⟩
  · exact (Nat.mul_div_cancel' (h ▸ Nat.gcd_dvd_left a b)).symm
  · exact (Nat.mul_div_cancel' (h ▸ Nat.gcd_dvd_right a b)).symm
  · have := Nat.coprime_div_gcd_div_gcd (m := a) (n := b) (by rw [h]; exact Nat.pos_of_ne_zero hd)
    simpa [h] using this

/-- The gcd classes of a coprime-restricted pair family reduce exactly to the class `d = 1`. -/
theorem coprime_pairs_gcd_class (s : Finset (ℕ × ℕ)) (F : ℕ × ℕ → R)
    (hs : ∀ q ∈ s, Nat.Coprime q.1 q.2) :
    ∑ q ∈ s, F q = ∑ d ∈ ({1} : Finset ℕ), ∑ q ∈ s.filter (fun q => Nat.gcd q.1 q.2 = d), F q :=
  sum_pairs_by_gcd s _ (fun q hq => by simpa using hs q hq) F

end GcdClass

/-! ## 3. The signed `(ν, k) → m` reassembly -/

section Reassembly

variable {R : Type*} [CommRing R]

/-- The reassembled coefficient of `m` is symmetric under swapping the two factors of the
factorisation `m = ν k`: this is the exact `(ν,k) → m` signed reassembly. -/
theorem nuk_reassembly_symm {m : ℕ} (hm : m ≠ 0) (c : ℕ → ℕ → R) :
    ∑ nu ∈ m.divisors, c nu (m / nu) = ∑ k ∈ m.divisors, c (m / k) k := by
  rw [← Nat.sum_div_divisors m (fun nu => c nu (m / nu))]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Nat.mem_divisors.mp hk
  rw [Nat.div_div_self hk'.1 hm]

/-- Aggregating the reassembled coefficients over `m | n` is the same as summing the coefficient
over all factorisations `ν k | n`. -/
theorem sum_reassembled_eq_sum_divisorsAntidiagonal (n : ℕ) (c : ℕ → ℕ → R) :
    ∑ m ∈ n.divisors, ∑ p ∈ m.divisorsAntidiagonal, c p.1 p.2
      = ∑ m ∈ n.divisors, ∑ nu ∈ m.divisors, c nu (m / nu) :=
  Finset.sum_congr rfl fun m _ => Nat.sum_divisorsAntidiagonal (f := c) (n := m)

end Reassembly

end Gate1B.R11.Frontier.Latest
