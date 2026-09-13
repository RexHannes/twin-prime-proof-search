/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the truncated Möbius
coefficient  (T1)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

This is the bottom layer of the terminal-Ramanujan route.  It formalises the **actual**
truncated coefficient

```
λ(d) = ∑_{u v = d, u ∈ I₁, v ∈ I₂, u, v odd} μ(u) μ(v),
```

with the two sharp cutoffs `I₁ = (A₁, B₁]`, `I₂ = (A₂, B₂]` carried explicitly in *every*
statement (they are fields of the `Cutoffs` structure that every definition takes as its first
argument).  It is **not** replaced by the unrestricted convolution `μ * μ`; §3 contains the
kernel-checked proof that the two differ.

§4 contains the elementary **firewall**: assembled linear coefficients may cancel before
squaring, so a norm bound for an assembled cutoff does *not* imply the corresponding packetwise
norm bound.  A tiny finite counterexample is given, and it is kernel-checkable.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Mathlib

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset ArithmeticFunction

/-! ## 1. The two sharp cutoffs -/

/-- The two finite intervals `I₁ = (A₁, B₁]` and `I₂ = (A₂, B₂]`.  Every definition of this
route carries this structure explicitly, so that the cutoffs are never silently removed. -/
structure Cutoffs where
  /-- left cutoff of `I₁` (excluded) -/
  a1 : ℕ
  /-- right cutoff of `I₁` (included) -/
  b1 : ℕ
  /-- left cutoff of `I₂` (excluded) -/
  a2 : ℕ
  /-- right cutoff of `I₂` (included) -/
  b2 : ℕ
  deriving DecidableEq, Repr

namespace Cutoffs

/-- `I₁ = (A₁, B₁]`. -/
def I1 (I : Cutoffs) : Finset ℕ := Finset.Ioc I.a1 I.b1

/-- `I₂ = (A₂, B₂]`. -/
def I2 (I : Cutoffs) : Finset ℕ := Finset.Ioc I.a2 I.b2

/-- The box `I₁ × I₂` over which the truncated coefficient is assembled. -/
def box (I : Cutoffs) : Finset (ℕ × ℕ) := I.I1 ×ˢ I.I2

/-- `Q_max = B₁ B₂`: the largest product of the two cutoffs. -/
def Qmax (I : Cutoffs) : ℕ := I.b1 * I.b2

theorem mem_I1 {I : Cutoffs} {u : ℕ} : u ∈ I.I1 ↔ I.a1 < u ∧ u ≤ I.b1 := Finset.mem_Ioc

theorem mem_I2 {I : Cutoffs} {v : ℕ} : v ∈ I.I2 ↔ I.a2 < v ∧ v ≤ I.b2 := Finset.mem_Ioc

theorem mem_box {I : Cutoffs} {p : ℕ × ℕ} :
    p ∈ I.box ↔ (I.a1 < p.1 ∧ p.1 ≤ I.b1) ∧ (I.a2 < p.2 ∧ p.2 ≤ I.b2) := by
  simp [box, I1, I2, Finset.mem_product, Finset.mem_Ioc]

/-- Both coordinates of a box point are positive: the cutoff intervals are half-open on the
left, so `0` never occurs. -/
theorem box_pos {I : Cutoffs} {p : ℕ × ℕ} (hp : p ∈ I.box) : 0 < p.1 ∧ 0 < p.2 := by
  rw [mem_box] at hp
  exact ⟨Nat.pos_of_ne_zero (by omega), Nat.pos_of_ne_zero (by omega)⟩

/-- The product of a box point never exceeds `Q_max`. -/
theorem box_prod_le {I : Cutoffs} {p : ℕ × ℕ} (hp : p ∈ I.box) : p.1 * p.2 ≤ I.Qmax := by
  rw [mem_box] at hp
  exact Nat.mul_le_mul hp.1.2 hp.2.2

end Cutoffs

/-! ## 2. The truncated Möbius coefficient -/

/-- **The truncated Möbius coefficient**

`λ(d) = ∑_{uv = d, u ∈ I₁, v ∈ I₂, u, v odd} μ(u) μ(v)`.

The two sharp cutoffs and the two oddness conditions are literal parts of the definition. -/
def lam (I : Cutoffs) (d : ℕ) : ℤ :=
  ∑ p ∈ I.box, if Odd p.1 ∧ Odd p.2 ∧ p.1 * p.2 = d then (moebius p.1) * (moebius p.2) else 0

/-- `λ` vanishes at `0`: the cutoff intervals contain no zero. -/
theorem lam_zero (I : Cutoffs) : lam I 0 = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := I.box_pos hp
  rw [if_neg]
  rintro ⟨-, -, h0⟩
  exact absurd h0 (Nat.mul_ne_zero h.1.ne' h.2.ne')

/-- **Sharp support**: `λ` is supported in `d ≤ Q_max = B₁B₂`.  This is the formal trace of the
two cutoffs. -/
theorem lam_eq_zero_of_Qmax_lt (I : Cutoffs) {d : ℕ} (hd : I.Qmax < d) : lam I d = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  have h := I.box_prod_le hp
  rw [if_neg]
  rintro ⟨-, -, rfl⟩
  omega

/-- `λ` is supported on odd `d`. -/
theorem lam_eq_zero_of_even (I : Cutoffs) {d : ℕ} (hd : ¬ Odd d) : lam I d = 0 := by
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [if_neg]
  rintro ⟨h1, h2, rfl⟩
  exact hd (h1.mul h2)

/-- An explicit pointwise formula: for a fixed `d`, only the box points with product `d`
contribute. -/
theorem lam_eq_sum_filter (I : Cutoffs) (d : ℕ) :
    lam I d =
      ∑ p ∈ I.box.filter (fun p => Odd p.1 ∧ Odd p.2 ∧ p.1 * p.2 = d), (moebius p.1) * (moebius p.2) := by
  rw [lam, Finset.sum_filter]

/-! ## 3. `λ` is not the unrestricted convolution -/

/-- The unrestricted Dirichlet convolution `(μ * μ)(d) = ∑_{uv = d} μ(u)μ(v)`, given here only
to be *distinguished* from `λ`. -/
def muConv (d : ℕ) : ℤ := ∑ p ∈ d.divisorsAntidiagonal, (moebius p.1) * (moebius p.2)

/-- **The cutoffs are not cosmetic.**  With `I₁ = I₂ = (0,1]` the truncated coefficient at
`d = 3` is `0`, whereas the unrestricted convolution is `-2`: `λ` may not be replaced by
`μ * μ`. -/
theorem lam_ne_muConv :
    lam ⟨0, 1, 0, 1⟩ 3 = 0 ∧ muConv 3 = -2 ∧ lam ⟨0, 1, 0, 1⟩ 3 ≠ muConv 3 := by
  have h1 : lam ⟨0, 1, 0, 1⟩ 3 = 0 := by
    simp [lam, Cutoffs.box, Cutoffs.I1, Cutoffs.I2]
  have h2 : muConv 3 = -2 := by
    have h : (3 : ℕ).divisorsAntidiagonal = {(1, 3), (3, 1)} := by decide
    rw [muConv, h]
    simp [moebius_apply_prime (by norm_num : Nat.Prime 3)]
  exact ⟨h1, h2, by rw [h1, h2]; norm_num⟩

/-- A sanity computation: with cutoffs wide enough to contain every factorisation of `3`, the
truncated coefficient does reproduce the two admissible pairs `(1,3)` and `(3,1)`. -/
theorem lam_three_wide : lam ⟨0, 3, 0, 3⟩ 3 = -2 := by
  have hb : (Cutoffs.box ⟨0, 3, 0, 3⟩) =
      {(1, 1), (1, 2), (1, 3), (2, 1), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)} := by decide
  rw [lam, hb]
  norm_num [Finset.sum_insert, moebius_apply_prime (by norm_num : Nat.Prime 3)]

/-! ## 4. The assembled-versus-packetwise firewall -/

/-- **Firewall (cancellation before squaring).**  Assembled linear coefficients may cancel, so
an arbitrarily good bound on the *assembled* quantity gives no bound whatsoever on the
packetwise `ℓ¹` or `ℓ²` norms: for every tolerance `ε > 0` there is a two-packet coefficient
vector whose assembled value is `0` while its packetwise norms are `1` and `1/2`. -/
theorem assembled_bound_does_not_imply_packetwise (ε : ℚ) (hε : 0 < ε) :
    ∃ f : Fin 2 → ℚ, |∑ i, f i| ≤ ε ∧ (∑ i, |f i|) = 1 ∧ (∑ i, (f i) ^ 2) = 1 / 2 := by
  refine ⟨![1 / 2, -(1 / 2)], ?_, ?_, ?_⟩ <;>
    simp [Fin.sum_univ_two, abs_of_nonneg] <;> norm_num
  · linarith

/-- The same firewall in scaling form: the packetwise `ℓ²` mass can be made arbitrarily large
while the assembled value stays exactly `0`. -/
theorem assembled_zero_with_large_packets (T : ℚ) :
    ∃ f : Fin 2 → ℚ, (∑ i, f i) = 0 ∧ T ≤ ∑ i, (f i) ^ 2 := by
  refine ⟨![|T| + 1, -(|T| + 1)], by simp [Fin.sum_univ_two]; ring, ?_⟩
  have hT : T ≤ |T| := le_abs_self T
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  nlinarith [abs_nonneg T]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
