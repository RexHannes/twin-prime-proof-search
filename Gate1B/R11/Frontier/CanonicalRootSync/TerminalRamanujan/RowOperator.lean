/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan : the EP-M2 row operator and
its quadratic moment  (T9)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted.

The exact formal objects of EP-M2:

```
R(e,s) = ∑_{z : e ∣ sz+2} β₅(z) F((sz+2)/e),      𝔐_raw = ∑_{e,s} W(s) |R(e,s)|².
```

`β₅` is an abstract finite source coefficient: **no** analytic property is proved or assumed for
it.  Three layers are kept strictly apart:

* the *algebraic identity* `R = R_low + R_top` and `𝔐_raw = 𝔐_top + 2 𝔠 + 𝔐_low`;
* the *analytic hypotheses*, which appear only as explicit inequalities in the statements;
* the *budget implication*, which derives the raw-to-top reduction **from** those hypotheses.

No asymptotic statement is proved here, and no bound is assumed.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.TerminalSplit

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

open Finset

/-! ## 1. The row operator -/

/-- **The EP-M2 row operator** `R(e,s) = ∑_{z, e ∣ sz+2} β₅(z) F((sz+2)/e)`, over the finite
source support `Z`. -/
def rowOp (Z : Finset ℕ) (beta5 : ℕ → ℝ) (Fval : ℕ → ℝ) (e s : ℕ) : ℝ :=
  ∑ z ∈ Z, if e ∣ s * z + 2 then beta5 z * Fval ((s * z + 2) / e) else 0

/-- The row operator is additive in the arithmetic input `F`. -/
theorem rowOp_add (Z : Finset ℕ) (beta5 F₁ F₂ : ℕ → ℝ) (e s : ℕ) :
    rowOp Z beta5 (fun N => F₁ N + F₂ N) e s
      = rowOp Z beta5 F₁ e s + rowOp Z beta5 F₂ e s := by
  unfold rowOp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun z _ => ?_
  split
  · ring
  · ring

/-- Every argument at which the row operator evaluates `F` is positive: `sz+2 ≥ 2` and `e` is a
genuine divisor, so `(sz+2)/e ≥ 1`.  This is what lets the low/top split of `F` be inserted
into the row operator with no side condition. -/
theorem rowOp_arg_pos {e s z : ℕ} (h : e ∣ s * z + 2) : 0 < (s * z + 2) / e := by
  have hn : 0 < s * z + 2 := by omega
  have he : 0 < e := by
    rcases Nat.eq_zero_or_pos e with rfl | he
    · rw [zero_dvd_iff] at h; omega
    · exact he
  exact Nat.div_pos (Nat.le_of_dvd hn h) he

/-- **The row-operator form of the low/top split**: the row operator of `F` is the row operator
of `F_low` plus the row operator of `F_top`. -/
theorem rowOp_terminal_split (I : Cutoffs) {q0 : ℕ} (hq0 : q0 ≤ I.Qmax)
    (Z : Finset ℕ) (beta5 : ℕ → ℝ) (e s : ℕ) :
    rowOp Z beta5 (fun N => ((Fsum I N : ℚ) : ℝ)) e s
      = rowOp Z beta5 (fun N => ((Flow I q0 N : ℚ) : ℝ)) e s
        + rowOp Z beta5 (fun N => ((Ftop I q0 N : ℚ) : ℝ)) e s := by
  rw [← rowOp_add]
  unfold rowOp
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : e ∣ s * z + 2
  · rw [if_pos h, if_pos h]
    simp only
    rw [Fsum_eq_low_add_top I hq0 (rowOp_arg_pos h)]
    push_cast
    ring
  · rw [if_neg h, if_neg h]

/-! ## 2. The quadratic moment -/

/-- **The finite quadratic moment** `𝔐 = ∑_{e,s} W(s) |R(e,s)|²`. -/
def moment (E S : Finset ℕ) (W : ℕ → ℝ) (R : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ E ×ˢ S, W p.2 * (R p.1 p.2) ^ 2

/-- The cross term `𝔠 = ∑_{e,s} W(s) R(e,s) R'(e,s)` of two row families. -/
def crossTerm (E S : Finset ℕ) (W : ℕ → ℝ) (R R' : ℕ → ℕ → ℝ) : ℝ :=
  ∑ p ∈ E ×ˢ S, W p.2 * (R p.1 p.2 * R' p.1 p.2)

/-- **The exact moment decomposition** (algebra only, no estimate):
`𝔐_raw = 𝔐_top + 2 𝔠(low, top) + 𝔐_low`. -/
theorem moment_split {E S : Finset ℕ} {W : ℕ → ℝ} {R Rlow Rtop : ℕ → ℕ → ℝ}
    (h : ∀ e s, R e s = Rlow e s + Rtop e s) :
    moment E S W R
      = moment E S W Rtop + 2 * crossTerm E S W Rlow Rtop + moment E S W Rlow := by
  unfold moment crossTerm
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [h p.1 p.2]
  ring

/-! ## 3. The budget layer: hypotheses in, reduction out -/

/-- **The raw-to-top reduction.**  *If* the terminal moment, the cross term and the low-band
moment obey the supplied budgets, *then* the raw moment obeys the assembled budget.  Nothing is
assumed about `β₅`, `W` or `F`; the three inequalities are the entire analytic input. -/
theorem raw_moment_budget {E S : Finset ℕ} {W : ℕ → ℝ} {R Rlow Rtop : ℕ → ℕ → ℝ}
    {Btop Bcross Blow : ℝ}
    (hsplit : ∀ e s, R e s = Rlow e s + Rtop e s)
    (htop : moment E S W Rtop ≤ Btop)
    (hcross : |crossTerm E S W Rlow Rtop| ≤ Bcross)
    (hlow : moment E S W Rlow ≤ Blow) :
    moment E S W R ≤ Btop + 2 * Bcross + Blow := by
  have hc : crossTerm E S W Rlow Rtop ≤ Bcross := le_trans (le_abs_self _) hcross
  rw [moment_split hsplit]
  linarith

/-- The reduction is sharp in the trivial direction: with a vanishing low band the raw moment
*is* the terminal moment. -/
theorem moment_eq_top_of_low_zero {E S : Finset ℕ} {W : ℕ → ℝ} {R Rlow Rtop : ℕ → ℕ → ℝ}
    (hsplit : ∀ e s, R e s = Rlow e s + Rtop e s) (hzero : ∀ e s, Rlow e s = 0) :
    moment E S W R = moment E S W Rtop := by
  rw [moment_split hsplit]
  have h1 : crossTerm E S W Rlow Rtop = 0 := by
    unfold crossTerm
    exact Finset.sum_eq_zero fun p _ => by rw [hzero]; ring
  have h2 : moment E S W Rlow = 0 := by
    unfold moment
    exact Finset.sum_eq_zero fun p _ => by rw [hzero]; ring
  rw [h1, h2]; ring

/-- **The algebra does not supply the estimate.**  The moment decomposition is universally
valid, yet there are data for which the raw moment exceeds any prescribed terminal budget: the
analytic hypotheses of `raw_moment_budget` are load-bearing. -/
theorem moment_algebra_does_not_bound (B : ℝ) :
    ∃ (E S : Finset ℕ) (W : ℕ → ℝ) (R : ℕ → ℕ → ℝ), B < moment E S W R := by
  refine ⟨{0}, {0}, fun _ => 1, fun _ _ => |B| + 1, ?_⟩
  unfold moment
  have h : ({0} : Finset ℕ) ×ˢ ({0} : Finset ℕ) = {((0 : ℕ), (0 : ℕ))} := rfl
  rw [h, Finset.sum_singleton]
  nlinarith [abs_nonneg B, le_abs_self B]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan
