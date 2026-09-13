/-
# Gate1B / R11 / Frontier / Latest : the zero-resonance ledger

Append-only module.  Definitions and **exact deterministic lemmas** only.  Nothing here assumes
GRH, nothing assumes the absence of an exceptional zero, and nothing assumes that the retained
strip contains at most one zero.  No open proposition is inhabited.

* §1 the retained zero region
  `Re ρ > 1 − A log L / L`, `|Im ρ| ≤ L^D`, `Re ρ ≤ 1`,
  and the exact trichotomy against its complement (zero-density side / height side);
* §2 monotonicity of the retained region in `A` and `D`, and boundedness of the retained
  region (it is contained in an explicit box, so the retained family is a *finite/polylog*
  family in the intended instance);
* §3 zero families, the retained predicate, and the **zero/source moment** proposition, which is
  the exact open analytic node; plus the deterministic glue: splitting a family adds moments,
  and shrinking a family preserves a moment bound;
* §4 the three separate statuses of the ledger, as distinct propositions:
  zero-density-closed, Deuring–Heilbronn-conditional, exceptional-moment-open.  They are
  definitions, never inhabited here.
-/
import Mathlib

namespace Gate1B.R11.Frontier.Latest

open Finset
open scoped Classical

/-! ## 1. The retained zero region -/

/-- The retained zero region of the ledger: `1 − A log L / L < Re ρ ≤ 1` and `|Im ρ| ≤ L^D`. -/
def RetainedZero (A D L : ℝ) (rho : ℂ) : Prop :=
  1 - A * Real.log L / L < rho.re ∧ rho.re ≤ 1 ∧ |rho.im| ≤ L ^ D

/-- The zero-density side of the complement: the real part is to the left of the retained
window. -/
def LeftOfRetained (A L : ℝ) (rho : ℂ) : Prop := rho.re ≤ 1 - A * Real.log L / L

/-- The height side of the complement: the imaginary part exceeds the retained height. -/
def AboveRetainedHeight (D L : ℝ) (rho : ℂ) : Prop := L ^ D < |rho.im|

/-- **Exact trichotomy.**  Every point of the closed half-plane `Re ρ ≤ 1` is retained, or lies
left of the retained window, or lies above the retained height.  No analytic input. -/
theorem retained_trichotomy (A D L : ℝ) (rho : ℂ) (hre : rho.re ≤ 1) :
    RetainedZero A D L rho ∨ LeftOfRetained A L rho ∨ AboveRetainedHeight D L rho := by
  by_cases h1 : rho.re ≤ 1 - A * Real.log L / L
  · exact Or.inr (Or.inl h1)
  · by_cases h2 : |rho.im| ≤ L ^ D
    · exact Or.inl ⟨lt_of_not_ge h1, hre, h2⟩
    · exact Or.inr (Or.inr (lt_of_not_ge h2))

/-- The retained region and its zero-density complement are mutually exclusive. -/
theorem retained_not_left {A D L : ℝ} {rho : ℂ} (h : RetainedZero A D L rho) :
    ¬ LeftOfRetained A L rho := by
  intro hc
  exact absurd h.1 (not_lt.mpr hc)

/-- The retained region and its height complement are mutually exclusive. -/
theorem retained_not_above {A D L : ℝ} {rho : ℂ} (h : RetainedZero A D L rho) :
    ¬ AboveRetainedHeight D L rho := by
  intro hc
  exact absurd h.2.2 (not_le.mpr hc)

/-! ## 2. Monotonicity and boundedness -/

/-- Enlarging `A` enlarges the retained region (for `log L ≥ 0`, `L > 0`). -/
theorem retained_mono_A {A A' D L : ℝ} (hL : 0 < L) (hlog : 0 ≤ Real.log L) (hA : A ≤ A')
    {rho : ℂ} (h : RetainedZero A D L rho) : RetainedZero A' D L rho := by
  refine ⟨lt_of_le_of_lt ?_ h.1, h.2.1, h.2.2⟩
  have hstep : A * Real.log L / L ≤ A' * Real.log L / L := by gcongr
  linarith

/-- Enlarging `D` enlarges the retained region (for `L ≥ 1`). -/
theorem retained_mono_D {A D D' L : ℝ} (hL : 1 ≤ L) (hD : D ≤ D') {rho : ℂ}
    (h : RetainedZero A D L rho) : RetainedZero A D' L rho :=
  ⟨h.1, h.2.1, h.2.2.trans (Real.rpow_le_rpow_of_exponent_le hL hD)⟩

/-- **The retained region is bounded**: it sits inside an explicit box, so after the height cut
the retained family is confined to a compact rectangle. -/
theorem retained_bounded {A D L : ℝ} {rho : ℂ} (h : RetainedZero A D L rho) :
    |rho.re| ≤ max 1 |1 - A * Real.log L / L| ∧ |rho.im| ≤ L ^ D := by
  refine ⟨?_, h.2.2⟩
  rcases abs_cases rho.re with ⟨he, _⟩ | ⟨he, _⟩
  · rw [he]; exact le_max_of_le_left h.2.1
  · rw [he]
    refine le_max_of_le_right ?_
    have := h.1
    rcases abs_cases (1 - A * Real.log L / L) with ⟨hb, _⟩ | ⟨hb, _⟩ <;> rw [hb] <;> linarith

/-! ## 3. Zero families and the zero/source moment -/

/-- A *zero family* of the ledger: at each scale `x` a finite set of retained zeros together with
the source mass attached to each of them. -/
structure ZeroFamily where
  /-- The retained zeros at scale `x`. -/
  zeros : ℝ → Finset ℂ
  /-- The nonnegative source mass attached to a zero at scale `x`. -/
  source : ℝ → ℂ → ℝ
  /-- The source mass is nonnegative. -/
  source_nonneg : ∀ x rho, 0 ≤ source x rho

/-- The family is *retained* for the parameters `(A, D)` if every one of its zeros lies in the
retained region at height parameter `L = log x`. -/
def ZeroFamily.Retained (F : ZeroFamily) (A D : ℝ) : Prop :=
  ∀ x, 3 ≤ x → ∀ rho ∈ F.zeros x, RetainedZero A D (Real.log x) rho

/-- **The zero/source moment proposition** — the exact analytic node of the ledger: the total
source mass carried by the retained zeros is smaller than `x (log x)^{−B}`.  This is a
definition; it is never inhabited in this repository. -/
def ZeroMomentBound (F : ZeroFamily) (B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    ∑ rho ∈ F.zeros x, F.source x rho ≤ C * x * (Real.log x) ^ (-B)

/-- Deterministic glue: a moment bound for a family transfers to any subfamily (same source). -/
theorem ZeroMomentBound.mono {F G : ZeroFamily} {B : ℝ} (hFG : ∀ x, G.zeros x ⊆ F.zeros x)
    (hsrc : ∀ x rho, G.source x rho = F.source x rho) (h : ZeroMomentBound F B) :
    ZeroMomentBound G B := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨C, hC, fun x hx => ?_⟩
  have hle : ∑ rho ∈ G.zeros x, G.source x rho ≤ ∑ rho ∈ F.zeros x, F.source x rho := by
    calc ∑ rho ∈ G.zeros x, G.source x rho
        = ∑ rho ∈ G.zeros x, F.source x rho :=
          Finset.sum_congr rfl fun rho _ => hsrc x rho
      _ ≤ ∑ rho ∈ F.zeros x, F.source x rho :=
          Finset.sum_le_sum_of_subset_of_nonneg (hFG x)
            (fun rho _ _ => F.source_nonneg x rho)
  exact hle.trans (hbound x hx)

/-- Deterministic glue: splitting a zero family by a decidable mask splits its moment exactly. -/
theorem zero_moment_split (F : ZeroFamily) (x : ℝ) (p : ℂ → Prop) [DecidablePred p] :
    ∑ rho ∈ F.zeros x, F.source x rho
      = ∑ rho ∈ (F.zeros x).filter p, F.source x rho
        + ∑ rho ∈ (F.zeros x).filter (fun rho => ¬ p rho), F.source x rho :=
  (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- **Reduction of the moment to counting × pointwise size.**  If the retained family has at
most `K x` zeros at scale `x` and each carries source mass at most `s x`, and if
`K x · s x ≤ C x (log x)^{-B}`, then the zero/source moment bound holds.  This is the
deterministic step that reduces the exceptional-zero wedge to (i) a counting bound for the
retained family and (ii) a pointwise bound for a single retained zero. -/
theorem zeroMomentBound_of_card_and_pointwise (F : ZeroFamily) {B C : ℝ} (hC : 0 < C)
    (K s : ℝ → ℝ)
    (hcard : ∀ x : ℝ, 3 ≤ x → ((F.zeros x).card : ℝ) ≤ K x)
    (hpt : ∀ x : ℝ, 3 ≤ x → ∀ rho ∈ F.zeros x, F.source x rho ≤ s x)
    (hs : ∀ x : ℝ, 3 ≤ x → 0 ≤ s x)
    (hbudget : ∀ x : ℝ, 3 ≤ x → K x * s x ≤ C * x * (Real.log x) ^ (-B)) :
    ZeroMomentBound F B := by
  refine ⟨C, hC, fun x hx => ?_⟩
  calc ∑ rho ∈ F.zeros x, F.source x rho
      ≤ ∑ _rho ∈ F.zeros x, s x := Finset.sum_le_sum fun rho hrho => hpt x hx rho hrho
    _ = ((F.zeros x).card : ℝ) * s x := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ K x * s x := by
        exact mul_le_mul_of_nonneg_right (hcard x hx) (hs x hx)
    _ ≤ C * x * (Real.log x) ^ (-B) := hbudget x hx

/-! ## 4. The three separate statuses -/

/-- **ZERO-DENSITY-CLOSED**: the contribution of the zeros left of the retained window is
controlled.  A definition, never inhabited here. -/
def ZeroDensityClosed (F : ZeroFamily) (A B : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
    ∑ rho ∈ (F.zeros x).filter (fun rho => LeftOfRetained A (Real.log x) rho), F.source x rho
      ≤ C * x * (Real.log x) ^ (-B)

/-- **DEURING–HEILBRONN-CONDITIONAL**: zero repulsion for the retained family, stated as an
explicit hypothesis interface (never inhabited). -/
def DeuringHeilbronnRepulsion (F : ZeroFamily) (A D : ℝ) : Prop :=
  ∀ x : ℝ, 3 ≤ x → ∀ rho ∈ F.zeros x, ∀ sigma ∈ F.zeros x, rho ≠ sigma →
    RetainedZero A D (Real.log x) rho → RetainedZero A D (Real.log x) sigma →
      1 / Real.log x ≤ |rho.im - sigma.im| + |rho.re - sigma.re|

/-- **EXCEPTIONAL MOMENT OPEN**: the moment of the retained (near-1, low-height) family.  This
is the open node; it is *not* implied by the other two statuses, and it is never inhabited. -/
def ExceptionalMomentOpen (F : ZeroFamily) (A D B : ℝ) : Prop :=
  F.Retained A D ∧ ZeroMomentBound F B

/-- Deterministic assembly: if the left-of-window mass is controlled and the retained moment is
controlled, then the whole family's moment is controlled, with the constants added.  This is the
only bridge between the statuses, and it is an identity-level estimate, not an analytic input. -/
theorem total_moment_of_split {F : ZeroFamily} {A B : ℝ}
    (hleft : ZeroDensityClosed F A B)
    (hret : ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ rho ∈ (F.zeros x).filter (fun rho => ¬ LeftOfRetained A (Real.log x) rho),
        F.source x rho ≤ C * x * (Real.log x) ^ (-B)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x →
      ∑ rho ∈ F.zeros x, F.source x rho ≤ C * x * (Real.log x) ^ (-B) := by
  obtain ⟨C₁, hC₁, h₁⟩ := hleft
  obtain ⟨C₂, hC₂, h₂⟩ := hret
  refine ⟨C₁ + C₂, by linarith, fun x hx => ?_⟩
  rw [zero_moment_split F x (fun rho => LeftOfRetained A (Real.log x) rho)]
  nlinarith [h₁ x hx, h₂ x hx]

end Gate1B.R11.Frontier.Latest
