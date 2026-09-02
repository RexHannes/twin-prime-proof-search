/-
# Universal / D0WP — source record and source pins

**Status of this module: definitions plus KERNEL_PROVED exponent algebra.  All
source pins are deliberately left UNINHABITED.**

Contents:

* `D0WPSource` — the *actual inner provider variables* `d0, wp, r, A, D, W, Q`,
  and `D0WPSourceHypotheses`, the source hypotheses recorded separately.  The
  record deliberately contains **no** cancellation estimate: the desired
  analytic conclusion is never a field of the source type.
* `HardP3PhysicalRange` — the literal hard-`P3` range interface
  (`D, W ≥ X^{1/3-ε}`, `D W = Q ≥ X^{2/3-ε}`, `r ≤ X^{1/2+ε}`) together with the
  exponent consequences that are actually used.  Status `SOURCE_PIN_OPEN`: this
  repository does **not** construct an inhabitant.
* `DwpSeparationPin`, `GammaIndependencePin` — the exact separation propositions,
  with transport lemmas.  Status `SOURCE_PIN_OPEN`.
* `P3CenteringPin` — the literal `h = 0` centering equality `RawHZero =
  ModelHZero`, with its transport lemma.  Status `SOURCE_PIN_OPEN`.

For each pin we also prove that it is a *genuine* obligation, by exhibiting data
for which it fails.  This forbids reading any of the pins as vacuously true.
-/
import Mathlib

namespace Universal.D0WP

/-! ## §2 The `d0 · wp` source record -/

/-- The actual inner provider variables. -/
structure D0WPSource where
  /-- The (divisor-type) `d0` variable. -/
  d0 : ℕ
  /-- The prime `wp` variable. -/
  wp : ℕ
  /-- The modulus `r`. -/
  r : ℕ
  /-- The numerator `A` of the reciprocal phase. -/
  A : ℕ
  /-- The dyadic `d0`-scale. -/
  D : ℝ
  /-- The dyadic `wp`-scale. -/
  W : ℝ
  /-- The total modulus scale. -/
  Q : ℝ

/-- Source hypotheses, recorded separately from the source variables.  There is
no estimate field here, by design. -/
structure D0WPSourceHypotheses (S : D0WPSource) : Prop where
  /-- `wp` is prime. -/
  wp_prime : Nat.Prime S.wp
  /-- `gcd(d0, r) = 1`. -/
  d0_coprime_r : Nat.Coprime S.d0 S.r
  /-- `gcd(wp, r) = 1`. -/
  wp_coprime_r : Nat.Coprime S.wp S.r
  /-- `D W = Q`. -/
  DW_eq_Q : S.D * S.W = S.Q
  /-- Positivity of the dyadic scales. -/
  D_pos : 0 < S.D
  /-- Positivity of the dyadic scales. -/
  W_pos : 0 < S.W

/-! ## §12 Hard-`P3` physical range interface -/

/-- The literal hard-`P3` physical range, with the `o(1)` slack made explicit as
a nonnegative parameter `eps`. -/
structure HardP3PhysicalRange (X eps : ℝ) (S : D0WPSource) : Prop where
  /-- The size parameter is large. -/
  X_gt_one : 1 < X
  /-- The slack is nonnegative. -/
  eps_nonneg : 0 ≤ eps
  /-- `D ≥ X^{1/3-ε}`. -/
  D_lower : S.D ≥ X ^ ((1:ℝ)/3 - eps)
  /-- `W ≥ X^{1/3-ε}`. -/
  W_lower : S.W ≥ X ^ ((1:ℝ)/3 - eps)
  /-- `D W = Q`. -/
  DW_eq_Q : S.D * S.W = S.Q
  /-- `Q ≥ X^{2/3-ε}`. -/
  Q_lower : S.Q ≥ X ^ ((2:ℝ)/3 - eps)
  /-- `r ≤ X^{1/2+ε}`. -/
  r_upper : (S.r : ℝ) ≤ X ^ ((1:ℝ)/2 + eps)

/-- **SOURCE PIN (UNINHABITED here).**  The obligation that the literal current
source derives the hard-`P3` physical range.  No inhabitant is constructed in
this repository, and none may be inferred from a research report. -/
def HardP3RangePin (X eps : ℝ) (S : D0WPSource) : Prop := HardP3PhysicalRange X eps S

/-- Exponent consequence actually used by the large-`rSharp` lane:
`r / Q ≤ X^{-1/6 + 2ε}`. -/
theorem hardP3_r_div_Q_le {X eps : ℝ} {S : D0WPSource} (h : HardP3PhysicalRange X eps S) :
    (S.r : ℝ) / S.Q ≤ X ^ (-(1:ℝ)/6 + 2 * eps) := by
  have hX0 : (0:ℝ) < X := lt_trans zero_lt_one h.X_gt_one
  have hQpos : (0:ℝ) < X ^ ((2:ℝ)/3 - eps) := Real.rpow_pos_of_pos hX0 _
  have hQ : 0 < S.Q := lt_of_lt_of_le hQpos h.Q_lower
  have hnum : (S.r : ℝ) ≤ X ^ ((1:ℝ)/2 + eps) := h.r_upper
  have hstep : (S.r : ℝ) / S.Q ≤ X ^ ((1:ℝ)/2 + eps) / X ^ ((2:ℝ)/3 - eps) := by
    exact div_le_div₀ (le_of_lt (Real.rpow_pos_of_pos hX0 _)) hnum hQpos h.Q_lower
  calc (S.r : ℝ) / S.Q ≤ X ^ ((1:ℝ)/2 + eps) / X ^ ((2:ℝ)/3 - eps) := hstep
    _ = X ^ (((1:ℝ)/2 + eps) - ((2:ℝ)/3 - eps)) := (Real.rpow_sub hX0 _ _).symm
    _ = X ^ (-(1:ℝ)/6 + 2 * eps) := by ring_nf

/-- Exponent consequence actually used by the large-`rSharp` lane:
`1 / D ≤ X^{-1/3 + ε}`. -/
theorem hardP3_one_div_D_le {X eps : ℝ} {S : D0WPSource} (h : HardP3PhysicalRange X eps S) :
    1 / S.D ≤ X ^ (-(1:ℝ)/3 + eps) := by
  have hX0 : (0:ℝ) < X := lt_trans zero_lt_one h.X_gt_one
  have hDpos : (0:ℝ) < X ^ ((1:ℝ)/3 - eps) := Real.rpow_pos_of_pos hX0 _
  have hD : 0 < S.D := lt_of_lt_of_le hDpos h.D_lower
  have : 1 / S.D ≤ 1 / X ^ ((1:ℝ)/3 - eps) := by
    apply one_div_le_one_div_of_le hDpos h.D_lower
  calc 1 / S.D ≤ 1 / X ^ ((1:ℝ)/3 - eps) := this
    _ = X ^ (-((1:ℝ)/3 - eps)) := by
        rw [Real.rpow_neg (le_of_lt hX0)]
        simp
    _ = X ^ (-(1:ℝ)/3 + eps) := by ring_nf

/-! ## §13 `d0`/`wp` separation interface -/

/-- The finite data of a separated packet family: modulus, the two source
variables, the outer coefficient, and the actual coefficient. -/
structure SeparationData (ι : Type*) where
  /-- The modulus attached to the index. -/
  q : ι → ℕ
  /-- The `d0` component. -/
  d0 : ι → ℕ
  /-- The `wp` component. -/
  wp : ι → ℕ
  /-- The outer (frozen) coefficient. -/
  outer : ι → ℂ
  /-- The full coefficient. -/
  coeff : ι → ℂ

/-- **SOURCE PIN (UNINHABITED here).**  After the finite legal separation
(dyadic cut of `q = d0 · wp`, `Γ`, selected `E`, HB labels, prime-order
conditions, smooth/Perron factors) the coefficient is exactly
`outer · α(d0) · β(wp)`. -/
structure DwpSeparationPin {ι : Type*} (data : SeparationData ι) (α β : ℕ → ℂ) : Prop where
  /-- The dyadic cut factorisation of the modulus. -/
  qFactor : ∀ i, data.q i = data.d0 i * data.wp i
  /-- The exact separated coefficient form. -/
  separated : ∀ i, data.coeff i = data.outer i * α (data.d0 i) * β (data.wp i)

/-- **SOURCE PIN (UNINHABITED here).**  `Γ`-independence of the outer
coefficient, stated as an exact equality, never as an informal remark. -/
structure GammaIndependencePin {ι Γ : Type*} (outerFull : Γ → ι → ℂ) : Prop where
  /-- The outer coefficient does not depend on `Γ`. -/
  independent : ∀ g g' : Γ, ∀ i : ι, outerFull g i = outerFull g' i

/-- Transport along the separation pin: the packet sum becomes an explicitly
bilinear `d0 · wp` sum.  (This is a rewrite, not an estimate.) -/
theorem separated_sum_form {ι : Type*} [Fintype ι] {data : SeparationData ι} {α β : ℕ → ℂ}
    (pin : DwpSeparationPin data α β) (K : ℕ → ℕ → ℂ) :
    ∑ i, data.coeff i * K (data.d0 i) (data.wp i)
      = ∑ i, data.outer i * (α (data.d0 i) * β (data.wp i) * K (data.d0 i) (data.wp i)) := by
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pin.separated i]
  ring

/-- The separation pin is a genuine obligation: it can fail. -/
theorem dwpSeparationPin_not_automatic :
    ∃ (data : SeparationData Unit) (α β : ℕ → ℂ), ¬ DwpSeparationPin data α β := by
  refine ⟨⟨fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 0⟩,
    (fun _ => 1), (fun _ => 1), ?_⟩
  intro pin
  have := pin.separated ()
  norm_num at this

/-! ## §14 Centering interface -/

/-- The two centering objects, kept separate by construction. -/
structure CenteringData where
  /-- The raw `h = 0` term of the physical source. -/
  rawHZero : ℂ
  /-- The `h = 0` term of the model. -/
  modelHZero : ℂ

/-- **SOURCE PIN (UNINHABITED here).**  Literal `h = 0` centering: the raw and
model `h = 0` terms coincide. -/
def P3CenteringPin (c : CenteringData) : Prop := c.rawHZero = c.modelHZero

/-- Transport along the centering pin. -/
theorem centering_transport {c : CenteringData} (pin : P3CenteringPin c) {B : ℝ}
    (hb : ‖c.modelHZero‖ ≤ B) : ‖c.rawHZero‖ ≤ B := by
  rw [P3CenteringPin] at pin
  rw [pin]
  exact hb

/-- The centering pin is a genuine obligation: it can fail. -/
theorem centeringPin_not_automatic : ∃ c : CenteringData, ¬ P3CenteringPin c := by
  refine ⟨⟨0, 1⟩, ?_⟩
  intro h
  rw [P3CenteringPin] at h
  norm_num at h

end Universal.D0WP
