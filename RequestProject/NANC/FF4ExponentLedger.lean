import RequestProject.NANC.D4.BasicParams

/-!
# Route-A fibre frame: the rational exponent ledger

All statements here are identities and inequalities between rational numbers.
They record the exponent bookkeeping of the Route-A / FF4 frame; none of them
asserts that any analytic theorem (Bettin–Chandee, large sieve, FF4, Route A)
applies.

The exponent dictionary is the one already banked in
`RequestProject/NANC/D4/BasicParams.lean`:

* `R_exp a = a`,
* `H_exp a b = a + 2b - 2/3`,
* `M_exp = 1/3`,
* `formalMSaving = 1/6`.

In particular `H / R = X^(2b - 2/3)` at the level of exponents.
-/

namespace RouteAFibreFrame

open TwinPrimeProject.NANC.D4

/-! ### The `H / R` exponent -/

/-- `H / R = X^(2b - 2/3)` at the level of exponents. -/
theorem H_over_R_exponent (a b : ℚ) : H_exp a b - R_exp a = 2 * b - 2 / 3 := by
  simp [H_exp, R_exp]; ring

/-- `b ≥ 1/3` forces the exponent `2b - 2/3` to be nonnegative. -/
theorem exponent_gap_nonneg {b : ℚ} (hb : 1 / 3 ≤ b) : 0 ≤ 2 * b - 2 / 3 := by
  linarith

/-- Consequently `R ≤ H` at the level of exponents whenever `b ≥ 1/3`; this is
the numerical comparison consumed by
`RouteAFibreFrame.routeA_variance_from_ff4`. -/
theorem R_exp_le_H_exp {a b : ℚ} (hb : 1 / 3 ≤ b) : R_exp a ≤ H_exp a b := by
  have := exponent_gap_nonneg hb
  simp only [H_exp, R_exp]
  linarith

/-- On the closed high-`b` region the comparison `R ≤ H` always holds. -/
theorem R_exp_le_H_exp_of_highB {a b : ℚ} (h : HighBRegion a b) :
    R_exp a ≤ H_exp a b :=
  R_exp_le_H_exp h.2.1

/-! ### The formal Bettin–Chandee region arithmetic

`bcRegion` is *only* the arithmetic inequality `21a + 44b ≥ 21`.  Membership of a
vertex in this region is **not** a claim that the Bettin–Chandee theorem applies
there. -/

/-- The arithmetic region `21a + 44b ≥ 21`. -/
def bcRegion (a b : ℚ) : Prop := 21 ≤ 21 * a + 44 * b

/-- The margin by which a point satisfies (or fails) `21a + 44b ≥ 21`. -/
def bcMargin (a b : ℚ) : ℚ := 21 * a + 44 * b - 21

theorem bcRegion_iff_margin_nonneg (a b : ℚ) : bcRegion a b ↔ 0 ≤ bcMargin a b := by
  constructor <;> intro h <;> simp only [bcRegion, bcMargin] at * <;> linarith

/-! ### The three vertices -/

/-- Vertex `V₁ = (5/18, 1/3)`. -/
def V1 : ℚ × ℚ := (5 / 18, 1 / 3)
/-- Vertex `V₂ = (5/18, 25/72)`. -/
def V2 : ℚ × ℚ := (5 / 18, 25 / 72)
/-- Vertex `V₃ = (7/24, 1/3)`. -/
def V3 : ℚ × ℚ := (7 / 24, 1 / 3)

theorem bcMargin_V1 : bcMargin V1.1 V1.2 = -1 / 2 := by norm_num [bcMargin, V1]
theorem bcMargin_V2 : bcMargin V2.1 V2.2 = 1 / 9 := by norm_num [bcMargin, V2]
theorem bcMargin_V3 : bcMargin V3.1 V3.2 = -5 / 24 := by norm_num [bcMargin, V3]

/-- `V₂` satisfies the arithmetic inequality `21a + 44b ≥ 21`. -/
theorem bcRegion_V2 : bcRegion V2.1 V2.2 := by
  rw [bcRegion_iff_margin_nonneg, bcMargin_V2]; norm_num

/-- `V₁` fails the arithmetic inequality. -/
theorem not_bcRegion_V1 : ¬ bcRegion V1.1 V1.2 := by
  rw [bcRegion_iff_margin_nonneg, bcMargin_V1]; norm_num

/-- `V₃` fails the arithmetic inequality. -/
theorem not_bcRegion_V3 : ¬ bcRegion V3.1 V3.2 := by
  rw [bcRegion_iff_margin_nonneg, bcMargin_V3]; norm_num

/-- Exactly one of the three vertices satisfies `21a + 44b ≥ 21`. -/
theorem bcRegion_vertices :
    ¬ bcRegion V1.1 V1.2 ∧ bcRegion V2.1 V2.2 ∧ ¬ bcRegion V3.1 V3.2 :=
  ⟨not_bcRegion_V1, bcRegion_V2, not_bcRegion_V3⟩

/-! ### The `1/180` residual margin at `V₂`

The claimed residual margin at `V₂` is `1/180`, obtained from the raw margin
`1/9` after subtracting a formal saving `s` and a Route-A deficit `d`.  The
supplied data fix only the *sum* `s + d = 19/180`, not the individual values, so
the identity is recorded in exactly that conditional form. -/

/-- The total that must be subtracted from the raw `V₂` margin to leave `1/180`. -/
def v2SubtractedTotal : ℚ := 19 / 180

theorem v2_residual_margin {s d : ℚ} (h : s + d = v2SubtractedTotal) :
    bcMargin V2.1 V2.2 - (s + d) = 1 / 180 := by
  rw [bcMargin_V2, h]
  norm_num [v2SubtractedTotal]

theorem v2_subtracted_total_eq : (1 : ℚ) / 9 - v2SubtractedTotal = 1 / 180 := by
  norm_num [v2SubtractedTotal]

/-! ### Vertex deficits against the formal `m`-saving

`vertexFormalDeficit a b = H_exp a b - M_exp / 2 - formalMSaving` is the excess
of the Bettin–Chandee bookkeeping cost over the formal saving `1/6`.  Negative
values mean the formal saving covers the cost at that vertex. -/

/-- The deficit of a vertex against the formal `m`-saving `1/6`. -/
def vertexFormalDeficit (a b : ℚ) : ℚ := H_exp a b - M_exp / 2 - formalMSaving

theorem vertexFormalDeficit_V1 : vertexFormalDeficit V1.1 V1.2 = -1 / 18 := by
  norm_num [vertexFormalDeficit, H_exp, M_exp, formalMSaving, V1]

theorem vertexFormalDeficit_V2 : vertexFormalDeficit V2.1 V2.2 = -1 / 36 := by
  norm_num [vertexFormalDeficit, H_exp, M_exp, formalMSaving, V2]

theorem vertexFormalDeficit_V3 : vertexFormalDeficit V3.1 V3.2 = -1 / 24 := by
  norm_num [vertexFormalDeficit, H_exp, M_exp, formalMSaving, V3]

/-- The three claimed vertex deficits, as one rational identity. -/
theorem vertex_deficits :
    vertexFormalDeficit V1.1 V1.2 = -1 / 18 ∧
    vertexFormalDeficit V2.1 V2.2 = -1 / 36 ∧
    vertexFormalDeficit V3.1 V3.2 = -1 / 24 :=
  ⟨vertexFormalDeficit_V1, vertexFormalDeficit_V2, vertexFormalDeficit_V3⟩

/-- The banked CRG net exponents at the three vertices, restated in the Route-A
ledger. -/
theorem vertex_crg_net :
    crgNetExp V1.1 V1.2 = 0 ∧ crgNetExp V2.1 V2.2 = -1 / 36 ∧
    crgNetExp V3.1 V3.2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [crgNetExp, V1, V2, V3]

end RouteAFibreFrame
