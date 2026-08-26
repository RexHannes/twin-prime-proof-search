import RequestProject.NANC.Gate1BDet2.Gate1BExponentLedger

/-!
# Gate 1B / determinant-2 bank, Module 12: the δ-conductor exponent ledger

Exact rational arithmetic only.  Nothing in this module is an analytic
statement: no `X^r` size is asserted, no property of the Heath-Brown / DFI
delta symbol is proved, and the "delta-conductor label" `Ce = Qe = ω` is
recorded **only as a rational label reflecting the current working analytic
choice**, not as a theorem about a delta-symbol decomposition.

Exponent labels, relative to `X`:

* `Ue = 4/9`, `Ve = 5/9` (so `Ue + Ve = 1`);
* `Qe = ω`, `Re = 1 − ω` (so `Qe + Re = 1`), for `13/18 ≤ ω ≤ 8/9`;
* `He = Qe − Re = 2ω − 1`, the near-top dual `h`-length exponent.

The banked consequences of the window `13/18 ≤ ω ≤ 8/9` are
`1/9 ≤ Re ≤ 5/18`, `ω > 2/3`, `2 Re < Qe`, and, at the binding endpoint
`ω = 13/18`, `He = 4/9` and `He / Qe = 2 − 1/ω = 8/13`.

These names are deliberately distinct from the ones in
`Gate1BExponentLedger` (`Uexp`, `Vexp`, `Qexp`, `Rexp`): the numerical values of
`Ue`, `Ve` agree with `Uexp`, `Vexp`, as recorded below.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Delta

/-! ## 1. The exponent window -/

/-- The lower (binding) endpoint of the working `ω`-window. -/
def omegaLow : ℚ := 13 / 18

/-- The upper endpoint of the working `ω`-window. -/
def omegaHigh : ℚ := 8 / 9

/-- The working window `13/18 ≤ ω ≤ 8/9`. -/
def InWindow (omega : ℚ) : Prop := omegaLow ≤ omega ∧ omega ≤ omegaHigh

theorem omegaLow_lt_omegaHigh : omegaLow < omegaHigh := by
  norm_num [omegaLow, omegaHigh]

theorem inWindow_omegaLow : InWindow omegaLow := ⟨le_rfl, by norm_num [omegaLow, omegaHigh]⟩

/-! ## 2. The exponent labels -/

/-- `U = X^(4/9)`. -/
def Ue : ℚ := 4 / 9

/-- `V = X^(5/9)`. -/
def Ve : ℚ := 5 / 9

/-- `q = X^ω`. -/
def Qe (omega : ℚ) : ℚ := omega

/-- `R = X^(1−ω)`, the complementary length. -/
def Re (omega : ℚ) : ℚ := 1 - omega

/-- The labels `Ue`, `Ve` coincide with the ones of the earlier ledger module. -/
theorem Ue_eq_Uexp : Ue = Uexp := rfl

theorem Ve_eq_Vexp : Ve = Vexp := rfl

/-- `U V = X`. -/
theorem Ue_add_Ve : Ue + Ve = 1 := by norm_num [Ue, Ve]

/-- `q R = X`. -/
theorem Qe_add_Re (omega : ℚ) : Qe omega + Re omega = 1 := by simp [Qe, Re]

/-! ## 3. Consequences of the window -/

/-- In the window, `1/9 ≤ R_e`. -/
theorem Re_lower {omega : ℚ} (h : InWindow omega) : (1 : ℚ) / 9 ≤ Re omega := by
  have := h.2
  simp only [omegaHigh] at this
  simp only [Re]
  linarith

/-- In the window, `R_e ≤ 5/18`. -/
theorem Re_upper {omega : ℚ} (h : InWindow omega) : Re omega ≤ 5 / 18 := by
  have := h.1
  simp only [omegaLow] at this
  simp only [Re]
  linarith

/-- In the window, `1/9 ≤ R_e ≤ 5/18`. -/
theorem Re_mem_Icc {omega : ℚ} (h : InWindow omega) :
    (1 : ℚ) / 9 ≤ Re omega ∧ Re omega ≤ 5 / 18 :=
  ⟨Re_lower h, Re_upper h⟩

/-- In the window, `ω > 2/3`. -/
theorem omega_gt_two_thirds {omega : ℚ} (h : InWindow omega) : (2 : ℚ) / 3 < omega := by
  have := h.1
  simp only [omegaLow] at this
  linarith

/-- **The near-top separation.**  In the window, `2 R_e < Q_e`, i.e.
`2(1 − ω) < ω`; equivalently `ω > 2/3`. -/
theorem two_Re_lt_Qe {omega : ℚ} (h : InWindow omega) : 2 * Re omega < Qe omega := by
  have := omega_gt_two_thirds h
  simp only [Re, Qe]
  linarith

/-- The converse: `2 R_e < Q_e` holds exactly when `ω > 2/3`, so the inequality
carries no information beyond the window's left half. -/
theorem two_Re_lt_Qe_iff (omega : ℚ) : 2 * Re omega < Qe omega ↔ (2 : ℚ) / 3 < omega := by
  simp only [Re, Qe]
  constructor <;> intro h <;> linarith

/-! ## 4. The working delta-conductor label -/

/-- **WORKING ANALYTIC CHOICE, NOT A THEOREM ABOUT THE DELTA SYMBOL.**  The
optimised delta-conductor label used in the current route is `C_e = Q_e = ω`.
This definition records the *label*; it asserts nothing about any delta-symbol
decomposition. -/
def Ce (omega : ℚ) : ℚ := Qe omega

theorem Ce_eq_Qe (omega : ℚ) : Ce omega = Qe omega := rfl

theorem Ce_eq_omega (omega : ℚ) : Ce omega = omega := rfl

/-! ## 5. The near-top dual `h`-length -/

/-- The near-top dual `h`-length exponent `H_e = Q_e − R_e`. -/
def He (omega : ℚ) : ℚ := Qe omega - Re omega

/-- `H_e = 2ω − 1`. -/
theorem He_eq (omega : ℚ) : He omega = 2 * omega - 1 := by simp only [He, Qe, Re]; ring

/-- At the binding endpoint `ω = 13/18` one has `H_e = 4/9`. -/
theorem He_at_omegaLow : He omegaLow = 4 / 9 := by
  rw [He_eq]; norm_num [omegaLow]

/-- Relative to `q = X^ω`, the dual length has relative exponent
`H_e / Q_e = 2 − 1/ω` (for `ω ≠ 0`). -/
theorem He_div_Qe (omega : ℚ) (h : omega ≠ 0) : He omega / Qe omega = 2 - 1 / omega := by
  simp only [He_eq, Qe]
  field_simp

/-- At the binding endpoint, `2 − 18/13 = 8/13`. -/
theorem two_sub_inv_omegaLow : 2 - 1 / omegaLow = 8 / 13 := by
  norm_num [omegaLow]

/-- **The near-top relative dual exponent at the binding endpoint:**
`H_e / Q_e = 8/13`. -/
theorem He_div_Qe_at_omegaLow : He omegaLow / Qe omegaLow = 8 / 13 := by
  rw [He_div_Qe _ (by norm_num [omegaLow])]
  exact two_sub_inv_omegaLow

/-- In the window the relative dual exponent is at most `8/13`, with equality
only at the binding endpoint: `2 − 1/ω` is increasing in `ω`, so the *smallest*
relative dual length occurs at `ω = 13/18`. -/
theorem He_div_Qe_ge_of_inWindow {omega : ℚ} (h : InWindow omega) :
    8 / 13 ≤ He omega / Qe omega := by
  have h0 : (0 : ℚ) < omega := lt_of_lt_of_le (by norm_num [omegaLow]) h.1
  rw [He_div_Qe _ (ne_of_gt h0)]
  have h1 : (13 : ℚ) / 18 ≤ omega := by simpa [omegaLow] using h.1
  have h2 : 1 / omega ≤ 18 / 13 := by
    rw [div_le_div_iff₀ h0 (by norm_num)]
    linarith
  linarith

/-! ## 6. Guard -/

/-- **Guard.**  The ledger is pure rational arithmetic: every identity above is
an identity of rational numbers and none of them implies any statement about
sizes, delta symbols, or Kloosterman sums.  In particular the same identities
hold at values of `ω` outside the analytic window. -/
theorem delta_ledger_is_purely_rational (omega : ℚ) :
    Qe omega + Re omega = 1 ∧ He omega = 2 * omega - 1 ∧ Qe 0 + Re 0 = 1 :=
  ⟨Qe_add_Re omega, He_eq omega, Qe_add_Re 0⟩

end Delta
end Gate1BDet2
end TwinPrimeProject
