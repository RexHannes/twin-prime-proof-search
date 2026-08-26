import RequestProject.Options
namespace TwinPrimeProject.NANC

theorem t0_secondary_phase_unit_size (a b : ℚ) :
    (a+2*b-2/3) - (1/3+a+2*b) = -1 := by ring

theorem t0_secondary_phase_margin (a b : ℚ) (h : a+b ≤ 5/8) :
    (2/3+2*b)-(2*a+4*b-4/3)=2-2*a-2*b ∧ 3/4 ≤ 2-2*a-2*b := by constructor <;> linarith

theorem t0_margin_j0 (a b : ℚ) (h : a+b ≤ 5/8) :
    (2/3+2*b)-(2*a+4*b-2/3)=4/3-2*a-2*b ∧ 1/12 ≤ 4/3-2*a-2*b := by constructor <;> linarith

theorem t0_margin_j1 (a b : ℚ) (h : a+b ≤ 5/8) :
    (2/3+2*b)-(2*a+4*b-13/18)=25/18-2*a-2*b ∧ 5/36 ≤ 25/18-2*a-2*b := by constructor <;> linarith

theorem t0_margin_j2 (a b : ℚ) (ha0 : 5/18 ≤ a) (ha : a ≤ b) (h : a+b ≤ 5/8) :
    (2/3+2*b)-((3/2)*a+4*b-5/9)=11/9-(3/2)*a-2*b ∧
    1/9 ≤ 11/9-(3/2)*a-2*b := by constructor <;> linarith

theorem t0_margin_j2_value_at_5_16 :
    (11/9:ℚ)-(3/2)*(5/16)-2*(5/16)=37/288 := by norm_num

def delta3 (a b : ℚ) : ℚ := if b ≤ 1/3 then 5/6-(3/2)*a-b else 7/6-(3/2)*a-2*b

theorem t0_margin_j3_piecewise (a b : ℚ) :
    delta3 a b = if b ≤ 1/3 then 5/6-(3/2)*a-b else 7/6-(3/2)*a-2*b := rfl

theorem t0_margin_j3_global (a b : ℚ) (ha : a ≤ b) (hab : a+b ≤ 5/8)
    (ha0 : 5/18 ≤ a) : 5/96 ≤ delta3 a b := by
  unfold delta3
  split_ifs with hb
  · linarith
  · push_neg at hb; linarith
end NANC
