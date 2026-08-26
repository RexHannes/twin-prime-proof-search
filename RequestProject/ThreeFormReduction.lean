import Mathlib

/-! # Three-form arithmetic reduction for doubly-small max-jump tokens -/

namespace Erdos461A

structure ThreeFormData where
  aa : ℕ
  bb : ℕ
  bigA : ℕ
  bigB : ℕ
  rr : ℕ
  ha : 0 < aa
  hb : 0 < bb
  hcop : Nat.Coprime aa bb
  hminus : rr - 1 = 2 * aa * bigA
  hplus : rr + 1 = 2 * bb * bigB

theorem threeFormLinearEquation (d : ThreeFormData) :
    d.bb * d.bigB = d.aa * d.bigA + 1 := by
  have h1 : d.rr - 1 = 2 * d.aa * d.bigA := d.hminus
  have h2 : d.rr + 1 = 2 * d.bb * d.bigB := d.hplus
  -- From h2: d.rr + 1 ≥ 1, so d.rr ≥ 0 (always true)
  -- But also 2 * d.bb * d.bigB ≥ 2 * 1 * 0 = 0, but d.rr + 1 ≥ 1
  -- Actually we need: if d.rr = 0, then 1 = 2 * d.bb * d.bigB
  -- Since d.bb > 0, this requires d.bigB ≥ 1, so 2 * d.bb * d.bigB ≥ 2 > 1, contradiction
  -- So d.rr ≥ 1
  have hrr_pos : d.rr ≥ 1 := by
    by_contra h
    push_neg at h
    interval_cases d.rr
    simp_all
    nlinarith
  -- Use Nat.sub_add_cancel
  have hrr_eq : d.rr = 2 * d.aa * d.bigA + 1 := by
    have := Nat.sub_add_cancel hrr_pos
    rw [h1] at this
    exact this.symm
  -- From h2: d.rr + 1 = 2 * d.bb * d.bigB
  -- Substitute d.rr = 2 * d.aa * d.bigA + 1:
  rw [hrr_eq] at h2
  -- Now h2 : (2 * d.aa * d.bigA + 1) + 1 = 2 * d.bb * d.bigB
  -- Simplify: 2 * d.aa * d.bigA + 2 = 2 * d.bb * d.bigB
  ring_nf at h2
  linarith

theorem exactlyOneABEven (d : ThreeFormData)
    (hAodd : Odd d.bigA) (hBodd : Odd d.bigB) :
    Even d.aa ↔ ¬ Even d.bb := by
  have heq := threeFormLinearEquation d
  constructor
  · intro haa_even hb_even
    have h1 : Even (d.bb * d.bigB) := hb_even.mul_right d.bigB
    rw [heq] at h1
    simp [Nat.even_add, haa_even] at h1
  · intro hb_odd
    rcases Nat.even_or_odd d.bb with ⟨k, hk⟩ | hk
    · exact False.elim (hb_odd ⟨k, hk⟩)
    · have hprod_odd : Odd (d.bb * d.bigB) := hk.mul hBodd
      rw [heq] at hprod_odd
      obtain ⟨k, hk_eq⟩ := hprod_odd
      have : d.aa * d.bigA = 2 * k := by omega
      have heq' : Even (d.aa * d.bigA) := ⟨k, by omega⟩
      exact ((Nat.even_mul ..).mp heq').resolve_right (Nat.not_even_iff_odd.mpr hAodd)

theorem threeDividesABOfThreeRough
    (d : ThreeFormData) (hA : ¬ 3 ∣ d.bigA) (hB : ¬ 3 ∣ d.bigB)
    (hR : ¬ 3 ∣ d.rr) : 3 ∣ d.aa * d.bb := by
  have h1 : d.rr + 1 = 2 * d.bb * d.bigB := d.hplus
  have h2 : d.rr - 1 = 2 * d.aa * d.bigA := d.hminus
  -- Key: one of (rr-1) or (rr+1) is divisible by 3
  have hmod : d.rr % 3 = 1 ∨ d.rr % 3 = 2 := by
    omega
  rcases hmod with hr1 | hr2
  · -- Case: rr ≡ 1 (mod 3), so rr - 1 ≡ 0 (mod 3), meaning 3 ∣ 2 * aa * bigA
    have hdiv : 3 ∣ 2 * d.aa * d.bigA := by
      have : 3 ∣ d.rr - 1 := by omega
      omega
    have h3 : Nat.Prime 3 := by decide
    have := h3.dvd_mul.mp hdiv
    rcases this with h | h
    · -- 3 ∣ 2 * d.aa, but 3 ∤ 2, so 3 ∣ d.aa
      exact dvd_mul_of_dvd_left (by omega : 3 ∣ d.aa) _
    · exact absurd h hA
  · -- Case: rr ≡ 2 (mod 3), so rr + 1 ≡ 0 (mod 3), meaning 3 ∣ 2 * bb * bigB
    have hdiv : 3 ∣ 2 * d.bb * d.bigB := by
      have : 3 ∣ d.rr + 1 := by omega
      omega
    have h3 : Nat.Prime 3 := by decide
    have := h3.dvd_mul.mp hdiv
    rcases this with h | h
    · -- 3 ∣ 2 * d.bb, but 3 ∤ 2, so 3 ∣ d.bb
      exact dvd_mul_of_dvd_right (by omega : 3 ∣ d.bb) _
    · exact absurd h hB

theorem allLinearSolutions
    {a b A B A0 B0 : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hcop : IsCoprime a b) (h : b * B - a * A = 1)
    (h0 : b * B0 - a * A0 = 1) :
    ∃ k : ℤ, A = A0 + b * k ∧ B = B0 + a * k := by
  have key : b * (B - B0) = a * (A - A0) := by linarith
  have hdiv1 : a ∣ (B - B0) := by
    have : a ∣ (B - B0) * b := by rw [mul_comm]; exact key ▸ dvd_mul_right a (A - A0)
    exact hcop.dvd_of_dvd_mul_right this
  have hdiv2 : b ∣ (A - A0) := by
    have : b ∣ a * (A - A0) := key ▸ dvd_mul_right b (B - B0)
    rw [mul_comm] at this
    exact IsCoprime.dvd_of_dvd_mul_right hcop.symm this
  obtain ⟨k1, hk1⟩ := hdiv1
  obtain ⟨k2, hk2⟩ := hdiv2
  have hk_eq : k1 = k2 := by
    have : b * (a * k1) = a * (b * k2) := by rw [← hk1, ← hk2, key]
    have hab : a * b ≠ 0 := mul_ne_zero (ne_of_gt ha) (ne_of_gt hb)
    nlinarith [mul_pos ha hb]
  use k2
  rw [hk_eq] at hk1
  constructor
  · linarith
  · linarith

theorem roughFormParameterisation {a b A A0 k R : ℤ}
    (hA : A = A0 + b * k) (hR : R = 2 * a * A + 1) :
    R = 2 * a * b * k + (2 * a * A0 + 1) := by
  rw [hA] at hR
  nlinarith

def form1 (A0 b k : ℤ) : ℤ := A0 + b * k
def form2 (B0 a k : ℤ) : ℤ := B0 + a * k
def form3 (A0 a b k : ℤ) : ℤ := 2 * a * b * k + 2 * a * A0 + 1

noncomputable def forbiddenRoots (p : ℕ) [NeZero p]
    (A0 B0 a b : ZMod p) : Finset (ZMod p) :=
  Finset.univ.filter fun k =>
    A0 + b * k = 0 ∨ B0 + a * k = 0 ∨ 2 * a * b * k + 2 * a * A0 + 1 = 0

theorem localRootsAtTwo {A0 B0 a b : ZMod 2}
    (hlin : b * B0 - a * A0 = 1) (hab : a * b = 0) :
    (forbiddenRoots 2 A0 B0 a b).card = 1 := by
  revert A0 B0 a b
  decide

theorem localRootsAtThreeInadmissible {A0 B0 a b : ZMod 3}
    (ha : a ≠ 0) (hb : b ≠ 0) (hlin : b * B0 - a * A0 = 1) :
    forbiddenRoots 3 A0 B0 a b = Finset.univ := by
  revert A0 B0 a b
  decide

theorem localRootsAtThreeAdmissible {A0 B0 a b : ZMod 3}
    (hab : a * b = 0) (hlin : b * B0 - a * A0 = 1) :
    (forbiddenRoots 3 A0 B0 a b).card = 1 := by
  revert A0 B0 a b
  decide

theorem localRootsDividingAB {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {A0 B0 a b : ZMod p} (hab : a * b = 0)
    (hlin : b * B0 - a * A0 = 1) :
    (forbiddenRoots p A0 B0 a b).card = 1 := by
  rw [mul_eq_zero] at hab
  cases hab with
  | inl ha =>
    -- Case a = 0: then b * B0 = 1, so b ≠ 0
    have hb : b ≠ 0 := by
      intro hb0
      simp [ha, hb0] at hlin
    have hB0 : B0 ≠ 0 := by
      intro hB0'
      rw [ha, hB0'] at hlin
      simp at hlin
    rw [ha]
    simp only [forbiddenRoots]
    have hsimp : ∀ k : ZMod p, (A0 + b * k = 0 ∨ B0 + 0 * k = 0 ∨ 2 * 0 * b * k + 2 * 0 * A0 + 1 = 0) ↔ A0 + b * k = 0 := by
      intro k
      constructor
      · intro h
        rcases h with h | h | h
        all_goals first | solve_by_elim | simp_all
      · intro h
        exact Or.inl h
    rw [Finset.filter_congr (fun k _ => hsimp k)]
    have hset : (Finset.univ.filter fun k => A0 + b * k = 0) = {(-A0) / b} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        exact eq_div_of_mul_eq hb (by linear_combination h)
      · intro h
        rw [h]
        field_simp
        ring
    rw [hset, Finset.card_singleton]
  | inr hb =>
    -- Case b = 0: then -a * A0 = 1, so a ≠ 0
    have ha : a ≠ 0 := by
      intro ha0
      simp [ha0, hb] at hlin
    have hA0 : A0 ≠ 0 := by
      intro hA0'
      rw [hb, hA0'] at hlin
      simp at hlin
    rw [hb]
    have haA0 : a * A0 = -1 := by simp [hb] at hlin; linear_combination -hlin
    have h2aA0 : 2 * a * A0 + 1 ≠ 0 := by
      rw [show 2 * a * A0 = 2 * (a * A0) by ring, haA0]
      norm_num
    simp only [forbiddenRoots]
    have hsimp : ∀ k : ZMod p, (A0 + 0 * k = 0 ∨ B0 + a * k = 0 ∨ 2 * a * 0 * k + 2 * a * A0 + 1 = 0) ↔ B0 + a * k = 0 := by
      intro k
      constructor
      · intro h
        rcases h with h | h | h
        all_goals first | solve_by_elim | simp_all
      · intro h
        exact Or.inr (Or.inl h)
    rw [Finset.filter_congr (fun k _ => hsimp k)]
    have hset : (Finset.univ.filter fun k => B0 + a * k = 0) = {(-B0) / a} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro h
        exact eq_div_of_mul_eq ha (by linear_combination h)
      · intro h
        rw [h]
        field_simp
        ring
    rw [hset, Finset.card_singleton]

theorem localRootsGeneric {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    {A0 B0 a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0)
    (hlin : b * B0 - a * A0 = 1) :
    (forbiddenRoots p A0 B0 a b).card = 3 := by
  -- Define the three solutions
  have hp2 : (2 : ZMod p) ≠ 0 := by
    have hp2' : 2 < p := lt_of_lt_of_le (by norm_num : 2 < 5) hp
    have h : ((2 : ℕ) : ZMod p).val = 2 := by
      rw [ZMod.val_natCast]; exact Nat.mod_eq_of_lt hp2'
    have hne : ((2 : ℕ) : ZMod p).val ≠ 0 := by rw [h]; norm_num
    have := (ZMod.val_eq_zero ((2 : ℕ) : ZMod p))
    simp_all
  -- The three solutions
  let k1 : ZMod p := -A0 / b
  let k2 : ZMod p := -B0 / a
  let k3 : ZMod p := -(2 * a * A0 + 1) / (2 * a * b)
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  have h2ab : 2 * a * b ≠ 0 := by
    have : (2 : ZMod p) * a * b = (2 : ZMod p) * (a * b) := by ring
    rw [this]
    exact mul_ne_zero hp2 hab
  -- Show forbiddenRoots = {k1, k2, k3}
  have heq : forbiddenRoots p A0 B0 a b = {k1, k2, k3} := by
    ext k
    simp only [forbiddenRoots, Finset.mem_filter, Finset.mem_univ, true_and,
               Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h1 | h2 | h3)
      · left
        have hk : k = -A0 / b := by
          rw [eq_div_iff hb]
          rw [mul_comm]
          linear_combination h1
        rw [hk]
      · right; left
        have hk : k = -B0 / a := by
          rw [eq_div_iff ha]
          rw [mul_comm]
          linear_combination h2
        rw [hk]
      · right; right
        have hk : k = -(2 * a * A0 + 1) / (2 * a * b) := by
          rw [eq_div_iff h2ab]
          rw [mul_comm]
          linear_combination h3
        rw [hk]
    · rintro (rfl | rfl | rfl)
      · left
        simp [k1]
        field_simp [hb]
        ring
      · right; left
        simp [k2]
        field_simp [ha]
        ring
      · right; right
        simp [k3]
        field_simp [h2ab]
        ring
  -- Show k1, k2, k3 are distinct
  have hne12 : k1 ≠ k2 := by
    intro heq
    -- k1 = k2 means -A0/b = -B0/a, so a*A0 = b*B0
    have heq' : -A0 / b = -B0 / a := heq
    rw [div_eq_div_iff hb ha] at heq'
    -- heq' : (-A0) * a = (-B0) * b
    -- => -a * A0 = -b * B0 => a * A0 = b * B0
    have h1 : a * A0 = b * B0 := by linear_combination -heq'
    -- From hlin: b * B0 - a * A0 = 1, but h1 gives b * B0 - a * A0 = 0
    have : b * B0 - a * A0 = 0 := by linear_combination -h1
    rw [hlin] at this
    exact one_ne_zero this
  have hne13 : k1 ≠ k3 := by
    intro heq
    -- k1 = k3 means -A0/b = -(2*a*A0 + 1)/(2*a*b)
    have heq' : -A0 / b = -(2 * a * A0 + 1) / (2 * a * b) := heq
    rw [div_eq_div_iff hb h2ab] at heq'
    -- heq' : (-A0) * (2 * a * b) = -(2 * a * A0 + 1) * b
    -- => -2*a*b*A0 = -(2*a*A0 + 1)*b
    -- Rearranging: 2*a*b*A0 - (2*a*A0 + 1)*b = 0
    -- => b*(2*a*A0 - 2*a*A0 - 1) = 0
    -- => b*(-1) = 0 => b = 0 (contradiction) or ... wait let me compute more carefully
    -- -A0 * (2*a*b) = -(2*a*A0 + 1) * b
    -- => -2*a*b*A0 = -2*a*A0*b - b
    -- => 0 = -b
    -- => b = 0
    have h1 : b = 0 := by linear_combination heq'
    exact hb h1
  have hne23 : k2 ≠ k3 := by
    intro heq
    -- k2 = k3 means -B0/a = -(2*a*A0 + 1)/(2*a*b)
    have heq' : -B0 / a = -(2 * a * A0 + 1) / (2 * a * b) := heq
    rw [div_eq_div_iff ha h2ab] at heq'
    -- heq' : (-B0) * (2 * a * b) = -(2 * a * A0 + 1) * a
    -- Using hlin: b * B0 = a * A0 + 1
    -- => -2*a*b*B0 = -(2*a*A0 + 1)*a
    -- => 2*a*b*B0 = (2*a*A0 + 1)*a
    -- => 2*b*B0 = 2*a*A0 + 1 (dividing by a ≠ 0)
    -- Using b*B0 = a*A0 + 1: 2*(a*A0 + 1) = 2*a*A0 + 1
    -- => 2*a*A0 + 2 = 2*a*A0 + 1 => 2 = 1
    have h1 : -(B0 * (2 * a * b)) = -(2 * a * A0 + 1) * a := by linear_combination heq'
    -- From h1 and hlin: h1 + 2*a*hlin gives a * 2 = 0
    -- From h1 + a*hlin: a*b*B0 = a²*A0, so b*B0 = a*A0 (since a ≠ 0)
    -- But hlin says b*B0 - a*A0 = 1, contradiction
    have eq1 : -(B0 * (2 * a * b)) = -(2 * a * A0 + 1) * a := h1
    have eq2 : b * B0 - a * A0 = 1 := hlin
    -- Derive a = 0 directly from eq1 and eq2
    -- eq1 says: -2abB0 = -2a²A0 - a
    -- eq2 * 2a says: 2abB0 = 2a²A0 + 2a
    -- Adding: 0 = a
    have ha0 : a = 0 := by
      have h : 0 = a := by linear_combination eq1 + 2 * a * eq2
      exact h.symm
    exact absurd ha0 ha
  rw [heq]
  have hnot3 : k3 ∉ ({k1, k2} : Finset (ZMod p)) := by
    simp [Finset.mem_insert, Finset.mem_singleton, hne23.symm, hne13.symm]
  have hnot2 : k2 ∉ ({k1} : Finset (ZMod p)) := by
    simp [Finset.mem_singleton, hne12.symm]
  simp_all [Finset.card]

end Erdos461A
