/-
# Gate1B / R11 / Frontier : dense support, and the well-factorability firewall

Append-only module of the minimal-gap-kernel delta.

**Factor-support feasibility** of a modulus `d` at level `Q`:

```
FactorSupport d Q  :  ∀ Q₁,Q₂ ≥ 1 with Q₁·Q₂ = Q, ∃ a | d with a ≤ Q₁ and d/a ≤ Q₂.
```

Kernel-proved here:

* the **exact characterisation** `FactorSupport d Q ↔ GapBound d Q`, where `GapBound` is the
  consecutive-divisor gap condition `d · next(t) ≤ Q · t` for every divisor `t < d`;
* `FactorSupport d Q → Fgap d ≤ Q` (the Schinzel–Szekeres inequality in the direction that is
  proved here);
* a concrete instance: `Fgap 6 = 12` and `FactorSupport 6 12`, i.e. the converse holds at the
  exact Schinzel–Szekeres value in this example.

The remaining classical direction (`Fgap d ≤ Q → FactorSupport d Q`, equivalently
`Fgap d = d · G(d)`) is recorded as an **explicit theorem interface**
`SchinzelSzekeresSupport` and is *never* inhabited and *never* an axiom.

**Firewall.**  Factor-support feasibility is *not* coefficient well-factorability: a complete
signed coefficient chart of rank two is kernel-proved not to be a single product weight.
-/
import Gate1B.R11.Frontier.SchinzelSzekeresKernel

namespace Gate1B.R11.Frontier

open Finset

/-! ## 1. Consecutive divisors -/

/-- The least divisor of `d` strictly above `t` (junk value `0` if there is none). -/
def nextDiv (d t : ℕ) : ℕ :=
  if h : ({s ∈ d.divisors | t < s}).Nonempty then ({s ∈ d.divisors | t < s}).min' h else 0

theorem nextDiv_nonempty {d t : ℕ} (hd : d ≠ 0) (htd : t < d) :
    ({s ∈ d.divisors | t < s}).Nonempty :=
  ⟨d, Finset.mem_filter.2 ⟨Nat.mem_divisors_self d hd, htd⟩⟩

theorem nextDiv_dvd {d t : ℕ} (hd : d ≠ 0) (htd : t < d) : nextDiv d t ∣ d := by
  rw [nextDiv, dif_pos (nextDiv_nonempty hd htd)]
  exact Nat.dvd_of_mem_divisors
    (Finset.mem_filter.1 (Finset.min'_mem _ (nextDiv_nonempty hd htd))).1

theorem lt_nextDiv {d t : ℕ} (hd : d ≠ 0) (htd : t < d) : t < nextDiv d t := by
  rw [nextDiv, dif_pos (nextDiv_nonempty hd htd)]
  exact (Finset.mem_filter.1 (Finset.min'_mem _ (nextDiv_nonempty hd htd))).2

theorem nextDiv_le {d t s : ℕ} (hd : d ≠ 0) (htd : t < d) (hs : s ∣ d) (hts : t < s) :
    nextDiv d t ≤ s := by
  rw [nextDiv, dif_pos (nextDiv_nonempty hd htd)]
  refine Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hs, hd⟩, hts⟩)

/-! ## 2. Factor support and the gap bound -/

/-- Factor-support feasibility at level `Q` (real factorisations, as in well-factorability). -/
def FactorSupport (d : ℕ) (Q : ℝ) : Prop :=
  ∀ Q₁ Q₂ : ℝ, 1 ≤ Q₁ → 1 ≤ Q₂ → Q₁ * Q₂ = Q →
    ∃ a, a ∣ d ∧ (a : ℝ) ≤ Q₁ ∧ ((d / a : ℕ) : ℝ) ≤ Q₂

/-- The consecutive-divisor gap bound `d · next(t) ≤ Q · t`. -/
def GapBound (d : ℕ) (Q : ℝ) : Prop :=
  ∀ t, t ∣ d → t < d → (d : ℝ) * (nextDiv d t : ℝ) ≤ Q * (t : ℝ)

theorem factorSupport_of_gapBound {d : ℕ} (hd : d ≠ 0) {Q : ℝ} (h : GapBound d Q) :
    FactorSupport d Q := by
  classical
  intro Q₁ Q₂ h1 h2 hQ
  have hSne : (Finset.filter (fun a : ℕ => (a : ℝ) ≤ Q₁) d.divisors).Nonempty := by
    refine ⟨1, Finset.mem_filter.2 ⟨Nat.one_mem_divisors.2 hd, ?_⟩⟩
    simpa using h1
  obtain ⟨a, haS, hamax⟩ :
      ∃ a ∈ Finset.filter (fun a : ℕ => (a : ℝ) ≤ Q₁) d.divisors,
        ∀ b ∈ Finset.filter (fun a : ℕ => (a : ℝ) ≤ Q₁) d.divisors, b ≤ a :=
    ⟨_, Finset.max'_mem _ hSne, fun b hb => Finset.le_max' _ b hb⟩
  have had : a ∣ d := Nat.dvd_of_mem_divisors (Finset.mem_filter.1 haS).1
  have haQ : (a : ℝ) ≤ Q₁ := (Finset.mem_filter.1 haS).2
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos had (Nat.pos_of_ne_zero hd)
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  refine ⟨a, had, haQ, ?_⟩
  by_cases hae : a = d
  · subst hae
    rw [Nat.div_self ha0]
    simpa using h2
  · have hlt : a < d := lt_of_le_of_ne (Nat.le_of_dvd (Nat.pos_of_ne_zero hd) had) hae
    have hmax : ∀ s, s ∣ d → (s : ℝ) ≤ Q₁ → s ≤ a := fun s hs hsQ =>
      hamax s (Finset.mem_filter.2 ⟨Nat.mem_divisors.2 ⟨hs, hd⟩, hsQ⟩)
    have hQ1lt : Q₁ < (nextDiv d a : ℝ) := by
      by_contra hcon
      push_neg at hcon
      have := hmax (nextDiv d a) (nextDiv_dvd hd hlt) hcon
      have := lt_nextDiv hd hlt
      omega
    have hkey : (d : ℝ) * (nextDiv d a : ℝ) ≤ Q * (a : ℝ) := h a had hlt
    have hQ1pos : (0 : ℝ) < Q₁ := lt_of_lt_of_le zero_lt_one h1
    have hcast : ((d / a : ℕ) : ℝ) = (d : ℝ) / (a : ℝ) := by
      rw [Nat.cast_div had (ne_of_gt haR)]
    rw [hcast, div_le_iff₀ haR]
    nlinarith [hkey, hQ1lt, hdR, haR, hQ1pos]

theorem gapBound_of_factorSupport {d : ℕ} (hd : d ≠ 0) {Q : ℝ} (hQ : 1 ≤ Q)
    (h : FactorSupport d Q) : GapBound d Q := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hd
  -- first: `d ≤ Q`
  have hdQ : (d : ℝ) ≤ Q := by
    obtain ⟨a, had, haQ, hda⟩ := h Q 1 hQ le_rfl (mul_one Q)
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos had (Nat.pos_of_ne_zero hd)
    have hd1 : d / a ≤ 1 := by exact_mod_cast hda
    have hge : 1 ≤ d / a := (Nat.one_le_div_iff ha0).2 (Nat.le_of_dvd
      (Nat.pos_of_ne_zero hd) had)
    have heq : d / a = 1 := by omega
    have hadEq : a = d := by
      have h2 : d / a * a = d := Nat.div_mul_cancel had
      rw [heq, one_mul] at h2
      exact h2
    rw [← hadEq]
    exact haQ
  intro t htd htlt
  by_contra hcon
  push_neg at hcon
  set t' := nextDiv d t with ht'
  have ht'd : t' ∣ d := nextDiv_dvd hd htlt
  have htt' : t < t' := lt_nextDiv hd htlt
  have ht0 : 0 < t := Nat.pos_of_dvd_of_pos htd (Nat.pos_of_ne_zero hd)
  have htR : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht0
  have htRpos : (0 : ℝ) < (t : ℝ) := by linarith
  have hQpos : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have ht'R : (t : ℝ) < (t' : ℝ) := by exact_mod_cast htt'
  have htltR : (t : ℝ) < (d : ℝ) := by exact_mod_cast htlt
  -- the critical scale
  set c := Q * (t : ℝ) / (d : ℝ) with hc
  have hclt' : c < (t' : ℝ) := by
    rw [hc, div_lt_iff₀ hdR]; linarith [hcon]
  have hcQ : c < Q := by
    rw [hc, div_lt_iff₀ hdR]
    nlinarith
  have hct : (t : ℝ) ≤ c := by
    rw [hc, le_div_iff₀ hdR]
    nlinarith
  set Q₁ := (c + min (t' : ℝ) Q) / 2 with hQ₁
  have hQ₁gt : c < Q₁ := by
    rw [hQ₁]
    have : c < min (t' : ℝ) Q := lt_min hclt' hcQ
    linarith
  have hQ₁lt : Q₁ < min (t' : ℝ) Q := by
    rw [hQ₁]
    have : c < min (t' : ℝ) Q := lt_min hclt' hcQ
    linarith
  have hQ₁one : 1 ≤ Q₁ := by linarith [hct, htR, hQ₁gt]
  have hQ₁Q : Q₁ ≤ Q := le_of_lt (lt_of_lt_of_le hQ₁lt (min_le_right _ _))
  have hQ₁pos : (0 : ℝ) < Q₁ := lt_of_lt_of_le zero_lt_one hQ₁one
  have hQ₂one : 1 ≤ Q / Q₁ := (one_le_div hQ₁pos).2 hQ₁Q
  obtain ⟨a, had, haQ, hda⟩ := h Q₁ (Q / Q₁) hQ₁one hQ₂one (by field_simp)
  have ha0 : 0 < a := Nat.pos_of_dvd_of_pos had (Nat.pos_of_ne_zero hd)
  have haR : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha0
  have hat : a ≤ t := by
    by_contra hcon2
    push_neg at hcon2
    have := nextDiv_le hd htlt had hcon2
    have haR' : (a : ℝ) < (t' : ℝ) := lt_of_le_of_lt haQ (lt_of_lt_of_le hQ₁lt (min_le_left _ _))
    have : (t' : ℕ) ≤ a := this
    have : (t' : ℝ) ≤ (a : ℝ) := by exact_mod_cast this
    linarith
  have hcast : ((d / a : ℕ) : ℝ) = (d : ℝ) / (a : ℝ) := by
    rw [Nat.cast_div had (ne_of_gt haR)]
  rw [hcast] at hda
  have hatR : (a : ℝ) ≤ (t : ℝ) := by exact_mod_cast hat
  have hlow : (d : ℝ) / (t : ℝ) ≤ (d : ℝ) / (a : ℝ) :=
    div_le_div_of_nonneg_left (le_of_lt hdR) haR hatR
  have hup : (d : ℝ) / (a : ℝ) ≤ Q / Q₁ := hda
  have : (d : ℝ) / (t : ℝ) ≤ Q / Q₁ := le_trans hlow hup
  rw [div_le_div_iff₀ htRpos hQ₁pos] at this
  have : Q₁ ≤ Q * (t : ℝ) / (d : ℝ) := by
    rw [le_div_iff₀ hdR]; nlinarith
  rw [← hc] at this
  linarith [hQ₁gt]

/-- **Dense support characterisation.**  Factor-support feasibility at level `Q` is exactly the
consecutive-divisor gap bound. -/
theorem factorSupport_iff_gapBound {d : ℕ} (hd : d ≠ 0) {Q : ℝ} (hQ : 1 ≤ Q) :
    FactorSupport d Q ↔ GapBound d Q :=
  ⟨gapBound_of_factorSupport hd hQ, factorSupport_of_gapBound hd⟩

/-! ## 3. From factor support to `Fgap` -/

/-- The least prime of `v` never exceeds the divisor successor of `d/v`. -/
theorem minFac_le_nextDiv {d v : ℕ} (hd : d ≠ 0) (hvd : v ∣ d) (hv1 : 1 < v) :
    v.minFac ≤ nextDiv d (d / v) := by
  have ha : d / v ∣ d := Nat.div_dvd_of_dvd hvd
  have hlt : d / v < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd) hv1
  have ha0 : 0 < d / v := Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero hd)
  have ht' : d / v < nextDiv d (d / v) := lt_nextDiv hd hlt
  set p := v.minFac with hp
  by_cases hcase : p ≤ d / v
  · omega
  · push_neg at hcase
    by_contra hcon
    push_neg at hcon
    -- `nextDiv` is then coprime to `v`, hence divides `d/v`, contradiction
    have hcop : Nat.Coprime (nextDiv d (d / v)) v := by
      rw [Nat.coprime_iff_gcd_eq_one]
      by_contra hne
      obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hne
      have hqt : q ∣ nextDiv d (d / v) := hqdvd.trans (Nat.gcd_dvd_left _ _)
      have hqv : q ∣ v := hqdvd.trans (Nat.gcd_dvd_right _ _)
      have h1 : p ≤ q := Nat.minFac_le_of_dvd hq.two_le hqv
      have h2 : q ≤ nextDiv d (d / v) :=
        Nat.le_of_dvd (by omega) hqt
      omega
    have hdvd : nextDiv d (d / v) ∣ (d / v) * v := by
      rw [Nat.div_mul_cancel hvd]; exact nextDiv_dvd hd hlt
    have : nextDiv d (d / v) ∣ d / v := (Nat.Coprime.dvd_of_dvd_mul_right hcop) hdvd
    have := Nat.le_of_dvd ha0 this
    omega

/-- **Factor support implies the Schinzel–Szekeres bound.** -/
theorem Fgap_le_of_factorSupport {d : ℕ} (hd : d ≠ 0) {Q : ℝ} (hQ : 1 ≤ Q)
    (h : FactorSupport d Q) : (Fgap d : ℝ) ≤ Q := by
  have hgap : GapBound d Q := gapBound_of_factorSupport hd hQ h
  have hQ0 : (0 : ℝ) ≤ Q := le_trans zero_le_one hQ
  have hfloor : Fgap d ≤ ⌊Q⌋₊ := by
    refine (Fgap_le_iff hd (Nat.le_floor (by exact_mod_cast hQ))).2 fun v hvd hv1 => ?_
    have hvR : (v : ℝ) * (v.minFac : ℝ) ≤ Q := by
      have ha : d / v ∣ d := Nat.div_dvd_of_dvd hvd
      have hlt : d / v < d := Nat.div_lt_self (Nat.pos_of_ne_zero hd) hv1
      have ha0 : 0 < d / v := Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero hd)
      have hkey : (d : ℝ) * (nextDiv d (d / v) : ℝ) ≤ Q * ((d / v : ℕ) : ℝ) := hgap _ ha hlt
      have hdeq : (d : ℝ) = ((d / v : ℕ) : ℝ) * (v : ℝ) := by
        have : (d / v) * v = d := Nat.div_mul_cancel hvd
        exact_mod_cast this.symm
      have hminle : (v.minFac : ℝ) ≤ (nextDiv d (d / v) : ℝ) := by
        exact_mod_cast minFac_le_nextDiv hd hvd hv1
      have haR : (0 : ℝ) < ((d / v : ℕ) : ℝ) := by exact_mod_cast ha0
      have hvpos : (0 : ℝ) < (v : ℝ) := by
        have : 0 < v := by omega
        exact_mod_cast this
      nlinarith [hkey, hminle, haR, hvpos]
    exact Nat.le_floor (by exact_mod_cast hvR)
  calc (Fgap d : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hfloor
    _ ≤ Q := Nat.floor_le hQ0

/-! ## 4. The classical converse, as an interface -/

/-- The remaining classical Schinzel–Szekeres direction, recorded as an **explicit theorem
interface**.  Nothing in this layer inhabits it, and it is not an axiom. -/
def SchinzelSzekeresSupport : Prop :=
  ∀ (d : ℕ) (Q : ℝ), d ≠ 0 → (Fgap d : ℝ) ≤ Q → FactorSupport d Q

/-- If the interface is supplied, the characterisation becomes a biconditional in terms of
`Fgap`; this is the only way the interface is ever used. -/
theorem factorSupport_iff_Fgap_le (hSS : SchinzelSzekeresSupport) {d : ℕ} (hd : d ≠ 0)
    {Q : ℝ} (hQ : 1 ≤ Q) : FactorSupport d Q ↔ (Fgap d : ℝ) ≤ Q :=
  ⟨Fgap_le_of_factorSupport hd hQ, hSS d Q hd⟩

/-! ## 5. A concrete instance of the converse -/

theorem Fgap_six : Fgap 6 = 12 := by
  have m2 : Nat.minFac 2 = 2 := Nat.Prime.minFac_eq (by norm_num)
  have m3 : Nat.minFac 3 = 3 := Nat.Prime.minFac_eq (by norm_num)
  have m6 : Nat.minFac 6 = 2 := by norm_num
  refine le_antisymm ?_ ?_
  · refine (Fgap_le_iff (by norm_num) (by norm_num)).2 fun v hv h1 => ?_
    have hmem : v ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨hv, by norm_num⟩
    have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [h6] at hmem
    fin_cases hmem
    · omega
    · rw [m2]; omega
    · rw [m3]; omega
    · rw [m6]
  · have h := le_Fgap (d := 6) (v := 6) (by norm_num) dvd_rfl (by norm_num)
    rw [m6] at h
    omega

theorem nextDiv_six_one : nextDiv 6 1 = 2 := by decide

theorem nextDiv_six_two : nextDiv 6 2 = 3 := by decide

theorem nextDiv_six_three : nextDiv 6 3 = 6 := by decide

/-- At `d = 6` the converse direction holds at the exact Schinzel–Szekeres value `Q = Fgap 6`. -/
theorem factorSupport_six : FactorSupport 6 12 := by
  refine factorSupport_of_gapBound (by norm_num) ?_
  intro t ht htlt
  have hmem : t ∈ Nat.divisors 6 := Nat.mem_divisors.2 ⟨ht, by norm_num⟩
  have h6 : Nat.divisors 6 = {1, 2, 3, 6} := by decide
  rw [h6] at hmem
  fin_cases hmem
  · rw [nextDiv_six_one]; norm_num
  · rw [nextDiv_six_two]; norm_num
  · rw [nextDiv_six_three]; norm_num
  · omega

/-! ## 6. Well-factorability firewall -/

/-- A two-by-two coefficient chart is a *product weight* if it factors as `f(i)·g(j)`. -/
def IsProductWeight (c : Fin 2 → Fin 2 → ℝ) : Prop :=
  ∃ f g : Fin 2 → ℝ, ∀ i j, c i j = f i * g j

/-- The complete signed coefficient chart of the countermodel (rank two). -/
def signedChart : Fin 2 → Fin 2 → ℝ := ![![1, 1], ![1, -1]]

/-- **Countermodel.**  The complete dense signed coefficient need not be a single
well-factorable (product) weight: the rank-two chart is not of product form. -/
theorem signedChart_not_product : ¬ IsProductWeight signedChart := by
  rintro ⟨f, g, h⟩
  have h00 := h 0 0
  have h01 := h 0 1
  have h10 := h 1 0
  have h11 := h 1 1
  simp [signedChart] at h00 h01 h10 h11
  nlinarith [h00, h01, h10, h11]

/-- **Firewall.**  Factor-support feasibility of the modulus and well-factorability of the
complete signed coefficient are different statements: the first holds in the example, the
second fails. -/
theorem factor_support_ne_well_factorable :
    FactorSupport 6 12 ∧ ¬ IsProductWeight signedChart :=
  ⟨factorSupport_six, signedChart_not_product⟩

end Gate1B.R11.Frontier
