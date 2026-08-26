import Mathlib

/-!
# Exact Vaughan packet algebra

This file proves only finite/convolution algebra.  No discrepancy estimate is
asserted.  Arithmetic functions are Mathlib's positive-natural arithmetic
functions (forced to vanish at zero).
-/

namespace TwinPrimeProject

open scoped BigOperators
open ArithmeticFunction

/-- Cut an arithmetic function off at `Y`. -/
def afTruncLE (Y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ Y then f n else 0
  map_zero' := by simp

/-- The complementary strict truncation. -/
def afTruncGT (Y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f - afTruncLE Y f

theorem af_truncation_decomposition (Y : ℕ) (f : ArithmeticFunction ℝ) :
    f = afTruncLE Y f + afTruncGT Y f := by
  simp [afTruncGT]

/-- The exact Vaughan identity in the arithmetic-function convolution ring. -/
theorem exactVaughanIdentity (U V : ℕ) :
    vonMangoldt =
      afTruncLE V vonMangoldt
      + afTruncLE U (↑moebius : ArithmeticFunction ℝ) * log
      - afTruncLE U (↑moebius : ArithmeticFunction ℝ) * afTruncLE V vonMangoldt *
          (↑zeta : ArithmeticFunction ℝ)
      + afTruncGT U (↑moebius : ArithmeticFunction ℝ) * afTruncGT V vonMangoldt *
          (↑zeta : ArithmeticFunction ℝ) := by
  have hmu :
      (afTruncLE U (↑moebius : ArithmeticFunction ℝ) +
          afTruncGT U (↑moebius : ArithmeticFunction ℝ)) *
          (↑zeta : ArithmeticFunction ℝ) = 1 := by
    rw [← af_truncation_decomposition]
    exact coe_moebius_mul_coe_zeta
  have hlog :
      (afTruncLE V vonMangoldt + afTruncGT V vonMangoldt) *
          (↑zeta : ArithmeticFunction ℝ) = log := by
    rw [← af_truncation_decomposition]
    exact vonMangoldt_mul_zeta
  calc
    vonMangoldt = afTruncLE V vonMangoldt + afTruncGT V vonMangoldt :=
      af_truncation_decomposition V vonMangoldt
    _ = afTruncLE V vonMangoldt + 1 * afTruncGT V vonMangoldt := by ring
    _ = afTruncLE V vonMangoldt +
        ((afTruncLE U (↑moebius : ArithmeticFunction ℝ) +
          afTruncGT U (↑moebius : ArithmeticFunction ℝ)) *
          (↑zeta : ArithmeticFunction ℝ)) * afTruncGT V vonMangoldt := by rw [hmu]
    _ = _ := by rw [← hlog]; ring

/-- A finite shifted pairing.  `K` is an explicit support cutoff. -/
def shiftedPairing (K : ℕ) (f : ArithmeticFunction ℝ) (c : ℕ → ℝ) : ℝ :=
  ∑ N ∈ Finset.range (K + 1), f N * c (N - 2)

noncomputable def VaughanP1 (K U : ℕ) (c : ℕ → ℝ) : ℝ :=
  shiftedPairing K (afTruncLE U (↑moebius : ArithmeticFunction ℝ) * log) c

noncomputable def VaughanP2 (K U V : ℕ) (c : ℕ → ℝ) : ℝ :=
  shiftedPairing K
    (afTruncLE U (↑moebius : ArithmeticFunction ℝ) * afTruncLE V vonMangoldt *
      (↑zeta : ArithmeticFunction ℝ)) c

noncomputable def VaughanP3 (K U V : ℕ) (c : ℕ → ℝ) : ℝ :=
  shiftedPairing K
    (afTruncGT U (↑moebius : ArithmeticFunction ℝ) * afTruncGT V vonMangoldt *
      (↑zeta : ArithmeticFunction ℝ)) c

/-- Pairing is linear in the arithmetic-function input. -/
theorem shiftedPairing_add (K : ℕ) (f g : ArithmeticFunction ℝ) (c : ℕ → ℝ) :
    shiftedPairing K (f + g) c = shiftedPairing K f c + shiftedPairing K g c := by
  simp [shiftedPairing, Finset.sum_add_distrib, add_mul]

theorem shiftedPairing_sub (K : ℕ) (f g : ArithmeticFunction ℝ) (c : ℕ → ℝ) :
    shiftedPairing K (f - g) c = shiftedPairing K f c - shiftedPairing K g c := by
  unfold shiftedPairing
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  rw [ZeroHom.sub_apply, sub_mul]

/-- A coefficient supported on shifted arguments whose corresponding `N` lies
strictly above `V`. -/
def ShiftedSupportAbove (V : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ N, N ≤ V → c (N - 2) = 0

lemma truncatedLambda_pairing_zero (K V : ℕ) (c : ℕ → ℝ)
    (hc : ShiftedSupportAbove V c) :
    shiftedPairing K (afTruncLE V vonMangoldt) c = 0 := by
  apply Finset.sum_eq_zero
  intro N hN
  by_cases h : N ≤ V
  · simp [afTruncLE, hc N h]
  · simp [afTruncLE, h]

/-- Exact finite `P1-P2+P3` decomposition.  The packet definitions above are
finite pairings of the displayed Dirichlet convolutions, hence retain the
`log ((n+2)/d)` weight in `P1`; no separated P1 main term is asserted. -/
theorem exactP1P2P3Decomposition (K U V : ℕ) (c : ℕ → ℝ)
    (hc : ShiftedSupportAbove V c) :
    shiftedPairing K vonMangoldt c =
      VaughanP1 K U c - VaughanP2 K U V c + VaughanP3 K U V c := by
  rw [exactVaughanIdentity U V]
  simp only [shiftedPairing_add, shiftedPairing_sub]
  rw [truncatedLambda_pairing_zero K V c hc]
  simp [VaughanP1, VaughanP2, VaughanP3]

/-- The grouped low-low modulus coefficient. -/
noncomputable def lambda2 (U V q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, if d ≤ U ∧ q / d ≤ V then
    (moebius d : ℝ) * vonMangoldt (q / d) else 0

/-- The grouped high-high modulus coefficient. -/
noncomputable def lambda3 (U V q : ℕ) : ℝ :=
  ∑ d ∈ q.divisors, if U < d ∧ V < q / d then
    (moebius d : ℝ) * vonMangoldt (q / d) else 0

/-- Low-low modulus weights are pointwise logarithmically bounded. -/
theorem lambda2_abs_le_log (U V q : ℕ) : |lambda2 U V q| ≤ Real.log q := by
  unfold lambda2
  calc |∑ d ∈ q.divisors, if d ≤ U ∧ q / d ≤ V then ↑(moebius d) * Λ (q / d) else 0|
      ≤ ∑ d ∈ q.divisors, |if d ≤ U ∧ q / d ≤ V then ↑(moebius d) * Λ (q / d) else 0| := by
        apply Finset.abs_sum_le_sum_abs
      _ ≤ ∑ d ∈ q.divisors, |↑(moebius d) * Λ (q / d)| := by
        apply Finset.sum_le_sum
        intro d _
        split_ifs with h <;> simp [abs_nonneg, mul_nonneg]
      _ = ∑ d ∈ q.divisors, |(moebius d : ℝ)| * |Λ (q / d)| := by
        apply Finset.sum_congr rfl
        intro d _
        rw [abs_mul]
      _ ≤ ∑ d ∈ q.divisors, 1 * Λ (q / d) := by
        apply Finset.sum_le_sum
        intro d _
        have h1 : |(moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast abs_moebius_le_one
        have h2 : 0 ≤ Λ (q / d) := vonMangoldt_nonneg
        have h3 : |Λ (q / d)| = Λ (q / d) := abs_of_nonneg h2
        rw [h3]
        exact mul_le_mul h1 (le_refl _) (by positivity) (by positivity)
      _ = ∑ d ∈ q.divisors, Λ (q / d) := by simp
      _ ≤ Real.log q := by
        have h := congr_arg (fun f => f q) vonMangoldt_mul_zeta
        simp only at h
        calc ∑ d ∈ q.divisors, Λ (q / d) = ∑ d ∈ q.divisors, Λ d := by
               refine Finset.sum_bij (fun d _ => q / d) ?ift ?ifi ?ifs ?ifb
               · intro d hd
                 have hdvd := Nat.dvd_of_mem_divisors hd
                 have hqne : q ≠ 0 := by
                   intro hq; simp [hq] at hd
                 exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hqne⟩
               · intro a₁ ha₁ a₂ ha₂ heq
                 have ha₁dvd := Nat.dvd_of_mem_divisors ha₁
                 have ha₂dvd := Nat.dvd_of_mem_divisors ha₂
                 have hqne : q ≠ 0 := by simp [Nat.mem_divisors] at ha₁; exact ha₁.2
                 have hqpos : 0 < q := Nat.pos_of_ne_zero hqne
                 simp only at heq
                 have h1 := Nat.div_mul_cancel ha₁dvd
                 have h2 := Nat.div_mul_cancel ha₂dvd
                 have heq' : (q / a₁) * a₁ = (q / a₂) * a₂ := by rw [h1, h2]
                 rw [heq] at heq'
                 have hqdiv_pos : 0 < q / a₂ := Nat.div_pos (Nat.le_of_dvd hqpos ha₂dvd) (Nat.pos_of_mem_divisors ha₂)
                 exact Nat.eq_of_mul_eq_mul_left hqdiv_pos heq'
               · intro a₁ ha₁
                 use q / a₁
                 refine ⟨?_, ?_⟩
                 · have hdvd := Nat.dvd_of_mem_divisors ha₁
                   have hqne : q ≠ 0 := by simp [Nat.mem_divisors] at ha₁; exact ha₁.2
                   exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hqne⟩
                 · have hdvd := Nat.dvd_of_mem_divisors ha₁
                   have hqne : q ≠ 0 := by simp [Nat.mem_divisors] at ha₁; exact ha₁.2
                   simp [Nat.div_div_self hdvd (Nat.ne_of_gt (Nat.pos_of_ne_zero hqne))]
               · intro d hd; simp
          _ = (Λ * ↑zeta) q := by
               rw [ArithmeticFunction.mul_apply]
               simp
               by_cases hq : q = 0
               · simp [hq]
               · have eq : ∀ x ∈ q.divisorsAntidiagonal, x.2 ≠ 0 := by
                   intro x hx
                   simp only [Nat.mem_divisorsAntidiagonal] at hx
                   intro h
                   simp [h] at hx
                   exact hx.2 hx.1.symm
                 rw [Finset.sum_congr rfl (fun x hx => if_neg (eq x hx))]
                 have bij : Finset.image (fun d => (d, q / d)) q.divisors = q.divisorsAntidiagonal := by
                   ext ⟨a, b⟩
                   simp [Nat.mem_divisorsAntidiagonal, Nat.mem_divisors]
                   constructor
                   · rintro ⟨⟨ha, hqne⟩, hb⟩
                     exact ⟨by rw [← hb]; exact Nat.mul_div_cancel' ha, hqne⟩
                   · rintro ⟨hab, hqne⟩
                     have ha_pos : 0 < a := Nat.pos_of_ne_zero (by intro h; simp [h] at hab; exact hqne hab.symm)
                     exact ⟨⟨hab ▸ Nat.dvd_mul_right a b, hqne⟩, Nat.div_eq_of_eq_mul_left ha_pos (hab.symm.trans (mul_comm _ _))⟩
                 rw [← bij, Finset.sum_image (fun x hx y hy hxy => by simp at hxy; exact hxy.1)]
          _ = Real.log q := h
          _ ≤ Real.log q := le_refl _

/-- High-high modulus weights are pointwise logarithmically bounded. -/
theorem lambda3_abs_le_log (U V q : ℕ) : |lambda3 U V q| ≤ Real.log q := by
  unfold lambda3
  -- Step 1: Use triangle inequality
  have h1 : |∑ d ∈ q.divisors, if U < d ∧ V < q / d then ↑(moebius d) * Λ (q / d) else 0| ≤
            ∑ d ∈ q.divisors, |if U < d ∧ V < q / d then ↑(moebius d) * Λ (q / d) else 0| :=
    Finset.abs_sum_le_sum_abs _ _
  -- Step 2: Bound each term
  have h2 : ∑ d ∈ q.divisors, |if U < d ∧ V < q / d then ↑(moebius d) * Λ (q / d) else 0| ≤
            ∑ d ∈ q.divisors, Λ (q / d) := by
    apply Finset.sum_le_sum
    intro d hd
    split_ifs with h
    · -- case: U < d ∧ V < q / d
      rw [abs_mul]
      calc |(moebius d : ℝ)| * |Λ (q / d)|
          ≤ 1 * |Λ (q / d)| := by
            apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
            simpa [← @Int.cast_le ℝ] using ArithmeticFunction.abs_moebius_le_one
        _ = |Λ (q / d)| := by ring
        _ = Λ (q / d) := by
            rw [abs_of_nonneg]
            exact ArithmeticFunction.vonMangoldt_nonneg
    · -- case: not (U < d ∧ V < q / d)
      simp
  -- Step 3: Use the identity ∑ d|q, Λ(q/d) = log q
  have h3 : ∑ d ∈ q.divisors, Λ (q / d) ≤ Real.log q := by
    -- First, reindex: ∑ d|q, Λ(q/d) = ∑ d|q, Λ(d)
    have reindex : ∑ d ∈ q.divisors, Λ (q / d) = ∑ d ∈ q.divisors, Λ d := by
      by_cases hq : q = 0
      · simp [hq]
      · symm
        apply Finset.sum_bij (fun d _ => q / d)
        · intro d hd
          rw [Nat.mem_divisors] at hd ⊢
          exact ⟨Nat.div_dvd_of_dvd hd.1, hq⟩
        · intro d₁ hd₁ d₂ hd₂ h
          rw [Nat.mem_divisors] at hd₁ hd₂
          have h₁ : d₁ ∣ q := hd₁.1
          have h₂ : d₂ ∣ q := hd₂.1
          have eq1 := Nat.div_mul_cancel h₁
          have eq2 := Nat.div_mul_cancel h₂
          rw [h] at eq1
          have : q / d₂ > 0 := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hd₂.2) h₂) (Nat.pos_of_dvd_of_pos h₂ (Nat.pos_of_ne_zero hd₂.2))
          exact Nat.eq_of_mul_eq_mul_left this (eq1.trans eq2.symm)
        · intro d hd
          rw [Nat.mem_divisors] at hd
          exact ⟨q / d, Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd.1, hq⟩, Nat.div_div_self hd.1 hq⟩
        · intro d hd
          rw [Nat.mem_divisors] at hd
          rw [Nat.div_div_self hd.1 hq]
    rw [reindex]
    have key : ∑ d ∈ q.divisors, Λ d = (vonMangoldt * zeta) q := by
      rw [ArithmeticFunction.mul_apply]
      by_cases hq : q = 0
      · simp [hq]
      · refine Finset.sum_bij (fun d _ => (d, q / d)) ?_ ?_ ?_ ?_
        · intro d hd
          rw [Nat.mem_divisorsAntidiagonal]
          exact ⟨Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd), hq⟩
        · intro d₁ _ d₂ _ h
          exact congr_arg Prod.fst h
        · intro p hp
          rw [Nat.mem_divisorsAntidiagonal] at hp
          have hp1_ne_zero : p.1 ≠ 0 := fun h => hq (by simp [h] at hp; exact hp.1.symm)
          have hp1_pos : p.1 > 0 := Nat.pos_of_ne_zero hp1_ne_zero
          use p.1
          refine ⟨Nat.mem_divisors.mpr ⟨hp.1.symm ▸ dvd_mul_right p.1 p.2, hq⟩, ?_⟩
          exact Prod.ext rfl (Nat.div_eq_of_eq_mul_left hp1_pos (by rw [mul_comm]; exact hp.1.symm))
        · intro d hd
          simp [ArithmeticFunction.zeta_apply]
          rintro (rfl | hqd)
          · rfl
          · exfalso
            have := Nat.mem_divisors.mp hd
            exact Nat.not_lt.mpr (Nat.le_of_dvd (Nat.pos_of_ne_zero this.2) this.1) hqd
    rw [key, vonMangoldt_mul_zeta]; rfl
  exact le_trans h1 (le_trans h2 h3)

/-- Finite discrepancy for residue `a`, with an abstract expected term. -/
def finiteDiscrepancy (K q a : ℕ) (c : ℕ → ℝ) (expected : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Finset.range (K + 1), if n % q = a % q then c n else 0) - expected q

/-- Centered P3 after grouping by `q`; this definition makes the exact routing
and the retained signed modulus weight explicit. -/
noncomputable def centeredP3 (Q : Finset ℕ) (U V K a : ℕ) (c : ℕ → ℝ)
    (expected : ℕ → ℝ) : ℝ :=
  ∑ q ∈ Q, lambda3 U V q * finiteDiscrepancy K q a c expected

/-- Exact finite discrepancy routing. -/
theorem exactP3DiscrepancyRouting (Q : Finset ℕ) (U V K a : ℕ)
    (c : ℕ → ℝ) (expected : ℕ → ℝ)
    (_hodd : ∀ q ∈ Q, Odd q) :
    centeredP3 Q U V K a c expected =
      ∑ q ∈ Q, lambda3 U V q * finiteDiscrepancy K q a c expected := rfl

/-- Maximum logarithm on a nonempty finite modulus set. -/
noncomputable def finiteLogMax (Q : Finset ℕ) (hQ : Q.Nonempty) : ℝ :=
  (Q.image (fun q : ℕ => Real.log q)).max' (hQ.image _)

/-- Deterministic algebraic transference from absolute discrepancy to low P3. -/
theorem absoluteAnatomicalDistributionImpliesLowP3
    (Q : Finset ℕ) (hQ : Q.Nonempty) (U V K a : ℕ) (c : ℕ → ℝ)
    (expected : ℕ → ℝ) (E : ℝ) (_hodd : ∀ q ∈ Q, Odd q)
    (hE : ∑ q ∈ Q, |finiteDiscrepancy K q a c expected| ≤ E) :
    |centeredP3 Q U V K a c expected| ≤ finiteLogMax Q hQ * E := by
  rw [exactP3DiscrepancyRouting Q U V K a c expected _hodd]
  have h1 : |∑ q ∈ Q, lambda3 U V q * finiteDiscrepancy K q a c expected| ≤
      ∑ q ∈ Q, |lambda3 U V q * finiteDiscrepancy K q a c expected| := by
    exact Finset.abs_sum_le_sum_abs _ _
  have h2 : ∀ q ∈ Q, |lambda3 U V q * finiteDiscrepancy K q a c expected| ≤
      finiteLogMax Q hQ * |finiteDiscrepancy K q a c expected| := by
    intro q hq
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_right
    · calc |lambda3 U V q| ≤ Real.log q := lambda3_abs_le_log U V q
        _ ≤ finiteLogMax Q hQ := by
          exact Finset.le_max' (Q.image (fun q : ℕ => Real.log q)) (Real.log q) (Finset.mem_image_of_mem _ hq)
    · exact abs_nonneg _
  have h3 : ∑ q ∈ Q, |lambda3 U V q * finiteDiscrepancy K q a c expected| ≤
      ∑ q ∈ Q, finiteLogMax Q hQ * |finiteDiscrepancy K q a c expected| :=
    Finset.sum_le_sum h2
  calc |∑ q ∈ Q, lambda3 U V q * finiteDiscrepancy K q a c expected| ≤
      ∑ q ∈ Q, |lambda3 U V q * finiteDiscrepancy K q a c expected| := h1
    _ ≤ ∑ q ∈ Q, finiteLogMax Q hQ * |finiteDiscrepancy K q a c expected| := h3
    _ = finiteLogMax Q hQ * ∑ q ∈ Q, |finiteDiscrepancy K q a c expected| := by rw [Finset.mul_sum]
    _ ≤ finiteLogMax Q hQ * E := by
        apply mul_le_mul_of_nonneg_left hE
        have hlog0 : Real.log ↑(hQ.choose) ≥ 0 := by positivity
        rw [finiteLogMax]
        exact le_trans hlog0 (Finset.le_max' (Q.image (fun q : ℕ => Real.log q)) (Real.log hQ.choose) (Finset.mem_image_of_mem _ hQ.choose_spec))

end TwinPrimeProject
