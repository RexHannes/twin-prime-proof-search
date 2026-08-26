import RequestProject.NANC.Gate1BDet2.PrimitiveDet2PairConverse
import RequestProject.NANC.Gate1BDet2.DFBTAntiLoop

/-!
# Gate 1B / determinant-2 bank, Module 22: common-shift rigidity

The exact arithmetic behind the graph-degree audit of the common-shift
construction.  Two directions:

* **β-pair direction.**  `z₂ − z₁ = u h` gives `u ∣ z₂ − z₁`, and the shell
  gives `ℓ z₁ ≡ 2 (mod u)`.  Under invertibility of `z₁` modulo `u` this pins
  the residue class of `ℓ` modulo `u`, so an `ℓ`-interval of diameter `< u`
  contains at most one admissible `ℓ`.
* **b-pair direction.**  `v₂ − v₁ = ℓ h` gives `ℓ ∣ v₂ − v₁`, and the shell
  gives `u v₁ ≡ −2 (mod ℓ)`; the number of admissible values in a finite
  interval is then bounded by the residue-class counting lemma
  `card_le_of_residue_class_in_interval`.

Everything here is finite/combinatorial.  **No `X^{o(1)}` statement, and no
`U/ℓ + 1` asymptotic, is formalized**: the counting lemma is the exact finite
statement of which such a bound would be the analytic shadow.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-! ## 1. β-pair direction: divisibility and residue rigidity modulo `u` -/

/-- **`FIXED_BETA_PAIR_DIVISIBILITY_RIGIDITY`.**  The `z`-increment of a common
shift is divisible by `u`. -/
theorem u_dvd_z_shift {u z₁ z₂ h : ℤ} (hz : z₂ = z₁ + u * h) : u ∣ z₂ - z₁ :=
  ⟨h, by rw [hz]; ring⟩

/-- On the determinant-2 shell, `ℓ z₁ ≡ 2 (mod u)`. -/
theorem ell_mul_z_mod_u_eq_two {u l v₁ z₁ : ℤ} (hdet : OnDet2Line u l v₁ z₁) :
    l * z₁ ≡ 2 [ZMOD u] := by
  unfold OnDet2Line at hdet
  exact Int.modEq_iff_dvd.mpr ⟨-v₁, by linarith⟩

/-- **Residue rigidity.**  If `z₁` is invertible modulo `u`, two admissible
values of `ℓ` (for the same `(z₁, u)`) are congruent modulo `u`. -/
theorem ell_congr_mod_u_of_isCoprime {u z₁ l₁ l₂ : ℤ} (hcop : IsCoprime z₁ u)
    (h₁ : l₁ * z₁ ≡ 2 [ZMOD u]) (h₂ : l₂ * z₁ ≡ 2 [ZMOD u]) :
    l₁ ≡ l₂ [ZMOD u] := by
  have : z₁ * l₁ ≡ z₁ * l₂ [ZMOD u] := by
    have e₁ : z₁ * l₁ ≡ 2 [ZMOD u] := by simpa [mul_comm] using h₁
    have e₂ : z₁ * l₂ ≡ 2 [ZMOD u] := by simpa [mul_comm] using h₂
    exact e₁.trans e₂.symm
  exact modEq_cancel_left_of_isCoprime hcop this

/-- **`SHORT_INTERVAL_RESIDUE_UNIQUENESS`.**  For fixed `(z₁, u)` with `z₁`
invertible modulo `u > 0`, an `ℓ`-interval of diameter `< u` contains at most one
admissible `ℓ`.  (The generic integer rigidity step `eq_of_modEq_of_abs_sub_lt`
of Module 10 is reused, not restated.) -/
theorem ell_unique_in_short_interval {u z₁ l₁ l₂ : ℤ} (hu : 0 < u)
    (hcop : IsCoprime z₁ u)
    (h₁ : l₁ * z₁ ≡ 2 [ZMOD u]) (h₂ : l₂ * z₁ ≡ 2 [ZMOD u])
    (hshort : |l₁ - l₂| < u) :
    l₁ = l₂ :=
  eq_of_modEq_of_abs_sub_lt (ell_congr_mod_u_of_isCoprime hcop h₁ h₂) hu hshort

/-- The same statement phrased directly on the shell: for fixed `(z₁, u)` and a
short `ℓ`-window, the determinant-2 equation has at most one solution `ℓ` (with
its accompanying `v`). -/
theorem det2_ell_unique_in_short_interval {u l₁ l₂ v₁ v₂ z₁ : ℤ} (hu : 0 < u)
    (hcop : IsCoprime z₁ u)
    (hd₁ : OnDet2Line u l₁ v₁ z₁) (hd₂ : OnDet2Line u l₂ v₂ z₁)
    (hshort : |l₁ - l₂| < u) :
    l₁ = l₂ :=
  ell_unique_in_short_interval hu hcop (ell_mul_z_mod_u_eq_two hd₁)
    (ell_mul_z_mod_u_eq_two hd₂) hshort

/-! ## 2. b-pair direction: divisibility and residue class modulo `ℓ` -/

/-- **`FIXED_B_PAIR_DIVISIBILITY_RIGIDITY`.**  The `v`-increment of a common
shift is divisible by `ℓ`. -/
theorem ell_dvd_v_shift {l v₁ v₂ h : ℤ} (hv : v₂ = v₁ + l * h) : l ∣ v₂ - v₁ :=
  ⟨h, by rw [hv]; ring⟩

/-- On the determinant-2 shell, `u v₁ ≡ −2 (mod ℓ)`. -/
theorem u_mul_v_mod_ell_eq_neg_two {u l v₁ z₁ : ℤ} (hdet : OnDet2Line u l v₁ z₁) :
    u * v₁ ≡ -2 [ZMOD l] := by
  unfold OnDet2Line at hdet
  exact Int.modEq_iff_dvd.mpr ⟨-z₁, by linarith⟩

/-- Residue rigidity in the `b`-pair direction: if `v₁` is invertible modulo `ℓ`,
two admissible `u`'s are congruent modulo `ℓ`. -/
theorem u_congr_mod_ell_of_isCoprime {l v₁ u₁ u₂ : ℤ} (hcop : IsCoprime v₁ l)
    (h₁ : u₁ * v₁ ≡ -2 [ZMOD l]) (h₂ : u₂ * v₁ ≡ -2 [ZMOD l]) :
    u₁ ≡ u₂ [ZMOD l] := by
  have : v₁ * u₁ ≡ v₁ * u₂ [ZMOD l] := by
    have e₁ : v₁ * u₁ ≡ -2 [ZMOD l] := by simpa [mul_comm] using h₁
    have e₂ : v₁ * u₂ ≡ -2 [ZMOD l] := by simpa [mul_comm] using h₂
    exact e₁.trans e₂.symm
  exact modEq_cancel_left_of_isCoprime hcop this

/-! ## 3. Counting a residue class in a finite interval -/

/-- **`FINITE_RESIDUE_CLASS_INTERVAL_COUNT`.**  For `m > 0`, any finite set of
integers lying in `[a, b]` and in a single residue class modulo `m` has at most
`(b − a)/m + 1` elements (integer, i.e. floor, division).

This is the exact finite combinatorics of which the analytic estimate
`O(U/ℓ + 1)` is the shadow; no asymptotic statement is made here. -/
theorem card_le_of_residue_class_in_interval {m a b c : ℤ} (hm : 0 < m) (hab : a ≤ b)
    (S : Finset ℤ) (hS : ∀ n ∈ S, a ≤ n ∧ n ≤ b ∧ n ≡ c [ZMOD m]) :
    (S.card : ℤ) ≤ (b - a) / m + 1 := by
  classical
  set A : ℤ := -((c - a) / m) with hA
  set B : ℤ := (b - c) / m with hB
  -- the map `n ↦ (n − c)/m` sends `S` injectively into `Finset.Icc A B`
  have hmaps : ∀ n ∈ S, (n - c) / m ∈ Finset.Icc A B := by
    intro n hn
    obtain ⟨hna, hnb, hcong⟩ := hS n hn
    obtain ⟨k, hk⟩ : m ∣ n - c := (Int.modEq_iff_dvd.mp hcong.symm)
    have hnk : n = c + m * k := by linarith [hk]
    have hdiv : (n - c) / m = k := by
      rw [hk]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hm)
    rw [hdiv]
    refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
    · -- `A ≤ k`
      have h1 : -k * m ≤ c - a := by nlinarith [hna, hnk]
      have h2 : -k ≤ (c - a) / m := Int.le_ediv_iff_mul_le hm |>.mpr h1
      omega
    · -- `k ≤ B`
      have h1 : k * m ≤ b - c := by nlinarith [hnb, hnk]
      exact Int.le_ediv_iff_mul_le hm |>.mpr h1
  have hinj : Set.InjOn (fun n => (n - c) / m) S := by
    intro x hx y hy hxy
    obtain ⟨-, -, hcx⟩ := hS x (by simpa using hx)
    obtain ⟨-, -, hcy⟩ := hS y (by simpa using hy)
    obtain ⟨kx, hkx⟩ : m ∣ x - c := (Int.modEq_iff_dvd.mp hcx.symm)
    obtain ⟨ky, hky⟩ : m ∣ y - c := (Int.modEq_iff_dvd.mp hcy.symm)
    have ex : (x - c) / m = kx := by rw [hkx]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hm)
    have ey : (y - c) / m = ky := by rw [hky]; exact Int.mul_ediv_cancel_left _ (ne_of_gt hm)
    simp only [ex, ey] at hxy
    have : x - c = y - c := by rw [hkx, hky, hxy]
    omega
  have hcard : S.card ≤ (Finset.Icc A B).card :=
    Finset.card_le_card_of_injOn _ (fun n hn => by simpa using hmaps n (by simpa using hn)) hinj
  -- `B − A ≤ (b − a)/m`
  have hBA : B - A ≤ (b - a) / m := by
    have h1 : ((b - c) / m) * m ≤ b - c := Int.ediv_mul_le _ (ne_of_gt hm)
    have h2 : ((c - a) / m) * m ≤ c - a := Int.ediv_mul_le _ (ne_of_gt hm)
    have hsum : (B - A) * m ≤ b - a := by
      have : (B - A) = (b - c) / m + (c - a) / m := by rw [hA, hB]; ring
      rw [this, add_mul]
      linarith
    exact (Int.le_ediv_iff_mul_le hm).mpr hsum
  have hge : 0 ≤ (b - a) / m := Int.ediv_nonneg (by linarith) hm.le
  have hIcc : ((Finset.Icc A B).card : ℤ) ≤ (b - a) / m + 1 := by
    rw [Int.card_Icc]
    omega
  calc (S.card : ℤ) ≤ ((Finset.Icc A B).card : ℤ) := by exact_mod_cast hcard
    _ ≤ (b - a) / m + 1 := hIcc

/-- The `Finset.Icc`/filter form of the same count. -/
theorem card_filter_residue_class_Icc_le {m a b c : ℤ} (hm : 0 < m) (hab : a ≤ b) :
    (((Finset.Icc a b).filter (fun n => n ≡ c [ZMOD m])).card : ℤ) ≤ (b - a) / m + 1 := by
  classical
  refine card_le_of_residue_class_in_interval (c := c) hm hab _ ?_
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  exact ⟨hn.1.1, hn.1.2, hn.2⟩

end Gate1BDet2
end TwinPrimeProject
