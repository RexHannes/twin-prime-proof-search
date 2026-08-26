import RequestProject.NANC.HPoissonComplementaryDivisor.CRTPhase

/-!
# HPoissonComplementaryDivisor, Module 2: the finite congruence core after Poisson

**Poisson summation is NOT asserted anywhere in this module.**  Only the
integer/congruence reindexing that is *used after* an application of Poisson
summation is formalized:

* `residue_iff_mul` : `y ≡ 2 w̄ [ZMOD c] ↔ y w ≡ 2 [ZMOD c]` (for `w̄` an
  inverse of `w` mod `c`);
* `crt_split_two` : under the CRT hypotheses,
  `y w ≡ 2 [ZMOD q₁ q₂] ↔ q₁ ∣ y v₁ - 2 ∧ q₂ ∣ y v₂ - 2`;
* `residueClassEquiv` : `n ↦ n c + 2 w̄` is a bijection from `ℤ` onto the
  residue class `{ y : y ≡ 2 w̄ [ZMOD c] }` (for `c ≠ 0`).
-/

namespace TwinPrimeProject
namespace HPoissonCD

/-! ## 1. The inverse residue class as a multiplicative congruence -/

/-- **Reindexing core.**  If `w̄` is an inverse of `w` modulo `c`, then
`y ≡ 2 w̄ [ZMOD c]` is equivalent to `y w ≡ 2 [ZMOD c]`. -/
theorem residue_iff_mul {c w wbar y : ℤ} (hinv : w * wbar ≡ 1 [ZMOD c]) :
    y ≡ 2 * wbar [ZMOD c] ↔ y * w ≡ 2 [ZMOD c] := by
  constructor
  · intro hy
    calc y * w ≡ (2 * wbar) * w [ZMOD c] := hy.mul_right w
      _ = 2 * (w * wbar) := by ring
      _ ≡ 2 * 1 [ZMOD c] := hinv.mul_left 2
      _ = 2 := by ring
  · intro hy
    calc y = y * 1 := by ring
      _ ≡ y * (w * wbar) [ZMOD c] := (Int.ModEq.refl y).mul hinv.symm
      _ = (y * w) * wbar := by ring
      _ ≡ 2 * wbar [ZMOD c] := hy.mul_right wbar

/-! ## 2. CRT splitting of the congruence `y w ≡ 2` -/

/-- **CRT split.**  With `q₁, q₂` coprime and `w` a CRT solution with residues
`v₁, v₂`, the congruence `y w ≡ 2 [ZMOD q₁ q₂]` is equivalent to the pair of
divisibilities `q₁ ∣ y v₁ - 2` and `q₂ ∣ y v₂ - 2`. -/
theorem crt_split_two {q₁ q₂ v₁ v₂ w y : ℤ} (hq : IsCoprime q₁ q₂)
    (hw₁ : w ≡ v₁ [ZMOD q₁]) (hw₂ : w ≡ v₂ [ZMOD q₂]) :
    y * w ≡ 2 [ZMOD q₁ * q₂] ↔ (q₁ ∣ y * v₁ - 2 ∧ q₂ ∣ y * v₂ - 2) := by
  have e₁ : (y * w ≡ 2 [ZMOD q₁]) ↔ q₁ ∣ y * v₁ - 2 := by
    have h : y * w ≡ y * v₁ [ZMOD q₁] := hw₁.mul_left y
    constructor
    · intro hy
      have : y * v₁ ≡ 2 [ZMOD q₁] := h.symm.trans hy
      exact dvd_sub_comm.mp (Int.modEq_iff_dvd.mp this)
    · intro hd
      have : y * v₁ ≡ 2 [ZMOD q₁] := Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hd)
      exact h.trans this
  have e₂ : (y * w ≡ 2 [ZMOD q₂]) ↔ q₂ ∣ y * v₂ - 2 := by
    have h : y * w ≡ y * v₂ [ZMOD q₂] := hw₂.mul_left y
    constructor
    · intro hy
      have : y * v₂ ≡ 2 [ZMOD q₂] := h.symm.trans hy
      exact dvd_sub_comm.mp (Int.modEq_iff_dvd.mp this)
    · intro hd
      have : y * v₂ ≡ 2 [ZMOD q₂] := Int.modEq_iff_dvd.mpr (dvd_sub_comm.mp hd)
      exact h.trans this
  constructor
  · intro hy
    exact ⟨e₁.mp (hy.of_dvd ⟨q₂, rfl⟩), e₂.mp (hy.of_dvd ⟨q₁, mul_comm q₁ q₂⟩)⟩
  · rintro ⟨d₁, d₂⟩
    exact crt_unique hq (e₁.mpr d₁) (e₂.mpr d₂)

/-- **Combined form.**  The residue class `y ≡ 2 w̄ [ZMOD q₁ q₂]` is exactly
the pair of divisibility conditions on the two coprime factors. -/
theorem residue_iff_split {q₁ q₂ v₁ v₂ w wbar y : ℤ} (hq : IsCoprime q₁ q₂)
    (hw₁ : w ≡ v₁ [ZMOD q₁]) (hw₂ : w ≡ v₂ [ZMOD q₂])
    (hinv : w * wbar ≡ 1 [ZMOD q₁ * q₂]) :
    y ≡ 2 * wbar [ZMOD q₁ * q₂] ↔ (q₁ ∣ y * v₁ - 2 ∧ q₂ ∣ y * v₂ - 2) :=
  (residue_iff_mul hinv).trans (crt_split_two hq hw₁ hw₂)

/-! ## 3. The integer change of variables `y = n c + 2 w̄` -/

/-- The change of variables `n ↦ n c + 2 w̄` as an explicit bijection between
`ℤ` and the residue class `{ y // y ≡ 2 w̄ [ZMOD c] }`.  Requires `c ≠ 0`. -/
def residueClassEquiv (c wbar : ℤ) (hc : c ≠ 0) :
    ℤ ≃ {y : ℤ // y ≡ 2 * wbar [ZMOD c]} where
  toFun n := ⟨n * c + 2 * wbar, Int.modEq_iff_dvd.mpr ⟨-n, by ring⟩⟩
  invFun y := (y.1 - 2 * wbar) / c
  left_inv n := by
    simp only []
    rw [show n * c + 2 * wbar - 2 * wbar = n * c by ring, Int.mul_ediv_cancel _ hc]
  right_inv y := by
    obtain ⟨y, hy⟩ := y
    have hd : c ∣ y - 2 * wbar := dvd_sub_comm.mp (Int.modEq_iff_dvd.mp hy)
    apply Subtype.ext
    simp only []
    rw [Int.ediv_mul_cancel hd]
    ring

@[simp] theorem residueClassEquiv_apply (c wbar : ℤ) (hc : c ≠ 0) (n : ℤ) :
    ((residueClassEquiv c wbar hc) n : ℤ) = n * c + 2 * wbar := rfl

/-- Injectivity of the change of variables, stated directly. -/
theorem shift_injective {c : ℤ} (hc : c ≠ 0) (wbar : ℤ) :
    Function.Injective (fun n : ℤ => n * c + 2 * wbar) := by
  intro m n h
  simp only [] at h
  have : m * c = n * c := by linarith
  exact mul_right_cancel₀ hc this

/-- Surjectivity onto the residue class, stated directly. -/
theorem shift_surjective {c : ℤ} (wbar y : ℤ) (hy : y ≡ 2 * wbar [ZMOD c]) :
    ∃ n : ℤ, n * c + 2 * wbar = y := by
  obtain ⟨n, hn⟩ : c ∣ y - 2 * wbar := dvd_sub_comm.mp (Int.modEq_iff_dvd.mp hy)
  exact ⟨n, by linarith⟩

end HPoissonCD
end TwinPrimeProject
