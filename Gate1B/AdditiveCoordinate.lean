/-
# Gate 1B safe algebra bank — §7: the additive square-modulus coordinate.

`ADD-C45`:  for `R = r²` and `ℓ₁, ℓ₂` units mod `R`,

  `R ∣ D  ↔  q₁ − 2 ℓ₁⁻¹ ≡ q₂ − 2 ℓ₂⁻¹  (mod R)`.

Both directions are obtained by *multiplying by the unit* `ℓ₁ ℓ₂`; no informal
modular division is used.  The integer form `add_c45_int` carries the inverses
as explicit integers `ℓ'` with `R ∣ ℓ ℓ' − 1`; the `ZMod` form `add_c45_zmod`
carries them as inverses of genuine units of `ZMod R`.
-/
import Gate1B.C45
import Gate1B.Shell

namespace Gate1B

/-! ## Multiplying a divisibility by an invertible residue -/

/-- If `a` is invertible modulo `R` (witnessed by `R ∣ a a' − 1`) then
multiplication by `a` does not change divisibility by `R`. -/
theorem dvd_mul_left_iff_of_inv {R a a' x : ℤ} (h : R ∣ (a * a' - 1)) :
    R ∣ a * x ↔ R ∣ x := by
  constructor
  · intro hx
    have hrw : x = a' * (a * x) - (a * a' - 1) * x := by ring
    rw [hrw]
    exact dvd_sub (Dvd.dvd.mul_left hx a') (Dvd.dvd.mul_right h x)
  · intro hx
    exact Dvd.dvd.mul_left hx a

/-! ## §7 (ADD-C45), integer form -/

/-- **(ADD-C45), integer form.**  With explicit inverses `ℓᵢ'` modulo `R`,
`R ∣ D` is *equivalent* to the additive coordinate congruence
`q₁ − 2 ℓ₁' ≡ q₂ − 2 ℓ₂' (mod R)`. -/
theorem add_c45_int {R q1 q2 l1 l2 l1' l2' : ℤ}
    (h1 : R ∣ (l1 * l1' - 1)) (h2 : R ∣ (l2 * l2' - 1)) :
    R ∣ C45defect q1 q2 l1 l2 ↔ R ∣ ((q1 - 2 * l1') - (q2 - 2 * l2')) := by
  have key : l1 * l2 * ((q1 - 2 * l1') - (q2 - 2 * l2')) - C45defect q1 q2 l1 l2
      = -(2 * l2) * (l1 * l1' - 1) + (2 * l1) * (l2 * l2' - 1) := by
    unfold C45defect; ring
  have hdiff : R ∣ (l1 * l2 * ((q1 - 2 * l1') - (q2 - 2 * l2')) - C45defect q1 q2 l1 l2) := by
    rw [key]
    exact dvd_add (Dvd.dvd.mul_left h1 _) (Dvd.dvd.mul_left h2 _)
  have hunit : R ∣ (l1 * l2) * (l1' * l2') - 1 := by
    have hrw : (l1 * l2) * (l1' * l2') - 1
        = (l1 * l1' - 1) * (l2 * l2') + (l2 * l2' - 1) := by ring
    rw [hrw]
    exact dvd_add (Dvd.dvd.mul_right h1 _) h2
  constructor
  · intro hD
    have hsum := dvd_add hD hdiff
    simp only [add_sub_cancel] at hsum
    exact (dvd_mul_left_iff_of_inv hunit).mp (by simpa using hsum)
  · intro hE
    have h3 : R ∣ l1 * l2 * ((q1 - 2 * l1') - (q2 - 2 * l2')) := Dvd.dvd.mul_left hE _
    simpa using dvd_sub h3 hdiff

/-! ## §7 (ADD-C45), unit form in `ZMod R` -/

/-- **(ADD-C45), `ZMod` form.**  `ℓ₁, ℓ₂` are represented by units of `ZMod R`
and the coordinate is `q − 2 ℓ⁻¹`. -/
theorem add_c45_zmod {R : ℕ} {q1 q2 l1 l2 : ℤ} (l1u l2u : (ZMod R)ˣ)
    (h1 : ((l1u : ZMod R)) = (l1 : ZMod R)) (h2 : ((l2u : ZMod R)) = (l2 : ZMod R)) :
    ((R : ℤ) ∣ C45defect q1 q2 l1 l2) ↔
      ((q1 : ZMod R) - 2 * ((l1u⁻¹ : (ZMod R)ˣ) : ZMod R)
        = (q2 : ZMod R) - 2 * ((l2u⁻¹ : (ZMod R)ˣ) : ZMod R)) := by
  have hinv1 : (l1 : ZMod R) * ((l1u⁻¹ : (ZMod R)ˣ) : ZMod R) = 1 := by
    rw [← h1, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hinv2 : (l2 : ZMod R) * ((l2u⁻¹ : (ZMod R)ˣ) : ZMod R) = 1 := by
    rw [← h2, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hu : IsUnit ((l1 : ZMod R) * (l2 : ZMod R)) := by
    rw [← h1, ← h2, ← Units.val_mul]; exact Units.isUnit _
  have hcast : ((C45defect q1 q2 l1 l2 : ℤ) : ZMod R)
      = (l1 : ZMod R) * (l2 : ZMod R) *
        (((q1 : ZMod R) - 2 * ((l1u⁻¹ : (ZMod R)ˣ) : ZMod R))
          - ((q2 : ZMod R) - 2 * ((l2u⁻¹ : (ZMod R)ˣ) : ZMod R))) := by
    unfold C45defect
    push_cast
    linear_combination (2 * (l2 : ZMod R)) * hinv1 + (-2 * (l1 : ZMod R)) * hinv2
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, hcast, hu.mul_right_eq_zero, sub_eq_zero]

/-- **(ADD-C45) in the intended modulus `R = r²`**, with the units produced from
`gcd(ℓ₁ ℓ₂, r) = 1`. -/
theorem add_c45_rsq {r : ℕ} {q1 q2 l1 l2 : ℤ} (hco : IsCoprime (l1 * l2) (r : ℤ)) :
    (((r ^ 2 : ℕ) : ℤ) ∣ C45defect q1 q2 l1 l2) ↔
      ((q1 : ZMod (r ^ 2))
          - 2 * ((coprimeUnit (isCoprime_sq_of_isCoprime hco.of_mul_left_left))⁻¹
              : (ZMod (r ^ 2))ˣ)
        = (q2 : ZMod (r ^ 2))
          - 2 * ((coprimeUnit (isCoprime_sq_of_isCoprime hco.of_mul_left_right))⁻¹
              : (ZMod (r ^ 2))ˣ)) :=
  add_c45_zmod _ _ (coprimeUnit_val _) (coprimeUnit_val _)

/-- Existence of an explicit integer inverse modulo `r²` from coprimality to
`r`; this is what feeds the integer form `add_c45_int`. -/
theorem exists_inv_mod_sq {l : ℤ} {r : ℕ} (h : IsCoprime l (r : ℤ)) :
    ∃ l' : ℤ, ((r : ℤ) ^ 2) ∣ (l * l' - 1) := by
  obtain ⟨a, b, hab⟩ := (h.pow_right (n := 2) : IsCoprime l ((r : ℤ) ^ 2))
  exact ⟨a, ⟨-b, by linarith [hab]⟩⟩

end Gate1B
