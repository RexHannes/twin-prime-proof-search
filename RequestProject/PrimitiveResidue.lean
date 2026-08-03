import Mathlib
import RequestProject.PrimitiveLattice

/-!
# Primitive Form C residue class and reconstruction

* `PRIMITIVE_FORM_C_RESIDUE`  (§5.1): the residue class of `r₁` modulo `m₁q₂`.
* `PRIMITIVE_FORM_C_R2_RECONSTRUCTION` (§5.1): exact reconstruction of `r₂`.
* Compatibility with `n` (§5.2).

Invertibility is supplied by an *explicit* inverse witness (an integer `w`
with `(m₂q₁)·w ≡ 1 (mod m₁q₂)`), rather than by an opaque `⁻¹`, which keeps the
statements self-contained.  These are `LEAN_PROVED_CORE`: the modular/algebraic
core is proved; the residue class is the exact `ξ(m,q)` of the report.
-/

namespace Banking.PrimitiveResidue

open Int

/-- `PRIMITIVE_FORM_C_RESIDUE` (§5.1).

Under the standing lattice equations and with `w` an inverse of `m₂q₁` modulo
`m₁q₂`, we have `r₁ ≡ 2(m₂−m₁)·w (mod m₁q₂)`.  The right-hand side is exactly
`ξ(m,q) = 2(m₂−m₁)·overline{m₂q₁} (mod m₁q₂)`.

Status: `LEAN_PROVED_CORE`. -/
theorem primitive_formC_residue
    (m₁ m₂ n q₁ r₁ q₂ r₂ w : ℤ)
    (h₁ : q₁ * r₁ = m₁ * n + 2) (h₂ : q₂ * r₂ = m₂ * n + 2)
    (hw : (m₂ * q₁) * w ≡ 1 [ZMOD (m₁ * q₂)]) :
    r₁ ≡ 2 * (m₂ - m₁) * w [ZMOD (m₁ * q₂)] := by
  have hlat : (m₂ * q₁) * r₁ - (m₁ * q₂) * r₂ = 2 * (m₂ - m₁) := by
    have := Banking.PrimitiveLattice.two_outer_lattice_identity m₁ m₂ n q₁ r₁ q₂ r₂ h₁ h₂
    linarith [this]
  have hmod : (m₂ * q₁) * r₁ ≡ 2 * (m₂ - m₁) [ZMOD (m₁ * q₂)] := by
    have hd : (m₂ * q₁) * r₁ - 2 * (m₂ - m₁) = (m₁ * q₂) * r₂ := by linarith [hlat]
    exact (Int.modEq_iff_dvd.mpr ⟨r₂, by linarith [hd]⟩).symm
  calc r₁ ≡ (m₂ * q₁) * w * r₁ [ZMOD (m₁ * q₂)] := by
            have := hw.mul_right r₁
            simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using this.symm
    _ = (m₂ * q₁) * r₁ * w := by ring
    _ ≡ 2 * (m₂ - m₁) * w [ZMOD (m₁ * q₂)] := hmod.mul_right w

/-- The explicit residue value `ξ(m,q) = 2(m₂−m₁)·overline{m₂q₁}` (§5.1);
`w` is the supplied inverse of `m₂q₁` modulo `m₁q₂`. -/
def xi (m₁ m₂ w : ℤ) : ℤ := 2 * (m₂ - m₁) * w

/-- `PRIMITIVE_FORM_C_R2_RECONSTRUCTION` (§5.1).

`r₂` is reconstructed exactly by `m₁q₂ · r₂ = m₂q₁r₁ − 2(m₂−m₁)`, i.e.
`r₂ = (m₂q₁r₁ − 2(m₂−m₁)) / (m₁q₂)`.

Status: `LEAN_PROVED_CORE`. -/
theorem primitive_formC_r2_reconstruction
    (m₁ m₂ n q₁ r₁ q₂ r₂ : ℤ)
    (h₁ : q₁ * r₁ = m₁ * n + 2) (h₂ : q₂ * r₂ = m₂ * n + 2) :
    (m₁ * q₂) * r₂ = (m₂ * q₁) * r₁ - 2 * (m₂ - m₁) := by
  have := Banking.PrimitiveLattice.two_outer_lattice_identity m₁ m₂ n q₁ r₁ q₂ r₂ h₁ h₂
  linarith [this]

theorem primitive_formC_r2_div
    (m₁ m₂ n q₁ r₁ q₂ r₂ : ℤ) (hden : m₁ * q₂ ≠ 0)
    (h₁ : q₁ * r₁ = m₁ * n + 2) (h₂ : q₂ * r₂ = m₂ * n + 2) :
    r₂ = ((m₂ * q₁) * r₁ - 2 * (m₂ - m₁)) / (m₁ * q₂) := by
  have h := primitive_formC_r2_reconstruction m₁ m₂ n q₁ r₁ q₂ r₂ h₁ h₂
  rw [← h]
  exact (Int.mul_ediv_cancel_left r₂ hden).symm

/-! ## §5.2 Compatibility with `n`. -/

/-- Reduction modulo `m₁`: `q₁r₁ ≡ 2 (mod m₁)`. -/
theorem q1r1_mod_m1 (m₁ n q₁ r₁ : ℤ) (h₁ : q₁ * r₁ = m₁ * n + 2) :
    q₁ * r₁ ≡ 2 [ZMOD m₁] :=
  (Int.modEq_iff_dvd.mpr ⟨n, by linarith [h₁]⟩).symm

/-- Reduction modulo `m₁` in residue-of-`r₁` form: with `u` an inverse of `q₁`
modulo `m₁`, `r₁ ≡ 2·overline{q₁} (mod m₁)`. -/
theorem r1_mod_m1 (m₁ n q₁ r₁ u : ℤ) (h₁ : q₁ * r₁ = m₁ * n + 2)
    (hu : q₁ * u ≡ 1 [ZMOD m₁]) :
    r₁ ≡ 2 * u [ZMOD m₁] := by
  have hmod : q₁ * r₁ ≡ 2 [ZMOD m₁] := q1r1_mod_m1 m₁ n q₁ r₁ h₁
  calc r₁ ≡ q₁ * u * r₁ [ZMOD m₁] := by
            have := hu.mul_right r₁
            simpa [one_mul, mul_comm, mul_left_comm, mul_assoc] using this.symm
    _ = q₁ * r₁ * u := by ring
    _ ≡ 2 * u [ZMOD m₁] := hmod.mul_right u

/-- Integrality of `n = (q₁r₁ − 2)/m₁`: equivalently `m₁ ∣ q₁r₁ − 2`. -/
theorem m1_dvd_q1r1_sub_two (m₁ n q₁ r₁ : ℤ) (h₁ : q₁ * r₁ = m₁ * n + 2) :
    m₁ ∣ (q₁ * r₁ - 2) :=
  ⟨n, by linarith [h₁]⟩

/-- Reduction modulo `q₂` encodes the congruence `m₂n ≡ −2 (mod q₂)`. -/
theorem m2n_mod_q2 (m₂ n q₂ r₂ : ℤ) (h₂ : q₂ * r₂ = m₂ * n + 2) :
    m₂ * n ≡ -2 [ZMOD q₂] :=
  (Int.modEq_iff_dvd.mpr ⟨r₂, by linarith [h₂]⟩).symm

end Banking.PrimitiveResidue
