import RequestProject.NANC.FibreModel

/-!
# Gate 0–1 finite bank: the canonical congruence

Under the banked fibre relations

* `m j = c + j * r`,
* `α j = a0 + j * w0`,
* `c * w0 + 2 = r * a0`   (the root relation),

the *canonical congruence*

`r * α j ≡ 2  (mod m j)`

holds for every integer `j`.  It comes from the exact integer identity

`m j * w0 = r * α j - 2`.

If moreover `r` is invertible modulo `m j` (an inverse `s` with `r * s ≡ 1`),
then `α j ≡ 2 * s (mod m j)`, i.e. `α j ≡ 2 r̄`.

Everything in this file is finite integer algebra.  It fixes the generic fibre
phase under the stated hypotheses; it says nothing about global packet routing.

Status label: `CANONICAL_CONGRUENCE_BANKED`.
-/

namespace RouteAFibreFrame
namespace Gate01

/-- The exact integer identity `(c + j r) * w0 = r * (a0 + j w0) - 2` under the
root relation `c * w0 + 2 = r * a0`. -/
theorem m_mul_w0_identity (c r w0 a0 j : ℤ) (hroot : c * w0 + 2 = r * a0) :
    (c + j * r) * w0 = r * (a0 + j * w0) - 2 := by
  linear_combination hroot

/-- **Canonical congruence (raw form).**  `m j` divides `r * α j - 2`. -/
theorem m_dvd_r_alpha_sub_two (c r w0 a0 j : ℤ) (hroot : c * w0 + 2 = r * a0) :
    (c + j * r) ∣ r * (a0 + j * w0) - 2 :=
  ⟨w0, (m_mul_w0_identity c r w0 a0 j hroot).symm⟩

/-- **Canonical congruence.**  `r α_j ≡ 2 (mod m_j)`. -/
theorem canonical_congruence (c r w0 a0 j : ℤ) (hroot : c * w0 + 2 = r * a0) :
    r * (a0 + j * w0) ≡ 2 [ZMOD c + j * r] := by
  have h : (c + j * r) ∣ 2 - r * (a0 + j * w0) := ⟨-w0, by linear_combination hroot⟩
  exact Int.modEq_iff_dvd.mpr h

/-- **Inverted canonical congruence.**  If `s` is an inverse of `r` modulo `m`
and `r * α ≡ 2 (mod m)`, then `α ≡ 2 s (mod m)`. -/
theorem alpha_eq_two_rinv {m r alpha s : ℤ} (hinv : r * s ≡ 1 [ZMOD m])
    (hcong : r * alpha ≡ 2 [ZMOD m]) : alpha ≡ 2 * s [ZMOD m] := by
  have h1 : (r * s) * alpha ≡ 1 * alpha [ZMOD m] := hinv.mul_right alpha
  have h2 : s * (r * alpha) ≡ s * 2 [ZMOD m] := hcong.mul_left s
  have h3 : (r * s) * alpha = s * (r * alpha) := by ring
  calc alpha = 1 * alpha := (one_mul alpha).symm
    _ ≡ (r * s) * alpha [ZMOD m] := h1.symm
    _ = s * (r * alpha) := h3
    _ ≡ s * 2 [ZMOD m] := h2
    _ = 2 * s := by ring

/-- Combined statement: under the root relation and invertibility of `r`,
`α_j ≡ 2 r̄ (mod m_j)`. -/
theorem alpha_congruence_of_root (c r w0 a0 j s : ℤ) (hroot : c * w0 + 2 = r * a0)
    (hinv : r * s ≡ 1 [ZMOD c + j * r]) :
    a0 + j * w0 ≡ 2 * s [ZMOD c + j * r] :=
  alpha_eq_two_rinv hinv (canonical_congruence c r w0 a0 j hroot)

namespace Fibre

variable (F : RouteAFibreFrame.Fibre)

/-- The canonical congruence for the banked fibre model:
`r * α_j ≡ 2 (mod m_j)`. -/
theorem canonical_congruence (j : ℤ) : F.r * F.alpha j ≡ 2 [ZMOD F.m j] :=
  Gate01.canonical_congruence F.c F.r F.w0 F.a0 j F.root

/-- The inverted canonical congruence for the banked fibre model. -/
theorem alpha_congruence (j s : ℤ) (hinv : F.r * s ≡ 1 [ZMOD F.m j]) :
    F.alpha j ≡ 2 * s [ZMOD F.m j] :=
  Gate01.alpha_eq_two_rinv hinv (Fibre.canonical_congruence F j)

end Fibre

end Gate01
end RouteAFibreFrame
