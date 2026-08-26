import RequestProject.NANC.Gate1BDet2.DFBTAntiLoop

/-!
# Gate 1B / determinant-2 bank, Module 11: the off-shell DFBT decomposition

Module 10 banked the *on-shell* factorisation `Δ = q₁ q₂ (ℓ₁ − ℓ₂)`.  This
module records the exact **off-shell** correction.  Define the defects

  `ηᵢ = xᵢ − qᵢ ℓᵢ`,

which measure the failure of the physical shell identities.  Then, with no
hypotheses at all,

  `x₁ q₂ − x₂ q₁ = q₁ q₂ (ℓ₁ − ℓ₂) + η₁ q₂ − η₂ q₁`.

This formally records two things:

* the physical-shell part `q₁ q₂ (ℓ₁ − ℓ₂)` anti-loops (Module 10);
* an off-shell defect term `η₁ q₂ − η₂ q₁` can *survive* before inverse
  Poisson.

**Deliberately not asserted:** nothing here claims that the defect term enjoys
analytic cancellation.  The guard `offshell_defect_can_be_nonzero` exhibits a
configuration in which the defect is the only surviving contribution.
-/

namespace TwinPrimeProject
namespace Gate1BDet2

/-- The off-shell defect `η = x − q ℓ`. -/
def shellDefect (x q l : ℤ) : ℤ := x - q * l

@[simp] theorem shellDefect_def (x q l : ℤ) : shellDefect x q l = x - q * l := rfl

/-- The defect vanishes exactly on the physical shell. -/
theorem shellDefect_eq_zero_iff (x q l : ℤ) : shellDefect x q l = 0 ↔ x = q * l := by
  simp [shellDefect, sub_eq_zero]

/-- **DFBT off-shell Gram decomposition.**  For arbitrary integers, with
`ηᵢ = xᵢ − qᵢ ℓᵢ`,

  `x₁ q₂ − x₂ q₁ = q₁ q₂ (ℓ₁ − ℓ₂) + η₁ q₂ − η₂ q₁`.

No hypotheses are required. -/
theorem dfbt_gram_off_shell_decomposition (x₁ x₂ q₁ q₂ l₁ l₂ : ℤ) :
    gramDet x₁ x₂ q₁ q₂
      = q₁ * q₂ * (l₁ - l₂)
        + shellDefect x₁ q₁ l₁ * q₂ - shellDefect x₂ q₂ l₂ * q₁ := by
  unfold gramDet shellDefect; ring

/-- **Specialisation to the shell.**  If both defects vanish, the decomposition
collapses to the on-shell anti-loop identity of Module 10. -/
theorem dfbt_gram_off_shell_specialize {x₁ x₂ q₁ q₂ l₁ l₂ : ℤ}
    (h₁ : shellDefect x₁ q₁ l₁ = 0) (h₂ : shellDefect x₂ q₂ l₂ = 0) :
    gramDet x₁ x₂ q₁ q₂ = q₁ * q₂ * (l₁ - l₂) := by
  rw [dfbt_gram_off_shell_decomposition x₁ x₂ q₁ q₂ l₁ l₂, h₁, h₂]; ring

/-- The same specialisation stated directly from the shell identities. -/
theorem dfbt_gram_off_shell_specialize' {x₁ x₂ q₁ q₂ l₁ l₂ : ℤ}
    (h₁ : x₁ = q₁ * l₁) (h₂ : x₂ = q₂ * l₂) :
    gramDet x₁ x₂ q₁ q₂ = q₁ * q₂ * (l₁ - l₂) :=
  det2_gram_on_shell h₁ h₂

/-- The pure defect part, isolated: the Gram invariant minus its on-shell
value. -/
theorem dfbt_gram_defect_part (x₁ x₂ q₁ q₂ l₁ l₂ : ℤ) :
    gramDet x₁ x₂ q₁ q₂ - q₁ * q₂ * (l₁ - l₂)
      = shellDefect x₁ q₁ l₁ * q₂ - shellDefect x₂ q₂ l₂ * q₁ := by
  rw [dfbt_gram_off_shell_decomposition x₁ x₂ q₁ q₂ l₁ l₂]; ring

/-- **Guard (no free analytic cancellation).**  There are configurations with
`ℓ₁ = ℓ₂` — so that the anti-looping on-shell part vanishes identically — for
which the Gram invariant is nonzero, carried entirely by the off-shell defect.
Hence Module 10 does *not* by itself kill the off-shell contribution. -/
theorem offshell_defect_can_be_nonzero :
    ∃ x₁ x₂ q₁ q₂ l : ℤ,
      gramDet x₁ x₂ q₁ q₂
          = shellDefect x₁ q₁ l * q₂ - shellDefect x₂ q₂ l * q₁ ∧
        gramDet x₁ x₂ q₁ q₂ ≠ 0 := by
  refine ⟨1, 0, 1, 1, 0, by norm_num [gramDet, shellDefect], by norm_num [gramDet]⟩

end Gate1BDet2
end TwinPrimeProject
