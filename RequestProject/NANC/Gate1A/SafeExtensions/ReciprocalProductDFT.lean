/-
# NANC Gate 1A v9 — OPTIONAL_FINITE_CHILD: the reciprocal-product kernel

For a modulus `c`, a unit `A`, and an arbitrary unimodular phase `psi`, the
reciprocal-product kernel on the units is

    K_c(r,s) = psi (A * r⁻¹ * s⁻¹).

Only the *unconditional Hilbert–Schmidt (full-space) energy* is banked here: it
is exactly the number of pairs.  No interval residue aggregation, and no
non-trivial spectral estimate, is claimed.

**FIREWALL.**  A finite DFT / Hilbert–Schmidt child statement is **not**
`XQ-AMPLINE-SIGNED1A`.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V9

open Finset

variable {c : ℕ} [NeZero c]

/-- The reciprocal-product kernel on the units of `ZMod c`. -/
def reciprocalProductKernel (psi : ZMod c → ℂ) (A : (ZMod c)ˣ)
    (r s : (ZMod c)ˣ) : ℂ :=
  psi ((A : ZMod c) * ((r⁻¹ : (ZMod c)ˣ) : ZMod c) * ((s⁻¹ : (ZMod c)ˣ) : ZMod c))

/-- **Hilbert–Schmidt energy of the reciprocal-product kernel.**  For a
unimodular phase the total energy is exactly the number of `(r,s)` pairs. -/
theorem reciprocalProductKernel_hilbertSchmidt (psi : ZMod c → ℂ)
    (hpsi : ∀ z, ‖psi z‖ = 1) (A : (ZMod c)ˣ) :
    ∑ r : (ZMod c)ˣ, ∑ s : (ZMod c)ˣ, ‖reciprocalProductKernel psi A r s‖ ^ 2
      = (Fintype.card (ZMod c)ˣ : ℝ) ^ 2 := by
  have h : ∀ r s : (ZMod c)ˣ, ‖reciprocalProductKernel psi A r s‖ ^ 2 = 1 := by
    intro r s
    rw [reciprocalProductKernel, hpsi]
    norm_num
  simp [h, Finset.card_univ, sq]

end TwinPrimeProject.NANC.Gate1A.V9
