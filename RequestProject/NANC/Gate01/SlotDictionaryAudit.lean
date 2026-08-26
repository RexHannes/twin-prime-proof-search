import Mathlib

/-!
# Gate 0–1 audit: the old direct Bettin–Chandee slot dictionary

For the direct completed covariance (COMP), the old slot assignment
`(A, U, V) = (H, R L, M)` is **not** what the direct representation produces:
the natural masses there are `(H, L, L M)` or `(H, L², M)`.

The finite content banked here is the exponent-level distinctness of these
slot triples.  Writing masses as `X` to a rational exponent, the triples are
`(h, l, l + m)`, `(h, 2 l, m)` and `(h, ρ + l, m)`; the first differs from the
third as soon as `ρ ≠ 0`, and the second differs from the third as soon as
`l ≠ ρ`.

Scope of the audit (deliberately narrow):

* banked: `OLD_DIRECT_BC_SLOT_DICTIONARY_FALSE_FOR_COMP_REPRESENTATION`, i.e.
  the *direct* slot assignment does not arise directly;
* **not** banked: any claim that no Bettin–Chandee, Wright or dispersion
  reformulation can work.  Other variable transformations or averaged
  formulations are not excluded by anything proved here.
-/

namespace RouteAFibreFrame
namespace Gate01

/-- Exponent triple of a Bettin–Chandee slot assignment `(A, U, V)`. -/
abbrev SlotExponents := ℚ × ℚ × ℚ

/-- The old slot assignment `(H, R L, M)`. -/
def oldSlots (h l m rho : ℚ) : SlotExponents := (h, rho + l, m)

/-- The first natural direct assignment `(H, L, L M)`. -/
def directSlotsA (h l m : ℚ) : SlotExponents := (h, l, l + m)

/-- The second natural direct assignment `(H, L², M)`. -/
def directSlotsB (h l m : ℚ) : SlotExponents := (h, 2 * l, m)

/-- **Slot mismatch, first form.**  `(H, L, L M) ≠ (H, R L, M)` whenever the
`R`-exponent is nonzero. -/
theorem directSlotsA_ne_oldSlots (h l m rho : ℚ) (hrho : rho ≠ 0) :
    directSlotsA h l m ≠ oldSlots h l m rho := by
  intro hEq
  have : l = rho + l := congrArg (fun p : SlotExponents => p.2.1) hEq
  exact hrho (by linarith)

/-- **Slot mismatch, second form.**  `(H, L², M) ≠ (H, R L, M)` whenever the
`L`-exponent differs from the `R`-exponent. -/
theorem directSlotsB_ne_oldSlots (h l m rho : ℚ) (hne : l ≠ rho) :
    directSlotsB h l m ≠ oldSlots h l m rho := by
  intro hEq
  have : 2 * l = rho + l := congrArg (fun p : SlotExponents => p.2.1) hEq
  exact hne (by linarith)

/-- The two natural direct assignments differ from each other unless
`l = 0`. -/
theorem directSlotsA_ne_directSlotsB (h l m : ℚ) (hl : l ≠ 0) :
    directSlotsA h l m ≠ directSlotsB h l m := by
  intro hEq
  have : l = 2 * l := congrArg (fun p : SlotExponents => p.2.1) hEq
  exact hl (by linarith)

end Gate01
end RouteAFibreFrame
