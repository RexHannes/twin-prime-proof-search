import Mathlib

/-!
# Finite-field Kloosterman sums (prime model)

This module bank the *exact* finite-field definitions used in the prime
short-window audit:

* the standard additive character `ep p : AddChar (ZMod p) ℂ`
  (composition of `AddChar.zmod p 1` with `Circle → ℂ`);
* its elementary identities (`ep_add`, `ep_zero`, `ep_conj`) and primitivity
  (`ep_primitive`), yielding the complete-period orthogonality
  `ep_orthogonality`;
* the Kloosterman sum `kloosterman p a b = ∑_{x ∈ Fₚˣ} e_p(ax + b x⁻¹)`,
  its conjugation law `kloosterman_conj`, and the character sum over units
  `units_char_sum`;
* the short-window test vector `Fsum` (denoted `F_p(m)` in the ledger).

All finite-field inverses are the field inverse on `ZMod p` (`p` prime), and the
distinct-residue hypotheses in `KloostermanOrthogonality.lean` are stated by
indexing over the group of units `(ZMod p)ˣ`.

Status: `LEAN_PROVED` (every declaration here is fully proved, no `sorry`).
-/

open Complex

namespace PrimeShortWindow

variable (p : ℕ) [Fact p.Prime]

/-- The standard nontrivial additive character `e_p : ZMod p → ℂ`,
`x ↦ exp(2πi x / p)`, realized as `AddChar.zmod p 1` pushed into `ℂ`. -/
noncomputable def ep : AddChar (ZMod p) ℂ :=
  Circle.coeHom.compAddChar (AddChar.zmod p 1)

@[simp] theorem ep_add (x y : ZMod p) : ep p (x + y) = ep p x * ep p y := by
  simp [ep, AddChar.map_add_eq_mul]

@[simp] theorem ep_zero : ep p 0 = 1 := by simp [ep]

/-- Complex conjugation of the additive character negates the argument. -/
theorem ep_conj (x : ZMod p) : (starRingEnd ℂ) (ep p x) = ep p (-x) := by
  simp only [ep, MonoidHom.compAddChar_apply, Function.comp_apply, AddChar.map_neg_eq_inv,
    Circle.coeHom_apply]
  rw [← Circle.coe_inv_eq_conj, Circle.coe_inv]

/-- The character `ep p` is nontrivial. -/
theorem ep_ne_one : ep p ≠ 1 := by
  intro h
  have hall : ∀ x : ZMod p, (AddChar.zmod p 1) x = 1 := by
    intro x
    have hx : ep p x = 1 := by rw [h]; rfl
    simp only [ep, MonoidHom.compAddChar_apply, Function.comp_apply, Circle.coeHom_apply] at hx
    exact Circle.coe_injective (by simpa using hx)
  have hz : AddChar.zmod p (1 : ZMod p) = AddChar.zmod p (0 : ZMod p) := by
    ext x; rw [hall x]; simp
  exact one_ne_zero (AddChar.zmod_injective hz)

/-- `ep p` is a primitive additive character (any nontrivial character on a
field is primitive). -/
theorem ep_primitive : (ep p).IsPrimitive :=
  AddChar.IsPrimitive.of_ne_one (ep_ne_one p)

/-- Complete-period orthogonality of the additive character:
`∑_{m ∈ Fₚ} e_p(c m) = p·1_{c=0}`. -/
theorem ep_orthogonality (c : ZMod p) :
    ∑ m : ZMod p, ep p (c * m) = if c = 0 then (p : ℂ) else 0 := by
  have h := AddChar.sum_mulShift (ψ := ep p) c (ep_primitive p)
  simp only [mul_comm] at h ⊢
  rw [h]; simp [ZMod.card]

/-- Sum over units of a `ZMod p`-indexed complex function equals the full sum
minus the value at `0`. -/
theorem units_sum_bridge (g : ZMod p → ℂ) :
    ∑ x : (ZMod p)ˣ, g (x : ZMod p) = (∑ x : ZMod p, g x) - g 0 := by
  have key : ∑ x : (ZMod p)ˣ, g (x : ZMod p) = ∑ x ∈ {(0 : ZMod p)}ᶜ, g x := by
    refine Finset.sum_bij' (fun (x : (ZMod p)ˣ) _ => (x : ZMod p))
      (fun (x : ZMod p) (hx : x ∈ ({(0 : ZMod p)}ᶜ : Finset (ZMod p))) =>
        (Units.mk0 x (by simpa using hx)))
      ?_ ?_ ?_ ?_ ?_
    · intro a _
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact a.ne_zero
    · intro a _; exact Finset.mem_univ _
    · intro a _; ext; simp
    · intro a _; simp
    · intro a _; rfl
  have hsplit := Finset.sum_add_sum_compl {(0 : ZMod p)} g
  simp only [Finset.sum_singleton] at hsplit
  rw [key, ← hsplit]; ring

/-- Character sum over the units group:
`∑_{x ∈ Fₚˣ} e_p(c x) = (p·1_{c=0}) − 1`. -/
theorem units_char_sum (c : ZMod p) :
    ∑ x : (ZMod p)ˣ, ep p (c * (x : ZMod p)) = (if c = 0 then (p : ℂ) else 0) - 1 := by
  rw [units_sum_bridge p (fun x => ep p (c * x))]
  simp [ep_orthogonality p c]

/-- The Kloosterman sum `S(a,b;p) = ∑_{x ∈ Fₚˣ} e_p(a x + b x⁻¹)`. -/
noncomputable def kloosterman (a b : ZMod p) : ℂ :=
  ∑ x : (ZMod p)ˣ, ep p (a * (x : ZMod p) + b * ((x : ZMod p))⁻¹)

/-- Conjugation law: `conj S(a,b;p) = S(-a,-b;p)`. -/
theorem kloosterman_conj (a b : ZMod p) :
    (starRingEnd ℂ) (kloosterman p a b) = kloosterman p (-a) (-b) := by
  unfold kloosterman
  rw [map_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [ep_conj]; congr 1; ring

/-- The short-window test vector `F_p(m) = ∑_{q ∈ s} λ_q S(u q⁻¹, m; p)`,
indexed over a finite set `s` of *distinct* nonzero residues (units), with
`u` a fixed unit.  This encodes the distinct-residue hypothesis structurally. -/
noncomputable def Fsum (u : (ZMod p)ˣ) (s : Finset (ZMod p)ˣ) (lam : (ZMod p)ˣ → ℂ)
    (m : ZMod p) : ℂ :=
  ∑ q ∈ s, lam q * kloosterman p ((u * q⁻¹ : (ZMod p)ˣ) : ZMod p) m

end PrimeShortWindow
