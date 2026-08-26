/-
# Gate 1B safe algebra bank — §1–§2: the integer shell and its mod-`r^2` form.

Everything in this file is a finite algebraic fact about integers and about the
ring `ZMod (r^2)`.  There is **no** analytic content, no asymptotics, no sieve
input and no Gate-1B closure statement anywhere in this module.

Physical shell (SHELL):  `q * ℓ = t * r * v + 2`.
-/
import Mathlib

namespace Gate1B

/-! ## §1 Integer shell -/

/-- **(SHELL → shell_sub)** The exact integer identity `q ℓ − t r v = 2`. -/
theorem shell_sub {q l t r v : ℤ} (h : q * l = t * r * v + 2) :
    q * l - t * r * v = 2 := by
  linarith

/-- Converse of `shell_sub`: the two forms of the shell equation agree. -/
theorem shell_eq_iff_shell_sub {q l t r v : ℤ} :
    q * l = t * r * v + 2 ↔ q * l - t * r * v = 2 := by
  constructor <;> intro h <;> linarith

/-! ## §2 Units of `ZMod n` from coprimality -/

/-- If `l` is coprime to the modulus then its cast is a unit of `ZMod n`. -/
theorem isUnit_intCast_of_isCoprime {n : ℕ} {l : ℤ} (h : IsCoprime l (n : ℤ)) :
    IsUnit ((l : ZMod n)) := by
  obtain ⟨a, b, hab⟩ := h
  have hab' := congrArg (fun z : ℤ => (z : ZMod n)) hab
  push_cast at hab'
  exact IsUnit.of_mul_eq_one (b := (a : ZMod n)) (by simpa [mul_comm] using hab')

/-- The unit of `ZMod n` attached to an integer coprime to `n`. -/
noncomputable def coprimeUnit {n : ℕ} {l : ℤ} (h : IsCoprime l (n : ℤ)) : (ZMod n)ˣ :=
  (isUnit_intCast_of_isCoprime h).unit

@[simp] theorem coprimeUnit_val {n : ℕ} {l : ℤ} (h : IsCoprime l (n : ℤ)) :
    ((coprimeUnit h : (ZMod n)ˣ) : ZMod n) = (l : ZMod n) :=
  IsUnit.unit_spec _

/-- Coprimality to `r` upgrades to coprimality to `r ^ 2`. -/
theorem isCoprime_sq_of_isCoprime {l : ℤ} {r : ℕ} (h : IsCoprime l (r : ℤ)) :
    IsCoprime l (((r ^ 2 : ℕ) : ℤ)) := by
  have : IsCoprime l ((r : ℤ) ^ 2) := h.pow_right
  simpa using this

/-! ## §2 (S1): the mod-`r^2` shell congruence, in exact unit form -/

/-- **(S1)** On the shell `q ℓ = t r v + 2`, and with `ℓ` represented by a unit
`lu` of `ZMod n`, one has exactly `q = lu⁻¹ * (2 + r t v)` in `ZMod n`.

No informal modular division occurs: the inverse is the inverse of an explicit
unit of the ring. -/
theorem shell_unit_form {q l t r v : ℤ} {n : ℕ} (h : q * l = t * r * v + 2)
    (lu : (ZMod n)ˣ) (hlu : ((lu : ZMod n)) = (l : ZMod n)) :
    (q : ZMod n)
      = ((lu⁻¹ : (ZMod n)ˣ) : ZMod n) * (2 + (r : ZMod n) * (t : ZMod n) * (v : ZMod n)) := by
  have h1 : ((q * l : ℤ) : ZMod n) = ((t * r * v + 2 : ℤ) : ZMod n) := by
    exact_mod_cast congrArg _ h
  push_cast at h1
  have h2 : (q : ZMod n) * (lu : ZMod n) = 2 + (r : ZMod n) * (t : ZMod n) * (v : ZMod n) := by
    rw [hlu, h1]; ring
  calc (q : ZMod n) = (q : ZMod n) * (lu : ZMod n) * ((lu⁻¹ : (ZMod n)ˣ) : ZMod n) := by
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    _ = ((lu⁻¹ : (ZMod n)ˣ) : ZMod n)
          * (2 + (r : ZMod n) * (t : ZMod n) * (v : ZMod n)) := by rw [h2]; ring

/-- **(S1) in the intended modulus `r ^ 2`**, with the unit produced from
`gcd(ℓ, r) = 1`. -/
theorem shell_mod_rsq {q l t v : ℤ} {r : ℕ} (h : q * l = t * (r : ℤ) * v + 2)
    (hco : IsCoprime l (r : ℤ)) :
    (q : ZMod (r ^ 2))
      = ((coprimeUnit (isCoprime_sq_of_isCoprime hco))⁻¹ : (ZMod (r ^ 2))ˣ)
          * (2 + ((r : ℤ) : ZMod (r ^ 2)) * (t : ZMod (r ^ 2)) * (v : ZMod (r ^ 2))) := by
  exact shell_unit_form (r := (r : ℤ)) h _ (coprimeUnit_val _)

/-- The shell also forces `q` itself to be a unit modulo `r ^ 2` in the presence
of the coprimality hypothesis: the right-hand side of `S1` is a unit. -/
theorem isUnit_q_of_shell {q l t v : ℤ} {r : ℕ} (h : q * l = t * (r : ℤ) * v + 2)
    (hco : IsCoprime l (r : ℤ)) (hr : IsUnit (2 + ((r : ℤ) : ZMod (r ^ 2)) * (t : ZMod (r ^ 2))
      * (v : ZMod (r ^ 2)))) : IsUnit ((q : ZMod (r ^ 2))) := by
  rw [shell_mod_rsq h hco]
  exact (Units.isUnit _).mul hr

end Gate1B
