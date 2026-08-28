import Mathlib

/-!
# Current programme · Phase J2 · local Euler algebra (append-only)

Source-independent formal algebra for the balanced-seven local factor

  `F_z(p^e) = a_z(p)^e / e!`.

Two things are banked here, and nothing else.

1. **The formal Euler identity** `∑_e a^e/e! · T^e = exp (a T)` (`localEuler_tsum`).
   This is stated for `ℂ` with the honest `tsum`, so no analytic convergence
   obligation is manufactured; Mathlib already supplies the summability.

2. **The generalized von Mangoldt coefficient pattern**

       Λ_F(p)   = a_z(p) · log p,
       Λ_F(p^e) = 0        for e ≥ 2.

   The point of this module is that this is *not* recorded by fiat.  The
   coefficient sequence `lambdaLocal` is pinned by the standard logarithmic
   derivative recursion

       e · F(e) = ∑_{j=1}^{e} Λ(j) · F(e-j),      F(0) = 1,

   and `lambdaLocal_unique` proves that the recursion determines `Λ` uniquely.
   So `lambdaLocal_prime` / `lambdaLocal_prime_power` are genuine consequences
   of the local factor, not a definition dressed up as a theorem.

## DEFINITION PIN

The project contains no "class C" definition of a multiplicative class for
`Λ_F`.  Class-C nomenclature is therefore a **SOURCE / DEFINITION PIN**: no
membership statement is made here.  Only the precise prime-power coefficient
facts above are banked.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LocalEuler

open Finset

/-! ## 1. The local factor -/

/-- The balanced-seven local factor `F(e) = a^e / e!` at a single prime. -/
noncomputable def localF (a : ℂ) (e : ℕ) : ℂ := a ^ e / (Nat.factorial e : ℂ)

@[simp] theorem localF_zero (a : ℂ) : localF a 0 = 1 := by
  simp [localF]

@[simp] theorem localF_one (a : ℂ) : localF a 1 = a := by
  simp [localF]

/-- The factorial step identity: `e · F(e) = a · F(e-1)` for `e ≥ 1`.

This is exactly the cancellation of `1/e!` that makes the factorial-Euler
polarization work, isolated at a single prime. -/
theorem succ_mul_localF (a : ℂ) (d : ℕ) :
    ((d + 1 : ℕ) : ℂ) * localF a (d + 1) = a * localF a d := by
  have hf : (Nat.factorial (d + 1) : ℂ) = ((d + 1 : ℕ) : ℂ) * (Nat.factorial d : ℂ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hne : ((d + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero d)
  have hd : (Nat.factorial d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero d)
  unfold localF
  rw [hf, pow_succ']
  field_simp

/-! ## 2. The formal Euler identity -/

/-- `∑_e (a^e/e!) T^e = exp (a T)`.  Formal power-series content, stated with
Mathlib's `tsum`, so no extra convergence obligation is introduced. -/
theorem localEuler_tsum (a T : ℂ) :
    ∑' e : ℕ, localF a e * T ^ e = Complex.exp (a * T) := by
  have h : ∀ e : ℕ, localF a e * T ^ e = (a * T) ^ e / (Nat.factorial e : ℂ) := by
    intro e; unfold localF; rw [mul_pow]; ring
  simp_rw [h]
  rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]

/-! ## 3. The generalized von Mangoldt coefficient -/

/-- The local generalized von Mangoldt coefficient, with `log p` scaled out:
`Λ(1) = a`, `Λ(e) = 0` for `e ≥ 2`. -/
noncomputable def lambdaLocal (a : ℂ) (e : ℕ) : ℂ := if e = 1 then a else 0

/-- `Λ_F(p) = a_z(p) · log p`. -/
theorem lambdaLocal_prime (a : ℂ) : lambdaLocal a 1 = a := by
  simp [lambdaLocal]

/-- `Λ_F(p^e) = 0` for `e ≥ 2`. -/
theorem lambdaLocal_prime_power (a : ℂ) {e : ℕ} (he : 2 ≤ e) : lambdaLocal a e = 0 := by
  have : e ≠ 1 := by omega
  simp [lambdaLocal, this]

/-- The defining recursion, evaluated: only the `j = 1` term survives. -/
theorem lambdaLocal_conv (a : ℂ) (d : ℕ) :
    ∑ j ∈ Finset.Icc 1 (d + 1), lambdaLocal a j * localF a (d + 1 - j)
      = a * localF a d := by
  rw [Finset.sum_eq_single 1]
  · simp [lambdaLocal]
  · intro j hj hj1
    simp [lambdaLocal, hj1]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩) h

/-- **`lambdaLocal` satisfies the logarithmic-derivative recursion**

  `e · F(e) = ∑_{j=1}^{e} Λ(j) · F(e-j)`   for `e ≥ 1`. -/
theorem lambdaLocal_recursion (a : ℂ) (d : ℕ) :
    ((d + 1 : ℕ) : ℂ) * localF a (d + 1)
      = ∑ j ∈ Finset.Icc 1 (d + 1), lambdaLocal a j * localF a (d + 1 - j) := by
  rw [lambdaLocal_conv, succ_mul_localF]

/-- **Uniqueness.**  Any coefficient sequence satisfying the recursion agrees
with `lambdaLocal` on `e ≥ 1`.  This is what makes
`lambdaLocal_prime` / `lambdaLocal_prime_power` a *derived* prime-power pattern
rather than a definitional stipulation. -/
theorem lambdaLocal_unique (a : ℂ) (g : ℕ → ℂ)
    (hg : ∀ d : ℕ, ((d + 1 : ℕ) : ℂ) * localF a (d + 1)
            = ∑ j ∈ Finset.Icc 1 (d + 1), g j * localF a (d + 1 - j)) :
    ∀ e : ℕ, 1 ≤ e → g e = lambdaLocal a e := by
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro he
    obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
    have key := (hg d).symm.trans (lambdaLocal_recursion a d)
    -- split off the top term `j = d+1` on each side
    have hsplit : ∀ f : ℕ → ℂ,
        ∑ j ∈ Finset.Icc 1 (d + 1), f j * localF a (d + 1 - j)
          = (∑ j ∈ Finset.Icc 1 d, f j * localF a (d + 1 - j)) + f (d + 1) := by
      intro f
      rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ d + 1)]
      simp
    rw [hsplit g, hsplit (lambdaLocal a)] at key
    have hlow : ∑ j ∈ Finset.Icc 1 d, g j * localF a (d + 1 - j)
        = ∑ j ∈ Finset.Icc 1 d, lambdaLocal a j * localF a (d + 1 - j) := by
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [ih j (by omega) hj.1]
    rw [hlow] at key
    exact add_left_cancel key

/-! ## 4. The `log p`-carrying form -/

/-- `Λ_F(p^e) = lambdaLocal a e · log p`. -/
noncomputable def LambdaF (a : ℂ) (p : ℕ) (e : ℕ) : ℂ :=
  lambdaLocal a e * (Real.log p : ℂ)

/-- `Λ_F(p) = a_z(p) · log p`. -/
theorem LambdaF_prime (a : ℂ) (p : ℕ) : LambdaF a p 1 = a * (Real.log p : ℂ) := by
  simp [LambdaF, lambdaLocal_prime]

/-- `Λ_F(p^e) = 0` for `e ≥ 2`. -/
theorem LambdaF_prime_power (a : ℂ) (p : ℕ) {e : ℕ} (he : 2 ≤ e) : LambdaF a p e = 0 := by
  simp [LambdaF, lambdaLocal_prime_power a he]

/-! ## 5. Firewall

No class-C membership is asserted.  No analytic statement about `Λ_F` — in
particular no mean-value, no Siegel–Walfisz, no Bombieri–Vinogradov property —
follows from anything in this module.  The content here is purely the local
formal algebra. -/

/-- Counterguard: the local pattern does **not** by itself pin the value of `a`;
distinct `a` give distinct coefficient sequences, so no statement here can be
read as supplying arithmetic information about `a_z(p)`. -/
theorem lambdaLocal_injective_in_a {a b : ℂ} (h : lambdaLocal a = lambdaLocal b) : a = b := by
  have := congrFun h 1
  simpa [lambdaLocal] using this

end LocalEuler
end CurrentProgramme
end TwinPrimeProject
