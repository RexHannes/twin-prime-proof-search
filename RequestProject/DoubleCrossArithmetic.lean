import Mathlib

/-!
# Double-cross modular arithmetic (§6, §13)

This module machine-checks the *algebraic core* of the double-cross sector: the
residual coprimality after full prime-power extraction, the CRT reconstruction of
the collapse residue `c mod D`, and the independence of that residue from the
chosen integer lift.

The full phase factorisation (§6.3) and the one-modulus Fourier separation (§6.4)
are analytic/Fourier statements that are only externally audited; they are exposed
as interfaces in `DependencyInterfaces`, not proved here.  Accordingly these
lemmas are the `LEAN_PROVED_CORE` of `RESIDUAL_COLLAPSE_PROVED` and
`DOUBLE_CROSS_PRIMEPOWER_EXTRACTION`.
-/

namespace ShiftedMobiusBank

/-- §6.1 / §13(1) — residual coprimality after full prime-power extraction.

With `a = s₁·A`, `b = s₂·B`, and the inverse-domain coprimalities that hold in the
Kloosterman setting (`Coprime a b`, `Coprime m₁ a`, `Coprime m₂ b`, and
`A, B` coprime to the prime supports they were stripped of), the residual
variables `A, B` are coprime to `s₁·s₂·m₁·m₂`.  In particular `(A, D m₁ m₂) = 1`
and `(B, D m₁ m₂) = 1` with `D = s₁ s₂`. -/
theorem double_cross_residual_coprime
    {a b s1 s2 A B m1 m2 : ℕ}
    (ha : a = s1 * A) (hb : b = s2 * B)
    (hab : Nat.Coprime a b)
    (hm1a : Nat.Coprime m1 a) (hm2b : Nat.Coprime m2 b)
    (hAm2 : Nat.Coprime A m2) (hBm1 : Nat.Coprime B m1)
    (hAs1 : Nat.Coprime A s1) (hBs2 : Nat.Coprime B s2) :
    Nat.Coprime A (s1 * s2 * m1 * m2) ∧
    Nat.Coprime B (s1 * s2 * m1 * m2) := by
  rw [ha, hb] at hab
  have hAs2 : Nat.Coprime A s2 :=
    Nat.Coprime.coprime_dvd_right (dvd_mul_right s2 B)
      (Nat.Coprime.coprime_dvd_left (dvd_mul_left A s1) hab)
  rw [ha] at hm1a
  have hAm1 : Nat.Coprime A m1 :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left A s1) (Nat.Coprime.symm hm1a)
  rw [hb] at hm2b
  have hBm2 : Nat.Coprime B m2 :=
    Nat.Coprime.coprime_dvd_left (dvd_mul_left B s2) (Nat.Coprime.symm hm2b)
  have hBs1 : Nat.Coprime B s1 := by
    have h1 : Nat.Coprime (s1 * A) B :=
      Nat.Coprime.coprime_dvd_right (dvd_mul_left B s2) hab
    exact Nat.Coprime.coprime_dvd_right (dvd_mul_right s1 A) h1.symm
  have hAfull : Nat.Coprime A (s1 * s2 * m1 * m2) :=
    (((hAs1.mul_right hAs2).mul_right hAm1).mul_right hAm2)
  have hBfull : Nat.Coprime B (s1 * s2 * m1 * m2) :=
    (((hBs1.mul_right hBs2).mul_right hBm1).mul_right hBm2)
  exact ⟨hAfull, hBfull⟩

/-- §6.1 — coprimality of the extracted prime-power parts `(s₁, s₂) = 1`, in the
form used downstream: if `s₁ ∣ a`, `s₂ ∣ b`, and `Coprime a b`, then
`Coprime s₁ s₂`. -/
theorem primepower_parts_coprime {a b s1 s2 : ℕ}
    (hs1 : s1 ∣ a) (hs2 : s2 ∣ b) (hab : Nat.Coprime a b) :
    Nat.Coprime s1 s2 :=
  (Nat.Coprime.coprime_dvd_left hs1 hab).coprime_dvd_right hs2

/-- §6.2 / §13(2,3) — CRT reconstruction of the collapse residue.

For coprime moduli `s₁, s₂` and prescribed residues `r₁ mod s₁`, `r₂ mod s₂`
(in the application `r₁ = m₁⁻¹ mod s₁`, `r₂ = m₂⁻¹ mod s₂`), there is a *unique*
residue `c mod (s₁ s₂)` reducing to `r₁` and `r₂`.  This is the exact algebraic
content of the residual-collapse identity: the two cross-terms are governed by a
single residue `c mod D`. -/
theorem crt_residual_collapse_core {s1 s2 : ℕ} (h : Nat.Coprime s1 s2)
    (r1 : ZMod s1) (r2 : ZMod s2) :
    ∃! c : ZMod (s1 * s2), (ZMod.chineseRemainder h) c = (r1, r2) := by
  refine ⟨(ZMod.chineseRemainder h).symm (r1, r2),
    (ZMod.chineseRemainder h).apply_symm_apply _, ?_⟩
  intro y hy
  apply (ZMod.chineseRemainder h).injective
  rw [hy, (ZMod.chineseRemainder h).apply_symm_apply]

/-- §13(6) — independence of the chosen integer lift of the collapse residue.
If two integer lifts agree modulo `D`, then multiplying by any fixed factor
`k` keeps them equal modulo `D`, so the downstream phase does not depend on the
lift. -/
theorem crt_lift_independence {D : ℕ} (x y k : ℤ)
    (hxy : (x : ZMod D) = (y : ZMod D)) :
    ((x * k : ℤ) : ZMod D) = ((y * k : ℤ) : ZMod D) := by
  push_cast
  rw [hxy]

end ShiftedMobiusBank
