import RequestProject.NANC.Gate01.SamePrimeAndExceptionalRow
import RequestProject.NANC.Gate01.GenericCRTResidue

/-!
# Gate 0–1: the generic completion interface (COMP)

The completed covariance form (COMP) of the generic `p ≠ q` stratum is an
**analytic** statement: it needs smooth Poisson summation, a truncation of the
`h`-range, and a bound `|E_e| ≪ D L^{-1} X^{o(1)}` for the resulting error.  It
is therefore recorded here only as an *interface*: the structure
`CompInterface` carries the completed representation as a supplied
proposition.  **No inhabitant of `CompInterface` with a true analytic content is
constructed anywhere in this development**, and nothing below proves COMP.

What *is* proved here is the finite algebra that the COMP phase factorisation
rests on: the CRT splitting of a phase with coprime denominators,

`x / (q m) ≡ (x m̄) / q + (x q̄) / m  (mod 1)`,

in exact integer form and in the exponential form
`e(x/(qm)) = e_q(x m̄) · e_m(x q̄)`.

Status labels:
`COMP_GENERIC_COMPLETION_INTERFACE` (CONDITIONAL / INTERFACE),
the CRT phase splitting is finite and proved.
-/

namespace RouteAFibreFrame
namespace Gate01

open Finset

/-! ### Finite CRT phase splitting -/

/-- **CRT phase splitting (integer form).**  If `m̄` inverts `m` modulo `q` and
`q̄` inverts `q` modulo `m`, then `x ≡ (x m̄) m + (x q̄) q (mod q m)`. -/
theorem crt_phase_splitting {q m x mbar qbar : ℤ}
    (hcop : Nat.Coprime q.natAbs m.natAbs)
    (hm : m * mbar ≡ 1 [ZMOD q]) (hq : q * qbar ≡ 1 [ZMOD m]) :
    x ≡ (x * mbar) * m + (x * qbar) * q [ZMOD q * m] := by
  have hq' : x ≡ (x * mbar) * m + (x * qbar) * q [ZMOD q] := by
    have h1 : x * (m * mbar) ≡ x * 1 [ZMOD q] := hm.mul_left x
    have h2 : (x * qbar) * q ≡ (x * qbar) * 0 [ZMOD q] := by
      refine Int.ModEq.mul_left _ ?_
      exact (Int.modEq_zero_iff_dvd).mpr dvd_rfl
    calc x = x * 1 := by ring
      _ ≡ x * (m * mbar) [ZMOD q] := h1.symm
      _ = (x * mbar) * m + (x * qbar) * 0 := by ring
      _ ≡ (x * mbar) * m + (x * qbar) * q [ZMOD q] := (Int.ModEq.refl _).add h2.symm
  have hm' : x ≡ (x * mbar) * m + (x * qbar) * q [ZMOD m] := by
    have h1 : x * (q * qbar) ≡ x * 1 [ZMOD m] := hq.mul_left x
    have h2 : (x * mbar) * m ≡ (x * mbar) * 0 [ZMOD m] := by
      refine Int.ModEq.mul_left _ ?_
      exact (Int.modEq_zero_iff_dvd).mpr dvd_rfl
    calc x = x * 1 := by ring
      _ ≡ x * (q * qbar) [ZMOD m] := h1.symm
      _ = (x * mbar) * 0 + (x * qbar) * q := by ring
      _ ≡ (x * mbar) * m + (x * qbar) * q [ZMOD m] := h2.symm.add (Int.ModEq.refl _)
  exact (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hq', hm'⟩

/-- **CRT phase splitting (rational form).**  The three fractions differ by an
integer: `x/(qm) = (x m̄)/q + (x q̄)/m + t` for some `t : ℤ`. -/
theorem crt_phase_splitting_rat {q m x mbar qbar : ℤ} (hq0 : q ≠ 0) (hm0 : m ≠ 0)
    (hcop : Nat.Coprime q.natAbs m.natAbs)
    (hm : m * mbar ≡ 1 [ZMOD q]) (hq : q * qbar ≡ 1 [ZMOD m]) :
    ∃ t : ℤ, (x : ℚ) / ((q : ℚ) * (m : ℚ))
      = ((x * mbar : ℤ) : ℚ) / (q : ℚ) + ((x * qbar : ℤ) : ℚ) / (m : ℚ) + (t : ℚ) := by
  obtain ⟨t, ht⟩ := (Int.modEq_iff_dvd.mp (crt_phase_splitting hcop hm hq))
  refine ⟨-t, ?_⟩
  have hqQ : (q : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hq0
  have hmQ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm0
  have ht' : ((x * mbar) * m + (x * qbar) * q - x : ℤ) = q * m * t := ht
  have : ((x * mbar) * m + (x * qbar) * q - x : ℚ) = (q : ℚ) * (m : ℚ) * (t : ℚ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) ht'
  push_cast
  push_cast at this
  field_simp
  linarith [this]

/-- **CRT phase splitting (exponential form).**  With `e(z) = exp(2πi z)`,
`e(x/(qm)) = e(x m̄ / q) · e(x q̄ / m)`. -/
theorem crt_phase_splitting_exp {q m x mbar qbar : ℤ} (hq0 : q ≠ 0) (hm0 : m ≠ 0)
    (hcop : Nat.Coprime q.natAbs m.natAbs)
    (hm : m * mbar ≡ 1 [ZMOD q]) (hq : q * qbar ≡ 1 [ZMOD m]) :
    Complex.exp (2 * Real.pi * Complex.I * ((x : ℂ) / ((q : ℂ) * (m : ℂ))))
      = Complex.exp (2 * Real.pi * Complex.I * (((x * mbar : ℤ) : ℂ) / (q : ℂ)))
        * Complex.exp (2 * Real.pi * Complex.I * (((x * qbar : ℤ) : ℂ) / (m : ℂ))) := by
  obtain ⟨t, ht⟩ := crt_phase_splitting_rat (x := x) hq0 hm0 hcop hm hq
  have htC : (x : ℂ) / ((q : ℂ) * (m : ℂ))
      = ((x * mbar : ℤ) : ℂ) / (q : ℂ) + ((x * qbar : ℤ) : ℂ) / (m : ℂ) + (t : ℂ) := by
    exact_mod_cast congrArg (fun z : ℚ => (z : ℂ)) ht
  rw [htC, mul_add, mul_add, Complex.exp_add, Complex.exp_add]
  have : Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) = 1 := by
    rw [show (2 : ℂ) * Real.pi * Complex.I * (t : ℂ) = (t : ℂ) * (2 * Real.pi * Complex.I) by ring]
    exact Complex.exp_int_mul_two_pi_mul_I t
  rw [this, mul_one]

/-! ### The COMP interface -/

/-- The structural (finite) side conditions of the generic completion: a common
smooth weight, `p ≠ q`, `p, q ∤ m m'`, `m' = m + k r`, the canonical congruence
`r α ≡ 2 (mod m)`, and the truncated frequency range `0 < |h| ≤ (pq/D) log^C X`.
These are recorded as data; they are exactly the hypotheses under which the
completed form is asserted outside Lean. -/
structure CompSideConditions where
  /-- `p ≠ q` in the generic stratum. -/
  distinct_primes : Prop
  /-- `p, q ∤ m m'`. -/
  coprime_to_moduli : Prop
  /-- `m' = m + k r`. -/
  shifted_modulus : Prop
  /-- The canonical congruence `r α ≡ 2 (mod m)`, proved in
  `Gate01.canonical_congruence`. -/
  canonical_congruence : Prop
  /-- The truncated frequency range `0 < |h| ≤ (p q / D) log^C X`. -/
  truncated_frequencies : Prop
  /-- The common smooth weight `W_D`. -/
  common_smooth_weight : Prop

/-- **COMP interface.**  The completed covariance representation together with
the error bound `|E_e| ≪ D L^{-1} X^{o(1)}`, supplied from outside Lean.  This
is an interface, not a theorem: no inhabitant is constructed here. -/
structure CompInterface where
  /-- The finite side conditions of the stratum. -/
  side : CompSideConditions
  /-- The completed covariance representation `C_e = (main completed sum) + E_e`
  together with the interface assumption `|E_e| ≪ D L^{-1} X^{o(1)}`. -/
  representation : Prop

end Gate01
end RouteAFibreFrame
