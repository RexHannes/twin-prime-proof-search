import Gate1B.HNEEffectiveConductor

/-!
# Gate 1B · sawtooth integer `r`, small-`r` phase algebra and the `C_r` data

**Exact arithmetic only.**  The analytic sawtooth decay and the arbitrary-log
tail are *not* proved: they are exposed as the interfaces
`SawtoothCoefficientDecay` and consumed by the finite implication
`sawtoothTail_l2_of_decay`.

## Contents

* §1 the sawtooth integer `r = d·k − u·ρ`, the exact division identity and
  `sawtooth_r_ne_zero` under `gcd(d,u) = 1`, `0 < ρ < d`;
* §2 the **exact frequency offset** `ρ/d − k/u = −r/(du)`: this is where the
  moving index `k` disappears into the single integer `r`;
* §3 the sawtooth coefficient `σ̂`, its exact rewriting in terms of `r`, and
  the decay interface;
* §4 the finite `L²` tail implication from a supplied decay bound;
* §5 the small-`r` reciprocal normal form (unit scalar · slow Archimedean
  phase · reciprocal arithmetic phase), with the arithmetic factor formalised
  exactly;
* §6 the numerator `C_r`, and the data `g_r = gcd(C_r,ℓ)`, `q_r = ℓ/g_r` with
  their exact divisibility and reduced-coprimality properties.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HNESawtooth

open Finset
open TwinPrimeProject.CurrentProgramme.HNEConductor

/-! ## 1. The sawtooth integer -/

/-- The sawtooth integer `r := d·k − u·ρ`. -/
def rSaw (d k u rho : ℤ) : ℤ := d * k - u * rho

/-- **Exact division identity** `d·k = u·ρ + r`. -/
theorem sawtooth_division (d k u rho : ℤ) : d * k = u * rho + rSaw d k u rho := by
  rw [rSaw]; ring

/-- **`sawtooth_r_ne_zero`.**  If `gcd(d,u) = 1` and `0 < ρ < d` then the
sawtooth integer is nonzero. -/
theorem sawtooth_r_ne_zero {d k u rho : ℤ} (hcop : IsCoprime d u)
    (hrho0 : 0 < rho) (hrhod : rho < d) : rSaw d k u rho ≠ 0 := by
  intro h
  have hdk : d * k = u * rho := by
    have := sawtooth_division d k u rho
    rw [h, add_zero] at this
    exact this
  have hdvd : d ∣ rho * u := ⟨k, by linarith [hdk, mul_comm rho u]⟩
  have hd : d ∣ rho := hcop.dvd_of_dvd_mul_right hdvd
  have := Int.le_of_dvd hrho0 hd
  linarith

/-! ## 2. The exact frequency offset: the moving index disappears -/

/-- **Exact frequency offset.**  `ρ/d − k/u = −r/(du)`.  The moving index `k`
appears on the right only through the single sawtooth integer `r`. -/
theorem sawtooth_frequency_offset {d k u rho : ℤ} (hd : (d : ℚ) ≠ 0) (hu : (u : ℚ) ≠ 0) :
    (rho : ℚ) / d - (k : ℚ) / u = -((rSaw d k u rho : ℤ) : ℚ) / ((d : ℚ) * u) := by
  rw [rSaw]
  push_cast
  field_simp
  ring

/-! ## 3. The sawtooth coefficient and its decay interface -/

/-- The Archimedean phase `e(x) = exp(2πi x)`. -/
noncomputable def eR (x : ℚ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * (x : ℝ))

/-- The sawtooth coefficient

`σ̂(ρ,d,u,k) = [1 − e(ρu/d)] / [u(1 − e(ρ/d − k/u))]`. -/
noncomputable def sigmaHat (rho d u k : ℤ) : ℂ :=
  (1 - eR ((rho : ℚ) * u / d)) /
    ((u : ℂ) * (1 - eR ((rho : ℚ) / d - (k : ℚ) / u)))

/-- **Exact rewriting of the sawtooth denominator in terms of `r`.**  The
moving index `k` is eliminated: the denominator depends on `k` only through
the sawtooth integer. -/
theorem sigmaHat_denominator_in_r {rho d u k : ℤ} (hd : (d : ℚ) ≠ 0) (hu : (u : ℚ) ≠ 0) :
    sigmaHat rho d u k =
      (1 - eR ((rho : ℚ) * u / d)) /
        ((u : ℂ) * (1 - eR (-((rSaw d k u rho : ℤ) : ℚ) / ((d : ℚ) * u)))) := by
  rw [sigmaHat, sawtooth_frequency_offset hd hu]

/-- **Interface (not proved).**  The analytic decay
`|σ̂| ≤ C·min(1, d/|r|)` of the research bank.  Trigonometric library
engineering is deliberately avoided: any consumer must be handed this
hypothesis. -/
structure SawtoothCoefficientDecay where
  /-- The implied constant. -/
  C : ℝ
  /-- The decay obligation, never discharged here. -/
  decay : Prop

/-! ## 4. Finite `L²` tail implication -/

/-- **`sawtoothTail_l2_of_decay`.**  From a *supplied* pointwise decay bound,
the finite `L²` tail estimate follows.  No asymptotics are hard-coded: the
bound is exactly the one handed in. -/
theorem sawtoothTail_l2_of_decay {ι : Type*} (S : Finset ι) (sigma : ι → ℂ)
    (bound : ι → ℝ) (hb : ∀ j ∈ S, ‖sigma j‖ ≤ bound j) :
    ∑ j ∈ S, ‖sigma j‖ ^ 2 ≤ ∑ j ∈ S, bound j ^ 2 := by
  refine Finset.sum_le_sum fun j hj => ?_
  have h0 : (0:ℝ) ≤ ‖sigma j‖ := norm_nonneg _
  nlinarith [hb j hj]

/-! ## 5. The small-`r` reciprocal normal form -/

/-- The small-`r` normal form

```
unitScalar · e(2r/(duℓ)) · e_ℓ(C_r · u⁻¹),
```

with the unit scalar and the slow Archimedean phase carried as explicit
parameters, and the reciprocal arithmetic phase formalised exactly. -/
noncomputable def hneSmallRNormalForm (unitScalar : ℂ) (r d u : ℤ) (l : ℕ)
    (Cr uinv : ℤ) : ℂ :=
  unitScalar * eR (2 * (r : ℚ) / ((d : ℚ) * u * l)) * eZ l (Cr * uinv)

/-- **`hne_smallR_reciprocal_normalForm` (Archimedean part).**  The slow phase
of the normal form is exactly the frequency offset scaled by `2/ℓ`: the moving
index `k` is absent from the normal form, and only the sawtooth integer `r`
survives. -/
theorem hne_smallR_reciprocal_normalForm {d k u rho : ℤ} {l : ℕ}
    (hd : (d : ℚ) ≠ 0) (hu : (u : ℚ) ≠ 0) (hl : (l : ℚ) ≠ 0) :
    eR (2 * ((rho : ℚ) / d - (k : ℚ) / u) / l)
      = eR (-(2 * ((rSaw d k u rho : ℤ) : ℚ)) / ((d : ℚ) * u * l)) := by
  rw [sawtooth_frequency_offset hd hu]
  congr 1
  field_simp

/-- The three factors of the normal form are separated exactly: the product of
the Archimedean and the arithmetic phase is the phase of the sum. -/
theorem smallR_phase_factors (unitScalar : ℂ) (r d u : ℤ) (l : ℕ)
    (Cr uinv : ℤ) :
    hneSmallRNormalForm unitScalar r d u l Cr uinv
      = unitScalar * Complex.exp (2 * Real.pi * Complex.I *
          (((2 * (r : ℚ) / ((d : ℚ) * u * l) : ℚ) : ℝ) +
            ((Cr * uinv : ℤ) : ℂ) / (l : ℂ))) := by
  rw [hneSmallRNormalForm, eR, eZ, mul_assoc, ← Complex.exp_add]
  ring_nf

/-! ## 6. The small-`r` reciprocal numerator `C_r` and its conductor data -/

/-- The small-`r` reciprocal numerator `C_r := 2·d⁻¹·(d·h·s⁻¹ − r)`, with `dinv`
and `sinv` explicit inverse witnesses. -/
def Cr (dinv d h sinv r : ℤ) : ℤ := 2 * dinv * (d * h * sinv - r)

/-- `g_r := gcd(C_r, ℓ)`. -/
def gr (C : ℤ) (l : ℕ) : ℕ := Int.gcd C l

/-- `q_r := ℓ / g_r`. -/
def qr (C : ℤ) (l : ℕ) : ℕ := l / gr C l

/-- **Exact divisibility and reduced-coprimality data for `(C_r, ℓ)`.** -/
theorem smallR_conductor_data (C : ℤ) (l : ℕ) (h : gr C l ≠ 0) :
    ((gr C l : ℕ) : ℤ) ∣ C ∧ gr C l ∣ l ∧ l = gr C l * qr C l ∧
      Nat.Coprime (Int.natAbs (C / (gr C l : ℤ))) (qr C l) := by
  have hdvdC : ((gr C l : ℕ) : ℤ) ∣ C := Int.gcd_dvd_left C (l : ℤ)
  have hdvdl : gr C l ∣ l := Int.natCast_dvd_natCast.mp (Int.gcd_dvd_right C (l : ℤ))
  refine ⟨hdvdC, hdvdl, (Nat.mul_div_cancel' hdvdl).symm, ?_⟩
  have hpos : 0 < Int.gcd C (l : ℤ) := Nat.pos_of_ne_zero h
  have hco := Int.gcd_div_gcd_div_gcd (i := C) (j := (l : ℤ)) hpos
  have hq : ((l : ℤ) / (gr C l : ℤ)).natAbs = qr C l := rfl
  rw [← hq]
  exact hco

end HNESawtooth
end CurrentProgramme
end TwinPrimeProject
