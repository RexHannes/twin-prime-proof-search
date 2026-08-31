import Mathlib

/-!
# Gate 1B · HNE effective-conductor arithmetic and residue-compressed Fourier bound

**Exact arithmetic and exact finite `L²` algebra.**

## Contents

* §1 the normalised additive phase `eZ q a = e(a/q)`, its congruence
  invariance and its exact scaling `e_{gq}(gc) = e_q(c)`;
* §2 the **effective conductor** data `g = gcd(C,ℓ)`, `ℓ = g·q_eff`,
  `C = g·C₀`, `gcd(C₀,q_eff) = 1`;
* §3 the exact conductor reduction of the reciprocal phase
  (`hne_effectiveConductor_phase_reduction`): the phase modulo `ℓ` **is** a
  phase modulo `q_eff = ℓ/gcd(C,ℓ)`, with the inverses reduced modulo
  `q_eff`;
* §4 residue compression modulo `q_eff`, the exact fibre `L²` bounds
  (`compress_l2_le`) and the exact bilinear compression identity;
* §5 the residue-compressed Fourier bound
  (`hne_effectiveConductor_fourier_bound`), derived from an explicit
  compressed-kernel operator hypothesis — the asymptotic threshold
  `q_eff ≥ Y^{3/2} L^B` is **not** formalised and appears only as the
  interface `HNEEffectiveConductorAdmissible`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HNEConductor

open Finset

/-! ## 1. The normalised additive phase -/

/-- `eZ q a = e(a/q) = exp(2πi a/q)`. -/
noncomputable def eZ (q : ℕ) (a : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) / (q : ℂ)))

@[simp] theorem eZ_zero (q : ℕ) : eZ q 0 = 1 := by simp [eZ]

/-- The phase only depends on the numerator modulo the denominator. -/
theorem eZ_congr {q : ℕ} (hq : q ≠ 0) {a b : ℤ} (h : (q : ℤ) ∣ a - b) :
    eZ q a = eZ q b := by
  obtain ⟨k, hk⟩ := h
  have ha : a = b + q * k := by linarith [hk]
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  rw [eZ, eZ, ha]
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (((b : ℂ) + (q : ℂ) * (k : ℂ)) / (q : ℂ))
      = 2 * (Real.pi : ℂ) * Complex.I * ((b : ℂ) / (q : ℂ))
        + (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by field_simp,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **Exact conductor scaling.**  `e_{g·q}(g·c) = e_q(c)`. -/
theorem eZ_scale {g q : ℕ} (hg : g ≠ 0) (c : ℤ) :
    eZ (g * q) ((g : ℤ) * c) = eZ q c := by
  have hgC : (g : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hg
  rw [eZ, eZ]
  congr 2
  push_cast
  rw [mul_div_mul_left _ _ hgC]

/-! ## 2. The effective-conductor data -/

/-- `ℓ = gcd(C,ℓ) · q_eff` with `q_eff = ℓ / gcd(C,ℓ)`. -/
theorem effectiveConductor_split (C l : ℕ) (h : Nat.gcd C l ≠ 0) :
    l = Nat.gcd C l * (l / Nat.gcd C l) ∧ C = Nat.gcd C l * (C / Nat.gcd C l) ∧
      Nat.Coprime (C / Nat.gcd C l) (l / Nat.gcd C l) := by
  refine ⟨(Nat.mul_div_cancel' (Nat.gcd_dvd_right C l)).symm,
    (Nat.mul_div_cancel' (Nat.gcd_dvd_left C l)).symm,
    Nat.coprime_div_gcd_div_gcd (Nat.pos_of_ne_zero h)⟩

/-! ## 3. The exact conductor reduction of the reciprocal phase -/

/-- Inverses reduce: if `q ∣ ℓ`, `u` is an inverse of `m` mod `ℓ` and `u'` is an
inverse of `m` mod `q`, then `u ≡ u' (mod q)`. -/
theorem inverse_reduce {q l m u u' : ℤ} (hql : q ∣ l)
    (hu : l ∣ m * u - 1) (hu' : q ∣ m * u' - 1) : q ∣ u - u' := by
  have h1 : q ∣ m * u - 1 := dvd_trans hql hu
  have key : u - u' = u' * ((m * u - 1) - (m * u' - 1)) - (m * u' - 1) * (u - u') := by
    ring
  rw [key]
  exact dvd_sub (Dvd.dvd.mul_left (dvd_sub h1 hu') u') (Dvd.dvd.mul_right hu' _)

/-- **`hne_effectiveConductor_phase_reduction`.**  With

```
ℓ = g·q_eff,   C = g·C₀,
m·u ≡ 1 (mod ℓ),  n·v ≡ 1 (mod ℓ),
m·u' ≡ 1 (mod q_eff),  n·v' ≡ 1 (mod q_eff),
```

the reciprocal phase modulo `ℓ` is exactly the reciprocal phase modulo the
**effective conductor** `q_eff`:

```
e_ℓ(C·u·v) = e_{q_eff}(C₀·u'·v').
```

The effective conductor is `ℓ/gcd(C,ℓ)`, never the full `ℓ`. -/
theorem hne_effectiveConductor_phase_reduction
    {l g qEff : ℕ} {C C0 m n u v u' v' : ℤ}
    (hl : l = g * qEff) (hC : C = (g : ℤ) * C0) (hg : g ≠ 0) (hq : qEff ≠ 0)
    (hu : (l : ℤ) ∣ m * u - 1) (hv : (l : ℤ) ∣ n * v - 1)
    (hu' : (qEff : ℤ) ∣ m * u' - 1) (hv' : (qEff : ℤ) ∣ n * v' - 1) :
    eZ l (C * u * v) = eZ qEff (C0 * u' * v') := by
  have hql : (qEff : ℤ) ∣ (l : ℤ) := ⟨(g : ℤ), by rw [hl]; push_cast; ring⟩
  have hu2 : (qEff : ℤ) ∣ u - u' := inverse_reduce hql hu hu'
  have hv2 : (qEff : ℤ) ∣ v - v' := inverse_reduce hql hv hv'
  have step1 : eZ l (C * u * v) = eZ qEff (C0 * u * v) := by
    rw [hl, hC, show (g : ℤ) * C0 * u * v = (g : ℤ) * (C0 * u * v) by ring]
    exact eZ_scale hg _
  rw [step1]
  refine eZ_congr hq ?_
  have key : C0 * u * v - C0 * u' * v' = C0 * v * (u - u') + C0 * u' * (v - v') := by
    ring
  rw [key]
  exact dvd_add (Dvd.dvd.mul_left hu2 _) (Dvd.dvd.mul_left hv2 _)

/-! ## 4. Residue compression modulo the effective conductor -/

variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

/-- The residue-compressed vector: `A_q(x) = ∑_{i : cls i = x} A(i)`. -/
noncomputable def compress {q : ℕ} (I : Finset ι) (A : ι → ℂ)
    (cls : ι → ZMod q) (x : ZMod q) : ℂ :=
  ∑ i ∈ I with cls i = x, A i

omit [DecidableEq ι] in
/-- **Exact fibre `L²` bound.**  If every residue fibre has at most `fibre`
elements then `‖A_q‖₂² ≤ fibre · ‖A‖₂²`. -/
theorem compress_l2_le {q : ℕ} [NeZero q] (I : Finset ι) (A : ι → ℂ)
    (cls : ι → ZMod q) (fibre : ℝ)
    (hfib : ∀ x : ZMod q, ((I.filter fun i => cls i = x).card : ℝ) ≤ fibre) :
    ∑ x : ZMod q, ‖compress I A cls x‖ ^ 2 ≤ fibre * ∑ i ∈ I, ‖A i‖ ^ 2 := by
  classical
  have hpt : ∀ x : ZMod q, ‖compress I A cls x‖ ^ 2
      ≤ fibre * ∑ i ∈ I with cls i = x, ‖A i‖ ^ 2 := by
    intro x
    set s := I.filter fun i => cls i = x with hs
    have h1 : ‖compress I A cls x‖ ≤ ∑ i ∈ s, ‖A i‖ := norm_sum_le _ _
    have h2 : (∑ i ∈ s, ‖A i‖) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖A i‖ ^ 2 := by
      have := Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) (fun i => ‖A i‖)
      simpa using this
    have h3 : ‖compress I A cls x‖ ^ 2 ≤ (∑ i ∈ s, ‖A i‖) ^ 2 := by
      nlinarith [h1, norm_nonneg (compress I A cls x)]
    have h4 : (s.card : ℝ) * ∑ i ∈ s, ‖A i‖ ^ 2 ≤ fibre * ∑ i ∈ s, ‖A i‖ ^ 2 := by
      have hnn : (0:ℝ) ≤ ∑ i ∈ s, ‖A i‖ ^ 2 :=
        Finset.sum_nonneg fun _ _ => by positivity
      exact mul_le_mul_of_nonneg_right (hfib x) hnn
    linarith
  calc ∑ x : ZMod q, ‖compress I A cls x‖ ^ 2
      ≤ ∑ x : ZMod q, fibre * ∑ i ∈ I with cls i = x, ‖A i‖ ^ 2 :=
        Finset.sum_le_sum fun x _ => hpt x
    _ = fibre * ∑ x : ZMod q, ∑ i ∈ I with cls i = x, ‖A i‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = fibre * ∑ i ∈ I, ‖A i‖ ^ 2 := by
        rw [Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (cls i))]

omit [DecidableEq ι] [DecidableEq κ] in
/-- **Exact bilinear compression identity.**  A bilinear form whose kernel
depends on the indices only through their residues modulo `q` is exactly the
compressed bilinear form. -/
theorem bilinear_compress {q : ℕ} [NeZero q] (I : Finset ι) (J : Finset κ)
    (A : ι → ℂ) (B : κ → ℂ) (clsA : ι → ZMod q) (clsB : κ → ZMod q)
    (K : ZMod q → ZMod q → ℂ) :
    ∑ i ∈ I, ∑ j ∈ J, A i * B j * K (clsA i) (clsB j)
      = ∑ x : ZMod q, ∑ y : ZMod q,
          compress I A clsA x * compress J B clsB y * K x y := by
  classical
  have expand : ∀ x y : ZMod q,
      compress I A clsA x * compress J B clsB y * K x y
        = ∑ i ∈ I with clsA i = x, ∑ j ∈ J with clsB j = y,
            A i * B j * K (clsA i) (clsB j) := by
    intro x y
    rw [compress, compress, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
  symm
  calc ∑ x : ZMod q, ∑ y : ZMod q,
        compress I A clsA x * compress J B clsB y * K x y
      = ∑ x : ZMod q, ∑ y : ZMod q, ∑ i ∈ I with clsA i = x,
          ∑ j ∈ J with clsB j = y, A i * B j * K (clsA i) (clsB j) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => expand x y
    _ = ∑ x : ZMod q, ∑ i ∈ I with clsA i = x, ∑ y : ZMod q,
          ∑ j ∈ J with clsB j = y, A i * B j * K (clsA i) (clsB j) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ x : ZMod q, ∑ i ∈ I with clsA i = x, ∑ j ∈ J,
          A i * B j * K (clsA i) (clsB j) :=
        Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun i _ =>
          Finset.sum_fiberwise_of_maps_to (fun j _ => Finset.mem_univ (clsB j)) _
    _ = ∑ i ∈ I, ∑ j ∈ J, A i * B j * K (clsA i) (clsB j) :=
        Finset.sum_fiberwise_of_maps_to (fun i _ => Finset.mem_univ (clsA i)) _

/-! ## 5. The residue-compressed Fourier bound -/

omit [DecidableEq ι] [DecidableEq κ] in
/-- **`hne_effectiveConductor_fourier_bound`.**  Given the compressed-kernel
operator bound as an explicit hypothesis, residue compression yields

```
|R_C| ≤ √(q_eff · fibreA · fibreB) · ‖A‖₂ · ‖B‖₂.
```

The operator hypothesis `hK` is exactly the finite Fourier input; it is not
proved here. -/
theorem hne_effectiveConductor_fourier_bound {q : ℕ} [NeZero q]
    (I : Finset ι) (J : Finset κ) (A : ι → ℂ) (B : κ → ℂ)
    (clsA : ι → ZMod q) (clsB : κ → ZMod q) (K : ZMod q → ZMod q → ℂ)
    (fibreA fibreB : ℝ) (hA : 0 ≤ fibreA) (hB : 0 ≤ fibreB)
    (hfibA : ∀ x : ZMod q, ((I.filter fun i => clsA i = x).card : ℝ) ≤ fibreA)
    (hfibB : ∀ y : ZMod q, ((J.filter fun j => clsB j = y).card : ℝ) ≤ fibreB)
    (hK : ∀ a b : ZMod q → ℂ,
      ‖∑ x : ZMod q, ∑ y : ZMod q, a x * b y * K x y‖
        ≤ Real.sqrt q * Real.sqrt (∑ x : ZMod q, ‖a x‖ ^ 2) *
            Real.sqrt (∑ y : ZMod q, ‖b y‖ ^ 2)) :
    ‖∑ i ∈ I, ∑ j ∈ J, A i * B j * K (clsA i) (clsB j)‖
      ≤ Real.sqrt (q * fibreA * fibreB) *
          Real.sqrt (∑ i ∈ I, ‖A i‖ ^ 2) * Real.sqrt (∑ j ∈ J, ‖B j‖ ^ 2) := by
  classical
  have hnormA : (0:ℝ) ≤ ∑ i ∈ I, ‖A i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hnormB : (0:ℝ) ≤ ∑ j ∈ J, ‖B j‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  rw [bilinear_compress I J A B clsA clsB K]
  have h1 := hK (compress I A clsA) (compress J B clsB)
  have h2 : Real.sqrt (∑ x : ZMod q, ‖compress I A clsA x‖ ^ 2)
      ≤ Real.sqrt (fibreA * ∑ i ∈ I, ‖A i‖ ^ 2) :=
    Real.sqrt_le_sqrt (compress_l2_le I A clsA fibreA hfibA)
  have h3 : Real.sqrt (∑ y : ZMod q, ‖compress J B clsB y‖ ^ 2)
      ≤ Real.sqrt (fibreB * ∑ j ∈ J, ‖B j‖ ^ 2) :=
    Real.sqrt_le_sqrt (compress_l2_le J B clsB fibreB hfibB)
  have hchain :
      Real.sqrt q * Real.sqrt (∑ x : ZMod q, ‖compress I A clsA x‖ ^ 2) *
          Real.sqrt (∑ y : ZMod q, ‖compress J B clsB y‖ ^ 2)
        ≤ Real.sqrt q * Real.sqrt (fibreA * ∑ i ∈ I, ‖A i‖ ^ 2) *
            Real.sqrt (fibreB * ∑ j ∈ J, ‖B j‖ ^ 2) := by
    gcongr
  have hfactor :
      Real.sqrt q * Real.sqrt (fibreA * ∑ i ∈ I, ‖A i‖ ^ 2) *
          Real.sqrt (fibreB * ∑ j ∈ J, ‖B j‖ ^ 2)
        = Real.sqrt (q * fibreA * fibreB) *
            Real.sqrt (∑ i ∈ I, ‖A i‖ ^ 2) * Real.sqrt (∑ j ∈ J, ‖B j‖ ^ 2) := by
    rw [Real.sqrt_mul hA, Real.sqrt_mul hB, Real.sqrt_mul (by positivity : (0:ℝ) ≤ (q:ℝ) * fibreA),
      Real.sqrt_mul (Nat.cast_nonneg q)]
    ring
  exact le_trans h1 (le_trans hchain (le_of_eq hfactor))

/-! ## 6. The asymptotic threshold: interface only -/

/-- **Interface (research-banked, not proved).**  The admissibility condition
`q_eff ≥ Y^{3/2} L^B` of the research bank.  The exponent infrastructure is not
formalised, so the condition is carried as a `Prop` field. -/
structure HNEEffectiveConductorAdmissible where
  /-- The effective conductor. -/
  qEff : ℕ
  /-- The research threshold, as an explicit unproved condition. -/
  thresholdCondition : Prop
  /-- The compressed-kernel operator input. -/
  operatorInput : Prop

/-- Metadata: research status of the effective-conductor closure. -/
def hneEffectiveConductorStatus : String :=
  "HNE-APRECIPROCAL-EFFECTIVE-CONDUCTOR45: ANALYTICALLY BANKED (research); " ++
    "formal content: exact conductor reduction + exact compressed L2 algebra."

end HNEConductor
end CurrentProgramme
end TwinPrimeProject
