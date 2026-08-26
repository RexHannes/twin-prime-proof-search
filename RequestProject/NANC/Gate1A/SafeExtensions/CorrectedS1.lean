/-
# NANC Gate 1A v9.2/v9.3/v9.4 — the corrected quotient-cell coefficient `S1`
# and the finite Fourier source match

Everything here is an **exact finite identity** about the additive phase

    e_n(k) = exp (2 π i k / n).

With

    C = p*q*r,   N = p*r,   I_j = j*N + [0,N),

the quotient-cell coefficient is defined *from the finite interval sum*

    beta_j(h) = (1/C) ∑_{s ∈ [0,N)} e_C(-h (jN + s)),

and we prove, in this order,

* `quotientCell_phaseFactor` — `beta_j(h) = e_q(-j h) · beta_0(h)`;
* `correctedS1_closed_form` — the **permanent S1 normalisation**

      beta_j^circ(h) = e_q(-j h) · (1 - e_q(-h)) / (C · (1 - e_C(-h)))   (h ≢ 0),

  with `beta_j^circ(0) = 0`;
* `correctedQuotient_fourier` — finite Fourier inversion for the centred cell:

      1_{I_j}(s*) - 1/q = ∑_{h ≠ 0} beta_j^circ(h) e_C(h s*);

* `correctedQuotient_crt_phase` — the CRT splitting of `e_C(h s)`;
* `correctedQuotient_authoritative_match` — with the Fourier kernel `e_C(-h s)`
  and the sign convention `c = -2` (i.e. `d s ≡ 2 mod q`, the same right-hand
  side as the `p*r`-congruence) the arithmetic factors are **exactly**

      e_{p r}(-2 h · inverse(q m))   and   e_q(-2 h · inverse(p r d));

  `correctedQuotient_match_c_two` records the `c = +2` variant, whose `q`-factor
  matches the authoritative one-sided phase while the `p*r`-factor carries the
  opposite sign — the sign convention is therefore *pinned*, not free.

The quotient scale is `U_q = q/H`, **not** `H/q`; `Uq_div_q` and
`Uq_ne_reciprocal_of_ne` bank the normalisation `U_q / q = 1/H` and the
firewall.

**No analytic Poisson/Schwartz estimate appears anywhere in this file.**
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V92

open Finset

/-! ## 1. The additive phase `e_n` on integers -/

/-- `e_n(k) = exp (2 π i k / n)`. -/
noncomputable def ee (n : ℕ) (k : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (n : ℂ))

@[simp] theorem ee_zero (n : ℕ) : ee n 0 = 1 := by simp [ee]

theorem ee_add (n : ℕ) (k l : ℤ) : ee n (k + l) = ee n k * ee n l := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ee_neg (n : ℕ) (k : ℤ) : ee n (-k) = (ee n k)⁻¹ := by
  unfold ee
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem ee_period (n : ℕ) (hn : n ≠ 0) (k t : ℤ) : ee n (k + n * t) = ee n k := by
  unfold ee
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have h : (2 * Real.pi * Complex.I * ((k + n * t : ℤ) : ℂ) / (n : ℂ))
      = 2 * Real.pi * Complex.I * (k : ℂ) / (n : ℂ) + (t : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem ee_congr {n : ℕ} (hn : n ≠ 0) {a b : ℤ} (h : (n : ℤ) ∣ (a - b)) : ee n a = ee n b := by
  obtain ⟨t, ht⟩ := h
  have hab : a = b + n * t := by omega
  rw [hab, ee_period n hn]

theorem ee_pow (n : ℕ) (k : ℤ) : ∀ s : ℕ, ee n (k * s) = (ee n k) ^ s := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
      have h : k * ((s : ℤ) + 1) = k * s + k := by ring
      push_cast
      rw [h, ee_add, ih, pow_succ]

theorem ee_eq_one_iff {n : ℕ} (hn : n ≠ 0) (k : ℤ) : ee n k = 1 ↔ (n : ℤ) ∣ k := by
  constructor
  · intro h
    rw [ee, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn
    field_simp at hm
    have hkm : k = n * m := by exact_mod_cast hm
    exact ⟨m, hkm⟩
  · intro h
    have h2 : ee n k = ee n 0 := ee_congr hn (by simpa using h)
    rw [h2, ee_zero]

/-- Rescaling the modulus: `e_N(k) = e_{N q}(k q)`. -/
theorem ee_scale {N q : ℕ} (hN : N ≠ 0) (hq : q ≠ 0) (k : ℤ) :
    ee N k = ee (N * q) (k * q) := by
  unfold ee
  congr 1
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN
  have hqc : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  push_cast
  field_simp

/-- Collapsing the modulus: `e_{N q}(k N) = e_q(k)`. -/
theorem ee_collapse {N q : ℕ} (hN : N ≠ 0) (hq : q ≠ 0) (k : ℤ) :
    ee (N * q) (k * N) = ee q k := by
  rw [ee_scale hq hN k, Nat.mul_comm q N]

/-- **Finite additive orthogonality** on `[0, n)`. -/
theorem sum_ee_range {n : ℕ} (hn : n ≠ 0) (t : ℤ) :
    ∑ h ∈ range n, ee n ((h : ℤ) * t) = if (n : ℤ) ∣ t then (n : ℂ) else 0 := by
  have hterm : ∀ h ∈ range n, ee n ((h : ℤ) * t) = (ee n t) ^ h := by
    intro h _
    rw [mul_comm, ee_pow]
  rw [Finset.sum_congr rfl hterm]
  by_cases hdvd : (n : ℤ) ∣ t
  · rw [if_pos hdvd, (ee_eq_one_iff hn t).2 hdvd]
    simp
  · rw [if_neg hdvd]
    have hne : ee n t ≠ 1 := fun hc => hdvd ((ee_eq_one_iff hn t).1 hc)
    rw [geom_sum_eq hne]
    have hpow : (ee n t) ^ n = 1 := by
      rw [← ee_pow n t n]
      exact (ee_eq_one_iff hn _).2 ⟨t, by ring⟩
    rw [hpow]
    simp

/-! ## 2. The quotient cell coefficient `beta_j` -/

variable (p q r : ℕ)

/-- The uncentred quotient-cell coefficient
`beta_j(h) = (1/C) ∑_{s<N} e_C(-h(jN+s))`, defined from the finite interval
sum. -/
noncomputable def betaCell (j h : ℤ) : ℂ :=
  (1 / ((p * q * r : ℕ) : ℂ)) *
    ∑ s ∈ range (p * r), ee (p * q * r) (-(h * ((j * (p * r) + s : ℤ))))

/-- The centred coefficient: `beta_j^circ(0) = 0`, `beta_j^circ(h) = beta_j(h)`
otherwise. -/
noncomputable def betaCellCentred (j h : ℤ) : ℂ :=
  if ((p * q * r : ℕ) : ℤ) ∣ h then 0 else betaCell p q r j h

/-- **Quotient-cell phase factor.**  `beta_j(h) = e_q(-j h) · beta_0(h)`. -/
theorem quotientCell_phaseFactor (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (j h : ℤ) :
    betaCell p q r j h = ee q (-(j * h)) * betaCell p q r 0 h := by
  have hN : p * r ≠ 0 := Nat.mul_ne_zero hp hr
  have hCsplit : p * q * r = (p * r) * q := by ring
  have hterm : ∀ s ∈ range (p * r),
      ee (p * q * r) (-(h * ((j * (p * r) + s : ℤ))))
        = ee q (-(j * h)) * ee (p * q * r) (-(h * (((0 : ℤ) * (p * r) + s : ℤ)))) := by
    intro s _
    have h1 : -(h * ((j * (p * r) + s : ℤ)))
        = (-(j * h)) * ((p * r : ℕ) : ℤ) + -(h * (s : ℤ)) := by push_cast; ring
    have h2 : (-(h * (((0 : ℤ) * (p * r) + s : ℤ)))) = -(h * (s : ℤ)) := by push_cast; ring
    rw [h1, h2, ee_add, hCsplit, ee_collapse hN hq]
  unfold betaCell
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  ring

/-- The `j = 0` cell coefficient in geometric-series form. -/
theorem betaCell_zero_eq (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (h : ℤ) :
    betaCell p q r 0 h
      = (1 / ((p * q * r : ℕ) : ℂ)) * ∑ s ∈ range (p * r), ee (p * q * r) (-(h * (s : ℤ))) := by
  unfold betaCell
  refine congrArg _ (Finset.sum_congr rfl fun s _ => ?_)
  congr 1
  push_cast
  ring

/-- **The permanent S1 closed form.**  For `h ≢ 0 (mod C)`,

    beta_j^circ(h) = e_q(-j h) · (1 - e_q(-h)) / (C · (1 - e_C(-h))). -/
theorem correctedS1_closed_form (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (j h : ℤ)
    (hh : ¬ ((p * q * r : ℕ) : ℤ) ∣ h) :
    betaCellCentred p q r j h
      = ee q (-(j * h)) * (1 - ee q (-h)) /
          (((p * q * r : ℕ) : ℂ) * (1 - ee (p * q * r) (-h))) := by
  have hN : p * r ≠ 0 := Nat.mul_ne_zero hp hr
  have hC : p * q * r ≠ 0 := by positivity
  have hCc : ((p * q * r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hC
  have hx : ee (p * q * r) (-h) ≠ 1 := by
    intro hc
    exact hh (dvd_neg.mp ((ee_eq_one_iff hC (-h)).1 hc))
  have hxne : (1 : ℂ) - ee (p * q * r) (-h) ≠ 0 := sub_ne_zero_of_ne (Ne.symm hx)
  have hgeom : ∑ s ∈ range (p * r), ee (p * q * r) (-(h * (s : ℤ)))
      = (1 - ee q (-h)) / (1 - ee (p * q * r) (-h)) := by
    have hterm : ∀ s ∈ range (p * r), ee (p * q * r) (-(h * (s : ℤ)))
        = (ee (p * q * r) (-h)) ^ s := by
      intro s _
      rw [show (-(h * (s : ℤ))) = (-h) * (s : ℤ) by ring, ee_pow]
    rw [Finset.sum_congr rfl hterm, geom_sum_eq hx]
    have hpow : (ee (p * q * r) (-h)) ^ (p * r) = ee q (-h) := by
      rw [← ee_pow (p * q * r) (-h) (p * r)]
      have hCsplit : p * q * r = (p * r) * q := by ring
      rw [hCsplit, ee_collapse hN hq]
    rw [hpow]
    have hx1 : ee (p * q * r) (-h) - 1 ≠ 0 := sub_ne_zero_of_ne hx
    rw [div_eq_div_iff hx1 hxne]
    ring
  unfold betaCellCentred
  rw [if_neg hh, quotientCell_phaseFactor p q r hp hq hr j h,
    betaCell_zero_eq p q r hp hq hr h, hgeom]
  field_simp

/-! ## 3. Finite Fourier inversion for the centred cell -/

/-- The indicator of the quotient cell `I_j = j N + [0,N)` modulo `C`. -/
noncomputable def cellIndicator (j sstar : ℤ) : ℂ :=
  ∑ s ∈ range (p * r),
    if ((p * q * r : ℕ) : ℤ) ∣ (sstar - (j * (p * r) + s)) then (1 : ℂ) else 0

/-- **Finite Fourier inversion, centred form.**

    1_{I_j}(s*) - 1/q = ∑_{h ≠ 0 mod C} beta_j^circ(h) · e_C(h s*).  -/
theorem correctedQuotient_fourier (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) (j sstar : ℤ) :
    ∑ h ∈ (range (p * q * r)).erase 0,
        betaCellCentred p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar)
      = cellIndicator p q r j sstar - (1 / (q : ℂ)) := by
  classical
  have hC : p * q * r ≠ 0 := by positivity
  have hN : p * r ≠ 0 := Nat.mul_ne_zero hp hr
  have hCc : ((p * q * r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hC
  have hqc : ((q : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hq
  -- the full sum over all frequencies reproduces the indicator
  have hfull : ∑ h ∈ range (p * q * r),
      betaCell p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar)
      = cellIndicator p q r j sstar := by
    have hterm : ∀ h ∈ range (p * q * r),
        betaCell p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar)
          = (1 / ((p * q * r : ℕ) : ℂ)) *
            ∑ s ∈ range (p * r),
              ee (p * q * r) ((h : ℤ) * (sstar - (j * (p * r) + s))) := by
      intro h _
      unfold betaCell
      rw [mul_assoc, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [← ee_add]
      congr 1
      ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
    unfold cellIndicator
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    have : ∑ h ∈ range (p * q * r), ee (p * q * r) ((h : ℤ) * (sstar - (j * (p * r) + s)))
        = if ((p * q * r : ℕ) : ℤ) ∣ (sstar - (j * (p * r) + s)) then ((p * q * r : ℕ) : ℂ)
          else 0 := sum_ee_range hC _
    rw [this]
    split_ifs
    · field_simp
    · simp
  -- the zero frequency contributes exactly 1/q
  have hpc : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp
  have hrc : ((r : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hr
  have hzero : betaCell p q r j 0 * ee (p * q * r) ((0 : ℤ) * sstar) = 1 / (q : ℂ) := by
    unfold betaCell
    have h1 : ∀ s ∈ range (p * r),
        ee (p * q * r) (-((0 : ℤ) * ((j * (p * r) + s : ℤ)))) = 1 := by
      intro s _; simp
    rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
      show ((0 : ℤ) * sstar) = 0 by ring, ee_zero, mul_one]
    push_cast
    field_simp
  have hsplit : ∑ h ∈ range (p * q * r),
      betaCell p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar)
      = betaCell p q r j 0 * ee (p * q * r) ((0 : ℤ) * sstar)
        + ∑ h ∈ (range (p * q * r)).erase 0,
            betaCell p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 (Nat.pos_of_ne_zero hC))]
    norm_num
  have hcentred : ∀ h ∈ (range (p * q * r)).erase 0,
      betaCellCentred p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar)
        = betaCell p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar) := by
    intro h hh
    have hh0 : h ≠ 0 := (Finset.mem_erase.1 hh).1
    have hlt : h < p * q * r := Finset.mem_range.1 (Finset.mem_erase.1 hh).2
    have hnd : ¬ ((p * q * r : ℕ) : ℤ) ∣ (h : ℤ) := by
      intro hdvd
      have : (p * q * r : ℕ) ∣ h := by exact_mod_cast hdvd
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hh0) this
      omega
    unfold betaCellCentred
    rw [if_neg hnd]
  rw [Finset.sum_congr rfl hcentred]
  rw [hfull, hzero] at hsplit
  rw [hsplit]
  ring

/-! ## 4. CRT splitting of the phase and the authoritative match -/

/-- **CRT phase splitting.**  If `q q̄ + N N̄ = 1 + N q t` then

    e_{N q}(x) = e_N(x q̄) · e_q(x N̄). -/
theorem correctedQuotient_crt_phase {N q : ℕ} (hN : N ≠ 0) (hq : q ≠ 0)
    {qbar Nbar t : ℤ} (hsplit : q * qbar + N * Nbar = 1 + (N * q : ℕ) * t) (x : ℤ) :
    ee (N * q) x = ee N (x * qbar) * ee q (x * Nbar) := by
  have h1 : ee N (x * qbar) = ee (N * q) (x * qbar * q) := ee_scale hN hq _
  have h2 : ee q (x * Nbar) = ee (N * q) (x * Nbar * N) := by
    rw [ee_collapse hN hq]
  rw [h1, h2, ← ee_add]
  refine (ee_congr (Nat.mul_ne_zero hN hq) ?_).symm
  have : x * qbar * q + x * Nbar * N - x = ((N * q : ℕ) : ℤ) * (x * t) := by
    have hs : (q : ℤ) * qbar + (N : ℤ) * Nbar = 1 + ((N * q : ℕ) : ℤ) * t := by exact_mod_cast hsplit
    push_cast at hs ⊢
    linear_combination (x : ℤ) * hs
  exact ⟨x * t, this⟩

/-- **Authoritative source match** (sign convention `c = -2`, i.e. both
congruences have right-hand side `2`).  With the Fourier kernel `e_C(-h s)`,

    e_C(-h s) = e_{p r}(-2 h q̄ m̄) · e_q(-2 h N̄ d̄),

which are exactly the authoritative arithmetic factors
`e_{p r}(-2 h · inverse(q m))` and `e_q(-2 h · inverse(p r d))`. -/
theorem correctedQuotient_authoritative_match {N q : ℕ} (hN : N ≠ 0) (hq : q ≠ 0)
    {qbar Nbar t m mbar d dbar s h : ℤ}
    (hsplit : q * qbar + N * Nbar = 1 + (N * q : ℕ) * t)
    (hm : (N : ℤ) ∣ (m * s - 2)) (hmbar : (N : ℤ) ∣ (m * mbar - 1))
    (hmcop : IsCoprime m (N : ℤ))
    (hd : (q : ℤ) ∣ (d * s - 2)) (hdbar : (q : ℤ) ∣ (d * dbar - 1))
    (hdcop : IsCoprime d (q : ℤ)) :
    ee (N * q) (-(h * s)) = ee N (-(2 * h * qbar * mbar)) * ee q (-(2 * h * Nbar * dbar)) := by
  have hsN : (N : ℤ) ∣ (s - 2 * mbar) := by
    have hkey : m * (s - 2 * mbar) = (m * s - 2) - 2 * (m * mbar - 1) := by ring
    have : (N : ℤ) ∣ m * (s - 2 * mbar) := by
      rw [hkey]; exact dvd_sub hm (Dvd.dvd.mul_left hmbar 2)
    exact (hmcop.symm).dvd_of_dvd_mul_left this
  have hsq : (q : ℤ) ∣ (s - 2 * dbar) := by
    have hkey : d * (s - 2 * dbar) = (d * s - 2) - 2 * (d * dbar - 1) := by ring
    have : (q : ℤ) ∣ d * (s - 2 * dbar) := by
      rw [hkey]; exact dvd_sub hd (Dvd.dvd.mul_left hdbar 2)
    exact (hdcop.symm).dvd_of_dvd_mul_left this
  rw [correctedQuotient_crt_phase hN hq hsplit (-(h * s))]
  congr 1
  · refine ee_congr hN ?_
    have : -(h * s) * qbar - -(2 * h * qbar * mbar) = (-(h * qbar)) * (s - 2 * mbar) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hsN _
  · refine ee_congr hq ?_
    have : -(h * s) * Nbar - -(2 * h * Nbar * dbar) = (-(h * Nbar)) * (s - 2 * dbar) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hsq _

/-- **Sign-convention record (`c = +2`).**  With `d s + 2 ≡ 0 (mod q)` the
`q`-factor is the authoritative one-sided phase `e_q(-2 h · inverse(p r d))`
*only after* the kernel `e_C(+h s)` is used, and then the `p r`-factor carries
the opposite sign `e_{p r}(+2 h · inverse(q m))`.  The global sign convention is
therefore pinned by the source, not free. -/
theorem correctedQuotient_match_c_two {N q : ℕ} (hN : N ≠ 0) (hq : q ≠ 0)
    {qbar Nbar t m mbar d dbar s h : ℤ}
    (hsplit : q * qbar + N * Nbar = 1 + (N * q : ℕ) * t)
    (hm : (N : ℤ) ∣ (m * s - 2)) (hmbar : (N : ℤ) ∣ (m * mbar - 1))
    (hmcop : IsCoprime m (N : ℤ))
    (hd : (q : ℤ) ∣ (d * s + 2)) (hdbar : (q : ℤ) ∣ (d * dbar - 1))
    (hdcop : IsCoprime d (q : ℤ)) :
    ee (N * q) (h * s) = ee N (2 * h * qbar * mbar) * ee q (-(2 * h * Nbar * dbar)) := by
  have hsN : (N : ℤ) ∣ (s - 2 * mbar) := by
    have hkey : m * (s - 2 * mbar) = (m * s - 2) - 2 * (m * mbar - 1) := by ring
    have : (N : ℤ) ∣ m * (s - 2 * mbar) := by
      rw [hkey]; exact dvd_sub hm (Dvd.dvd.mul_left hmbar 2)
    exact (hmcop.symm).dvd_of_dvd_mul_left this
  have hsq : (q : ℤ) ∣ (s + 2 * dbar) := by
    have hkey : d * (s + 2 * dbar) = (d * s + 2) + 2 * (d * dbar - 1) := by ring
    have : (q : ℤ) ∣ d * (s + 2 * dbar) := by
      rw [hkey]; exact dvd_add hd (Dvd.dvd.mul_left hdbar 2)
    exact (hdcop.symm).dvd_of_dvd_mul_left this
  rw [correctedQuotient_crt_phase hN hq hsplit (h * s)]
  congr 1
  · refine ee_congr hN ?_
    have : h * s * qbar - 2 * h * qbar * mbar = (h * qbar) * (s - 2 * mbar) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hsN _
  · refine ee_congr hq ?_
    have : h * s * Nbar - -(2 * h * Nbar * dbar) = (h * Nbar) * (s + 2 * dbar) := by ring
    rw [this]
    exact Dvd.dvd.mul_left hsq _

/-! ## 5. The quotient scale `U_q = q/H` -/

/-- The quotient scale. -/
noncomputable def Uq (q H : ℝ) : ℝ := q / H

/-- **Main normalisation.**  `U_q / q = 1/H`. -/
theorem Uq_div_q (q H : ℝ) (hq : q ≠ 0) (hH : H ≠ 0) : Uq q H / q = 1 / H := by
  unfold Uq; field_simp

/-- **FIREWALL.**  `U_q = q/H` is not the reciprocal `H/q` unless `q = H`
(for positive parameters). -/
theorem Uq_ne_reciprocal_of_ne {q H : ℝ} (hq : 0 < q) (hH : 0 < H) (hne : q ≠ H) :
    Uq q H ≠ H / q := by
  unfold Uq
  intro hc
  have h1 : q * q = H * H := by
    field_simp at hc
    linarith [hc]
  have h2 : (q - H) * (q + H) = 0 := by nlinarith [h1]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact hne (by linarith)
  · linarith

/-! ## 6. Amplitudes multiply the finite kernel identity -/

/-- **Abstract scalar amplitude.**  Multiplying the exact finite kernel by an
arbitrary scalar amplitude preserves the identity; no source amplitude is
invented. -/
theorem centeredQuotientKernel_withAmplitude (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (j sstar : ℤ) (amp : ℂ) :
    amp * ∑ h ∈ (range (p * q * r)).erase 0,
        betaCellCentred p q r j (h : ℤ) * ee (p * q * r) ((h : ℤ) * sstar)
      = amp * (cellIndicator p q r j sstar - 1 / (q : ℂ)) := by
  rw [correctedQuotient_fourier p q r hp hq hr j sstar]

end TwinPrimeProject.NANC.Gate1A.V92
