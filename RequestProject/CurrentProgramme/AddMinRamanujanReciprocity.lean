import Mathlib
import RequestProject.CurrentProgramme.AddMinSourceCoprimalityMuLog

/-!
# Gate 1B · Ramanujan sums, modular inverses and the reciprocal normal form

**Append-only delta layer.**  Everything proved in this module is exact finite
arithmetic: Ramanujan sums, a divisor identity, modular inverses, additive
character phase splitting, and the resulting reciprocal normal form for the
companion transform.  **No analytic estimate is proved anywhere.**

## Contents

1. `ramanujanC rRam B = ∑_{x mod rRam, gcd(x,rRam)=1} e_{rRam}(x B)` — the
   Ramanujan sum built from the repository's additive character `ezExp`.
2. `ramanujanC_hoelder` — the exact Hölder (divisor) form.
3. `ramanujan_divisor_sum` (with the two explicit branches
   `ramanujan_divisor_sum_of_dvd` / `_of_not_dvd`):
   `∑_{rRam ∣ N} c_{rRam}(B) = N · 1_{N ∣ B}`.  The indicator is *not* hidden
   inside a definition.
4. `exists_int_inverse`, `zmod_inv_mul_cancel`, `inv_quotient` — the modular
   inverse / quotient elimination: no ambiguous integer division survives.
5. `addMin_ramanujan_reciprocity` — the exact reciprocity theorem
   `1_{N∣B} e_{q_ℓ}(m B/N) = (1/N) e_{q_ℓ}(m N⁻¹ B) ∑_{rRam ∣ N} c_{rRam}(B)`.
6. `inv_reduction_qell_to_M`, `inv_unique_mod_M`, `phase_split_qell`,
   `reciprocal_phase_normalForm` — the `q_ℓ = ℓ M` phase splitting with the
   rigorous reduction of `N⁻¹ mod q_ℓ` to `N⁻¹ mod M`.
7. `roughTransform` and `addMin_companion_ramanujan_normalForm` — the literal
   finite source transform (keeping `μ(d)`, `log p`, `κ(h)`, `u`, `Θ`) and the
   companion normal-form compiler.
8. `old_representation_depends_on_quotient` — the quotient-removal firewall:
   the old rough coefficient really did depend on `[ℓ(dp−uh)−2]/(uA)`, and the
   new representation does not; the *new* coupling (moving divisor `rRam ∣ uA`,
   reciprocal `(uA)⁻¹` phase, same `Θ`) is recorded explicitly and not claimed
   to be absent.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AddMinRamanujan

open Finset ArithmeticFunction FiniteLiftLocalTwist DetLineCompanion

/-! ## 0. Character preliminaries -/

/-- `e_k(k j) = 1`. -/
theorem ezExp_modulus_mul (k : ℕ) (j : ℤ) : ezExp k ((k : ℤ) * j) = 1 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [ezExp]
  · have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
    rw [ezExp]
    have : (2 * (Real.pi : ℂ) * Complex.I * ((k : ℤ) * j : ℤ)) / (k : ℂ)
        = (j : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      push_cast
      field_simp
    rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- **Periodicity.**  `e_k` only depends on its argument modulo `k`. -/
theorem ezExp_congr (k : ℕ) {a b : ℤ} (h : (k : ℤ) ∣ (a - b)) :
    ezExp k a = ezExp k b := by
  obtain ⟨j, hj⟩ := h
  have ha : a = b + (k : ℤ) * j := by linarith [hj]
  rw [ha, ezExp_add, ezExp_modulus_mul, mul_one]

/-! ## 1. The Ramanujan sum -/

/-- **The Ramanujan sum** `c_{rRam}(B) = ∑_{x mod rRam, gcd(x,rRam)=1} e_{rRam}(x B)`.

The divisor variable is called `rRam` throughout, to avoid collision with the
programme's unrelated `r` variables. -/
noncomputable def ramanujanC (rRam : ℕ) (B : ℤ) : ℂ :=
  ∑ x ∈ (Finset.range rRam).filter (fun x => Nat.Coprime x rRam),
    ezExp rRam ((x : ℤ) * B)

@[simp] theorem ramanujanC_one (B : ℤ) : ramanujanC 1 B = 1 := by
  simp [ramanujanC, ezExp]

/-- **Hölder (divisor) form of the Ramanujan sum.**

`c_{rRam}(B) = ∑_{a b = rRam} μ(a) · b · 1_{b ∣ B}`.  Kernel-proved from the
Möbius coprimality identity and additive orthogonality. -/
theorem ramanujanC_hoelder (rRam : ℕ) (hr : 0 < rRam) (B : ℤ) :
    ramanujanC rRam B
      = ∑ ab ∈ rRam.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ) *
            (if (ab.2 : ℤ) ∣ B then (ab.2 : ℂ) else 0) := by
  classical
  have h0 : ramanujanC rRam B
      = ∑ x ∈ Finset.range rRam,
          (if Nat.Coprime x rRam then (1 : ℂ) else 0) * ezExp rRam ((x : ℤ) * B) := by
    rw [ramanujanC, Finset.sum_filter]
    exact Finset.sum_congr rfl fun x _ => by split <;> simp
  have h1 : ∀ x : ℕ, (if Nat.Coprime x rRam then (1 : ℂ) else 0)
      = ∑ a ∈ rRam.divisors, (if a ∣ x then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) := by
    intro x
    have hset : rRam.divisors.filter (fun a => a ∣ x) = (Nat.gcd x rRam).divisors := by
      ext a
      simp only [Finset.mem_filter, Nat.mem_divisors, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨har, _⟩, hax⟩
        exact ⟨⟨hax, har⟩, by simpa [Nat.gcd_eq_zero_iff] using fun _ h => absurd h hr.ne'⟩
      · rintro ⟨⟨hax, har⟩, _⟩
        exact ⟨⟨har, hr.ne'⟩, hax⟩
    rw [← Finset.sum_filter, hset]
    have hZ := moebius_divisor_sum (Nat.gcd x rRam)
    have hC : ∑ a ∈ (Nat.gcd x rRam).divisors, ((ArithmeticFunction.moebius a : ℤ) : ℂ)
        = (((if Nat.gcd x rRam = 1 then (1 : ℤ) else 0) : ℤ) : ℂ) := by
      rw [← hZ]; push_cast; ring
    rw [hC]
    unfold Nat.Coprime
    split <;> simp
  have h2 : ramanujanC rRam B
      = ∑ a ∈ rRam.divisors, ∑ x ∈ Finset.range rRam,
          (if a ∣ x then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) *
            ezExp rRam ((x : ℤ) * B) := by
    rw [h0, Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => by rw [h1 x, Finset.sum_mul]
  have hinner : ∀ a ∈ rRam.divisors,
      ∑ x ∈ Finset.range rRam,
          (if a ∣ x then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) *
            ezExp rRam ((x : ℤ) * B)
        = ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            (if ((rRam / a : ℕ) : ℤ) ∣ B then ((rRam / a : ℕ) : ℂ) else 0) := by
    intro a ha
    obtain ⟨hdvd, hne⟩ := Nat.mem_divisors.1 ha
    have ha0 : 0 < a := Nat.pos_of_dvd_of_pos hdvd hr
    set k : ℕ := rRam / a with hkdef
    have hk : a * k = rRam := Nat.mul_div_cancel' hdvd
    have hkpos : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h | h
      · rw [h, mul_zero] at hk; omega
      · exact h
    haveI : NeZero k := ⟨hkpos.ne'⟩
    have hstep : ∑ x ∈ Finset.range rRam,
        (if a ∣ x then ((ArithmeticFunction.moebius a : ℤ) : ℂ) else 0) *
          ezExp rRam ((x : ℤ) * B)
        = ((ArithmeticFunction.moebius a : ℤ) : ℂ) *
            ∑ x ∈ (Finset.range rRam).filter (fun x => a ∣ x), ezExp rRam ((x : ℤ) * B) := by
      rw [Finset.mul_sum, Finset.sum_filter]
      exact Finset.sum_congr rfl fun x _ => by split <;> simp
    have hbij : ∑ x ∈ (Finset.range rRam).filter (fun x => a ∣ x), ezExp rRam ((x : ℤ) * B)
        = ∑ y ∈ Finset.range k, ezExp k ((y : ℤ) * B) := by
      refine Finset.sum_nbij' (fun x => x / a) (fun y => a * y) ?_ ?_ ?_ ?_ ?_
      · intro x hx
        simp only [Finset.mem_filter, Finset.mem_range] at hx
        obtain ⟨y, rfl⟩ := hx.2
        have hdc : a * y / a = y := Nat.mul_div_cancel_left y ha0
        simp only [hdc]
        refine Finset.mem_range.2 ?_
        have hlt : a * y < a * k := by rw [hk]; exact hx.1
        exact lt_of_mul_lt_mul_left hlt (Nat.zero_le a)
      · intro y hy
        simp only [Finset.mem_range] at hy
        refine Finset.mem_filter.2 ⟨Finset.mem_range.2 ?_, ⟨y, rfl⟩⟩
        calc a * y < a * k := mul_lt_mul_of_pos_left hy ha0
        _ = rRam := hk
      · intro x hx
        simp only [Finset.mem_filter] at hx
        obtain ⟨y, rfl⟩ := hx.2
        have hdc : a * y / a = y := Nat.mul_div_cancel_left y ha0
        simp only [hdc]
      · intro y _
        have hdc : a * y / a = y := Nat.mul_div_cancel_left y ha0
        simp only [hdc]
      · intro x hx
        simp only [Finset.mem_filter] at hx
        obtain ⟨y, rfl⟩ := hx.2
        have hdc : a * y / a = y := Nat.mul_div_cancel_left y ha0
        simp only [hdc]
        rw [← hk]
        have hcast : ((a * y : ℕ) : ℤ) * B = (a : ℤ) * ((y : ℤ) * B) := by push_cast; ring
        rw [hcast, ezExp_scale_left a k _ ha0.ne']
    rw [hstep, hbij, sum_range_ezExp k B]
  rw [h2, Finset.sum_congr rfl hinner,
    Nat.sum_divisorsAntidiagonal
      (f := fun i j => ((ArithmeticFunction.moebius i : ℤ) : ℂ) *
        (if (j : ℤ) ∣ B then (j : ℂ) else 0))]

/-! ## 2. The exact Ramanujan divisor identity -/

/-- **`ADDMIN-RAMANUJAN-RECIPROCITY45`, divisor identity.**

`∑_{rRam ∣ N} c_{rRam}(B) = N · 1_{N ∣ B}`, with the indicator written out. -/
theorem ramanujan_divisor_sum (N : ℕ) (hN : 0 < N) (B : ℤ) :
    ∑ rRam ∈ N.divisors, ramanujanC rRam B = if (N : ℤ) ∣ B then (N : ℂ) else 0 := by
  classical
  have key := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun rRam => ramanujanC rRam B)
    (g := fun n => if (n : ℤ) ∣ B then (n : ℂ) else 0)).2
  refine key ?_ N hN
  intro n hn
  exact (ramanujanC_hoelder n hn B).symm

/-- The `N ∣ B` branch. -/
theorem ramanujan_divisor_sum_of_dvd {N : ℕ} (hN : 0 < N) {B : ℤ} (h : (N : ℤ) ∣ B) :
    ∑ rRam ∈ N.divisors, ramanujanC rRam B = (N : ℂ) := by
  rw [ramanujan_divisor_sum N hN B, if_pos h]

/-- The `N ∤ B` branch. -/
theorem ramanujan_divisor_sum_of_not_dvd {N : ℕ} (hN : 0 < N) {B : ℤ} (h : ¬ (N : ℤ) ∣ B) :
    ∑ rRam ∈ N.divisors, ramanujanC rRam B = 0 := by
  rw [ramanujan_divisor_sum N hN B, if_neg h]

/-- **Complete reassembly = the physical divisibility projector.**  Summing the
whole Ramanujan divisor family reconstructs exactly `1_{N ∣ B}` — no more, no
less. -/
theorem ramanujan_reassembly_is_divisibility_projector (N : ℕ) (hN : 0 < N) (B : ℤ) :
    ((N : ℂ))⁻¹ * ∑ rRam ∈ N.divisors, ramanujanC rRam B
      = (if (N : ℤ) ∣ B then (1 : ℂ) else 0) := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [ramanujan_divisor_sum N hN B]
  split_ifs
  · exact inv_mul_cancel₀ hNC
  · rw [mul_zero]

/-! ## 3. Modular inverses and quotient elimination -/

/-- An integer inverse of `N` modulo `q` exists as soon as `gcd(N, q) = 1`. -/
theorem exists_int_inverse (N q : ℕ) (h : Nat.Coprime N q) :
    ∃ invN : ℤ, (q : ℤ) ∣ ((N : ℤ) * invN - 1) := by
  refine ⟨Nat.gcdA N q, ?_⟩
  have hb := Nat.gcd_eq_gcd_ab N q
  rw [h] at hb
  refine ⟨-(Nat.gcdB N q), ?_⟩
  push_cast at hb ⊢
  linarith [hb]

/-- **Quotient elimination in `ZMod q`.**  If `gcd(N, q) = 1` then
`N⁻¹ · (N · t) = t` in `ZMod q`; no integer division occurs. -/
theorem zmod_inv_mul_cancel (q N : ℕ) [NeZero q] (h : Nat.Coprime N q) (t : ZMod q) :
    ((N : ZMod q))⁻¹ * ((N : ZMod q) * t) = t := by
  have hu : IsUnit ((N : ZMod q)) := (ZMod.isUnit_iff_coprime N q).2 h
  rw [← mul_assoc, ZMod.inv_mul_of_unit _ hu, one_mul]

/-- **Quotient elimination, integer form.**  If `N invN ≡ 1 (mod q)` and
`B = N t`, then `invN · B ≡ t (mod q)`. -/
theorem inv_quotient {N q : ℕ} {invN t : ℤ} (hinv : (q : ℤ) ∣ ((N : ℤ) * invN - 1)) :
    (q : ℤ) ∣ (invN * ((N : ℤ) * t) - t) := by
  obtain ⟨j, hj⟩ := hinv
  refine ⟨t * j, ?_⟩
  have : (N : ℤ) * invN = 1 + q * j := by linarith [hj]
  calc invN * ((N : ℤ) * t) - t = ((N : ℤ) * invN) * t - t := by ring
  _ = (1 + (q : ℤ) * j) * t - t := by rw [this]
  _ = (q : ℤ) * (t * j) := by ring

/-- **Transport to the additive character.**  `e_q(m · invN · (N t)) = e_q(m t)`. -/
theorem ezExp_inv_quotient {N q : ℕ} {invN t m : ℤ}
    (hinv : (q : ℤ) ∣ ((N : ℤ) * invN - 1)) :
    ezExp q (m * invN * ((N : ℤ) * t)) = ezExp q (m * t) := by
  refine ezExp_congr q ?_
  obtain ⟨j, hj⟩ := inv_quotient (N := N) (q := q) (invN := invN) (t := t) hinv
  refine ⟨m * j, ?_⟩
  have : m * invN * ((N : ℤ) * t) - m * t = m * (invN * ((N : ℤ) * t) - t) := by ring
  rw [this, hj]
  ring

/-! ## 4. The Ramanujan reciprocity theorem -/

/-- **`addMin_ramanujan_reciprocity`.**

```
1_{N ∣ B} · e_{q}(m · B/N)
    = (1/N) · e_{q}(m · N⁻¹ · B) · ∑_{rRam ∣ N} c_{rRam}(B).
```

Hypotheses printed explicitly: `0 < N` and `N · invN ≡ 1 (mod q)` (the latter is
supplied by `exists_int_inverse` from `gcd(N,q) = 1`).  No ambiguous integer
division survives: on the right-hand side the quotient `B/N` does not occur. -/
theorem addMin_ramanujan_reciprocity (N q : ℕ) (hN : 0 < N) (invN : ℤ)
    (hinv : (q : ℤ) ∣ ((N : ℤ) * invN - 1)) (m B : ℤ) :
    (if (N : ℤ) ∣ B then ezExp q (m * (B / N)) else 0)
      = ((N : ℂ))⁻¹ * ezExp q (m * invN * B) *
          ∑ rRam ∈ N.divisors, ramanujanC rRam B := by
  have hNC : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  by_cases hd : (N : ℤ) ∣ B
  · obtain ⟨t, rfl⟩ := hd
    rw [if_pos ⟨t, rfl⟩, ramanujan_divisor_sum_of_dvd hN ⟨t, rfl⟩]
    have hquot : (N : ℤ) * t / (N : ℤ) = t :=
      Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.2 hN.ne')
    rw [hquot, ezExp_inv_quotient (N := N) (q := q) hinv]
    field_simp
  · rw [if_neg hd, ramanujan_divisor_sum_of_not_dvd hN hd, mul_zero]

/-! ## 5. `q_ℓ = ℓ M`: inverse reduction and phase splitting -/

/-- **Inverse reduction `q_ℓ → M`.**  If `M ∣ q` then an inverse of `N` mod `q`
is an inverse of `N` mod `M`. -/
theorem inv_reduction_qell_to_M {M q : ℕ} (hMq : (M : ℤ) ∣ (q : ℤ)) {N invN : ℤ}
    (h : (q : ℤ) ∣ (N * invN - 1)) : (M : ℤ) ∣ (N * invN - 1) :=
  dvd_trans hMq h

/-- **Uniqueness of the inverse mod `M`.**  Any two inverses of `N` mod `M`
agree mod `M`; in particular the reduction of `invN_{q_ℓ}` *is* `invN_M`. -/
theorem inv_unique_mod_M {M : ℕ} {N invN invM : ℤ}
    (h1 : (M : ℤ) ∣ (N * invN - 1)) (h2 : (M : ℤ) ∣ (N * invM - 1)) :
    (M : ℤ) ∣ (invN - invM) := by
  have hx : invN - invM = (-invN) * (N * invM - 1) + invM * (N * invN - 1) := by ring
  rw [hx]
  exact dvd_add (Dvd.dvd.mul_left h2 _) (Dvd.dvd.mul_left h1 _)

/-- **Phase splitting on `q_ℓ = ℓ M`.**  With `B = ℓ T − 2`,

```
e_{ℓM}(m invN (ℓT − 2)) = e_{ℓM}(−2 m invN) · e_M(m invN T).
```
-/
theorem phase_split_qell (ell M : ℕ) (hell : ell ≠ 0) (m invN T : ℤ) :
    ezExp (ell * M) (m * invN * ((ell : ℤ) * T - 2))
      = ezExp (ell * M) (-2 * (m * invN)) * ezExp M (m * invN * T) := by
  have hsplit : m * invN * ((ell : ℤ) * T - 2)
      = -2 * (m * invN) + (ell : ℤ) * (m * invN * T) := by ring
  rw [hsplit, ezExp_add, ezExp_scale_left ell M _ hell]

/-- **The reduction is legitimate.**  Under `M ∣ invN − invM`, the `M`-phase may
be written with `invN_M`. -/
theorem ezExp_M_inv_reduction (M : ℕ) {invN invM m T : ℤ} (h : (M : ℤ) ∣ (invN - invM)) :
    ezExp M (m * invN * T) = ezExp M (m * invM * T) := by
  refine ezExp_congr M ?_
  obtain ⟨j, hj⟩ := h
  refine ⟨m * T * j, ?_⟩
  have : m * invN * T - m * invM * T = m * T * (invN - invM) := by ring
  rw [this, hj]; ring

/-- **Ramanujan-side splitting.**  `e_{rRam}(x(ℓT − 2)) = e_{rRam}(−2x)·e_{rRam}(x ℓ T)`. -/
theorem phase_split_rRam (rRam : ℕ) (x ell T : ℤ) :
    ezExp rRam (x * (ell * T - 2)) = ezExp rRam (-2 * x) * ezExp rRam (x * ell * T) := by
  have hsplit : x * (ell * T - 2) = -2 * x + x * ell * T := by ring
  rw [hsplit, ezExp_add]

/-! ## 6. The exact reciprocal normal form -/

/-- The constant `−2` phase: it carries the *fixed shift* `2`, never an average
over shifts. -/
noncomputable def constantPhase (qell rRam : ℕ) (mInvN x : ℤ) : ℂ :=
  ezExp qell (-2 * mInvN) * ezExp rRam (-2 * x)

/-- The effective rough phase `Θ = m invN_M / M + x ℓ / rRam`, evaluated at
`T = d p − u h`, realised as a product of additive characters (no real
representative is needed). -/
noncomputable def thetaPhase (M rRam : ℕ) (mInvM x ell T : ℤ) : ℂ :=
  ezExp M (mInvM * T) * ezExp rRam (x * ell * T)

/-- **The exact reciprocal phase identity.**

```
e_{q_ℓ}(m invN B_det) · e_{rRam}(x B_det)
  = constantPhase(−2) · phase_Θ(d p − u h),      B_det = ℓ(dp − uh) − 2,
```
with `Θ = m invN_M / M + x ℓ / rRam`.  All signs are checked by Lean. -/
theorem reciprocal_phase_normalForm (ell M rRam : ℕ) (hell : ell ≠ 0)
    (m invN invM x T : ℤ) (hred : (M : ℤ) ∣ (invN - invM)) :
    ezExp (ell * M) (m * invN * ((ell : ℤ) * T - 2)) * ezExp rRam (x * ((ell : ℤ) * T - 2))
      = constantPhase (ell * M) rRam (m * invN) x *
          thetaPhase M rRam (m * invM) x (ell : ℤ) T := by
  rw [phase_split_qell ell M hell m invN T, phase_split_rRam rRam x (ell : ℤ) T,
    ezExp_M_inv_reduction M hred]
  unfold constantPhase thetaPhase
  ring

/-! ## 7. The literal rough transform -/

/-- **The finite rough source.**  The arithmetic variables `d, p, h, u` are kept
separate, and the coefficient keeps its literal `μ(d) · log p · κ(h)` shape times
an abstract smooth weight. -/
structure RoughSource (ι : Type*) where
  /-- The finite tuple set. -/
  T : Finset ι
  /-- The Möbius variable `d`. -/
  dNat : ι → ℕ
  /-- The prime variable `p`. -/
  pNat : ι → ℕ
  /-- The shift variable `h`. -/
  hVar : ι → ℤ
  /-- The source variable `u` (kept separate, as in the source). -/
  u : ℤ
  /-- The shift weight `κ`. -/
  kappa : ℤ → ℂ
  /-- The remaining smooth weight `W(...)`. -/
  W : ι → ℂ
  /-- The determinant combination `T = d p − u h`. -/
  Tval : ι → ℤ
  /-- `T` really is `d p − u h`. -/
  Tval_eq : ∀ t ∈ T, Tval t = (dNat t : ℤ) * (pNat t : ℤ) - u * hVar t

variable {ι : Type*}

/-- **`roughTransform`** — the literal finite source transform

```
∑_{d,p,h} μ(d) log p κ(h) W(...) e(Θ (d p − u h)).
```
-/
noncomputable def roughTransform (R : RoughSource ι) (M rRam : ℕ) (mInvM x ell : ℤ) : ℂ :=
  ∑ t ∈ R.T, ((ArithmeticFunction.moebius (R.dNat t) : ℤ) : ℂ) *
    ((Real.log (R.pNat t) : ℝ) : ℂ) * R.kappa (R.hVar t) * R.W t *
      thetaPhase M rRam mInvM x ell (R.Tval t)

/-- The rough transform really is evaluated at the determinant combination
`d p − u h`; `u` is not absorbed. -/
theorem roughTransform_phase_law (R : RoughSource ι) (M rRam : ℕ) (mInvM x ell : ℤ) :
    roughTransform R M rRam mInvM x ell
      = ∑ t ∈ R.T, ((ArithmeticFunction.moebius (R.dNat t) : ℤ) : ℂ) *
          ((Real.log (R.pNat t) : ℝ) : ℂ) * R.kappa (R.hVar t) * R.W t *
            thetaPhase M rRam mInvM x ell
              ((R.dNat t : ℤ) * (R.pNat t : ℤ) - R.u * R.hVar t) := by
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [R.Tval_eq t ht]

/-! ## 8. The companion reciprocal normal-form compiler -/

/-- The set of units `x mod rRam`. -/
def unitsMod (rRam : ℕ) : Finset ℕ :=
  (Finset.range rRam).filter (fun x => Nat.Coprime x rRam)

/-- **Term-level reciprocity in expanded form.**  The quotient phase of one
companion term becomes a moving divisor sum `rRam ∣ N` together with a unit sum
`x mod rRam`. -/
theorem quotientPhase_to_reciprocal (N q : ℕ) (hN : 0 < N) (invN : ℤ)
    (hinv : (q : ℤ) ∣ ((N : ℤ) * invN - 1)) (m B : ℤ) :
    (if (N : ℤ) ∣ B then (1 : ℂ) else 0) * ezExp q (m * (B / N))
      = ((N : ℂ))⁻¹ * ∑ rRam ∈ N.divisors, ∑ x ∈ unitsMod rRam,
          ezExp q (m * invN * B) * ezExp rRam ((x : ℤ) * B) := by
  have hkey := addMin_ramanujan_reciprocity N q hN invN hinv m B
  have hL : (if (N : ℤ) ∣ B then (1 : ℂ) else 0) * ezExp q (m * (B / N))
      = (if (N : ℤ) ∣ B then ezExp q (m * (B / N)) else 0) := by
    split <;> simp
  rw [hL, hkey, mul_assoc, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun rRam _ => ?_
  unfold ramanujanC unitsMod
  rw [Finset.mul_sum]

/-- `N = u A` for a companion tuple, as a natural number. -/
structure CompanionModuli (ι : Type*) where
  /-- `n t = u_t A_t`. -/
  nNat : ι → ℕ
  /-- The integer inverse of `n t` modulo `q_ℓ`. -/
  invQ : ι → ℤ
  /-- The integer inverse of `n t` modulo `M`. -/
  invM : ι → ℤ

/-- **`addMin_companion_ramanujan_normalForm`.**

The companion transform, after Ramanujan reciprocity, is a sum over the tuples
`(u, A, d, p, h)`, the *moving* divisors `rRam ∣ uA` and the units `x mod rRam`,
of the reciprocal phase times the `Θ`-phase.  The quotient
`[ℓ(dp − uh) − 2]/(uA)` **does not occur** on the right-hand side.

All hypotheses are printed: positivity of `uA`, the inverse congruences mod
`q_ℓ = ℓM` and mod `M`, `ℓ ≠ 0`, and the physical support condition. -/
theorem addMin_companion_ramanujan_normalForm [DecidableEq ι] (K : CompanionSkeleton ι)
    (C : CompanionModuli ι) (ell M : ℕ) (S : Finset ℤ) (m : ℤ)
    (hell : ell ≠ 0)
    (hn : ∀ t ∈ K.T, ((C.nNat t : ℕ) : ℤ) = K.u t * K.A t)
    (hnpos : ∀ t ∈ K.T, 0 < C.nNat t)
    (hinv : ∀ t ∈ K.T, ((ell * M : ℕ) : ℤ) ∣ ((C.nNat t : ℤ) * C.invQ t - 1))
    (hinvM : ∀ t ∈ K.T, (M : ℤ) ∣ ((C.nNat t : ℤ) * C.invM t - 1))
    (hS : ∀ t ∈ K.T, (K.u t * K.A t) ∣ Nval K (ell : ℤ) t →
      Nval K (ell : ℤ) t / (K.u t * K.A t) ∈ S) :
    companionHat K (ell : ℤ) S (ell * M) m
      = ∑ t ∈ K.T, K.coeff t * ((C.nNat t : ℂ))⁻¹ *
          ∑ rRam ∈ (C.nNat t).divisors, ∑ x ∈ unitsMod rRam,
            constantPhase (ell * M) rRam (m * C.invQ t) (x : ℤ) *
              thetaPhase M rRam (m * C.invM t) (x : ℤ) (ell : ℤ)
                (K.d t * K.p t - K.u t * K.h t) := by
  classical
  have hua : ∀ t ∈ K.T, K.u t * K.A t ≠ 0 := by
    intro t ht
    rw [← hn t ht]
    exact_mod_cast (hnpos t ht).ne'
  rw [companionHat_normal_form K (ell : ℤ) S (ell * M) m hua hS]
  refine Finset.sum_congr rfl fun t ht => ?_
  set n : ℕ := C.nNat t with hndef
  have hnZ : (n : ℤ) = K.u t * K.A t := hn t ht
  have hnpos' : 0 < n := hnpos t ht
  set B : ℤ := Nval K (ell : ℤ) t with hB
  have hterm := quotientPhase_to_reciprocal n (ell * M) hnpos' (C.invQ t) (hinv t ht) m B
  rw [← hnZ]
  have hrewrite : K.coeff t * (if (n : ℤ) ∣ B then (1 : ℂ) else 0) *
      ezExp (ell * M) (m * (B / (n : ℤ)))
      = K.coeff t * ((if (n : ℤ) ∣ B then (1 : ℂ) else 0) *
          ezExp (ell * M) (m * (B / (n : ℤ)))) := by ring
  rw [hrewrite, hterm]
  have hBform : B = (ell : ℤ) * (K.d t * K.p t - K.u t * K.h t) - 2 := rfl
  have hred : (M : ℤ) ∣ (C.invQ t - C.invM t) := by
    refine inv_unique_mod_M (N := (n : ℤ)) ?_ (hinvM t ht)
    refine inv_reduction_qell_to_M ?_ (hinv t ht)
    exact ⟨(ell : ℤ), by push_cast; ring⟩
  have hsum : ∀ rRam ∈ n.divisors,
      ∑ x ∈ unitsMod rRam, ezExp (ell * M) (m * C.invQ t * B) * ezExp rRam ((x : ℤ) * B)
        = ∑ x ∈ unitsMod rRam,
            constantPhase (ell * M) rRam (m * C.invQ t) (x : ℤ) *
              thetaPhase M rRam (m * C.invM t) (x : ℤ) (ell : ℤ)
                (K.d t * K.p t - K.u t * K.h t) := by
    intro rRam _
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hBform]
    exact reciprocal_phase_normalForm ell M rRam hell m (C.invQ t) (C.invM t) (x : ℤ)
      (K.d t * K.p t - K.u t * K.h t) hred
  rw [Finset.sum_congr rfl hsum]
  ring

/-! ## 9. The quotient-removal firewall -/

/-- **The old representation genuinely depended on the quotient.**

`e_q(m · B/N)` is not independent of `N`: for `q = 2`, `B = 2`, `m = 1`, one has
`N = 1 ↦ 1` and `N = 2 ↦ −1`.  This is what the reciprocal normal form removes
from the rough coefficient. -/
theorem old_representation_depends_on_quotient :
    ezExp 2 ((1 : ℤ) * ((2 : ℤ) / (1 : ℤ))) ≠ ezExp 2 ((1 : ℤ) * ((2 : ℤ) / (2 : ℤ))) := by
  have h1 : ezExp 2 ((1 : ℤ) * ((2 : ℤ) / (1 : ℤ))) = 1 := by
    have : ezExp 2 (2 : ℤ) = 1 := by
      have := ezExp_modulus_mul 2 1
      simpa using this
    simpa using this
  have h2 : ezExp 2 ((1 : ℤ) * ((2 : ℤ) / (2 : ℤ))) = -1 := by
    have harg : (2 : ℂ) * (Real.pi : ℂ) * Complex.I * ((1 : ℤ) : ℂ) / ((2 : ℕ) : ℂ)
        = (Real.pi : ℂ) * Complex.I := by
      push_cast
      ring
    have : ezExp 2 (1 : ℤ) = -1 := by
      rw [ezExp, harg, Complex.exp_pi_mul_I]
    simpa using this
  rw [h1, h2]
  norm_num

/-- **The new representation is quotient-free.**  Every summand of the
reciprocal normal form is the value of the fixed function

```
(qell, M, rRam, mInvN, x, mInvM, ell, T) ↦ constantPhase · thetaPhase,
```

which takes no quotient argument: the source dependence has moved to the moving
divisor `rRam ∣ uA`, the reciprocal `(uA)⁻¹` phase and the shared `Θ`. -/
theorem reciprocal_summand_is_quotient_free (qell M rRam : ℕ) (mInvN x mInvM ell T : ℤ) :
    constantPhase qell rRam mInvN x * thetaPhase M rRam mInvM x ell T
      = (fun (data : ℕ × ℕ × ℕ × ℤ × ℤ × ℤ × ℤ × ℤ) =>
            constantPhase data.1 data.2.2.1 data.2.2.2.1 data.2.2.2.2.1 *
              thetaPhase data.2.1 data.2.2.1 data.2.2.2.2.2.1 data.2.2.2.2.1
                data.2.2.2.2.2.2.1 data.2.2.2.2.2.2.2)
          (qell, M, rRam, mInvN, x, mInvM, ell, T) := rfl

/-- **The new coupling, recorded honestly.**  The reciprocal form still couples
the source to the modulus in three ways, and this is *not* claimed to be removed:
the divisor `rRam` moves with `uA`, the phase carries `(uA)⁻¹ mod q_ℓ` (reduced
to `mod M`), and the rough transform is evaluated at the same `Θ`. -/
theorem new_coupling_is_present (R : RoughSource ι) (M rRam : ℕ) (mInvM x ell : ℤ) :
    roughTransform R M rRam mInvM x ell
      = ∑ t ∈ R.T, ((ArithmeticFunction.moebius (R.dNat t) : ℤ) : ℂ) *
          ((Real.log (R.pNat t) : ℝ) : ℂ) * R.kappa (R.hVar t) * R.W t *
            thetaPhase M rRam mInvM x ell (R.Tval t) := rfl

end AddMinRamanujan
end CurrentProgramme
end TwinPrimeProject
