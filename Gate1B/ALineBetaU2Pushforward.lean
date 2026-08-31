import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.RatioDiagonalPhysicalisation

/-!
# Gate 1B · A-line, `(q,v)` pushforward and the dual operator interface

**Phase C of the C4Shift consolidation.**  Append-only.  Everything proved here
is exact finite algebra, exact combinatorics, finite Fourier inversion, or a
purely functional Cauchy–Schwarz inequality with all hypotheses printed.  **No
analytic estimate is proved and no analytic socket is inhabited.**

## Contents

1. `aline_exists_A0` / `aline_A0_unique` — the Bézout residue `A₀` of
   `u s A ≡ −2 (mod ℓ)`; `aline_y_param` and `aline_q_param` give
   `y_t = y₀ + u s t` and `q_{t,h} = y₀ + u(s t + h)`.
2. `ell_y_congr_two_mod_u`, `y_congr_reciprocal`, `yCanon`, `exists_nu` — the
   reciprocal residue `y ≡ 2 ℓ⁻¹ (mod u)` and the canonical representative.
3. `line_shift` — `q₂ − q₁ = u g` with `g = s r + Δ`.
4. `Gamma` — the exact finite Γ-source with all source fields retained.
5. `pushforward_dvd`, `pushforward_congr` — `u ∣ v` and `ℓ q ≡ 2 (mod u)`.
6. `ell_unique_in_window` — at most one physical `ℓ` per `(q, v, u)` when the
   window is not wider than `u`.
7. `fibre_card_le_divisors` — the fibre over `(q,v)` injects into the divisors
   of `v` inside the `u`-range: **divisor-type, not `U/R`-type**, multiplicity.
8. `Vsharp_pushforward` — the exact change-of-variables identity.
9. `fourier_inversion` — exact finite Fourier inversion for the β-autocorrelation
   pairing.
10. `dual_cauchy_interface` — the exact operator inequality; `BetaU2Input` is an
    **UNINHABITED** interface for the analytic β-`U²` bound.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace ALinePushforward

open Finset FiniteLiftLocalTwist

/-! ## 1. A-line Bézout parametrisation -/

/-- **Existence of the Bézout residue.**  If `u s` is invertible mod `ℓ`, then
`u s A₀ ≡ −2 (mod ℓ)` is solvable. -/
theorem aline_exists_A0 {ell : ℕ} {u s : ℤ} (hcop : IsCoprime (u * s) (ell : ℤ)) :
    ∃ A0 : ℤ, (ell : ℤ) ∣ (u * s * A0 + 2) := by
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨-2 * a, ⟨2 * b, ?_⟩⟩
  linear_combination -2 * hab

/-- **Uniqueness of the Bézout residue mod `ℓ`.** -/
theorem aline_A0_unique {ell : ℕ} {u s A A' : ℤ} (hcop : IsCoprime (u * s) (ell : ℤ))
    (h : (ell : ℤ) ∣ (u * s * A + 2)) (h' : (ell : ℤ) ∣ (u * s * A' + 2)) :
    (ell : ℤ) ∣ (A - A') := by
  obtain ⟨c, hc⟩ := h
  obtain ⟨c', hc'⟩ := h'
  have hmul : (ell : ℤ) ∣ (u * s) * (A - A') := ⟨c - c', by linear_combination hc - hc'⟩
  exact (hcop.symm).dvd_of_dvd_mul_left hmul

/-- **A-line `y`-parametrisation.**  With `A_t = A₀ + ℓ t` and `ℓ y₀ = u s A₀ + 2`,
the solution of `ℓ y_t = u s A_t + 2` is `y_t = y₀ + u s t`. -/
theorem aline_y_param {ell : ℕ} {u s A0 y0 t : ℤ} (hy0 : (ell : ℤ) * y0 = u * s * A0 + 2) :
    (ell : ℤ) * (y0 + u * s * t) = u * s * (A0 + (ell : ℤ) * t) + 2 := by
  linear_combination hy0

/-- **A-line `q`-parametrisation.**  From the determinant line
`ℓ(q − u h) − u A_t s = 2` one gets `q = y₀ + u(s t + h)`. -/
theorem aline_q_param {ell : ℕ} (hell : (ell : ℤ) ≠ 0) {u s A0 y0 t h q : ℤ}
    (hy0 : (ell : ℤ) * y0 = u * s * A0 + 2)
    (hq : (ell : ℤ) * (q - u * h) - u * (A0 + (ell : ℤ) * t) * s = 2) :
    q = y0 + u * (s * t + h) := by
  have hkey : (ell : ℤ) * (q - (y0 + u * (s * t + h))) = 0 := by
    linear_combination hq - hy0
  rcases mul_eq_zero.1 hkey with h0 | h0
  · exact absurd h0 hell
  · linarith [h0]

/-! ## 2. The reciprocal residue -/

/-- `ℓ y_t ≡ 2 (mod u)`. -/
theorem ell_y_congr_two_mod_u {ell : ℕ} {u s A y : ℤ}
    (hy : (ell : ℤ) * y = u * A * s + 2) : u ∣ ((ell : ℤ) * y - 2) :=
  ⟨A * s, by linear_combination hy⟩

/-- **Reciprocal residue.**  With `ℓ ℓ⁻¹ ≡ 1 (mod u)`, `y ≡ 2 ℓ⁻¹ (mod u)`. -/
theorem y_congr_reciprocal {ell : ℕ} {u y invell : ℤ}
    (hinv : u ∣ ((ell : ℤ) * invell - 1)) (hy : u ∣ ((ell : ℤ) * y - 2)) :
    u ∣ (y - 2 * invell) := by
  obtain ⟨c, hc⟩ := hinv
  obtain ⟨d, hd⟩ := hy
  exact ⟨invell * d - y * c, by linear_combination invell * hd - y * hc⟩

/-- The canonical reciprocal residue `y_{u,ℓ} = (2 ℓ⁻¹) mod u`. -/
def yCanon (u invell : ℤ) : ℤ := (2 * invell) % u

/-- `y_{u,ℓ}` is congruent to `2 ℓ⁻¹` modulo `u`. -/
theorem yCanon_congr (u invell : ℤ) : u ∣ (2 * invell - yCanon u invell) := by
  refine ⟨(2 * invell) / u, ?_⟩
  unfold yCanon
  have := Int.mul_ediv_add_emod (2 * invell) u
  linarith

/-- **Existence of `ν`.**  `y₀ = y_{u,ℓ} + u ν` for an integer `ν`. -/
theorem exists_nu {ell : ℕ} {u y0 invell : ℤ}
    (hinv : u ∣ ((ell : ℤ) * invell - 1)) (hy : u ∣ ((ell : ℤ) * y0 - 2)) :
    ∃ nu : ℤ, y0 = yCanon u invell + u * nu := by
  have h1 : u ∣ (y0 - 2 * invell) := y_congr_reciprocal hinv hy
  have h2 : u ∣ (2 * invell - yCanon u invell) := yCanon_congr u invell
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  exact ⟨a + b, by linear_combination ha + hb⟩

/-- **Canonical `q`-parametrisation.** -/
theorem q_param_canonical {u s t h y0 nu invell : ℤ}
    (hy0 : y0 = yCanon u invell + u * nu) :
    y0 + u * (s * t + h) = yCanon u invell + u * (nu + s * t + h) := by
  rw [hy0]; ring

/-! ## 3. Line shift algebra -/

/-- **Line shift.**  For two copies of the line, `q₂ − q₁ = u g` with
`g = s r + Δ`, `r = t₂ − t₁`, `Δ = h₂ − h₁`. -/
theorem line_shift {u s y0 t₁ t₂ h₁ h₂ : ℤ} :
    (y0 + u * (s * t₂ + h₂)) - (y0 + u * (s * t₁ + h₁))
      = u * (s * (t₂ - t₁) + (h₂ - h₁)) := by ring

/-! ## 4. The Γ source -/

/-- **The exact finite Γ-source.**  All source fields (`c4j` on both lines and
`kappa` on both shifts) are retained; the two defining equations
`w = ν + s t + h₁` and `g = s r + (h₂ − h₁)` are carried as explicit
conditions. -/
noncomputable def Gamma (T H : Finset ℤ) (c4j kappa : ℤ → ℂ) (nu s A0 : ℤ) (ell : ℕ)
    (g w : ℤ) : ℂ :=
  ∑ t ∈ T, ∑ r ∈ T, ∑ h₁ ∈ H, ∑ h₂ ∈ H,
    (if w = nu + s * t + h₁ ∧ g = s * r + (h₂ - h₁) then
        c4j (A0 + (ell : ℤ) * t) * (starRingEnd ℂ) (c4j (A0 + (ell : ℤ) * (t + r))) *
          kappa h₁ * (starRingEnd ℂ) (kappa h₂)
      else 0)

/-! ## 5. The `(q, v)` pushforward -/

/-- `q = y_{u,ℓ} + u w`. -/
def qOf (yc u w : ℤ) : ℤ := yc + u * w

/-- `v = u g`. -/
def vOf (u g : ℤ) : ℤ := u * g

/-- `u ∣ v`. -/
theorem pushforward_dvd (u g : ℤ) : u ∣ vOf u g := ⟨g, rfl⟩

/-- `ℓ q ≡ 2 (mod u)`. -/
theorem pushforward_congr {ell : ℕ} {yc u w : ℤ} (h : u ∣ ((ell : ℤ) * yc - 2)) :
    u ∣ ((ell : ℤ) * qOf yc u w - 2) := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c + (ell : ℤ) * w, by unfold qOf; linear_combination hc⟩

/-! ## 6. Uniqueness of the physical `ℓ` -/

/-- **At most one physical `ℓ` per `(q, v, u)`.**

The hypothesis `R ≤ u` is the explicit finite interval-width encoding of the
research condition `R < U`; the repository does *not* supply the endpoint
scales, so the width is a printed hypothesis. -/
theorem ell_unique_in_window {u q R₀ R e₁ e₂ : ℤ} (hcop : IsCoprime q u)
    (hwidth : R ≤ u)
    (h₁ : R₀ ≤ e₁ ∧ e₁ < R₀ + R) (h₂ : R₀ ≤ e₂ ∧ e₂ < R₀ + R)
    (c₁ : u ∣ (e₁ * q - 2)) (c₂ : u ∣ (e₂ * q - 2)) :
    e₁ = e₂ := by
  obtain ⟨a, ha⟩ := c₁
  obtain ⟨b, hb⟩ := c₂
  have hmul : u ∣ (e₁ - e₂) * q := ⟨a - b, by linear_combination ha - hb⟩
  have hd : u ∣ (e₁ - e₂) := (hcop.symm).dvd_of_dvd_mul_right hmul
  have habs : |e₁ - e₂| < u := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd habs
  omega

/-! ## 7. The preimage divisor statement -/

/-- **Fibre multiplicity is divisor-type.**

The fibre of `(q,v)` — recorded as a finite set `F` of pairs `(u, ℓ)` — injects
into the set of `u` in the physical range dividing `v`.  This is exact
combinatorics: the multiplicity is bounded by a divisor count, **not** by
`U/R`. -/
theorem fibre_card_le_divisors {q v : ℤ} (F : Finset (ℤ × ℤ)) (Urange : Finset ℤ)
    {R₀ R : ℤ}
    (hU : ∀ p ∈ F, p.1 ∈ Urange)
    (hdvd : ∀ p ∈ F, p.1 ∣ v)
    (hcop : ∀ p ∈ F, IsCoprime q p.1)
    (hwidth : ∀ p ∈ F, R ≤ p.1)
    (hwin : ∀ p ∈ F, R₀ ≤ p.2 ∧ p.2 < R₀ + R)
    (hcong : ∀ p ∈ F, p.1 ∣ (p.2 * q - 2)) :
    F.card ≤ (Urange.filter (fun u => u ∣ v)).card := by
  classical
  refine Finset.card_le_card_of_injOn (fun p => p.1) ?_ ?_
  · intro p hp
    exact Finset.mem_filter.2 ⟨hU p hp, hdvd p hp⟩
  · intro p hp p' hp' hfst
    have hfst' : p.1 = p'.1 := hfst
    have hp₀ : p ∈ F := hp
    have hp₀' : p' ∈ F := hp'
    have hell : p.2 = p'.2 := by
      refine ell_unique_in_window (u := p.1) (q := q) (R₀ := R₀) (R := R)
        (hcop p hp₀) (hwidth p hp₀) (hwin p hp₀) (hwin p' hp₀') (hcong p hp₀) ?_
      rw [hfst']
      exact hcong p' hp₀'
    exact Prod.ext hfst' hell

/-! ## 8. The pushed `H` coefficient and the change of variables -/

section Pushforward

variable {I : Type*}

/-- The pushed coefficient `H(q,v)`: the sum of the source coefficient over the
fibre of `(q,v)`. -/
noncomputable def Hcoef (S : Finset I) (push : I → ℤ × ℤ) (coef : I → ℂ)
    (qv : ℤ × ℤ) : ℂ :=
  ∑ i ∈ S.filter (fun i => push i = qv), coef i

/-- The source-side sum `V^♯`. -/
noncomputable def Vsharp (S : Finset I) (push : I → ℤ × ℤ) (coef : I → ℂ)
    (beta : ℤ → ℂ) : ℂ :=
  ∑ i ∈ S, coef i * beta (push i).1 * (starRingEnd ℂ) (beta ((push i).1 + (push i).2))

/-- **Exact change of variables.**  `V^♯ = ∑_{q,v} H(q,v) β(q) conj β(q+v)`.

The only hypothesis is that the pushforward map lands in the finite index set
`P`; there is no analytic content and no routed-tail term is silently
absorbed. -/
theorem Vsharp_pushforward (S : Finset I) (push : I → ℤ × ℤ) (coef : I → ℂ)
    (beta : ℤ → ℂ) (P : Finset (ℤ × ℤ)) (hmaps : ∀ i ∈ S, push i ∈ P) :
    Vsharp S push coef beta
      = ∑ qv ∈ P, Hcoef S push coef qv * beta qv.1 * (starRingEnd ℂ) (beta (qv.1 + qv.2)) := by
  classical
  unfold Vsharp Hcoef
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun i => coef i * beta (push i).1 * (starRingEnd ℂ) (beta ((push i).1 + (push i).2)))]
  refine Finset.sum_congr rfl fun qv _ => ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hpush : push i = qv := (Finset.mem_filter.1 hi).2
  rw [hpush]

end Pushforward

/-! ## 9. β-autocorrelation and finite Fourier inversion -/

/-- The β-autocorrelation Fourier object `C_v(θ)` at the discrete frequency
`θ = k/P`. -/
noncomputable def Cv (P : ℕ) (beta : ℤ → ℂ) (Qs : Finset ℤ) (v : ℤ) (k : ℕ) : ℂ :=
  ∑ q ∈ Qs, beta q * (starRingEnd ℂ) (beta (q + v)) * ezExp P (q * k)

/-- The Fourier transform `Ĥ(θ, v)` at the discrete frequency `θ = k/P`. -/
noncomputable def Hhat (P : ℕ) (H : ℤ × ℤ → ℂ) (Qs : Finset ℤ) (v : ℤ) (k : ℕ) : ℂ :=
  ∑ q ∈ Qs, H (q, v) * ezExp P (-(q * k))

/-- **Exact finite Fourier inversion.**

`∑_{k mod P} Ĥ(k/P, v) C_v(k/P) = P · ∑_q H(q,v) β(q) conj β(q+v)`,

under the explicit separation hypothesis that the `q`-support is injective
modulo `P` (the discrete-Haar substitute for the torus integral). -/
theorem fourier_inversion (P : ℕ) [NeZero P] (Qs : Finset ℤ) (H : ℤ × ℤ → ℂ)
    (beta : ℤ → ℂ) (v : ℤ)
    (hsep : ∀ q ∈ Qs, ∀ q' ∈ Qs, (P : ℤ) ∣ (q' - q) → q' = q) :
    ∑ k ∈ Finset.range P, Hhat P H Qs v k * Cv P beta Qs v k
      = (P : ℂ) * ∑ q ∈ Qs, H (q, v) * beta q * (starRingEnd ℂ) (beta (q + v)) := by
  classical
  have hexp : ∀ (q q' : ℤ) (k : ℕ),
      ezExp P (-(q * k)) * ezExp P (q' * k) = ezExp P ((k : ℤ) * (q' - q)) := by
    intro q q' k
    rw [← ezExp_add]
    congr 1
    ring
  have expand : ∀ k ∈ Finset.range P, Hhat P H Qs v k * Cv P beta Qs v k
      = ∑ q ∈ Qs, ∑ q' ∈ Qs,
          (H (q, v) * (beta q' * (starRingEnd ℂ) (beta (q' + v)))) *
            ezExp P ((k : ℤ) * (q' - q)) := by
    intro k _
    unfold Hhat Cv
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    rw [← hexp q q' k]; ring
  rw [Finset.sum_congr rfl expand, Finset.sum_comm]
  have hinner : ∀ q ∈ Qs,
      ∑ k ∈ Finset.range P, ∑ q' ∈ Qs,
          (H (q, v) * (beta q' * (starRingEnd ℂ) (beta (q' + v)))) *
            ezExp P ((k : ℤ) * (q' - q))
        = (P : ℂ) * (H (q, v) * beta q * (starRingEnd ℂ) (beta (q + v))) := by
    intro q hq
    rw [Finset.sum_comm]
    have hk : ∀ q' ∈ Qs,
        ∑ k ∈ Finset.range P,
            (H (q, v) * (beta q' * (starRingEnd ℂ) (beta (q' + v)))) *
              ezExp P ((k : ℤ) * (q' - q))
          = (H (q, v) * (beta q' * (starRingEnd ℂ) (beta (q' + v)))) *
              (if (P : ℤ) ∣ (q' - q) then (P : ℂ) else 0) := by
      intro q' _
      rw [← Finset.mul_sum, sum_range_ezExp P (q' - q)]
    rw [Finset.sum_congr rfl hk, Finset.sum_eq_single q]
    · simp
      ring
    · intro q' hq' hne
      have hnd : ¬ ((P : ℤ) ∣ (q' - q)) := fun hd => hne (hsep q hq q' hq' hd)
      rw [if_neg hnd, mul_zero]
    · intro hq0; exact absurd hq hq0
  rw [Finset.sum_congr rfl hinner, Finset.mul_sum]

/-! ## 10. The dual Cauchy interface -/

/-- **Exact dual Cauchy inequality.**  A purely functional inequality: no
analytic input is used, and none is produced. -/
theorem dual_cauchy_interface (P : ℕ) (Vset : Finset ℤ) (Hh Cc : ℕ → ℤ → ℂ) (B : ℝ)
    (hB : ∀ k ∈ Finset.range P, Real.sqrt (∑ v ∈ Vset, ‖Cc k v‖ ^ 2) ≤ B) :
    ‖∑ k ∈ Finset.range P, ∑ v ∈ Vset, Hh k v * Cc k v‖
      ≤ B * ∑ k ∈ Finset.range P, Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) := by
  classical
  have hk : ∀ k ∈ Finset.range P,
      ‖∑ v ∈ Vset, Hh k v * Cc k v‖ ≤ B * Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) := by
    intro k hkmem
    have h1 : ‖∑ v ∈ Vset, Hh k v * Cc k v‖ ≤ ∑ v ∈ Vset, ‖Hh k v‖ * ‖Cc k v‖ := by
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun v _ => le_of_eq (norm_mul _ _)
    have h2 : ∑ v ∈ Vset, ‖Hh k v‖ * ‖Cc k v‖
        ≤ Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) * Real.sqrt (∑ v ∈ Vset, ‖Cc k v‖ ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    have h3 : Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) * Real.sqrt (∑ v ∈ Vset, ‖Cc k v‖ ^ 2)
        ≤ Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) * B :=
      mul_le_mul_of_nonneg_left (hB k hkmem) (Real.sqrt_nonneg _)
    calc ‖∑ v ∈ Vset, Hh k v * Cc k v‖ ≤ ∑ v ∈ Vset, ‖Hh k v‖ * ‖Cc k v‖ := h1
      _ ≤ Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) * Real.sqrt (∑ v ∈ Vset, ‖Cc k v‖ ^ 2) := h2
      _ ≤ Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) * B := h3
      _ = B * Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) := by ring
  calc ‖∑ k ∈ Finset.range P, ∑ v ∈ Vset, Hh k v * Cc k v‖
      ≤ ∑ k ∈ Finset.range P, ‖∑ v ∈ Vset, Hh k v * Cc k v‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range P, B * Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) :=
        Finset.sum_le_sum hk
    _ = B * ∑ k ∈ Finset.range P, Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) := by
        rw [Finset.mul_sum]

/-- **UNINHABITED analytic interface.**  The β-`U²` bound is *not* available in
this repository; this structure states it and is never constructed. -/
structure BetaU2Input where
  /-- The frequency modulus of the discrete Haar formulation. -/
  P : ℕ
  /-- The shift support. -/
  Vset : Finset ℤ
  /-- The β-autocorrelation Fourier object. -/
  Cc : ℕ → ℤ → ℂ
  /-- The claimed natural bound. -/
  betaBound : ℝ
  /-- The analytic β-`U²` estimate itself (**not proved anywhere**). -/
  u2 : ∀ k ∈ Finset.range P, Real.sqrt (∑ v ∈ Vset, ‖Cc k v‖ ^ 2) ≤ betaBound

/-- **Conditional compiler.**  Given the (uninhabited) β-`U²` input, the dual
Cauchy interface is available with the stated bound.  This is an implication,
not a closure. -/
theorem dual_cauchy_of_betaU2 (J : BetaU2Input) (Hh : ℕ → ℤ → ℂ) :
    ‖∑ k ∈ Finset.range J.P, ∑ v ∈ J.Vset, Hh k v * J.Cc k v‖
      ≤ J.betaBound * ∑ k ∈ Finset.range J.P,
          Real.sqrt (∑ v ∈ J.Vset, ‖Hh k v‖ ^ 2) :=
  dual_cauchy_interface J.P J.Vset Hh J.Cc J.betaBound J.u2

/-! ## 11. Status metadata for this phase (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the A-line / `(q,v)` / dual operator bank. -/
def statusRows : List LedgerEntry :=
  [ ⟨"DETLINE-ALINE-BEZOUT45", Status.provedAlgebraic,
     "FORMALLY BANKED. aline_exists_A0, aline_A0_unique, aline_y_param, aline_q_param, ell_y_congr_two_mod_u, y_congr_reciprocal, yCanon, exists_nu, q_param_canonical, line_shift."⟩,
    ⟨"DETLINE-QV-PUSHFORWARD-DIVISOR-FIBRE45", Status.provedFinite,
     "FORMALLY BANKED. pushforward_dvd, pushforward_congr, ell_unique_in_window (explicit interval-width hypothesis R <= u), fibre_card_le_divisors: fixed (q,v) multiplicity is divisor-type, NOT U/R-type. The source-weighted second moment is NOT formalised."⟩,
    ⟨"DETLINE-QV-CHANGE-OF-VARIABLES45", Status.provedAlgebraic,
     "FORMALLY BANKED. Vsharp_pushforward is an exact fibrewise regrouping; routed-tail inputs are not absorbed."⟩,
    ⟨"BETAU2-RECIPROCAL-RESIDUE-RESTRICTION45", Status.supersededAsControllingFrontier,
     "STRICTLY REDUCED / NOT FALSE."⟩,
    ⟨"BETAU2-INPUT45", Status.analyticOpen,
     "UNINHABITED. BetaU2Input; dual_cauchy_of_betaU2 is a conditional compiler only."⟩,
    ⟨"ALINE-T-DIAGONAL45", Status.externallyAudited,
     "RESEARCH POWER CLOSED X^(-1/12+o(1)) (metadata only; not formalised)."⟩,
    ⟨"ALINE-SMALL-BETA-SHIFT45", Status.externallyAudited,
     "RESEARCH POWER CLOSED X^(-5/36+o(1)) (metadata only; not formalised)."⟩,
    ⟨"ALINE-SQRT-U-OVER-R-INCIDENCE-TAX45", Status.supersededAsControllingFrontier,
     "SUPERSEDED AS INTRINSIC OBSTRUCTION (research metadata); the exact divisor-type fibre bound fibre_card_le_divisors is what is formally banked."⟩ ]

/-- No row of this phase is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

end ALinePushforward
end CurrentProgramme
end TwinPrimeProject
