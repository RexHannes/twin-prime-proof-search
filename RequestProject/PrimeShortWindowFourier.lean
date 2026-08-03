import RequestProject.KloostermanOrthogonality

/-!
# Prime short-window Fourier identity and normalized trace form (§3, §4, §5)

* §5 `finite_fourier_inversion`, `short_window_fourier_normalization`
  (`LEAN_PROVED`): the discrete Fourier normalization
  `∑_m W(m)|F_p(m)|² = p⁻¹ ∑_ℓ Ŵ(ℓ) C_p(ℓ)`.

* §4 `kl2`, `kloosterman_reindex`, `kloosterman_symm`,
  `kloosterman_eq_sqrt_mul_kl2` (`LEAN_PROVED`): the normalized Kloosterman
  trace function `Kl₂(z;p) = p^{-1/2} ∑_{x≠0} e_p(x + z x⁻¹)` and the conversion
  `S(a,b;p) = p^{1/2} Kl₂(ab;p)` for nonzero `a`.

* §3 `twisted_orthogonality`, `prime_short_window_fourier_identity`: the nonzero
  Fourier-mode identity `PRIME_SHORT_WINDOW_FOURIER_IDENTITY`.

* §5 conditional interface `ArbitraryLambdaFromFourier`
  (`CONDITIONAL_INTERFACE`).
-/

open Complex

namespace PrimeShortWindow

variable (p : ℕ) [Fact p.Prime]

/-! ## §5 Finite Fourier inversion and short-window normalization -/

/-- Discrete Fourier inversion over `Fₚ`: for arbitrary `W, G : Fₚ → ℂ`,
`∑_m W(m) G(m) = p⁻¹ ∑_ℓ (∑_n W(n) e_p(−ℓn)) (∑_m G(m) e_p(ℓm))`. -/
theorem finite_fourier_inversion (W G : ZMod p → ℂ) :
    ∑ m : ZMod p, W m * G m
      = (p : ℂ)⁻¹ * ∑ l : ZMod p,
          (∑ n : ZMod p, W n * ep p (-(l * n))) * (∑ m : ZMod p, G m * ep p (l * m)) := by
  have hp : (p : ℂ) ≠ 0 := by
    have h := (Fact.out : p.Prime).pos; exact_mod_cast h.ne'
  have hlorth : ∀ n m : ZMod p,
      (∑ l : ZMod p, ep p (-(l * n)) * ep p (l * m)) = if m = n then (p : ℂ) else 0 := by
    intro n m
    have h1 : (∑ l : ZMod p, ep p (-(l * n)) * ep p (l * m))
        = ∑ l : ZMod p, ep p ((m - n) * l) := by
      refine Finset.sum_congr rfl fun l _ => by rw [← ep_add]; congr 1; ring
    rw [h1, ep_orthogonality]; simp only [sub_eq_zero]
  have key : (∑ l : ZMod p,
      (∑ n : ZMod p, W n * ep p (-(l * n))) * (∑ m : ZMod p, G m * ep p (l * m)))
        = (p : ℂ) * ∑ m : ZMod p, W m * G m := by
    simp only [Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun n _ => Finset.sum_comm)]
    have hstep : ∀ n m : ZMod p,
        (∑ l : ZMod p, (W n * ep p (-(l * n))) * (G m * ep p (l * m)))
          = W n * G m * (if m = n then (p : ℂ) else 0) := by
      intro n m
      rw [← hlorth n m, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [Finset.sum_congr rfl (fun n _ => Finset.sum_congr rfl (fun m _ => hstep n m))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_eq_single n]
    · rw [if_pos rfl]; ring
    · intro m _ hmn; rw [if_neg hmn]; ring
    · intro h; exact absurd (Finset.mem_univ n) h
  rw [key, ← mul_assoc, inv_mul_cancel₀ hp, one_mul]

/-- `C_p(ℓ) = ∑_m |F_p(m)|² e_p(ℓ m)`, the Fourier transform of the short-window
energy density. -/
noncomputable def Cp (u : (ZMod p)ˣ) (s : Finset (ZMod p)ˣ) (lam : (ZMod p)ˣ → ℂ)
    (l : ZMod p) : ℂ :=
  ∑ m : ZMod p, (Fsum p u s lam m * (starRingEnd ℂ) (Fsum p u s lam m)) * ep p (l * m)

/-- **Short-window Fourier normalization** (§5): for any periodized weight `W`,
`∑_m W(m) |F_p(m)|² = p⁻¹ ∑_ℓ Ŵ(ℓ) C_p(ℓ)` with `Ŵ(ℓ) = ∑_n W(n) e_p(−ℓ n)`. -/
theorem short_window_fourier_normalization (W : ZMod p → ℂ) (u : (ZMod p)ˣ)
    (s : Finset (ZMod p)ˣ) (lam : (ZMod p)ˣ → ℂ) :
    ∑ m : ZMod p, W m * (Fsum p u s lam m * (starRingEnd ℂ) (Fsum p u s lam m))
      = (p : ℂ)⁻¹ * ∑ l : ZMod p,
          (∑ n : ZMod p, W n * ep p (-(l * n))) * Cp p u s lam l :=
  finite_fourier_inversion p W (fun m => Fsum p u s lam m * (starRingEnd ℂ) (Fsum p u s lam m))

/-! ## §4 Normalized Kloosterman trace function -/

/-- The normalized Kloosterman trace function
`Kl₂(z;p) = p^{-1/2} ∑_{x≠0} e_p(x + z x⁻¹)`. -/
noncomputable def kl2 (z : ZMod p) : ℂ := (Real.sqrt p : ℂ)⁻¹ * kloosterman p 1 z

/-- Reindexing `x ↦ a⁻¹ x`: for `a ≠ 0`, `S(a,b;p) = S(1, ab; p)`. -/
theorem kloosterman_reindex (a b : ZMod p) (ha : a ≠ 0) :
    kloosterman p a b = kloosterman p 1 (a * b) := by
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.mulLeft (Units.mk0 a ha))
      (fun y : (ZMod p)ˣ => ep p ((1 : ZMod p) * (y : ZMod p) + (a * b) * ((y : ZMod p))⁻¹))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  congr 1
  have hax : ((Equiv.mulLeft (Units.mk0 a ha) x : (ZMod p)ˣ) : ZMod p) = a * (x : ZMod p) := by
    simp [Equiv.mulLeft, Units.val_mul]
  rw [hax, mul_inv]; field_simp

/-- Kloosterman symmetry `S(a,b;p) = S(b,a;p)` (reindex `x ↦ x⁻¹`). -/
theorem kloosterman_symm (a b : ZMod p) : kloosterman p a b = kloosterman p b a := by
  unfold kloosterman
  rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
      (fun x : (ZMod p)ˣ => ep p (b * (x : ZMod p) + a * ((x : ZMod p))⁻¹))]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val, inv_inv]
  congr 1; ring

/-- **Normalized trace conversion** (§4): for `a ≠ 0`,
`S(a,b;p) = p^{1/2} Kl₂(ab;p)`. -/
theorem kloosterman_eq_sqrt_mul_kl2 (a b : ZMod p) (ha : a ≠ 0) :
    kloosterman p a b = (Real.sqrt p : ℂ) * kl2 p (a * b) := by
  have hsp : (Real.sqrt p : ℂ) ≠ 0 := by
    have hpp := (Fact.out : p.Prime).pos
    have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast hpp)
    exact_mod_cast this.ne'
  rw [kl2, ← mul_assoc, mul_inv_cancel₀ hsp, one_mul, kloosterman_reindex p a b ha]

/-! ## §3 Nonzero Fourier-mode identity -/

/-- Reduction step (`LEAN_PROVED`): complete-period orthogonality in `m` turns
the twisted sum into a constrained double sum over the units, with constraint
`x⁻¹ − y⁻¹ + ℓ = 0`. -/
theorem twisted_reduction (a b l : ZMod p) :
    (∑ m : ZMod p, kloosterman p a m * (starRingEnd ℂ) (kloosterman p b m) * ep p (l * m))
      = (p : ℂ) * ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
          (if (x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l = 0 then
            ep p (a * (x : ZMod p) - b * (y : ZMod p)) else 0) := by
  have hstep : ∀ m : ZMod p,
      kloosterman p a m * (starRingEnd ℂ) (kloosterman p b m) * ep p (l * m)
        = ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
            ep p (a * (x : ZMod p) - b * (y : ZMod p))
              * ep p (m * ((x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l)) := by
    intro m
    unfold kloosterman
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [ep_conj]; simp only [← ep_add]; congr 1; ring
  rw [Finset.sum_congr rfl (fun m _ => hstep m)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [← Finset.mul_sum]
  have hm : (∑ m : ZMod p, ep p (m * ((x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l)))
      = if (x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l = 0 then (p : ℂ) else 0 := by
    rw [← ep_orthogonality p ((x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l)]
    exact Finset.sum_congr rfl (fun m _ => by rw [mul_comm])
  rw [hm]
  by_cases hc : (x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l = 0
  · rw [if_pos hc, if_pos hc]; ring
  · rw [if_neg hc, if_neg hc]; ring

/-- Reformulation of the RHS by splitting the Kloosterman sum at `t = 1`
(the `t = 1` term cancels the `+1`, banking the `−1` as the excluded
contribution): `e_p(−(a+b)ℓ⁻¹)·S(aℓ⁻¹,bℓ⁻¹) − 1 = ∑_{t≠1} e_p(aℓ⁻¹ t + bℓ⁻¹ t⁻¹ − (a+b)ℓ⁻¹)`. -/
theorem twisted_RHS_reform (a b l : ZMod p) :
    ep p (-((a + b) * l⁻¹)) * kloosterman p (a * l⁻¹) (b * l⁻¹) - 1
      = ∑ t ∈ (Finset.univ.erase (1 : (ZMod p)ˣ)),
          ep p (a * l⁻¹ * (t : ZMod p) + b * l⁻¹ * (t : ZMod p)⁻¹ - (a + b) * l⁻¹) := by
  unfold kloosterman
  rw [Finset.mul_sum, ← Finset.add_sum_erase _ _ (Finset.mem_univ (1 : (ZMod p)ˣ))]
  have h1 : ep p (-((a + b) * l⁻¹)) *
      ep p (a * l⁻¹ * ((1 : (ZMod p)ˣ) : ZMod p) + b * l⁻¹ * ((1 : (ZMod p)ˣ) : ZMod p)⁻¹) = 1 := by
    simp only [Units.val_one, inv_one, mul_one]
    rw [← ep_add, show -((a + b) * l⁻¹) + (a * l⁻¹ + b * l⁻¹) = 0 by ring, ep_zero]
  rw [h1, add_sub_cancel_left]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [← ep_add]; congr 1; ring

/-- The exact finite-field value identity along the substitution `t = 1 + ℓ X`. -/
theorem twisted_value_id (a b l X : ZMod p) (hX : X ≠ 0) (hl : l ≠ 0) (ht : (1 + l * X) ≠ 0) :
    a * X - b * (X⁻¹ + l)⁻¹
      = a * l⁻¹ * (1 + l * X) + b * l⁻¹ * (1 + l * X)⁻¹ - (a + b) * l⁻¹ := by
  have ht' : (1 + X * l) ≠ 0 := by rwa [mul_comm] at ht
  have hXl : X⁻¹ + l = (1 + l * X) / X := by field_simp
  rw [hXl, inv_div]; field_simp; ring

/-- Collapse of the inner `y`-sum: for each `x`, the constraint fixes
`y⁻¹ = x⁻¹ + ℓ`, giving a single surviving term unless `x⁻¹ + ℓ = 0`. -/
theorem twisted_ycollapse (a b l : ZMod p) (x : (ZMod p)ˣ) :
    (∑ y : (ZMod p)ˣ, (if (x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l = 0 then
        ep p (a * (x : ZMod p) - b * (y : ZMod p)) else 0))
      = (if (x : ZMod p)⁻¹ + l = 0 then 0
          else ep p (a * (x : ZMod p) - b * ((x : ZMod p)⁻¹ + l)⁻¹)) := by
  by_cases hc : (x : ZMod p)⁻¹ + l = 0
  · rw [if_pos hc]
    refine Finset.sum_eq_zero (fun y _ => ?_)
    rw [if_neg]
    intro h
    have : (y : ZMod p)⁻¹ = (x : ZMod p)⁻¹ + l := by linear_combination -h
    rw [hc] at this
    exact (inv_ne_zero (Units.ne_zero y)) this
  · rw [if_neg hc, Finset.sum_eq_single (Units.mk0 ((x : ZMod p)⁻¹ + l)⁻¹ (inv_ne_zero hc))]
    · rw [if_pos (by rw [Units.val_mk0, inv_inv]; ring)]; simp only [Units.val_mk0]
    · intro y _ hy
      rw [if_neg]
      intro h
      apply hy
      have hyinv : (y : ZMod p)⁻¹ = (x : ZMod p)⁻¹ + l := by linear_combination -h
      exact Units.ext (by rw [Units.val_mk0, ← hyinv, inv_inv])
    · intro hmem; exact absurd (Finset.mem_univ _) hmem

/-- The fractional-linear bijection `x ↦ t = 1 + ℓ x` between
`Fₚˣ ∖ {x : x⁻¹ = −ℓ}` and `Fₚˣ ∖ {1}`, matching the two sums termwise. -/
theorem twisted_bij_sum (a b l : ZMod p) (hl : l ≠ 0) :
    (∑ x : (ZMod p)ˣ, (if (x : ZMod p)⁻¹ + l = 0 then (0 : ℂ)
        else ep p (a * (x : ZMod p) - b * ((x : ZMod p)⁻¹ + l)⁻¹)))
      = ∑ t ∈ (Finset.univ.erase (1 : (ZMod p)ˣ)),
          ep p (a * l⁻¹ * (t : ZMod p) + b * l⁻¹ * (t : ZMod p)⁻¹ - (a + b) * l⁻¹) := by
  have hlinv : l⁻¹ ≠ 0 := inv_ne_zero hl
  set x₀ : (ZMod p)ˣ := Units.mk0 (-l⁻¹) (neg_ne_zero.mpr hlinv) with hx₀
  have hx0coe : (x₀ : ZMod p) = -l⁻¹ := by rw [hx₀, Units.val_mk0]
  have key1 : ∀ x : (ZMod p)ˣ, x ≠ x₀ → 1 + l * (x : ZMod p) ≠ 0 := by
    intro x hx h; apply hx; apply Units.ext; rw [hx0coe]
    have hlx : l * (x : ZMod p) = -1 := by linear_combination h
    field_simp; linear_combination hlx
  have key3 : ∀ x : (ZMod p)ˣ, x ≠ x₀ → (x : ZMod p)⁻¹ + l ≠ 0 := by
    intro x hx h; apply hx; apply Units.ext; rw [hx0coe]
    have hxi : (x : ZMod p)⁻¹ = -l := by linear_combination h
    rw [← inv_inv (x : ZMod p), hxi, inv_neg]
  have hFx0 : (if (x₀ : ZMod p)⁻¹ + l = 0 then (0 : ℂ)
      else ep p (a * (x₀ : ZMod p) - b * ((x₀ : ZMod p)⁻¹ + l)⁻¹)) = 0 := by
    rw [if_pos]; rw [hx0coe, inv_neg, inv_inv]; ring
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ x₀), hFx0, zero_add]
  refine Finset.sum_bij'
    (fun (x : (ZMod p)ˣ) (hx : x ∈ Finset.univ.erase x₀) =>
      Units.mk0 (1 + l * (x : ZMod p)) (key1 x (Finset.mem_erase.mp hx).1))
    (fun (t : (ZMod p)ˣ) (ht : t ∈ Finset.univ.erase (1 : (ZMod p)ˣ)) =>
      Units.mk0 (((t : ZMod p) - 1) * l⁻¹) (by
        have htne : (t : ZMod p) ≠ 1 := fun hh => (Finset.mem_erase.mp ht).1 (Units.ext hh)
        exact mul_ne_zero (sub_ne_zero.mpr htne) hlinv))
    ?_ ?_ ?_ ?_ ?_
  · intro x hx
    rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have hh : (1 : ZMod p) + l * (x : ZMod p) = 1 := by
      have := congrArg (Units.val) h; simpa using this
    have hlx0 : l * (x : ZMod p) = 0 := by linear_combination hh
    rcases mul_eq_zero.mp hlx0 with h1 | h2
    · exact hl h1
    · exact (Units.ne_zero x) h2
  · intro t ht
    rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ _⟩
    intro h
    have hval : ((t : ZMod p) - 1) * l⁻¹ = -l⁻¹ := by
      have := congrArg (Units.val) h; rw [Units.val_mk0, hx0coe] at this; exact this
    have hsub : (t : ZMod p) - 1 = -1 := by field_simp at hval; linear_combination hval
    exact (Units.ne_zero t) (by linear_combination hsub)
  · intro x hx
    apply Units.ext; rw [Units.val_mk0, Units.val_mk0]; field_simp; ring
  · intro t ht
    apply Units.ext; rw [Units.val_mk0, Units.val_mk0]; field_simp; ring
  · intro x hx
    have hxne : x ≠ x₀ := (Finset.mem_erase.mp hx).1
    rw [if_neg (key3 x hxne), Units.val_mk0]
    congr 1
    exact twisted_value_id p a b l (x : ZMod p) (Units.ne_zero x) hl (key1 x hxne)

/-- Fractional-linear bijection step (§3 crux).  For `ℓ ≠ 0`, the constrained
double sum equals `e_p(−(a+b)ℓ⁻¹)·S(a ℓ⁻¹, b ℓ⁻¹) − 1`.

The pairs `(x,y)` with `x⁻¹ − y⁻¹ + ℓ = 0` are parametrized bijectively by
`t ∈ Fₚˣ ∖ {1}` via `x = (t−1)/ℓ`, `y = (t−1)/(tℓ)`; the excluded value
`t = 1` produces the `−1`. -/
theorem twisted_bijection (a b l : ZMod p) (hl : l ≠ 0) :
    (∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
        (if (x : ZMod p)⁻¹ - (y : ZMod p)⁻¹ + l = 0 then
          ep p (a * (x : ZMod p) - b * (y : ZMod p)) else 0))
      = ep p (-((a + b) * l⁻¹)) * kloosterman p (a * l⁻¹) (b * l⁻¹) - 1 := by
  rw [twisted_RHS_reform p a b l,
    Finset.sum_congr rfl (fun x _ => twisted_ycollapse p a b l x)]
  exact twisted_bij_sum p a b l hl

/-- **Twisted complete-period orthogonality** (§3 crux).  For `ℓ ≠ 0`,
`∑_m S(a,m) conj S(b,m) e_p(ℓ m) = p·(e_p(−(a+b)ℓ⁻¹)·S(a ℓ⁻¹, b ℓ⁻¹) − 1)`.

The `−1` term is the excluded `t = 1` contribution of the substitution
`t = 1 + ℓ x` (equivalently `t = w/(w−ℓ)`), which ranges bijectively over
`Fₚˣ ∖ {1}`. -/
theorem twisted_orthogonality (a b l : ZMod p) (hl : l ≠ 0) :
    ∑ m : ZMod p, kloosterman p a m * (starRingEnd ℂ) (kloosterman p b m) * ep p (l * m)
      = (p : ℂ) * (ep p (-((a + b) * l⁻¹)) * kloosterman p (a * l⁻¹) (b * l⁻¹) - 1) := by
  rw [twisted_reduction p a b l, twisted_bijection p a b l hl]

/-- **PRIME_SHORT_WINDOW_FOURIER_IDENTITY** (§3).  For `ℓ ≠ 0` and `κ = u ℓ⁻¹`,
`C_p(ℓ) = p ∑_{q,q'} λ_q conj λ_{q'} [ e_p(−κ(q⁻¹+q'⁻¹)) S(κ q'⁻¹, κ q⁻¹) − 1 ]`. -/
theorem prime_short_window_fourier_identity (u : (ZMod p)ˣ) (s : Finset (ZMod p)ˣ)
    (lam : (ZMod p)ˣ → ℂ) (l : ZMod p) (hl : l ≠ 0) :
    Cp p u s lam l
      = (p : ℂ) * ∑ q ∈ s, ∑ q' ∈ s, (lam q * (starRingEnd ℂ) (lam q')) *
          (ep p (-(((u : ZMod p) * l⁻¹) * ((q : ZMod p)⁻¹ + (q' : ZMod p)⁻¹)))
            * kloosterman p (((u : ZMod p) * l⁻¹) * (q' : ZMod p)⁻¹)
                (((u : ZMod p) * l⁻¹) * (q : ZMod p)⁻¹) - 1) := by
  unfold Cp
  have hpt : ∀ m : ZMod p,
      (Fsum p u s lam m * (starRingEnd ℂ) (Fsum p u s lam m)) * ep p (l * m)
        = ∑ q ∈ s, ∑ q' ∈ s, (lam q * (starRingEnd ℂ) (lam q')) *
            (kloosterman p ((u*q⁻¹ : (ZMod p)ˣ) : ZMod p) m
              * (starRingEnd ℂ) (kloosterman p ((u*q'⁻¹ : (ZMod p)ˣ) : ZMod p) m)
              * ep p (l * m)) := by
    intro m
    unfold Fsum
    rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun q' _ => ?_
    rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun m _ => hpt m)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun q _ => Finset.sum_comm]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q' hq' => ?_
  rw [← Finset.mul_sum, twisted_orthogonality p _ _ l hl]
  have hcoe_q : ((u*q⁻¹ : (ZMod p)ˣ) : ZMod p) = (u:ZMod p) * (q:ZMod p)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  have hcoe_q' : ((u*q'⁻¹ : (ZMod p)ˣ) : ZMod p) = (u:ZMod p) * (q':ZMod p)⁻¹ := by
    rw [Units.val_mul, Units.val_inv_eq_inv_val]
  rw [hcoe_q, hcoe_q']
  rw [kloosterman_symm p (((u:ZMod p) * (q:ZMod p)⁻¹) * l⁻¹) (((u:ZMod p) * (q':ZMod p)⁻¹) * l⁻¹)]
  ring_nf

/-! ## §5 Conditional interface -/

/-- **ARBITRARY_LAMBDA_FROM_FOURIER** (§5, `CONDITIONAL_INTERFACE`).  Records the
implication: if the nonzero Fourier modes `C_p(ℓ)` over the effective support
`0 < |ℓ| ≪ Q p^ε` are controlled by `p^{2+ε} ‖λ‖₂²`, then the arbitrary-vector
short-window bound holds.  The `≪`/`p^ε` inputs are analytic and recorded as
abstract hypotheses (`fourierControl → shortWindowBound`). -/
structure ArbitraryLambdaFromFourier where
  /-- Hypothesis: nonzero Fourier modes are controlled on the effective support. -/
  fourierControl : Prop
  /-- Conclusion: the arbitrary-vector short-window bound. -/
  shortWindowBound : Prop
  /-- The recorded conditional implication. -/
  implication : fourierControl → shortWindowBound

end PrimeShortWindow
