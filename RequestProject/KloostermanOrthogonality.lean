import RequestProject.FiniteFieldKloosterman

/-!
# Complete-period Kloosterman orthogonality and the Q-shear energy identity

`KLOOSTERMAN_COMPLETE_ORTHOGONALITY` (§2):
`∑_{m ∈ Fₚ} S(a,m;p) · conj S(b,m;p) = p (p·1_{a=b} − 1)`.

`Q_SHEAR_COMPLETE_PERIOD_ENERGY` (§2):
`∑_{m ∈ Fₚ} |F_p(m)|² = p ( p·‖λ‖₂² − |∑_q λ_q|² )`.

Status: `LEAN_PROVED`.
-/

open Complex

namespace PrimeShortWindow

variable (p : ℕ) [Fact p.Prime]

/-- **KLOOSTERMAN_COMPLETE_ORTHOGONALITY.**  For all `a b : ZMod p`,
`∑_m S(a,m) conj S(b,m) = p (p·1_{a=b} − 1)`. -/
theorem kloosterman_complete_orthogonality (a b : ZMod p) :
    ∑ m : ZMod p, kloosterman p a m * (starRingEnd ℂ) (kloosterman p b m)
      = (p : ℂ) * ((p : ℂ) * (if a = b then 1 else 0) - 1) := by
  -- Expand `S(a,m) · conj S(b,m)` as a double sum over the units `x, y`.
  have hstep : ∀ m : ZMod p,
      kloosterman p a m * (starRingEnd ℂ) (kloosterman p b m)
        = ∑ x : (ZMod p)ˣ, ∑ y : (ZMod p)ˣ,
            ep p (a * (x:ZMod p) - b * (y:ZMod p))
              * ep p (m * ((x:ZMod p)⁻¹ - (y:ZMod p)⁻¹)) := by
    intro m
    unfold kloosterman
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => ?_))
    rw [ep_conj]; simp only [← ep_add]; congr 1; ring
  rw [Finset.sum_congr rfl (fun m _ => hstep m)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_comm)]
  -- Sum the innermost `∑_m e_p(m(x⁻¹-y⁻¹))` by complete-period orthogonality.
  have hinner : ∀ x y : (ZMod p)ˣ,
      (∑ m : ZMod p, ep p (a*(x:ZMod p) - b*(y:ZMod p))
          * ep p (m * ((x:ZMod p)⁻¹ - (y:ZMod p)⁻¹)))
        = ep p (a*(x:ZMod p) - b*(y:ZMod p)) *
            (if (x:ZMod p)⁻¹ - (y:ZMod p)⁻¹ = 0 then (p:ℂ) else 0) := by
    intro x y
    rw [← Finset.mul_sum]
    congr 1
    rw [← ep_orthogonality p ((x:ZMod p)⁻¹ - (y:ZMod p)⁻¹)]
    exact Finset.sum_congr rfl (fun m _ => by rw [mul_comm])
  rw [Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => hinner x y))]
  -- The diagonal `x⁻¹ = y⁻¹` picks out `y = x`; collapse the `y`-sum.
  have hcond : ∀ x y : (ZMod p)ˣ,
      ((x:ZMod p)⁻¹ - (y:ZMod p)⁻¹ = 0) ↔ (y = x) := by
    intro x y
    rw [sub_eq_zero, inv_inj]
    exact ⟨fun h => Units.ext h.symm, fun h => by rw [h]⟩
  have hcollapse : ∀ x : (ZMod p)ˣ,
      (∑ y : (ZMod p)ˣ, ep p (a*(x:ZMod p) - b*(y:ZMod p)) *
          (if (x:ZMod p)⁻¹ - (y:ZMod p)⁻¹ = 0 then (p:ℂ) else 0))
        = ep p ((a - b)*(x:ZMod p)) * (p:ℂ) := by
    intro x
    rw [Finset.sum_congr rfl (fun y _ => by
      rw [if_congr (hcond x y) rfl rfl, mul_ite, mul_zero])]
    rw [Finset.sum_ite_eq' Finset.univ x
        (fun y => ep p (a*(x:ZMod p) - b*(y:ZMod p)) * (p:ℂ))]
    simp only [Finset.mem_univ, if_true]
    congr 2; ring
  rw [Finset.sum_congr rfl (fun x _ => hcollapse x)]
  rw [← Finset.sum_mul]
  rw [show (∑ x : (ZMod p)ˣ, ep p ((a-b)*(x:ZMod p)))
        = (if a - b = 0 then (p:ℂ) else 0) - 1 from units_char_sum p (a-b)]
  by_cases hab : a = b
  · rw [if_pos (by rw [hab, sub_self]), if_pos hab]; ring
  · rw [if_neg (by rwa [sub_eq_zero]), if_neg hab]; ring

/-- **Q_SHEAR_COMPLETE_PERIOD_ENERGY.**  The complete-period energy of the
short-window test vector `F_p`:
`∑_m F_p(m) conj F_p(m) = p ( p ∑_q λ_q conj λ_q − (∑_q λ_q) conj(∑_q λ_q) )`. -/
theorem q_shear_complete_period_energy (u : (ZMod p)ˣ) (s : Finset (ZMod p)ˣ)
    (lam : (ZMod p)ˣ → ℂ) :
    ∑ m : ZMod p, Fsum p u s lam m * (starRingEnd ℂ) (Fsum p u s lam m)
      = (p : ℂ) * ((p : ℂ) * (∑ q ∈ s, lam q * (starRingEnd ℂ) (lam q))
          - (∑ q ∈ s, lam q) * (starRingEnd ℂ) (∑ q ∈ s, lam q)) := by
  -- Expand `|F_p(m)|²` as a double sum of Kloosterman products.
  have hpt : ∀ m : ZMod p, Fsum p u s lam m * (starRingEnd ℂ) (Fsum p u s lam m)
      = ∑ q ∈ s, ∑ q' ∈ s, (lam q * (starRingEnd ℂ) (lam q')) *
          (kloosterman p ((u*q⁻¹ : (ZMod p)ˣ) : ZMod p) m
            * (starRingEnd ℂ) (kloosterman p ((u*q'⁻¹ : (ZMod p)ˣ) : ZMod p) m)) := by
    intro m
    unfold Fsum
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => ?_
    rw [map_mul]; ring
  rw [Finset.sum_congr rfl (fun m _ => hpt m)]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun q _ => Finset.sum_comm]
  -- `u q⁻¹ = u q'⁻¹` (as residues) iff `q = q'` (group cancellation + coe injective).
  have hcond : ∀ q q' : (ZMod p)ˣ,
      ((((u*q⁻¹ : (ZMod p)ˣ)) : ZMod p) = (((u*q'⁻¹ : (ZMod p)ˣ)) : ZMod p)) ↔ q = q' := by
    intro q q'
    rw [Units.val_inj]
    exact ⟨fun h => inv_injective (mul_left_cancel h), fun h => by rw [h]⟩
  -- Apply complete-period orthogonality to each `(q, q')` pair.
  have horth : ∀ q q' : (ZMod p)ˣ,
      (∑ m : ZMod p, (lam q * (starRingEnd ℂ) (lam q')) *
          (kloosterman p ((u*q⁻¹ : (ZMod p)ˣ) : ZMod p) m
            * (starRingEnd ℂ) (kloosterman p ((u*q'⁻¹ : (ZMod p)ˣ) : ZMod p) m)))
        = (lam q * (starRingEnd ℂ) (lam q')) *
            ((p:ℂ) * ((p:ℂ) * (if q = q' then 1 else 0) - 1)) := by
    intro q q'
    rw [← Finset.mul_sum, kloosterman_complete_orthogonality]
    rw [if_congr (hcond q q') rfl rfl]
  rw [Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => horth q q']
  -- Final algebra: collapse the diagonal and factor.
  have hS1 : ∀ q ∈ s,
      (∑ q' ∈ s, (lam q * (starRingEnd ℂ) (lam q')) * (if q = q' then (1:ℂ) else 0))
        = lam q * (starRingEnd ℂ) (lam q) := by
    intro q hq
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq s q (fun q' => lam q * (starRingEnd ℂ) (lam q')), if_pos hq]
  have hS1sum : (∑ q ∈ s, lam q * (starRingEnd ℂ) (lam q))
      = ∑ q ∈ s, ∑ q' ∈ s, (lam q * (starRingEnd ℂ) (lam q')) * (if q = q' then (1:ℂ) else 0) :=
    (Finset.sum_congr rfl hS1).symm
  rw [map_sum, Finset.sum_mul_sum, hS1sum]
  rw [Finset.sum_congr rfl (fun q _ => Finset.sum_congr rfl (fun q' _ =>
    show (lam q * (starRingEnd ℂ) (lam q')) * ((p:ℂ) * ((p:ℂ) * (if q = q' then (1:ℂ) else 0) - 1))
      = (p:ℂ)*(p:ℂ)*((lam q * (starRingEnd ℂ) (lam q')) * (if q = q' then (1:ℂ) else 0))
        - (p:ℂ)*(lam q * (starRingEnd ℂ) (lam q')) from by ring))]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end PrimeShortWindow
