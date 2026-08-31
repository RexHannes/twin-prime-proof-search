import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.C4ShiftNormPromotionRepair

/-!
# Gate 1B · C4Shift leafwise major / one-minor frontier (append-only)

Exact algebra, finite Fourier and source-DAG update only.  **No new analytic
number theory is proved.**

## Contents

* **§B** canonical major data `ω = a/q + β`, `gcd(a,q) = 1`, `q ≤ Q₀`, with
  *deterministic ownership*: Farey separation forces the approximating fraction
  to be unique (`major_arc_ownership_unique`).
* **§C** Gauss / character diagonalisation of `e_q(−a X Z)` over the Dirichlet
  characters mod `q`, with the correct conjugations
  (`major_char_diagonal`).  No primitive-character assumption.
* **§D** exact unit / non-unit reduction of `e_q(−a X Z)` to the reduced
  modulus, and the finite `gcd` partition.
* **§E** the multiplicative (Dirichlet) factorisation `χ(x₁x₂x₃x₄) = ∏ χ(xᵢ)`;
  the *false* additive-Fourier factorisation is **not** revived.
* **§F** leafwise source classification with a deterministic first defect index
  `i₀ = j+1` (built on the already-banked `c4leaf` lemmas).
* **§H** the one-minor projector `P₁ₘ = 1 − M₄(ω₁)M₄(ω₂)` and the exact
  tuple-level splitting of `Γ♯` into its one-minor and double-major parts.
* **§I** the `(h,K)` AP-index normal form on the odd clean `ℓ`-sector, and the
  *unrestricted* orthogonality consequences.  The restricted one-minor sums are
  **not** claimed to collapse.
* **§K** `C4ShiftOneMinorPushedEnergyInput` — **UNINHABITED** analytic socket.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace C4ShiftLeafwise

open Finset FiniteLiftLocalTwist C4ShiftQFourier C4ShiftAPFourier

/-! ## §B.  Canonical major data and deterministic ownership -/

/-- **Farey separation.**  Two distinct fractions with denominators `q₁,q₂` are
at distance at least `1/(q₁q₂)`. -/
theorem farey_separation (a1 a2 : ℤ) (q1 q2 : ℕ) (h1 : 0 < q1) (h2 : 0 < q2)
    (hne : a1 * (q2 : ℤ) ≠ a2 * (q1 : ℤ)) :
    1 / ((q1 : ℝ) * (q2 : ℝ)) ≤ |(a1 : ℝ) / (q1 : ℝ) - (a2 : ℝ) / (q2 : ℝ)| := by
  have hq1 : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast h1
  have hq2 : (0 : ℝ) < (q2 : ℝ) := by exact_mod_cast h2
  have hZ : (1 : ℤ) ≤ |a1 * (q2 : ℤ) - a2 * (q1 : ℤ)| := by
    rcases eq_or_ne (a1 * (q2 : ℤ) - a2 * (q1 : ℤ)) 0 with h | h
    · exact absurd (by linarith [sub_eq_zero.mp h] : a1 * (q2 : ℤ) = a2 * (q1 : ℤ)) hne
    · exact Int.one_le_abs (by simpa using h)
  have hR : (1 : ℝ) ≤ |(a1 : ℝ) * (q2 : ℝ) - (a2 : ℝ) * (q1 : ℝ)| := by
    have : ((|a1 * (q2 : ℤ) - a2 * (q1 : ℤ)| : ℤ) : ℝ)
        = |(a1 : ℝ) * (q2 : ℝ) - (a2 : ℝ) * (q1 : ℝ)| := by push_cast; ring_nf
    rw [← this]
    exact_mod_cast hZ
  have hkey : |(a1 : ℝ) / (q1 : ℝ) - (a2 : ℝ) / (q2 : ℝ)|
      = |(a1 : ℝ) * (q2 : ℝ) - (a2 : ℝ) * (q1 : ℝ)| / ((q1 : ℝ) * (q2 : ℝ)) := by
    rw [div_sub_div _ _ (ne_of_gt hq1) (ne_of_gt hq2), abs_div,
      abs_of_pos (by positivity : (0 : ℝ) < (q1 : ℝ) * (q2 : ℝ))]
    congr 2
    ring
  rw [hkey, div_le_div_iff_of_pos_right (by positivity)]
  exact hR

/-- **Deterministic ownership of overlapping major arcs.**  If `ω` is within
`1/(2Q₀²)` of two reduced fractions with denominators at most `Q₀`, the two
fractions coincide.  Hence arc ownership is a *function* of `ω`, not a choice. -/
theorem major_arc_ownership_unique (om : ℝ) (a1 a2 : ℤ) (q1 q2 Q0 : ℕ)
    (h1 : 0 < q1) (h2 : 0 < q2) (hq1 : q1 ≤ Q0) (hq2 : q2 ≤ Q0) (hQ0 : 0 < Q0)
    (hd1 : |om - (a1 : ℝ) / (q1 : ℝ)| < 1 / (2 * (Q0 : ℝ) ^ 2))
    (hd2 : |om - (a2 : ℝ) / (q2 : ℝ)| < 1 / (2 * (Q0 : ℝ) ^ 2)) :
    a1 * (q2 : ℤ) = a2 * (q1 : ℤ) := by
  by_contra hne
  have hsep := farey_separation a1 a2 q1 q2 h1 h2 hne
  have hQ0R : (0 : ℝ) < (Q0 : ℝ) := by exact_mod_cast hQ0
  have hq1R : (0 : ℝ) < (q1 : ℝ) := by exact_mod_cast h1
  have hq2R : (0 : ℝ) < (q2 : ℝ) := by exact_mod_cast h2
  have hq1' : (q1 : ℝ) ≤ (Q0 : ℝ) := by exact_mod_cast hq1
  have hq2' : (q2 : ℝ) ≤ (Q0 : ℝ) := by exact_mod_cast hq2
  have hprod : (q1 : ℝ) * (q2 : ℝ) ≤ (Q0 : ℝ) ^ 2 := by nlinarith
  have hlow : 1 / ((Q0 : ℝ) ^ 2) ≤ 1 / ((q1 : ℝ) * (q2 : ℝ)) := by
    apply one_div_le_one_div_of_le (by positivity) hprod
  have htri : |(a1 : ℝ) / (q1 : ℝ) - (a2 : ℝ) / (q2 : ℝ)|
      ≤ |om - (a1 : ℝ) / (q1 : ℝ)| + |om - (a2 : ℝ) / (q2 : ℝ)| := by
    have := abs_sub_abs_le_abs_sub ((a1 : ℝ) / (q1 : ℝ) - om) (om - (a2 : ℝ) / (q2 : ℝ))
    calc |(a1 : ℝ) / (q1 : ℝ) - (a2 : ℝ) / (q2 : ℝ)|
        = |((a1 : ℝ) / (q1 : ℝ) - om) + (om - (a2 : ℝ) / (q2 : ℝ))| := by ring_nf
      _ ≤ |(a1 : ℝ) / (q1 : ℝ) - om| + |om - (a2 : ℝ) / (q2 : ℝ)| := abs_add_le _ _
      _ = |om - (a1 : ℝ) / (q1 : ℝ)| + |om - (a2 : ℝ) / (q2 : ℝ)| := by rw [abs_sub_comm]
  have hsum : |om - (a1 : ℝ) / (q1 : ℝ)| + |om - (a2 : ℝ) / (q2 : ℝ)|
      < 1 / ((Q0 : ℝ) ^ 2) := by
    have : (1 : ℝ) / (2 * (Q0 : ℝ) ^ 2) + 1 / (2 * (Q0 : ℝ) ^ 2) = 1 / ((Q0 : ℝ) ^ 2) := by
      field_simp
      ring
    linarith
  linarith

/-! ## §C.  Gauss / character diagonalisation -/

section Char

variable (q : ℕ) [NeZero q]

/-- The Gauss-type sum `G_{q,a}(χ) = ∑_{x mod q}^* e_q(−a x) conj χ(x)`. -/
noncomputable def gaussSumChar (a : ℤ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ x : (ZMod q)ˣ,
    ezExp q (-(a * (((x : ZMod q).val : ℤ)))) * (starRingEnd ℂ) (χ ((x : ZMod q)))

omit [NeZero q] in
/-- On units, complex conjugation of a Dirichlet character value is evaluation
at the inverse. -/
theorem conj_char_apply (χ : DirichletCharacter ℂ q) (x : (ZMod q)ˣ) :
    (starRingEnd ℂ) (χ ((x : ZMod q))) = χ (((x : ZMod q))⁻¹) := by
  have h1 : χ ((x : ZMod q)) * χ (((x : ZMod q))⁻¹) = 1 := by
    rw [← map_mul, ZMod.mul_inv_of_unit _ x.isUnit, map_one]
  have hnorm : ‖χ ((x : ZMod q))‖ = 1 := DirichletCharacter.unit_norm_eq_one χ x
  rw [← Complex.inv_eq_conj hnorm]
  exact inv_eq_of_mul_eq_one_right h1

variable [HasEnoughRootsOfUnity ℂ (Monoid.exponent (ZMod q)ˣ)]

/-- **Character diagonalisation of the major-arc phase.**  For units `X, Z`
mod `q`,

`e_q(−a X Z) = (1/φ(q)) ∑_{χ mod q} G_{q,a}(χ) χ(X) χ(Z)`.

No primitivity is assumed. -/
theorem major_char_diagonal (a : ℤ) (X Z : (ZMod q)ˣ) :
    (1 / (q.totient : ℂ)) *
        ∑ χ : DirichletCharacter ℂ q,
          gaussSumChar q a χ * χ ((X : ZMod q)) * χ ((Z : ZMod q))
      = ezExp q (-(a * ((((X * Z : (ZMod q)ˣ) : ZMod q)).val : ℤ))) := by
  classical
  have htot : ((q.totient : ℂ)) ≠ 0 := by
    have : 0 < q.totient := Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))
    exact_mod_cast this.ne'
  have hswap : ∑ χ : DirichletCharacter ℂ q,
        gaussSumChar q a χ * χ ((X : ZMod q)) * χ ((Z : ZMod q))
      = ∑ x : (ZMod q)ˣ, ezExp q (-(a * (((x : ZMod q).val : ℤ)))) *
          ∑ χ : DirichletCharacter ℂ q,
            χ (((x : ZMod q))⁻¹) * χ (((X * Z : (ZMod q)ˣ) : ZMod q)) := by
    unfold gaussSumChar
    have step : ∀ χ : DirichletCharacter ℂ q,
        (∑ x : (ZMod q)ˣ, ezExp q (-(a * (((x : ZMod q).val : ℤ)))) *
            (starRingEnd ℂ) (χ ((x : ZMod q)))) * χ ((X : ZMod q)) * χ ((Z : ZMod q))
          = ∑ x : (ZMod q)ˣ, ezExp q (-(a * (((x : ZMod q).val : ℤ)))) *
              (χ (((x : ZMod q))⁻¹) * χ (((X * Z : (ZMod q)ˣ) : ZMod q))) := by
      intro χ
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [conj_char_apply]
      have hXZ : χ ((X : ZMod q)) * χ ((Z : ZMod q)) = χ (((X * Z : (ZMod q)ˣ) : ZMod q)) := by
        rw [← map_mul]
        norm_cast
      rw [← hXZ]
      ring
    rw [Finset.sum_congr rfl fun χ _ => step χ, Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum]
  rw [hswap]
  have horth : ∀ x : (ZMod q)ˣ,
      ∑ χ : DirichletCharacter ℂ q,
          χ (((x : ZMod q))⁻¹) * χ (((X * Z : (ZMod q)ˣ) : ZMod q))
        = if (x : ZMod q) = ((X * Z : (ZMod q)ˣ) : ZMod q) then (q.totient : ℂ) else 0 :=
    fun x => DirichletCharacter.sum_char_inv_mul_char_eq ℂ x.isUnit _
  rw [Finset.sum_congr rfl (fun x _ => by rw [horth x])]
  rw [Finset.mul_sum]
  rw [Finset.sum_eq_single (X * Z)]
  · rw [if_pos rfl]
    field_simp
  · intro y _ hy
    have : (y : ZMod q) ≠ ((X * Z : (ZMod q)ˣ) : ZMod q) := fun h => hy (Units.ext h)
    rw [if_neg this]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

end Char

/-! ## §D.  Unit / non-unit reduction -/

/-- **Exact reduction to the reduced modulus.**  If the argument carries a
factor `d` shared with the modulus, the phase descends to modulus `q/d`. -/
theorem nonunit_reduction (d q' : ℕ) (hd : d ≠ 0) (a m : ℤ) :
    ezExp (d * q') (-(a * ((d : ℤ) * m))) = ezExp q' (-(a * m)) := by
  rw [show -(a * ((d : ℤ) * m)) = (d : ℤ) * (-(a * m)) by ring]
  exact ezExp_scale_left d q' _ hd

/-- **The finite `gcd` partition** of a complete residue sum. -/
theorem gcd_partition (q : ℕ) (hq : q ≠ 0) (f : ℕ → ℂ) :
    ∑ d ∈ q.divisors, ∑ x ∈ (Finset.range q).filter (fun x => Nat.gcd x q = d), f x
      = ∑ x ∈ Finset.range q, f x := by
  refine Finset.sum_fiberwise_of_maps_to (fun x _ => ?_) f
  exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right x q, hq⟩

/-! ## §E.  Multiplicative (Dirichlet) factorisation -/

/-- **The four-product source diagonalises under a multiplicative character.**
This is the *correct* factorisation; the additive-Fourier factorisation refuted
by `C4ShiftAPFourier.c4_additive_factorisation_false` is not revived. -/
theorem char_fourfold_factor {q : ℕ} (χ : DirichletCharacter ℂ q) (x1 x2 x3 x4 : ZMod q) :
    χ (x1 * x2 * x3 * x4) = χ x1 * χ x2 * χ x3 * χ x4 := by
  simp [map_mul]

/-- The legal 2+2 four-product grouping, restated in this layer. -/
theorem fourProduct_2plus2' (Xs Zs Aset : Finset ℤ) (al ga : ℤ → ℂ) (om : ℝ)
    (hmaps : ∀ p ∈ Xs ×ˢ Zs, p.1 * p.2 ∈ Aset) :
    ∑ A ∈ Aset, (∑ p ∈ Xs ×ˢ Zs, if A = p.1 * p.2 then al p.1 * ga p.2 else 0) *
        eR (-(om * (A : ℝ)))
      = ∑ p ∈ Xs ×ˢ Zs, al p.1 * ga p.2 * eR (-(om * ((p.1 * p.2 : ℤ) : ℝ))) :=
  C4ShiftAPFourier.fourProduct_2plus2 Xs Zs Aset al ga om hmaps

/-! ## §F.  Leafwise source classification: deterministic first defect -/

/-- The deterministic first defect coordinate of the leaf `j`. -/
def firstDefectIndex (j : ℕ) : ℕ := j + 1

/-- `j = 5` is the pure model leaf. -/
theorem leaf_five_pure (lam del : ℕ → ℂ) :
    C4ShiftNormRepair.c4leaf 5 lam del = lam 1 * lam 2 * lam 3 * lam 4 :=
  C4ShiftNormRepair.c4leaf_five lam del

/-- For `j ≤ 4` the leaf contains the defect coordinate `δ_{i₀}` with
`i₀ = j + 1`.  Source classification only. -/
theorem leaf_first_defect (j : ℕ) (hj : j ≤ 4) (lam del : ℕ → ℂ) :
    C4ShiftNormRepair.c4leaf j lam del
      = (∏ i ∈ Finset.Ico 1 j, lam i) *
        (del (firstDefectIndex j) * ∏ i ∈ Finset.Ico (j + 2) 6, del i) :=
  C4ShiftNormRepair.c4leaf_first_defect j hj lam del

/-! ## §H.  The one-minor projector -/

/-- The one-minor projector `P₁ₘ(ω₁,ω₂) = 1 − M₄(ω₁) M₄(ω₂)`.  It carries the
major/minor, minor/major and minor/minor cells at once. -/
noncomputable def P1m (M4 : ℝ → ℂ) (o1 o2 : ℝ) : ℂ := 1 - M4 o1 * M4 o2

/-- With a genuine `{0,1}`-valued major projector, `P₁ₘ = 1` exactly on the
three one-minor cells. -/
theorem P1m_eq_one_iff (M4 : ℝ → ℂ) (o1 o2 : ℝ)
    (h1 : M4 o1 = 0 ∨ M4 o1 = 1) (h2 : M4 o2 = 0 ∨ M4 o2 = 1) :
    P1m M4 o1 o2 = 1 ↔ (M4 o1 = 0 ∨ M4 o2 = 0) := by
  unfold P1m
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

/-- `P₁ₘ = 0` exactly on the double-major cell. -/
theorem P1m_eq_zero_iff (M4 : ℝ → ℂ) (o1 o2 : ℝ)
    (h1 : M4 o1 = 0 ∨ M4 o1 = 1) (h2 : M4 o2 = 0 ∨ M4 o2 = 1) :
    P1m M4 o1 o2 = 0 ↔ (M4 o1 = 1 ∧ M4 o2 = 1) := by
  unfold P1m
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> simp [h1, h2]

section OneMinor

variable (S T H : Finset ℤ)

/-- **`Γ^{1m,♯}`**: the sharp source with the one-minor projector inserted **at
tuple level**.  The `r ≠ 0` and `|g| > thr` routing is a restriction of the
underlying tuple sum — never a multiplication of a post-summed `Γ` by an
`r`-indicator. -/
noncomputable def GammaOneMinorSharp (thr : ℤ) (om1 om2 : ℤ × ℤ × ℤ × ℤ × ℤ → ℝ)
    (M4 : ℝ → ℂ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (w g : ℤ) : ℂ :=
  ∑ i ∈ (gammaIndex S T H).filter (fun i => ¬ rCoord i = 0 ∧ ¬ |gCoord i| ≤ thr),
    (if w = wCoord nu i ∧ g = gCoord i then
      P1m M4 (om1 i) (om2 i) * gammaVal c kappa i else 0)

/-- The complementary **double-major** sharp source. -/
noncomputable def GammaDoubleMajorSharp (thr : ℤ) (om1 om2 : ℤ × ℤ × ℤ × ℤ × ℤ → ℝ)
    (M4 : ℝ → ℂ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (w g : ℤ) : ℂ :=
  ∑ i ∈ (gammaIndex S T H).filter (fun i => ¬ rCoord i = 0 ∧ ¬ |gCoord i| ≤ thr),
    (if w = wCoord nu i ∧ g = gCoord i then
      M4 (om1 i) * M4 (om2 i) * gammaVal c kappa i else 0)

/-- **Exact one-minor / double-major splitting of `Γ♯`.**  A pure linearity
identity: `P₁ₘ + M₄M₄ = 1` at every tuple. -/
theorem gammaSharp_one_minor_split (thr : ℤ) (om1 om2 : ℤ × ℤ × ℤ × ℤ × ℤ → ℝ)
    (M4 : ℝ → ℂ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (w g : ℤ) :
    GammaSharp S T H thr c kappa nu w g
      = GammaOneMinorSharp S T H thr om1 om2 M4 c kappa nu w g
        + GammaDoubleMajorSharp S T H thr om1 om2 M4 c kappa nu w g := by
  classical
  unfold GammaSharp GammaRestricted GammaOneMinorSharp GammaDoubleMajorSharp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : w = wCoord nu i ∧ g = gCoord i
  · rw [if_pos h, if_pos h, if_pos h]
    unfold P1m
    ring
  · rw [if_neg h, if_neg h, if_neg h, add_zero]

end OneMinor

/-! ## §I.  The `(h,K)` AP-index normal form on the odd clean sector -/

/-- **Inversion of the `(h,K)` substitution on the odd sector.**  If `v` is an
inverse of `2` mod `ℓ`, then `k₁ = v(K+h)` and `k₂ = v(K−h)`. -/
theorem hK_inversion (l : ℕ) (v k1 k2 : ZMod l) (hv : v * 2 = 1) :
    k1 = v * ((k1 + k2) + (k1 - k2)) ∧ k2 = v * ((k1 + k2) - (k1 - k2)) := by
  constructor
  · linear_combination (-k1) * hv
  · linear_combination (-k2) * hv

/-- **The exact `(h,K)` phase normal form.**  With `h = k₁ − k₂`, `K = k₁ + k₂`
and `v` an inverse of `2` mod `ℓ`,

`k₁A₁ − k₂A₂ + 2h w = v K (A₁ − A₂) + v h (A₁ + A₂ + 4w)`,

where `w` is the reciprocal residue `(us)⁻¹`. -/
theorem apindex_phase_normalform (l : ℕ) (v k1 k2 A1 A2 w : ZMod l) (hv : v * 2 = 1) :
    k1 * A1 - k2 * A2 + 2 * (k1 - k2) * w
      = v * (k1 + k2) * (A1 - A2) + v * (k1 - k2) * (A1 + A2 + 4 * w) := by
  linear_combination (-(k1 * A1) + k2 * A2 - 2 * k1 * w + 2 * k2 * w) * hv

/-- **Unrestricted `K`-orthogonality.**  A non-vanishing complete `K`-sum forces
the congruence in its argument. -/
theorem full_sum_support (l : ℕ) [NeZero l] (m : ℤ)
    (h : ∑ K ∈ Finset.range l, ezExp l ((K : ℤ) * m) ≠ 0) : (l : ℤ) ∣ m := by
  by_contra hd
  rw [sum_range_ezExp l m, if_neg hd] at h
  exact h rfl

/-- **Consequence of the two unrestricted sums.**  `ℓ ∣ A₁ − A₂` (from the full
`K`-sum) together with `ℓ ∣ A₁ + A₂ + 4w` (from the full `h`-sum) forces
`A₁ ≡ A₂ ≡ −2w (mod ℓ)`, where `w` is the reciprocal residue.

This is stated for the **unrestricted** sums only; nothing is claimed about the
restricted one-minor sums. -/
theorem full_hK_sums_force_A (l : ℕ) (A1 A2 w v : ℤ) (hv : (l : ℤ) ∣ (2 * v - 1))
    (h1 : (l : ℤ) ∣ (A1 - A2)) (h2 : (l : ℤ) ∣ (A1 + A2 + 4 * w)) :
    (l : ℤ) ∣ (A1 + 2 * w) ∧ (l : ℤ) ∣ (A2 + 2 * w) := by
  have hdouble : (l : ℤ) ∣ 2 * (A1 + 2 * w) := by
    have : 2 * (A1 + 2 * w) = (A1 - A2) + (A1 + A2 + 4 * w) := by ring
    rw [this]
    exact dvd_add h1 h2
  have hA1 : (l : ℤ) ∣ (A1 + 2 * w) := by
    have hexp : A1 + 2 * w
        = v * (2 * (A1 + 2 * w)) - (2 * v - 1) * (A1 + 2 * w) := by ring
    rw [hexp]
    exact dvd_sub (Dvd.dvd.mul_left hdouble v) (Dvd.dvd.mul_right hv _)
  refine ⟨hA1, ?_⟩
  have : A2 + 2 * w = (A1 + 2 * w) - (A1 - A2) := by ring
  rw [this]
  exact dvd_sub hA1 h1

/-! ## §J.  The `ℓ`-cardinality firewall (restated) -/

/-- `ℓ^{-2} · #{(k₁,k₂) mod ℓ} = 1`: the two AP-index state counts consume the
normalisation exactly.  Restated from the repair layer. -/
theorem ell_normalisation_no_saving' (l : ℕ) (hl : l ≠ 0) :
    ((l : ℝ) ^ 2)⁻¹ * ((Finset.range l ×ˢ Finset.range l).card : ℝ) = 1 :=
  C4ShiftNormRepair.ell_normalisation_no_saving l hl

/-! ## §K.  The current analytic socket (UNINHABITED) -/

/-- **UNINHABITED analytic socket** for the one-minor pushed energy:

`∫_θ [ ∑_v |Ĥ_j^{1m}(θ,v)|² ]^{1/2} dθ ≤ Y^{3/4} log^C X`

in the research scaling, written in the repository's discrete-Haar form.  It is
never constructed. -/
structure C4ShiftOneMinorPushedEnergyInput where
  /-- Number of sample points of the discrete `θ`-grid. -/
  P : ℕ
  /-- The shift support. -/
  Vset : Finset ℤ
  /-- The leaf index. -/
  leaf : ℕ
  /-- The one-minor pushed transform. -/
  Hh1m : ℕ → ℤ → ℂ
  /-- The natural bound (research value `Y^{3/4} log^C X`). -/
  naturalBound : ℝ
  /-- **The analytic estimate itself — never proved here.** -/
  bound : (1 / (P : ℝ)) * ∑ k ∈ Finset.range P,
      Real.sqrt (∑ v ∈ Vset, ‖Hh1m k v‖ ^ 2) ≤ naturalBound

/-- **UNINHABITED equivalent source socket**: the one-minor AP-index
restriction. -/
structure C4ShiftOneMinorAPIndexRestrictionInput where
  /-- The modulus family. -/
  Lset : Finset ℕ
  /-- The restricted AP-index sum, indexed by `(ℓ, k₁, k₂)`. -/
  restricted : ℕ → ℕ → ℕ → ℂ
  /-- The claimed bound. -/
  naturalBound : ℝ
  /-- **The analytic estimate itself — never proved here.** -/
  bound : ∑ l ∈ Lset, ((l : ℝ) ^ 2)⁻¹ *
      ∑ k1 ∈ Finset.range l, ∑ k2 ∈ Finset.range l, ‖restricted l k1 k2‖
    ≤ naturalBound

/-! ## Status metadata (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the leafwise major / one-minor delta. -/
def statusRows : List LedgerEntry :=
  [ ⟨"C4SHIFT-ONE-FOURPRODUCT-MINOR45", Status.supersededAsControllingFrontier,
     "OLD CLOSURE RETRACTED (recorded permanently). The pointwise bilinear estimate itself is NOT marked false."⟩,
    ⟨"C4SHIFT-ONE-MINOR-POINTWISE45", Status.falseRoute,
     "POWER NONCLOSING AS A PUSHED-NORM ROUTE. The pointwise -> L1_theta l2_v promotion is INVALID; see C4ShiftNormRepair.pointwise_substitution_nonclosing."⟩,
    ⟨"FOURPRODUCT-POINTWISE-MINOR45", Status.externallyAudited,
     "RESEARCH PASS / LOG-CORRECTED. Not formalised, not false."⟩,
    ⟨"C4SHIFT-MAJOR-ARC-OWNERSHIP45", Status.provedAlgebraic,
     "FORMALLY PROVED: farey_separation, major_arc_ownership_unique. Deterministic ownership of overlapping arcs. No asymptotic width estimate is formalised."⟩,
    ⟨"C4SHIFT-MAJOR-CHAR-DIAGONAL45", Status.provedAlgebraic,
     "FORMALLY PROVED: major_char_diagonal with gaussSumChar and the correct conjugations (conj_char_apply). No primitive-character assumption."⟩,
    ⟨"C4SHIFT-MAJOR-NONUNIT-REDUCTION45", Status.provedAlgebraic,
     "FORMALLY PROVED: nonunit_reduction, gcd_partition. The analytic claim that nonunit cells cost only log^O(1) remains RESEARCH METADATA."⟩,
    ⟨"C4SHIFT-MAJOR-MULTIPLICATIVE-FACTOR45", Status.provedAlgebraic,
     "ALGEBRAIC CORE FORMALLY PROVED: char_fourfold_factor and fourProduct_2plus2'. The false additive-Fourier factorisation is NOT revived. Mellin separation of smooth weights is NOT formalised."⟩,
    ⟨"C4SHIFT-J5-SOURCE", Status.provedAlgebraic,
     "PURE MODEL LEAF: leaf_five_pure."⟩,
    ⟨"C4SHIFT-JLT5-SOURCE", Status.provedAlgebraic,
     "CONTAINS ACTUAL DEFECT with deterministic first index i0 = j+1: leaf_first_defect, firstDefectIndex. No analytic smallness of delta-character transforms is claimed."⟩,
    ⟨"C4SHIFT-ONE-MINOR-PROJECTOR45", Status.provedAlgebraic,
     "FORMALLY PROVED: P1m, P1m_eq_one_iff, P1m_eq_zero_iff, gammaSharp_one_minor_split. The routing is inserted at TUPLE level; no post-summed Gamma is multiplied by an r-indicator."⟩,
    ⟨"C4SHIFT-APINDEX-ORTHOGONALITY45", Status.provedAlgebraic,
     "FORMALLY PROVED NORMAL FORM: hK_inversion, apindex_phase_normalform, full_sum_support, full_hK_sums_force_A. Odd clean sector only; the 2-adic sector is routed separately (see C4ShiftNormRepair.hKmap_not_injective_two). It is NOT claimed that the restricted one-minor sums collapse."⟩,
    ⟨"C4SHIFT-ELL-NORMALISATION-NOSAVING45", Status.provedFinite,
     "FORMALLY PROVED (restated): ell_normalisation_no_saving'."⟩,
    ⟨"C4SHIFT-DEFECT-SMALLMOD-CHAR45", Status.externallyAudited,
     "RESEARCH PASS CANDIDATE FOR NONPRINCIPAL; PRINCIPAL -> LOCAL PROFILE. NOT a formal Lean closure."⟩,
    ⟨"C4SHIFT-J5-MAJOR-LOCALMODEL45", Status.sourceOpen,
     "STRUCTURAL PASS; PHYSICAL CANONICAL MATCH SOURCE OPEN."⟩,
    ⟨"C4SHIFT-DOUBLEMAJOR-TO-LOCALMATCH45", Status.conditionalCompiler,
     "DECOMPOSITION PASS; NOT GATE CLOSURE."⟩,
    ⟨"C4SHIFT-ONE-MINOR-PUSHED-ENERGY45", Status.analyticOpen,
     "ANALYTIC OPEN / UNINHABITED: C4ShiftOneMinorPushedEnergyInput. FIRST EXACT ANALYTIC RESIDUAL."⟩,
    ⟨"C4SHIFT-ONE-MINOR-APINDEX-RESTRICTION45", Status.analyticOpen,
     "ANALYTIC OPEN / UNINHABITED equivalent source socket: C4ShiftOneMinorAPIndexRestrictionInput."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen,
     "CURRENT PARENT. OPEN."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
     "PARALLEL LOCAL CHILD. SOURCE OPEN; NOT CLOSED."⟩ ]

/-- No row of this delta is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

/-- The parallel local child is **not** closed. -/
theorem broad_major_tree_match_not_closed :
    ∀ e ∈ statusRows, e.label = "TOPBAND-BROAD-MAJOR-TREE-MATCH45" →
      e.status = Status.sourceOpen ∧ e.status.isKernelProved = false := by decide

end C4ShiftLeafwise
end CurrentProgramme
end TwinPrimeProject
