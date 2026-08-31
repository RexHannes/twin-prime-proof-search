import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import RequestProject.CurrentProgramme.AddMinRamanujanReciprocity
import Gate1B.C4ShiftQFourierPushforward

/-!
# Gate 1B · C4Shift AP-Fourier and the double-major frontier

**Append-only.**  Exact finite algebra and finite Fourier analysis only.  No
analytic estimate is proved here, and no research CLOSED claim is converted into
a Lean theorem.

## Contents

1. Character values (`eR_intCast`, `eR_neg_half`, …).
2. **Section A** — the tuple-level `Γ♯` and the exact three-way partition
   `Γ = Γ_{r=0} + Γ_{small g} + Γ♯`.  Physical thresholds live in the
   UNINHABITED interface `GammaSharpRangeInput`.
3. **Section B** — the AP-Fourier normal form
   `C(ξ) = e(ξA₀/ℓ)/ℓ · ∑_{k mod ℓ} e_ℓ(−kA₀) F4((ξ−k)/ℓ)`
   and the reciprocal form `e_ℓ(−kA₀) = e_ℓ(2k(us)⁻¹)`.
4. **Section C** — double reciprocity: `s A₀ = b_{u,ℓ} + ℓ ν` and the exact
   phase cancellation down to `e(−2θ/ℓ)`.
5. **Section D** — the *correct* 2+2 four-product grouping, and an explicit
   finite **counterexample** refuting the additive factorisation of the
   four-product transform.
6. **Section E** — linked frequencies.
7. **Section F** — an explicit algebraic **resonance** at which both linked
   frequencies vanish: "no double major" is FALSE at the algebraic level.
   (Nothing is claimed about `m_top`.)
8. **Section G** — the exact `s`-Gram identity for the two-line source.
9. **Section H** — collision geometry: the coprime factorisation of a
   same-`w` collision.
10. **Section I** — status rows (metadata only).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace C4ShiftAPFourier

open Finset FiniteLiftLocalTwist C4ShiftQFourier

/-! ## 0. Character values -/

theorem eR_intCast (n : ℤ) : eR ((n : ℝ)) = 1 := by
  unfold eR
  rw [show (2 * (Real.pi : ℂ) * Complex.I * ((n : ℝ) : ℂ))
      = (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I n

theorem eR_neg_one : eR (-1 : ℝ) = 1 := by
  have := eR_intCast (-1)
  simpa using this

theorem eR_neg_two : eR (-2 : ℝ) = 1 := by
  have := eR_intCast (-2)
  simpa using this

theorem eR_half : eR (1 / 2 : ℝ) = -1 := by
  unfold eR
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (((1 : ℝ) / 2 : ℝ) : ℂ))
      = (Real.pi : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

theorem eR_neg_half : eR (-(1 / 2) : ℝ) = -1 := by
  have h : (-(1 / 2) : ℝ) = 1 / 2 + (-1) := by norm_num
  rw [h, eR_add, eR_half, eR_neg_one, mul_one]

/-! ## Section A.  The tuple-level `Γ♯` and the exact partition -/

section Sharp

variable (S T H : Finset ℤ)

/-- The `r`-coordinate `r = t₂ − t₁` of a Γ-tuple.  It is a function of the
*tuple*, not of the post-summed `(w,g)` fibre. -/
def rCoord (i : ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ := i.2.2.1 - i.2.1

/-- `Γ` restricted, at the level of the underlying tuples, to a decidable
routing predicate. -/
noncomputable def GammaRestricted (P : ℤ × ℤ × ℤ × ℤ × ℤ → Prop)
    [DecidablePred P] (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ)
    (w g : ℤ) : ℂ :=
  ∑ i ∈ (gammaIndex S T H).filter P,
    (if w = wCoord nu i ∧ g = gCoord i then gammaVal c kappa i else 0)

/-- The `r = 0` branch. -/
noncomputable def GammaDiagR0 (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (w g : ℤ) : ℂ :=
  GammaRestricted S T H (fun i => rCoord i = 0) c kappa nu w g

/-- The `r ≠ 0`, `|g| ≤ threshold` branch. -/
noncomputable def GammaSmallG (thr : ℤ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ)
    (w g : ℤ) : ℂ :=
  GammaRestricted S T H (fun i => ¬ rCoord i = 0 ∧ |gCoord i| ≤ thr) c kappa nu w g

/-- **`Γ♯`**, defined at the level of the underlying tuples: `r ≠ 0` and
`|s r + h₂ − h₁| > threshold`. -/
noncomputable def GammaSharp (thr : ℤ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ)
    (w g : ℤ) : ℂ :=
  GammaRestricted S T H (fun i => ¬ rCoord i = 0 ∧ ¬ |gCoord i| ≤ thr) c kappa nu w g

/-- **Exact finite partition** of the two-line Γ-source into the `r = 0`
branch, the small-`g` branch and `Γ♯`.  This is a disjoint routing identity at
tuple level; nothing analytic is used. -/
theorem gamma_sharp_partition (thr : ℤ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ)
    (w g : ℤ) :
    GammaTwoLine S T H c kappa nu w g
      = GammaDiagR0 S T H c kappa nu w g
        + GammaSmallG S T H thr c kappa nu w g
        + GammaSharp S T H thr c kappa nu w g := by
  classical
  unfold GammaTwoLine GammaDiagR0 GammaSmallG GammaSharp GammaRestricted
  have h1 := Finset.sum_filter_add_sum_filter_not (gammaIndex S T H)
    (fun i => rCoord i = 0)
    (fun i => if w = wCoord nu i ∧ g = gCoord i then gammaVal c kappa i else 0)
  have h2 := Finset.sum_filter_add_sum_filter_not
    ((gammaIndex S T H).filter (fun i => ¬ rCoord i = 0))
    (fun i => |gCoord i| ≤ thr)
    (fun i => if w = wCoord nu i ∧ g = gCoord i then gammaVal c kappa i else 0)
  rw [Finset.filter_filter, Finset.filter_filter] at h2
  rw [← h1, ← h2, add_assoc]

/-- **UNINHABITED source-range interface.**  The physical scale thresholds
(`|g| ≤ L^{B₁}` routing) are not represented in this repository; this structure
records exactly what would be needed, and is never constructed. -/
structure GammaSharpRangeInput where
  /-- The routing threshold. -/
  thr : ℤ
  /-- The `s`-support. -/
  Ssup : Finset ℤ
  /-- The `t`-support. -/
  Tsup : Finset ℤ
  /-- The `h`-support. -/
  Hsup : Finset ℤ
  /-- The physical claim: off the `r = 0` diagonal, `g` is large. -/
  routing : ∀ i ∈ gammaIndex Ssup Tsup Hsup, ¬ rCoord i = 0 → thr < |gCoord i|

/-- Conditional on the (uninhabited) routing interface, the small-`g` branch is
empty and the partition collapses to two terms. -/
theorem gamma_smallG_vanishes (I : GammaSharpRangeInput) (c : ℤ → ℤ → ℂ)
    (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (w g : ℤ) :
    GammaSmallG I.Ssup I.Tsup I.Hsup I.thr c kappa nu w g = 0 := by
  classical
  unfold GammaSmallG GammaRestricted
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_filter] at hi
  exact absurd (I.routing i hi.1 hi.2.1) (not_lt.2 hi.2.2)

end Sharp

/-! ## Section B.  The AP-Fourier normal form -/

/-- **AP restriction in Fourier form.**  For `ℓ ≠ 0`, restricting a finite
`A`-sum to the residue class `A ≡ A₀ (mod ℓ)` costs exactly an average of `ℓ`
shifted transforms. -/
theorem ap_fourier_restriction (l : ℕ) [NeZero l] (Aset : Finset ℤ) (f : ℤ → ℂ)
    (A0 : ℤ) (om : ℝ) :
    ∑ A ∈ Aset.filter (fun A => (l : ℤ) ∣ (A - A0)), f A * eR (-(om * (A : ℝ)))
      = (1 / (l : ℂ)) * ∑ k ∈ Finset.range l, ezExp l (-((k : ℤ) * A0)) *
          ∑ A ∈ Aset, f A * eR (-((om - (k : ℝ) / (l : ℝ)) * (A : ℝ))) := by
  classical
  have hlC : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hlR : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have key : ∀ k ∈ Finset.range l,
      ezExp l (-((k : ℤ) * A0)) *
          ∑ A ∈ Aset, f A * eR (-((om - (k : ℝ) / (l : ℝ)) * (A : ℝ)))
        = ∑ A ∈ Aset, f A * eR (-(om * (A : ℝ))) * ezExp l ((k : ℤ) * (A - A0)) := by
    intro k _
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    have hphase : eR (((-((k : ℤ) * A0) : ℤ) : ℝ) / (l : ℝ)) *
          eR (-((om - (k : ℝ) / (l : ℝ)) * (A : ℝ)))
        = eR (-(om * (A : ℝ))) * eR ((((k : ℤ) * (A - A0) : ℤ) : ℝ) / (l : ℝ)) := by
      rw [← eR_add, ← eR_add]
      congr 1
      push_cast
      field_simp
      ring
    calc ezExp l (-((k : ℤ) * A0)) * (f A * eR (-((om - (k : ℝ) / (l : ℝ)) * (A : ℝ))))
        = f A * (eR (((-((k : ℤ) * A0) : ℤ) : ℝ) / (l : ℝ)) *
            eR (-((om - (k : ℝ) / (l : ℝ)) * (A : ℝ)))) := by
          rw [ezExp_eq_eR]; ring
      _ = f A * (eR (-(om * (A : ℝ))) * eR ((((k : ℤ) * (A - A0) : ℤ) : ℝ) / (l : ℝ))) := by
          rw [hphase]
      _ = f A * eR (-(om * (A : ℝ))) * ezExp l ((k : ℤ) * (A - A0)) := by
          rw [ezExp_eq_eR]; ring
  rw [Finset.sum_congr rfl key, Finset.sum_comm, Finset.mul_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [← Finset.mul_sum, sum_range_ezExp l (A - A0)]
  by_cases hd : (l : ℤ) ∣ (A - A0)
  · rw [if_pos hd, if_pos hd]
    field_simp
  · rw [if_neg hd, if_neg hd]
    simp

/-- **The AP-Fourier normal form of the line coefficient.**

With `a` the source coefficient in the `A`-variable, `C(ξ) = ∑_t a(A₀+ℓt) e(−ξt)`
and `F4(ω) = ∑_{A} a(A) e(−ωA)`, the exact identity is

`C(ξ) = e(ξ A₀/ℓ) · (1/ℓ) · ∑_{k mod ℓ} e_ℓ(−k A₀) F4((ξ−k)/ℓ)`.

The physical support statement (that the AP slice of `Aset` is exactly the
`t`-line) is an explicit hypothesis. -/
theorem lineCoeff_ap_fourier (l : ℕ) [NeZero l] (Tsup Aset : Finset ℤ) (a : ℤ → ℂ)
    (A0 : ℤ) (xi : ℝ)
    (hsupport : Aset.filter (fun A => (l : ℤ) ∣ (A - A0))
      = Tsup.image (fun t => A0 + (l : ℤ) * t)) :
    ∑ t ∈ Tsup, a (A0 + (l : ℤ) * t) * eR (-(xi * (t : ℝ)))
      = eR (xi * (A0 : ℝ) / (l : ℝ)) * ((1 / (l : ℂ)) *
          ∑ k ∈ Finset.range l, ezExp l (-((k : ℤ) * A0)) *
            ∑ A ∈ Aset, a A * eR (-(((xi - (k : ℝ)) / (l : ℝ)) * (A : ℝ)))) := by
  classical
  have hlR : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hinj : Set.InjOn (fun t : ℤ => A0 + (l : ℤ) * t) Tsup := by
    intro x _ y _ hxy
    have hl0 : (l : ℤ) ≠ 0 := Int.natCast_ne_zero.2 (NeZero.ne l)
    have : (l : ℤ) * x = (l : ℤ) * y := by simpa using hxy
    exact mul_left_cancel₀ hl0 this
  -- rewrite the `t`-line as the AP slice
  have hline : ∑ A ∈ Aset.filter (fun A => (l : ℤ) ∣ (A - A0)),
        a A * eR (-((xi / (l : ℝ)) * (A : ℝ)))
      = ∑ t ∈ Tsup, a (A0 + (l : ℤ) * t) *
          eR (-((xi / (l : ℝ)) * ((A0 + (l : ℤ) * t : ℤ) : ℝ))) := by
    rw [hsupport, Finset.sum_image (fun x hx y hy h => hinj hx hy h)]
  have hAP := ap_fourier_restriction l Aset a A0 (xi / (l : ℝ))
  have hfreq : ∀ k : ℕ, (xi / (l : ℝ) - (k : ℝ) / (l : ℝ)) = (xi - (k : ℝ)) / (l : ℝ) := by
    intro k; field_simp
  simp only [hfreq] at hAP
  rw [hline] at hAP
  rw [← hAP]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hph : eR (xi * (A0 : ℝ) / (l : ℝ)) *
          eR (-((xi / (l : ℝ)) * ((A0 + (l : ℤ) * t : ℤ) : ℝ)))
        = eR (-(xi * (t : ℝ))) := by
      rw [← eR_add]
      congr 1
      push_cast
      field_simp
      ring
    calc a (A0 + (l : ℤ) * t) * eR (-(xi * (t : ℝ)))
        = a (A0 + (l : ℤ) * t) * (eR (xi * (A0 : ℝ) / (l : ℝ)) *
            eR (-((xi / (l : ℝ)) * ((A0 + (l : ℤ) * t : ℤ) : ℝ)))) := by rw [hph]
      _ = eR (xi * (A0 : ℝ) / (l : ℝ)) * (a (A0 + (l : ℤ) * t) *
            eR (-((xi / (l : ℝ)) * ((A0 + (l : ℤ) * t : ℤ) : ℝ)))) := by ring

/-- **Reciprocal form of the AP phase.**  If `u s A₀ ≡ −2 (mod ℓ)` and `w` is an
inverse of `u s` modulo `ℓ`, then `e_ℓ(−k A₀) = e_ℓ(2 k w)`. -/
theorem ap_phase_reciprocal (l : ℕ) (k u s A0 w : ℤ)
    (hA0 : (l : ℤ) ∣ (u * s * A0 + 2)) (hw : (l : ℤ) ∣ (u * s * w - 1)) :
    ezExp l (-(k * A0)) = ezExp l (2 * k * w) := by
  refine AddMinRamanujan.ezExp_congr l ?_
  have hkey : A0 + 2 * w = w * (u * s * A0 + 2) - A0 * (u * s * w - 1) := by ring
  have h : (l : ℤ) ∣ (A0 + 2 * w) := by
    rw [hkey]
    exact dvd_sub (Dvd.dvd.mul_left hA0 w) (Dvd.dvd.mul_left hw A0)
  have : -(k * A0) - 2 * k * w = -k * (A0 + 2 * w) := by ring
  rw [this]
  exact Dvd.dvd.mul_left h (-k)

/-! ## Section C.  Double reciprocity normal form -/

/-- `b_{u,ℓ}` exists as an integer: `u ∣ ℓ y_{u,ℓ} − 2`. -/
theorem exists_bul {l y u : ℤ} (h : u ∣ (l * y - 2)) : ∃ b : ℤ, u * b = l * y - 2 := by
  obtain ⟨b, hb⟩ := h
  exact ⟨b, hb.symm⟩

/-- `s A₀ = b_{u,ℓ} + ℓ ν`, from `u s A₀ + 2 = ℓ y₀`, `y₀ = y_{u,ℓ} + u ν` and
`u b = ℓ y_{u,ℓ} − 2`. -/
theorem sA0_eq_b_add_l_nu {u s A0 l y0 ycan nu b : ℤ} (hu : u ≠ 0)
    (hy0 : u * s * A0 + 2 = l * y0) (hnu : y0 = ycan + u * nu)
    (hb : u * b = l * ycan - 2) :
    s * A0 = b + l * nu := by
  have h : u * (s * A0) = u * (b + l * nu) := by
    have : u * s * A0 + 2 = l * (ycan + u * nu) := by rw [← hnu]; exact hy0
    nlinarith [this, hb]
  exact mul_left_cancel₀ hu h

/-- **The double-reciprocity phase cancellation.**  All `A₀`- and `ν`-phases
cancel against the reciprocal residue, leaving exactly `e(−2θ/ℓ)`. -/
theorem double_reciprocity_phase (l u y b nu s A0 : ℤ) (theta : ℝ)
    (hl : (l : ℝ) ≠ 0) (hb : u * b = l * y - 2) (hsA : s * A0 = b + l * nu) :
    eR (-(theta * (y : ℝ))) *
        eR ((u : ℝ) * theta * ((s * A0 : ℤ) : ℝ) / (l : ℝ)) *
        eR (-((u : ℝ) * theta * (nu : ℝ)))
      = eR (-(2 * theta / (l : ℝ))) := by
  have hbR : (u : ℝ) * (b : ℝ) = (l : ℝ) * (y : ℝ) - 2 := by exact_mod_cast hb
  have hsAR : ((s * A0 : ℤ) : ℝ) = (b : ℝ) + (l : ℝ) * (nu : ℝ) := by exact_mod_cast hsA
  rw [← eR_add, ← eR_add]
  congr 1
  rw [hsAR]
  field_simp
  linear_combination theta * hbR

/-! ## Section D.  The four-product source: correct 2+2 grouping -/

/-- Fibrewise collapse along the multiplication map `(X,Z) ↦ XZ`. -/
theorem sum_mul_fibre (Xs Zs Aset : Finset ℤ) (al ga : ℤ → ℂ) (phi : ℤ → ℂ)
    (hmaps : ∀ p ∈ Xs ×ˢ Zs, p.1 * p.2 ∈ Aset) :
    ∑ A ∈ Aset, (∑ p ∈ Xs ×ˢ Zs, if A = p.1 * p.2 then al p.1 * ga p.2 else 0) * phi A
      = ∑ p ∈ Xs ×ˢ Zs, al p.1 * ga p.2 * phi (p.1 * p.2) := by
  classical
  have h1 : ∀ A ∈ Aset,
      (∑ p ∈ Xs ×ˢ Zs, if A = p.1 * p.2 then al p.1 * ga p.2 else 0) * phi A
        = ∑ p ∈ Xs ×ˢ Zs,
            (if A = p.1 * p.2 then al p.1 * ga p.2 * phi (p.1 * p.2) else 0) := by
    intro A _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : A = p.1 * p.2
    · rw [if_pos h, if_pos h, h]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_ite_eq' Aset (p.1 * p.2) (fun _ => al p.1 * ga p.2 * phi (p.1 * p.2)),
    if_pos (hmaps p hp)]

/-- **The correct 2+2 four-product grouping.**  With the source coefficient
defined by the *multiplicative* pairing `c₄(A) = ∑_{XZ = A} α(X) γ(Z)`, the
transform is the bilinear form `∑_{X,Z} α(X) γ(Z) e(−ω X Z)`. -/
theorem fourProduct_2plus2 (Xs Zs Aset : Finset ℤ) (al ga : ℤ → ℂ) (om : ℝ)
    (hmaps : ∀ p ∈ Xs ×ˢ Zs, p.1 * p.2 ∈ Aset) :
    ∑ A ∈ Aset, (∑ p ∈ Xs ×ˢ Zs, if A = p.1 * p.2 then al p.1 * ga p.2 else 0) *
        eR (-(om * (A : ℝ)))
      = ∑ p ∈ Xs ×ˢ Zs, al p.1 * ga p.2 * eR (-(om * ((p.1 * p.2 : ℤ) : ℝ))) := by
  exact sum_mul_fibre Xs Zs Aset al ga (fun A => eR (-(om * (A : ℝ)))) hmaps

/-- **COUNTEREXAMPLE.**  The four-product transform does **not** factor as a
product of two transforms: a multiplicative Dirichlet pairing is not an additive
convolution.  Explicit witness: `α = γ = 1` on `{1,2}` and `ω = 1/2`, where the
bilinear form equals `2` and the product of transforms equals `0`. -/
theorem c4_additive_factorisation_false :
    ∃ (al ga : ℤ → ℂ) (Xs Zs : Finset ℤ) (om : ℝ),
      ∑ p ∈ Xs ×ˢ Zs, al p.1 * ga p.2 * eR (-(om * ((p.1 * p.2 : ℤ) : ℝ)))
        ≠ (∑ X ∈ Xs, al X * eR (-(om * (X : ℝ)))) *
          (∑ Z ∈ Zs, ga Z * eR (-(om * (Z : ℝ)))) := by
  classical
  refine ⟨fun _ => 1, fun _ => 1, {1, 2}, {1, 2}, 1 / 2, ?_⟩
  have hne : (1 : ℤ) ≠ 2 := by norm_num
  rw [Finset.sum_product, Finset.sum_pair hne, Finset.sum_pair hne, Finset.sum_pair hne]
  have c1 : (-(1 / 2 * (((1 : ℤ) * (1 : ℤ) : ℤ) : ℝ)) : ℝ) = -(1 / 2) := by norm_num
  have c2 : (-(1 / 2 * (((1 : ℤ) * (2 : ℤ) : ℤ) : ℝ)) : ℝ) = -1 := by norm_num
  have c3 : (-(1 / 2 * (((2 : ℤ) * (1 : ℤ) : ℤ) : ℝ)) : ℝ) = -1 := by norm_num
  have c4 : (-(1 / 2 * (((2 : ℤ) * (2 : ℤ) : ℤ) : ℝ)) : ℝ) = -2 := by norm_num
  simp only [c1, c2, c3, c4, eR_neg_half, eR_neg_one, eR_neg_two]
  norm_num [eR_neg_half, eR_neg_one]

/-! ## Section E.  Linked frequencies -/

/-- The two AP frequencies produced by the double-Fourier factorisation. -/
noncomputable def omega1 (s al eta k1 l : ℝ) : ℝ := (s * (al - eta) - k1) / l

/-- The second AP frequency. -/
noncomputable def omega2 (s eta k2 l : ℝ) : ℝ := (-(s * eta) - k2) / l

/-- **Linked frequency difference.**  With `α = u θ` and `h = k₁ − k₂`,
`ω₁ − ω₂ = (s u θ − h)/ℓ`. -/
theorem linked_frequency_diff (s u theta eta k1 k2 l : ℝ) :
    omega1 s (u * theta) eta k1 l - omega2 s eta k2 l
      = (s * u * theta - (k1 - k2)) / l := by
  unfold omega1 omega2
  ring

/-- **Linked frequency sum.**  With `α = u θ` and `K = k₁ + k₂`,
`ω₁ + ω₂ = (s u θ − 2 s η − K)/ℓ`. -/
theorem linked_frequency_sum (s u theta eta k1 k2 l : ℝ) :
    omega1 s (u * theta) eta k1 l + omega2 s eta k2 l
      = (s * u * theta - 2 * s * eta - (k1 + k2)) / l := by
  unfold omega1 omega2
  ring

/-! ## Section F.  Algebraic resonance: "no double major" is false -/

/-- **The double-major resonance family.**  For every `s ≠ 0` and every pair
`(a,b)`, the choice `η = a/s`, `u θ = (a+b)/s`, `k₁ = b`, `k₂ = −a` makes *both*
linked frequencies vanish.  Hence a statement asserting that the two AP
frequencies cannot vanish simultaneously is **false at the algebraic level**.

Nothing whatsoever is claimed here about the top-band multiplier. -/
theorem double_major_resonance (l s a b : ℝ) (hs : s ≠ 0) :
    omega1 s ((a + b) / s) (a / s) b l = 0 ∧ omega2 s (a / s) (-a) l = 0 := by
  constructor
  · unfold omega1
    have : s * ((a + b) / s - a / s) - b = 0 := by field_simp; ring
    rw [this, zero_div]
  · unfold omega2
    have : -(s * (a / s)) - -a = 0 := by field_simp; ring
    rw [this, zero_div]

/-! ## Section G.  The `s`-Gram identity -/

/-- The `s`-indexed inner product `⟨B_{s₁}, B_{s₂}⟩ = ∑_x B_{s₁}(x) conj B_{s₂}(x)`. -/
noncomputable def sInner (W : Finset ℤ) (B : ℤ → ℤ → ℂ) (s1 s2 : ℤ) : ℂ :=
  ∑ x ∈ W, B s1 x * (starRingEnd ℂ) (B s2 x)

/-- The two-point form `Γ'(x,y) = ∑_s B_s(x) conj B_s(y)`; the physical
`Γ(w,g)` is `Γ'(w, w+g)`. -/
noncomputable def GammaTwoPoint (S : Finset ℤ) (B : ℤ → ℤ → ℂ) (x y : ℤ) : ℂ :=
  ∑ s ∈ S, B s x * (starRingEnd ℂ) (B s y)

/-- **Exact `s`-Gram identity (`g`-Plancherel).**

`∑_{x,y} |Γ'(x,y)|² = ∑_{s₁,s₂} |⟨B_{s₁},B_{s₂}⟩|²`,
written multiplicatively with `z * conj z`. -/
theorem gram_identity (W S : Finset ℤ) (B : ℤ → ℤ → ℂ) :
    ∑ p ∈ W ×ˢ W, GammaTwoPoint S B p.1 p.2 * (starRingEnd ℂ) (GammaTwoPoint S B p.1 p.2)
      = ∑ q ∈ S ×ˢ S, sInner W B q.1 q.2 * (starRingEnd ℂ) (sInner W B q.1 q.2) := by
  classical
  have expand : ∀ p ∈ W ×ˢ W,
      GammaTwoPoint S B p.1 p.2 * (starRingEnd ℂ) (GammaTwoPoint S B p.1 p.2)
        = ∑ s1 ∈ S, ∑ s2 ∈ S,
            (B s1 p.1 * (starRingEnd ℂ) (B s1 p.2)) *
              (starRingEnd ℂ) (B s2 p.1 * (starRingEnd ℂ) (B s2 p.2)) := by
    intro p _
    unfold GammaTwoPoint
    rw [map_sum, Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl expand]
  rw [Finset.sum_comm]
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun s1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s2 _ => ?_
  -- fixed `(s₁,s₂)`: the `(x,y)` sum factorises
  have hfac : ∑ p ∈ W ×ˢ W,
      (B s1 p.1 * (starRingEnd ℂ) (B s1 p.2)) *
        (starRingEnd ℂ) (B s2 p.1 * (starRingEnd ℂ) (B s2 p.2))
      = (∑ x ∈ W, B s1 x * (starRingEnd ℂ) (B s2 x)) *
        (∑ y ∈ W, (starRingEnd ℂ) (B s1 y) * B s2 y) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  rw [hfac]
  unfold sInner
  congr 1
  rw [map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp only [map_mul, Complex.conj_conj]

/-! ## Section H.  Collision geometry -/

/-- **Same-`w` collision, coprime factorisation.**  If `s₁ A₁ = s₂ A₂` with
`s₁ = d a`, `s₂ = d b`, `d ≠ 0` and `a, b` coprime, then there is a common
cofactor `C` with `A₁ = b C` and `A₂ = a C`. -/
theorem collision_coprime_factorisation {s1 s2 A1 A2 d a b : ℤ}
    (hs1 : s1 = d * a) (hs2 : s2 = d * b) (hd : d ≠ 0) (hab : IsCoprime a b)
    (h : s1 * A1 = s2 * A2) :
    ∃ C : ℤ, A1 = b * C ∧ A2 = a * C := by
  have hcancel : a * A1 = b * A2 := by
    apply mul_left_cancel₀ hd
    calc d * (a * A1) = s1 * A1 := by rw [hs1]; ring
      _ = s2 * A2 := h
      _ = d * (b * A2) := by rw [hs2]; ring
  obtain ⟨x, y, hxy⟩ := hab
  refine ⟨x * A2 + y * A1, ?_, ?_⟩
  · calc A1 = (x * a + y * b) * A1 := by rw [hxy]; ring
      _ = x * (a * A1) + y * b * A1 := by ring
      _ = x * (b * A2) + y * b * A1 := by rw [hcancel]
      _ = b * (x * A2 + y * A1) := by ring
  · calc A2 = (x * a + y * b) * A2 := by rw [hxy]; ring
      _ = x * a * A2 + y * (b * A2) := by ring
      _ = x * a * A2 + y * (a * A1) := by rw [hcancel]
      _ = a * (x * A2 + y * A1) := by ring

/-! ## Section I.  Status metadata (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the AP-Fourier / double-major delta. -/
def statusRows : List LedgerEntry :=
  [ ⟨"C4SHIFT-GAMMASHARP-TUPLE-PARTITION45", Status.provedAlgebraic,
     "FORMALLY BANKED. GammaSharp is defined at TUPLE level (r is not a function of the (w,g) fibre); gamma_sharp_partition is an exact three-way finite partition. The physical thresholds are the UNINHABITED GammaSharpRangeInput."⟩,
    ⟨"C4SHIFT-AP-FOURIER-NORMALFORM45", Status.provedAlgebraic,
     "FORMALLY BANKED. ap_fourier_restriction and lineCoeff_ap_fourier: C(xi) = e(xi A0/l)/l * sum_k e_l(-k A0) F4((xi-k)/l). ap_phase_reciprocal gives e_l(-k A0) = e_l(2 k (us)^{-1})."⟩,
    ⟨"C4SHIFT-DOUBLE-RECIPROCITY-NORMALFORM45", Status.provedAlgebraic,
     "FORMALLY BANKED. sA0_eq_b_add_l_nu and double_reciprocity_phase: all A0- and nu-phases cancel, leaving exactly e(-2 theta / l)."⟩,
    ⟨"C4SHIFT-C4-FOURIER-FACTOR45", Status.falseRoute,
     "FALSE. The multiplicative Dirichlet pairing of the four-product source was incorrectly treated as an additive convolution. Refuted by the explicit finite countermodel c4_additive_factorisation_false."⟩,
    ⟨"CORRECT-2PLUS2-FOURPRODUCT45", Status.provedAlgebraic,
     "FORMALLY BANKED. fourProduct_2plus2 (via sum_mul_fibre): the legal grouping is the bilinear form sum_{X,Z} alpha(X) gamma(Z) e(-omega X Z)."⟩,
    ⟨"C4SHIFT-LINKED-FREQUENCY45", Status.provedAlgebraic,
     "FORMALLY BANKED. linked_frequency_diff and linked_frequency_sum."⟩,
    ⟨"C4SHIFT-NO-DOUBLE-MAJOR45", Status.falseRoute,
     "FALSE AT THE ALGEBRAIC RESONANCE LEVEL. double_major_resonance exhibits eta = a/s, u theta = (a+b)/s, k1 = b, k2 = -a with omega1 = omega2 = 0. NOTHING is claimed about the top-band multiplier m_top."⟩,
    ⟨"C4SHIFT-S-GRAM-IDENTITY45", Status.provedAlgebraic,
     "FORMALLY BANKED. gram_identity: sum_{x,y} |Gamma'(x,y)|^2 = sum_{s1,s2} |<B_{s1},B_{s2}>|^2. No Gram contraction estimate is claimed."⟩,
    ⟨"C4SHIFT-COLLISION-GEOMETRY45", Status.provedAlgebraic,
     "FORMALLY BANKED. collision_coprime_factorisation: s1 A1 = s2 A2 with s1 = d a, s2 = d b, gcd(a,b)=1 forces A1 = b C, A2 = a C."⟩,
    ⟨"C4SHIFT-DOUBLEMAJOR-FOURPRODUCT-APGRAM45", Status.analyticOpen,
     "ANALYTIC OPEN / UNINHABITED. No analytic estimate for the double-major four-product AP-Gram sector is formalised anywhere in this repository."⟩ ]

/-- No row of this delta is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

/-- The two refuted routes are recorded as `falseRoute`, and no row of this
delta claims a kernel proof of an analytic statement. -/
theorem false_rows_are_marked_false :
    ∀ e ∈ statusRows, e.status = Status.falseRoute →
      e.status.isKernelProved = false := by decide

end C4ShiftAPFourier
end CurrentProgramme
end TwinPrimeProject
