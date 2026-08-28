/-
# Gate 1B v12 — additive Θ-Fourier transform of the moving Kloosterman family

**Status: PROVED_ALGEBRAIC.  COORDINATE TRANSFORM ONLY — NOT A SAVING.**

For an explicit additive character system mod `c` (the repository convention,
`Gate1B.SafeAlgebra.AdditiveCharacterSystem`) and a unit `t`, we compute the
additive Fourier transform of the moving family `Θ ↦ S(tΘ, 1; c)` exactly:

    ∑_{Θ mod c} S(tΘ,1;c) e_c(-ξΘ)  =  c · e_c(t ξ⁻¹)   for ξ a unit,
                                    =  0                 otherwise.

We also prove the finite Plancherel identity for the transform and deduce the
exact square mass `∑_Θ |S(tΘ,1;c)|² = c · |(ZMod c)ˣ|`.

**Formal status comment: coordinate transform only.**  Both directions of this
identity carry exactly the same mass; nothing is contracted, and no Kloosterman
estimate (Weil or otherwise) is claimed or used.

Contents:

* `addHat` — the additive transform;
* `add_plancherel`;
* `kloosterman_theta_fourier_unit`, `kloosterman_theta_fourier_nonunit`;
* `kloosterman_theta_square_mass`;
* `thetaFourier_is_coordinate_change` — the mass-preservation statement.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteKloosterman

namespace Gate1B.SafeAlgebra

open Finset

namespace AdditiveCharacterSystem

variable {c : ℕ} [NeZero c] (C : AdditiveCharacterSystem c)

/-- The additive (Θ-side) Fourier transform. -/
noncomputable def addHat (f : ZMod c → ℂ) (xi : ZMod c) : ℂ :=
  ∑ theta : ZMod c, f theta * C.chi (-(xi * theta))

/-- **Finite Plancherel** for the additive Θ-transform: the transform multiplies
the total mass by exactly `c`. -/
theorem add_plancherel (f : ZMod c → ℂ) :
    ∑ xi : ZMod c, ‖C.addHat f xi‖ ^ 2 = (c : ℝ) * ∑ theta : ZMod c, ‖f theta‖ ^ 2 := by
  classical
  have hL : ((∑ xi : ZMod c, ‖C.addHat f xi‖ ^ 2 : ℝ) : ℂ)
      = ∑ xi : ZMod c, C.addHat f xi * (starRingEnd ℂ) (C.addHat f xi) := by
    push_cast
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have key : (∑ xi : ZMod c, C.addHat f xi * (starRingEnd ℂ) (C.addHat f xi))
      = (c : ℂ) * ∑ theta : ZMod c, f theta * (starRingEnd ℂ) (f theta) := by
    have expand : ∀ xi : ZMod c, C.addHat f xi * (starRingEnd ℂ) (C.addHat f xi)
        = ∑ a : ZMod c, ∑ b : ZMod c,
            (f a * (starRingEnd ℂ) (f b)) * C.chi (xi * (b - a)) := by
      intro xi
      unfold addHat
      rw [map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      have h1 : (starRingEnd ℂ) (f b * C.chi (-(xi * b)))
          = (starRingEnd ℂ) (f b) * C.chi (xi * b) := by
        rw [map_mul, C.conj_eq, neg_neg]
      rw [h1]
      have h2 : C.chi (-(xi * a)) * C.chi (xi * b) = C.chi (xi * (b - a)) := by
        rw [← C.add]
        congr 1
        ring
      calc f a * C.chi (-(xi * a)) * ((starRingEnd ℂ) (f b) * C.chi (xi * b))
          = (f a * (starRingEnd ℂ) (f b)) * (C.chi (-(xi * a)) * C.chi (xi * b)) := by ring
        _ = (f a * (starRingEnd ℂ) (f b)) * C.chi (xi * (b - a)) := by rw [h2]
    simp_rw [expand]
    rw [Finset.sum_comm]
    have inner : ∀ a : ZMod c, ∑ xi : ZMod c, ∑ b : ZMod c,
        (f a * (starRingEnd ℂ) (f b)) * C.chi (xi * (b - a))
        = (c : ℂ) * (f a * (starRingEnd ℂ) (f a)) := by
      intro a
      rw [Finset.sum_comm]
      have hb : ∀ b : ZMod c, ∑ xi : ZMod c, (f a * (starRingEnd ℂ) (f b)) * C.chi (xi * (b - a))
          = (f a * (starRingEnd ℂ) (f b)) * (if b - a = 0 then (c : ℂ) else 0) := by
        intro b
        rw [← Finset.mul_sum, C.orthogonality (b - a)]
      simp_rw [hb]
      have hb2 : ∀ b : ZMod c, (f a * (starRingEnd ℂ) (f b)) * (if b - a = 0 then (c : ℂ) else 0)
          = (if b = a then (f a * (starRingEnd ℂ) (f b)) * (c : ℂ) else 0) := by
        intro b
        by_cases h : b = a
        · simp [h]
        · have : b - a ≠ 0 := sub_ne_zero.mpr h
          simp [h, this]
      simp_rw [hb2]
      rw [Finset.sum_ite_eq' Finset.univ a]
      simp [mul_comm]
    simp_rw [inner]
    rw [← Finset.mul_sum]
  have h2 : (∑ theta : ZMod c, f theta * (starRingEnd ℂ) (f theta))
      = ((∑ theta : ZMod c, ‖f theta‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  have hfinal : ((∑ xi : ZMod c, ‖C.addHat f xi‖ ^ 2 : ℝ) : ℂ)
      = (((c : ℝ) * ∑ theta : ZMod c, ‖f theta‖ ^ 2 : ℝ) : ℂ) := by
    rw [hL, key, h2]
    push_cast
    ring
  exact_mod_cast hfinal

/-- **Exact Θ-Fourier evaluation at a unit frequency.** -/
theorem kloosterman_theta_fourier_unit (t xi : (ZMod c)ˣ) :
    C.addHat (fun theta => C.kloosterman ((t : ZMod c) * theta) 1) (xi : ZMod c)
      = (c : ℂ) * C.chi ((t : ZMod c) * ((xi⁻¹ : (ZMod c)ˣ) : ZMod c)) := by
  classical
  unfold addHat kloosterman
  have step : ∀ theta : ZMod c,
      (∑ u : (ZMod c)ˣ, C.chi ((t : ZMod c) * theta * (u : ZMod c)
          + 1 * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))) * C.chi (-((xi : ZMod c) * theta))
      = ∑ u : (ZMod c)ˣ, C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c))
          * C.chi (theta * ((t : ZMod c) * (u : ZMod c) - (xi : ZMod c))) := by
    intro theta
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [C.add, one_mul]
    rw [mul_comm (C.chi ((t : ZMod c) * theta * (u : ZMod c)))]
    rw [mul_assoc, ← C.add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun theta _ => step theta]
  rw [Finset.sum_comm]
  have inner : ∀ u : (ZMod c)ˣ,
      (∑ theta : ZMod c, C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c))
        * C.chi (theta * ((t : ZMod c) * (u : ZMod c) - (xi : ZMod c))))
      = C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c))
        * (if (t : ZMod c) * (u : ZMod c) - (xi : ZMod c) = 0 then (c : ℂ) else 0) := by
    intro u
    rw [← Finset.mul_sum, C.orthogonality _]
  rw [Finset.sum_congr rfl fun u _ => inner u]
  have hcond : ∀ u : (ZMod c)ˣ,
      C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c))
        * (if (t : ZMod c) * (u : ZMod c) - (xi : ZMod c) = 0 then (c : ℂ) else 0)
      = if u = t⁻¹ * xi then C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c)) * (c : ℂ) else 0 := by
    intro u
    by_cases h : u = t⁻¹ * xi
    · subst h
      have : (t : ZMod c) * ((t⁻¹ * xi : (ZMod c)ˣ) : ZMod c) - (xi : ZMod c) = 0 := by
        have : ((t * (t⁻¹ * xi) : (ZMod c)ˣ) : ZMod c) = (xi : ZMod c) := by
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        push_cast at this ⊢
        rw [this]
        ring
      simp
    · have hne : (t : ZMod c) * (u : ZMod c) - (xi : ZMod c) ≠ 0 := by
        intro h0
        apply h
        have h1 : ((t * u : (ZMod c)ˣ) : ZMod c) = (xi : ZMod c) := by
          push_cast
          linear_combination h0
        have h2 : t * u = xi := Units.ext h1
        calc u = t⁻¹ * (t * u) := by rw [← mul_assoc, inv_mul_cancel, one_mul]
          _ = t⁻¹ * xi := by rw [h2]
      simp [h, hne]
  rw [Finset.sum_congr rfl fun u _ => hcond u]
  rw [Finset.sum_ite_eq' Finset.univ (t⁻¹ * xi)]
  simp only [Finset.mem_univ, if_true]
  rw [mul_comm]
  congr 2
  have : ((t⁻¹ * xi)⁻¹ : (ZMod c)ˣ) = xi⁻¹ * t := by
    rw [mul_inv_rev, inv_inv]
  rw [this]
  push_cast
  ring

/-- **Exact Θ-Fourier evaluation at a non-unit frequency: it vanishes.** -/
theorem kloosterman_theta_fourier_nonunit (t : (ZMod c)ˣ) (xi : ZMod c) (hxi : ¬ IsUnit xi) :
    C.addHat (fun theta => C.kloosterman ((t : ZMod c) * theta) 1) xi = 0 := by
  classical
  unfold addHat kloosterman
  have step : ∀ theta : ZMod c,
      (∑ u : (ZMod c)ˣ, C.chi ((t : ZMod c) * theta * (u : ZMod c)
          + 1 * ((u⁻¹ : (ZMod c)ˣ) : ZMod c))) * C.chi (-(xi * theta))
      = ∑ u : (ZMod c)ˣ, C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c))
          * C.chi (theta * ((t : ZMod c) * (u : ZMod c) - xi)) := by
    intro theta
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [C.add, one_mul]
    rw [mul_comm (C.chi ((t : ZMod c) * theta * (u : ZMod c)))]
    rw [mul_assoc, ← C.add]
    congr 2
    ring
  rw [Finset.sum_congr rfl fun theta _ => step theta]
  rw [Finset.sum_comm]
  have inner : ∀ u : (ZMod c)ˣ,
      (∑ theta : ZMod c, C.chi (((u⁻¹ : (ZMod c)ˣ) : ZMod c))
        * C.chi (theta * ((t : ZMod c) * (u : ZMod c) - xi)))
      = 0 := by
    intro u
    rw [← Finset.mul_sum, C.orthogonality _]
    have hne : (t : ZMod c) * (u : ZMod c) - xi ≠ 0 := by
      intro h0
      exact hxi ⟨t * u, by push_cast; linear_combination h0⟩
    simp [hne]
  rw [Finset.sum_congr rfl fun u _ => inner u]
  simp

/-- Auxiliary: a function supported on the units may be summed over the units. -/
theorem sum_eq_sum_units {M : Type*} [AddCommMonoid M] (g : ZMod c → M)
    (hg : ∀ x : ZMod c, ¬ IsUnit x → g x = 0) :
    ∑ x : ZMod c, g x = ∑ u : (ZMod c)ˣ, g (u : ZMod c) := by
  classical
  set S : Finset (ZMod c) := Finset.univ.image (fun u : (ZMod c)ˣ => (u : ZMod c)) with hS
  have h1 : ∑ x ∈ S, g x = ∑ x : ZMod c, g x := by
    refine Finset.sum_subset (Finset.subset_univ S) ?_
    intro x _ hxS
    refine hg x ?_
    rintro ⟨u, rfl⟩
    exact hxS (Finset.mem_image.2 ⟨u, Finset.mem_univ _, rfl⟩)
  have h2 : ∑ x ∈ S, g x = ∑ u : (ZMod c)ˣ, g (u : ZMod c) := by
    rw [hS]
    refine Finset.sum_image ?_
    intro u _ v _ huv
    exact Units.ext huv
  rw [← h1, h2]

/-- **Exact Θ-side square mass of the moving Kloosterman family.**  A consequence
of Plancherel and the exact transform evaluation; still an identity, not a
bound. -/
theorem kloosterman_theta_square_mass (t : (ZMod c)ˣ) :
    ∑ theta : ZMod c, ‖C.kloosterman ((t : ZMod c) * theta) 1‖ ^ 2
      = (c : ℝ) * (Fintype.card (ZMod c)ˣ : ℝ) := by
  classical
  have hplan := C.add_plancherel (fun theta => C.kloosterman ((t : ZMod c) * theta) 1)
  have hval : ∀ xi : ZMod c,
      ‖C.addHat (fun theta => C.kloosterman ((t : ZMod c) * theta) 1) xi‖ ^ 2
        = if IsUnit xi then ((c : ℝ)) ^ 2 else 0 := by
    intro xi
    by_cases h : IsUnit xi
    · obtain ⟨v, rfl⟩ := h
      rw [C.kloosterman_theta_fourier_unit t v]
      simp [C.norm_one]
    · rw [C.kloosterman_theta_fourier_nonunit t xi h]
      simp [h]
  have hsum : ∑ xi : ZMod c,
      ‖C.addHat (fun theta => C.kloosterman ((t : ZMod c) * theta) 1) xi‖ ^ 2
      = (Fintype.card (ZMod c)ˣ : ℝ) * ((c : ℝ)) ^ 2 := by
    rw [Finset.sum_congr rfl fun xi _ => hval xi]
    rw [sum_eq_sum_units (fun xi => if IsUnit xi then ((c : ℝ)) ^ 2 else 0)
      (fun x hx => by simp [hx])]
    simp [Finset.card_univ]
  rw [hsum] at hplan
  have hcne : (c : ℝ) ≠ 0 := by
    have : c ≠ 0 := NeZero.ne c
    exact_mod_cast this
  field_simp at hplan ⊢
  linarith [hplan]

/-- **Counterguard C.**  The additive Θ-Fourier transform is a coordinate change:
it preserves total mass exactly (up to the fixed factor `c`) and therefore
cannot by itself be a contraction. -/
theorem thetaFourier_is_coordinate_change (f : ZMod c → ℂ) :
    ∑ xi : ZMod c, ‖C.addHat f xi‖ ^ 2 = (c : ℝ) * ∑ theta : ZMod c, ‖f theta‖ ^ 2 :=
  C.add_plancherel f

end AdditiveCharacterSystem

end Gate1B.SafeAlgebra
