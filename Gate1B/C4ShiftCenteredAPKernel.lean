import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.C4ShiftLeafwiseOneMinor

/-!
# Gate 1B · C4Shift centered AP kernel, physical 2+2 shift and the Bézout frontier

**Append-only.**  This module adds only *exact* finite algebra, modular
arithmetic and finite Fourier identities on top of
`Gate1B.C4ShiftLeafwiseOneMinor`.  Nothing in the previous layers is edited, and
**no analytic estimate is proved**: the analytic content stays in an
**uninhabited** source socket.

## Contents

* **§1** the exact one-minor AP phase identity, in *centered* form
  `K/2·(A₁−A₂) + h/2·(A₁+A₂+4(us)⁻¹) = k₁(A₁−A₀) − k₂(A₂−A₀)`
  with `A₀ = −2(us)⁻¹`, and the unit characterisation of `A₀`.
* **§2** the full `(h,K)` (equivalently `(k₁,k₂)`) orthogonality:
  `R_full = 1_{A₁≡A₀} · 1_{A₂≡A₀}`.
* **§3** the sampled double-major operators `M±_{ℓ,ξ}` and the exact
  factorisation `R_MM = M⁺_{ℓ,ξ₁}(A₁−A₀) · M⁻_{ℓ,ξ₂}(A₂−A₀)`, together with
  the centering identity `R_1m = R_full − R_MM`.
* **§4** the owner decomposition `R_1m = m⁺M⁻ + M⁺m⁻ + m⁺m⁻` with
  `m± = APδ± − M±`.  **No analytic bound.**
* **§5** the discrete major-projector aliasing identity for a finite Fourier
  model of `M₄`.  No decay and no total major-arc measure is formalised.
* **§6** the `ℓ`-state-count firewall (restated): **no automatic `1/ℓ²`
  saving**.
* **§7** the physical `2+2` shifted source `A_i = X_i Z_i`,
  `X₂Z₂ − X₁Z₁ = ℓ r`, `r ≠ 0`, `g = s r + h₂ − h₁`.
* **§8** the Bézout normal form `d₀ ∣ r`, `r = d₀ r₀`, `bZ₂ − aZ₁ = ℓ₀ r₀`.
* **§9** the Bézout solution line `Z₁ = Z₁⁰ + b t`, `Z₂ = Z₂⁰ + a t`, its
  converse, and an exact finite cardinality bound for `t` in a box.
  **No square-root cancellation along `t` is claimed.**
* **§10** the nonzero-shift firewall: `r ≠ 0` excludes the *true* product
  diagonal `A₁ = A₂`, which is **not** the congruence `A₁ ≡ A₂ (mod ℓ)`.
* **§12** `C4ShiftOffdiagCenteredAP58GramInput` — **UNINHABITED** analytic
  socket, with only a trivial conditional consumer.

The `5/8` scaling (`Y⁴`, `ℓ ≍ Y^{5/2}`, `T = Y⁴/ℓ ≍ Y^{3/2}`, required norm
`T^{1/2}L^C` versus the current coefficient-blind `T L^{C₀}`) is **research
metadata only** and is deliberately not formalised as a real-power claim.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace C4ShiftCenteredAP

open Finset FiniteLiftLocalTwist C4ShiftQFourier

/-! ## §1.  The exact centered one-minor AP phase identity -/

/-- **Centered AP phase identity.**  On the odd clean `ℓ`-sector, with
`h = k₁ − k₂`, `K = k₁ + k₂`, `v` an inverse of `2`, `w = (us)⁻¹` and
`A₀ = −2w`,

`v·K·(A₁ − A₂) + v·h·(A₁ + A₂ + 4w) = k₁(A₁ − A₀) − k₂(A₂ − A₀)`

as an identity in `ZMod ℓ`.  Pure algebra; no analytic input. -/
theorem centered_ap_phase_identity (l : ℕ) (v k1 k2 A1 A2 w A0 : ZMod l)
    (hv : v * 2 = 1) (hA0 : A0 = -(2 * w)) :
    v * (k1 + k2) * (A1 - A2) + v * (k1 - k2) * (A1 + A2 + 4 * w)
      = k1 * (A1 - A0) - k2 * (A2 - A0) := by
  subst hA0
  linear_combination (k1 * A1 - k2 * A2 + 2 * k1 * w - 2 * k2 * w) * hv

/-- **`A₀` is the reciprocal residue.**  If `w` is an inverse of `us` then
`A₀ = −2w` satisfies `us·A₀ = −2`. -/
theorem centered_A0_spec (l : ℕ) (us w A0 : ZMod l) (hw : us * w = 1)
    (hA0 : A0 = -(2 * w)) : us * A0 = -2 := by
  subst hA0
  linear_combination (-2 : ZMod l) * hw

/-- **Unit hypothesis collapses the target.**  If `us` is a unit and both
`us·A = −2` and `us·A₀ = −2`, then `A = A₀`. -/
theorem centered_target_of_unit (l : ℕ) (us A A0 : ZMod l) (hu : IsUnit us)
    (h1 : us * A = -2) (h2 : us * A0 = -2) : A = A0 := by
  obtain ⟨U, rfl⟩ := hu
  have h3 : (U : ZMod l) * A = (U : ZMod l) * A0 := h1.trans h2.symm
  have hinv : ((U⁻¹ : (ZMod l)ˣ) : ZMod l) * ((U : ZMod l)) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  calc A = ((U⁻¹ : (ZMod l)ˣ) : ZMod l) * ((U : ZMod l) * A) := by
        rw [← mul_assoc, hinv, one_mul]
    _ = ((U⁻¹ : (ZMod l)ˣ) : ZMod l) * ((U : ZMod l) * A0) := by rw [h3]
    _ = A0 := by rw [← mul_assoc, hinv, one_mul]

/-! ## §2.  Full `(k₁,k₂)` orthogonality -/

/-- The **full** (uncentered, unweighted) AP kernel. -/
noncomputable def Rfull (l : ℕ) (A1 A2 A0 : ℤ) : ℂ :=
  ((l : ℂ) ^ 2)⁻¹ * ∑ k1 ∈ Finset.range l, ∑ k2 ∈ Finset.range l,
    ezExp l ((k1 : ℤ) * (A1 - A0) - (k2 : ℤ) * (A2 - A0))

/-- Elementary factorisation of the two-variable phase. -/
private theorem ezExp_split (l : ℕ) (k1 k2 : ℕ) (X Y : ℤ) :
    ezExp l ((k1 : ℤ) * X - (k2 : ℤ) * Y)
      = ezExp l ((k1 : ℤ) * X) * ezExp l ((k2 : ℤ) * (-Y)) := by
  rw [← ezExp_add]
  congr 1
  ring

/-- **Full `h,K` orthogonality.**  `R_full(A₁,A₂) = 1_{A₁≡A₀} · 1_{A₂≡A₀}`.
No analytic assumption. -/
theorem Rfull_eq_indicator (l : ℕ) [NeZero l] (A1 A2 A0 : ℤ) :
    Rfull l A1 A2 A0
      = (if (l : ℤ) ∣ (A1 - A0) then (1 : ℂ) else 0) *
        (if (l : ℤ) ∣ (A2 - A0) then (1 : ℂ) else 0) := by
  classical
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hfac : ∑ k1 ∈ Finset.range l, ∑ k2 ∈ Finset.range l,
        ezExp l ((k1 : ℤ) * (A1 - A0) - (k2 : ℤ) * (A2 - A0))
      = (∑ k1 ∈ Finset.range l, ezExp l ((k1 : ℤ) * (A1 - A0))) *
        (∑ k2 ∈ Finset.range l, ezExp l ((k2 : ℤ) * (-(A2 - A0)))) := by
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun k1 _ =>
      Finset.sum_congr rfl fun k2 _ => ezExp_split l k1 k2 _ _
  have hneg : ((l : ℤ) ∣ (-(A2 - A0))) ↔ ((l : ℤ) ∣ (A2 - A0)) := dvd_neg
  unfold Rfull
  rw [hfac, sum_range_ezExp l (A1 - A0), sum_range_ezExp l (-(A2 - A0))]
  simp only [hneg]
  by_cases h1 : (l : ℤ) ∣ (A1 - A0) <;> by_cases h2 : (l : ℤ) ∣ (A2 - A0)
  · rw [if_pos h1, if_pos h2, if_pos h1, if_pos h2, sq]
    field_simp
  · rw [if_pos h1, if_neg h2, if_pos h1, if_neg h2]; ring
  · rw [if_neg h1, if_pos h2, if_neg h1, if_pos h2]; ring
  · rw [if_neg h1, if_neg h2, if_neg h1, if_neg h2]; ring

/-- **Unit form of the target.**  Under `us·A_i ≡ −2 (mod ℓ)` for `i = 1,2` and
`us·A₀ ≡ −2` with `us` a unit, the full kernel equals `1`. -/
theorem Rfull_eq_one_of_unit (l : ℕ) [NeZero l] (A1 A2 A0 : ℤ) (us : ZMod l)
    (hu : IsUnit us) (h1 : us * (A1 : ZMod l) = -2) (h2 : us * (A2 : ZMod l) = -2)
    (h0 : us * (A0 : ZMod l) = -2) : Rfull l A1 A2 A0 = 1 := by
  have e1 : ((A1 : ZMod l)) = ((A0 : ZMod l)) := centered_target_of_unit l us _ _ hu h1 h0
  have e2 : ((A2 : ZMod l)) = ((A0 : ZMod l)) := centered_target_of_unit l us _ _ hu h2 h0
  have d1 : (l : ℤ) ∣ (A1 - A0) := by
    have := sub_eq_zero.2 e1
    rwa [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  have d2 : (l : ℤ) ∣ (A2 - A0) := by
    have := sub_eq_zero.2 e2
    rwa [← Int.cast_sub, ZMod.intCast_zmod_eq_zero_iff_dvd] at this
  rw [Rfull_eq_indicator, if_pos d1, if_pos d2, mul_one]

/-! ## §3.  Sampled double-major operators and the centered kernel -/

/-- The sampled **plus** major operator
`M⁺_{ℓ,ξ}(n) = ℓ⁻¹ ∑_{k mod ℓ} M₄((ξ−k)/ℓ) e_ℓ(kn)`. -/
noncomputable def Mplus (M4 : ℝ → ℂ) (l : ℕ) (xi : ℝ) (n : ℤ) : ℂ :=
  ((l : ℂ))⁻¹ * ∑ k ∈ Finset.range l, M4 ((xi - (k : ℝ)) / (l : ℝ)) * ezExp l ((k : ℤ) * n)

/-- The sampled **minus** major operator
`M⁻_{ℓ,ξ}(n) = ℓ⁻¹ ∑_{k mod ℓ} M₄((ξ−k)/ℓ) e_ℓ(−kn)`. -/
noncomputable def Mminus (M4 : ℝ → ℂ) (l : ℕ) (xi : ℝ) (n : ℤ) : ℂ :=
  ((l : ℂ))⁻¹ * ∑ k ∈ Finset.range l, M4 ((xi - (k : ℝ)) / (l : ℝ)) * ezExp l (-((k : ℤ) * n))

/-- The **double-major** sampled kernel. -/
noncomputable def RMM (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) : ℂ :=
  ((l : ℂ) ^ 2)⁻¹ * ∑ k1 ∈ Finset.range l, ∑ k2 ∈ Finset.range l,
    (M4 ((xi1 - (k1 : ℝ)) / (l : ℝ)) * M4 ((xi2 - (k2 : ℝ)) / (l : ℝ))) *
      ezExp l ((k1 : ℤ) * (A1 - A0) - (k2 : ℤ) * (A2 - A0))

/-- The **one-minor** (centered) kernel
`R_1m = ℓ⁻² ∑_{k₁,k₂} (1 − M₄(ω₁)M₄(ω₂)) e_ℓ(Φ)`. -/
noncomputable def R1m (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) : ℂ :=
  ((l : ℂ) ^ 2)⁻¹ * ∑ k1 ∈ Finset.range l, ∑ k2 ∈ Finset.range l,
    (1 - M4 ((xi1 - (k1 : ℝ)) / (l : ℝ)) * M4 ((xi2 - (k2 : ℝ)) / (l : ℝ))) *
      ezExp l ((k1 : ℤ) * (A1 - A0) - (k2 : ℤ) * (A2 - A0))

/-- **Exact factorisation of the double-major kernel.** -/
theorem RMM_factor (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) :
    RMM M4 l xi1 xi2 A1 A2 A0
      = Mplus M4 l xi1 (A1 - A0) * Mminus M4 l xi2 (A2 - A0) := by
  unfold RMM Mplus Mminus
  rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  congr 1
  · rw [← mul_inv, ← sq]
  · refine Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => ?_
    rw [ezExp_split l k1 k2]
    rw [show (-((k2 : ℤ) * (A2 - A0))) = (k2 : ℤ) * (-(A2 - A0)) by ring]
    ring

/-- **Exact centering identity.**  `R_1m = R_full − R_MM`. -/
theorem R1m_centered (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) :
    R1m M4 l xi1 xi2 A1 A2 A0 = Rfull l A1 A2 A0 - RMM M4 l xi1 xi2 A1 A2 A0 := by
  unfold R1m Rfull RMM
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k1 _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun k2 _ => by ring

/-! ## §4.  Owner decomposition -/

/-- The sampled AP delta in the `+` direction: `APδ⁺(n) = ℓ⁻¹ ∑_k e_ℓ(kn)`. -/
noncomputable def APdeltaPlus (l : ℕ) (n : ℤ) : ℂ :=
  ((l : ℂ))⁻¹ * ∑ k ∈ Finset.range l, ezExp l ((k : ℤ) * n)

/-- The sampled AP delta in the `−` direction. -/
noncomputable def APdeltaMinus (l : ℕ) (n : ℤ) : ℂ :=
  ((l : ℂ))⁻¹ * ∑ k ∈ Finset.range l, ezExp l (-((k : ℤ) * n))

/-- The complementary (minor) sampled operator `m⁺ = APδ⁺ − M⁺`. -/
noncomputable def mplus (M4 : ℝ → ℂ) (l : ℕ) (xi : ℝ) (n : ℤ) : ℂ :=
  APdeltaPlus l n - Mplus M4 l xi n

/-- The complementary (minor) sampled operator `m⁻ = APδ⁻ − M⁻`. -/
noncomputable def mminus (M4 : ℝ → ℂ) (l : ℕ) (xi : ℝ) (n : ℤ) : ℂ :=
  APdeltaMinus l n - Mminus M4 l xi n

/-- The full kernel factors through the two sampled AP deltas. -/
theorem Rfull_factor (l : ℕ) (A1 A2 A0 : ℤ) :
    Rfull l A1 A2 A0 = APdeltaPlus l (A1 - A0) * APdeltaMinus l (A2 - A0) := by
  unfold Rfull APdeltaPlus APdeltaMinus
  rw [mul_mul_mul_comm, Finset.sum_mul_sum]
  congr 1
  · rw [← mul_inv, ← sq]
  · refine Finset.sum_congr rfl fun k1 _ => Finset.sum_congr rfl fun k2 _ => ?_
    rw [ezExp_split l k1 k2]
    rw [show (-((k2 : ℤ) * (A2 - A0))) = (k2 : ℤ) * (-(A2 - A0)) by ring]

/-- **Owner decomposition of the centered kernel.**

`R_1m = m⁺M⁻ + M⁺m⁻ + m⁺m⁻`,

with the three exact owners `mM`, `Mm`, `mm`.  Purely algebraic: no analytic
bound whatsoever is attached to any owner. -/
theorem R1m_owner_decomposition (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) :
    R1m M4 l xi1 xi2 A1 A2 A0
      = mplus M4 l xi1 (A1 - A0) * Mminus M4 l xi2 (A2 - A0)
        + Mplus M4 l xi1 (A1 - A0) * mminus M4 l xi2 (A2 - A0)
        + mplus M4 l xi1 (A1 - A0) * mminus M4 l xi2 (A2 - A0) := by
  rw [R1m_centered, Rfull_factor, RMM_factor]
  unfold mplus mminus
  ring

/-- The `mM` owner. -/
noncomputable def ownerMm (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) : ℂ :=
  mplus M4 l xi1 (A1 - A0) * Mminus M4 l xi2 (A2 - A0)

/-- The `Mm` owner. -/
noncomputable def ownermM (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) : ℂ :=
  Mplus M4 l xi1 (A1 - A0) * mminus M4 l xi2 (A2 - A0)

/-- The `mm` owner. -/
noncomputable def ownermm (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) : ℂ :=
  mplus M4 l xi1 (A1 - A0) * mminus M4 l xi2 (A2 - A0)

/-- The owner decomposition, restated with the named owners. -/
theorem R1m_owners (M4 : ℝ → ℂ) (l : ℕ) (xi1 xi2 : ℝ) (A1 A2 A0 : ℤ) :
    R1m M4 l xi1 xi2 A1 A2 A0
      = ownerMm M4 l xi1 xi2 A1 A2 A0 + ownermM M4 l xi1 xi2 A1 A2 A0
        + ownermm M4 l xi1 xi2 A1 A2 A0 :=
  R1m_owner_decomposition M4 l xi1 xi2 A1 A2 A0

/-! ## §5.  Major-projector aliasing (finite Fourier model) -/

section Aliasing

variable (Rset : Finset ℤ) (M4hat : ℤ → ℂ)

/-- The finite Fourier model of the major projector:
`M₄(x) = ∑_{r ∈ R} M̂₄(r) e(rx)`. -/
noncomputable def M4model (x : ℝ) : ℂ := ∑ r ∈ Rset, M4hat r * eR ((r : ℝ) * x)

/-- **Discrete aliasing identity for `M⁺`.**  For the finite Fourier model,

`M⁺_{ℓ,ξ}(n) = ∑_{r ≡ n (mod ℓ)} M̂₄(r) e(rξ/ℓ)`.

Only the algebraic core is formalised; no decay and no total major-arc measure
is claimed. -/
theorem Mplus_aliasing (l : ℕ) [NeZero l] (xi : ℝ) (n : ℤ) :
    Mplus (M4model Rset M4hat) l xi n
      = ∑ r ∈ Rset, (if (l : ℤ) ∣ (n - r) then M4hat r * eR ((r : ℝ) * xi / (l : ℝ)) else 0) := by
  classical
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hlR : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  unfold Mplus M4model
  have hstep : ∀ k ∈ Finset.range l,
      (∑ r ∈ Rset, M4hat r * eR ((r : ℝ) * ((xi - (k : ℝ)) / (l : ℝ)))) * ezExp l ((k : ℤ) * n)
        = ∑ r ∈ Rset, M4hat r * eR ((r : ℝ) * xi / (l : ℝ)) * ezExp l ((k : ℤ) * (n - r)) := by
    intro k _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hsplit : (r : ℝ) * ((xi - (k : ℝ)) / (l : ℝ))
        = (r : ℝ) * xi / (l : ℝ) + (((-(r * (k : ℤ)) : ℤ) : ℝ) / (l : ℝ)) := by
      push_cast
      field_simp
      ring
    have hz : ezExp l (-(r * (k : ℤ))) * ezExp l ((k : ℤ) * n)
        = ezExp l ((k : ℤ) * (n - r)) := by
      rw [← ezExp_add]; congr 1; ring
    rw [hsplit, eR_add, ← ezExp_eq_eR]
    linear_combination (M4hat r * eR ((r : ℝ) * xi / (l : ℝ))) * hz
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, sum_range_ezExp l (n - r)]
  by_cases hd : (l : ℤ) ∣ (n - r)
  · rw [if_pos hd, if_pos hd]
    field_simp
  · rw [if_neg hd, if_neg hd]
    simp

/-- **Discrete aliasing identity for `M⁻`.** -/
theorem Mminus_aliasing (l : ℕ) [NeZero l] (xi : ℝ) (n : ℤ) :
    Mminus (M4model Rset M4hat) l xi n
      = ∑ r ∈ Rset, (if (l : ℤ) ∣ (n + r) then M4hat r * eR ((r : ℝ) * xi / (l : ℝ)) else 0) := by
  classical
  have hl : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  have hlR : (l : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne l)
  unfold Mminus M4model
  have hstep : ∀ k ∈ Finset.range l,
      (∑ r ∈ Rset, M4hat r * eR ((r : ℝ) * ((xi - (k : ℝ)) / (l : ℝ)))) * ezExp l (-((k : ℤ) * n))
        = ∑ r ∈ Rset, M4hat r * eR ((r : ℝ) * xi / (l : ℝ)) * ezExp l ((k : ℤ) * (-(n + r))) := by
    intro k _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hsplit : (r : ℝ) * ((xi - (k : ℝ)) / (l : ℝ))
        = (r : ℝ) * xi / (l : ℝ) + (((-(r * (k : ℤ)) : ℤ) : ℝ) / (l : ℝ)) := by
      push_cast
      field_simp
      ring
    have hz : ezExp l (-(r * (k : ℤ))) * ezExp l (-((k : ℤ) * n))
        = ezExp l ((k : ℤ) * (-(n + r))) := by
      rw [← ezExp_add]; congr 1; ring
    rw [hsplit, eR_add, ← ezExp_eq_eR]
    linear_combination (M4hat r * eR ((r : ℝ) * xi / (l : ℝ))) * hz
  rw [Finset.sum_congr rfl hstep, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [← Finset.mul_sum, sum_range_ezExp l (-(n + r))]
  by_cases hd : (l : ℤ) ∣ (n + r)
  · rw [if_pos ((dvd_neg).2 hd), if_pos hd]
    field_simp
  · rw [if_neg (fun hc => hd ((dvd_neg).1 hc)), if_neg hd]
    simp

end Aliasing

/-! ## §6.  The `ℓ`-state-count firewall (restated) -/

/-- **NO AUTOMATIC `1/ℓ²` SAVING.**  The `ℓ^{-2}` normalisation is exactly
consumed by the `ℓ²` states `(k₁,k₂) mod ℓ`. -/
theorem ell_state_count_no_saving (l : ℕ) (hl : l ≠ 0) :
    ((l : ℝ) ^ 2)⁻¹ * ((Finset.range l ×ˢ Finset.range l).card : ℝ) = 1 :=
  C4ShiftLeafwise.ell_normalisation_no_saving' l hl

/-! ## §7.  The physical `2+2` shifted source -/

/-- **The physical `2+2` shifted tuple source.**  `A_i = X_i Z_i` are genuine
products of the two source lines; the shift equation `X₂Z₂ − X₁Z₁ = ℓ r` with
`r ≠ 0` is the tuple-level restriction that is carried throughout.  `r = 0` is
**never** reintroduced. -/
structure Physical2Plus2Shift where
  /-- First line, `X`-coordinate. -/
  X1 : ℤ
  /-- First line, `Z`-coordinate. -/
  Z1 : ℤ
  /-- Second line, `X`-coordinate. -/
  X2 : ℤ
  /-- Second line, `Z`-coordinate. -/
  Z2 : ℤ
  /-- The AP modulus. -/
  ell : ℤ
  /-- The nonzero shift parameter. -/
  r : ℤ
  /-- The `s`-coordinate of the tuple. -/
  s : ℤ
  /-- The first `h`-coordinate. -/
  h1 : ℤ
  /-- The second `h`-coordinate. -/
  h2 : ℤ
  /-- The `g`-coordinate. -/
  g : ℤ
  /-- The exact shift equation at tuple level. -/
  shift : X2 * Z2 - X1 * Z1 = ell * r
  /-- **Tuple-level source restriction**: the shift is nonzero. -/
  rne : r ≠ 0
  /-- The banked algebraic relation defining `g`. -/
  gdef : g = s * r + h2 - h1

namespace Physical2Plus2Shift

variable (P : Physical2Plus2Shift)

/-- The first four-product `A₁ = X₁Z₁`. -/
def A1 : ℤ := P.X1 * P.Z1

/-- The second four-product `A₂ = X₂Z₂`. -/
def A2 : ℤ := P.X2 * P.Z2

/-- **Physical `2+2` shift**: `A₂ − A₁ = ℓ r`. -/
theorem shift_A : P.A2 - P.A1 = P.ell * P.r := P.shift

/-- The same identity written on the product coordinates. -/
theorem shift_product : P.X2 * P.Z2 - P.X1 * P.Z1 = P.ell * P.r := P.shift

/-- The banked `g`-relation `g = s r + h₂ − h₁`. -/
theorem g_relation : P.g = P.s * P.r + P.h2 - P.h1 := P.gdef

/-- **Congruence** `A₁ ≡ A₂ (mod ℓ)` always holds on the source. -/
theorem congruence_mod_ell : P.ell ∣ (P.A2 - P.A1) := ⟨P.r, P.shift⟩

/-- **Nonzero-shift firewall.**  Under `r ≠ 0` and `ℓ ≠ 0` the *true* product
diagonal `A₁ = A₂` cannot occur.  This is emphatically **not** the same as the
congruence `A₁ ≡ A₂ (mod ℓ)`, which does hold (`congruence_mod_ell`). -/
theorem true_diagonal_excluded (hl : P.ell ≠ 0) : P.A1 ≠ P.A2 := by
  intro h
  have : P.ell * P.r = 0 := by rw [← P.shift_A, h, sub_self]
  rcases mul_eq_zero.1 this with h0 | h0
  · exact hl h0
  · exact P.rne h0

end Physical2Plus2Shift

/-- **The distinction is load-bearing.**  A congruence `A₁ ≡ A₂ (mod ℓ)` does
not imply equality: an explicit witness. -/
theorem congruence_not_equality :
    ∃ (l A1 A2 : ℤ), l ∣ (A2 - A1) ∧ A1 ≠ A2 :=
  ⟨5, 0, 5, ⟨1, by norm_num⟩, by norm_num⟩

/-! ## §8.  Bézout normal form of the `2+2` shift -/

/-- **Bézout normal form.**  With `d = gcd(X₁,X₂)`, `X₁ = d a`, `X₂ = d b`,
`g₀ = gcd(d,ℓ)`, `d = g₀ d₀`, `ℓ = g₀ ℓ₀`, `gcd(d₀,ℓ₀) = 1`, the shift equation
`X₂Z₂ − X₁Z₁ = ℓ r` forces `d₀ ∣ r`, and, writing `r = d₀ r₀`,

`b Z₂ − a Z₁ = ℓ₀ r₀`. -/
theorem bezout_2plus2_normalform
    (X1 Z1 X2 Z2 l r d a b g0 d0 l0 : ℤ)
    (hX1 : X1 = d * a) (hX2 : X2 = d * b)
    (hd : d = g0 * d0) (hl : l = g0 * l0)
    (hg0 : g0 ≠ 0) (hd0 : d0 ≠ 0)
    (hcop : IsCoprime d0 l0)
    (hshift : X2 * Z2 - X1 * Z1 = l * r) :
    d0 ∣ r ∧ ∃ r0 : ℤ, r = d0 * r0 ∧ b * Z2 - a * Z1 = l0 * r0 := by
  have hcancel : d0 * (b * Z2 - a * Z1) = l0 * r := by
    have h : g0 * (d0 * (b * Z2 - a * Z1)) = g0 * (l0 * r) := by
      subst hX1 hX2 hd hl
      ring_nf
      ring_nf at hshift
      linarith [hshift]
    exact mul_left_cancel₀ hg0 h
  have hdvd : d0 ∣ r := hcop.dvd_of_dvd_mul_left ⟨_, hcancel.symm⟩
  obtain ⟨r0, hr0⟩ := hdvd
  refine ⟨⟨r0, hr0⟩, r0, hr0, ?_⟩
  have : d0 * (b * Z2 - a * Z1) = d0 * (l0 * r0) := by
    rw [hcancel, hr0]; ring
  exact mul_left_cancel₀ hd0 this

/-! ## §9.  The Bézout solution line -/

/-- **Forward direction.**  Every point of the Bézout line solves the equation. -/
theorem bezout_solution_line_forward (a b Z10 Z20 rhs t : ℤ)
    (h0 : b * Z20 - a * Z10 = rhs) :
    b * (Z20 + a * t) - a * (Z10 + b * t) = rhs := by
  linear_combination h0

/-- **Converse.**  For `gcd(a,b) = 1`, `a ≠ 0` and a fixed right-hand side,
*every* integer solution lies on the line `Z₁ = Z₁⁰ + b t`, `Z₂ = Z₂⁰ + a t`. -/
theorem bezout_solution_line_converse (a b Z10 Z20 Z1 Z2 rhs : ℤ)
    (hcop : IsCoprime a b) (ha : a ≠ 0)
    (h0 : b * Z20 - a * Z10 = rhs) (h : b * Z2 - a * Z1 = rhs) :
    ∃ t : ℤ, Z1 = Z10 + b * t ∧ Z2 = Z20 + a * t := by
  have hkey : b * (Z2 - Z20) = a * (Z1 - Z10) := by linear_combination h - h0
  have hdvd : a ∣ (Z2 - Z20) := hcop.dvd_of_dvd_mul_left ⟨Z1 - Z10, hkey⟩
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ?_, by linarith [ht]⟩
  have : a * (b * t) = a * (Z1 - Z10) := by
    rw [← hkey, ht]; ring
  have := mul_left_cancel₀ ha this
  linarith

/-- **Exact finite cardinality bound along the Bézout line.**  If every `t` in a
nonempty finite set `T` sends `Z₁⁰ + b t` into the box `[lo,hi]` (with `b > 0`),
then `(#T − 1)·b ≤ hi − lo`.  No cancellation along `t` is claimed — this is a
pure counting bound. -/
theorem bezout_line_card_bound (Z10 b lo hi : ℤ) (hb : 0 < b) (T : Finset ℤ)
    (hT : T.Nonempty) (hbox : ∀ t ∈ T, lo ≤ Z10 + b * t ∧ Z10 + b * t ≤ hi) :
    ((T.card : ℤ) - 1) * b ≤ hi - lo := by
  classical
  set tmin := T.min' hT with htmin
  set tmax := T.max' hT with htmax
  have hmin : tmin ∈ T := T.min'_mem hT
  have hmax : tmax ∈ T := T.max'_mem hT
  have hle : tmin ≤ tmax := T.min'_le _ hmax
  have hsub : T ⊆ Finset.Icc tmin tmax := fun x hx =>
    Finset.mem_Icc.2 ⟨T.min'_le x hx, T.le_max' x hx⟩
  have hc : T.card ≤ (Finset.Icc tmin tmax).card := Finset.card_le_card hsub
  rw [Int.card_Icc] at hc
  have hcard : (T.card : ℤ) ≤ tmax - tmin + 1 := by omega
  have h1 := (hbox tmin hmin).1
  have h2 := (hbox tmax hmax).2
  have hspan : b * (tmax - tmin) ≤ hi - lo := by linarith
  nlinarith [hcard, hspan, hb.le]

/-! ## §12.  The new analytic socket (UNINHABITED) -/

/-- **UNINHABITED analytic socket.**

`C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45`
(equivalently `C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45`).

The exact source retained by the socket:

* the **centered** AP kernel `R_1m` (never the raw `R_full`);
* the three owners `mM`, `Mm`, `mm`;
* the physical shift `X₂Z₂ − X₁Z₁ = ℓ r` with `r ≠ 0`;
* the exact Bézout parametrisation of the `Z`-line;
* the actual `α_j / γ_j` `2+2` coefficients;
* a linked top-band source predicate;
* the pushed `L¹_θ ℓ²_v` target.

It is **never constructed**. -/
structure C4ShiftOffdiagCenteredAP58GramInput where
  /-- The AP modulus. -/
  l : ℕ
  /-- The modulus is nonzero. -/
  lne : l ≠ 0
  /-- The first sampled major frequency. -/
  xi1 : ℝ
  /-- The second sampled major frequency. -/
  xi2 : ℝ
  /-- The major projector. -/
  M4 : ℝ → ℂ
  /-- The centered target residue `A₀ = −2(us)⁻¹`. -/
  A0 : ℤ
  /-- The physical `2+2` shifted source, carrying `r ≠ 0`. -/
  src : Physical2Plus2Shift
  /-- Bézout: the reduced `X`-coefficients. -/
  a : ℤ
  /-- Bézout: the reduced `X`-coefficients. -/
  b : ℤ
  /-- Bézout: the reduced modulus. -/
  l0 : ℤ
  /-- Bézout: the reduced shift. -/
  r0 : ℤ
  /-- Bézout: coprimality of the reduced `X`-coefficients. -/
  acop : IsCoprime a b
  /-- Bézout: the normal-form equation of the `Z`-line. -/
  bezout : b * src.Z2 - a * src.Z1 = l0 * r0
  /-- The actual `α_j` `2+2` coefficient. -/
  al : ℤ → ℂ
  /-- The actual `γ_j` `2+2` coefficient. -/
  ga : ℤ → ℂ
  /-- The linked top-band source predicate. -/
  topBand : Prop
  /-- The linked top-band source is supplied together with the estimate. -/
  topBandSource : topBand
  /-- Number of sample points of the discrete `θ`-grid. -/
  P : ℕ
  /-- The shift support. -/
  Vset : Finset ℤ
  /-- The `mM` owner transform. -/
  HmM : ℕ → ℤ → ℂ
  /-- The `Mm` owner transform. -/
  HMm : ℕ → ℤ → ℂ
  /-- The `mm` owner transform. -/
  Hmm : ℕ → ℤ → ℂ
  /-- The owner transforms reassemble the centered kernel against the actual
  `2+2` coefficients. -/
  owners : ∀ (k : ℕ) (v : ℤ), HmM k v + HMm k v + Hmm k v
      = R1m M4 l xi1 xi2 src.A1 src.A2 A0 * al v * ga v
  /-- The natural bound (research value `T^{1/2} L^C`). -/
  naturalBound : ℝ
  /-- **The analytic estimate itself — never proved here.** -/
  bound : (1 / (P : ℝ)) * ∑ k ∈ Finset.range P,
      Real.sqrt (∑ v ∈ Vset, ‖HmM k v + HMm k v + Hmm k v‖ ^ 2) ≤ naturalBound

/-- **Trivial conditional consumer** of the uninhabited socket.  It asserts
nothing unconditionally. -/
theorem centeredAP58_conditional_consumer (I : C4ShiftOffdiagCenteredAP58GramInput) :
    (1 / (I.P : ℝ)) * ∑ k ∈ Finset.range I.P,
        Real.sqrt (∑ v ∈ I.Vset, ‖I.HmM k v + I.HMm k v + I.Hmm k v‖ ^ 2)
      ≤ I.naturalBound :=
  I.bound

/-! ## Status metadata (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the centered AP-kernel / Bézout delta. -/
def statusRows : List LedgerEntry :=
  [ ⟨"C4SHIFT-ONE-FOURPRODUCT-MINOR45", Status.supersededAsControllingFrontier,
     "OLD CLOSURE RETRACTED (recorded permanently, unchanged)."⟩,
    ⟨"C4SHIFT-ONE-MINOR-PUSHED-ENERGY45", Status.supersededAsControllingFrontier,
     "STRICTLY REDUCED / OLD FIRST RESIDUAL SUPERSEDED. NOT false: its analyticOpen row in the previous layer is preserved."⟩,
    ⟨"C4SHIFT-1M-APKERNEL45", Status.provedAlgebraic,
     "FORMAL PASS: centered_ap_phase_identity, centered_A0_spec, centered_target_of_unit."⟩,
    ⟨"C4SHIFT-1M-CENTERED-KERNEL45", Status.provedAlgebraic,
     "FORMAL PASS: Rfull_eq_indicator, Rfull_eq_one_of_unit, RMM_factor, R1m_centered."⟩,
    ⟨"C4SHIFT-MAJORPROJECTOR-HKFOURIER45", Status.provedAlgebraic,
     "FORMAL ALGEBRAIC PASS: Mplus_aliasing, Mminus_aliasing for the finite Fourier model M4model. No decay, no total major-arc measure."⟩,
    ⟨"C4SHIFT-1M-LEAFWISE-CENTERING45", Status.provedAlgebraic,
     "FORMAL DECOMPOSITION PASS / NO ANALYTIC CLOSURE: R1m_owner_decomposition, R1m_owners (owners mM, Mm, mm)."⟩,
    ⟨"C4SHIFT-2PLUS2-PHYSICAL-SHIFT45", Status.provedAlgebraic,
     "FORMAL PASS: Physical2Plus2Shift with A_i = X_i Z_i, shift_A, shift_product, g_relation (g = s r + h2 - h1), rne : r != 0. |g| > L^B1 is NOT formalised."⟩,
    ⟨"C4SHIFT-NONZERO-SHIFT-FIREWALL45", Status.provedAlgebraic,
     "FORMAL PASS: true_diagonal_excluded (r != 0 excludes A1 = A2) together with congruence_mod_ell and congruence_not_equality. Congruence mod ell is NOT equality."⟩,
    ⟨"C4SHIFT-BEZOUT-2PLUS2-NORMALFORM45", Status.provedAlgebraic,
     "FORMAL PASS: bezout_2plus2_normalform (d0 | r, r = d0 r0, b Z2 - a Z1 = l0 r0)."⟩,
    ⟨"C4SHIFT-BEZOUT-SOLUTION-LINE45", Status.provedAlgebraic,
     "FORMAL PASS: bezout_solution_line_forward, bezout_solution_line_converse, bezout_line_card_bound. NO square-root cancellation along t is claimed."⟩,
    ⟨"C4SHIFT-ELL-STATECOUNT-FIREWALL45", Status.provedFinite,
     "NO AUTOMATIC 1/ell^2 SAVING: ell_state_count_no_saving."⟩,
    ⟨"C4SHIFT-5/8-SCALING45", Status.externallyAudited,
     "RESEARCH METADATA ONLY: four-product Y^4, ell ~ Y^(5/2), nominal level 5/8, T = Y^4/ell ~ Y^(3/2), required norm T^(1/2) L^C vs current coefficient-blind T L^C0. NOT formalised."⟩,
    ⟨"C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45", Status.analyticOpen,
     "CURRENT FIRST EXACT ANALYTIC RESIDUAL. ANALYTIC OPEN / UNINHABITED: C4ShiftOffdiagCenteredAP58GramInput. Equivalent sharper name: C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45."⟩,
    ⟨"C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45", Status.analyticOpen,
     "ALIAS of C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45. ANALYTIC OPEN / UNINHABITED."⟩,
    ⟨"TOPBAND-BROAD-MAJOR-TREE-MATCH45", Status.sourceOpen,
     "PARALLEL LOCAL RESIDUAL. SOURCE OPEN; NOT CLOSED."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen,
     "OPEN."⟩ ]

/-- No row of this delta is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

/-- The new first exact analytic residual is recorded as analytic-open. -/
theorem statusRows_first_residual :
    ∃ e ∈ statusRows, e.label = "C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45" ∧
      e.status = Status.analyticOpen := by decide

/-- The superseded row is **not** marked false. -/
theorem pushed_energy_not_false :
    ∀ e ∈ statusRows, e.label = "C4SHIFT-ONE-MINOR-PUSHED-ENERGY45" →
      e.status = Status.supersededAsControllingFrontier := by decide

end C4ShiftCenteredAP
end CurrentProgramme
end TwinPrimeProject
