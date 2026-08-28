import Mathlib.Tactic
import Mathlib.Algebra.Order.Chebyshev
import RequestProject.CurrentProgramme.EndpointMixedAddMult

/-!
# Phase D · collision parametrisation and the finite `L²` collision bound

## Contents

* `gcd_decomposition` — the exact `ρ = (r,s)`, `r = ρr₀`, `s = ρs₀`,
  `(r₀,s₀) = 1` decomposition;
* `collision_param` and `collision_param_converse` — the **exact** kernel-checked
  parametrisation of a collision `m₁'s − m₁r = m₂'s − m₂r` by a single integer
  shift `t`:  `m₁ − m₂ = s₀t`, `m₁' − m₂' = r₀t`;
* `norm_sq_sum_le_card_mul` and `sum_sq_collision_le` — the finite Cauchy /
  collision inequality, whose multiplicity factor is the **actual** maximal
  fibre cardinality of the finite model.  No `1 + ρ` is written;
* `collision_fibre_card_le_interval` — the *interval* capacity count: in a box
  model `Pm = Icc a b`, a nonempty fibre has at most
  `((b − m₀)/s₀ − (a − m₀)/s₀ + 1)` elements, an exact consequence of the
  interval model and of the `t`-parametrisation;
* `MixedGcdMomentInput` — the **uninhabited** arithmetic/source interface that
  would be needed to turn the resulting gcd factor into a polylog /
  subpolynomial cost.  It is *not* inhabited, and no `X^{o(1)}` is encoded.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Collision

open Finset

/-! ## 1. gcd decomposition -/

/-- Exact `gcd` decomposition of a pair `(r, s)` with `r ≠ 0`. -/
theorem gcd_decomposition (r s : ℤ) (hr : r ≠ 0) :
    ∃ rho r0 s0 : ℤ, 0 < rho ∧ r = rho * r0 ∧ s = rho * s0 ∧ IsCoprime r0 s0 := by
  have hg : 0 < (Int.gcd r s : ℤ) := by
    have : 0 < Int.gcd r s := Int.gcd_pos_of_ne_zero_left s hr
    exact_mod_cast this
  refine ⟨(Int.gcd r s : ℤ), r / (Int.gcd r s : ℤ), s / (Int.gcd r s : ℤ), hg, ?_, ?_, ?_⟩
  · rw [Int.mul_ediv_cancel' (Int.gcd_dvd_left r s)]
  · rw [Int.mul_ediv_cancel' (Int.gcd_dvd_right r s)]
  · rw [Int.isCoprime_iff_gcd_eq_one]
    exact Int.gcd_div_gcd_div_gcd (by exact_mod_cast hg)

/-! ## 2. Exact collision parametrisation -/

/-- **Collision parametrisation (forward).**  If two `(m, m')`-pairs give the
same value of the mixed index, then they differ by a single integer shift `t`
along `(s₀, r₀)`. -/
theorem collision_param {rho r0 s0 : ℤ} (hrho : rho ≠ 0) (hs0 : s0 ≠ 0)
    (hcop : IsCoprime r0 s0) {m₁ m₂ m₁' m₂' : ℤ}
    (h : m₁' * (rho * s0) - m₁ * (rho * r0)
          = m₂' * (rho * s0) - m₂ * (rho * r0)) :
    ∃ t : ℤ, m₁ - m₂ = s0 * t ∧ m₁' - m₂' = r0 * t := by
  have h1 : ((m₁' - m₂') * s0) * rho = ((m₁ - m₂) * r0) * rho := by ring_nf; ring_nf at h; linarith
  have h2 : (m₁' - m₂') * s0 = (m₁ - m₂) * r0 := mul_right_cancel₀ hrho h1
  have hdvd0 : s0 ∣ (m₁ - m₂) * r0 := ⟨m₁' - m₂', by rw [← h2]; ring⟩
  have hdvd : s0 ∣ (m₁ - m₂) := (hcop.symm).dvd_of_dvd_mul_right hdvd0
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ht, ?_⟩
  have h3 : (m₁' - m₂') * s0 = (r0 * t) * s0 := by rw [h2, ht]; ring
  exact mul_right_cancel₀ hs0 h3

/-- **Collision parametrisation (converse).**  Every integer shift `t` along
`(s₀, r₀)` produces a collision.  No coprimality is needed. -/
theorem collision_param_converse (rho r0 s0 t : ℤ) {m₁ m₂ m₁' m₂' : ℤ}
    (h1 : m₁ - m₂ = s0 * t) (h2 : m₁' - m₂' = r0 * t) :
    m₁' * (rho * s0) - m₁ * (rho * r0)
      = m₂' * (rho * s0) - m₂ * (rho * r0) := by
  have e1 : m₁ = m₂ + s0 * t := by linarith
  have e2 : m₁' = m₂' + r0 * t := by linarith
  rw [e1, e2]; ring

/-! ## 3. The finite `L²` collision inequality -/

/-- Cauchy–Schwarz in the crude counting form: `‖∑ z‖² ≤ #s · ∑ ‖z‖²`. -/
theorem norm_sq_sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, ‖f i‖ ^ 2 := by
  have h1 : ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ := norm_sum_le _ _
  have h2 : ‖∑ i ∈ s, f i‖ ^ 2 ≤ (∑ i ∈ s, ‖f i‖) ^ 2 := by
    have hnn : (0 : ℝ) ≤ ‖∑ i ∈ s, f i‖ := norm_nonneg _
    exact pow_le_pow_left₀ hnn h1 2
  exact h2.trans sq_sum_le_card_mul_sum_sq

/-- **Finite collision `L²` inequality.**  With

  `B_ν = ∑_{p ∈ P : ν(p) = ν} X(p₁) Y(p₂)`,

one has

  `∑_ν ‖B_ν‖² ≤ K · ∑_{p ∈ P} ‖X(p₁)‖² ‖Y(p₂)‖²`,

where `K` is any bound for the **actual** fibre cardinalities of the finite
model.  No multiplicity is invented. -/
theorem sum_sq_collision_le {ι : Type*} [DecidableEq ι] (P : Finset (ι × ι))
    (v : ι × ι → ℤ) (Ns : Finset ℤ) (X Y : ι → ℂ) (K : ℝ)
    (hmaps : ∀ p ∈ P, v p ∈ Ns)
    (hK : ∀ n ∈ Ns, ((P.filter (fun p => v p = n)).card : ℝ) ≤ K) :
    ∑ n ∈ Ns, ‖∑ p ∈ P.filter (fun p => v p = n), X p.1 * Y p.2‖ ^ 2
      ≤ K * ∑ p ∈ P, ‖X p.1‖ ^ 2 * ‖Y p.2‖ ^ 2 := by
  classical
  have hstep : ∀ n ∈ Ns,
      ‖∑ p ∈ P.filter (fun p => v p = n), X p.1 * Y p.2‖ ^ 2
        ≤ K * ∑ p ∈ P.filter (fun p => v p = n), ‖X p.1‖ ^ 2 * ‖Y p.2‖ ^ 2 := by
    intro n hn
    refine (norm_sq_sum_le_card_mul _ _).trans ?_
    have hnn : (0 : ℝ) ≤ ∑ p ∈ P.filter (fun p => v p = n), ‖X p.1 * Y p.2‖ ^ 2 :=
      Finset.sum_nonneg fun p _ => by positivity
    have := mul_le_mul_of_nonneg_right (hK n hn) hnn
    refine this.trans_eq ?_
    congr 1
    exact Finset.sum_congr rfl fun p _ => by rw [norm_mul, mul_pow]
  have hsum := Finset.sum_le_sum hstep
  refine hsum.trans_eq ?_
  rw [← Finset.mul_sum]
  congr 1
  exact Finset.sum_fiberwise_of_maps_to hmaps _

/-- **Product form.**  On a full product box the right-hand side factorises
exactly. -/
theorem sum_sq_product_factor {ι : Type*} [DecidableEq ι] (A B : Finset ι)
    (X Y : ι → ℂ) :
    ∑ p ∈ A ×ˢ B, ‖X p.1‖ ^ 2 * ‖Y p.2‖ ^ 2
      = (∑ m ∈ A, ‖X m‖ ^ 2) * (∑ m' ∈ B, ‖Y m'‖ ^ 2) := by
  rw [Finset.sum_product, Finset.sum_mul_sum]

/-! ## 4. Interval capacity for the collision multiplicity -/

/-- **Interval capacity.**  In the interval box model `Pm = Icc a b`, the set of
first coordinates of a collision fibre through a base point `m₀` is contained in
the `s₀`-progression through `m₀`, and therefore has at most
`(b − m₀)/s₀ − (a − m₀)/s₀ + 1` elements.

This is the *actual* finite-interval count; it is deliberately **not** written
as `1 + ρ`. -/
theorem collision_fibre_card_le_interval (a b m₀ s0 : ℤ) (hs0 : 0 < s0)
    (hab : a ≤ b) :
    (((Finset.Icc a b).filter (fun m => s0 ∣ (m - m₀))).card : ℤ)
      ≤ (b - m₀) / s0 - (a - m₀) / s0 + 1 := by
  classical
  set T : Finset ℤ := Finset.Icc ((a - m₀) / s0) ((b - m₀) / s0) with hT
  have hle : (a - m₀) / s0 ≤ (b - m₀) / s0 := Int.ediv_le_ediv hs0 (by linarith)
  have hmapsto : Set.MapsTo (fun m => (m - m₀) / s0)
      ↑((Finset.Icc a b).filter (fun m => s0 ∣ (m - m₀))) ↑T := by
    intro m hm
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Icc] at hm
    obtain ⟨⟨ha, hb⟩, -⟩ := hm
    simp only [hT, Finset.coe_Icc, Set.mem_Icc]
    exact ⟨Int.ediv_le_ediv hs0 (by linarith), Int.ediv_le_ediv hs0 (by linarith)⟩
  have hinj : Set.InjOn (fun m => (m - m₀) / s0)
      ↑((Finset.Icc a b).filter (fun m => s0 ∣ (m - m₀))) := by
    intro m₁ h₁ m₂ h₂ h
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at h₁ h₂
    obtain ⟨t₁, ht₁⟩ := h₁.2
    obtain ⟨t₂, ht₂⟩ := h₂.2
    have e₁ : (m₁ - m₀) / s0 = t₁ := by rw [ht₁, Int.mul_ediv_cancel_left _ hs0.ne']
    have e₂ : (m₂ - m₀) / s0 = t₂ := by rw [ht₂, Int.mul_ediv_cancel_left _ hs0.ne']
    simp only [] at h
    rw [e₁, e₂] at h
    have : m₁ - m₀ = m₂ - m₀ := by rw [ht₁, ht₂, h]
    linarith
  have hcard := Finset.card_le_card_of_injOn _ hmapsto hinj
  have hTcard : (T.card : ℤ) = (b - m₀) / s0 - (a - m₀) / s0 + 1 := by
    rw [hT, Int.card_Icc_of_le _ _ (by linarith)]
    ring
  calc ((((Finset.Icc a b).filter (fun m => s0 ∣ (m - m₀))).card : ℤ))
      ≤ (T.card : ℤ) := by exact_mod_cast hcard
    _ = (b - m₀) / s0 - (a - m₀) / s0 + 1 := hTcard

/-! ## 4b. The mixed coefficient `L²` bank -/

/-- The mixed coefficient is a genuine rank-one pair sum: the `Z`-factors
separate, `Z(mr,ℓ,k)` depending only on `m` and `Z(m's,ℓ,k)` only on `m'`. -/
theorem bMix_eq_pair_sum (Pm : Finset ℤ) (α : ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ)
    (l : ℕ) (k r s v : ℤ) :
    MixedAddMult.bMix Pm α Z l k r s v
      = ∑ p ∈ (Pm ×ˢ Pm).filter (fun p => MixedAddMult.nu p.1 p.2 r s = v),
          (α p.1 * Z (p.1 * r) l k) *
            (starRingEnd ℂ) (α p.2 * Z (p.2 * s) l k) := by
  classical
  rw [MixedAddMult.bMix]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [map_mul]
  ring

/-- **`ENDPOINT-MIXED-COEFF-L2-45` (finite form).**  The exact finite `L²`
collision bound for the mixed coefficient, with the multiplicity factor `K`
being any bound for the *actual* fibre cardinalities of the finite model.

Nothing subpolynomial is asserted: `K` is an explicit hypothesis. -/
theorem sum_sq_bMix_le (Pm : Finset ℤ) (α : ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ)
    (l : ℕ) (k r s : ℤ) (Ns : Finset ℤ) (K : ℝ)
    (hmaps : ∀ p ∈ Pm ×ˢ Pm, MixedAddMult.nu p.1 p.2 r s ∈ Ns)
    (hK : ∀ n ∈ Ns,
      (((Pm ×ˢ Pm).filter (fun p => MixedAddMult.nu p.1 p.2 r s = n)).card : ℝ) ≤ K) :
    ∑ v ∈ Ns, ‖MixedAddMult.bMix Pm α Z l k r s v‖ ^ 2
      ≤ K * ((∑ m ∈ Pm, ‖α m * Z (m * r) l k‖ ^ 2) *
              (∑ m' ∈ Pm, ‖α m' * Z (m' * s) l k‖ ^ 2)) := by
  classical
  have hrw : ∑ v ∈ Ns, ‖MixedAddMult.bMix Pm α Z l k r s v‖ ^ 2
      = ∑ v ∈ Ns,
          ‖∑ p ∈ (Pm ×ˢ Pm).filter (fun p => MixedAddMult.nu p.1 p.2 r s = v),
            (α p.1 * Z (p.1 * r) l k) *
              (starRingEnd ℂ) (α p.2 * Z (p.2 * s) l k)‖ ^ 2 :=
    Finset.sum_congr rfl fun v _ => by rw [bMix_eq_pair_sum]
  rw [hrw]
  refine (sum_sq_collision_le (Pm ×ˢ Pm) (fun p => MixedAddMult.nu p.1 p.2 r s) Ns
    (fun m => α m * Z (m * r) l k)
    (fun m' => (starRingEnd ℂ) (α m' * Z (m' * s) l k)) K hmaps hK).trans ?_
  have hfac : ∑ p ∈ Pm ×ˢ Pm, ‖α p.1 * Z (p.1 * r) l k‖ ^ 2 *
        ‖(starRingEnd ℂ) (α p.2 * Z (p.2 * s) l k)‖ ^ 2
      = (∑ m ∈ Pm, ‖α m * Z (m * r) l k‖ ^ 2) *
        (∑ m' ∈ Pm, ‖α m' * Z (m' * s) l k‖ ^ 2) := by
    simp only [RCLike.norm_conj]
    rw [Finset.sum_product, Finset.sum_mul_sum]
  exact le_of_eq (by rw [hfac])

/-! ## 5. The gcd-moment interface (UNINHABITED) -/

/-- **UNINHABITED ARITHMETIC / SOURCE INTERFACE.**

  `MixedGcdMomentInput : SOURCE_OPEN.`

Turning the collision multiplicity's gcd factor into a polylog or
subpolynomial cost requires a divisor-moment estimate that this repository does
**not** contain.  The interface records exactly the quantity that would have to
be supplied.  It is a bare structure: no inhabitant is constructed anywhere, and
no `X^{o(1)}` is encoded. -/
structure MixedGcdMomentInput where
  /-- The scale. -/
  Xscale : ℝ
  /-- The `(r,s)`-support over which the gcd moment is taken. -/
  support : Finset (ℤ × ℤ)
  /-- The weight attached to each `(r,s)`. -/
  weight : ℤ × ℤ → ℝ
  /-- The claimed moment bound level. -/
  level : ℝ
  /-- Nonnegativity of the weights (part of the obligation). -/
  weight_nonneg : ∀ p ∈ support, 0 ≤ weight p
  /-- The literal gcd-moment estimate.  NOT PROVED HERE. -/
  moment : ∑ p ∈ support, weight p * (Int.gcd p.1 p.2 : ℝ) ≤ level

/-- **Firewall.**  A `MixedGcdMomentInput` is not automatic: supplied data with
a level below the actual value cannot be realised. -/
theorem mixedGcdMoment_not_automatic :
    ¬ ∃ I : MixedGcdMomentInput,
        I.support = {(2, 2)} ∧ I.weight = (fun _ => 1) ∧ I.level = 0 := by
  rintro ⟨I, hs, hw, hl⟩
  have := I.moment
  rw [hs, hw, hl] at this
  norm_num [Int.gcd] at this

end Collision
end CurrentProgramme
end TwinPrimeProject
