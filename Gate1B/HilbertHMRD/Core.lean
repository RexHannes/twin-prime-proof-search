/-
# Gate1B / Hilbert-HMRD : the abstract finite theorem

A **finite, abstract** Hilbert-valued reciprocal packet and the two HMRD branches.

Data: a complex inner-product space `H`, finite index sets `Dset`, `Wset`, scalar weights
`α`, `β`, vectors `u_d`, `v_w ∈ H`, residue data `x_d, y_w ∈ ZMod s` for the effective
modulus `s`, and a phase `f : ZMod s → ℂ`.  The packet is

```
S_H = ∑_{d,w} α_d β_w f(x_d y_w) ⟨u_d, v_w⟩,
```

with `⟨·,·⟩` the pairing that is **linear in the first slot** (the source convention);
in Mathlib's convention this is `inner ℂ (v w) (u d)`.

Two branches, both kernel-proved:

* **small-modulus branch** (§14): if `f` is unimodular and supported on the units,
  `|S_H| ≤ √(φ(s)) · P · B₁` with `P` a bound for `‖∑_d α_d e_s(m x_d) u_d‖` uniform in the
  frequency `m`, and `B₁ = ∑_w |β_w| ‖v_w‖`;
* **energy branch** (§15): after pushing `d, w` to their inverse residue classes,
  `|S_H| ≤ √(s · c_D · c_W) · A₂ · B₂`, where `c_D, c_W` bound the residue-class
  multiplicities (for a source in an interval of length `D` one has `c_D = 1 + D/s`, by the
  banked counting lemma `Universal.D0WP.card_residue_class_le`) and `A₂² = ∑_d |α_d|²‖u_d‖²`,
  `B₂² = ∑_w |β_w|²‖v_w‖²`.

The `min` of the two branches is the finite Hilbert-HMRD statement.

Nothing here is postulated: there is no axiom, and no physical Gate1B source is involved.
The effective-modulus reduction `e_r(A u⁻¹) = e_{r♯}(A♯ u⁻¹)` is the separately banked
`Universal.D0WP.ac_effective_modulus`; here `s` already denotes the effective modulus.
-/
import Gate1B.HilbertHMRD.Fourier
import Gate1B.HilbertHMRD.OperatorStability
import Universal.D0WP.ResidueEnergy

namespace Gate1B.HilbertHMRD

open Finset

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}
variable {s : ℕ} [NeZero s]

/-! ## 1. The pairing and the packet -/

/-- The source pairing `⟨x, y⟩`, **linear in the first slot**.  In Mathlib's convention
(conjugate-linear in the first slot) this is `inner ℂ y x`. -/
def pairing (x y : H) : ℂ := inner ℂ y x

theorem norm_pairing_le (x y : H) : ‖pairing x y‖ ≤ ‖x‖ * ‖y‖ := by
  rw [pairing, mul_comm]
  exact norm_inner_le_norm _ _

/-- The Hilbert-valued reciprocal packet. -/
def packet (s : ℕ) [NeZero s] (Dset : Finset ι) (Wset : Finset κ) (al : ι → ℂ) (be : κ → ℂ)
    (u : ι → H) (v : κ → H) (xr : ι → ZMod s) (yr : κ → ZMod s) (f : ZMod s → ℂ) : ℂ :=
  ∑ d ∈ Dset, ∑ w ∈ Wset, al d * be w * f (xr d * yr w) * pairing (u d) (v w)

/-! ## 2. The small-modulus branch -/

/-- **Small-modulus branch (§14).**  For a unimodular phase supported on the units,

```
|S_H| ≤ √(φ(s)) · P · B₁.
```

The Fourier `ℓ¹` cost is exactly `√(φ(s))` in the normalisation of
`Gate1B.HilbertHMRD.fcoef`; no constant is hidden. -/
theorem packet_small_branch (Dset : Finset ι) (Wset : Finset κ) (al : ι → ℂ) (be : κ → ℂ)
    (u : ι → H) (v : κ → H) (xr : ι → ZMod s) (yr : κ → ZMod s) (f : ZMod s → ℂ)
    (hsupp : ∀ x, ¬ IsUnit x → f x = 0) (hb : ∀ x, ‖f x‖ ≤ 1) (P B1 : ℝ)
    (hP : ∀ m : ZMod s, ‖∑ d ∈ Dset, (al d * ez s (m * xr d)) • u d‖ ≤ P)
    (hB1 : ∑ w ∈ Wset, ‖be w‖ * ‖v w‖ ≤ B1) :
    ‖packet s Dset Wset al be u v xr yr f‖ ≤ Real.sqrt (Nat.totient s) * (P * B1) := by
  have hP0 : 0 ≤ P := le_trans (norm_nonneg _) (hP 0)
  have hB10 : 0 ≤ B1 := le_trans (Finset.sum_nonneg fun w _ => by positivity) hB1
  set K : ZMod s → ℂ := fun t =>
    ∑ w ∈ Wset, be w * inner ℂ (v w) (∑ d ∈ Dset, (al d * ez s ((t * yr w) * xr d)) • u d)
    with hK
  have hslice : ∀ t : ZMod s, ‖K t‖ ≤ P * B1 := by
    intro t
    have hterm : ∀ w ∈ Wset,
        ‖be w * inner ℂ (v w) (∑ d ∈ Dset, (al d * ez s ((t * yr w) * xr d)) • u d)‖
          ≤ P * (‖be w‖ * ‖v w‖) := by
      intro w _
      rw [norm_mul]
      have h1 : ‖inner ℂ (v w) (∑ d ∈ Dset, (al d * ez s ((t * yr w) * xr d)) • u d)‖
          ≤ ‖v w‖ * P :=
        le_trans (norm_inner_le_norm _ _)
          (mul_le_mul_of_nonneg_left (hP (t * yr w)) (norm_nonneg _))
      calc ‖be w‖ * ‖inner ℂ (v w) (∑ d ∈ Dset, (al d * ez s ((t * yr w) * xr d)) • u d)‖
          ≤ ‖be w‖ * (‖v w‖ * P) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
        _ = P * (‖be w‖ * ‖v w‖) := by ring
    calc ‖K t‖ ≤ ∑ w ∈ Wset,
          ‖be w * inner ℂ (v w) (∑ d ∈ Dset, (al d * ez s ((t * yr w) * xr d)) • u d)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ w ∈ Wset, P * (‖be w‖ * ‖v w‖) := Finset.sum_le_sum hterm
      _ = P * ∑ w ∈ Wset, ‖be w‖ * ‖v w‖ := by rw [Finset.mul_sum]
      _ ≤ P * B1 := mul_le_mul_of_nonneg_left hB1 hP0
  have hexpand : packet s Dset Wset al be u v xr yr f = ∑ t : ZMod s, fcoef s f t * K t := by
    have hpt : ∀ d ∈ Dset, ∀ w ∈ Wset,
        al d * be w * f (xr d * yr w) * pairing (u d) (v w)
          = ∑ t : ZMod s, fcoef s f t
              * (be w * inner ℂ (v w) ((al d * ez s ((t * yr w) * xr d)) • u d)) := by
      intro d _ w _
      rw [← fourier_inversion f (xr d * yr w), Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [inner_smul_right, pairing, show (t * yr w) * xr d = t * (xr d * yr w) by ring]
      ring
    calc packet s Dset Wset al be u v xr yr f
        = ∑ d ∈ Dset, ∑ w ∈ Wset, ∑ t : ZMod s, fcoef s f t
              * (be w * inner ℂ (v w) ((al d * ez s ((t * yr w) * xr d)) • u d)) := by
          rw [packet]
          exact Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun w hw => hpt d hd w hw
      _ = ∑ w ∈ Wset, ∑ d ∈ Dset, ∑ t : ZMod s, fcoef s f t
              * (be w * inner ℂ (v w) ((al d * ez s ((t * yr w) * xr d)) • u d)) :=
          Finset.sum_comm
      _ = ∑ w ∈ Wset, ∑ t : ZMod s, ∑ d ∈ Dset, fcoef s f t
              * (be w * inner ℂ (v w) ((al d * ez s ((t * yr w) * xr d)) • u d)) :=
          Finset.sum_congr rfl fun w _ => Finset.sum_comm
      _ = ∑ t : ZMod s, ∑ w ∈ Wset, ∑ d ∈ Dset, fcoef s f t
              * (be w * inner ℂ (v w) ((al d * ez s ((t * yr w) * xr d)) • u d)) :=
          Finset.sum_comm
      _ = ∑ t : ZMod s, fcoef s f t * K t := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hK, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [inner_sum, Finset.mul_sum, Finset.mul_sum]
  calc ‖packet s Dset Wset al be u v xr yr f‖ = ‖∑ t : ZMod s, fcoef s f t * K t‖ := by
        rw [hexpand]
    _ ≤ ∑ t : ZMod s, ‖fcoef s f t * K t‖ := norm_sum_le _ _
    _ = ∑ t : ZMod s, ‖fcoef s f t‖ * ‖K t‖ := by
        exact Finset.sum_congr rfl fun t _ => norm_mul _ _
    _ ≤ ∑ t : ZMod s, ‖fcoef s f t‖ * (P * B1) :=
        Finset.sum_le_sum fun t _ =>
          mul_le_mul_of_nonneg_left (hslice t) (norm_nonneg _)
    _ = (∑ t : ZMod s, ‖fcoef s f t‖) * (P * B1) := by rw [Finset.sum_mul]
    _ ≤ Real.sqrt (Nat.totient s) * (P * B1) :=
        mul_le_mul_of_nonneg_right (fcoef_l1_le_sqrt_totient f hsupp hb) (mul_nonneg hP0 hB10)

/-! ## 3. Hilbert-valued residue-class energy -/

/-- **Hilbert-valued fibre energy.**  If every residue fibre of `cls` inside `S` has at most
`B` elements, then pushing the weighted vectors forward to residue classes costs at most the
factor `B` in `ℓ²`. -/
theorem fiber_energy_le_hilbert {ζ : Type*} [DecidableEq ζ] [Fintype ζ]
    (S : Finset ι) (cls : ι → ζ) (al : ι → ℂ) (X : ι → H) (B : ℝ)
    (hB : ∀ z : ζ, ((S.filter (fun d => cls d = z)).card : ℝ) ≤ B) :
    ∑ z : ζ, ‖∑ d ∈ S.filter (fun d => cls d = z), al d • X d‖ ^ 2
      ≤ B * ∑ d ∈ S, ‖al d‖ ^ 2 * ‖X d‖ ^ 2 := by
  have per : ∀ z : ζ, ‖∑ d ∈ S.filter (fun d => cls d = z), al d • X d‖ ^ 2
      ≤ B * ∑ d ∈ S.filter (fun d => cls d = z), ‖al d‖ ^ 2 * ‖X d‖ ^ 2 := by
    intro z
    set F := S.filter (fun d => cls d = z) with hF
    have h1 : ‖∑ d ∈ F, al d • X d‖ ≤ ∑ d ∈ F, ‖al d‖ * ‖X d‖ := by
      refine le_trans (norm_sum_le _ _) (le_of_eq ?_)
      exact Finset.sum_congr rfl fun d _ => norm_smul _ _
    have h2 : (∑ d ∈ F, ‖al d‖ * ‖X d‖) ^ 2
        ≤ (F.card : ℝ) * ∑ d ∈ F, (‖al d‖ * ‖X d‖) ^ 2 := sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ d ∈ F, al d • X d‖ ^ 2 ≤ (∑ d ∈ F, ‖al d‖ * ‖X d‖) ^ 2 := by
      nlinarith [norm_nonneg (∑ d ∈ F, al d • X d),
        Finset.sum_nonneg (fun d (_ : d ∈ F) => mul_nonneg (norm_nonneg (al d))
          (norm_nonneg (X d)))]
    have h4 : (F.card : ℝ) * ∑ d ∈ F, (‖al d‖ * ‖X d‖) ^ 2
        ≤ B * ∑ d ∈ F, ‖al d‖ ^ 2 * ‖X d‖ ^ 2 := by
      have hrw : ∑ d ∈ F, (‖al d‖ * ‖X d‖) ^ 2 = ∑ d ∈ F, ‖al d‖ ^ 2 * ‖X d‖ ^ 2 :=
        Finset.sum_congr rfl fun d _ => by ring
      rw [hrw]
      exact mul_le_mul_of_nonneg_right (hB z)
        (Finset.sum_nonneg fun d _ => by positivity)
    linarith [h3.trans (h2.trans h4)]
  calc ∑ z : ζ, ‖∑ d ∈ S.filter (fun d => cls d = z), al d • X d‖ ^ 2
      ≤ ∑ z : ζ, B * ∑ d ∈ S.filter (fun d => cls d = z), ‖al d‖ ^ 2 * ‖X d‖ ^ 2 :=
        Finset.sum_le_sum fun z _ => per z
    _ = B * ∑ z : ζ, ∑ d ∈ S.filter (fun d => cls d = z), ‖al d‖ ^ 2 * ‖X d‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = B * ∑ d ∈ S, ‖al d‖ ^ 2 * ‖X d‖ ^ 2 := by
        rw [Finset.sum_fiberwise S cls fun d => ‖al d‖ ^ 2 * ‖X d‖ ^ 2]

/-! ## 4. The reciprocal Fourier kernel and its `√s` bilinear bound -/

/-- Orthogonality of the kernel `K(p,q) = e_s(A p q)` in `p`. -/
theorem ez_kernel_orth (A q q' : ZMod s) :
    ∑ p : ZMod s, ez s (A * (p * q)) * (starRingEnd ℂ) (ez s (A * (p * q')))
      = if A * (q - q') = 0 then (s : ℂ) else 0 := by
  have hterm : ∀ p : ZMod s,
      ez s (A * (p * q)) * (starRingEnd ℂ) (ez s (A * (p * q'))) = ez s ((A * (q - q')) * p) := by
    intro p
    rw [ez_conj, ← ez_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun p _ => hterm p, sum_ez_orth]

/-- The scalar `ℓ²` bound for the conjugated reciprocal kernel, with constant `√s`. -/
theorem scalar_kernel_bound (A : ZMod s) (hA : IsUnit A) :
    ScalarL2Bound (fun p q : ZMod s => (starRingEnd ℂ) (ez s (A * (p * q)))) (Real.sqrt s) := by
  intro Y
  have hc : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj']
    push_cast
    ring
  set G : ZMod s → ℂ := fun p => ∑ q : ZMod s, (starRingEnd ℂ) (ez s (A * (p * q))) * Y q with hG
  have hmain : ∑ p : ZMod s, G p * (starRingEnd ℂ) (G p)
      = (s : ℂ) * ∑ q : ZMod s, Y q * (starRingEnd ℂ) (Y q) := by
    have e1 : ∀ p : ZMod s, G p * (starRingEnd ℂ) (G p)
        = ∑ q : ZMod s, ∑ q' : ZMod s,
            ((starRingEnd ℂ) (ez s (A * (p * q))) * ez s (A * (p * q')))
              * (Y q * (starRingEnd ℂ) (Y q')) := by
      intro p
      rw [hG]
      simp only [map_sum, map_mul, Complex.conj_conj]
      rw [Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring
    rw [Finset.sum_congr rfl fun p _ => e1 p, Finset.sum_comm]
    have step : ∀ q : ZMod s, ∑ p : ZMod s, ∑ q' : ZMod s,
        ((starRingEnd ℂ) (ez s (A * (p * q))) * ez s (A * (p * q')))
          * (Y q * (starRingEnd ℂ) (Y q'))
        = (s : ℂ) * (Y q * (starRingEnd ℂ) (Y q)) := by
      intro q
      rw [Finset.sum_comm]
      have inner' : ∀ q' : ZMod s, ∑ p : ZMod s,
          ((starRingEnd ℂ) (ez s (A * (p * q))) * ez s (A * (p * q')))
            * (Y q * (starRingEnd ℂ) (Y q'))
          = (if q' = q then (s : ℂ) else 0) * (Y q * (starRingEnd ℂ) (Y q')) := by
        intro q'
        rw [← Finset.sum_mul]
        congr 1
        have hrw : ∀ p : ZMod s,
            (starRingEnd ℂ) (ez s (A * (p * q))) * ez s (A * (p * q'))
              = ez s (A * (p * q')) * (starRingEnd ℂ) (ez s (A * (p * q))) := fun p => by ring
        rw [Finset.sum_congr rfl fun p _ => hrw p, ez_kernel_orth]
        by_cases h : q' = q
        · simp [h]
        · have hne : A * (q' - q) ≠ 0 := fun hzero =>
            h (sub_eq_zero.mp ((hA.mul_right_eq_zero).mp hzero))
          simp [hne, h]
      rw [Finset.sum_congr rfl fun q' _ => inner' q']
      simp
    rw [Finset.sum_congr rfl fun q _ => step q, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ Finset.univ) => hc (G p),
    Finset.sum_congr rfl fun q (_ : q ∈ Finset.univ) => hc (Y q)] at hmain
  have hreal : ∑ p : ZMod s, ‖G p‖ ^ 2 = (s : ℝ) * ∑ q : ZMod s, ‖Y q‖ ^ 2 := by
    exact_mod_cast hmain
  have hsq : Real.sqrt s ^ 2 = (s : ℝ) := Real.sq_sqrt (by positivity)
  rw [hsq]
  exact le_of_eq hreal

/-- **Hilbert-valued `√s` bilinear bound for the reciprocal kernel.**  Obtained from the
scalar bound by the tensor-stability theorem `hilbertL2Bound_of_scalarL2Bound`. -/
theorem hilbert_bilinear_sqrt [FiniteDimensional ℂ H] (A : ZMod s) (hA : IsUnit A)
    (X Y : ZMod s → H) :
    ‖∑ p : ZMod s, ∑ q : ZMod s, ez s (A * (p * q)) * pairing (X p) (Y q)‖
      ≤ Real.sqrt s * (Real.sqrt (∑ p : ZMod s, ‖X p‖ ^ 2)
          * Real.sqrt (∑ q : ZMod s, ‖Y q‖ ^ 2)) := by
  set T : ZMod s → H := fun p => ∑ q : ZMod s, (starRingEnd ℂ) (ez s (A * (p * q))) • Y q with hT
  have hpair : ∀ p : ZMod s,
      ∑ q : ZMod s, ez s (A * (p * q)) * pairing (X p) (Y q) = inner ℂ (T p) (X p) := by
    intro p
    rw [hT, sum_inner]
    exact Finset.sum_congr rfl fun q _ => by
      rw [inner_smul_left, Complex.conj_conj, pairing]
  have hTnorm : ∑ p : ZMod s, ‖T p‖ ^ 2 ≤ (s : ℝ) * ∑ q : ZMod s, ‖Y q‖ ^ 2 := by
    have hbound := hilbertL2Bound_of_scalarL2Bound
      (H := H) (fun p q : ZMod s => (starRingEnd ℂ) (ez s (A * (p * q)))) (Real.sqrt s)
      (scalar_kernel_bound A hA) Y
    rwa [Real.sq_sqrt (by positivity : (0:ℝ) ≤ (s : ℝ))] at hbound
  calc ‖∑ p : ZMod s, ∑ q : ZMod s, ez s (A * (p * q)) * pairing (X p) (Y q)‖
      = ‖∑ p : ZMod s, inner ℂ (T p) (X p)‖ := by
        rw [Finset.sum_congr rfl fun p _ => hpair p]
    _ ≤ ∑ p : ZMod s, ‖inner ℂ (T p) (X p)‖ := norm_sum_le _ _
    _ ≤ ∑ p : ZMod s, ‖T p‖ * ‖X p‖ :=
        Finset.sum_le_sum fun p _ => norm_inner_le_norm _ _
    _ ≤ Real.sqrt (∑ p : ZMod s, ‖T p‖ ^ 2) * Real.sqrt (∑ p : ZMod s, ‖X p‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ ≤ Real.sqrt ((s : ℝ) * ∑ q : ZMod s, ‖Y q‖ ^ 2) * Real.sqrt (∑ p : ZMod s, ‖X p‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hTnorm) (Real.sqrt_nonneg _)
    _ = Real.sqrt s * (Real.sqrt (∑ p : ZMod s, ‖X p‖ ^ 2)
          * Real.sqrt (∑ q : ZMod s, ‖Y q‖ ^ 2)) := by
        rw [Real.sqrt_mul (by positivity)]
        ring

/-! ## 5. The energy branch -/

/-- **Energy branch (§15).**  With the phase pushed to inverse residue classes,
`f(x_d y_w) = e_s(A · p_d q_w)`, and residue-class multiplicities bounded by `c_D`, `c_W`,

```
|S_H| ≤ √(s · c_D · c_W) · A₂ · B₂.
```
-/
theorem packet_energy_branch [FiniteDimensional ℂ H] (Dset : Finset ι) (Wset : Finset κ)
    (al : ι → ℂ) (be : κ → ℂ) (u : ι → H) (v : κ → H) (xr : ι → ZMod s) (yr : κ → ZMod s)
    (f : ZMod s → ℂ) (A : ZMod s) (hA : IsUnit A) (pin : ι → ZMod s) (qin : κ → ZMod s)
    (hphase : ∀ d ∈ Dset, ∀ w ∈ Wset, f (xr d * yr w) = ez s (A * (pin d * qin w)))
    (cD cW : ℝ)
    (hcD : ∀ z : ZMod s, ((Dset.filter (fun d => pin d = z)).card : ℝ) ≤ cD)
    (hcW : ∀ z : ZMod s, ((Wset.filter (fun w => qin w = z)).card : ℝ) ≤ cW) :
    ‖packet s Dset Wset al be u v xr yr f‖
      ≤ Real.sqrt ((s : ℝ) * cD * cW)
        * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
            * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2)) := by
  have hcD0 : 0 ≤ cD := le_trans (by positivity) (hcD 0)
  have hcW0 : 0 ≤ cW := le_trans (by positivity) (hcW 0)
  set U : ZMod s → H := fun p => ∑ d ∈ Dset.filter (fun d => pin d = p), al d • u d with hU
  set V : ZMod s → H := fun q => ∑ w ∈ Wset.filter (fun w => qin w = q),
    ((starRingEnd ℂ) (be w)) • v w with hV
  -- Step 1: rewrite the packet in pushed-forward form
  have hstep : packet s Dset Wset al be u v xr yr f
      = ∑ p : ZMod s, ∑ q : ZMod s, ez s (A * (p * q)) * pairing (U p) (V q) := by
    symm
    have hcell : ∀ p q : ZMod s, ez s (A * (p * q)) * pairing (U p) (V q)
        = ∑ d ∈ Dset.filter (fun d => pin d = p), ∑ w ∈ Wset.filter (fun w => qin w = q),
            al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w) := by
      intro p q
      rw [hU, hV, pairing, sum_inner, Finset.mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun w hw => ?_
      rw [Finset.mem_filter] at hw
      rw [inner_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun d hd => ?_
      rw [Finset.mem_filter] at hd
      rw [inner_smul_left, inner_smul_right, Complex.conj_conj, ← pairing, hd.2, hw.2]
      ring
    calc ∑ p : ZMod s, ∑ q : ZMod s, ez s (A * (p * q)) * pairing (U p) (V q)
        = ∑ p : ZMod s, ∑ q : ZMod s, ∑ d ∈ Dset.filter (fun d => pin d = p),
            ∑ w ∈ Wset.filter (fun w => qin w = q),
              al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hcell p q
      _ = ∑ p : ZMod s, ∑ d ∈ Dset.filter (fun d => pin d = p), ∑ q : ZMod s,
            ∑ w ∈ Wset.filter (fun w => qin w = q),
              al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w) :=
          Finset.sum_congr rfl fun p _ => Finset.sum_comm
      _ = ∑ d ∈ Dset, ∑ q : ZMod s, ∑ w ∈ Wset.filter (fun w => qin w = q),
              al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w) :=
          Finset.sum_fiberwise Dset pin
            (fun d => ∑ q : ZMod s, ∑ w ∈ Wset.filter (fun w => qin w = q),
              al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w))
      _ = ∑ d ∈ Dset, ∑ w ∈ Wset,
              al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w) :=
          Finset.sum_congr rfl fun d _ =>
            Finset.sum_fiberwise Wset qin
              (fun w => al d * be w * ez s (A * (pin d * qin w)) * pairing (u d) (v w))
      _ = packet s Dset Wset al be u v xr yr f := by
          rw [packet]
          exact (Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun w hw => by
            rw [hphase d hd w hw]).symm
  -- Step 2: the two pushed-forward energies
  have hUenergy : ∑ p : ZMod s, ‖U p‖ ^ 2 ≤ cD * ∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2 :=
    fiber_energy_le_hilbert Dset pin al u cD hcD
  have hVenergy : ∑ q : ZMod s, ‖V q‖ ^ 2 ≤ cW * ∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2 := by
    have h := fiber_energy_le_hilbert Wset qin (fun w => (starRingEnd ℂ) (be w)) v cW hcW
    simpa using h
  -- Step 3: combine
  have hmain := hilbert_bilinear_sqrt (H := H) A hA U V
  rw [← hstep] at hmain
  have hSU : Real.sqrt (∑ p : ZMod s, ‖U p‖ ^ 2)
      ≤ Real.sqrt cD * Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2) := by
    rw [← Real.sqrt_mul hcD0]
    exact Real.sqrt_le_sqrt hUenergy
  have hSV : Real.sqrt (∑ q : ZMod s, ‖V q‖ ^ 2)
      ≤ Real.sqrt cW * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2) := by
    rw [← Real.sqrt_mul hcW0]
    exact Real.sqrt_le_sqrt hVenergy
  have hfinal : Real.sqrt s * (Real.sqrt (∑ p : ZMod s, ‖U p‖ ^ 2)
        * Real.sqrt (∑ q : ZMod s, ‖V q‖ ^ 2))
      ≤ Real.sqrt ((s : ℝ) * cD * cW)
        * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
            * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2)) := by
    have hprod : Real.sqrt (∑ p : ZMod s, ‖U p‖ ^ 2) * Real.sqrt (∑ q : ZMod s, ‖V q‖ ^ 2)
        ≤ (Real.sqrt cD * Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2))
            * (Real.sqrt cW * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2)) :=
      mul_le_mul hSU hSV (Real.sqrt_nonneg _) (by positivity)
    have hrw : Real.sqrt ((s : ℝ) * cD * cW) = Real.sqrt s * Real.sqrt cD * Real.sqrt cW := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity)]
    rw [hrw]
    calc Real.sqrt s * (Real.sqrt (∑ p : ZMod s, ‖U p‖ ^ 2)
            * Real.sqrt (∑ q : ZMod s, ‖V q‖ ^ 2))
        ≤ Real.sqrt s * ((Real.sqrt cD * Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2))
            * (Real.sqrt cW * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2))) :=
          mul_le_mul_of_nonneg_left hprod (Real.sqrt_nonneg _)
      _ = Real.sqrt s * Real.sqrt cD * Real.sqrt cW
            * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
              * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2)) := by ring
  exact le_trans hmain hfinal

/-- **Energy branch for interval sources.**  If the two sources lie in intervals of lengths
`Dlen`, `Wlen` and the inverse-class maps separate residues modulo `s`, the multiplicities
are the banked `1 + D/s`, `1 + W/s` (`Universal.D0WP.card_residue_class_le`), giving

```
|S_H| ≤ √(s(1+D/s)(1+W/s)) · A₂ · B₂.
```
-/
theorem packet_energy_branch_interval [FiniteDimensional ℂ H] (Dset Wset : Finset ℕ)
    (a Dlen b Wlen : ℕ) (hD : Dset ⊆ Finset.Ico a (a + Dlen))
    (hW : Wset ⊆ Finset.Ico b (b + Wlen)) (al be : ℕ → ℂ) (u v : ℕ → H)
    (xr yr : ℕ → ZMod s) (f : ZMod s → ℂ) (A : ZMod s) (hA : IsUnit A)
    (pin qin : ℕ → ZMod s)
    (hsepD : ∀ d₁ ∈ Dset, ∀ d₂ ∈ Dset, pin d₁ = pin d₂ → d₁ ≡ d₂ [MOD s])
    (hsepW : ∀ w₁ ∈ Wset, ∀ w₂ ∈ Wset, qin w₁ = qin w₂ → w₁ ≡ w₂ [MOD s])
    (hphase : ∀ d ∈ Dset, ∀ w ∈ Wset, f (xr d * yr w) = ez s (A * (pin d * qin w))) :
    ‖packet s Dset Wset al be u v xr yr f‖
      ≤ Real.sqrt ((s : ℝ) * (1 + (Dlen / s : ℕ) : ℝ) * (1 + (Wlen / s : ℕ) : ℝ))
        * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
            * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2)) := by
  have hs : s ≠ 0 := NeZero.ne s
  have hcD : ∀ z : ZMod s, ((Dset.filter (fun d => pin d = z)).card : ℝ)
      ≤ (1 + (Dlen / s : ℕ) : ℝ) := by
    intro z
    have hsub : Dset.filter (fun d => pin d = z) ⊆ Finset.Ico a (a + Dlen) :=
      (Finset.filter_subset _ _).trans hD
    have hmod : ∀ d₁ ∈ Dset.filter (fun d => pin d = z),
        ∀ d₂ ∈ Dset.filter (fun d => pin d = z), d₁ ≡ d₂ [MOD s] := by
      intro d₁ h₁ d₂ h₂
      rw [Finset.mem_filter] at h₁ h₂
      exact hsepD d₁ h₁.1 d₂ h₂.1 (h₁.2.trans h₂.2.symm)
    exact_mod_cast Universal.D0WP.card_residue_class_le hs _ hsub hmod
  have hcW : ∀ z : ZMod s, ((Wset.filter (fun w => qin w = z)).card : ℝ)
      ≤ (1 + (Wlen / s : ℕ) : ℝ) := by
    intro z
    have hsub : Wset.filter (fun w => qin w = z) ⊆ Finset.Ico b (b + Wlen) :=
      (Finset.filter_subset _ _).trans hW
    have hmod : ∀ w₁ ∈ Wset.filter (fun w => qin w = z),
        ∀ w₂ ∈ Wset.filter (fun w => qin w = z), w₁ ≡ w₂ [MOD s] := by
      intro w₁ h₁ w₂ h₂
      rw [Finset.mem_filter] at h₁ h₂
      exact hsepW w₁ h₁.1 w₂ h₂.1 (h₁.2.trans h₂.2.symm)
    exact_mod_cast Universal.D0WP.card_residue_class_le hs _ hsub hmod
  exact packet_energy_branch Dset Wset al be u v xr yr f A hA pin qin hphase _ _ hcD hcW

/-! ## 6. The finite Hilbert-HMRD theorem -/

/-- **Finite Hilbert-valued HMRD (§13).**  The packet obeys the minimum of the two branches:

```
|S_H| ≤ min ( √(φ(s)) · P · B₁ , √(s·c_D·c_W) · A₂ · B₂ ).
```

Both branches are kernel-proved above; nothing is assumed. -/
theorem packet_hmrd [FiniteDimensional ℂ H] (Dset : Finset ι) (Wset : Finset κ)
    (al : ι → ℂ) (be : κ → ℂ) (u : ι → H) (v : κ → H) (xr : ι → ZMod s) (yr : κ → ZMod s)
    (f : ZMod s → ℂ) (hsupp : ∀ x, ¬ IsUnit x → f x = 0) (hb : ∀ x, ‖f x‖ ≤ 1)
    (P B1 : ℝ) (hP : ∀ m : ZMod s, ‖∑ d ∈ Dset, (al d * ez s (m * xr d)) • u d‖ ≤ P)
    (hB1 : ∑ w ∈ Wset, ‖be w‖ * ‖v w‖ ≤ B1)
    (A : ZMod s) (hA : IsUnit A) (pin : ι → ZMod s) (qin : κ → ZMod s)
    (hphase : ∀ d ∈ Dset, ∀ w ∈ Wset, f (xr d * yr w) = ez s (A * (pin d * qin w)))
    (cD cW : ℝ)
    (hcD : ∀ z : ZMod s, ((Dset.filter (fun d => pin d = z)).card : ℝ) ≤ cD)
    (hcW : ∀ z : ZMod s, ((Wset.filter (fun w => qin w = z)).card : ℝ) ≤ cW) :
    ‖packet s Dset Wset al be u v xr yr f‖
      ≤ min (Real.sqrt (Nat.totient s) * (P * B1))
          (Real.sqrt ((s : ℝ) * cD * cW)
            * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
              * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2))) :=
  le_min
    (packet_small_branch Dset Wset al be u v xr yr f hsupp hb P B1 hP hB1)
    (packet_energy_branch Dset Wset al be u v xr yr f A hA pin qin hphase cD cW hcD hcW)

end

end Gate1B.HilbertHMRD
