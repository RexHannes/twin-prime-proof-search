import Mathlib
import RequestProject.CurrentProgramme.DetLineCompanionAdditiveFourier
import RequestProject.CurrentProgramme.NearPrimitivePhysicalProjector
import RequestProject.CurrentProgramme.BroadMinorAdditiveFourier

/-!
# Gate 1B · the additive-minor crosspair socket (append-only delta layer)

`DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45 : ANALYTIC_OPEN / UNINHABITED`.

This module assembles the exact objects banked in

* `FiniteLiftLocalTwistCompression` (finite lift `e`, local twists),
* `NearPrimitivePhysicalProjector` (conductor `c`, weight `w_{c,e}`),
* `BroadMinorAdditiveFourier` (`ρ̂ = (1−Π)δ̂`, plateau / transition / minor),
* `DetLineCompanionAdditiveFourier` (`Ĉ` with the genuine quotient phase),

into the **exact formal expression** `additiveMinorCrossPair`, and exposes the
current research residual as an **uninhabited** interface.

## Non-claims

* The interface is never inhabited: no analytic arbitrary-log estimate is proved.
* The source data is *not* replaced by arbitrary `L²` vectors: the companion
  keeps its five variables `u, A, d, p, h`, the coefficient keeps its literal
  `μ(d) · log p · κ(h) · (physical coefficient)` form, the divisibility
  condition `uA ∣ ℓ(dp−uh)−2` is retained, and the phase is the genuine
  quotient phase.
* `additiveMinorSeparateEnergy_natural_scale` records that the separate-energy
  (Cauchy) route is *nonclosing at natural scale* — not false, simply
  insufficient.
* `ttStar_identification_reconstructs_determinant_shell` records that
  identifying the two physical `s` variables returns a relation of the same
  determinant type: a representation loop, not a controlling route.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AdditiveMinorCrosspair

open Finset ZMod DetLineCompanion NearPrimitiveProjector FiniteLiftLocalTwist

/-! ## 1. The source-specific data -/

/-- **The additive-minor crosspair data.**  Everything the research statement
mentions is retained as an explicit field: the finite lift `e`, the conductor
`c`, `ℓ = c e`, the projector weight `w_{c,e} = Ω_c(S)/φ(ce)`, the modulus
`q_ℓ`, the additive-minor frequency set, the actual `ρ̂ = (1−Π)δ̂` multiplier
form, the companion skeleton with its five variables, and the literal
coefficient shape `μ(d) · log p · κ(h) · physical`. -/
structure AdditiveMinorCrosspairData (ι : Type*) where
  /-- The companion skeleton, with `u, A, d, p, h` kept separate. -/
  K : CompanionSkeleton ι
  /-- `d` as a natural number, for `μ(d)`. -/
  dNat : ι → ℕ
  /-- `p` as a natural number, for `log p`. -/
  pNat : ι → ℕ
  /-- Compatibility of `dNat` with the skeleton's `d`. -/
  dNat_eq : ∀ t ∈ K.T, (dNat t : ℤ) = K.d t
  /-- Compatibility of `pNat` with the skeleton's `p`. -/
  pNat_eq : ∀ t ∈ K.T, (pNat t : ℤ) = K.p t
  /-- The shift weight `κ(h)`. -/
  kappa : ℤ → ℂ
  /-- The physical coefficient source. -/
  physCoeff : ι → ℂ
  /-- **The literal coefficient shape** `coeff = μ(d) · log p · κ(h) · physical`. -/
  coeff_form : ∀ t ∈ K.T,
    K.coeff t = ((ArithmeticFunction.moebius (dNat t) : ℤ) : ℂ) *
      ((Real.log (pNat t) : ℝ) : ℂ) * kappa (K.h t) * physCoeff t
  /-- The finite-lift / conductor cells `(e, c)`. -/
  cells : Finset (ℕ × ℕ)
  /-- The physical support radius `S`. -/
  S : ℕ
  /-- The physical `s`-support. -/
  supp : Finset ℤ
  /-- The modulus `q_ℓ` attached to a cell. -/
  qOf : ℕ × ℕ → ℕ
  /-- The broad-minor multiplier `Π_ℓ`. -/
  Pi : ℕ × ℕ → ℤ → ℝ
  /-- The companion source transform `δ̂_{j,ℓ}`. -/
  deltaHat : ℕ × ℕ → ℤ → ℂ
  /-- `ρ̂_{j,ℓ}`, in its **actual multiplier form**. -/
  rhoHat : ℕ × ℕ → ℤ → ℂ
  /-- The actual multiplier law `ρ̂ = (1 − Π) δ̂`. -/
  rhoHat_form : ∀ cell ∈ cells, ∀ m : ℤ,
    rhoHat cell m = (1 - (Pi cell m : ℂ)) * deltaHat cell m
  /-- The additive-minor frequency set of a cell. -/
  minorFreqs : ℕ × ℕ → Finset ℤ
  /-- The additive-minor frequencies are exactly the `Π = 0` frequencies. -/
  minorFreqs_spec : ∀ cell ∈ cells, ∀ m ∈ minorFreqs cell, Pi cell m = 0
  /-- Nonvanishing of the completed modulus on the tuple set. -/
  uA_pos : ∀ t ∈ K.T, 0 < K.u t * K.A t

variable {ι : Type*}

/-- `ℓ = c · e` for the cell `(e, c)`. -/
def ellOf (cell : ℕ × ℕ) : ℤ := (cell.2 * cell.1 : ℕ)

/-- The projector weight `w_{c,e} = Ω_c(S) / φ(c e)` of a cell. -/
noncomputable def weightOf (D : AdditiveMinorCrosspairData ι) (cell : ℕ × ℕ) : ℝ :=
  physicalWeight cell.2 cell.1 D.S

/-- The companion transform of a cell, at additive frequency `m`. -/
noncomputable def compHat (D : AdditiveMinorCrosspairData ι) (cell : ℕ × ℕ) (m : ℤ) : ℂ :=
  companionHat D.K (ellOf cell) D.supp (D.qOf cell) m

/-! ## 2. The exact additive-minor crosspair expression -/

/-- **`AdditiveMinorCrossPair`** — the exact remaining formal expression

```
∑_{e,c} (w_{c,e}/q_ℓ) ∑_{m ∈ additive minor} ρ̂_{j,ℓ}(m) conj(Ĉ_{j,ℓ}(m)).
```

It is **not** estimated anywhere in this repository. -/
noncomputable def additiveMinorCrossPair (D : AdditiveMinorCrosspairData ι) : ℂ :=
  ∑ cell ∈ D.cells,
    ((weightOf D cell : ℂ) / (D.qOf cell : ℂ)) *
      ∑ m ∈ D.minorFreqs cell,
        D.rhoHat cell m * (starRingEnd ℂ) (compHat D cell m)

/-- **The crosspair really does carry the source-specific companion.**  On the
additive-minor frequencies the companion factor is the exact quotient-phase
normal form: divisibility `uA ∣ ℓ(dp−uh)−2` is explicit and the phase is
`e_{q_ℓ}(m [ℓ(dp−uh)−2]/(uA))`. -/
theorem compHat_is_quotient_phase [DecidableEq ι] (D : AdditiveMinorCrosspairData ι)
    (cell : ℕ × ℕ) (m : ℤ)
    (hS : ∀ t ∈ D.K.T, (D.K.u t * D.K.A t) ∣ Nval D.K (ellOf cell) t →
      Nval D.K (ellOf cell) t / (D.K.u t * D.K.A t) ∈ D.supp) :
    compHat D cell m
      = ∑ t ∈ D.K.T, D.K.coeff t *
          (if (D.K.u t * D.K.A t) ∣ Nval D.K (ellOf cell) t then (1 : ℂ) else 0) *
          ezExp (D.qOf cell)
            (m * (Nval D.K (ellOf cell) t / (D.K.u t * D.K.A t))) :=
  companionHat_normal_form D.K (ellOf cell) D.supp (D.qOf cell) m
    (fun t ht => (D.uA_pos t ht).ne') hS

/-- **On the additive minor, `ρ̂ = δ̂`.**  Exact: `Π = 0` there. -/
theorem rhoHat_eq_deltaHat_on_minor (D : AdditiveMinorCrosspairData ι)
    {cell : ℕ × ℕ} (hcell : cell ∈ D.cells) {m : ℤ} (hm : m ∈ D.minorFreqs cell) :
    D.rhoHat cell m = D.deltaHat cell m := by
  rw [D.rhoHat_form cell hcell m, D.minorFreqs_spec cell hcell m hm]
  push_cast
  ring

/-! ## 3. The analytic socket (UNINHABITED) -/

/-- **`DetLineNearPrimAdditiveMinorCrosspairInput` — UNINHABITED.**

The current first exact research residual: the additive-minor crosspair admits
an arbitrary-log saving.  Every source-specific ingredient is retained through
the data `D`; the interface adds only the (unproved) analytic bound. -/
structure DetLineNearPrimAdditiveMinorCrosspairInput (D : AdditiveMinorCrosspairData ι) where
  /-- The declared arbitrary-log budget. -/
  budget : ℝ
  /-- The analytic assertion.  **NOT SUPPLIED.** -/
  bound : ‖additiveMinorCrossPair D‖ ≤ budget

/-- The socket is an assumption, not a theorem: all it yields is its own
declared bound. -/
theorem crosspair_input_is_an_assumption {D : AdditiveMinorCrosspairData ι}
    (I : DetLineNearPrimAdditiveMinorCrosspairInput D) :
    ‖additiveMinorCrossPair D‖ ≤ I.budget := I.bound

/-! ## 4. Natural-scale nonclosure firewall -/

/-- **Abstract Cauchy–Schwarz.**  `|⟨ρ, C⟩| ≤ ‖ρ‖₂ ‖C‖₂`.  Pure finite
functional analysis; it produces the *natural scale* only. -/
theorem cauchy_pairing_bound {κ : Type*} (s : Finset κ) (f g : κ → ℂ) (R C : ℝ)
    (hR : 0 ≤ R) (hC : 0 ≤ C)
    (hf : ∑ i ∈ s, ‖f i‖ ^ 2 ≤ R ^ 2) (hg : ∑ i ∈ s, ‖g i‖ ^ 2 ≤ C ^ 2) :
    ‖∑ i ∈ s, f i * (starRingEnd ℂ) (g i)‖ ≤ R * C := by
  have h1 : ‖∑ i ∈ s, f i * (starRingEnd ℂ) (g i)‖ ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul, RCLike.norm_conj]
  have h2 : (∑ i ∈ s, ‖f i‖ * ‖g i‖) ^ 2
      ≤ (∑ i ∈ s, ‖f i‖ ^ 2) * ∑ i ∈ s, ‖g i‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq s (fun i => ‖f i‖) (fun i => ‖g i‖)
  have hfn : (0 : ℝ) ≤ ∑ i ∈ s, ‖f i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hgn : (0 : ℝ) ≤ ∑ i ∈ s, ‖g i‖ ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  have hsum : (0 : ℝ) ≤ ∑ i ∈ s, ‖f i‖ * ‖g i‖ :=
    Finset.sum_nonneg fun i _ => by positivity
  nlinarith [h1, h2, hsum, mul_nonneg hR hC, mul_le_mul hf hg hgn (sq_nonneg R)]

/-- **`ADDITIVE-MINOR-SEPARATE-ENERGY45` — NATURAL SCALE / NONCLOSING.**

Separate `L²` control of the two sides gives no saving: the Cauchy bound is
attained.  This is the repository's existing countermodel, re-exported here; it
does **not** say the route is mathematically false, only that it is
insufficient at the available norm sizes. -/
theorem additiveMinorSeparateEnergy_natural_scale :
    ∃ (f : ZMod 2 → ℂ),
      ((2 : ℂ))⁻¹ * ∑ k : ZMod 2, 𝓕 f k * (starRingEnd ℂ) (𝓕 f k)
        = ∑ t : ZMod 2, f t * (starRingEnd ℂ) (f t) ∧
      ∑ t : ZMod 2, f t * (starRingEnd ℂ) (f t) = 2 :=
  FiniteLineFourier.separate_energy_gives_no_cancellation

/-! ## 5. TT\* representation loop -/

/-- **`ADDITIVE-MINOR-TTSTAR45` — REPRESENTATION LOOP.**

Identifying the two physical `s` variables returns a relation of exactly the
same determinant type (a rank-two determinant shell relation between the two
tuples), so the TT\* step reproduces the source geometry rather than controlling
it.  No general TT\* theorem is claimed false. -/
theorem ttStar_identification_reconstructs_determinant_shell
    (K : CompanionSkeleton ι) (ell : ℤ) (t t' : ι) (s : ℤ)
    (h : detRel K ell t s) (h' : detRel K ell t' s) :
    ell * ((K.d t * K.p t - K.u t * K.h t) - (K.d t' * K.p t' - K.u t' * K.h t'))
      = (K.u t * K.A t - K.u t' * K.A t') * s := by
  unfold detRel at h h'
  ring_nf
  ring_nf at h h'
  linarith

end AdditiveMinorCrosspair
end CurrentProgramme
end TwinPrimeProject
