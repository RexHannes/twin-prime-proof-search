import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.RamRecPostReduction

/-!
# Gate 1B · Ratio-fibre physicalisation bank (append-only)

**Phase B of the C4Shift consolidation.**  Append-only: nothing historical is
edited.  All statements here are exact finite algebra / finite Fourier
orthogonality / divisor algebra.  Where the *physical* source objects (the
`rho` transform, the support ranges of the physical shift `s`, the no-wrap
range inequalities) are not present in the repository, they appear as
**abstract function parameters** or as **uninhabited source interfaces**; they
are never fabricated and never turned into axioms.

## Contents

1. `ratioFibreSum`, `Rfibre`, `Gfibre` — the ratio-fibre objects with all finite
   variables retained.
2. `fibre_orthogonality` / `fibre_orthogonality_of_not_dvd` — the exact
   full-fibre Fourier identity
   `∑_{m mod ℓM, m ≡ λn (M)} e_{ℓM}(mz) = ℓ · 1_{ℓ ∣ z} · e_M(λ n (z/ℓ))`,
   with the quotient represented *after* divisibility is available (no ambiguous
   integer division).
3. `physical_s_congruence` — `z = s + 2N⁻¹` satisfies `ℓ ∣ z ↔ N s ≡ -2 (mod ℓ)`;
   `RatioPhysicalRangeInput` (UNINHABITED) carries the physical range support and
   yields `physical_s_unique`.
4. `K` — introduced only through `ell * K = N*s + 2`; `Rfibre_formula` is the
   exact `M`-character formula `ℓ ρ(s) e_M(λ r⁻¹ K)`.
5. `Gfibre_hoelder` — the rough λ-Fourier normal form expanded through the banked
   Ramanujan character.
6. `sum_lambda_orthogonality` — `∑_{λ mod M} e_M(λ r⁻¹ (K−y)) = M · 1_{y ≡ K}`
   and the resulting congruence `ℓ y ≡ N s + 2 (mod M)`.
7. `local_coefficient` — `d/N · μ(j) = μ(j)/(n j)` for `d = r/j`, `N = r n`.
8. `RatioNoWrapInput` (UNINHABITED) and the conditional physical shell
   `ell * y - N * s = 2`.
9. `W_infty_eq_one`, `W_trunc_error_le` — local weight reassembly and the exact
   finite truncation bound.
10. `crosspairD` — the physical crosspair normal form as a compiler over the
    exact interfaces (its analytic estimate is **not** inhabited).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace RatioPhysicalisation

open Finset ArithmeticFunction FiniteLiftLocalTwist AddMinRamanujan

/-! ## 1. Ratio-fibre definitions -/

/-- The full fibre sum over `m mod ℓM` with `m ≡ c (mod M)`, parametrised by
`m = c + M t`, `0 ≤ t < ℓ`. -/
noncomputable def ratioFibreSum (ell M : ℕ) (c z : ℤ) : ℂ :=
  ∑ t ∈ Finset.range ell, ezExp (ell * M) ((c + (M : ℤ) * t) * z)

/-- **The parametrisation is exhaustive.**  Every integer `m ≡ c (mod M)` is
congruent mod `ℓM` to exactly the parametrised representative `c + M t` for some
`0 ≤ t < ℓ`. -/
theorem fibre_parametrisation (ell M : ℕ) (hell : 0 < ell) {c m : ℤ}
    (h : (M : ℤ) ∣ (m - c)) :
    ∃ t ∈ Finset.range ell, ((ell * M : ℕ) : ℤ) ∣ (m - (c + (M : ℤ) * t)) := by
  obtain ⟨sq, hsq⟩ := h
  refine ⟨(sq % ell).toNat, ?_, ?_⟩
  · have h1 : 0 ≤ sq % (ell : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hell.ne')
    have h2 : sq % (ell : ℤ) < ell := Int.emod_lt_of_pos _ (by exact_mod_cast hell)
    refine Finset.mem_range.2 ?_
    omega
  · have h1 : 0 ≤ sq % (ell : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hell.ne')
    have hcast : ((sq % (ell : ℤ)).toNat : ℤ) = sq % (ell : ℤ) := Int.toNat_of_nonneg h1
    refine ⟨(sq / ell) * 1, ?_⟩
    rw [hcast]
    have hdiv : sq - sq % (ell : ℤ) = (ell : ℤ) * (sq / ell) := by
      have := Int.mul_ediv_add_emod sq (ell : ℤ)
      linarith [this]
    push_cast
    linear_combination hsq + (M : ℤ) * hdiv

/-- The ratio-fibre object `R_{ℓ;N,n}(λ)` with the abstract physical transform
`rho` retained as a function parameter (it is *not* instantiated here). -/
noncomputable def Rfibre (ell M : ℕ) (rho : ℤ → ℂ) (s n z lam : ℤ) : ℂ :=
  rho s * ratioFibreSum ell M (lam * n) z

/-- The rough ratio-fibre object `G_{u;ℓ,N,n}(λ)`, with abstract rough
coefficient `b` and the banked Ramanujan character `ramanujanC`. -/
noncomputable def Gfibre (M rRam Y : ℕ) (b : ℕ → ℂ) (invr ell lam : ℤ) : ℂ :=
  ∑ y ∈ Finset.range Y,
    (starRingEnd ℂ) (b y) * ezExp M (-(lam * invr * (y : ℤ))) * ramanujanC rRam (2 - ell * y)

/-! ## 2. Full-fibre Fourier orthogonality -/

/-- **Full-fibre Fourier orthogonality, divisible case.**  With `z = ℓ z'` the
fibre sum equals `ℓ · e_M(c z')`.  The quotient `z'` is *given*, so no ambiguous
integer division occurs. -/
theorem fibre_orthogonality (ell M : ℕ) (hell : 0 < ell) (hM : 0 < M) (c z z' : ℤ)
    (hz : z = (ell : ℤ) * z') :
    ratioFibreSum ell M c z = (ell : ℂ) * ezExp M (c * z') := by
  haveI : NeZero ell := ⟨hell.ne'⟩
  have hsplit : ∀ t : ℕ, ezExp (ell * M) ((c + (M : ℤ) * t) * z)
      = ezExp (ell * M) (c * z) * ezExp ell ((t : ℤ) * z) := by
    intro t
    have h1 : (c + (M : ℤ) * t) * z = c * z + (M : ℤ) * ((t : ℤ) * z) := by ring
    rw [h1, ezExp_add]
    congr 1
    exact ezExp_scale_right ell M ((t : ℤ) * z) hM.ne'
  have hc : ezExp (ell * M) (c * z) = ezExp M (c * z') := by
    have : c * z = (ell : ℤ) * (c * z') := by rw [hz]; ring
    rw [this]
    exact ezExp_scale_left ell M (c * z') hell.ne'
  have hsum : ∑ t ∈ Finset.range ell, ezExp ell ((t : ℤ) * z) = (ell : ℂ) := by
    rw [sum_range_ezExp ell z, if_pos ⟨z', hz⟩]
  calc ratioFibreSum ell M c z
      = ∑ t ∈ Finset.range ell, ezExp (ell * M) (c * z) * ezExp ell ((t : ℤ) * z) := by
        exact Finset.sum_congr rfl fun t _ => hsplit t
    _ = ezExp (ell * M) (c * z) * ∑ t ∈ Finset.range ell, ezExp ell ((t : ℤ) * z) := by
        rw [Finset.mul_sum]
    _ = (ell : ℂ) * ezExp M (c * z') := by rw [hsum, hc]; ring

/-- **Full-fibre Fourier orthogonality, non-divisible case.** -/
theorem fibre_orthogonality_of_not_dvd (ell M : ℕ) (hell : 0 < ell) (hM : 0 < M) (c z : ℤ)
    (hz : ¬ ((ell : ℤ) ∣ z)) :
    ratioFibreSum ell M c z = 0 := by
  haveI : NeZero ell := ⟨hell.ne'⟩
  have hsplit : ∀ t : ℕ, ezExp (ell * M) ((c + (M : ℤ) * t) * z)
      = ezExp (ell * M) (c * z) * ezExp ell ((t : ℤ) * z) := by
    intro t
    have h1 : (c + (M : ℤ) * t) * z = c * z + (M : ℤ) * ((t : ℤ) * z) := by ring
    rw [h1, ezExp_add]
    congr 1
    exact ezExp_scale_right ell M ((t : ℤ) * z) hM.ne'
  have hsum : ∑ t ∈ Finset.range ell, ezExp ell ((t : ℤ) * z) = 0 := by
    rw [sum_range_ezExp ell z, if_neg hz]
  calc ratioFibreSum ell M c z
      = ∑ t ∈ Finset.range ell, ezExp (ell * M) (c * z) * ezExp ell ((t : ℤ) * z) :=
        Finset.sum_congr rfl fun t _ => hsplit t
    _ = ezExp (ell * M) (c * z) * ∑ t ∈ Finset.range ell, ezExp ell ((t : ℤ) * z) := by
        rw [Finset.mul_sum]
    _ = 0 := by rw [hsum, mul_zero]

/-! ## 3. The physical `s` congruence and its (uninhabited) range interface -/

/-- **Physical `s` congruence.**  For `z = s + 2 N⁻¹` (with `N N⁻¹ ≡ 1 mod ℓ`
and `gcd(N, ℓ) = 1`): `ℓ ∣ z ↔ ℓ ∣ N s + 2`. -/
theorem physical_s_congruence (ell : ℕ) (N invN s z : ℤ)
    (hz : z = s + 2 * invN) (hinv : (ell : ℤ) ∣ (N * invN - 1))
    (hcop : IsCoprime N (ell : ℤ)) :
    (ell : ℤ) ∣ z ↔ (ell : ℤ) ∣ (N * s + 2) := by
  obtain ⟨w, hw⟩ := hinv
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨N * v - 2 * w, by rw [hz] at hv; linear_combination N * hv - 2 * hw⟩
  · rintro ⟨v, hv⟩
    have hNz : (ell : ℤ) ∣ N * z := ⟨v + 2 * w, by rw [hz]; linear_combination hv + 2 * hw⟩
    exact (hcop.symm).dvd_of_dvd_mul_left hNz

/-- **UNINHABITED source interface.**  The physical support `|s| < ℓ` (more
precisely: the physical shifts lie in a half-open interval of length `ℓ`) is
*not* represented anywhere in this repository.  This structure records exactly
that range datum and is never constructed. -/
structure RatioPhysicalRangeInput where
  /-- The lift modulus. -/
  ell : ℕ
  /-- Positivity of the lift modulus. -/
  ell_pos : 0 < ell
  /-- The determinant-line source integer `N`. -/
  N : ℤ
  /-- `N` is invertible modulo the lift. -/
  coprime : IsCoprime N (ell : ℤ)
  /-- Left endpoint of the physical window. -/
  s₀ : ℤ
  /-- The physical support predicate (a source object, not defined here). -/
  physical : ℤ → Prop
  /-- The *only* analytic-free content assumed: the physical window has length `ℓ`. -/
  window : ∀ s, physical s → s₀ ≤ s ∧ s < s₀ + ell

/-- **Conditional uniqueness of the physical `s`.**  Conditional on the
uninhabited range interface. -/
theorem physical_s_unique (I : RatioPhysicalRangeInput) {s₁ s₂ : ℤ}
    (h₁ : I.physical s₁) (h₂ : I.physical s₂)
    (c₁ : (I.ell : ℤ) ∣ (I.N * s₁ + 2)) (c₂ : (I.ell : ℤ) ∣ (I.N * s₂ + 2)) :
    s₁ = s₂ := by
  obtain ⟨a₁, b₁⟩ := I.window s₁ h₁
  obtain ⟨a₂, b₂⟩ := I.window s₂ h₂
  obtain ⟨v₁, hv₁⟩ := c₁
  obtain ⟨v₂, hv₂⟩ := c₂
  have hdvd : (I.ell : ℤ) ∣ I.N * (s₁ - s₂) := ⟨v₁ - v₂, by linear_combination hv₁ - hv₂⟩
  have hd : (I.ell : ℤ) ∣ (s₁ - s₂) := (I.coprime.symm).dvd_of_dvd_mul_left hdvd
  have habs : |s₁ - s₂| < (I.ell : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd hd habs
  omega

/-! ## 4. The `K` variable and the exact `M`-character formula -/

/-- `K` exists as an integer exactly when `ℓ ∣ N s + 2`; it is never introduced
by an ambiguous division. -/
theorem exists_K (ell : ℕ) (N s : ℤ) (h : (ell : ℤ) ∣ (N * s + 2)) :
    ∃ K : ℤ, (ell : ℤ) * K = N * s + 2 := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, hK.symm⟩

/-- **Fibre phase reduction.**  With `N = r n`, `r r⁻¹ ≡ 1 (mod M)`,
`N N⁻¹ ≡ 1 (mod ℓM)`, `z = s + 2N⁻¹`, `ℓ K = N s + 2` and `ℓ z' = z`:

`n z' ≡ r⁻¹ K (mod M)`. -/
theorem fibre_phase_reduction {ell M : ℕ} (hell : 0 < ell)
    {r n N invr invN s z z' K : ℤ}
    (hN : N = r * n) (hr : (M : ℤ) ∣ (r * invr - 1))
    (hinvN : ((ell : ℤ) * M) ∣ (N * invN - 1))
    (hz : z = s + 2 * invN) (hK : (ell : ℤ) * K = N * s + 2)
    (hz' : (ell : ℤ) * z' = z) (hcop : IsCoprime r (M : ℤ)) :
    (M : ℤ) ∣ (n * z' - invr * K) := by
  obtain ⟨w, hw⟩ := hinvN
  have hell' : (ell : ℤ) ≠ 0 := by exact_mod_cast hell.ne'
  -- `N z' = K + 2 M w`
  have key : (ell : ℤ) * (N * z' - K - 2 * (M : ℤ) * w) = 0 := by
    have h1 : (ell : ℤ) * (N * z') = N * z := by rw [← hz']; ring
    have h2 : N * z = N * s + 2 * (N * invN) := by rw [hz]; ring
    linear_combination h1 + h2 + 2 * hw - hK
  have hNz : N * z' - K = 2 * (M : ℤ) * w := by
    have := mul_eq_zero.1 key
    rcases this with h | h
    · exact absurd h hell'
    · linarith [h]
  obtain ⟨c, hc⟩ := hr
  have hdvd : (M : ℤ) ∣ r * (n * z' - invr * K) := by
    refine ⟨2 * w - c * K, ?_⟩
    rw [hN] at hNz
    linear_combination hNz - K * hc
  exact (hcop.symm).dvd_of_dvd_mul_left hdvd

/-- **The exact `M`-character formula for the full ratio fibre.**

`R_full(λ) = ℓ · ρ(s) · e_M(λ r⁻¹ K)`, conditional only on the abstract `ρ`
being supplied as a function (no analytic property of `ρ` is used). -/
theorem Rfibre_formula {ell M : ℕ} (hell : 0 < ell) (hM : 0 < M) (rho : ℤ → ℂ)
    {r n N invr invN s z z' K lam : ℤ}
    (hN : N = r * n) (hr : (M : ℤ) ∣ (r * invr - 1))
    (hinvN : ((ell : ℤ) * M) ∣ (N * invN - 1))
    (hz : z = s + 2 * invN) (hK : (ell : ℤ) * K = N * s + 2)
    (hz' : (ell : ℤ) * z' = z) (hcop : IsCoprime r (M : ℤ)) :
    Rfibre ell M rho s n z lam = (ell : ℂ) * rho s * ezExp M (lam * invr * K) := by
  have hred := fibre_phase_reduction hell hN hr hinvN hz hK hz' hcop
  have hphase : ezExp M (lam * n * z') = ezExp M (lam * invr * K) := by
    refine ezExp_congr M ?_
    obtain ⟨c, hc⟩ := hred
    exact ⟨lam * c, by linear_combination lam * hc⟩
  unfold Rfibre
  rw [fibre_orthogonality ell M hell hM (lam * n) z z' hz'.symm]
  rw [show (lam * n) * z' = lam * n * z' by ring, hphase]
  ring

/-! ## 5. Rough λ-Fourier normal form -/

/-- **Rough λ-Fourier normal form, Hölder-expanded.**  Uses the already-banked
Ramanujan character and its exact divisor (Hölder) form. -/
theorem Gfibre_hoelder (M rRam Y : ℕ) (hr : 0 < rRam) (b : ℕ → ℂ) (invr ell lam : ℤ) :
    Gfibre M rRam Y b invr ell lam
      = ∑ y ∈ Finset.range Y,
          (starRingEnd ℂ) (b y) * ezExp M (-(lam * invr * (y : ℤ))) *
            ∑ ab ∈ rRam.divisorsAntidiagonal,
              ((ArithmeticFunction.moebius ab.1 : ℤ) : ℂ) *
                (if (ab.2 : ℤ) ∣ (2 - ell * y) then (ab.2 : ℂ) else 0) := by
  unfold Gfibre
  exact Finset.sum_congr rfl fun y _ => by rw [ramanujanC_hoelder rRam hr]

/-! ## 6. λ orthogonality -/

/-- **λ orthogonality with a unit twist.**

`∑_{λ mod M} e_M(λ r⁻¹ w) = M · 1_{M ∣ w}` whenever `r⁻¹` is a unit mod `M`. -/
theorem sum_lambda_orthogonality (M : ℕ) [NeZero M] (invr w : ℤ)
    (hu : IsUnit ((invr : ℤ) : ZMod M)) :
    ∑ lam ∈ Finset.range M, ezExp M ((lam : ℤ) * invr * w)
      = if (M : ℤ) ∣ w then (M : ℂ) else 0 := by
  classical
  obtain ⟨u, hu'⟩ := hu
  -- rewrite each term through `ZMod M`
  have hterm : ∀ lam : ℕ, ezExp M ((lam : ℤ) * invr * w)
      = ezExp M ((((lam : ZMod M) * ((invr : ℤ) : ZMod M)).val : ℤ) * w) := by
    intro lam
    refine ezExp_congr M ?_
    have hz : (((lam : ℤ) * invr - (((lam : ZMod M) * ((invr : ℤ) : ZMod M)).val : ℤ) : ℤ)
        : ZMod M) = 0 := by
      push_cast
      simp [ZMod.natCast_val]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).1 hz
    obtain ⟨c, hc⟩ := this
    exact ⟨c * w, by linear_combination w * hc⟩
  have hsum1 : ∑ lam ∈ Finset.range M, ezExp M ((lam : ℤ) * invr * w)
      = ∑ x : ZMod M, ezExp M (((x * ((invr : ℤ) : ZMod M)).val : ℤ) * w) := by
    rw [Finset.sum_congr rfl (fun lam _ => hterm lam)]
    refine Finset.sum_nbij' (fun lam => (lam : ZMod M)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_univ _
    · intro x _; exact Finset.mem_range.2 (ZMod.val_lt x)
    · intro a ha; exact ZMod.val_cast_of_lt (Finset.mem_range.1 ha)
    · intro x _; simp
    · intro a _; rfl
  have hbij : Function.Bijective (fun x : ZMod M => x * ((invr : ℤ) : ZMod M)) := by
    constructor
    · intro a b hab
      have := congrArg (fun z => z * ((↑u⁻¹ : ZMod M))) hab
      simpa [mul_assoc, ← hu', ← Units.val_mul, mul_inv_cancel] using this
    · intro y
      refine ⟨y * ((↑u⁻¹ : ZMod M)), ?_⟩
      simp [mul_assoc, ← hu', ← Units.val_mul, inv_mul_cancel]
  have hsum2 : ∑ x : ZMod M, ezExp M (((x * ((invr : ℤ) : ZMod M)).val : ℤ) * w)
      = ∑ x : ZMod M, ezExp M ((x.val : ℤ) * w) :=
    Fintype.sum_bijective _ hbij _ _ (fun _ => rfl)
  rw [hsum1, hsum2, sum_ezExp M w]

/-- **The shell congruence.**  If `y ≡ K (mod M)` and `ℓ K = N s + 2`, then
`ℓ y ≡ N s + 2 (mod M)`. -/
theorem shell_congruence {M : ℕ} {ell N s y K : ℤ}
    (hy : (M : ℤ) ∣ (K - y)) (hK : ell * K = N * s + 2) :
    (M : ℤ) ∣ (ell * y - (N * s + 2)) := by
  obtain ⟨c, hc⟩ := hy
  exact ⟨-(ell * c), by linear_combination hK - ell * hc⟩

/-! ## 7. Near-full divisor algebra -/

/-- **Exact local coefficient.**  For `r = j d` and `N = r n`,
`(d / N) μ(j) = μ(j) / (n j)`. -/
theorem local_coefficient {r n j d N : ℕ} (hj : r = j * d) (hN : N = r * n)
    (hn : 0 < n) (hjpos : 0 < j) (hd : 0 < d) :
    ((d : ℚ) / N) * ((ArithmeticFunction.moebius j : ℤ) : ℚ)
      = ((ArithmeticFunction.moebius j : ℤ) : ℚ) / ((n : ℚ) * j) := by
  subst hj
  subst hN
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hj' : (j : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hjpos.ne'
  have hd' : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  push_cast
  field_simp

/-! ## 8. The (uninhabited) no-wrap socket and the physical shell -/

/-- **UNINHABITED source interface.**  The no-wrap range inequality
`|k − n j s| < M` is a *source range* datum; the repository contains no data
constructing it.  This structure records exactly that inequality. -/
structure RatioNoWrapInput where
  /-- The ratio modulus. -/
  M : ℕ
  /-- The congruence-side integer. -/
  k : ℤ
  /-- The physical target. -/
  target : ℤ
  /-- The one range input: no wrap-around modulo `M`. -/
  noWrap : |k - target| < (M : ℤ)

/-- **Conditional no-wrap collapse.**  Congruence plus the (uninhabited) range
input gives literal equality. -/
theorem eq_of_noWrap (I : RatioNoWrapInput) (h : (I.M : ℤ) ∣ (I.k - I.target)) :
    I.k = I.target := by
  have := Int.eq_zero_of_abs_lt_dvd h I.noWrap
  omega

/-- **Exact physical shell, conditional on the no-wrap input.**  From
`ℓ y ≡ N s + 2 (mod M)` and no wrap-around, `ℓ y − N s = 2`. -/
theorem physical_shell {M : ℕ} {ell N s y : ℤ}
    (hcong : (M : ℤ) ∣ (ell * y - (N * s + 2)))
    (hnw : |(ell * y - N * s) - 2| < (M : ℤ)) :
    ell * y - N * s = 2 := by
  have h : (M : ℤ) ∣ ((ell * y - N * s) - 2) := by
    obtain ⟨c, hc⟩ := hcong
    exact ⟨c, by linear_combination hc⟩
  have := Int.eq_zero_of_abs_lt_dvd h hnw
  omega

/-! ## 9. Local weight reassembly -/

/-- Reindexing of a double divisor sum: `(n ∣ N, j ∣ N/n) ↔ (t ∣ N, j ∣ t)` via
`t = n j`. -/
theorem double_divisor_reindex {α : Type*} [AddCommMonoid α] (N : ℕ) (hN : N ≠ 0)
    (f : ℕ → ℕ → α) :
    ∑ n ∈ N.divisors, ∑ j ∈ (N / n).divisors, f n j
      = ∑ t ∈ N.divisors, ∑ j ∈ t.divisors, f (t / j) j := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => (⟨p.1 * p.2, p.2⟩ : (_ : ℕ) × ℕ))
    (fun p => (⟨p.1 / p.2, p.2⟩ : (_ : ℕ) × ℕ)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨n, j⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨hn, -⟩, hj, hNn0⟩ := hp
    have hNn : N / n * n = N := Nat.div_mul_cancel hn
    obtain ⟨c, hc⟩ := hj
    have hNeq : N = n * j * c := by rw [← hNn, hc]; ring
    refine ⟨⟨⟨c, hNeq⟩, hN⟩, ⟨n, by ring⟩, ?_⟩
    intro h0
    exact hN (by rw [hNeq, h0]; ring)
  · rintro ⟨t, j⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp ⊢
    obtain ⟨⟨ht, -⟩, hj, htne⟩ := hp
    have hjpos : 0 < j :=
      Nat.pos_of_ne_zero (by rintro rfl; exact htne (Nat.eq_zero_of_zero_dvd hj))
    set d := t / j with hddef
    have hdj : d * j = t := Nat.div_mul_cancel hj
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h0 | h
      · rw [h0] at hdj; simp at hdj; exact absurd hdj.symm htne
      · exact h
    obtain ⟨m, hm⟩ := ht
    have hfact : N = d * (j * m) := by rw [hm, ← hdj]; ring
    have hNd : N / d = j * m := by
      rw [hfact]
      exact Nat.mul_div_cancel_left _ hdpos
    refine ⟨⟨⟨j * m, hfact⟩, hN⟩, ⟨m, by rw [hNd]⟩, ?_⟩
    rw [hNd]
    intro h0
    have hm0 : m = 0 := by
      rcases Nat.mul_eq_zero.1 h0 with h | h
      · exact absurd h hjpos.ne'
      · exact h
    exact hN (by rw [hm, hm0, Nat.mul_zero])
  · rintro ⟨n, j⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨-, -⟩, hj, hne⟩ := hp
    have hjpos : 0 < j :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne (Nat.eq_zero_of_zero_dvd hj))
    simp [Nat.mul_div_cancel _ hjpos]
  · rintro ⟨t, j⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨-, -⟩, hj, htne⟩ := hp
    simp [Nat.div_mul_cancel hj]
  · rintro ⟨n, j⟩ hp
    simp only [Finset.mem_sigma, Nat.mem_divisors] at hp
    obtain ⟨⟨-, -⟩, hj, hne⟩ := hp
    have hjpos : 0 < j :=
      Nat.pos_of_ne_zero (by rintro rfl; exact hne (Nat.eq_zero_of_zero_dvd hj))
    simp [Nat.mul_div_cancel _ hjpos]

/-- The infinite local weight `W_∞(N) = ∑_{n ∣ N} (1/n) ∑_{j ∣ N/n} μ(j)/j`. -/
noncomputable def W_infty (N : ℕ) : ℚ :=
  ∑ n ∈ N.divisors, (1 / (n : ℚ)) * ∑ j ∈ (N / n).divisors,
    ((ArithmeticFunction.moebius j : ℤ) : ℚ) / (j : ℚ)

/-- The truncated local weight: only the divisor products `t = n j ≤ T` are
retained. -/
noncomputable def W_trunc (N T : ℕ) : ℚ :=
  ∑ t ∈ N.divisors.filter (fun t => t ≤ T), (1 / (t : ℚ)) *
    ∑ j ∈ t.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ)

/-- The `t`-form of the local weight. -/
noncomputable def W_tform (N : ℕ) : ℚ :=
  ∑ t ∈ N.divisors, (1 / (t : ℚ)) * ∑ j ∈ t.divisors,
    ((ArithmeticFunction.moebius j : ℤ) : ℚ)

/-- The nested form and the `t`-form of the local weight agree. -/
theorem W_infty_eq_W_tform (N : ℕ) (hN : N ≠ 0) : W_infty N = W_tform N := by
  classical
  unfold W_infty W_tform
  have h1 : ∀ n ∈ N.divisors, (1 / (n : ℚ)) * ∑ j ∈ (N / n).divisors,
      ((ArithmeticFunction.moebius j : ℤ) : ℚ) / (j : ℚ)
      = ∑ j ∈ (N / n).divisors,
          ((ArithmeticFunction.moebius j : ℤ) : ℚ) / ((n : ℚ) * (j : ℚ)) := by
    intro n _
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [Finset.sum_congr rfl h1,
    double_divisor_reindex N hN
      (fun n j => ((ArithmeticFunction.moebius j : ℤ) : ℚ) / ((n : ℚ) * (j : ℚ)))]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htne : t ≠ 0 := by
    have := Nat.mem_divisors.1 ht
    rintro rfl
    exact this.2 (Nat.eq_zero_of_zero_dvd this.1)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjt : j ∣ t := (Nat.mem_divisors.1 hj).1
  have hjpos : 0 < j := Nat.pos_of_ne_zero (by rintro rfl; exact htne (Nat.eq_zero_of_zero_dvd hjt))
  have hcast : ((t / j : ℕ) : ℚ) * (j : ℚ) = (t : ℚ) := by
    rw [← Nat.cast_mul, Nat.div_mul_cancel hjt]
  rw [hcast]
  ring

/-- **Local weight reassembly.**  `W_∞(N) = 1`. -/
theorem W_infty_eq_one (N : ℕ) (hN : N ≠ 0) : W_infty N = 1 := by
  classical
  rw [W_infty_eq_W_tform N hN]
  unfold W_tform
  have hterm : ∀ t ∈ N.divisors, (1 / (t : ℚ)) * ∑ j ∈ t.divisors,
      ((ArithmeticFunction.moebius j : ℤ) : ℚ) = if t = 1 then 1 else 0 := by
    intro t ht
    have h := moebius_divisor_sum t
    have hQ : ∑ j ∈ t.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ)
        = ((if t = 1 then (1 : ℤ) else 0 : ℤ) : ℚ) := by
      rw [← h]; push_cast; ring
    rw [hQ]
    by_cases h1 : t = 1 <;> simp [h1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' N.divisors 1 (fun _ => (1 : ℚ))]
  simp [hN]

/-- **Exact finite truncation bound.**

`|1 − W_T(N)| ≤ ∑_{t ∣ N, t > T} τ(t)/t`.

This is a purely finite pointwise bound.  **No source-weighted average and no
arbitrary-log claim is made.** -/
theorem W_trunc_error_le (N T : ℕ) (hN : N ≠ 0) :
    |1 - W_trunc N T| ≤ ∑ t ∈ N.divisors.filter (fun t => ¬ t ≤ T),
      ((t.divisors.card : ℚ) / (t : ℚ)) := by
  classical
  have hsplit : W_tform N
      = W_trunc N T + ∑ t ∈ N.divisors.filter (fun t => ¬ t ≤ T), (1 / (t : ℚ)) *
          ∑ j ∈ t.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ) := by
    unfold W_trunc W_tform
    rw [← Finset.sum_filter_add_sum_filter_not N.divisors (fun t => t ≤ T)]
  have h1 : (1 : ℚ) - W_trunc N T
      = ∑ t ∈ N.divisors.filter (fun t => ¬ t ≤ T), (1 / (t : ℚ)) *
          ∑ j ∈ t.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ) := by
    have := W_infty_eq_one N hN
    rw [W_infty_eq_W_tform N hN] at this
    rw [hsplit] at this
    linarith [this]
  rw [h1]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum ?_)
  intro t ht
  have htN : t ∈ N.divisors := (Finset.mem_filter.1 ht).1
  have htpos : 0 < t := Nat.pos_of_mem_divisors htN
  have hb : |∑ j ∈ t.divisors, ((ArithmeticFunction.moebius j : ℤ) : ℚ)|
      ≤ (t.divisors.card : ℚ) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have : ∀ j ∈ t.divisors, |((ArithmeticFunction.moebius j : ℤ) : ℚ)| ≤ 1 := by
      intro j _
      have hz : |(ArithmeticFunction.moebius j : ℤ)| ≤ 1 :=
        ArithmeticFunction.abs_moebius_le_one
      exact_mod_cast hz
    calc ∑ j ∈ t.divisors, |((ArithmeticFunction.moebius j : ℤ) : ℚ)|
        ≤ ∑ _j ∈ t.divisors, (1 : ℚ) := Finset.sum_le_sum this
      _ = (t.divisors.card : ℚ) := by simp
  have ht' : |(1 : ℚ) / (t : ℚ)| = 1 / (t : ℚ) := by
    rw [abs_of_nonneg]
    positivity
  have hrw : ((t.divisors.card : ℚ) / (t : ℚ)) = 1 / (t : ℚ) * (t.divisors.card : ℚ) := by
    ring
  rw [abs_mul, ht', hrw]
  exact mul_le_mul_of_nonneg_left hb (by positivity)

/-! ## 10. Physical crosspair normal form -/

/-- Abstract source data for the transformed crosspair `D_j`.  Every field is an
abstract finite object: **no analytic estimate and no synthetic source object is
created here.** -/
structure CrosspairData where
  /-- The lift modulus. -/
  ell : ℕ
  /-- Positivity of the lift. -/
  ell_pos : 0 < ell
  /-- Finite support of the tuples `(u, A, s, h)`. -/
  support : Finset (ℤ × ℤ × ℤ × ℤ)
  /-- The smooth/physical weight. -/
  w : ℤ × ℤ × ℤ × ℤ → ℂ
  /-- The `u`-side coefficient. -/
  a4 : ℤ → ℂ
  /-- The `A`-side coefficient. -/
  c4j : ℤ → ℂ
  /-- The physical `ρ`-transform. -/
  rhoj : ℤ → ℂ
  /-- The `h`-side kernel. -/
  kappa : ℤ → ℂ
  /-- The outer β-factor. -/
  beta : ℤ → ℂ
  /-- The shell divisibility, retained as an explicit support condition. -/
  shell : ∀ p ∈ support, (ell : ℤ) ∣ (p.1 * p.2.1 * p.2.2.1 + 2)
  /-- The shell quotient, provided as an integer (never by ambiguous division). -/
  K : ℤ × ℤ × ℤ × ℤ → ℤ
  /-- `K` really is the quotient. -/
  K_spec : ∀ p ∈ support, (ell : ℤ) * K p = p.1 * p.2.1 * p.2.2.1 + 2

/-- The transformed crosspair `D_j`, written with the *integer* shell quotient
`K` in place of `(uAs+2)/ℓ`. -/
noncomputable def crosspairD (D : CrosspairData) : ℂ :=
  ∑ p ∈ D.support,
    D.w p * D.a4 p.1 * D.c4j p.2.1 * D.rhoj p.2.2.1 * D.kappa p.2.2.2 *
      D.beta (D.K p + p.1 * p.2.2.2)

/-- **Compiler theorem.**  The crosspair normal form contains no ambiguous
integer division: the β-argument is the genuine integer solution of
`ℓ · x = u A s + 2` shifted by `u h`.  (This is a structural statement; **no
analytic estimate for `D_j` is inhabited**.) -/
theorem crosspairD_argument_spec (D : CrosspairData) (p : ℤ × ℤ × ℤ × ℤ)
    (hp : p ∈ D.support) :
    (D.ell : ℤ) * (D.K p + p.1 * p.2.2.2)
      = (p.1 * p.2.1 * p.2.2.1 + 2) + (D.ell : ℤ) * p.1 * p.2.2.2 := by
  have := D.K_spec p hp
  linear_combination this

/-! ## 11. Status metadata for this phase (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the ratio-fibre physicalisation bank. -/
def statusRows : List LedgerEntry :=
  [ ⟨"DETLINE-RAMREC-NEARFULL-RATIO-PHASEGAP45", Status.supersededAsControllingFrontier,
     "SUPERSEDED / STRICTLY REDUCED / NOT FALSE. Its exact algebra is now carried by fibre_orthogonality, Rfibre_formula, sum_lambda_orthogonality and physical_shell."⟩,
    ⟨"DETLINE-RAMREC-RATIO-DIAGONAL-DEFECT-BETA45", Status.supersededAsControllingFrontier,
     "HISTORICAL CHILD. Retained as a label; not false, not controlling."⟩,
    ⟨"RATIO-PHYSICAL-S-RANGE-INPUT45", Status.sourceOpen,
     "UNINHABITED SOURCE INTERFACE RatioPhysicalRangeInput (physical window of length ell). physical_s_unique is a conditional compiler over it."⟩,
    ⟨"RATIO-NOWRAP-INPUT45", Status.sourceOpen,
     "UNINHABITED SOURCE INTERFACE RatioNoWrapInput. eq_of_noWrap and physical_shell are conditional compilers over the range inequality."⟩,
    ⟨"RAMREC-LOCAL-WEIGHT-REASSEMBLY45", Status.provedAlgebraic,
     "KERNEL-PROVED: double_divisor_reindex, W_infty_eq_W_tform, W_infty_eq_one, W_trunc_error_le. The analytic truncation n*j <= log^B X is NOT formalised."⟩ ]

/-- No row of this phase is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

end RatioPhysicalisation
end CurrentProgramme
end TwinPrimeProject
