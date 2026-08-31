import Mathlib
import RequestProject.CurrentProgramme.FiniteLiftLocalTwistCompression

/-!
# Gate 1B · companion additive Fourier normal form (append-only delta layer)

`DETLINE-COMPANION-ADDITIVE-FOURIER45`.

**Everything here is an exact finite identity.**  The variables
`u, A, d, p, h` are kept separate, the coefficient is kept abstract, and the
quotient integrality is *never* hidden: it appears as the explicit divisibility
condition `uA ∣ N` with `N = ℓ(dp − uh) − 2`, and the phase is the genuine
quotient phase `e_{q_ℓ}(m · N/(uA))`.

## Contents

* `detline_iff` — `ℓ(dp − uh) − uAs = 2  ↔  uA ∣ N ∧ s = N/(uA)`, with the
  nonvanishing hypothesis `uA ≠ 0` printed explicitly.
* `companionHat_normal_form` — the exact DFT normal form
  `Ĉ(m) = ∑_{u,A,d,p,h} coeff · 1_{uA ∣ N} · e_{q_ℓ}(m N/(uA))`.
* `dvd_completion` — `1_{k ∣ N} = (1/k) ∑_{b mod k} e_k(bN)`.
* `completed_quotient_phase` and `companionHat_completed` — the completed
  companion identity
  `(1/uA) ∑_{b mod uA} e_{q_ℓ uA}((b q_ℓ + m)(ℓ(dp − uh) − 2))`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace DetLineCompanion

open Finset FiniteLiftLocalTwist

/-! ## 1. The finite companion skeleton -/

/-- The finite companion skeleton `C_{j,ℓ}`: an abstract finite index set of
tuples `(u, A, d, p, h)` with an abstract coefficient.  The five variables are
kept separate, exactly as in the source. -/
structure CompanionSkeleton (ι : Type*) where
  /-- The finite tuple set. -/
  T : Finset ι
  /-- The `u` variable. -/
  u : ι → ℤ
  /-- The `A` variable. -/
  A : ι → ℤ
  /-- The `d` variable (carrying `μ(d)` in the source). -/
  d : ι → ℤ
  /-- The `p` variable (carrying `log p` in the source). -/
  p : ι → ℤ
  /-- The `h` variable (carrying `κ(h)` in the source). -/
  h : ι → ℤ
  /-- The abstract coefficient `coeff(u,A,d,p,h)`. -/
  coeff : ι → ℂ

variable {ι : Type*}

/-- `N = ℓ(dp − uh) − 2`. -/
def Nval (K : CompanionSkeleton ι) (ell : ℤ) (t : ι) : ℤ :=
  ell * (K.d t * K.p t - K.u t * K.h t) - 2

/-- The determinant relation `ℓ(dp − uh) − uAs = 2` at the tuple `t`. -/
def detRel (K : CompanionSkeleton ι) (ell : ℤ) (t : ι) (s : ℤ) : Prop :=
  ell * (K.d t * K.p t - K.u t * K.h t) - K.u t * K.A t * s = 2

instance (K : CompanionSkeleton ι) (ell : ℤ) (t : ι) (s : ℤ) :
    Decidable (detRel K ell t s) := by
  unfold detRel; infer_instance

/-- The finite companion `C_{j,ℓ}(s) = ∑_{ℓ(dp−uh)−uAs=2} coeff(u,A,d,p,h)`. -/
noncomputable def companion (K : CompanionSkeleton ι) (ell : ℤ) (s : ℤ) : ℂ :=
  ∑ t ∈ K.T.filter (fun t => detRel K ell t s), K.coeff t

/-! ## 2. The exact determinant equivalence -/

/-- **Exact equivalence, with integrality exposed.**

`ℓ(dp − uh) − uAs = 2  ↔  uA ∣ N ∧ s = N/(uA)`, where `N = ℓ(dp − uh) − 2`.
The hypothesis `uA ≠ 0` is printed explicitly. -/
theorem detline_iff {ell u A d p h s : ℤ} (hua : u * A ≠ 0) :
    ell * (d * p - u * h) - u * A * s = 2
      ↔ (u * A ∣ (ell * (d * p - u * h) - 2) ∧
          s = (ell * (d * p - u * h) - 2) / (u * A)) := by
  constructor
  · intro he
    have hmul : u * A * s = ell * (d * p - u * h) - 2 := by linarith
    refine ⟨⟨s, hmul.symm⟩, ?_⟩
    rw [← hmul, Int.mul_ediv_cancel_left _ hua]
  · rintro ⟨⟨k, hk⟩, hs⟩
    rw [hs, hk, Int.mul_ediv_cancel_left _ hua]
    linarith [hk]

/-- The same equivalence phrased on the skeleton. -/
theorem detRel_iff (K : CompanionSkeleton ι) (ell : ℤ) {t : ι} (s : ℤ)
    (hua : K.u t * K.A t ≠ 0) :
    detRel K ell t s ↔
      ((K.u t * K.A t) ∣ Nval K ell t ∧ s = Nval K ell t / (K.u t * K.A t)) :=
  detline_iff hua

/-! ## 3. The exact DFT normal form -/

/-- The companion transform `Ĉ_{j,ℓ}(m) = ∑_{s ∈ S} C_{j,ℓ}(s) e_{q_ℓ}(m s)` on a
finite physical `s`-support `S`. -/
noncomputable def companionHat (K : CompanionSkeleton ι) (ell : ℤ) (S : Finset ℤ)
    (q : ℕ) (m : ℤ) : ℂ :=
  ∑ s ∈ S, companion K ell s * ezExp q (m * s)

/-- **`DETLINE-COMPANION-ADDITIVE-FOURIER45`: the exact DFT normal form.**

```
Ĉ_{j,ℓ}(m) = ∑_{u,A,d,p,h} coeff · 1_{uA ∣ ℓ(dp−uh)−2} · e_{q_ℓ}(m [ℓ(dp−uh)−2]/(uA)).
```

Hypotheses printed explicitly: `uA ≠ 0` on the tuple set, and the physical
`s`-support contains every admissible quotient. -/
theorem companionHat_normal_form [DecidableEq ι] (K : CompanionSkeleton ι) (ell : ℤ)
    (S : Finset ℤ) (q : ℕ) (m : ℤ)
    (hua : ∀ t ∈ K.T, K.u t * K.A t ≠ 0)
    (hS : ∀ t ∈ K.T, (K.u t * K.A t) ∣ Nval K ell t →
      Nval K ell t / (K.u t * K.A t) ∈ S) :
    companionHat K ell S q m
      = ∑ t ∈ K.T, K.coeff t *
          (if (K.u t * K.A t) ∣ Nval K ell t then (1 : ℂ) else 0) *
          ezExp q (m * (Nval K ell t / (K.u t * K.A t))) := by
  classical
  have step1 : ∀ s : ℤ, companion K ell s * ezExp q (m * s)
      = ∑ t ∈ K.T, (if detRel K ell t s then K.coeff t * ezExp q (m * s) else 0) := by
    intro s
    rw [companion, Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun t _ => by split <;> simp
  rw [companionHat, Finset.sum_congr rfl fun s _ => step1 s, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t ht => ?_
  by_cases hdvd : (K.u t * K.A t) ∣ Nval K ell t
  · rw [if_pos hdvd, mul_one]
    rw [Finset.sum_eq_single (Nval K ell t / (K.u t * K.A t))]
    · rw [if_pos ((detRel_iff K ell _ (hua t ht)).2 ⟨hdvd, rfl⟩)]
    · intro s _ hne
      rw [if_neg]
      intro hP
      exact hne ((detRel_iff K ell s (hua t ht)).1 hP).2
    · intro hnot
      exact absurd (hS t ht hdvd) hnot
  · rw [if_neg hdvd]
    refine (Finset.sum_eq_zero fun s _ => ?_).trans (by ring)
    rw [if_neg]
    intro hP
    exact hdvd ((detRel_iff K ell s (hua t ht)).1 hP).1

/-! ## 4. The divisibility completion identity -/

/-- **Divisibility completion.**  `1_{k ∣ N} = (1/k) ∑_{b mod k} e_k(bN)` for
`k > 0`.  This is the repository's finite orthogonality, instantiated. -/
theorem dvd_completion (k : ℕ) [NeZero k] (Nz : ℤ) :
    (if (k : ℤ) ∣ Nz then (1 : ℂ) else 0)
      = ((k : ℂ))⁻¹ * ∑ b : ZMod k, ezExp k (b.val * Nz) :=
  additive_indicator_exp k Nz

/-- **Completed quotient phase.**  For `k > 0`, `q > 0`,

```
(1/k) ∑_{b mod k} e_{q k}((b q + m) N) = 1_{k ∣ N} · e_q(m · N/k).
```

Signs and denominators are literal: the outer modulus is `q k`, the inner
frequency is `b q + m`, and the quotient `N/k` appears only under `k ∣ N`. -/
theorem completed_quotient_phase (q k : ℕ) [NeZero q] [NeZero k] (m Nz : ℤ) :
    ((k : ℂ))⁻¹ * ∑ b ∈ Finset.range k, ezExp (q * k) (((b : ℤ) * q + m) * Nz)
      = (if (k : ℤ) ∣ Nz then ezExp q (m * (Nz / k)) else 0) := by
  have hq : q ≠ 0 := NeZero.ne q
  have hk : k ≠ 0 := NeZero.ne k
  have hkC : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk
  have hterm : ∀ b : ℕ, ezExp (q * k) (((b : ℤ) * q + m) * Nz)
      = ezExp k ((b : ℤ) * Nz) * ezExp (q * k) (m * Nz) := by
    intro b
    have hsplit : ((b : ℤ) * q + m) * Nz = (q : ℤ) * ((b : ℤ) * Nz) + m * Nz := by
      ring
    rw [hsplit, ezExp_add, ezExp_scale_left q k _ hq]
  rw [Finset.sum_congr rfl fun b _ => hterm b, ← Finset.sum_mul, sum_range_ezExp k Nz]
  by_cases hd : (k : ℤ) ∣ Nz
  · obtain ⟨N', hN'⟩ := hd
    rw [if_pos ⟨N', hN'⟩, if_pos ⟨N', hN'⟩]
    have hquot : Nz / (k : ℤ) = N' := by
      rw [hN', Int.mul_ediv_cancel_left _ (by exact_mod_cast hk)]
    have hphase : ezExp (q * k) (m * Nz) = ezExp q (m * (Nz / k)) := by
      rw [hquot, hN', show m * ((k : ℤ) * N') = (k : ℤ) * (m * N') by ring,
        ezExp_scale_right q k _ hk]
    rw [hphase, ← mul_assoc, inv_mul_cancel₀ hkC, one_mul]
  · rw [if_neg hd, if_neg hd, zero_mul, mul_zero]

/-- **The completed companion identity.**  Combining the normal form with the
divisibility completion, the companion transform is

```
Ĉ_{j,ℓ}(m) = ∑_{u,A,d,p,h} coeff · (1/uA) ∑_{b mod uA} e_{q_ℓ uA}((b q_ℓ + m)[ℓ(dp−uh)−2]).
```

The hypothesis `uA > 0` (positivity of the completed modulus) is printed
explicitly. -/
theorem companionHat_completed [DecidableEq ι] (K : CompanionSkeleton ι) (ell : ℤ)
    (S : Finset ℤ) (q : ℕ) [NeZero q] (m : ℤ)
    (hpos : ∀ t ∈ K.T, 0 < K.u t * K.A t)
    (hS : ∀ t ∈ K.T, (K.u t * K.A t) ∣ Nval K ell t →
      Nval K ell t / (K.u t * K.A t) ∈ S) :
    companionHat K ell S q m
      = ∑ t ∈ K.T, K.coeff t *
          ((((K.u t * K.A t).toNat : ℕ) : ℂ))⁻¹ *
            ∑ b ∈ Finset.range ((K.u t * K.A t).toNat),
              ezExp (q * (K.u t * K.A t).toNat)
                (((b : ℤ) * q + m) * Nval K ell t) := by
  classical
  have hua : ∀ t ∈ K.T, K.u t * K.A t ≠ 0 := fun t ht => (hpos t ht).ne'
  rw [companionHat_normal_form K ell S q m hua hS]
  refine Finset.sum_congr rfl fun t ht => ?_
  set X : ℤ := K.u t * K.A t with hX
  have hXpos : 0 < X := hpos t ht
  set k : ℕ := X.toNat with hkdef
  have hkZ : (k : ℤ) = X := Int.toNat_of_nonneg hXpos.le
  have hkpos : 0 < k := by omega
  haveI : NeZero k := ⟨hkpos.ne'⟩
  have hkey := completed_quotient_phase q k m (Nval K ell t)
  rw [hkZ] at hkey
  conv_rhs => rw [mul_assoc]
  rw [hkey]
  split_ifs with hdvd
  · ring
  · ring

end DetLineCompanion
end CurrentProgramme
end TwinPrimeProject
