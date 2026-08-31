import Gate1B.CanonicalR9Comparison

/-!
# Gate 1B · packet-local comparison, global FM firewall, and the two-comparison adapter

**Exact algebra and one explicit arithmetic obstruction.**  Nothing analytic is
proved, and `b9Can` is *never* promoted to a global Ford–Maynard comparison
sequence.

## Contents

* §1 `R9CanonicalPacketComparison`: the packet-local admissibility structure,
  containing only what Gate 1B actually needs.  It has **no** pointwise
  positivity, **no** Euler multiplicativity and **no** global prime-mass field,
  and an explicit instance with a genuinely signed comparison sequence shows
  that positivity is not required;
* §2 `GlobalFMComparison`: a separate interface for a global Ford–Maynard
  comparison sequence.  `b9Can` is not asserted to inhabit it;
* §3 the **prime-mass obstruction**
  `ninefoldConvolution_prime_eq_zero_of_coordinate_support`: a ninefold
  convolution of coordinates whose supports avoid a prime `p` has coefficient
  `0` at `p`.  No asymptotic `Y^9` versus `Y L^C` comparison is hard-coded;
* §4 the exact two-comparison adapter identity
  `r9_twoComparison_adapter_identity`;
* §5 `R9CanonicalToGlobalAdapterBound`, an **interface only**, together with an
  explicit countermodel showing it is not automatic.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace R9Adapter

open Finset

/-! ## 1. Packet-local comparison admissibility -/

/-- **Packet-local** comparison admissibility for the canonical R9 packet.

The fields correspond exactly to the internal Gate 1B needs: an explicit
comparison sequence, the exact `c9 − b` decomposition, the zero mode,
fixed-depth moment interfaces, the factorial normalisation, the prime-power
owner and the local/nonzero owner separation.

Deliberately **absent**: pointwise positivity, Euler multiplicativity, global
prime mass. -/
structure R9CanonicalPacketComparison where
  /-- The source coefficient sequence. -/
  c9 : ℕ → ℂ
  /-- The packet-local (signed) comparison sequence. -/
  b : ℕ → ℂ
  /-- The comparison error. -/
  w : ℕ → ℂ
  /-- The exact `c9 − b` decomposition. -/
  w_def : w = fun n => c9 n - b n
  /-- The zero mode of the comparison. -/
  zeroMode : ℂ
  /-- The zero mode is defined, not postulated. -/
  zeroMode_def : Prop
  /-- The depth at which the moment interfaces are taken. -/
  momentDepth : ℕ
  /-- The fixed-depth moment interface (an obligation, never discharged here). -/
  fixedDepthMoments : Prop
  /-- Explicit factorial normalisation of the occupancy model. -/
  factorialNormalisation : Prop
  /-- The prime-power owner obligation. -/
  primePowerOwner : Prop
  /-- Separation of the local owner from the nonzero-frequency owner. -/
  localNonzeroOwnerSeparation : Prop

/-- **Signed comparison is allowed.**  An explicit packet-local comparison whose
sequence takes a negative value: pointwise positivity is genuinely not part of
the packet-local interface. -/
def signedPacketExample : R9CanonicalPacketComparison where
  c9 := fun _ => 0
  b := fun n => if n = 1 then -1 else 0
  w := fun n => 0 - (if n = 1 then -1 else 0)
  w_def := rfl
  zeroMode := 0
  zeroMode_def := True
  momentDepth := 9
  fixedDepthMoments := True
  factorialNormalisation := True
  primePowerOwner := True
  localNonzeroOwnerSeparation := True

theorem signedPacketExample_signed : signedPacketExample.b 1 = -1 := by
  simp [signedPacketExample]

/-! ## 2. Global Ford–Maynard comparison: a separate interface -/

/-- A **global** Ford–Maynard comparison sequence.  This is a different
interface from `R9CanonicalPacketComparison`, and `b9Can` is never asserted to
inhabit it. -/
structure GlobalFMComparison where
  /-- The global comparison sequence. -/
  bFM : ℕ → ℂ
  /-- Pointwise nonnegativity. -/
  nonneg : Prop
  /-- Dyadic support. -/
  dyadicSupport : Prop
  /-- Correct prime mass. -/
  primeMass : Prop
  /-- Generalized prime-factor distribution. -/
  primeFactorDistribution : Prop
  /-- The global Type-I/II contract. -/
  typeIIContract : Prop

/-! ## 3. The prime-mass obstruction -/

/-- Ordered nine-tuples of positive divisors of `N` with product `N`. -/
noncomputable def nineTuples (N : ℕ) : Finset (Fin 9 → ℕ) :=
  (Fintype.piFinset fun _ => N.divisors).filter fun v => ∏ i, v i = N

/-- The ninefold (Dirichlet) convolution coefficient at `N`, written out as a
finite sum over ordered nine-tuples. -/
noncomputable def nineConvAt (f : Fin 9 → ℕ → ℂ) (N : ℕ) : ℂ :=
  ∑ v ∈ nineTuples N, ∏ i, f i (v i)

/-- **Prime-mass obstruction (bare form).**  If every coordinate vanishes at the
prime `p`, the ninefold convolution coefficient at `p` is `0`. -/
theorem ninefoldConvolution_prime_eq_zero_of_coordinate_vanishing
    {p : ℕ} (hp : p.Prime) (f : Fin 9 → ℕ → ℂ) (hf : ∀ i, f i p = 0) :
    nineConvAt f p = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro v hv
  have hprod : ∏ i, v i = p := (Finset.mem_filter.mp hv).2
  have hex : ∃ i, v i = p := by
    by_contra hcon
    push_neg at hcon
    have hone : ∀ i : Fin 9, v i = 1 := by
      intro i
      have hdvd : v i ∣ p := hprod ▸ Finset.dvd_prod_of_mem v (Finset.mem_univ i)
      rcases (Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd) with h | h
      · exact h
      · exact absurd h (hcon i)
    have : ∏ i, v i = 1 := by simp [hone]
    rw [hprod] at this
    exact hp.one_lt.ne' this
  obtain ⟨i, hi⟩ := hex
  refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
  rw [hi, hf i]

/-- **Prime-mass obstruction (support form, §19 of the specification).**  If
`p` is prime, each coordinate is supported in an interval `(lo i, hi i]` that
excludes `p`, and `n₁⋯n₉ = p`, then the ninefold convolution coefficient at `p`
vanishes.  Consequently a ninefold convolution of interval-supported
coordinates cannot carry the prime mass demanded of a global Ford–Maynard
comparison sequence. -/
theorem ninefoldConvolution_prime_eq_zero_of_coordinate_support
    {p : ℕ} (hp : p.Prime) (f : Fin 9 → ℕ → ℂ) (lo hi : Fin 9 → ℕ)
    (hsupp : ∀ i n, f i n ≠ 0 → lo i < n ∧ n ≤ hi i)
    (hexcl : ∀ i, ¬ (lo i < p ∧ p ≤ hi i)) :
    nineConvAt f p = 0 := by
  refine ninefoldConvolution_prime_eq_zero_of_coordinate_vanishing hp f fun i => ?_
  by_contra hne
  exact hexcl i (hsupp i p hne)

/-- The status of `b9Can` as a global Ford–Maynard comparison sequence is
`FAIL by prime-mass obstruction`.  This is recorded as metadata; the Lean
content is the theorem above. -/
def b9Can_as_globalFM_status : String :=
  "b9Can AS GLOBAL FM COMPARISON: FAIL by prime-mass obstruction."

/-! ## 4. The two-comparison adapter identity -/

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- The adapter defect `Δ_adapter := b9Can − PR9(bFM)`. -/
def deltaAdapter (PR9 : V →ₗ[ℂ] V) (b9Can bFM : V) : V := b9Can - PR9 bFM

/-- **BOXED (§22 of the specification).**  Under `PR9(a) = c9`,

```
PR9(a − bFM) = (c9 − b9Can) + Δ_adapter.
```

Exact linear algebra; no analytic content. -/
theorem r9_twoComparison_adapter_identity (PR9 : V →ₗ[ℂ] V) (a bFM b9Can c9 : V)
    (ha : PR9 a = c9) :
    PR9 (a - bFM) = (c9 - b9Can) + deltaAdapter PR9 b9Can bFM := by
  rw [map_sub, ha, deltaAdapter]
  abel

/-! ## 5. The adapter bound: interface only -/

/-- **Interface (OPEN).**  The requirement that the adapter defect is small in
the compiler seminorm.  This is *not* proved anywhere; it is the residual
`R9-CANONICAL-TO-GLOBAL-COMPARISON-ADAPTER45`. -/
def R9CanonicalToGlobalAdapterBound
    (seminorm : V → ℝ) (PR9 : V →ₗ[ℂ] V) (b9Can bFM : V) (budget : ℝ) : Prop :=
  seminorm (deltaAdapter PR9 b9Can bFM) ≤ budget

/-- **Firewall.**  The adapter bound is not automatic: there are data for which
it fails.  Hence no consumer may assume it without being handed it. -/
theorem adapterBound_not_automatic :
    ∃ (seminorm : ℂ → ℝ) (PR9 : ℂ →ₗ[ℂ] ℂ) (b9Can bFM : ℂ) (budget : ℝ),
      ¬ R9CanonicalToGlobalAdapterBound seminorm PR9 b9Can bFM budget := by
  refine ⟨fun z => ‖z‖, LinearMap.id, 1, 0, 0, ?_⟩
  simp [R9CanonicalToGlobalAdapterBound, deltaAdapter]

end R9Adapter
end CurrentProgramme
end TwinPrimeProject
