/-
# Gate1B / R11 / Frontier : the prime-kernel bridge

Append-only module of the minimal-gap-kernel delta.

A **prime kernel** is a minimal bad-gap kernel that happens to be a prime; kernel-proved here:

```
p prime  →  (IsMinKernel x p  ↔  x < p·p),        i.e.  √x < p.
```

For `M = p·m ≤ x` with such a `p` the bad-gap source is the exact finite formula

```
H_bad(z,x,M) = − ∑_{e | m, e > z/p} μ(e) log(m/e),
```

which is the exceptional bridge in the range `√x < p ≤ z` (there the threshold does **not**
collapse the fibre to `Λ`).  The kernel-proved range facts for the short variable `e` are
`e ≤ m`, `m·p ≤ x`, `m < p` and `m² < x`.

The research exponent `x^{1/22-ε}` is recorded **only** as a range interface: the real
inequality `e ≤ z/√x` is kernel-proved *conditionally* on the explicit hypothesis
`x^{3/2} ≤ z·p`, and the exponent proposition itself is never inhabited.
-/
import Gate1B.R11.Frontier.BadGapFibreContraction

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## 1. Prime kernels -/

theorem Fgap_prime {p : ℕ} (hp : p.Prime) : Fgap p = p * p := by
  refine le_antisymm ?_ ?_
  · refine (Fgap_le_iff hp.ne_zero (by nlinarith [hp.two_le]) ).2 fun v hv hv1 => ?_
    have : v = p := ((Nat.dvd_prime hp).1 hv).resolve_left (by omega)
    subst this
    rw [Nat.Prime.minFac_eq hp]
  · have := le_Fgap hp.ne_zero (dvd_refl p) hp.one_lt
    rwa [Nat.Prime.minFac_eq hp] at this

/-- **Prime-kernel characterisation.** -/
theorem isMinKernel_prime_iff {x p : ℕ} (hx : 1 ≤ x) (hp : p.Prime) :
    IsMinKernel x p ↔ x < p * p := by
  constructor
  · intro h
    have := h.2.1
    rwa [Fgap_prime hp] at this
  · intro hlt
    refine ⟨hp.squarefree, by rwa [Fgap_prime hp], fun t ht htne => ?_⟩
    have : t = 1 := ((Nat.dvd_prime hp).1 ht).resolve_right htne
    subst this
    simpa using hx

/-! ## 2. The bridge source formula -/

/-- **Prime-kernel bridge (exact finite source).**  For `M = p·m ≤ x` with `p` a prime kernel,
the bad-gap source is minus the short-divisor sum over `e | m`, `e > z/p`. -/
theorem Hbad_prime_kernel {z : ℝ} {x M p m : ℕ} (hx : 1 ≤ x) (hM0 : M ≠ 0) (hMx : M ≤ x)
    (hp : p.Prime) (hpx : x < p * p) (hpm : p * m = M) :
    Hbad z x M = - ∑ e ∈ m.divisors,
      (if z / (p : ℝ) < (e : ℝ) then (μ e : ℝ) * Real.log ((m : ℝ) / (e : ℝ)) else 0) := by
  have hker : IsMinKernel x p := (isMinKernel_prime_iff hx hp).2 hpx
  rw [Hbad_contraction hx hM0 hMx hker hpm, ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  rw [Hdiv]
  simp [neg_mul, one_mul]

/-! ## 3. Range facts for the short variable -/

section Range

variable {x p m : ℕ}

/-- The cofactor of a prime kernel is smaller than the kernel. -/
theorem prime_kernel_cofactor_lt (hpx : x < p * p) (hMx : p * m ≤ x) :
    m < p := by
  by_contra hcon
  push_neg at hcon
  have : p * p ≤ p * m := Nat.mul_le_mul_left p hcon
  omega

/-- The cofactor of a prime kernel satisfies `m² < x`. -/
theorem prime_kernel_cofactor_sq_lt (hpx : x < p * p) (hMx : p * m ≤ x)
    (hm : 0 < m) : m * m < x := by
  have h1 : m < p := prime_kernel_cofactor_lt hpx hMx
  calc m * m < p * m := by exact Nat.mul_lt_mul_of_lt_of_le h1 (le_refl m) hm
    _ ≤ x := hMx

/-- Every short divisor is at most the cofactor. -/
theorem short_divisor_le {e : ℕ} (hm : 0 < m) (he : e ∣ m) : e ≤ m :=
  Nat.le_of_dvd hm he

/-- **Range interface** (conditional).  Under the explicit real hypothesis `x^{3/2} ≤ z·p`, every
short divisor satisfies `e ≤ z/√x`. -/
theorem short_divisor_le_interface {z : ℝ} {e : ℕ} (hx : 0 < x) (hp : 0 < p) (hm : 0 < m)
    (he : e ∣ m) (hMx : p * m ≤ x) (hint : (x : ℝ) * Real.sqrt x ≤ z * p) :
    (e : ℝ) ≤ z / Real.sqrt x := by
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hsq : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hxR
  have hem : (e : ℝ) ≤ (m : ℝ) := by exact_mod_cast short_divisor_le hm he
  have hpm : (p : ℝ) * (m : ℝ) ≤ (x : ℝ) := by exact_mod_cast hMx
  have hmx : (m : ℝ) ≤ (x : ℝ) / (p : ℝ) := by
    rw [le_div_iff₀ hpR]; linarith [hpm]
  have hkey : (x : ℝ) / (p : ℝ) ≤ z / Real.sqrt x := by
    rw [div_le_div_iff₀ hpR hsq]
    calc (x : ℝ) * Real.sqrt x ≤ z * (p : ℝ) := hint
      _ = z * (p : ℝ) := rfl
  linarith [hem, hmx, hkey]

end Range

/-! ## 4. The research exponent, as an interface only -/

/-- The research exponent of the bridge range, recorded as a *proposition*.  It is an interface:
nothing in this layer inhabits it. -/
def BridgeExponentRange (x : ℕ) (z epsSafe : ℝ) : Prop :=
  z / Real.sqrt x ≤ (x : ℝ) ^ ((1 : ℝ) / 22 - epsSafe)

/-- The bridge exponent range is a hypothesis, never a theorem of this layer: if it is assumed,
it transports to the short divisors, and that is the *only* way it is used. -/
theorem bridge_exponent_transport {x p m : ℕ} {z epsSafe : ℝ} {e : ℕ} (hx : 0 < x) (hp : 0 < p)
    (hm : 0 < m) (he : e ∣ m) (hMx : p * m ≤ x) (hint : (x : ℝ) * Real.sqrt x ≤ z * p)
    (hrange : BridgeExponentRange x z epsSafe) :
    (e : ℝ) ≤ (x : ℝ) ^ ((1 : ℝ) / 22 - epsSafe) :=
  le_trans (short_divisor_le_interface hx hp hm he hMx hint) hrange

end Gate1B.R11.Frontier
