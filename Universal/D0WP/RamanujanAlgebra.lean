/-
# Universal / D0WP — squarefree Ramanujan algebra

**Status of this module: KERNEL_PROVED exact algebra.**

The centering interface needs the exact normalised Ramanujan ratio

```
c_q(h) / φ(q) = μ(q/(q,h)) / φ(q/(q,h))         (q squarefree).
```

Here `c_q(h)` is taken in its **Hölder divisor form**

```
c_q(h) = Σ_{d ∣ (q,h)} d · μ(q/d),
```

which is the form the source ledger uses.  The identification of this divisor
form with the additive-character sum `Σ_{a ∈ (ℤ/q)ˣ} e_q(ah)` is *not* claimed
here; it is a separate classical statement and is not needed for the algebra
below.

No asymptotic size bound is claimed: only the exact identity.
-/
import Mathlib

namespace Universal.D0WP

open ArithmeticFunction Finset
open scoped ArithmeticFunction.Moebius

/-- Ramanujan sum in Hölder divisor form. -/
noncomputable def ramanujanHolder (q h : ℕ) : ℤ :=
  ∑ d ∈ (Nat.gcd q h).divisors, (d : ℤ) * μ (q / d)

/-- Möbius inversion of `Σ_{d ∣ n} φ(d) = n`, in the form `Σ_{d ∣ g} d μ(g/d) = φ(g)`. -/
theorem totient_moebius_sum (g : ℕ) (hg : 0 < g) :
    ∑ d ∈ g.divisors, (d : ℤ) * μ (g / d) = (g.totient : ℤ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq
      (f := fun i => (i.totient : ℤ)) (g := fun i => (i : ℤ))).mp ?_ g hg
  · rw [Nat.sum_divisorsAntidiagonal' (f := fun a b => (μ a : ℤ) • (b : ℤ))] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    simp [mul_comm]
  · intro m _
    exact_mod_cast congrArg (fun t : ℕ => (t : ℤ)) (Nat.sum_totient m)

/-- **Squarefree Ramanujan identity (kernel-proved).** -/
theorem ramanujan_squarefree (q h : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    ramanujanHolder q h = (μ (q / Nat.gcd q h) : ℤ) * ((Nat.gcd q h).totient : ℤ) := by
  set g := Nat.gcd q h with hgdef
  have hgdvd : g ∣ q := Nat.gcd_dvd_left q h
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left h hq
  have hqg : q = (q / g) * g := (Nat.div_mul_cancel hgdvd).symm
  have hcop : Nat.Coprime g (q / g) := by
    apply Nat.coprime_of_squarefree_mul
    rw [← Nat.mul_div_cancel' hgdvd] at hsq
    exact hsq
  unfold ramanujanHolder
  rw [← hgdef]
  have hterm : ∀ d ∈ g.divisors, (d : ℤ) * μ (q / d)
      = (μ (q / g) : ℤ) * ((d : ℤ) * μ (g / d)) := by
    intro d hd
    have hdg : d ∣ g := (Nat.mem_divisors.mp hd).1
    have hqd : q / d = (q / g) * (g / d) := by
      conv_lhs => rw [hqg]
      exact Nat.mul_div_assoc _ hdg
    rw [hqd]
    have hc : Nat.Coprime (q / g) (g / d) :=
      Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdg) hcop.symm
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, totient_moebius_sum g hg0]

/-- **Normalised Ramanujan ratio (kernel-proved).**  For squarefree `q`,

```
c_q(h)/φ(q) = μ(q/(q,h))/φ(q/(q,h)).
```
-/
theorem ramanujan_ratio_squarefree (q h : ℕ) (hq : 0 < q) (hsq : Squarefree q) :
    (ramanujanHolder q h : ℚ) / (q.totient : ℚ)
      = (μ (q / Nat.gcd q h) : ℚ) / ((q / Nat.gcd q h).totient : ℚ) := by
  set g := Nat.gcd q h with hgdef
  have hgdvd : g ∣ q := Nat.gcd_dvd_left q h
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left h hq
  have hcop : Nat.Coprime g (q / g) := by
    apply Nat.coprime_of_squarefree_mul
    rw [← Nat.mul_div_cancel' hgdvd] at hsq
    exact hsq
  have hqfac : q = g * (q / g) := (Nat.mul_div_cancel' hgdvd).symm
  have htot : q.totient = g.totient * (q / g).totient := by
    conv_lhs => rw [hqfac]
    exact Nat.totient_mul hcop
  have hgtot : (0 : ℚ) < (g.totient : ℚ) := by
    exact_mod_cast Nat.totient_pos.mpr hg0
  have hmtot : (0 : ℚ) < ((q / g).totient : ℚ) := by
    have : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq hgdvd) hg0
    exact_mod_cast Nat.totient_pos.mpr this
  have hnum : (ramanujanHolder q h : ℚ)
      = (μ (q / g) : ℚ) * (g.totient : ℚ) := by
    have := ramanujan_squarefree q h hq hsq
    rw [← hgdef] at this
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) this
  rw [hnum, htot]
  push_cast
  field_simp

end Universal.D0WP
