/-
# Gate1B / R11 / Frontier : the centered decomposition of the physical divisor source

Append-only module of the minimal-gap-kernel delta.

For the physical divisor source we fix, over a declared finite `d`-range (odd `d`) and a declared
finite `n`-range:

```
L_C    = RAW progression contribution,
MAIN_C = reduced-residue principal average,
E_C    = centered discrepancy,
```

and kernel-prove the **exact finite identity** `L_C = E_C + MAIN_C`.

The current exact centered source is

```
E_R11 = ∑_{C, d odd} μ(d) ∑_n Ω_C(n) 1_{z_C < d ≤ n+2} log((n+2)/d)
          · [ 1_{n ≡ −2 (mod d)} − 1_{gcd(n,d)=1}/φ(d) ].
```

This **definition** is kernel-proved (it is a definition plus the reassembly identity above); the
desired **estimate** remains OPEN and is recorded as a proposition that is never inhabited.
-/
import Gate1B.R11.Frontier.PrincipalTailInterface

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- The common weight `1_{z<d≤n+2} log((n+2)/d)` of the three charts. -/
noncomputable def sourceWeight (z : ℝ) (d n : ℕ) : ℝ :=
  if z < (d : ℝ) ∧ d ≤ n + 2 then Real.log (((n + 2 : ℕ) : ℝ) / (d : ℝ)) else 0

/-- The progression indicator `1_{n ≡ −2 (mod d)}`. -/
noncomputable def progIndicator (d n : ℕ) : ℝ := if d ∣ n + 2 then 1 else 0

/-- The reduced-residue principal weight `1_{gcd(n,d)=1}/φ(d)`. -/
noncomputable def principalIndicator (d n : ℕ) : ℝ :=
  if Nat.gcd n d = 1 then 1 / (Nat.totient d : ℝ) else 0

/-- `L_C`: the raw progression contribution. -/
noncomputable def rawProgression (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ d ∈ Ds with ¬ (2 ∣ d), (μ d : ℝ) *
    ∑ n ∈ Ns, Ω n * sourceWeight z d n * progIndicator d n

/-- `MAIN_C`: the reduced-residue principal average. -/
noncomputable def principalAverage (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ d ∈ Ds with ¬ (2 ∣ d), (μ d : ℝ) *
    ∑ n ∈ Ns, Ω n * sourceWeight z d n * principalIndicator d n

/-- `E_C`: the centered discrepancy. -/
noncomputable def centeredDiscrepancy (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) : ℝ :=
  ∑ d ∈ Ds with ¬ (2 ∣ d), (μ d : ℝ) *
    ∑ n ∈ Ns, Ω n * sourceWeight z d n * (progIndicator d n - principalIndicator d n)

/-- **Exact centered decomposition.**  `L_C = E_C + MAIN_C`. -/
theorem raw_eq_centered_add_principal (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) :
    rawProgression Ds Ns Ω z
      = centeredDiscrepancy Ds Ns Ω z + principalAverage Ds Ns Ω z := by
  unfold rawProgression centeredDiscrepancy principalAverage
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-! ## The current exact centered source `E_R11` -/

variable {ι : Type*}

/-- `E_R11`: the exact centered source of the current coordinate, summed over the charts. -/
noncomputable def E_R11 (Cs : Finset ι) (Ds Ns : Finset ℕ) (Ω : ι → ℕ → ℝ) (z : ι → ℝ) : ℝ :=
  ∑ C ∈ Cs, centeredDiscrepancy Ds Ns (Ω C) (z C)

/-- The chartwise reassembly of the total source: raw = centered + principal, chart by chart. -/
theorem total_raw_eq_centered_add_principal (Cs : Finset ι) (Ds Ns : Finset ℕ)
    (Ω : ι → ℕ → ℝ) (z : ι → ℝ) :
    ∑ C ∈ Cs, rawProgression Ds Ns (Ω C) (z C)
      = E_R11 Cs Ds Ns Ω z + ∑ C ∈ Cs, principalAverage Ds Ns (Ω C) (z C) := by
  unfold E_R11
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun C _ => raw_eq_centered_add_principal Ds Ns (Ω C) (z C)

/-- The desired estimate for the centered source.  **OPEN**: a proposition, never inhabited in
this layer, never an axiom. -/
def CenteredSourceEstimate (Cs : Finset ι) (Ds Ns : Finset ℕ) (Ω : ι → ℕ → ℝ) (z : ι → ℝ)
    (x L S0 C₀ : ℝ) : Prop :=
  |E_R11 Cs Ds Ns Ω z| ≤ C₀ * x * L ^ (-S0)

/-- The *only* legal downstream use: the centered estimate plus the principal estimate bound the
raw source.  The hypotheses are explicit; nothing is inhabited here. -/
theorem raw_bound_of_centered_and_principal (Cs : Finset ι) (Ds Ns : Finset ℕ)
    (Ω : ι → ℕ → ℝ) (z : ι → ℝ) {B₁ B₂ : ℝ}
    (hE : |E_R11 Cs Ds Ns Ω z| ≤ B₁)
    (hM : |∑ C ∈ Cs, principalAverage Ds Ns (Ω C) (z C)| ≤ B₂) :
    |∑ C ∈ Cs, rawProgression Ds Ns (Ω C) (z C)| ≤ B₁ + B₂ := by
  rw [total_raw_eq_centered_add_principal]
  exact le_trans (abs_add_le _ _) (add_le_add hE hM)

end Gate1B.R11.Frontier
