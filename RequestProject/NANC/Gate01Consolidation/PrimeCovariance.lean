import RequestProject.NANC.Gate01Consolidation.CRTCentering

/-!
# BANK H / I — the prime-centered covariance kernel and the second moment

For a finite set `P` of moduli (in practice primes; the algebra never needs
primality) and the natural centering `ρ_p(y) = 1_{p ∣ y} − 1/p` put

`K_P(u, v) = ∑_{p ∈ P} ρ_p(u) ρ_p(v)`.

Proved here:

* **KP**      the pointwise expansion of the kernel;
* **KP-DIAG** `K_P(Y, Y) = ∑_{p ∈ P, p ∣ Y} (1 − 2/p) + ∑_{p ∈ P} 1/p²`;
* **KP-OFF**  the four-term expansion of `K_P(u, v)`;
* **P2MOM**   `∑_{p ∈ P} |B_p|² = ∑_{i,j} A_i conj(A_j) K_P(Y_i, Y_j)` for
  `B_p = ∑_i A_i ρ_p(Y_i)`.

```text
PRIME_CENTERED_SECOND_MOMENT_IDENTITY = PROVED
PRIME_CENTERED_OFF_DIAGONAL_BOUND     = OPEN ANALYTIC
```

No analytic bound on the right-hand side of P2MOM is asserted.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- The prime-centered covariance kernel `K_P(u,v) = ∑_{p ∈ P} ρ_p(u) ρ_p(v)`. -/
noncomputable def covKernel (P : Finset ℕ) (u v : ℕ) : ℝ :=
  ∑ p ∈ P, rho p u * rho p v

/-- **KP.**  The pointwise expansion of the covariance kernel. -/
theorem covKernel_expand (P : Finset ℕ) (u v : ℕ) :
    covKernel P u v
      = ∑ p ∈ P, ((if p ∣ u then (1 : ℝ) else 0) * (if p ∣ v then (1 : ℝ) else 0)
          - (if p ∣ u then (1 : ℝ) else 0) / p
          - (if p ∣ v then (1 : ℝ) else 0) / p
          + 1 / (p : ℝ) ^ 2) := by
  unfold covKernel rho
  refine Finset.sum_congr rfl (fun p _ => ?_)
  field_simp
  ring

/-- **KP-OFF.**  The four-term expansion of the kernel.  (No hypothesis `u ≠ v`
is needed: the identity is valid for all `u, v`.) -/
theorem covKernel_off (P : Finset ℕ) (u v : ℕ) :
    covKernel P u v
      = (∑ _p ∈ P.filter (fun p => p ∣ u ∧ p ∣ v), (1 : ℝ))
        - (∑ p ∈ P.filter (fun p => p ∣ u), 1 / (p : ℝ))
        - (∑ p ∈ P.filter (fun p => p ∣ v), 1 / (p : ℝ))
        + ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  rw [covKernel_expand, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hu : p ∣ u <;> by_cases hv : p ∣ v <;> simp [hu, hv]

/-- **KP-DIAG.**  The diagonal of the kernel. -/
theorem covKernel_diag (P : Finset ℕ) (Y : ℕ) :
    covKernel P Y Y
      = (∑ p ∈ P.filter (fun p => p ∣ Y), (1 - 2 / (p : ℝ)))
        + ∑ p ∈ P, 1 / (p : ℝ) ^ 2 := by
  rw [covKernel_expand, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases hu : p ∣ Y
  · simp [hu]; ring
  · simp [hu]

/-! ## BANK I — the exact second moment expansion -/

/-- The centered linear form `B_p = ∑_i A_i ρ_p(Y_i)`. -/
noncomputable def centeredForm {ι : Type*} (I : Finset ι) (A : ι → ℂ) (Y : ι → ℕ)
    (p : ℕ) : ℂ :=
  ∑ i ∈ I, A i * (rho p (Y i) : ℂ)

/-- **P2MOM.**  The exact second-moment expansion.  Pure finite algebra; no
analytic bound on the right-hand side is asserted. -/
theorem sum_normSq_centeredForm {ι : Type*} (I : Finset ι) (P : Finset ℕ)
    (A : ι → ℂ) (Y : ι → ℕ) :
    ∑ p ∈ P, centeredForm I A Y p * (starRingEnd ℂ) (centeredForm I A Y p)
      = ∑ i ∈ I, ∑ j ∈ I, A i * (starRingEnd ℂ) (A j) * (covKernel P (Y i) (Y j) : ℂ) := by
  have hswap : ∀ p ∈ P,
      centeredForm I A Y p * (starRingEnd ℂ) (centeredForm I A Y p)
        = ∑ i ∈ I, ∑ j ∈ I,
            A i * (starRingEnd ℂ) (A j) * ((rho p (Y i) : ℂ) * (rho p (Y j) : ℂ)) := by
    intro p _
    unfold centeredForm
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    simp only [map_mul, Complex.conj_ofReal]
    ring
  rw [Finset.sum_congr rfl hswap, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold covKernel
  push_cast
  rw [Finset.mul_sum]

/-- The real form of P2MOM: the second moment is the Hermitian form of the
kernel. -/
theorem sum_normSq_centeredForm_norm {ι : Type*} (I : Finset ι) (P : Finset ℕ)
    (A : ι → ℂ) (Y : ι → ℕ) :
    (∑ p ∈ P, (Complex.normSq (centeredForm I A Y p) : ℂ))
      = ∑ i ∈ I, ∑ j ∈ I, A i * (starRingEnd ℂ) (A j) * (covKernel P (Y i) (Y j) : ℂ) := by
  rw [← sum_normSq_centeredForm I P A Y]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Complex.mul_conj]

end Gate01Consolidation
end TwinPrimeProject
