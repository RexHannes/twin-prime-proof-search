import RequestProject.NANC.Gate1BDet2.ModulusSignCollapse

/-!
# Gate 1B / determinant-2 bank, Module 37: full-face fixed packet

Only what is *source-legal* is banked here.

For a clean squarefree `q` and routed cell weights `ρ_c(p, q)`:

  `λ_c(q) = ∑_{p ∣ q} μ(q/p) w(p) ρ_c(p, q)`,

and on squarefree support the sign collapses (Module 1's cofactor identity is
reused, not reproved):

  `λ_c(q) = − μ(q) L_c(q)`,   `L_c(q) = ∑_{p ∣ q} w(p) ρ_c(p, q)`.

If a *finite family* of cells `C` is a partition of unity over the exact fixed
switched packet, `∑_{c ∈ C} ρ_c(p, q) = ρ_sw(p, q)`, then

  `∑_{c ∈ C} λ_c(q) = − μ(q) L_sw(q)`.

**`L_sw(q) = log q` is deliberately NOT proved**, and the statement that the
direct/switched/skeleton routing exhausts the prime-divisor face family is left
as the ordinary uninhabited interface Prop `SourceFaceCompleteness`, with a
guard showing fixed-switched recombination does not imply it.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace FullFace

open Finset ArithmeticFunction ArithmeticFunction.Moebius

variable {R : Type*} [CommRing R]

/-! ## 1. Routed face coefficients on squarefree support -/

/-- The routed face sum `L_c(q) = ∑_{p ∣ q} w(p) ρ_c(p, q)`. -/
def LRouted (w : ℕ → R) (rho : ℕ → ℕ → R) (q : ℕ) : R :=
  ∑ p ∈ q.primeFactors, w p * rho p q

/-- The routed Möbius-weighted face coefficient
`λ_c(q) = ∑_{p ∣ q} μ(q/p) w(p) ρ_c(p, q)`. -/
def lambdaRouted (w : ℕ → R) (rho : ℕ → ℕ → R) (q : ℕ) : R :=
  ∑ p ∈ q.primeFactors, ((μ (q / p) : ℤ) : R) * (w p * rho p q)

/-- **Face sign collapse.**  On squarefree support, `λ_c(q) = − μ(q) L_c(q)`. -/
theorem lambdaRouted_eq_neg_moebius_mul_LRouted {w : ℕ → R} {rho : ℕ → ℕ → R} {q : ℕ}
    (hq : Squarefree q) :
    lambdaRouted w rho q = -((μ q : ℤ) : R) * LRouted w rho q := by
  unfold lambdaRouted LRouted
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun p hp => ?_)
  rw [Nat.mem_primeFactors] at hp
  rw [moebius_div_prime_of_squarefree hq hp.1 hp.2.1]
  push_cast
  ring

/-! ## 2. Finite cell families and the fixed switched packet -/

/-- **Partition of unity over the fixed switched packet.**  If the finite family
`C` of cells satisfies `∑_{c ∈ C} ρ_c(p, q) = ρ_sw(p, q)` for every `p`, then
the routed coefficients recombine into the switched packet coefficient. -/
theorem sum_lambdaRouted_eq_lambdaRouted_switched {ι : Type*} (C : Finset ι)
    (w : ℕ → R) (rho : ι → ℕ → ℕ → R) (rhoSw : ℕ → ℕ → R) (q : ℕ)
    (hpart : ∀ p, ∑ c ∈ C, rho c p q = rhoSw p q) :
    ∑ c ∈ C, lambdaRouted w (rho c) q = lambdaRouted w rhoSw q := by
  unfold lambdaRouted
  have hcomm : ∑ c ∈ C, ∑ p ∈ q.primeFactors, ((μ (q / p) : ℤ) : R) * (w p * rho c p q)
      = ∑ p ∈ q.primeFactors, ∑ c ∈ C, ((μ (q / p) : ℤ) : R) * (w p * rho c p q) :=
    Finset.sum_comm
  rw [hcomm]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [← hpart p, Finset.mul_sum, Finset.mul_sum]

/-- **Fixed switched packet recombination.**  On squarefree support,
`∑_{c ∈ C} λ_c(q) = − μ(q) L_sw(q)`. -/
theorem sum_lambdaRouted_eq_neg_moebius_mul_LSwitched {ι : Type*} (C : Finset ι)
    (w : ℕ → R) (rho : ι → ℕ → ℕ → R) (rhoSw : ℕ → ℕ → R) {q : ℕ}
    (hq : Squarefree q) (hpart : ∀ p, ∑ c ∈ C, rho c p q = rhoSw p q) :
    ∑ c ∈ C, lambdaRouted w (rho c) q = -((μ q : ℤ) : R) * LRouted w rhoSw q := by
  rw [sum_lambdaRouted_eq_lambdaRouted_switched C w rho rhoSw q hpart,
    lambdaRouted_eq_neg_moebius_mul_LRouted hq]

/-! ## 3. Interface: source face completeness -/

/-- **OPEN INTERFACE.**  The routed face family (direct / switched / skeleton)
really exhausts the complete prime-divisor face family of `q`.  Never
inhabited. -/
def SourceFaceCompleteness (routedFaces fullFaces : Finset ℕ) : Prop :=
  routedFaces = fullFaces

/-- **GUARD.**  Fixed-switched recombination is an exact identity that holds for
*any* routed family; it therefore cannot imply source face completeness.  A
routed family may miss prime-divisor faces: for `q = 6`, the routed set `{2}` is
not the full face set `{2, 3}`, while the recombination identity above still
holds. -/
theorem fixed_switched_recombination_does_not_imply_full_face_completeness :
    ∃ routedFaces fullFaces : Finset ℕ,
      (∀ (ι : Type) (C : Finset ι) (w : ℕ → ℤ) (rho : ι → ℕ → ℕ → ℤ)
          (rhoSw : ℕ → ℕ → ℤ) (q : ℕ), Squarefree q →
          (∀ p, ∑ c ∈ C, rho c p q = rhoSw p q) →
          ∑ c ∈ C, lambdaRouted w (rho c) q = -((μ q : ℤ) : ℤ) * LRouted w rhoSw q)
      ∧ ¬ SourceFaceCompleteness routedFaces fullFaces := by
  refine ⟨{2}, {2, 3}, ?_, ?_⟩
  · intro ι C w rho rhoSw q hq hpart
    exact sum_lambdaRouted_eq_neg_moebius_mul_LSwitched C w rho rhoSw hq hpart
  · unfold SourceFaceCompleteness
    decide

end FullFace
end Gate1BDet2
end TwinPrimeProject
