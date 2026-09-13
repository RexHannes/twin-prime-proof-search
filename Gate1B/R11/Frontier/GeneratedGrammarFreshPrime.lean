/-
# Gate1B / R11 / Frontier : the unshifted fresh-prime convolution identity

Append-only module of the residue-aware / generated-grammar delta.  **Exact finite algebra
only.**

The repository's actual generated grammar (`V11FMPerronGrammar`, `V11GeneratedExpression`) is
*reused*, not re-created: the convolution used here is the repository's `dconv`, and the
corollary is stated for the repository's `semExpr` of the `conv` constructor.

Central identity, for squarefree `R` and a fresh prime `p ∤ R`:

```
(f ∗ g)(pR) = ∑_{e | R} [ f(pe) g(R/e) + f(e) g(pR/e) ] .
```

The evaluation point is `pR` — the **unshifted** predecessor.  Nothing here says anything about
`pR + 2`; see the evaluation-point firewall in `GeneratedGrammarVariation.lean`.
-/
import Mathlib
import RequestProject.NANC.Gate1B.V11GeneratedExpression

namespace Gate1B.R11.Frontier

open Finset TwinPrimeProject.Gate1BV11

/-! ## 1. The divisor set of a fresh-prime multiple -/

/-- For a prime `p` not dividing `R ≠ 0`, the divisors of `pR` are the divisors of `R` together
with their `p`-multiples. -/
theorem divisors_mul_prime {p R : ℕ} (hp : p.Prime) (hR : R ≠ 0) :
    (p * R).divisors = R.divisors ∪ R.divisors.image (fun e => p * e) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  ext d
  simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
  constructor
  · rintro ⟨hd, -⟩
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      exact Or.inr ⟨e, ⟨(mul_dvd_mul_iff_left hp0).mp hd, hR⟩, rfl⟩
    · have hcop : Nat.Coprime d p :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpd))
      exact Or.inl ⟨(Nat.Coprime.dvd_of_dvd_mul_left hcop hd), hR⟩
  · rintro (⟨hd, -⟩ | ⟨e, ⟨he, -⟩, rfl⟩)
    · exact ⟨Dvd.dvd.mul_left hd p, by positivity⟩
    · exact ⟨mul_dvd_mul_left p he, by positivity⟩

/-- The two pieces are disjoint. -/
theorem divisors_mul_prime_disjoint {p R : ℕ} (hpR : ¬ p ∣ R) :
    Disjoint R.divisors (R.divisors.image (fun e => p * e)) := by
  refine Finset.disjoint_left.mpr ?_
  rintro d hd hd'
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hd'
  exact hpR (dvd_trans (Dvd.intro e rfl) (Nat.mem_divisors.mp hd).1)

/-! ## 2. The fresh-prime convolution identity -/

/-- **The unshifted fresh-prime convolution identity.**  For a prime `p` not dividing `R ≠ 0`:

```
(f ∗ g)(pR) = ∑_{e | R} [ f(pe) g(R/e) + f(e) g(pR/e) ] .
```
-/
theorem dconv_fresh_prime (f g : ℕ → ℂ) {p R : ℕ} (hp : p.Prime) (hR : R ≠ 0)
    (hpR : ¬ p ∣ R) :
    dconv f g (p * R) = ∑ e ∈ R.divisors, (f (p * e) * g (R / e) + f e * g (p * R / e)) := by
  have hp0 : p ≠ 0 := hp.ne_zero
  have hinj : Set.InjOn (fun e => p * e) R.divisors := by
    intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) hab
  unfold dconv
  have hkey : ∀ e ∈ R.divisors, f (p * e) * g (p * R / (p * e)) = f (p * e) * g (R / e) := by
    intro e _
    rw [Nat.mul_div_mul_left R e (Nat.pos_of_ne_zero hp0)]
  rw [divisors_mul_prime hp hR,
    Finset.sum_union (divisors_mul_prime_disjoint hpR),
    Finset.sum_image hinj, Finset.sum_congr rfl hkey,
    Finset.sum_add_distrib, add_comm]

/-- The same identity for squarefree `R`, as banked in the research notes. -/
theorem dconv_fresh_prime_squarefree (f g : ℕ → ℂ) {p R : ℕ} (hp : p.Prime)
    (hR : Squarefree R) (hpR : ¬ p ∣ R) :
    dconv f g (p * R) = ∑ e ∈ R.divisors, (f (p * e) * g (R / e) + f e * g (p * R / e)) :=
  dconv_fresh_prime f g hp hR.ne_zero hpR

/-- The generated-grammar form: the identity for the `conv` constructor of the repository's
generated expressions. -/
theorem semExpr_conv_fresh_prime (e1 e2 : GenExpr) {p R : ℕ} (hp : p.Prime) (hR : R ≠ 0)
    (hpR : ¬ p ∣ R) :
    semExpr (.conv e1 e2) (p * R)
      = ∑ e ∈ R.divisors, (semExpr e1 (p * e) * semExpr e2 (R / e)
          + semExpr e1 e * semExpr e2 (p * R / e)) :=
  dconv_fresh_prime _ _ hp hR hpR

end Gate1B.R11.Frontier
