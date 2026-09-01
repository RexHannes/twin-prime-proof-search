import Gate1B.HStarK0J0SourceGrammar

/-!
# Gate 1B · HSTAR-K0J0-DETERMINANT-SHELL

**Exact arithmetic and exact finite reindexing only.  No Gate 1B analytic
estimate is proved or assumed.**

## Contents

* §1 the shell variables `d, p, r, m, n` and the shell assignment
  `q = d·p`, `ℓ = r`, `u = m`, `v = n`;
* §2 the determinant identity

  `d·p·r = m·n + 2  →  q·ℓ − u·v = 2`,

  both in `ℤ` and in truncated `ℕ` form, together with the converse and the
  fixed shift `2` (never averaged);
* §3 the exact modulus-coefficient reindexing at the finite/algebraic level:
  a sum over moduli `q ≤ K` of a divisor-pair coefficient equals the
  corresponding sum over the factor pairs `(d, p)`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset
open scoped BigOperators

/-! ## 1. Shell variables -/

/-- The determinant-shell data of the HSTAR first parent. -/
structure DeterminantShellData where
  d : ℕ
  p : ℕ
  r : ℕ
  m : ℕ
  n : ℕ
  deriving DecidableEq, Repr

namespace DeterminantShellData

variable (S : DeterminantShellData)

/-- The shell modulus `q = d·p`. -/
def q : ℕ := S.d * S.p

/-- The shell multiplier `ℓ = r`. -/
def ell : ℕ := S.r

/-- The shell variable `u = m`. -/
def u : ℕ := S.m

/-- The shell variable `v = n`. -/
def v : ℕ := S.n

/-- The shell relation `d·p·r = m·n + 2`. -/
def ShellRelation : Prop := S.d * S.p * S.r = S.m * S.n + 2

/-- The determinant relation `q·ℓ − u·v = 2`, stated in `ℤ`. -/
def DeterminantRelation : Prop := (S.q : ℤ) * S.ell - (S.u : ℤ) * S.v = 2

end DeterminantShellData

/-! ## 2. The determinant identity -/

/-- **HSTAR-K0J0-DETERMINANT-SHELL.**  `d·p·r = m·n + 2` implies
`q·ℓ − u·v = 2` for the shell assignment `q = d·p`, `ℓ = r`, `u = m`,
`v = n`.  The shift is the literal fixed `2`. -/
theorem determinant_shell (S : DeterminantShellData) (h : S.ShellRelation) :
    S.DeterminantRelation := by
  have h' : ((S.d * S.p * S.r : ℕ) : ℤ) = ((S.m * S.n + 2 : ℕ) : ℤ) := by exact_mod_cast h
  simp only [DeterminantShellData.DeterminantRelation, DeterminantShellData.q,
    DeterminantShellData.ell, DeterminantShellData.u, DeterminantShellData.v]
  push_cast at h' ⊢
  linarith

/-- The converse: the determinant relation forces the shell relation. -/
theorem shell_of_determinant (S : DeterminantShellData) (h : S.DeterminantRelation) :
    S.ShellRelation := by
  simp only [DeterminantShellData.DeterminantRelation, DeterminantShellData.q,
    DeterminantShellData.ell, DeterminantShellData.u, DeterminantShellData.v] at h
  push_cast at h
  have : ((S.d * S.p * S.r : ℕ) : ℤ) = ((S.m * S.n + 2 : ℕ) : ℤ) := by push_cast; linarith
  exact_mod_cast this

/-- Bare numeric form of the shell identity (no structure wrapper). -/
theorem determinant_shell_raw {d p r m n : ℕ} (h : d * p * r = m * n + 2) :
    ((d * p : ℕ) : ℤ) * r - (m : ℤ) * n = 2 :=
  determinant_shell ⟨d, p, r, m, n⟩ h

/-- `ℕ`-form with truncated subtraction: the determinant is `2` on the nose. -/
theorem determinant_shell_nat {d p r m n : ℕ} (h : d * p * r = m * n + 2) :
    (d * p) * r - m * n = 2 := by
  rw [Nat.mul_assoc] at h ⊢
  omega

/-! ## 3. Exact modulus-coefficient reindexing -/

/-- The finite set of factor pairs `(d, p)` with `d·p ≤ K`. -/
def factorPairSet (K : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 K) ×ˢ (Finset.Icc 1 K)).filter (fun p => 1 ≤ p.1 * p.2 ∧ p.1 * p.2 ≤ K)

/-- **Exact divisor-pair reindexing.**  Summing a coefficient over all moduli
`N ≤ K` and all ordered factorisations of `N` is the same as summing over all
factor pairs `(d, p)` with `d·p ≤ K`. -/
theorem sum_divisorPair_reindex (K : ℕ) (Φ : ℕ → ℕ → ℂ) :
    ∑ N ∈ Finset.Icc 1 K, ∑ x ∈ Nat.divisorsAntidiagonal N, Φ x.1 x.2 =
      ∑ x ∈ factorPairSet K, Φ x.1 x.2 := by
  classical
  rw [Finset.sum_sigma']
  refine (Finset.sum_nbij' (fun x => (⟨x.1 * x.2, x⟩ : (_ : ℕ) × (ℕ × ℕ)))
    (fun s => s.2) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨d, p⟩ hx
    simp only [factorPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨hd1, hdK⟩, hp1, hpK⟩, h1, hK⟩ := hx
    have hne : d * p ≠ 0 := by omega
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨h1, hK⟩,
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, hne⟩⟩
  · rintro ⟨N, d, p⟩ hs
    simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisorsAntidiagonal] at hs
    obtain ⟨⟨hN1, hNK⟩, hprod, hN0⟩ := hs
    have hd1 : 1 ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exfalso; rw [h, Nat.zero_mul] at hprod; omega
      · exact h
    have hp1 : 1 ≤ p := by
      rcases Nat.eq_zero_or_pos p with h | h
      · exfalso; rw [h, Nat.mul_zero] at hprod; omega
      · exact h
    have hdN : d ≤ N := by
      have : d * 1 ≤ d * p := Nat.mul_le_mul_left d hp1
      omega
    have hpN : p ≤ N := by
      have : 1 * p ≤ d * p := Nat.mul_le_mul_right p hd1
      omega
    simp only [factorPairSet, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
    exact ⟨⟨⟨hd1, by omega⟩, hp1, by omega⟩, by omega, by omega⟩
  · rintro ⟨d, p⟩ _; rfl
  · rintro ⟨N, d, p⟩ hs
    simp only [Finset.mem_sigma, Nat.mem_divisorsAntidiagonal] at hs
    obtain ⟨-, hprod, -⟩ := hs
    subst hprod
    rfl
  · rintro ⟨d, p⟩ _; rfl

/-- **Modulus-coefficient reindexing.**  For a modulus coefficient of
convolution type `λ(q) = ∑_{d·p = q} a(d) b(p)` and any weight `F`,

`∑_{q ≤ K} λ(q) F(q) = ∑_{d·p ≤ K} a(d) b(p) F(d·p)`.

This is the exact algebraic step that turns the `(d, p)` product source of the
determinant shell into a single modulus variable `q`. -/
theorem modulus_coefficient_reindex (K : ℕ) (a b F : ℕ → ℂ) :
    ∑ N ∈ Finset.Icc 1 K,
        (∑ x ∈ Nat.divisorsAntidiagonal N, a x.1 * b x.2) * F N =
      ∑ x ∈ factorPairSet K, a x.1 * b x.2 * F (x.1 * x.2) := by
  classical
  rw [← sum_divisorPair_reindex K (fun d p => a d * b p * F (d * p))]
  refine Finset.sum_congr rfl fun N hN => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x hx => ?_
  obtain ⟨hprod, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  rw [hprod]

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
