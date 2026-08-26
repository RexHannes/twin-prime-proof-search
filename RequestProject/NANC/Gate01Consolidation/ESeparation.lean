import RequestProject.NANC.Gate01Consolidation.NonzeroOrthogonality

/-!
# BANK B — exact E-separation

For a finitely supported coefficient sequence `c` on a window `S` put

* `C_q = ∑_{x ∈ S, x ≡ −2 (q)} c x`   (`congrSum`);
* `C_• = ∑_{x ∈ S} c x`               (`fullSum`);
* `ĉ_q(a) = ∑_{x ∈ S} c x e_q(a x)`   (`fourierHat`).

Proved here, exactly and finitely:

* **ESEP1** `C_q = C_•/q + (1/q) ∑_{a ≠ 0 (q)} e_q(2a) ĉ_q(a)`;
* **ESEP2** `C_q − E = (C_•/q − E) + (1/q) ∑_{a ≠ 0 (q)} e_q(2a) ĉ_q(a)`
  for an *arbitrary* expected value `E`;
* the logical corollary that the nonzero-frequency term does not depend on the
  expected value in any way (`nonzeroFreq_independent_of_expected`).

No analytic bound for the nonzero-frequency term is stated or proved.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-- `C_q`: the mass of `c` on the progression `x ≡ −2 (mod q)`. -/
noncomputable def congrSum (S : Finset ℕ) (q : ℕ) (c : ℕ → ℂ) : ℂ :=
  ∑ x ∈ S.filter (fun x => q ∣ x + 2), c x

/-- `C_•`: the total mass of `c` on the window. -/
noncomputable def fullSum (S : Finset ℕ) (c : ℕ → ℂ) : ℂ := ∑ x ∈ S, c x

/-- `ĉ_q(a)`: the additive Fourier transform of `c` at frequency `a/q`. -/
noncomputable def fourierHat (S : Finset ℕ) (q : ℕ) (c : ℕ → ℂ) (a : ℕ) : ℂ :=
  ∑ x ∈ S, c x * ec q (a * x)

/-- The nonzero-frequency term of the E-separation. -/
noncomputable def nonzeroFreqTerm (S : Finset ℕ) (q : ℕ) (c : ℕ → ℂ) : ℂ :=
  (1 / (q : ℂ)) * ∑ a ∈ (Finset.range q).erase 0, ec q (2 * a) * fourierHat S q c a

/-- Pointwise form of NZORTH at the shifted argument `x + 2`. -/
theorem nonzero_orthogonality_shift {q : ℕ} (hq : 0 < q) (x : ℕ) :
    (1 / (q : ℂ)) * ∑ a ∈ (Finset.range q).erase 0, ec q (2 * a) * ec q (a * x)
      = (if q ∣ x + 2 then (1 : ℂ) else 0) - 1 / (q : ℂ) := by
  have hcomb : ∀ a ∈ (Finset.range q).erase 0,
      ec q (2 * (a : ℤ)) * ec q ((a : ℤ) * x) = ec q ((a : ℤ) * ((x : ℤ) + 2)) := by
    intro a _
    rw [← ec_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl hcomb, sum_ec_nonzero_div hq ((x : ℤ) + 2)]
  have : ((q : ℤ) ∣ ((x : ℤ) + 2)) ↔ (q ∣ x + 2) := by
    constructor
    · intro h; exact_mod_cast (by push_cast; exact h : ((q : ℤ)) ∣ ((x + 2 : ℕ) : ℤ))
    · intro h
      have : ((q : ℤ)) ∣ ((x + 2 : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr h
      push_cast at this
      exact this
  by_cases h : q ∣ x + 2
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (fun hc => h (this.mp hc)), if_neg h]

/-- **ESEP1.**  The exact finite additive decomposition of the progression mass. -/
theorem esep1 {q : ℕ} (hq : 0 < q) (S : Finset ℕ) (c : ℕ → ℂ) :
    congrSum S q c = fullSum S c / (q : ℂ) + nonzeroFreqTerm S q c := by
  have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hswap : nonzeroFreqTerm S q c
      = ∑ x ∈ S, c x * ((if q ∣ x + 2 then (1 : ℂ) else 0) - 1 / (q : ℂ)) := by
    unfold nonzeroFreqTerm fourierHat
    rw [Finset.mul_sum]
    have h1 : ∀ a ∈ (Finset.range q).erase 0,
        (1 / (q : ℂ)) * (ec q (2 * (a : ℤ)) * ∑ x ∈ S, c x * ec q ((a : ℤ) * x))
          = ∑ x ∈ S, (1 / (q : ℂ)) * (c x * (ec q (2 * (a : ℤ)) * ec q ((a : ℤ) * x))) := by
      intro a _
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun x _ => by ring)
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    have : ∑ a ∈ (Finset.range q).erase 0,
        (1 / (q : ℂ)) * (c x * (ec q (2 * (a : ℤ)) * ec q ((a : ℤ) * x)))
        = c x * ((1 / (q : ℂ)) *
            ∑ a ∈ (Finset.range q).erase 0, ec q (2 * (a : ℤ)) * ec q ((a : ℤ) * x)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun a _ => by ring)
    rw [this, nonzero_orthogonality_shift hq x]
  rw [hswap]
  unfold congrSum fullSum
  rw [Finset.sum_filter, Finset.sum_div]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  by_cases h : q ∣ x + 2
  · rw [if_pos h, if_pos h]; field_simp; ring
  · rw [if_neg h, if_neg h]; field_simp; ring

/-- **ESEP2.**  E-separation with an arbitrary expected value `E`. -/
theorem esep2 {q : ℕ} (hq : 0 < q) (S : Finset ℕ) (c : ℕ → ℂ) (E : ℂ) :
    congrSum S q c - E = (fullSum S c / (q : ℂ) - E) + nonzeroFreqTerm S q c := by
  rw [esep1 hq S c]; ring

/-- **Logical corollary of E-separation.**  The nonzero-frequency term is
independent of the expected value: for any two candidate expected values the
same term appears, and it is definable without mentioning `E` at all. -/
theorem nonzeroFreq_independent_of_expected {q : ℕ} (hq : 0 < q) (S : Finset ℕ)
    (c : ℕ → ℂ) (E₁ E₂ : ℂ) :
    (congrSum S q c - E₁) - (fullSum S c / (q : ℂ) - E₁)
      = (congrSum S q c - E₂) - (fullSum S c / (q : ℂ) - E₂) ∧
    (congrSum S q c - E₁) - (fullSum S c / (q : ℂ) - E₁) = nonzeroFreqTerm S q c := by
  refine ⟨by ring, ?_⟩
  rw [esep1 hq S c]; ring

end Gate01Consolidation
end TwinPrimeProject
