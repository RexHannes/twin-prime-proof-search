import Mathlib
import Gate1B.PuncturedFourierFrame

/-!
# Gate 1B · primitive determinant arithmetic, product phase factorisation and
the `h = 0` firewall

**Everything in this module is exact arithmetic, exact finite algebra, or a
purely logical implication.**  No analytic estimate is proved, none is assumed,
and no analytic interface is inhabited.

## Contents

* §3 **primitive determinant arithmetic**: from `X₁ = d a`, `X₂ = d b`,
  `Z₁ = e c`, `Z₂ = e f` and `X₂Z₂ − X₁Z₁ = ℓ r` with `gcd(de, ℓ) = 1`, the
  divisibility `de ∣ r`, the reduced determinant identity `bf − ac = ℓ r₀`, its
  nonvanishing, and the two semi-diagonal exclusions (supplied physical bounds
  are kept as explicit hypotheses);
* §4 **product phase factorisation** in `ZMod M`;
* §6 **primitive gcd Möbius identities** (finite divisor sums only);
* §7 **degenerate `M`-divisor router** for prime `M`;
* §8 the **original-zero / cyclic-zero firewall**: the two notions are recorded
  as *distinct*, with an explicit countermodel; nothing identifies them;
* §11 an **optional conditional compiler**: a purely logical implication whose
  analytic antecedents are explicit hypotheses and are *not* supplied here.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace PrimitiveDeterminant

open Finset
open ArithmeticFunction
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

/-! ## 3. Primitive determinant arithmetic -/

/-- **`doubleGcd_dvd_shift`.**  With `X₁ = d a`, `X₂ = d b`, `Z₁ = e c`,
`Z₂ = e f` and `X₂Z₂ − X₁Z₁ = ℓ r`, coprimality of `de` and `ℓ` forces
`de ∣ r`. -/
theorem doubleGcd_dvd_shift {d e a b c f X₁ X₂ Z₁ Z₂ ell r : ℤ}
    (hX₁ : X₁ = d * a) (hX₂ : X₂ = d * b) (hZ₁ : Z₁ = e * c) (hZ₂ : Z₂ = e * f)
    (hdet : X₂ * Z₂ - X₁ * Z₁ = ell * r) (hcop : IsCoprime (d * e) ell) :
    (d * e) ∣ r := by
  have hdvd : (d * e) ∣ ell * r := by
    refine ⟨b * f - a * c, ?_⟩
    rw [← hdet, hX₁, hX₂, hZ₁, hZ₂]
    ring
  exact hcop.dvd_of_dvd_mul_left hdvd

/-- The same statement with the source's `gcd`-form coprimality hypothesis. -/
theorem doubleGcd_dvd_shift_gcd {d e a b c f X₁ X₂ Z₁ Z₂ ell r : ℤ}
    (hX₁ : X₁ = d * a) (hX₂ : X₂ = d * b) (hZ₁ : Z₁ = e * c) (hZ₂ : Z₂ = e * f)
    (hdet : X₂ * Z₂ - X₁ * Z₁ = ell * r) (hcop : Int.gcd (d * e) ell = 1) :
    (d * e) ∣ r :=
  doubleGcd_dvd_shift hX₁ hX₂ hZ₁ hZ₂ hdet (Int.isCoprime_iff_gcd_eq_one.2 hcop)

/-- **`primitiveDeterminant_factor`.**  Writing `r = (de) r₀`, the determinant
equation descends to the *primitive* determinant equation `bf − ac = ℓ r₀`. -/
theorem primitiveDeterminant_factor {d e a b c f X₁ X₂ Z₁ Z₂ ell r r₀ : ℤ}
    (hd : d ≠ 0) (he : e ≠ 0)
    (hX₁ : X₁ = d * a) (hX₂ : X₂ = d * b) (hZ₁ : Z₁ = e * c) (hZ₂ : Z₂ = e * f)
    (hdet : X₂ * Z₂ - X₁ * Z₁ = ell * r) (hr : r = d * e * r₀) :
    b * f - a * c = ell * r₀ := by
  have hexp : (d * e) * (b * f - a * c) = (d * e) * (ell * r₀) := by
    have : X₂ * Z₂ - X₁ * Z₁ = (d * e) * (b * f - a * c) := by
      rw [hX₁, hX₂, hZ₁, hZ₂]; ring
    rw [← this, hdet, hr]; ring
  have hde : (d * e) ≠ 0 := mul_ne_zero hd he
  exact mul_left_cancel₀ hde hexp

/-- **`primitiveDeterminant_nonzero_of_shift_nonzero`.**  A nonzero shift gives a
nonzero primitive determinant. -/
theorem primitiveDeterminant_nonzero_of_shift_nonzero {a b c f ell r₀ : ℤ}
    (hell : ell ≠ 0) (hr₀ : r₀ ≠ 0) (h : b * f - a * c = ell * r₀) :
    b * f - a * c ≠ 0 := by
  rw [h]
  exact mul_ne_zero hell hr₀

/-- **Same-`X` semi-diagonal exclusion.**  If both `X`-variables are the same
`d a`, the determinant equation forces `d ∣ r`; with the supplied physical
bounds `r ≠ 0` and `|r| < |d|` this is impossible.  The bounds are hypotheses;
no analytic input is used. -/
theorem sameX_semidiagonal_impossible {d a Z₁ Z₂ ell r : ℤ}
    (hdet : (d * a) * Z₂ - (d * a) * Z₁ = ell * r) (hcop : IsCoprime d ell)
    (hr : r ≠ 0) (hlt : |r| < |d|) : False := by
  have hdvd : d ∣ ell * r := by
    refine ⟨a * (Z₂ - Z₁), ?_⟩
    rw [← hdet]; ring
  have hdr : d ∣ r := hcop.dvd_of_dvd_mul_left hdvd
  have habs : |d| ≤ |r| :=
    Int.le_of_dvd (abs_pos.2 hr) ((abs_dvd d |r|).2 ((dvd_abs d r).2 hdr))
  omega

/-- **Same-`Z` semi-diagonal exclusion**, the mirror statement in `e`. -/
theorem sameZ_semidiagonal_impossible {e c X₁ X₂ ell r : ℤ}
    (hdet : X₂ * (e * c) - X₁ * (e * c) = ell * r) (hcop : IsCoprime e ell)
    (hr : r ≠ 0) (hlt : |r| < |e|) : False := by
  have hdvd : e ∣ ell * r := by
    refine ⟨c * (X₂ - X₁), ?_⟩
    rw [← hdet]; ring
  have hdr : e ∣ r := hcop.dvd_of_dvd_mul_left hdvd
  have habs : |e| ≤ |r| :=
    Int.le_of_dvd (abs_pos.2 hr) ((abs_dvd e |r|).2 ((dvd_abs e r).2 hdr))
  omega

/-! ## 4. Product phase factorisation -/

variable {M : ℕ} [NeZero M]

/-- **`determinant_phase_factorization`.**  If `bf − ac = ℓ r₀` in `ZMod M`,
the determinant phase factors into the two product phases. -/
theorem determinant_phase_factorization (k ell r₀ a b c f : ZMod M)
    (h : b * f - a * c = ell * r₀) :
    eM M (k * (ell * r₀)) = eM M (k * (b * f)) * eM M (-(k * (a * c))) := by
  rw [← eM_add]
  congr 1
  rw [← h]
  ring

/-- The integer-level form: the hypothesis is the *integral* primitive
determinant identity, the conclusion is the factorisation of the mod-`M`
phases. -/
theorem determinant_phase_factorization_int (k : ZMod M) (a b c f ell r₀ : ℤ)
    (h : b * f - a * c = ell * r₀) :
    eM M (k * ((ell : ZMod M) * (r₀ : ZMod M)))
      = eM M (k * ((b : ZMod M) * (f : ZMod M)))
        * eM M (-(k * ((a : ZMod M) * (c : ZMod M)))) := by
  refine determinant_phase_factorization k _ _ _ _ _ _ ?_
  have := congrArg (fun z : ℤ => (z : ZMod M)) h
  push_cast at this
  exact this

/-! ## 6. Primitive gcd Möbius identities -/

/-- The divisors of `a` that also divide `b` are exactly the divisors of
`gcd(a,b)`. -/
theorem divisors_filter_dvd (a b : ℕ) (ha : a ≠ 0) :
    a.divisors.filter (fun d => d ∣ b) = (Nat.gcd a b).divisors := by
  ext d
  simp [Nat.mem_divisors, Nat.dvd_gcd_iff, ha, Nat.gcd_eq_zero_iff, and_comm]

/-- `∑_{d ∣ n} μ(d) = 1_{n = 1}`, obtained from Mathlib's Möbius inversion. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun g : ArithmeticFunction ℤ => g n) moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  simpa using h

/-- **`coprime_indicator_mobius`.**  `1_{gcd(a,b)=1} = ∑_{ρ ∣ a, ρ ∣ b} μ(ρ)`. -/
theorem coprime_indicator_mobius (a b : ℕ) (ha : a ≠ 0) :
    ∑ rho ∈ a.divisors.filter (fun d => d ∣ b), (moebius rho : ℤ)
      = if Nat.Coprime a b then 1 else 0 := by
  rw [divisors_filter_dvd a b ha, sum_moebius_divisors]

/-- **`double_coprime_indicator_mobius`.**  The two-variable version used for the
pair `(a,b)`, `(c,f)`. -/
theorem double_coprime_indicator_mobius (a b c f : ℕ) (ha : a ≠ 0) (hc : c ≠ 0) :
    (∑ rho ∈ a.divisors.filter (fun d => d ∣ b), (moebius rho : ℤ))
        * (∑ sigma ∈ c.divisors.filter (fun d => d ∣ f), (moebius sigma : ℤ))
      = if Nat.Coprime a b ∧ Nat.Coprime c f then 1 else 0 := by
  rw [coprime_indicator_mobius a b ha, coprime_indicator_mobius c f hc]
  by_cases h₁ : Nat.Coprime a b
  · by_cases h₂ : Nat.Coprime c f
    · rw [if_pos h₁, if_pos h₂, if_pos ⟨h₁, h₂⟩]; norm_num
    · rw [if_pos h₁, if_neg h₂, if_neg (fun h => h₂ h.2)]; norm_num
  · rw [if_neg h₁, if_neg (fun h : Nat.Coprime a b ∧ Nat.Coprime c f => h₁ h.1)]; norm_num

/-! ## 7. Degenerate `M`-divisor router -/

/-- **`prime_dvd_mul_router`.**  For prime `M`, `M ∣ ρσ` routes to one factor. -/
theorem prime_dvd_mul_router {M ρ σ : ℕ} (hM : Nat.Prime M) (h : M ∣ ρ * σ) :
    M ∣ ρ ∨ M ∣ σ :=
  (Nat.Prime.dvd_mul hM).1 h

/-- Arithmetic consequence of the router: a positive variable divisible by `M`
is at least `M`.  (The analytic large-divisor estimate is *not* formalised.) -/
theorem le_of_dvd_pos {M ρ : ℕ} (hρ : 0 < ρ) (h : M ∣ ρ) : M ≤ ρ :=
  Nat.le_of_dvd hρ h

/-- The router in the form used by the divisor-splitting argument. -/
theorem prime_dvd_mul_router_ge {M ρ σ : ℕ} (hM : Nat.Prime M) (hρ : 0 < ρ) (hσ : 0 < σ)
    (h : M ∣ ρ * σ) : M ≤ ρ ∨ M ≤ σ :=
  (prime_dvd_mul_router hM h).imp (le_of_dvd_pos hρ) (le_of_dvd_pos hσ)

/-! ## 8. Original-zero / cyclic-zero firewall -/

/-- The **original** determinant zero: the integral determinant vanishes. -/
def OriginalDetZero (a b c f : ℤ) : Prop := b * f - a * c = 0

/-- The **cyclic** zero: the determinant vanishes only in the auxiliary cyclic
representation `ZMod M`. -/
def CyclicDetZero (M : ℕ) (a b c f : ℤ) : Prop := ((b * f - a * c : ℤ) : ZMod M) = 0

/-- **`originalZero_preserved`.**  The original zero is preserved by the cyclic
representation: this is the only implication that holds. -/
theorem originalZero_preserved (M : ℕ) (a b c f : ℤ) (h : OriginalDetZero a b c f) :
    CyclicDetZero M a b c f := by
  unfold OriginalDetZero at h
  unfold CyclicDetZero
  rw [h]
  simp

/-- **`cyclicZero_not_identified`.**  The converse fails: a cyclic zero is *not*
an original zero.  Explicit countermodel with `M = 5`, `bf − ac = 5`. -/
theorem cyclicZero_not_identified :
    ∃ (M : ℕ) (a b c f : ℤ), Nat.Prime M ∧ CyclicDetZero M a b c f ∧
      ¬ OriginalDetZero a b c f := by
  refine ⟨5, 0, 5, 0, 1, by norm_num, ?_, ?_⟩
  · unfold CyclicDetZero
    decide
  · unfold OriginalDetZero
    norm_num

/-- **The two notions are not the same predicate.** -/
theorem cyclicZero_ne_originalZero :
    ¬ (∀ (M : ℕ) (a b c f : ℤ), Nat.Prime M → (CyclicDetZero M a b c f ↔ OriginalDetZero a b c f)) := by
  intro h
  obtain ⟨M, a, b, c, f, hp, hcyc, horig⟩ := cyclicZero_not_identified
  exact horig ((h M a b c f hp).1 hcyc)

/-- **`puncturedFrame_uses_nonzeroOnly`.**  The zero frequency is not a frequency
of the punctured frame. -/
theorem puncturedFrame_uses_nonzeroOnly : (0 : ZMod M) ∉ nzFreq M := by
  simp

/-- The punctured synthesis operator does not see the value of a coefficient
vector at the zero frequency: the auxiliary zero frequency is *avoided*, not
identified with anything. -/
theorem puncturedSynthesis_indep_of_zero_freq (c c' : ZMod M → ℂ)
    (h : ∀ k : ZMod M, k ≠ 0 → c k = c' k) (r : ZMod M) :
    ∑ k ∈ nzFreq M, c k * eM M (k * r) = ∑ k ∈ nzFreq M, c' k * eM M (k * r) :=
  Finset.sum_congr rfl fun k hk => by rw [h k (mem_nzFreq.1 hk)]

/-! ## 11. Optional conditional compiler

A purely logical implication.  Its antecedents `hSupport`, `hProduct` and
`hScale` are **hypotheses**, not theorems of this repository, and nothing here
supplies them. -/

/-- **Conditional net compiler.**  From

* `hSupport : A ≤ C · T / √E`,
* `hProduct : B ≤ A / √M` (the replacement block gains `M^{-1/2}`),
* `hScale   : M = T / E`,

one gets `B ≤ C · √T`.  All square-root and positivity assumptions are
explicit; the conclusion is algebra, not analysis. -/
theorem conditional_net_compiler {A B C E T Mscale : ℝ}
    (hE : 0 < E) (hT : 0 < T) (hScale : Mscale = T / E)
    (hSupport : A ≤ C * (T / Real.sqrt E))
    (hProduct : B ≤ A / Real.sqrt Mscale) :
    B ≤ C * Real.sqrt T := by
  have hMpos : 0 < Mscale := by rw [hScale]; positivity
  have hsqrtM : 0 < Real.sqrt Mscale := Real.sqrt_pos.2 hMpos
  have hstep : A / Real.sqrt Mscale ≤ (C * (T / Real.sqrt E)) / Real.sqrt Mscale := by
    gcongr
  have hsqE : 0 < Real.sqrt E := Real.sqrt_pos.2 hE
  have hkey : (C * (T / Real.sqrt E)) / Real.sqrt Mscale = C * Real.sqrt T := by
    rw [hScale, Real.sqrt_div hT.le E]
    field_simp
    rw [Real.sq_sqrt hT.le]
  calc B ≤ A / Real.sqrt Mscale := hProduct
    _ ≤ (C * (T / Real.sqrt E)) / Real.sqrt Mscale := hstep
    _ = C * Real.sqrt T := hkey

end PrimitiveDeterminant
end CurrentProgramme
end TwinPrimeProject
