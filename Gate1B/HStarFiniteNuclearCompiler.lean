import Gate1B.HStarTemplateFamily

/-!
# Gate 1B · finite nuclear compiler, nuclearization certificate, raw energy algebra

**Deterministic finite algebra only.**  Nothing in this module contains a
hidden analytic statement: every bound is an abstract nonnegative real budget.

## Contents

* §1 the finite nuclear compiler

  `(∑ᵢ |cᵢ| ≤ Nuclear) → (∀ i, |Tᵢ| ≤ PacketBound) → |∑ᵢ cᵢ Tᵢ| ≤ Nuclear · PacketBound`;

* §2 `HStarK0J0NuclearizationCertificate`, the **open interface**.  It records
  a finite discrete template index, a finite Perron surrogate index, the
  coefficient of each template, the exact decomposition identity and a total
  nuclear bound.  **No inhabitant of this structure is constructed anywhere in
  this bank**, no axiom asserts one, and the continuous Perron source of such a
  decomposition is external analytic input.  Only deterministic consequences
  *given* a certificate are proved;

* §3 raw finite energy algebra: bounded-depth product-representation
  multiplicity, support restriction, unit-modulus invariance and a finite
  Cauchy–Schwarz compiler;

* §4 the **energy firewall**: the raw multiplicative/source energy is not the
  Gate 1A physical covariance energy.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset
open scoped BigOperators

/-! ## 1. The finite nuclear compiler -/

/-- **Finite nuclear compiler.**  Purely deterministic: an `ℓ¹` bound on the
coefficients and a uniform bound on the packets give the product bound for the
recombination. -/
theorem nuclear_compiler {n : ℕ} (c T : Fin n → ℂ) (Nuclear PacketBound : ℝ)
    (hP : 0 ≤ PacketBound)
    (hc : ∑ i, ‖c i‖ ≤ Nuclear) (hT : ∀ i, ‖T i‖ ≤ PacketBound) :
    ‖∑ i, c i * T i‖ ≤ Nuclear * PacketBound := by
  have h1 : ‖∑ i, c i * T i‖ ≤ ∑ i, ‖c i * T i‖ := norm_sum_le _ _
  have h2 : ∑ i, ‖c i * T i‖ ≤ ∑ i, ‖c i‖ * PacketBound := by
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hT i) (norm_nonneg _)
  have h3 : ∑ i, ‖c i‖ * PacketBound = (∑ i, ‖c i‖) * PacketBound := by
    rw [Finset.sum_mul]
  have h4 : (∑ i, ‖c i‖) * PacketBound ≤ Nuclear * PacketBound :=
    mul_le_mul_of_nonneg_right hc hP
  calc ‖∑ i, c i * T i‖ ≤ ∑ i, ‖c i * T i‖ := h1
    _ ≤ ∑ i, ‖c i‖ * PacketBound := h2
    _ = (∑ i, ‖c i‖) * PacketBound := h3
    _ ≤ Nuclear * PacketBound := h4

/-- The recombination of a template family from packet values. -/
noncomputable def familyRecombination (F : HStarTemplateFamily)
    (T : Fin F.size → ℂ) : ℂ :=
  ∑ i, F.coeff i * T i

/-- The nuclear compiler, specialised to a template family. -/
theorem family_recombination_bound (F : HStarTemplateFamily) (T : Fin F.size → ℂ)
    (Nuclear PacketBound : ℝ) (hP : 0 ≤ PacketBound)
    (hc : ∑ i, ‖F.coeff i‖ ≤ Nuclear) (hT : ∀ i, ‖T i‖ ≤ PacketBound) :
    ‖familyRecombination F T‖ ≤ Nuclear * PacketBound :=
  nuclear_compiler _ _ _ _ hP hc hT

/-! ## 2. The nuclearization certificate (OPEN INTERFACE, uninhabited) -/

/-- **OPEN INTERFACE.**  A nuclearization certificate for the HSTAR `k = 0`,
`J = ∅` first parent `S` with parent value `parentValue`.

No inhabitant is constructed in this bank, and no axiom provides one: the
continuous Perron nuclearization that would produce such a certificate is
external analytic input.  Only the deterministic consequences below are
proved. -/
structure HStarK0J0NuclearizationCertificate
    (S : HStarK0J0Source) (parentValue : ℂ) where
  /-- The finite discrete template family. -/
  family : HStarTemplateFamily
  /-- The finite Perron surrogate index attached to each template. -/
  perronIndex : Fin family.size → PerronParameterIndex
  /-- The value of each template. -/
  templateValue : Fin family.size → ℂ
  /-- The exact decomposition identity. -/
  decomposition : parentValue = ∑ i, family.coeff i * templateValue i
  /-- The total nuclear budget. -/
  nuclear : ℝ
  nuclear_nonneg : 0 ≤ nuclear
  /-- The total nuclear bound on the coefficients. -/
  nuclear_bound : ∑ i, ‖family.coeff i‖ ≤ nuclear

/-- **Deterministic consequence of a certificate.**  Given a certificate and a
uniform packet bound, the parent obeys the product bound.  The certificate is
an explicit hypothesis; it is never supplied. -/
theorem parent_bound_of_certificate {S : HStarK0J0Source} {parentValue : ℂ}
    (cert : HStarK0J0NuclearizationCertificate S parentValue)
    (PacketBound : ℝ) (hP : 0 ≤ PacketBound)
    (hT : ∀ i, ‖cert.templateValue i‖ ≤ PacketBound) :
    ‖parentValue‖ ≤ cert.nuclear * PacketBound := by
  have h0 : ‖parentValue‖ = ‖∑ i, cert.family.coeff i * cert.templateValue i‖ :=
    congrArg norm cert.decomposition
  rw [h0]
  exact nuclear_compiler _ _ _ _ hP cert.nuclear_bound hT

/-- The certificate value is the recombination of its own family. -/
theorem certificate_recombination {S : HStarK0J0Source} {parentValue : ℂ}
    (cert : HStarK0J0NuclearizationCertificate S parentValue) :
    parentValue = familyRecombination cert.family cert.templateValue :=
  cert.decomposition

/-! ## 3. Raw finite energy algebra -/

/-- The raw source energy of a coefficient on a finite support. -/
noncomputable def rawSourceEnergy (A : Finset ℕ) (f : ℕ → ℂ) : ℝ :=
  ∑ i ∈ A, ‖f i‖ ^ 2

/-- **Support restriction can only decrease the raw energy.** -/
theorem rawSourceEnergy_mono {A B : Finset ℕ} (h : A ⊆ B) (f : ℕ → ℂ) :
    rawSourceEnergy A f ≤ rawSourceEnergy B f := by
  refine Finset.sum_le_sum_of_subset_of_nonneg h fun i _ _ => ?_
  positivity

/-- **Unit-modulus twists preserve the raw energy.** -/
theorem rawSourceEnergy_unitTwist (A : Finset ℕ) (f : ℕ → ℂ) (t : UnitTwist) :
    rawSourceEnergy A (fun i => t.twist i * f i) = rawSourceEnergy A f := by
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_mul, t.norm_one i, one_mul]

/-- **Finite Cauchy–Schwarz energy compiler.** -/
theorem finite_cauchy_energy (A : Finset ℕ) (f g : ℕ → ℂ) :
    (∑ i ∈ A, ‖f i‖ * ‖g i‖) ^ 2 ≤ rawSourceEnergy A f * rawSourceEnergy A g := by
  simpa [rawSourceEnergy] using
    Finset.sum_mul_sq_le_sq_mul_sq A (fun i => ‖f i‖) (fun i => ‖g i‖)

/-- The raw multiplicative energy of a finite set of moduli: the number of
quadruples with `a·b = c·d`. -/
def rawMultiplicativeEnergy (A : Finset ℕ) : ℕ :=
  ((A ×ˢ A ×ˢ A ×ˢ A).filter (fun x => x.1 * x.2.1 = x.2.2.1 * x.2.2.2)).card

/-- **Support restriction can only decrease the raw multiplicative energy.** -/
theorem rawMultiplicativeEnergy_mono {A B : Finset ℕ} (h : A ⊆ B) :
    rawMultiplicativeEnergy A ≤ rawMultiplicativeEnergy B := by
  refine Finset.card_le_card ?_
  refine Finset.filter_subset_filter _ ?_
  exact Finset.product_subset_product h
    (Finset.product_subset_product h (Finset.product_subset_product h h))

/-- **Bounded-depth product-representation multiplicity.**  The ordered
factorisations of `N` inject into pairs of divisors, so their number is at most
the square of the divisor count. -/
theorem card_divisorsAntidiagonal_le (N : ℕ) :
    (Nat.divisorsAntidiagonal N).card ≤ N.divisors.card * N.divisors.card := by
  classical
  have hsub : Nat.divisorsAntidiagonal N ⊆ N.divisors ×ˢ N.divisors := by
    intro x hx
    obtain ⟨hprod, hN0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    refine Finset.mem_product.mpr ⟨?_, ?_⟩
    · exact Nat.mem_divisors.mpr ⟨⟨x.2, hprod.symm⟩, hN0⟩
    · exact Nat.mem_divisors.mpr ⟨⟨x.1, by rw [← hprod]; ring⟩, hN0⟩
  calc (Nat.divisorsAntidiagonal N).card ≤ (N.divisors ×ˢ N.divisors).card :=
        Finset.card_le_card hsub
    _ = N.divisors.card * N.divisors.card := Finset.card_product _ _

/-! ## 4. The energy firewall -/

/-- A Gate 1A physical weight: the common physical field `W_D` that the HSTAR
template type does **not** carry. -/
structure Gate1APhysicalWeight where
  WD : ℕ → ℝ

/-- The Gate 1A physical covariance energy, by definition weighted by `W_D`. -/
noncomputable def gate1APhysicalCovarianceEnergy
    (W : Gate1APhysicalWeight) (A : Finset ℕ) (f : ℕ → ℂ) : ℝ :=
  ∑ i ∈ A, W.WD i * ‖f i‖ ^ 2

/-- **Energy firewall.**  `RawMultiplicativeEnergy ≠ Gate1APhysicalCovarianceEnergy`:
the two are different definitions and take different values.  (This is a
statement about the definitions, not an analytic no-go theorem.) -/
theorem rawEnergy_ne_gate1A_covarianceEnergy :
    ∃ (W : Gate1APhysicalWeight) (A : Finset ℕ) (f : ℕ → ℂ),
      rawSourceEnergy A f ≠ gate1APhysicalCovarianceEnergy W A f := by
  refine ⟨⟨fun _ => 0⟩, {1}, fun _ => 1, ?_⟩
  simp [rawSourceEnergy, gate1APhysicalCovarianceEnergy]

/-- Raw energy is the unweighted case; the two notions agree only when the
physical weight is identically one, which is an explicit hypothesis and is
never assumed elsewhere. -/
theorem rawEnergy_eq_covariance_of_trivial_weight
    (W : Gate1APhysicalWeight) (A : Finset ℕ) (f : ℕ → ℂ)
    (hW : ∀ i ∈ A, W.WD i = 1) :
    rawSourceEnergy A f = gate1APhysicalCovarianceEnergy W A f := by
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [hW i hi, one_mul]

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
