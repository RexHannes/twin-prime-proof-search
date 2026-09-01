import Gate1B.FM722BalancedCoagulation

/-!
# Gate 1B · FM722 · the **generated Γ source** type

The repository does not contain a literal Ford-generated `Γ` source object, so
this module introduces one as an explicit finite **interface**:

* `GeneratedGammaAtomization` — a finite atom index, atom coefficients, atom
  support intervals, the product reconstruction and `L¹/L²` metadata.  There is
  deliberately **no arbitrary-β field**: the structure cannot be fed an
  arbitrary bounded coefficient sequence, only genuinely generated atoms.
* `FordGeneratedGammaSource` — the *physical source realisation*: an
  atomization of a supplied `Γ` family whose atom exponents obey the FM722
  pre-supremum atom-form constraints.  **This bank never inhabits it**, and no
  analytic or source theorem of Ford's is fabricated here: at paper/source
  level `FM722-GAMMA-PRESUPREMUM-ATOMFORM45` is recorded as a PASS, not as a
  kernel-proved Lean theorem.

What *is* kernel-proved here is the **dictionary**: any physical source in the
above sense feeds the finite balanced-coagulation lemma and therefore produces
a whole-atom split with `1/3 ≤ α_A < 1/3 + σ < 1/2` and `1/3 < α_C ≤ 2/3`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset

/-- **Generated Γ atomization** (finite interface).

Fields: the finite atom index, the atom coefficients, the atom support
intervals, the atom exponents, the atom factors together with the product
reconstruction of the generated value, and the `L¹/L²` metadata.

There is **no arbitrary-β field**: nothing here accepts an unstructured
divisor-bounded sequence in place of the generated atoms. -/
structure GeneratedGammaAtomization where
  /-- The number of atoms. -/
  numAtoms : ℕ
  /-- The atom coefficients. -/
  coeff : Fin numAtoms → ℂ
  /-- Left endpoint of the support interval of each atom. -/
  lo : Fin numAtoms → ℝ
  /-- Right endpoint of the support interval of each atom. -/
  hi : Fin numAtoms → ℝ
  /-- Support intervals are nondegenerate. -/
  lo_le_hi : ∀ j, lo j ≤ hi j
  /-- The exponent (log-scale length) of each atom. -/
  expo : Fin numAtoms → ℝ
  /-- Atom exponents are nonnegative. -/
  expo_nonneg : ∀ j, 0 ≤ expo j
  /-- The atom factors. -/
  atomValue : Fin numAtoms → ℕ → ℂ
  /-- The generated value. -/
  value : ℕ → ℂ
  /-- **Product reconstruction.** -/
  reconstruction : ∀ n, value n = ∏ j, atomValue j n
  /-- `L¹` metadata. -/
  l1Bound : ℝ
  /-- `L²` metadata. -/
  l2Bound : ℝ
  /-- The `L¹` metadata bounds the coefficient mass. -/
  coeff_l1 : ∑ j, ‖coeff j‖ ≤ l1Bound
  /-- The `L²` metadata bounds the coefficient energy. -/
  coeff_l2 : ∑ j, ‖coeff j‖ ^ 2 ≤ l2Bound

/-- The ordered list of atom exponents of an atomization. -/
noncomputable def GeneratedGammaAtomization.expoList (G : GeneratedGammaAtomization) : List ℝ :=
  List.ofFn G.expo

theorem GeneratedGammaAtomization.expoList_sum (G : GeneratedGammaAtomization) :
    G.expoList.sum = ∑ j, G.expo j := by
  rw [GeneratedGammaAtomization.expoList, List.sum_ofFn]

theorem GeneratedGammaAtomization.expoList_mem (G : GeneratedGammaAtomization) {x : ℝ}
    (hx : x ∈ G.expoList) : ∃ j, G.expo j = x := by
  rw [GeneratedGammaAtomization.expoList, List.mem_ofFn] at hx
  obtain ⟨j, hj⟩ := hx
  exact ⟨j, hj⟩

/-- **Physical source realisation (INTERFACE — never inhabited here).**

An atomization of a supplied family `Gamma` whose atom exponents satisfy the
FM722 pre-supremum atom-form constraints `0 ≤ α_j ≤ σ < 1/6` and
`∑_j α_j = 1 − ρ` with `0 ≤ ρ < 1/6`.

No term of this type is constructed anywhere in this bank; Ford's analytic /
source theorem is **not** fabricated, assumed, or turned into an axiom. -/
structure FordGeneratedGammaSource (Gamma : ℕ → ℂ) (sigma rho : ℝ) where
  /-- The atomization of the source. -/
  atomize : GeneratedGammaAtomization
  /-- The atomization realises the supplied source family. -/
  realises : ∀ n, Gamma n = atomize.value n
  /-- `σ` is nonnegative. -/
  sigma_nonneg : 0 ≤ sigma
  /-- `σ < 1/6`. -/
  sigma_lt : sigma < 1 / 6
  /-- `ρ` is nonnegative. -/
  rho_nonneg : 0 ≤ rho
  /-- `ρ < 1/6`. -/
  rho_lt : rho < 1 / 6
  /-- Every atom exponent is at most `σ`. -/
  expo_le : ∀ j, atomize.expo j ≤ sigma
  /-- The atom exponents sum to `1 − ρ`. -/
  expo_sum : ∑ j, atomize.expo j = 1 - rho

/-- **Dictionary (kernel-proved).**  Any physical generated source feeds the
finite balanced-coagulation lemma: there is a whole-atom prefix `A` of the
ordered atom family with `1/3 ≤ α_A < 1/3 + σ` and complement `C` satisfying
`1/3 < α_C ≤ 2/3`.  No atom is split. -/
theorem generated_source_admits_balanced_coagulation {Gamma : ℕ → ℂ} {sigma rho : ℝ}
    (S : FordGeneratedGammaSource Gamma sigma rho) :
    ∃ k, k ≤ S.atomize.expoList.length ∧
      1 / 3 ≤ (S.atomize.expoList.take k).sum ∧
      (S.atomize.expoList.take k).sum < 1 / 3 + sigma ∧
      1 / 3 < (S.atomize.expoList.drop k).sum ∧
      (S.atomize.expoList.drop k).sum ≤ 2 / 3 := by
  refine balanced_coagulation S.atomize.expoList sigma rho ?_ ?_ S.sigma_nonneg S.sigma_lt
    S.rho_nonneg S.rho_lt ?_
  · intro x hx
    obtain ⟨j, hj⟩ := S.atomize.expoList_mem hx
    exact hj ▸ S.atomize.expo_nonneg j
  · intro x hx
    obtain ⟨j, hj⟩ := S.atomize.expoList_mem hx
    exact hj ▸ S.expo_le j
  · rw [S.atomize.expoList_sum, S.expo_sum]

/-- The coagulation window of a physical generated source lies strictly below
`1/2`. -/
theorem generated_source_window_lt_half {Gamma : ℕ → ℂ} {sigma rho : ℝ}
    (S : FordGeneratedGammaSource Gamma sigma rho) : 1 / 3 + sigma < 1 / 2 :=
  coagulation_window_lt_half sigma S.sigma_lt

end FM722
end CurrentProgramme
end TwinPrimeProject
