import RequestProject.NANC.Gate1B.V11FMPerronGrammarCompiler

/-!
# V11 · Gate 1B — the generated Type-II reassembly compiler

The correct v11 downstream target is the project-local predicate
`FMPerronGeneratedTypeIIAtScale`.  It is **not** the old project predicate
`FullTypeIIBound`: no exact dictionary between the two exists in the repository,
and none is invented here.  No "Ford one-sixth theorem" is defined, since none
was present in V10.

The compiler takes

* an exact source packet decomposition of the FM-SieveGen sum,
* a generated-grammar certificate for every transformed coefficient,
* an analytic bound for every packet,
* a polylogarithmic packet / nuclear budget,

and returns `FMPerronGeneratedTypeIIAtScale`.  Every analytic ingredient is a
hypothesis.
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

variable {N : ℕ}

/-- **The generated Type-II reassembly certificate.** -/
structure GeneratedTypeIIReassembly (d : FMSieveGenData N) (Packet : Type) [Fintype Packet] where
  /-- The value of each packet, for a supplied tuple of factor functions. -/
  packetValue : (Fin N → ℕ → ℂ) → Packet → ℂ
  /-- The budget of each packet. -/
  packetBudget : Packet → ℝ
  /-- The coefficient transformation performed by the reassembly. -/
  transform : (Fin N → ℕ → ℂ) → (Fin N → ℕ → ℂ)
  /-- **generated-grammar certificate for every transformed coefficient.** -/
  transformedGenerated :
    ∀ x, (∀ j, FMPerronGeneratedUnit (x j)) → ∀ j, FMPerronGeneratedUnit (transform x j)
  /-- **exact source packet decomposition.** -/
  exactPacketDecomposition :
    ∀ x, (∀ j, FMPerronGeneratedUnit (x j)) →
      sieveGenValue d x = ∑ p, packetValue x p
  /-- **every packet analytic bound.** -/
  packetBound :
    ∀ x, (∀ j, FMPerronGeneratedUnit (x j)) → ∀ p, ‖packetValue x p‖ ≤ packetBudget p
  /-- **polylog packet / nuclear budget.** -/
  nuclearBudget : ∑ p, packetBudget p ≤ d.target

/-- **THE GENERATED TYPE-II REASSEMBLY COMPILER.** -/
theorem fmPerronGeneratedTypeII_of_reassembly (d : FMSieveGenData N) (Packet : Type)
    [Fintype Packet] (R : GeneratedTypeIIReassembly d Packet) :
    FMPerronGeneratedTypeIIAtScale d := by
  intro x hx
  calc ‖sieveGenValue d x‖ = ‖∑ p, R.packetValue x p‖ := by
        rw [R.exactPacketDecomposition x hx]
    _ ≤ ∑ p, ‖R.packetValue x p‖ := norm_sum_le _ _
    _ ≤ ∑ p, R.packetBudget p := Finset.sum_le_sum fun p _ => R.packetBound x hx p
    _ ≤ d.target := R.nuclearBudget

/-- The reassembly also certifies that the transformed coefficients stay in the
generated class — the closure property the grammar exists for. -/
theorem reassembly_transform_stays_generated (d : FMSieveGenData N) (Packet : Type)
    [Fintype Packet] (R : GeneratedTypeIIReassembly d Packet)
    (x : Fin N → ℕ → ℂ) (hx : ∀ j, FMPerronGeneratedUnit (x j)) (j : Fin N) :
    FMPerronGenerated (R.transform x j) :=
  (R.transformedGenerated x hx j).1

/-! ### Guards -/

/-- **Guard.**  The certificate is not vacuous data: it does not contain its own
conclusion as a field, and its conclusion can fail — for the toy configuration
the conclusion is false, hence no such certificate exists for it. -/
theorem no_reassembly_for_toyData (Packet : Type) [Fintype Packet] :
    ¬ Nonempty (GeneratedTypeIIReassembly toyData Packet) := by
  rintro ⟨R⟩
  exact fmPerronGeneratedTypeII_toy_fails (fmPerronGeneratedTypeII_of_reassembly _ _ R)

/-- **Guard.**  The compiler targets the v11 predicate, unfolded here to its
literal definition. -/
theorem reassembly_targets_v11_predicate (d : FMSieveGenData N) :
    FMPerronGeneratedTypeIIAtScale d ↔
      ∀ x : Fin N → ℕ → ℂ, (∀ j, FMPerronGeneratedUnit (x j)) →
        ‖sieveGenValue d x‖ ≤ d.target := Iff.rfl

end Gate1BV11
end TwinPrimeProject
