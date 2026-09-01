import Gate1B.Gate1BFamilyScopeFirewall

/-!
# Gate 1B · HSTAR source-template uniformity: OPEN INTERFACES only

**Nothing analytic is proved here and nothing is promoted.**  This module
records, as parameterised interfaces, the two obligations that the HSTAR
source-template frontier needs, and proves only the deterministic consequences
that follow *given* those interfaces.

## Contents

* §1 `HStarTemplateUniformityCertificate`: a family-uniform Gate 1B bound for a
  supplied evaluation of the templates.  It is a *parameter*, never supplied
  for the physical HSTAR evaluation and the physical Gate 1B target;
* §2 `FordToGateSourceCensus`: the exhaustiveness obligation "every source
  produced upstream occurs in the supplied finite family".  Also never
  supplied;
* §3 the deterministic compilers chaining a census, a uniformity certificate
  and a nuclearization certificate into a parent bound.  Each analytic input is
  an explicit argument.

The research frontier label attached to these interfaces is
`HSTAR-K0J0-SOURCETEMPLATE-GATE1B-UNIFORMITY45`, recorded in the status layer.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset
open scoped BigOperators

/-! ## 1. Template-uniform Gate 1B bound (interface) -/

/-- **OPEN INTERFACE.**  A family-uniform Gate 1B bound for the evaluation
`eval` of the templates of `F`, with packet bound `B`.

This is a *parameterised* interface: it is not asserted, and it is never
constructed in this bank for the physical HSTAR evaluation and the physical
Gate 1B target.  (For arbitrary `eval` and arbitrary `B` the structure is of
course satisfiable; the open content is the *physical* instance, which is
exactly the frontier label.) -/
structure HStarTemplateUniformityCertificate
    (F : HStarTemplateFamily) (eval : HStarK0J0Template → ℂ) (B : ℝ) where
  /-- The bound is a nonnegative budget. -/
  bound_nonneg : 0 ≤ B
  /-- Every template of the family obeys the bound. -/
  uniform : ∀ i : Fin F.size, ‖eval (F.templates i)‖ ≤ B

/-- A uniformity certificate yields the family-uniform predicate for the
induced packet values. -/
theorem familyUniform_of_certificate {F : HStarTemplateFamily}
    {eval : HStarK0J0Template → ℂ} {B : ℝ}
    (cert : HStarTemplateUniformityCertificate F eval B) :
    Gate1BFamilyUniformBound F (fun i => eval (F.templates i)) B :=
  cert.uniform

/-- **Scope reminder.**  A uniformity certificate is strictly stronger data
than scalar closure of the recombination: the converse direction fails
(`scalar_does_not_imply_family_uniform`). -/
theorem scalar_closure_insufficient_for_uniformity :
    ¬ ∀ (F : HStarTemplateFamily) (T : Fin F.size → ℂ) (B : ℝ),
        Gate1BClosedScalarTBU ‖familyRecombination F T‖ B 0 →
          Gate1BFamilyUniformBound F T B :=
  scalar_does_not_imply_family_uniform

/-! ## 2. Ford-to-Gate source census (interface) -/

/-- **OPEN INTERFACE.**  The exhaustiveness obligation: every template produced
upstream (predicate `produced`) occurs in the finite family `F`.  Never
supplied in this bank. -/
structure FordToGateSourceCensus
    (produced : HStarK0J0Template → Prop) (F : HStarTemplateFamily) where
  exhaustive : ∀ T : HStarK0J0Template, produced T → ∃ i : Fin F.size, F.templates i = T

/-- **Deterministic consequence.**  Given the census and a family-uniform
bound, every produced template obeys the bound. -/
theorem produced_bound_of_census_and_uniformity
    {produced : HStarK0J0Template → Prop} {F : HStarTemplateFamily}
    {eval : HStarK0J0Template → ℂ} {B : ℝ}
    (census : FordToGateSourceCensus produced F)
    (cert : HStarTemplateUniformityCertificate F eval B) :
    ∀ T, produced T → ‖eval T‖ ≤ B := by
  intro T hT
  obtain ⟨i, hi⟩ := census.exhaustive T hT
  have := cert.uniform i
  rwa [hi] at this

/-! ## 3. Deterministic compilers -/

/-- **Deterministic reassembly compiler.**  A nuclearization certificate for
the parent, together with a template-uniform bound for the very packets it
decomposes into, gives the parent bound `Nuclear · B`.  Both certificates are
explicit arguments; neither is supplied. -/
theorem parent_bound_of_certificates {S : HStarK0J0Source} {parentValue : ℂ}
    (nucCert : HStarK0J0NuclearizationCertificate S parentValue)
    {eval : HStarK0J0Template → ℂ} {B : ℝ}
    (uniCert : HStarTemplateUniformityCertificate nucCert.family eval B)
    (hmatch : ∀ i, nucCert.templateValue i = eval (nucCert.family.templates i)) :
    ‖parentValue‖ ≤ nucCert.nuclear * B := by
  refine parent_bound_of_certificate nucCert B uniCert.bound_nonneg fun i => ?_
  rw [hmatch i]
  exact uniCert.uniform i

/-- **Firewall.**  The reassembly compiler consumes a *family* certificate: a
scalar Gate 1B closure statement is not an admissible substitute. -/
theorem reassembly_needs_family_certificate :
    ¬ ∀ (F : HStarTemplateFamily) (T : Fin F.size → ℂ) (B : ℝ),
        Gate1BClosedScalarTBU ‖familyRecombination F T‖ B 0 →
          ∀ i : Fin F.size, ‖T i‖ ≤ B :=
  scalar_does_not_imply_family_uniform

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
