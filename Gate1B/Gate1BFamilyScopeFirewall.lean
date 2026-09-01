import Gate1B.HStarFiniteNuclearCompiler

/-!
# Gate 1B · scalar-versus-family scope firewall, and the Gate 1A scope firewall

**Purely logical / finite content.  No analytic statement is proved here, and
no analytic interface is promoted.**

## Contents

* §1 the **scalar** Gate 1B closure predicate, restated name-disjointly.  The
  legacy predicate of exactly this shape (`|total| ≤ bound ∧ uncovered = 0`)
  lives in a top-level tree which is outside every library glob of this
  repository; it is left completely untouched and nothing here is identified
  with it;
* §2 the **family-uniform** predicate `Gate1BFamilyUniformBound`, which
  literally quantifies over every template of a supplied finite family;
* §3 the **scope firewall**: scalar closure does *not* propositionally imply
  the family-uniform bound — an explicit countermodel with cancellation —
  together with the two explicit bridge theorems that *do* hold, in each
  direction, with their hypotheses visible;
* §4 the **Gate 1A scope firewall**: the Gate 1A canonical source shape carries
  a common physical field `W_D`, the HSTAR template type does not, and no map
  recovers `W_D` from a template.  The raw energy / covariance energy
  distinction is the one already proved in
  `Gate1B.HStarFiniteNuclearCompiler`.  No analytic no-go theorem is claimed.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset
open scoped BigOperators

/-! ## 1. The scalar predicate -/

/-- The **scalar** Gate 1B closure predicate, in the legacy three-argument
shape `(total, bound, uncovered mass)`.  Restated here name-disjointly; the
legacy declaration is untouched and is not imported. -/
def Gate1BClosedScalarTBU (T B U : ℝ) : Prop := |T| ≤ B ∧ U = 0

/-! ## 2. The family-uniform predicate -/

/-- **Family-uniform Gate 1B bound.**  Unlike the scalar predicate, this
literally quantifies over *every* template of the supplied finite family. -/
def Gate1BFamilyUniformBound (F : HStarTemplateFamily) (T : Fin F.size → ℂ)
    (B : ℝ) : Prop :=
  ∀ i : Fin F.size, ‖T i‖ ≤ B

/-- Synonym used when the family-uniform predicate is read as a property of the
template family itself. -/
def HStarTemplateGate1BBound (F : HStarTemplateFamily) (T : Fin F.size → ℂ)
    (B : ℝ) : Prop :=
  Gate1BFamilyUniformBound F T B

theorem hStarTemplateGate1BBound_iff (F : HStarTemplateFamily)
    (T : Fin F.size → ℂ) (B : ℝ) :
    HStarTemplateGate1BBound F T B ↔ ∀ i : Fin F.size, ‖T i‖ ≤ B := Iff.rfl

/-! ## 3. The scope firewall -/

/-- The cancelling packet values used as the scope countermodel. -/
noncomputable def cancellingPackets : Fin samplePairFamily.size → ℂ :=
  fun i => if i.val = 0 then 10 else -10

theorem cancellingPackets_recombination :
    familyRecombination samplePairFamily cancellingPackets = 0 := by
  simp [familyRecombination, cancellingPackets, samplePairFamily, Fin.sum_univ_two]

/-- **Scope firewall (countermodel).**  Scalar Gate 1B closure of the
recombined total holds with bound `1`, while the family-uniform bound with the
same constant fails: the family carries information the scalar does not. -/
theorem scalar_closed_but_not_family_uniform :
    Gate1BClosedScalarTBU ‖familyRecombination samplePairFamily cancellingPackets‖ 1 0 ∧
      ¬ Gate1BFamilyUniformBound samplePairFamily cancellingPackets 1 := by
  constructor
  · refine ⟨?_, rfl⟩
    rw [cancellingPackets_recombination]
    norm_num
  · intro h
    have h1 := h ⟨1, by decide⟩
    simp [cancellingPackets] at h1

/-- **Scope firewall (non-implication).**  There is no propositional
implication from scalar closure to the family-uniform template bound. -/
theorem scalar_does_not_imply_family_uniform :
    ¬ ∀ (F : HStarTemplateFamily) (T : Fin F.size → ℂ) (B : ℝ),
        Gate1BClosedScalarTBU ‖familyRecombination F T‖ B 0 →
          Gate1BFamilyUniformBound F T B := by
  intro h
  obtain ⟨hs, hn⟩ := scalar_closed_but_not_family_uniform
  exact hn (h samplePairFamily cancellingPackets 1 hs)

/-- **Explicit bridge, family ⇒ scalar.**  A family-uniform bound plus a
nuclear `ℓ¹` budget gives a scalar bound for the recombination.  Every
hypothesis is visible. -/
theorem scalar_of_family_uniform (F : HStarTemplateFamily) (T : Fin F.size → ℂ)
    (B Nuclear : ℝ) (hB : 0 ≤ B) (hc : ∑ i, ‖F.coeff i‖ ≤ Nuclear)
    (h : Gate1BFamilyUniformBound F T B) :
    Gate1BClosedScalarTBU ‖familyRecombination F T‖ (Nuclear * B) 0 := by
  refine ⟨?_, rfl⟩
  rw [abs_of_nonneg (norm_nonneg _)]
  exact family_recombination_bound F T Nuclear B hB hc h

/-- **Explicit bridge, per-template ⇒ family.**  The only way to obtain the
family-uniform predicate is to supply a bound for every template. -/
theorem family_uniform_of_forall (F : HStarTemplateFamily) (T : Fin F.size → ℂ)
    (B : ℝ) (h : ∀ i : Fin F.size, ‖T i‖ ≤ B) :
    Gate1BFamilyUniformBound F T B := h

/-! ## 4. Gate 1A scope firewall -/

/-- The Gate 1A canonical source shape: it carries the common **physical**
field `W_D` in addition to its template payload. -/
structure Gate1ACanonicalSourceShape where
  /-- The common physical weight. -/
  WD : ℕ → ℝ
  /-- The template payload. -/
  template : HStarK0J0Template

/-- Forgetting the physical field. -/
def Gate1ACanonicalSourceShape.forgetWD (S : Gate1ACanonicalSourceShape) :
    HStarK0J0Template := S.template

/-- **Gate 1A scope firewall (structural).**  Two Gate 1A canonical sources can
differ while having the same HSTAR template payload: the HSTAR template type is
strictly poorer, so the two source types are not definitionally identical. -/
theorem forgetWD_not_injective :
    ∃ S₁ S₂ : Gate1ACanonicalSourceShape,
      S₁ ≠ S₂ ∧ S₁.forgetWD = S₂.forgetWD := by
  refine ⟨⟨fun _ => 0, sampleTemplate⟩, ⟨fun _ => 1, sampleTemplate⟩, ?_, rfl⟩
  intro h
  have hW := congrArg Gate1ACanonicalSourceShape.WD h
  have h0 : (0 : ℝ) = 1 := congrFun hW 0
  norm_num at h0

/-- **Gate 1A scope firewall (no reconstruction).**  No map recovers the
physical weight `W_D` from the HSTAR template payload. -/
theorem no_physical_weight_from_template :
    ¬ ∃ G : HStarK0J0Template → (ℕ → ℝ),
        ∀ S : Gate1ACanonicalSourceShape, G S.forgetWD = S.WD := by
  rintro ⟨G, hG⟩
  have h1 := hG ⟨fun _ => 0, sampleTemplate⟩
  have h2 := hG ⟨fun _ => 1, sampleTemplate⟩
  have h3 : (fun _ : ℕ => (0 : ℝ)) = (fun _ : ℕ => (1 : ℝ)) := by
    have e1 : G sampleTemplate = fun _ : ℕ => (0 : ℝ) := h1
    have e2 : G sampleTemplate = fun _ : ℕ => (1 : ℝ) := h2
    rw [← e1, ← e2]
  have h0 : (0 : ℝ) = 1 := congrFun h3 0
  norm_num at h0

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
