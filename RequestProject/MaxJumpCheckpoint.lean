import RequestProject.MaxJumpArithmetic
import RequestProject.ThreeFormReduction
import RequestProject.ThreeFormSieveInput
import RequestProject.MaxJumpForest

/-!
# Erdős 461A max-jump D3S checkpoint aggregator

This exports a conditional checkpoint with one isolated analytic input.  It does
not prove a uniform super-Erdős--Graham bound or Erdős #461A.
-/

namespace Erdos461A

inductive BankStatus where
  | leanProved
  | conditionalOneAnalyticInput
  | openAnalyticInput
  | outOfScope
  deriving Repr, DecidableEq

structure StatusEntry where
  label : String
  status : BankStatus
  note : String := ""
  deriving Repr

def maxJumpStatus : List StatusEntry :=
  [ ⟨"EXCESS_IDENTITY", .leanProved, "finite fibre identity"⟩
  , ⟨"EQUAL_LABEL_SPACING", .leanProved, "uses the supplied established spacing premise"⟩
  , ⟨"SIDE_FACTOR_IDENTITIES", .leanProved, ""⟩
  , ⟨"GCD_SIDE_FACTORS_TWO", .leanProved, ""⟩
  , ⟨"MAX_JUMP_AT_LEAST_FOUR", .leanProved, ""⟩
  , ⟨"THREE_FORM_REDUCTION", .leanProved, ""⟩
  , ⟨"LARGE_U_COUNT", .conditionalOneAnalyticInput,
      "not separately formalised; remains part of explicit downstream assembly premise"⟩
  , ⟨"SINGULAR_FACTOR_AVERAGE", .conditionalOneAnalyticInput,
      "not separately formalised; remains part of explicit downstream assembly premise"⟩
  , ⟨"K_TO_H_ENVELOPE_REPAIR", .conditionalOneAnalyticInput,
      "recorded in the isolated sieve statement description"⟩
  , ⟨"DYADIC_INDEX_REPAIR", .conditionalOneAnalyticInput,
      "not separately formalised; remains part of explicit downstream assembly premise"⟩
  , ⟨"THREE_FORM_LOCAL_ROOT_TABLE", .leanProved, ""⟩
  , ⟨"OPEN_ANALYTIC_INPUT_threeFormUpperSieve", .openAnalyticInput,
      "single remaining analytic input; no global inhabitant"⟩
  , ⟨"DOUBLY_SMALL_TOKENS_D3S", .conditionalOneAnalyticInput, ""⟩
  , ⟨"MAX_JUMP_FOREST_ACYCLIC", .leanProved, ""⟩
  , ⟨"ORPHAN_SEA_OCCURRENCE_BOUND", .conditionalOneAnalyticInput,
      "counts token-centre occurrences, not distinct labels"⟩
  , ⟨"HALL_MATCHING", .outOfScope, ""⟩
  , ⟨"BRFC", .outOfScope, ""⟩
  , ⟨"CHSA", .outOfScope, ""⟩
  , ⟨"BORF", .outOfScope, ""⟩
  , ⟨"UNIFORM_SUPER_EG", .outOfScope, "NOT PROVED"⟩
  , ⟨"ERDOS_461A", .outOfScope, "NOT PROVED"⟩
  ]

end Erdos461A
