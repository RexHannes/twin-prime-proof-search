import RequestProject.CurrentProgramme.CurrentStatus

/-!
# Twin-prime programme · project-local dependency graph

The living graph deliberately contains only the fixed-shift / Ford–Maynard / Twin-Prime
programme.  Erdős-#287 source objects, compilers, conclusions and status nodes are kept in
the separate #287 repository and are not dependencies of this graph.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Graph

/-- Nodes of the current Twin-Prime dependency graph. -/
inductive Node where
  | gate0
  | packetCensus
  | gate1A
  | gate1B
  | gate2
  | fullFMTypeII
  | twinPrimes
  deriving DecidableEq, Repr, Inhabited

/-- Directed project-local architecture edges. -/
def edge : Node → Node → Bool
  | Node.gate0, Node.packetCensus => true
  | Node.packetCensus, Node.gate1A => true
  | Node.packetCensus, Node.gate1B => true
  | Node.gate1A, Node.gate2 => true
  | Node.gate1B, Node.gate2 => true
  | Node.gate2, Node.fullFMTypeII => true
  | Node.fullFMTypeII, Node.twinPrimes => true
  | _, _ => false

/-- Reachability in the finite DAG. -/
def reachIn : ℕ → Node → Node → Bool
  | 0, a, b => decide (a = b)
  | (k + 1), a, b =>
      decide (a = b) ||
        (List.any [Node.gate0, Node.packetCensus, Node.gate1A, Node.gate1B,
                   Node.gate2, Node.fullFMTypeII, Node.twinPrimes]
          (fun c => edge a c && reachIn k c b))

/-- Reachability with enough depth for this DAG. -/
def reach (a b : Node) : Bool := reachIn 8 a b

/-- The intended Twin-Prime spine is present. -/
theorem twin_branch_present : reach Node.gate0 Node.twinPrimes = true := by
  decide

/-- Gate-1A and Gate-1B remain parallel provider layers. -/
theorem providers_are_parallel :
    reach Node.gate1A Node.gate1B = false ∧
      reach Node.gate1B Node.gate1A = false := by
  constructor <;> decide

/-- The census-to-Gate-1A architecture edge does not by itself prove that the literal
current census requires Gate-1A. -/
theorem providerArrowIsConditional :
    edge Node.packetCensus Node.gate1A = true ∧
      ¬ Ford.Gate1ARequired Ford.repositoryCensus :=
  ⟨rfl, Ford.gate1ARequired_not_derivable_from_empty_census⟩

/-- All current project-local nodes. -/
def allNodes : List Node :=
  [Node.gate0, Node.packetCensus, Node.gate1A, Node.gate1B,
   Node.gate2, Node.fullFMTypeII, Node.twinPrimes]

/-- Gate 0 is a source of the current project-local graph. -/
theorem gate0_is_a_source :
    (allNodes.filter (fun a => a != Node.gate0)).all
      (fun a => !(reach a Node.gate0)) = true := by
  decide

end Graph
end CurrentProgramme
end TwinPrimeProject
