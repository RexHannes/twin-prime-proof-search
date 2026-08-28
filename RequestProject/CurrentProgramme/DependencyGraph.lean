import RequestProject.CurrentProgramme.CurrentStatus

/-!
# Phase L · master dependency graph (machine-readable)

The canonical architecture is preserved:

```
  finite source / Gate 0
        |
        v
  generated packet census
     /             \
    v               v
 Gate 1A          Gate 1B
    \               /
     \             /
        Gate 2
          |
          v
  Ford-generated packet / leakage reassembly
          |
          v
  fixed-certificate leakage + comparison + effectivity
          |
          v
  positive affine mass
          |
          v
  WindowPairSupply
          |
          v
  existing finite compiler
          |
          v
  Erdős #287
```

Provider arrows out of the census are **census-determined**: `Node.gate1A` and
`Node.gate1B` are reachable from `Node.packetCensus` only when the literal
census demands them.  Since the census is unpopulated (see
`Ford.census_is_source_open`), those arrows are recorded as *conditional*.

The twin-prime programme keeps its **separate** downstream graph, and
`no_cross_implication` records that neither conclusion implies the other in
this graph.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Graph

/-- Nodes of the current master dependency graph. -/
inductive Node where
  /-- Finite source / Gate 0. -/
  | gate0
  /-- Generated packet census. -/
  | packetCensus
  /-- Gate-1A provider layer. -/
  | gate1A
  /-- Gate-1B provider layer. -/
  | gate1B
  /-- Gate 2. -/
  | gate2
  /-- Ford-generated packet / leakage reassembly. -/
  | fordReassembly
  /-- Fixed-certificate leakage + comparison + effectivity. -/
  | fcl
  /-- Positive affine mass. -/
  | positiveAffineMass
  /-- WindowPairSupply. -/
  | windowPairSupply
  /-- The finite #287 compiler. -/
  | finiteCompiler287
  /-- Erdős problem #287. -/
  | erdos287
  /-- Full Ford–Maynard Type II. -/
  | fullFMTypeII
  /-- Twin prime conjecture (separate downstream). -/
  | twinPrimes
  deriving DecidableEq, Repr, Inhabited

/-- Directed edges of the master graph.  `gate1A`/`gate1B` sit downstream of the
census, and the arrow into `gate2` from each provider is present only in the
architecture sense: see `providerArrowIsConditional`. -/
def edge : Node → Node → Bool
  | Node.gate0, Node.packetCensus => true
  | Node.packetCensus, Node.gate1A => true
  | Node.packetCensus, Node.gate1B => true
  | Node.gate1A, Node.gate2 => true
  | Node.gate1B, Node.gate2 => true
  | Node.gate2, Node.fordReassembly => true
  | Node.gate2, Node.fullFMTypeII => true
  | Node.fordReassembly, Node.fcl => true
  | Node.fcl, Node.positiveAffineMass => true
  | Node.positiveAffineMass, Node.windowPairSupply => true
  | Node.windowPairSupply, Node.finiteCompiler287 => true
  | Node.finiteCompiler287, Node.erdos287 => true
  | Node.fullFMTypeII, Node.twinPrimes => true
  | _, _ => false

/-- Reachability in the master graph (bounded unfolding: the graph is a DAG of
depth at most 12). -/
def reachIn : ℕ → Node → Node → Bool
  | 0, a, b => decide (a = b)
  | (k + 1), a, b =>
      decide (a = b) ||
        (List.any [Node.gate0, Node.packetCensus, Node.gate1A, Node.gate1B,
                   Node.gate2, Node.fordReassembly, Node.fcl,
                   Node.positiveAffineMass, Node.windowPairSupply,
                   Node.finiteCompiler287, Node.erdos287, Node.fullFMTypeII,
                   Node.twinPrimes]
          (fun c => edge a c && reachIn k c b))

/-- Reachability with the full depth. -/
def reach (a b : Node) : Bool := reachIn 13 a b

/-- **L.**  The canonical spine is present: Gate 0 reaches Erdős #287 through
the census, a provider, Gate 2, the Ford reassembly, FCL, positive mass,
`WindowPairSupply` and the finite compiler. -/
theorem spine_present : reach Node.gate0 Node.erdos287 = true := by decide

/-- **L.**  Gate 0 also reaches Full FM Type II and, beyond it, twin primes. -/
theorem twin_branch_present : reach Node.gate0 Node.twinPrimes = true := by decide

/-- **L, firewall.**  Erdős #287 does **not** imply twin primes in this graph. -/
theorem erdos287_does_not_reach_twinPrimes :
    reach Node.erdos287 Node.twinPrimes = false := by decide

/-- **L, firewall.**  Twin primes does not reach Erdős #287 either. -/
theorem twinPrimes_does_not_reach_erdos287 :
    reach Node.twinPrimes Node.erdos287 = false := by decide

/-- **L, firewall.**  No cross-implication in either direction. -/
theorem no_cross_implication :
    reach Node.erdos287 Node.twinPrimes = false ∧
      reach Node.twinPrimes Node.erdos287 = false :=
  ⟨erdos287_does_not_reach_twinPrimes, twinPrimes_does_not_reach_erdos287⟩

/-- **L.**  Not every packet is forced through every gate: `gate1A` does not
reach `gate1B` and vice versa. -/
theorem providers_are_parallel :
    reach Node.gate1A Node.gate1B = false ∧
      reach Node.gate1B Node.gate1A = false := by
  constructor <;> decide

/-- **L, provider-arrow honesty.**  The architecture edge
`packetCensus → gate1A` exists, but whether it is *used* is a derived fact of
the literal census, which is unpopulated.  Recorded as a conjunction so that
neither half can be quoted alone. -/
theorem providerArrowIsConditional :
    edge Node.packetCensus Node.gate1A = true ∧
      ¬ Ford.Gate1ARequired Ford.repositoryCensus :=
  ⟨rfl, Ford.gate1ARequired_not_derivable_from_empty_census⟩

/-- The list of all nodes. -/
def allNodes : List Node :=
  [Node.gate0, Node.packetCensus, Node.gate1A, Node.gate1B, Node.gate2,
   Node.fordReassembly, Node.fcl, Node.positiveAffineMass,
   Node.windowPairSupply, Node.finiteCompiler287, Node.erdos287,
   Node.fullFMTypeII, Node.twinPrimes]

/-- **L.**  The graph is acyclic at the source: no node other than `gate0`
itself reaches `gate0`. -/
theorem gate0_is_a_source :
    (allNodes.filter (fun a => a != Node.gate0)).all
      (fun a => !(reach a Node.gate0)) = true := by decide

end Graph
end CurrentProgramme
end TwinPrimeProject
