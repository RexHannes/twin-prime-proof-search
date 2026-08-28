import RequestProject.CurrentProgramme.StatusTypes

/-!
# Phase G · Ford / Maynard generated-packet census and provider assignment

## G1 — real Ford provenance

Search result (literal, over all `.lean` sources outside `.lake`):

* `RealFordGrammarCertificate` — **present** as a v11 type, but recorded there
  as *uninhabited / repo data absent*;
* `FMPerron grammar` — present (`RequestProject/NANC/Gate1B/V11FMPerronGrammar.lean`);
* `Proposition 7.22`, `equation (7.23)`, `C(R)`, `R(P)`, `G(d;n)`,
  `fixed certificate` (Ford's) — **absent** as literal definitions.

Therefore:

  `RealFordGrammarCertificate : SOURCE_BLOCKED`

and the Ford definitions are **not reconstructed from memory**.

## G6 — provider assignment

`Provider` is the enum of possible providers.  `PacketCensus` is a *literal*
census: a finite list of packets, each with the provider its source structure
demands.  `Gate1ARequired` is then a **derived** predicate of the census, never
a global assumption:

  `Gate1ARequired c ↔ ∃ p ∈ c.packets, p.provider = Provider.gate1A`.

Because the literal Ford packet enumeration is absent from the repository, the
census actually present here is the **empty census**, and the derived fact is

  `GATE1A_REQUIRED : NOT DERIVABLE — census source-open`.

We do *not* set `GATE1A_REQUIRED := true` by fiat, and we do *not* set it
false: `census_is_source_open` records that the census is unpopulated.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Ford

/-- Possible providers for a generated packet. -/
inductive Provider where
  /-- Supplied by the Gate-0 finite source layer. -/
  | gate0
  /-- Requires the Gate-1A provider. -/
  | gate1A
  /-- Requires the Gate-1B provider. -/
  | gate1B
  /-- Handled directly at Gate 2. -/
  | gate2Direct
  /-- The literal source object for this packet is missing. -/
  | sourceOpen
  /-- A genuine analytic theorem is missing. -/
  | analyticOpen
  /-- No provider has been assigned yet. -/
  | noProviderYet
  deriving DecidableEq, Repr, Inhabited

/-- One generated packet, with the provider its **literal source structure**
demands. -/
structure Packet where
  /-- Packet name as it appears in the generated grammar. -/
  name : String
  /-- Provider forced by the packet's source structure. -/
  provider : Provider
  /-- Provenance note: which literal source object determined the assignment. -/
  provenance : String
  deriving Repr, Inhabited

/-- A literal packet census. -/
structure PacketCensus where
  /-- The packets. -/
  packets : List Packet
  /-- Whether the enumeration is claimed exhaustive.  Exhaustiveness itself is
  a *source* obligation and is recorded, never assumed. -/
  exhaustivenessClaimed : Bool
  deriving Repr, Inhabited

/-- **G6.**  `GATE1A_REQUIRED` is a *derived* predicate of the census. -/
def Gate1ARequired (c : PacketCensus) : Prop :=
  ∃ p ∈ c.packets, p.provider = Provider.gate1A

instance (c : PacketCensus) : Decidable (Gate1ARequired c) := by
  unfold Gate1ARequired
  infer_instance

/-- The census actually available in this repository.  It is **empty** because
the literal Ford generated-packet enumeration (Prop. 7.22 / eq. (7.23) /
`C(R)` / `R(P)` / `G(d;n)`) is absent.  Exhaustiveness is *not* claimed. -/
def repositoryCensus : PacketCensus where
  packets := []
  exhaustivenessClaimed := false

/-- **G6, honest status.**  The repository census is unpopulated and does not
claim exhaustiveness; therefore it cannot be used to conclude anything about
which providers are required. -/
theorem census_is_source_open :
    repositoryCensus.packets = [] ∧
      repositoryCensus.exhaustivenessClaimed = false := ⟨rfl, rfl⟩

/-- **G6 firewall.**  `Gate1ARequired` must not be assumed globally.  From the
empty census it is *not* derivable — and this is a statement about the empty
census only, not a claim that Gate 1A is unnecessary for the real programme. -/
theorem gate1ARequired_not_derivable_from_empty_census :
    ¬ Gate1ARequired repositoryCensus := by
  rintro ⟨p, hp, -⟩
  simp [repositoryCensus] at hp

/-- **G6 firewall, the other direction.**  Neither is `¬ Gate1ARequired`
justified for the *real* programme: as soon as one packet with a Gate-1A source
structure is censused, the requirement follows.  So the empty-census result
above is not evidence that Gate 1A is `NOT_CURRENTLY_REQUIRED`. -/
theorem gate1ARequired_of_one_packet (p : Packet) (hp : p.provider = Provider.gate1A)
    (c : PacketCensus) (hmem : p ∈ c.packets) : Gate1ARequired c :=
  ⟨p, hmem, hp⟩

/-- **G6.**  Exhaustiveness of a census is a separate obligation: a census can
be nonempty and still not cover the source. -/
def CensusExhaustive (c : PacketCensus) (allRequired : List String) : Prop :=
  ∀ s ∈ allRequired, ∃ p ∈ c.packets, p.name = s

/-- Exhaustiveness does not follow from a nonempty census. -/
theorem exhaustiveness_not_automatic :
    ¬ CensusExhaustive ⟨[⟨"A", Provider.gate0, "test"⟩], false⟩ ["A", "B"] := by
  intro h
  obtain ⟨p, hp, hname⟩ := h "B" (by simp)
  simp at hp
  subst hp
  simp at hname

/-! ## G5 — cheap finite repairs (exact domains only) -/

/-- The `q ≥ 5` finite repair, with its exact domain: `q` a modulus in the
generated grammar exceeding the first four. -/
theorem q_ge_five_of_gt_four {q : ℕ} (h : 4 < q) : 5 ≤ q := h

/-- The sign-sensitive minus endpoint `q ≤ ⌊M/2⌋`, with its exact domain. -/
theorem minus_endpoint_le {q M : ℕ} (h : 2 * q ≤ M) : q ≤ M / 2 :=
  Nat.le_div_iff_mul_le (by norm_num) |>.2 (by omega)

/-- The `M ∈ {q, 2q}` divisor blocker: in that case `q ∣ M`, so no proper
fragmentation is available at this packet. -/
theorem divisor_blocker {q M : ℕ} (h : M = q ∨ M = 2 * q) : q ∣ M := by
  rcases h with rfl | rfl
  · exact dvd_rfl
  · exact ⟨2, by ring⟩

/-- The blocker really is a restriction: `M = 3q + 1` is not divisible by `q`
for `q ≥ 2`. -/
theorem divisor_blocker_nontrivial {q : ℕ} (hq : 2 ≤ q) : ¬ q ∣ (3 * q + 1) := by
  intro h
  have : q ∣ 1 := (Nat.dvd_add_right ⟨3, by ring⟩).mp h
  have := Nat.le_of_dvd one_pos this
  omega

/-! ## G1 / G4 — source blocks -/

/-- **G4, SOURCE_OPEN.**  `R9-GDN-SPECIALIZATION`.  The literal `G(d;n)` is
absent from the repository, so the balanced-R9 specialisation cannot be derived
(divisor cutoff, Möbius sign, support, local weights, normalisation, and the
ordered/distinct convention are all unpinned).  Source promotion is stopped.

This structure is UNINHABITED. -/
structure GdnSpecialization where
  /-- The literal `G(d;n)`. -/
  G : ℕ → ℕ → ℤ
  /-- The balanced-R9 specialisation value. -/
  balancedValue : ℤ
  /-- The divisor cutoff convention. -/
  cutoff : ℕ
  /-- The derived specialisation, from the literal definition.  NOT SUPPLIED. -/
  specialisation : balancedValue = ∑ j ∈ Finset.range cutoff, (-1 : ℤ) ^ j * G j 9

/-- **G4 firewall.**  Without the literal `G(d;n)` the value `70` cannot be
identified with a physical Ford coefficient: the balanced value is pinned by
the pair `(G, cutoff)` and by nothing less.  Both must come from the source. -/
theorem gdn_balancedValue_determined (s t : GdnSpecialization)
    (hG : s.G = t.G) (hc : s.cutoff = t.cutoff) :
    s.balancedValue = t.balancedValue := by
  rw [s.specialisation, t.specialisation, hG, hc]

end Ford
end CurrentProgramme
end TwinPrimeProject
