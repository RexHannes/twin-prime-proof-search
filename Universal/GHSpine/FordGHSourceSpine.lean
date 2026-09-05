/-
# Universal / GHSpine — banked paper source: the Ford `G/H` spine

**Status of this module: KERNEL_PROVED finite spine arithmetic; the literal Ford
grammar certificate is KEPT UNINHABITED.**

What is banked here, and only this:

* the **`G/H` source spine** as an explicit interface (`FordGHSpine`), with the
  spine equation `H(n) = Σ_{j<cut} (-1)^j G(n,j)` recorded as a *field* of the
  interface rather than as an assumption of the repository;
* the **model spine** `modelG n j = C(n,j)`, `modelH` at the balanced cut, for
  which the spine equation is kernel-proved;
* `balanced R9 ∈ k0J0` — the balanced R9 row of the new census lies in the
  `k0 = J0 = 0` block, hence is classified `P00_R9` and is **not** a top-level
  sibling of the first-parent block (this is the fact that superseded the old
  triple, see `Universal.GHSpine.TopLevelCensus`);
* the **clean strict balanced arithmetic**: with the exact coordinate `1/9`
  (no `η`, no `ε` slack), four coordinates lie strictly below the `1/2` cut and
  five strictly above it, and the resulting alternating spine value is
  `H(9) = 70 = C(8,4)`.

Firewall, kept from the earlier layers and re-stated as theorems here:

* `seventy_is_a_binomial_value_only` — `70` is a value of the model spine and is
  **not** identified with a physical Ford coefficient;
* `RealFordGHGrammarPin` — the obligation that the literal Ford grammar (the
  `G(d;n)` specialisation) produces this spine.  It has **no inhabitant** in this
  repository, and `realFordGHGrammarPin_not_automatic` shows it is a genuine
  obligation.
-/
import Mathlib
import Universal.GHSpine.TopLevelCensus

namespace Universal.GHSpine

/-! ## §1 The `G/H` source spine interface -/

/-- The Ford `G/H` source spine: a pair of paper-source functions together with
the spine equation and the balanced cut at which it is read.  Note that no
estimate is a field of this record. -/
structure FordGHSpine where
  /-- The paper's `G`. -/
  G : ℕ → ℕ → ℤ
  /-- The paper's `H`. -/
  H : ℕ → ℤ
  /-- The balanced cut index. -/
  cut : ℕ
  /-- The spine equation. -/
  spine : ∀ n, H n = ∑ j ∈ Finset.range cut, (-1 : ℤ) ^ j * G n j

/-! ## §2 The model spine and its clean value -/

/-- The model `G`: the binomial coefficients of the `R9` block. -/
def modelG (n j : ℕ) : ℤ := (Nat.choose n j : ℤ)

/-- The model `H` at the balanced cut `5`. -/
def modelH (n : ℕ) : ℤ := ∑ j ∈ Finset.range 5, (-1 : ℤ) ^ j * modelG n j

/-- The model spine satisfies the spine equation by construction. -/
def modelSpine : FordGHSpine where
  G := modelG
  H := modelH
  cut := 5
  spine := fun _ => rfl

/-- **Clean strict balanced value: `H(9) = 70`.** -/
theorem modelH_nine : modelH 9 = 70 := by
  simp [modelH, modelG, Finset.sum_range_succ, Nat.choose]

/-- `70` is the binomial value `C(8,4)`; recorded so that the number is tied to
an explicit combinatorial object and to nothing else. -/
theorem modelH_nine_eq_choose : modelH 9 = (Nat.choose 8 4 : ℤ) := by
  rw [modelH_nine]
  norm_num [Nat.choose]

/-- **Firewall.**  The value `70` depends on the cut: the neighbouring cut gives
a different number, so `70` may not be identified with a physical Ford
coefficient without the literal grammar. -/
theorem seventy_is_a_binomial_value_only :
    modelH 9 = 70 ∧ (∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * modelG 9 j) = -56 ∧
      (70 : ℤ) ≠ -56 := by
  refine ⟨modelH_nine, ?_, by norm_num⟩
  simp [modelG, Finset.sum_range_succ, Nat.choose]

/-! ## §3 Clean strict balanced arithmetic (no `η`, no `ε`) -/

/-- The balanced R9 coordinate. -/
def r9Coord : ℚ := 1 / 9

/-- The nine balanced coordinates sum to `1`. -/
theorem r9_balanced_total : ∑ _i ∈ Finset.range 9, r9Coord = 1 := by
  norm_num [r9Coord]

/-- **Clean strict, lower side.**  Four balanced coordinates lie strictly below
the `1/2` cut — with no perturbation parameter at all. -/
theorem r9_four_below_cut_strict : 4 * r9Coord < 1 / 2 := by
  norm_num [r9Coord]

/-- **Clean strict, upper side.**  Five balanced coordinates lie strictly above
the `1/2` cut. -/
theorem r9_five_above_cut_strict : 1 / 2 < 5 * r9Coord := by
  norm_num [r9Coord]

/-- The balanced coordinate is strictly inside the Type-II window `(0, 1/2)`. -/
theorem r9_coord_in_window : 0 < r9Coord ∧ r9Coord < 1 / 2 := by
  constructor <;> norm_num [r9Coord]

/-- The cut index of the clean strict balanced configuration is exactly the `5`
at which the model spine is read: four coordinates below, five above. -/
theorem clean_cut_is_five :
    4 * r9Coord < 1 / 2 ∧ 1 / 2 < 5 * r9Coord ∧ modelSpine.cut = 5 :=
  ⟨r9_four_below_cut_strict, r9_five_above_cut_strict, rfl⟩

/-! ## §4 `balanced R9 ∈ k0J0` -/

/-- The balanced R9 census row: it sits at `k0 = J0 = 0`. -/
def balancedR9Row : CensusRow := ⟨0, 0, true⟩

/-- **Banked paper source fact:** the balanced R9 row lies in the `k0 = J0 = 0`
block. -/
theorem balancedR9_mem_k0J0 : inK0J0 balancedR9Row := ⟨rfl, rfl⟩

/-- Consequently the balanced R9 row is classified `P00_R9` by the new census:
it is a *sub-class of* the `k0J0` block, not a top-level sibling of it. -/
theorem balancedR9Row_classify : classify balancedR9Row = TopClass.P00_R9 := by
  rw [classify_eq_P00_R9_iff]
  exact ⟨⟨rfl, rfl⟩, rfl⟩

/-- The balanced R9 row is *not* in the `P_ge1` class; this is exactly the
statement that the old `BALANCED_R9` label could not be a disjoint top-level
class. -/
theorem balancedR9Row_not_P_ge1 : classify balancedR9Row ≠ TopClass.P_ge1 := by
  rw [balancedR9Row_classify]
  decide

/-! ## §5 The literal Ford grammar obligation (UNINHABITED) -/

/-- **SOURCE PIN (UNINHABITED here, KEPT UNINHABITED).**  The obligation that the
literal Ford grammar — the `G(d;n)` specialisation of the paper — produces the
spine banked above, i.e. agrees with the model spine on the balanced block and
reads it at the clean cut `5`.  No inhabitant is constructed in this repository:
the literal `G(d;n)` is absent from it, and it is not reconstructed from memory.

This pin is deliberately kept **separate** from the physical Vaughan `(U,V)` pin
and from the physical first-parent census pin: none of the three implies
another. -/
structure RealFordGHGrammarPin (S : FordGHSpine) : Prop where
  /-- The literal grammar is read at the clean balanced cut. -/
  cut_eq : S.cut = 5
  /-- The literal grammar agrees with the model spine on the balanced block. -/
  G_eq : ∀ j ∈ Finset.range 5, S.G 9 j = modelG 9 j

/-- Conditional consequence: *if* the literal grammar pin is supplied, the
literal spine value at the balanced block is `70`.  The pin is not supplied. -/
theorem fordGH_value_of_pin {S : FordGHSpine} (pin : RealFordGHGrammarPin S) :
    S.H 9 = 70 := by
  rw [S.spine 9, pin.cut_eq]
  rw [Finset.sum_congr rfl (fun j hj => by rw [pin.G_eq j hj])]
  exact modelH_nine

/-- The Ford grammar pin is a genuine obligation: it can fail. -/
theorem realFordGHGrammarPin_not_automatic :
    ∃ S : FordGHSpine, ¬ RealFordGHGrammarPin S := by
  refine ⟨⟨fun _ _ => 0, fun _ => 0, 0, fun _ => by simp⟩, ?_⟩
  intro pin
  have h := pin.cut_eq
  simp at h

/-- The three source obligations are kept separate: none of them is a theorem
scheme of this repository. -/
theorem ford_grammar_pin_kept_uninhabited :
    ¬ (∀ S : FordGHSpine, RealFordGHGrammarPin S) := by
  obtain ⟨S, hS⟩ := realFordGHGrammarPin_not_automatic
  exact fun h => hS (h S)

end Universal.GHSpine
