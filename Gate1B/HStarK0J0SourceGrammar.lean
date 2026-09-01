import Gate1B.HStarK0J0VaughanCentering

/-!
# Gate 1B · the HSTAR `k = 0`, `J = ∅` **source** type and the source-factor firewall

**Source/algebraic DATA only.**  This module records the literal first HSTAR
parent *before* the Ford supremum, as a finite data type.  It does **not**
formalise the analytic statement that any Ford lemma produces the
decomposition; the nuclearization side is a separate, uninhabited certificate
interface (`Gate1B.HStarFiniteNuclearCompiler`).

## Contents

* §1 the discrete grammar: source kinds, endpoint branches, dyadic supports,
  block-depth bounds and the finite Perron parameter index;
* §2 `HStarK0J0Source`, the first-parent source type, with `k = 0`, `J = ∅`,
  `g_∅ = 1` enforced by fields, and the two source kinds kept distinct;
* §3 the **source factor firewall**: `uBase e = μ(e) · twist e` versus
  `vBase e = twist e`; the two are provably different functions, the `u`-side
  is supported on squarefree arguments while a unit twist never vanishes, and
  no common coefficient family contains both;
* §4 the **strict prime-support ordering** carried by the `u`-side only.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset ArithmeticFunction

/-! ## 1. Discrete grammar -/

/-- The two source kinds occurring in the HSTAR first parent. -/
inductive HStarSourceKind
  /-- Squarefree Möbius multiplicative source (the `u`-side). -/
  | squarefreeMoebiusMultiplicative
  /-- Completely multiplicative unit twist (the `v`-side). -/
  | completelyMultiplicativeUnitTwist
  deriving DecidableEq, Repr

/-- **Firewall.**  The two source kinds are distinct constructors. -/
theorem hStarSourceKind_u_ne_v :
    HStarSourceKind.squarefreeMoebiusMultiplicative ≠
      HStarSourceKind.completelyMultiplicativeUnitTwist := by decide

/-- The discrete endpoint branches of the first parent. -/
inductive HStarEndpointBranch
  | leftEndpoint
  | interior
  | rightEndpoint
  deriving DecidableEq, Repr

/-- A dyadic support interval `[lo, hi]`. -/
structure DyadicSupport where
  lo : ℕ
  hi : ℕ
  lo_le_hi : lo ≤ hi
  deriving Repr

/-- The **finite** Perron parameter index.  The continuous Perron integral is
an external analytic object and is *not* represented here; only a finite
surrogate index is. -/
structure PerronParameterIndex where
  idx : ℕ
  deriving DecidableEq, Repr

/-! ## 2. The HSTAR `k = 0`, `J = ∅` source type -/

/-- The literal first HSTAR parent, as **source data only**: no analytic
content, no bound, no integral. -/
structure HStarK0J0Source where
  /-- The block index `k`, pinned to `0`. -/
  k : ℕ
  k_eq : k = 0
  /-- The index set `J`, pinned to `∅`. -/
  J : Finset ℕ
  J_eq : J = ∅
  /-- The empty-set coefficient `g_∅`, pinned to `1`. -/
  gEmpty : ℂ
  gEmpty_eq : gEmpty = 1
  /-- The `u`-source kind. -/
  uKind : HStarSourceKind
  uKind_eq : uKind = HStarSourceKind.squarefreeMoebiusMultiplicative
  /-- The `v`-source kind. -/
  vKind : HStarSourceKind
  vKind_eq : vKind = HStarSourceKind.completelyMultiplicativeUnitTwist
  /-- Block-depth bounds. -/
  depthLo : ℕ
  depthHi : ℕ
  depth_le : depthLo ≤ depthHi
  /-- Support intervals of the two sides. -/
  uSupport : DyadicSupport
  vSupport : DyadicSupport
  /-- The discrete endpoint branch. -/
  endpoint : HStarEndpointBranch
  /-- The finite Perron parameter index. -/
  perron : PerronParameterIndex

namespace HStarK0J0Source

variable (S : HStarK0J0Source)

theorem k_is_zero : S.k = 0 := S.k_eq

theorem J_is_empty : S.J = ∅ := S.J_eq

theorem gEmpty_is_one : S.gEmpty = 1 := S.gEmpty_eq

/-- **The two sides of the first parent never carry the same source kind.** -/
theorem uKind_ne_vKind : S.uKind ≠ S.vKind := by
  rw [S.uKind_eq, S.vKind_eq]
  exact hStarSourceKind_u_ne_v

end HStarK0J0Source

/-! ## 3. Source factor firewall -/

/-- A **unit twist**: a completely multiplicative unit-modulus decoration.  Only
the unit-modulus property is used. -/
structure UnitTwist where
  twist : ℕ → ℂ
  norm_one : ∀ e, ‖twist e‖ = 1

/-- The `u`-base factor `μ(e) · twist(e)`. -/
noncomputable def uBase (t : UnitTwist) (e : ℕ) : ℂ :=
  (ArithmeticFunction.moebius e : ℂ) * t.twist e

/-- The `v`-base factor `twist(e)`: no Möbius factor, no squarefree
restriction. -/
noncomputable def vBase (t : UnitTwist) (e : ℕ) : ℂ := t.twist e

/-- The trivial unit twist `e ↦ 1`. -/
noncomputable def oneTwist : UnitTwist := ⟨fun _ => 1, by simp⟩

/-- The `u`-side vanishes off the squarefree numbers. -/
theorem uBase_eq_zero_of_not_squarefree (t : UnitTwist) {e : ℕ} (h : ¬ Squarefree e) :
    uBase t e = 0 := by
  rw [uBase, ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
  simp

/-- The `v`-side never vanishes: a unit twist has modulus one everywhere. -/
theorem vBase_ne_zero (t : UnitTwist) (e : ℕ) : vBase t e ≠ 0 := by
  intro h
  have := t.norm_one e
  rw [show t.twist e = (0 : ℂ) from h] at this
  simp at this

/-- **Source factor firewall.**  The `u`-base and the `v`-base are genuinely
different coefficient families: at `e = 4` the `u`-side vanishes and the
`v`-side does not. -/
theorem uBase_ne_vBase (t : UnitTwist) : uBase t ≠ vBase t := by
  intro h
  have h4 : uBase t 4 = vBase t 4 := congrFun h 4
  have hz : uBase t 4 = 0 :=
    uBase_eq_zero_of_not_squarefree t (by decide)
  exact vBase_ne_zero t 4 (by rw [← h4, hz])

/-- **No common coefficient family.**  There is no single function that is
simultaneously the `u`-base and the `v`-base of the same twist. -/
theorem no_common_source_family (t : UnitTwist) :
    ¬ ∃ F : ℕ → ℂ, F = uBase t ∧ F = vBase t := by
  rintro ⟨F, h1, h2⟩
  exact uBase_ne_vBase t (h1 ▸ h2)

/-! ## 4. Strict prime-support ordering (the `u`-side only) -/

/-- A `u`-block records a **strictly increasing** prime list. -/
structure UBlockPrimeSupport where
  primes : List ℕ
  sorted : primes.Pairwise (· < ·)

/-- A `v`-block records an arbitrary list: no ordering, no multiplicity
restriction. -/
structure VBlockSupport where
  entries : List ℕ

/-- Strict ordering forces distinctness on the `u`-side. -/
theorem uBlock_primes_nodup (b : UBlockPrimeSupport) : b.primes.Nodup :=
  List.Pairwise.nodup b.sorted

/-- The `v`-side carries no such restriction: `[2, 2]` is an admissible
`v`-support but not a `u`-support. -/
theorem vBlock_support_not_strictly_ordered :
    ∃ b : VBlockSupport, ¬ b.entries.Pairwise (· < ·) := by
  refine ⟨⟨[2, 2]⟩, ?_⟩
  intro h
  have : ([2, 2] : List ℕ).Nodup := List.Pairwise.nodup h
  simp at this

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
