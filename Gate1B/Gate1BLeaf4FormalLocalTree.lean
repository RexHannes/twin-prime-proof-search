import Mathlib

/-!
# Gate 1B · Leaf-4 formal local tree, Bézout-row arithmetic and convolution firewall

**Append-only.**  This module adds *new* declarations only.  No historical
Gate 1B module is imported for modification, none is edited, and nothing here
re-interprets an older algebraic theorem as an analytic closure.

Everything proved here is **unconditional integer / algebraic arithmetic** or a
purely formal (symbolic) construction.  No analytic estimate is proved and none
is assumed.

## Contents

* §1 Bézout-row normal form: `bezoutRow_det_invariant`,
  `scaledBezoutRow_det_invariant` — the row determinant is invariant along the
  Bézout line, and scales by `d` after multiplication by `d`.
* §2 product-difference arithmetic: `gate1B_leaf4_productDifference` and its
  literal `N = ℓ·r` form `gate1B_leaf4_productDifference_shift`, the arithmetic
  kernel of the research label `HZERO-J4-ALPHA4-PRODUCTDIFF45`.
* §3 **Dirichlet vs additive convolution firewall**: two *separate* namespaces
  `DirichletConv` and `AdditiveConv`, plus an explicit countermodel
  `dirichlet_ne_additive_conv` proving the two operations are not the same.
  No universal inequality between them is claimed.
* §4 the **noncommutative major-tree interface** `MajorTreeInterface` with the
  ordered local slots `M1, M2, M3, M5`, ordered composition, and a countermodel
  `majorTree_comp_not_commutative` forbidding the replacement of ordered
  composition by scalar multiplication.
* §5 the **formal Leaf-4 split** `γ₄ = γ₄Loc + γ₄Rem` with `ρ₅ = δ₅ − λ₅`, the
  symbolic coefficients `c44Loc = λ₁ *_D λ₂ *_D λ₃ *_D λ₅` and
  `c45 = λ₁ *_D λ₂ *_D λ₃ *_D λ₄`, associativity of the Dirichlet product, and
  the **owner firewall** `c44Loc_ne_c45`: bare Leaf 5 is *not* the Leaf-4 owner.
  The equality `c44Loc = c45` is proved **only** under the explicit hypothesis
  `λ₄ = λ₅`.

The research reading of these facts (analytic status, source pins) lives in
`Gate1B.Gate1BLeaf4RowLocalStatus`; it is metadata, never a theorem.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Gate1BRowLocal

/-! ## 1. Bézout-row normal form (unconditional integer algebra)

With `a_h = a₀ + f·h`, `b_h = b₀ + c·h` and `f·b₀ − c·a₀ = N`, the row
determinant `f·b_h − c·a_h` is *invariant* in `h`. -/

/-- The Bézout row `a_h = a₀ + f·h`. -/
def aRow (a0 f h : ℤ) : ℤ := a0 + f * h

/-- The Bézout row `b_h = b₀ + c·h`. -/
def bRow (b0 c h : ℤ) : ℤ := b0 + c * h

/-- **Bézout-row determinant invariance.**  If `f·b₀ − c·a₀ = N` then
`f·b_h − c·a_h = N` for every `h`. -/
theorem bezoutRow_det_invariant (a0 b0 c f N h : ℤ) (hdet : f * b0 - c * a0 = N) :
    f * bRow b0 c h - c * aRow a0 f h = N := by
  simp only [aRow, bRow]
  linear_combination hdet

/-- **Scaled Bézout-row determinant.**  With `A_h = d·a_h` and `B_h = d·b_h`,
`f·B_h − c·A_h = d·N`. -/
theorem scaledBezoutRow_det_invariant (a0 b0 c f d N h : ℤ) (hdet : f * b0 - c * a0 = N) :
    f * (d * bRow b0 c h) - c * (d * aRow a0 f h) = d * N := by
  simp only [aRow, bRow]
  linear_combination d * hdet

/-! ## 2. Product-difference arithmetic

`HZERO-J4-ALPHA4-PRODUCTDIFF45`, arithmetic kernel only. -/

/-- **Leaf-4 product difference.**  If `u₁v₁ = A_h = d·a_h` and
`u₂v₂ = B_h = d·b_h` with `f·b₀ − c·a₀ = N`, then

`c·u₁·v₁ − f·u₂·v₂ = −d·N`.

Unconditional integer algebra; no analytic assumption. -/
theorem gate1B_leaf4_productDifference
    (u1 v1 u2 v2 a0 b0 c f d N h : ℤ)
    (hdet : f * b0 - c * a0 = N)
    (h1 : u1 * v1 = d * aRow a0 f h)
    (h2 : u2 * v2 = d * bRow b0 c h) :
    c * u1 * v1 - f * u2 * v2 = -(d * N) := by
  have h1' : c * u1 * v1 = c * (u1 * v1) := by ring
  have h2' : f * u2 * v2 = f * (u2 * v2) := by ring
  rw [h1', h2', h1, h2]
  simp only [aRow, bRow]
  linear_combination (-d) * hdet

/-- **Literal `N = ℓ·r` form.**  `c·u₁·v₁ − f·u₂·v₂ = −d·ℓ·r`, matching the
literal identity recorded under `HZERO-J4-ALPHA4-PRODUCTDIFF45`. -/
theorem gate1B_leaf4_productDifference_shift
    (u1 v1 u2 v2 a0 b0 c f d ell r h : ℤ)
    (hdet : f * b0 - c * a0 = ell * r)
    (h1 : u1 * v1 = d * aRow a0 f h)
    (h2 : u2 * v2 = d * bRow b0 c h) :
    c * u1 * v1 - f * u2 * v2 = -(d * ell * r) := by
  have := gate1B_leaf4_productDifference u1 v1 u2 v2 a0 b0 c f d (ell * r) h hdet h1 h2
  rw [this]; ring

/-! ## 3. Dirichlet vs additive convolution firewall

The two convolutions are given **separate namespaces and separate names**, and
an explicit countermodel shows they are not the same operation.  No universal
inequality between them is proved or assumed. -/

namespace DirichletConv

/-- Dirichlet convolution, as the ring multiplication of `ArithmeticFunction ℂ`.
Written `f *_D g` in the reports. -/
def dmul (f g : ArithmeticFunction ℂ) : ArithmeticFunction ℂ := f * g

@[simp] theorem dmul_apply (f g : ArithmeticFunction ℂ) (n : ℕ) :
    dmul f g n = ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2 := by
  simp [dmul, ArithmeticFunction.mul_apply]

theorem dmul_assoc (f g h : ArithmeticFunction ℂ) :
    dmul (dmul f g) h = dmul f (dmul g h) := by
  simp [dmul, mul_assoc]

theorem dmul_comm (f g : ArithmeticFunction ℂ) : dmul f g = dmul g f := by
  simp [dmul, mul_comm]

end DirichletConv

namespace AdditiveConv

/-- Additive (Cauchy) convolution of coefficient sequences.  **Not** the
Dirichlet convolution. -/
noncomputable def aconv (f g : ℕ → ℂ) : ℕ → ℂ := fun n => ∑ k ∈ Finset.range (n + 1), f k * g (n - k)

@[simp] theorem aconv_apply (f g : ℕ → ℂ) (n : ℕ) :
    aconv f g n = ∑ k ∈ Finset.range (n + 1), f k * g (n - k) := rfl

end AdditiveConv

/-- **Firewall (countermodel).**  Dirichlet convolution and additive convolution
are *different* operations: for `f = δ₁` (the unit of `ArithmeticFunction ℂ`),
`(f *_D f)(1) = 1` while `aconv f f 1 = 0`.

Consequently no proof in this bank may silently identify the two. -/
theorem dirichlet_ne_additive_conv :
    ∃ f : ArithmeticFunction ℂ,
      DirichletConv.dmul f f 1 ≠ AdditiveConv.aconv (fun n => f n) (fun n => f n) 1 := by
  refine ⟨1, ?_⟩
  have hD : DirichletConv.dmul (1 : ArithmeticFunction ℂ) 1 1 = 1 := by
    simp [DirichletConv.dmul]
  have hA : AdditiveConv.aconv (fun n => (1 : ArithmeticFunction ℂ) n)
      (fun n => (1 : ArithmeticFunction ℂ) n) 1 = 0 := by
    simp [AdditiveConv.aconv, Finset.sum_range_succ]
  rw [hD, hA]
  exact one_ne_zero

/-! ## 4. Noncommutative major-tree interface

The ordered major dilation operators are exposed as an *interface*; no analytic
major operator is constructed here.  Ordered composition is never replaced by
scalar multiplication. -/

/-- Formal type of a major dilation operator acting on coefficient sequences. -/
abbrev MajorOp : Type := (ℕ → ℂ) → (ℕ → ℂ)

/-- The ordered local slots of the alpha-side major tree.  The four fields are
*ordered*: `M1` and `M2` are the `α₄`-side slots, `M3` and `M5` the `γ₄`-side
local slots. -/
structure MajorTreeInterface where
  /-- First ordered major dilation slot. -/
  M1 : MajorOp
  /-- Second ordered major dilation slot. -/
  M2 : MajorOp
  /-- Third ordered major dilation slot. -/
  M3 : MajorOp
  /-- Fifth (local) ordered major dilation slot. -/
  M5 : MajorOp

namespace MajorTreeInterface

/-- Ordered `α`-side composition `M1 ∘ M2`. -/
def alphaComp (T : MajorTreeInterface) : MajorOp := T.M1 ∘ T.M2

/-- Ordered `γ`-side local composition `M3 ∘ M5`. -/
def gammaLocComp (T : MajorTreeInterface) : MajorOp := T.M3 ∘ T.M5

/-- The full ordered local composition `M1 ∘ M2 ∘ M3 ∘ M5`. -/
def localComp (T : MajorTreeInterface) : MajorOp := T.M1 ∘ T.M2 ∘ T.M3 ∘ T.M5

/-- The ordered list of local slots, in the order they occur in the tree. -/
def slots (T : MajorTreeInterface) : List MajorOp := [T.M1, T.M2, T.M3, T.M5]

@[simp] theorem slots_length (T : MajorTreeInterface) : T.slots.length = 4 := rfl

theorem localComp_eq_alpha_comp_gammaLoc (T : MajorTreeInterface) :
    T.localComp = T.alphaComp ∘ T.gammaLocComp := rfl

end MajorTreeInterface

/-- The formal Leaf-4 local tree: the ordered slots `M1, M2, M3, M5` of the
*full recursive broad-major tree*, packaged as data. -/
structure Leaf4FormalLocalTree where
  /-- The underlying ordered major-tree interface. -/
  tree : MajorTreeInterface

namespace Leaf4FormalLocalTree

/-- The ordered local composition owned by the `j = 4` component. -/
def comp (L : Leaf4FormalLocalTree) : MajorOp := L.tree.localComp

/-- The ordered slots of the Leaf-4 local tree. -/
def slots (L : Leaf4FormalLocalTree) : List MajorOp := L.tree.slots

@[simp] theorem slots_length (L : Leaf4FormalLocalTree) : L.slots.length = 4 := rfl

end Leaf4FormalLocalTree

/-- **Firewall (countermodel).**  Composition of major slots is *not*
commutative, so the ordered tree may not be replaced by a scalar (commutative)
product; in particular `Fourier(α₄) = Fourier(λ₁)·Fourier(λ₂)` is not available
and is deliberately not formalised. -/
theorem majorTree_comp_not_commutative :
    ∃ S T : MajorOp, S ∘ T ≠ T ∘ S := by
  refine ⟨fun f => fun _ => f 0, fun f => fun n => f (n + 1), ?_⟩
  intro hcomp
  have h := congrFun (congrFun hcomp (fun n => if n = 1 then (1 : ℂ) else 0)) 0
  simp at h

/-! ## 5. Formal Leaf-4 split and the owner identity

All coefficients are symbolic elements of `ArithmeticFunction ℂ`; `*_D` is the
Dirichlet product `DirichletConv.dmul`. -/

/-- `α₄ = λ₁ *_D λ₂` at the symbolic coefficient level.  (The *operator* level
is the ordered `MajorTreeInterface.alphaComp`, which is `noncommutative` and is
never identified with this scalar product.) -/
def alpha4 (l1 l2 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ := DirichletConv.dmul l1 l2

/-- `γ₄ = λ₃ *_D δ₅`. -/
def gamma4 (l3 d5 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ := DirichletConv.dmul l3 d5

/-- `ρ₅ := δ₅ − λ₅`. -/
noncomputable def rho5 (d5 l5 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ := d5 - l5

/-- `γ₄Loc := λ₃ *_D λ₅`. -/
def gamma4Loc (l3 l5 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ := DirichletConv.dmul l3 l5

/-- `γ₄Rem := λ₃ *_D ρ₅`. -/
noncomputable def gamma4Rem (l3 d5 l5 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  DirichletConv.dmul l3 (rho5 d5 l5)

/-- **Formal Leaf-4 split.**  `γ₄ = γ₄Loc + γ₄Rem`. -/
theorem gamma4_split (l3 d5 l5 : ArithmeticFunction ℂ) :
    gamma4 l3 d5 = gamma4Loc l3 l5 + gamma4Rem l3 d5 l5 := by
  simp [gamma4, gamma4Loc, gamma4Rem, rho5, DirichletConv.dmul, mul_sub]

/-- The formal Leaf-4 **local** coefficient
`c44Loc = λ₁ *_D λ₂ *_D λ₃ *_D λ₅`. -/
def c44Loc (l1 l2 l3 l5 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  DirichletConv.dmul (DirichletConv.dmul (DirichletConv.dmul l1 l2) l3) l5

/-- The **bare Leaf-5** coefficient `c45 = λ₁ *_D λ₂ *_D λ₃ *_D λ₄`. -/
def c45 (l1 l2 l3 l4 : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  DirichletConv.dmul (DirichletConv.dmul (DirichletConv.dmul l1 l2) l3) l4

/-- `c44Loc` is the ordered Dirichlet product of the `α₄` block with the local
`γ₄` block: `c44Loc = (λ₁ *_D λ₂) *_D (λ₃ *_D λ₅)`, by associativity. -/
theorem c44Loc_eq_alpha4_dmul_gamma4Loc (l1 l2 l3 l5 : ArithmeticFunction ℂ) :
    c44Loc l1 l2 l3 l5 = DirichletConv.dmul (alpha4 l1 l2) (gamma4Loc l3 l5) := by
  simp [c44Loc, alpha4, gamma4Loc, DirichletConv.dmul, mul_assoc]

/-- Associativity normal form of `c45`. -/
theorem c45_eq_alpha4_dmul (l1 l2 l3 l4 : ArithmeticFunction ℂ) :
    c45 l1 l2 l3 l4 = DirichletConv.dmul (alpha4 l1 l2) (DirichletConv.dmul l3 l4) := by
  simp [c45, alpha4, DirichletConv.dmul, mul_assoc]

/-- **Conditional** identification of the Leaf-4 local coefficient with the bare
Leaf-5 coefficient.  It requires the *explicitly supplied* source equality
`λ₄ = λ₅`, which is **not** available in the current bank. -/
theorem c44Loc_eq_c45_of_lambda4_eq_lambda5
    (l1 l2 l3 l4 l5 : ArithmeticFunction ℂ) (h : l4 = l5) :
    c44Loc l1 l2 l3 l5 = c45 l1 l2 l3 l4 := by
  simp [c44Loc, c45, h]

/-- **Owner firewall (countermodel).**  Without an extra source equality,
`c44Loc ≠ c45`: bare Leaf 5 is *not* the Leaf-4 owner.  Witness: all of
`λ₁, λ₂, λ₃, λ₅` the Dirichlet unit and `λ₄ = 0`. -/
theorem c44Loc_ne_c45 :
    ∃ l1 l2 l3 l4 l5 : ArithmeticFunction ℂ, c44Loc l1 l2 l3 l5 ≠ c45 l1 l2 l3 l4 := by
  refine ⟨1, 1, 1, 0, 1, ?_⟩
  intro hEq
  have h1 : c44Loc (1 : ArithmeticFunction ℂ) 1 1 1 1 = 1 := by
    simp [c44Loc, DirichletConv.dmul]
  have h0 : c45 (1 : ArithmeticFunction ℂ) 1 1 0 1 = 0 := by
    simp [c45, DirichletConv.dmul]
  have hval := congrArg (fun F : ArithmeticFunction ℂ => F 1) hEq
  simp only [] at hval
  rw [h1, h0] at hval
  exact one_ne_zero hval

end Gate1BRowLocal
end CurrentProgramme
end TwinPrimeProject
