/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the JCORE formal object  (J1)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted, and no
analytic proposition is inhabited anywhere in this directory.

The JCORE object of the current joint-core route is formalised here as a **finite, abstract**
moment: the analytic weights are kept as an abstract finite coefficient family, and all
admissibility conditions are explicit predicates.  The variables are kept distinct:

```
outer :  (e, z, k)          core :  (n, u, v)          second copy :  (ñ, ũ, ṽ)
```

The second copy appears through the *square expansion* of the moment (§3), never by fiat, and
**no cross-copy coprimality is assumed**: in particular `(u, ṽ) = 1` and `(ũ, v) = 1` are not
part of the admissibility predicate and are not used anywhere in this directory.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.CRTPhase

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The variables -/

/-- The outer (source) variables of the JCORE object: the reciprocity variable `e`, the source
variable `z` and the small label `k`. -/
structure Outer where
  /-- reciprocity variable -/
  e : ℕ
  /-- source variable -/
  z : ℕ
  /-- small label -/
  k : ℕ
  deriving DecidableEq

/-- The core variables of the JCORE object: the (signed) dual frequency `n` and the two
denominators `u`, `v`.  The second copy `(ñ, ũ, ṽ)` is another term of the same type. -/
structure Core where
  /-- signed dual frequency -/
  n : ℤ
  /-- first denominator -/
  u : ℕ
  /-- second denominator -/
  v : ℕ
  deriving DecidableEq

namespace Core

/-- The denominator `uv` of a core point. -/
def den (i : Core) : ℕ := i.u * i.v

end Core

/-! ## 2. Admissibility masks -/

/-- **The dual support mask** of a core point: positive denominators and the banked dual support
coprimality `(n, uv) = 1`.  Nothing else — in particular no cross-copy condition. -/
structure CoreAdmissible (i : Core) : Prop where
  /-- `u > 0` -/
  upos : 0 < i.u
  /-- `v > 0` -/
  vpos : 0 < i.v
  /-- the banked dual support condition `(n, uv) = 1` -/
  coprime : Nat.Coprime i.n.natAbs i.den

/-- **The outer admissibility mask**: positive source and reciprocity variables. -/
structure OuterAdmissible (o : Outer) : Prop where
  /-- `e > 0` -/
  epos : 0 < o.e
  /-- `z > 0` -/
  zpos : 0 < o.z

/-- The core denominator is positive on the mask. -/
theorem den_pos {i : Core} (h : CoreAdmissible i) : 0 < i.den :=
  Nat.mul_pos h.upos h.vpos

/-- **No cross-copy coprimality is implied by the masks.**  Two admissible core points may have
`(u, ṽ) > 1` and `(ũ, v) > 1` simultaneously: the JCORE object may not be simplified by assuming
these. -/
theorem masks_do_not_give_cross_coprimality :
    ∃ i j : Core, CoreAdmissible i ∧ CoreAdmissible j
      ∧ 1 < Nat.gcd i.u j.v ∧ 1 < Nat.gcd j.u i.v := by
  refine ⟨⟨1, 2, 2⟩, ⟨1, 2, 2⟩, ⟨by norm_num, by norm_num, ?_⟩, ⟨by norm_num, by norm_num, ?_⟩,
    by norm_num, by norm_num⟩ <;>
  · show Nat.Coprime (1 : ℤ).natAbs (2 * 2)
    norm_num

/-! ## 3. The JCORE moment and its square expansion -/

/-- **The JCORE moment**: an outer sum of the squared modulus of the core sum, with an abstract
finite coefficient family `F`.  No analytic property of `F` is assumed. -/
noncomputable def jMoment (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) : ℝ :=
  ∑ o ∈ O, ‖∑ i ∈ Iset, F o i‖ ^ 2

/-- **The square expansion of the JCORE moment**: two copies of the core variables. -/
noncomputable def jExpand (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) : ℂ :=
  ∑ o ∈ O, ∑ i ∈ Iset, ∑ j ∈ Iset, F o i * (starRingEnd ℂ) (F o j)

/-- The moment *is* its square expansion: the second copy `(ñ, ũ, ṽ)` of the core variables is
produced by the expansion, not assumed. -/
theorem jMoment_eq_jExpand (O : Finset Outer) (Iset : Finset Core) (F : Outer → Core → ℂ) :
    ((jMoment O Iset F : ℝ) : ℂ) = jExpand O Iset F := by
  unfold jMoment jExpand
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun o _ => ?_
  have h2 : ((‖∑ i ∈ Iset, F o i‖ ^ 2 : ℝ) : ℂ)
      = (∑ i ∈ Iset, F o i) * (starRingEnd ℂ) (∑ i ∈ Iset, F o i) := by
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [h2, map_sum, Finset.sum_mul_sum]

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
