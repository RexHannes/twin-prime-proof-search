/-
# Gate 1B v8.2 — QK5 finite bank: abstract character diagonalization and
  reindexing counterguards

**TIER B policy.**  The concrete Dirichlet-character/Gauss-sum diagonalization

    S(m,n;q) = (1/φ(q)) ∑_{χ mod q} τ_q(χ)² conj(χ(mn))

is **not** proved here.  What is proved is the generic *conditional* finite
identity whose orthogonality relation is an explicit theorem hypothesis:
`finiteCharacterDiagonalization_of_orthogonality`.  The concrete specialisation
is recorded as OPEN in `QK5CharacterInterfaces.lean` (comments only).

Also banked: the counterguard that a reindexing identity is not a contraction —
it preserves the exact value, hence the exact size, of an arbitrary finite
kernel.

**FIREWALL.**  A finite character identity does not imply the high-conductor
character moment.  A Kloosterman reindexing identity does not imply a
Kloosterman estimate.
-/
import Universal.SafeAlgebra.KloostermanReindex

namespace Gate1B.SafeExtensions

open Finset

/-- **Abstract conditional diagonalization.**  Given a finite family of
"characters" `chi : X → G → ℂ` satisfying the orthogonality relation as an
explicit hypothesis, every function on `G` is recovered from its transform.
No property of Dirichlet characters is used or asserted. -/
theorem finiteCharacterDiagonalization_of_orthogonality
    {G X : Type*} [Fintype G] [DecidableEq G] [Fintype X] [Nonempty X]
    (chi : X → G → ℂ)
    (horth : ∀ g h : G,
      ∑ x, chi x g * (starRingEnd ℂ) (chi x h)
        = if g = h then (Fintype.card X : ℂ) else 0)
    (f : G → ℂ) (g : G) :
    f g = (1 / (Fintype.card X : ℂ))
      * ∑ x, (∑ h, f h * (starRingEnd ℂ) (chi x h)) * chi x g := by
  have hcard : (Fintype.card X : ℂ) ≠ 0 := by
    have : 0 < Fintype.card X := Fintype.card_pos
    exact_mod_cast this.ne'
  have hswap : ∑ x, (∑ h, f h * (starRingEnd ℂ) (chi x h)) * chi x g
      = ∑ h, f h * ∑ x, chi x g * (starRingEnd ℂ) (chi x h) := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [hswap]
  have : ∑ h, f h * ∑ x, chi x g * (starRingEnd ℂ) (chi x h)
      = f g * (Fintype.card X : ℂ) := by
    rw [Finset.sum_congr rfl fun h _ => by rw [horth g h]]
    simp
  rw [this]
  field_simp

/-- **Counterguard B.**  A reindexing identity is not a contraction: the
Kloosterman-like kernel after the unit substitution is *equal* to the kernel
before it, so its norm is unchanged. -/
theorem kLike_reindex_not_contraction {q : ℕ} [NeZero q] (F : ZMod q → ℂ)
    (k c : ZMod q) (u : (ZMod q)ˣ) :
    ‖Universal.SafeAlgebra.kLike F (k * (u : ZMod q)) c‖
      = ‖Universal.SafeAlgebra.kLike F k (c * (u : ZMod q))‖ := by
  rw [Universal.SafeAlgebra.kLike_productSlot_reindex]

end Gate1B.SafeExtensions
