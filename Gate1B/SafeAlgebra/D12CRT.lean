/-
# Gate 1B v8.2 — the D₁₂ CRT slot

Finite CRT bookkeeping for a coprime pair of moduli `(m, n)`: the joint residue
`d12Value` realising a prescribed pair of residues, its two projection
specifications, and existence/uniqueness.

Everything is an instance of `ZMod.chineseRemainder`; no analytic content.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

/-- The D₁₂ joint residue attached to a prescribed pair of residues. -/
noncomputable def d12Value {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod m) (b : ZMod n) :
    ZMod (m * n) :=
  (ZMod.chineseRemainder h).symm (a, b)

/-- The first projection of the D₁₂ residue is the first prescribed residue. -/
theorem d12_spec_left {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod m) (b : ZMod n) :
    (ZMod.castHom (Dvd.intro n rfl) (ZMod m)) (d12Value h a b) = a := by
  have := (ZMod.chineseRemainder h).apply_symm_apply (a, b)
  simpa [ZMod.chineseRemainder, d12Value] using congrArg Prod.fst this

/-- The second projection of the D₁₂ residue is the second prescribed residue. -/
theorem d12_spec_right {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod m) (b : ZMod n) :
    (ZMod.castHom (Dvd.intro_left m rfl) (ZMod n)) (d12Value h a b) = b := by
  have := (ZMod.chineseRemainder h).apply_symm_apply (a, b)
  simpa [ZMod.chineseRemainder, d12Value] using congrArg Prod.snd this

/-- **Existence and uniqueness of the D₁₂ slot.**  For coprime moduli the joint
residue is the unique element with the prescribed projections. -/
theorem d12_exists_unique {m n : ℕ} (h : Nat.Coprime m n) (a : ZMod m) (b : ZMod n) :
    ∃! x : ZMod (m * n),
      (ZMod.castHom (Dvd.intro n rfl) (ZMod m)) x = a ∧
        (ZMod.castHom (Dvd.intro_left m rfl) (ZMod n)) x = b := by
  refine ⟨d12Value h a b, ⟨d12_spec_left h a b, d12_spec_right h a b⟩, ?_⟩
  rintro y ⟨hy1, hy2⟩
  have hy : (ZMod.chineseRemainder h) y = (a, b) := by
    apply Prod.ext <;> simpa [ZMod.chineseRemainder] using (by assumption : _)
  have : y = (ZMod.chineseRemainder h).symm (a, b) := by
    rw [← hy, (ZMod.chineseRemainder h).symm_apply_apply]
  simpa [d12Value] using this

end Gate1B.SafeAlgebra
