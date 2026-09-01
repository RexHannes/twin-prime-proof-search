import Mathlib

/-!
# Gate 1B · FM722 · **symbolic slope / line-length ledger and capacity firewall**

Deterministic exponent arithmetic over `ℚ`.  Nothing here is asymptotic: the
symbol `~` is **not** encoded as a theorem anywhere in this module, and no
inequality proved here is an analytic statement about an actual sum.

Given exponents `qExp`, `pExp`, `zExp`, `yExp`:

```
  oneAtomLineExp   = qExp − pExp − zExp
  twoAtomLineExp   = qExp − pExp − zExp − yExp
  oneAtomSlopeExp  = pExp + zExp
  twoAtomSlopeExp  = pExp + zExp + yExp
```

§3 is the **capacity firewall**: a hard second opening does *not* inherit a
slope threshold, and it can shorten the line below any prescribed level.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

/-- Symbolic exponents of the long-line ledger.  Finite rational data. -/
structure LongLineExponents where
  /-- Exponent of the modulus range. -/
  qExp : ℚ
  /-- Exponent of the prime index. -/
  pExp : ℚ
  /-- Exponent of the first opened atom. -/
  zExp : ℚ
  /-- Exponent of the second opened atom. -/
  yExp : ℚ
  deriving DecidableEq

namespace LongLineExponents

variable (E : LongLineExponents)

/-- Symbolic length exponent of the one-atom line. -/
def oneAtomLineExp : ℚ := E.qExp - E.pExp - E.zExp

/-- Symbolic length exponent of the two-atom (hard-opened) line. -/
def twoAtomLineExp : ℚ := E.qExp - E.pExp - E.zExp - E.yExp

/-- Symbolic slope exponent of the one-atom line. -/
def oneAtomSlopeExp : ℚ := E.pExp + E.zExp

/-- Symbolic slope exponent of the two-atom (hard-opened) line. -/
def twoAtomSlopeExp : ℚ := E.pExp + E.zExp + E.yExp

/-! ## 1. The obvious identities -/

theorem twoAtomLineExp_eq : E.twoAtomLineExp = E.oneAtomLineExp - E.yExp := by
  simp [twoAtomLineExp, oneAtomLineExp]

theorem twoAtomSlopeExp_eq : E.twoAtomSlopeExp = E.oneAtomSlopeExp + E.yExp := by
  simp [twoAtomSlopeExp, oneAtomSlopeExp]

theorem oneAtom_line_add_slope : E.oneAtomLineExp + E.oneAtomSlopeExp = E.qExp := by
  simp [oneAtomLineExp, oneAtomSlopeExp]

theorem twoAtom_line_add_slope : E.twoAtomLineExp + E.twoAtomSlopeExp = E.qExp := by
  simp [twoAtomLineExp, twoAtomSlopeExp]

/-- A hard opening moves exactly the amount `yExp` from the line length to the
slope. -/
theorem hard_opening_transfer :
    E.oneAtomLineExp - E.twoAtomLineExp = E.twoAtomSlopeExp - E.oneAtomSlopeExp := by
  simp [oneAtomLineExp, twoAtomLineExp, oneAtomSlopeExp, twoAtomSlopeExp]

end LongLineExponents

/-! ## 2. Monotonicity in the trivial direction (kept explicit) -/

open LongLineExponents

/-- With a nonnegative second atom exponent the two-atom line is **not longer**
than the one-atom line. -/
theorem twoAtomLine_le_oneAtomLine (E : LongLineExponents) (hy : 0 ≤ E.yExp) :
    E.twoAtomLineExp ≤ E.oneAtomLineExp := by
  rw [E.twoAtomLineExp_eq]; linarith

/-- With a nonnegative second atom exponent the two-atom slope is **not
smaller** than the one-atom slope. -/
theorem oneAtomSlope_le_twoAtomSlope (E : LongLineExponents) (hy : 0 ≤ E.yExp) :
    E.oneAtomSlopeExp ≤ E.twoAtomSlopeExp := by
  rw [E.twoAtomSlopeExp_eq]; linarith

/-! ## 3. The capacity firewall -/

/-- **CAPACITY FIREWALL (slope threshold).**  From `oneAtomSlopeExp < 1/3` it
does **not** follow that `twoAtomSlopeExp < 1/3`: an explicit rational
countermodel. -/
theorem slope_threshold_not_inherited :
    ∃ E : LongLineExponents, E.oneAtomSlopeExp < 1 / 3 ∧ ¬ (E.twoAtomSlopeExp < 1 / 3) := by
  refine ⟨⟨1, 1 / 10, 1 / 10, 1 / 2⟩, ?_, ?_⟩ <;>
    simp [LongLineExponents.oneAtomSlopeExp, LongLineExponents.twoAtomSlopeExp] <;> norm_num

/-- The universally quantified inheritance statement is **false**. -/
theorem no_slope_threshold_inheritance :
    ¬ ∀ E : LongLineExponents, E.oneAtomSlopeExp < 1 / 3 → E.twoAtomSlopeExp < 1 / 3 := by
  obtain ⟨E, h1, h2⟩ := slope_threshold_not_inherited
  exact fun h => h2 (h E h1)

/-- **CAPACITY FIREWALL (line length).**  For every prescribed threshold `t`
there is a *long* one-atom line (length exponent `≥ 1`) whose hard second
opening has length exponent below `t`. -/
theorem hard_opening_can_shorten_below (t : ℚ) :
    ∃ E : LongLineExponents,
      1 ≤ E.oneAtomLineExp ∧ 0 < E.yExp ∧ E.twoAtomLineExp < t := by
  have h1 : (0:ℚ) ≤ |t| := abs_nonneg t
  have h2 : -|t| ≤ t := neg_abs_le t
  refine ⟨⟨2 + |t|, 1 / 2, 1 / 2, 2 + 2 * |t|⟩, ?_, ?_, ?_⟩
  · show (1:ℚ) ≤ 2 + |t| - 1 / 2 - 1 / 2
    linarith
  · show (0:ℚ) < 2 + 2 * |t|
    linarith
  · show 2 + |t| - 1 / 2 - 1 / 2 - (2 + 2 * |t|) < t
    linarith

/-- **Semantic guard.**  Determinant preservation under a hard opening carries
no length information: the two statements are logically independent in the
ledger, since the ledger has models with arbitrarily large and arbitrarily
small `twoAtomLineExp` for a fixed `oneAtomLineExp`. -/
theorem line_length_not_determined_by_one_atom_data :
    ∃ E F : LongLineExponents,
      E.oneAtomLineExp = F.oneAtomLineExp ∧ E.twoAtomLineExp ≠ F.twoAtomLineExp := by
  refine ⟨⟨1, 0, 0, 0⟩, ⟨1, 0, 0, 1⟩, by simp [LongLineExponents.oneAtomLineExp], ?_⟩
  simp [LongLineExponents.twoAtomLineExp]

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
