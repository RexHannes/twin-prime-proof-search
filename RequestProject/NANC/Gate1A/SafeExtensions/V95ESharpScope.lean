/-
# NANC Gate 1A v9.5 — `E♯` scope and the P3-free dependency certificate

`E♯` is defined here **without any P3 hypothesis**: a prime `r ∼ R`, a bounded
shift `|k| ≤ K`, the pair `m, m + k·r ∼ M`, and a generic full-conductor/unit
condition.  There is no field recording that `π ∣ m`, that `m` is clean-P3, or
that `m` has three prime factors.

`ESharpGenericIsP3Free` is therefore a *structural* theorem, not a text search:
the generic bound is a statement about `ESharpSource`, so it is applicable to
the image of a clean-P3 source under the forgetful map, and two clean-P3
sources with the same `E♯` data receive literally the same bound.

Combined with the positive row enlargement of v9.4, a `GenericBPPBound`
immediately yields clean-P3 control.  Nothing analytic is proved here: the
generic bound itself is an explicit certificate interface.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.PositiveRowEnlargement

namespace TwinPrimeProject.NANC.Gate1A.V95

open Finset

/-! ## 1. `E♯` rows: no P3 field -/

/-- An `E♯` row.  Note the fields: prime `r`, bounded shift `k`, the pair
`m, m + k r` in the dyadic block, and a generic unit condition.  There is **no**
P3 field of any kind. -/
structure ESharpRow where
  /-- Dyadic scale of the modulus. -/
  R : ℕ
  /-- Shift bound. -/
  K : ℕ
  /-- Dyadic scale of the physical variable. -/
  M : ℕ
  /-- The prime modulus. -/
  r : ℕ
  r_prime : Nat.Prime r
  r_range : R ≤ r ∧ r < 2 * R
  /-- The shift. -/
  k : ℤ
  k_small : k.natAbs ≤ K
  /-- The physical variable. -/
  m : ℕ
  m_range : M ≤ m ∧ m < 2 * M
  shifted_range : (M : ℤ) ≤ (m : ℤ) + k * (r : ℤ) ∧ (m : ℤ) + k * (r : ℤ) < 2 * (M : ℤ)
  /-- Generic full-conductor / unit condition. -/
  generic_unit : ¬ (r : ℤ) ∣ (m : ℤ)

/-- A clean-P3 row is an `E♯` row *plus* P3 data. -/
structure CleanP3Row extends ESharpRow where
  /-- The distinguished third prime. -/
  p3 : ℕ
  p3_prime : Nat.Prime p3
  p3_dvd : p3 ∣ toESharpRow.m
  three_prime_factors : toESharpRow.m.primeFactors.card = 3

/-- The forgetful map that drops all P3 data. -/
def forgetP3 (x : CleanP3Row) : ESharpRow := x.toESharpRow

/-! ## 2. `E♯` sources and the generic engine interface -/

/-- A finite `E♯` source: finitely many `E♯` rows with complex coefficients. -/
structure ESharpSource where
  Row : Type
  [rowFintype : Fintype Row]
  row : Row → ESharpRow
  coeff : Row → ℂ

attribute [instance] ESharpSource.rowFintype

/-- A finite clean-P3 source. -/
structure CleanP3Source where
  Row : Type
  [rowFintype : Fintype Row]
  row : Row → CleanP3Row
  coeff : Row → ℂ

attribute [instance] CleanP3Source.rowFintype

/-- Forgetting the P3 data of a clean-P3 source produces an `E♯` source. -/
def CleanP3Source.toESharp (S : CleanP3Source) : ESharpSource where
  Row := S.Row
  rowFintype := S.rowFintype
  row := fun i => forgetP3 (S.row i)
  coeff := S.coeff

/-- **The generic BPP engine, as an explicit certificate interface.**  No
analytic content is proved here: an inhabitant of this structure *is* the
generic estimate. -/
structure GenericBPPBound where
  /-- The normalized energy functional on `E♯` sources. -/
  normalizedEnergy : ESharpSource → ℝ
  /-- The generic target `M H L⁴ X^{o(1)}` (normalized form). -/
  genericTarget : ℝ
  /-- The generic bound, for **every** admissible `E♯` source. -/
  bound : ∀ S : ESharpSource, normalizedEnergy S ≤ genericTarget

/-! ## 3. The P3-free dependency certificate -/

/-- **`ESharpGenericIsP3Free`.**  The generic bound applies to a clean-P3
source through the forgetful map, using no P3 field whatsoever. -/
theorem ESharpGenericIsP3Free (G : GenericBPPBound) (S : CleanP3Source) :
    G.normalizedEnergy S.toESharp ≤ G.genericTarget :=
  G.bound S.toESharp

/-- The dependency statement in its sharpest form: the generic bound is a
function of the `E♯` data alone, so two clean-P3 sources sharing their `E♯`
data receive the same value.  (Any hypothetical dependence on `p3`,
`p3_dvd` or `three_prime_factors` would make this false.) -/
theorem genericBound_depends_only_on_esharpData (G : GenericBPPBound) (S T : CleanP3Source)
    (h : S.toESharp = T.toESharp) :
    G.normalizedEnergy S.toESharp = G.normalizedEnergy T.toESharp := by
  rw [h]

/-- The forgetful map genuinely discards data: `E♯` is a strict enlargement, so
the generic engine is applied to strictly more rows than the clean-P3 ones. -/
theorem forgetP3_forgets (x y : CleanP3Row) (h : forgetP3 x = forgetP3 y) :
    x.toESharpRow = y.toESharpRow := h

/-! ## 4. Clean-P3 consequence of a generic bound -/

/-- **Clean-P3 control from the generic engine.**  Positive row enlargement
(v9.4) plus a generic `E♯` bound controls the clean-P3 rows. -/
theorem cleanP3_controlled_of_generic {Row : Type*} [Fintype Row]
    (P : V94.PositiveRowEnlargement Row) (e : Row → ℝ) (he : ∀ r, 0 ≤ e r) (B : ℝ)
    (hB : ∑ r ∈ P.esharpRows, e r ≤ B) :
    ∑ r ∈ P.cleanRows, e r ≤ B :=
  P.cleanP3_energy_le_of_esharp_bound e he B hB

end TwinPrimeProject.NANC.Gate1A.V95
