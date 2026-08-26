/-
# NANC Gate 1A v9.8 — the canonical all-`m` Direct row family

Section 7 of the v9.8 instructions asks for the canonical Gate 1A Direct row
family, defined by

* `r ∼ R` prime,
* `|k| ≤ K`,
* `m ∼ M` and `m + k r ∼ M`,
* the generic unit / full-conductor condition,

and by **nothing else** — in particular with no `m = π₁π₂π₃`, no `π ∣ m` and no
clean-P3 factorisation.

The repository already has exactly this type: `V95.ESharpRow`
(`RequestProject/NANC/Gate1A/SafeExtensions/V95ESharpScope.lean`), whose field
list is literally the list above.  It is therefore *reused*, not restated:

    Gate1ADirectAllMRow := V95.ESharpRow.

What is added here is the scope evidence:

* `allMRow_witness` — the family is inhabited;
* `exists_allMRow_not_cleanP3` — the all-`m` family is *strictly* larger than
  the clean-P3 family, so the canonical theorem really is an all-`m` theorem;
* `cleanP3_embeds_allM` — every clean-P3 row is an all-`m` row (the v9.5
  forgetful map), and
* `cleanP3_energy_le_allM_energy` — the positive-energy corollary, which is the
  Section 17 clean-P3 corollary in its finite form.
-/
import Mathlib
import RequestProject.NANC.Gate1A.SafeExtensions.V95ESharpScope
import RequestProject.NANC.Gate1A.SafeExtensions.PositiveRowEnlargement

namespace TwinPrimeProject.NANC.Gate1A.V98

open Finset
open TwinPrimeProject.NANC.Gate1A.V95

/-- **The canonical Gate 1A Direct all-`m` row family.**  Reuse of the existing
`E♯` row type, whose fields are exactly `r ∼ R` prime, `|k| ≤ K`, `m ∼ M`,
`m + k r ∼ M` and the generic unit condition. -/
abbrev Gate1ADirectAllMRow := ESharpRow

/-- An explicit canonical row: `R = 2`, `K = 0`, `M = 3`, `r = 2`, `k = 0`,
`m = 3`.  Its `m` has a single prime factor, so it is *not* a clean-P3 row. -/
def allMRowWitness : Gate1ADirectAllMRow where
  R := 2
  K := 0
  M := 3
  r := 2
  r_prime := Nat.prime_two
  r_range := by norm_num
  k := 0
  k_small := by norm_num
  m := 3
  m_range := by norm_num
  shifted_range := by norm_num
  generic_unit := by decide

/-- The canonical all-`m` family is inhabited. -/
theorem allMRow_witness : Nonempty Gate1ADirectAllMRow := ⟨allMRowWitness⟩

/-- **The all-`m` family is strictly larger than the clean-P3 family.**  The
witness row has `m = 3`, which has one prime factor, so no clean-P3 row maps
onto it. -/
theorem exists_allMRow_not_cleanP3 :
    ∃ x : Gate1ADirectAllMRow, ∀ y : CleanP3Row, forgetP3 y ≠ x := by
  refine ⟨allMRowWitness, fun y hy => ?_⟩
  have hm : y.toESharpRow.m = 3 := by
    have := congrArg ESharpRow.m hy
    simpa [allMRowWitness] using this
  have h3 := y.three_prime_factors
  rw [hm] at h3
  rw [Nat.Prime.primeFactors (by norm_num : Nat.Prime 3)] at h3
  simp at h3

/-- **Clean-P3 rows embed into the canonical all-`m` family** (the v9.5
forgetful map, re-exported at the v9.8 name). -/
def cleanP3_embeds_allM (y : CleanP3Row) : Gate1ADirectAllMRow := forgetP3 y

/-- Two clean-P3 rows with the same canonical all-`m` row have the same
underlying `E♯` data. -/
theorem cleanP3_embeds_allM_faithful (x y : CleanP3Row) (h : forgetP3 x = forgetP3 y) :
    x.toESharpRow = y.toESharpRow := forgetP3_forgets x y h

/-- **Section 17, finite form.**  For a non-negative row energy, the clean-P3
energy never exceeds the canonical all-`m` Direct energy: the clean-P3 bound is
a corollary of the all-`m` bound and needs no separate analytic theorem. -/
theorem cleanP3_energy_le_allM_energy {Row : Type*} [Fintype Row] [DecidableEq Row]
    (P : V94.PositiveRowEnlargement Row) (e : Row → ℝ) (he : ∀ r, 0 ≤ e r) :
    ∑ r ∈ P.cleanRows, e r ≤ ∑ r ∈ P.esharpRows, e r :=
  P.cleanP3_energy_le_esharp_energy e he

/-- The same statement in the form used by the closure compiler: any bound for
the all-`m` family is inherited by the clean-P3 family. -/
theorem cleanP3_of_allM_bound {Row : Type*} [Fintype Row] [DecidableEq Row]
    (P : V94.PositiveRowEnlargement Row) (e : Row → ℝ) (he : ∀ r, 0 ≤ e r) (B : ℝ)
    (hB : ∑ r ∈ P.esharpRows, e r ≤ B) :
    ∑ r ∈ P.cleanRows, e r ≤ B :=
  P.cleanP3_energy_le_of_esharp_bound e he B hB

end TwinPrimeProject.NANC.Gate1A.V98
