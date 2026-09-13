/-
# Gate1B / R11 / Frontier : exact transfer identity of the old empty-site repair

Abstract finite row data:

* a finite site set split into the **occupied** part `O` and the **empty** part `E`
  (`Disjoint O E`);
* a positive/principal kernel `m : U → ℂ`;
* the **original row** `d0`, supported on `O`;
* the **correction** `a`, supported on `E`.

The old empty-site repair is

    a u = − 1_E(u) · s · conj (m u) / G_E,
    s   = ∑_{v ∈ O} d0 v · m v,
    G_E = ∑_{u ∈ E} |m u|².

Assuming `G_E ≠ 0` the file proves, by the kernel:

* `L_phys a = 0` — the **full physical functional** of the correction vanishes, i.e. the repair is
  a source-preserving algebraic transform (it inserts nothing at occupied sites);
* `L_pr a = − L_pr d0` — the principal functional of the correction is exactly minus that of the
  original row;
* hence `L_np a = L_pr d0` — **the exact research correction**
  `L_nonprincipal(repair) = L_principal(original row)`;
* `L_pr (d0 + a) = 0` while `L_phys (d0 + a) = L_phys d0`.

**Firewall (§5, §8).**  Cancelling the principal component does *not* remove the corresponding
contribution from the complete spectrum: the mass is transferred to the nonprincipal functional,
and explicit finite data are exhibited for which the repaired row has vanishing principal
functional but nonvanishing complete functional.  No universal impossibility theorem is stated.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace Gate1B.R11.Frontier

open Finset

noncomputable section

variable {U : Type*} [DecidableEq U]

/-! ## 1. The data -/

/-- The principal Gram mass of the empty sites, `G_E = ∑_{u ∈ E} |m u|²`. -/
def gramEmpty (E : Finset U) (m : U → ℂ) : ℂ := ∑ u ∈ E, (starRingEnd ℂ) (m u) * m u

omit [DecidableEq U] in
/-- `G_E` is a nonnegative real number. -/
theorem gramEmpty_eq_sq (E : Finset U) (m : U → ℂ) :
    gramEmpty E m = ((∑ u ∈ E, ‖m u‖ ^ 2 : ℝ) : ℂ) := by
  rw [gramEmpty, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  exact Complex.normSq_eq_norm_sq (m u)

/-- The principal source mass `s = ∑_{v ∈ O} d0 v · m v`. -/
def sourceMass (O : Finset U) (m d0 : U → ℂ) : ℂ := ∑ v ∈ O, d0 v * m v

/-- The **old empty-site correction** `a`, supported on `E`. -/
def repairCorrection (O E : Finset U) (m d0 : U → ℂ) (u : U) : ℂ :=
  if u ∈ E then -(sourceMass O m d0 * (starRingEnd ℂ) (m u)) / gramEmpty E m else 0

theorem repairCorrection_of_not_mem {O E : Finset U} {m d0 : U → ℂ} {u : U} (hu : u ∉ E) :
    repairCorrection O E m d0 u = 0 := if_neg hu

/-! ## 2. The three functionals -/

/-- The **full physical functional**: only occupied sites carry physical mass. -/
def Lphys (O : Finset U) (f : U → ℂ) : ℂ := ∑ v ∈ O, f v

/-- The **principal functional** on the whole site set `Ω`. -/
def Lprin (Om : Finset U) (m f : U → ℂ) : ℂ := ∑ u ∈ Om, f u * m u

/-- The **nonprincipal functional**, defined by the decomposition
`L_all = L_principal + L_nonprincipal`. -/
def Lnonprin (Om O : Finset U) (m f : U → ℂ) : ℂ := Lphys O f - Lprin Om m f

omit [DecidableEq U] in
/-- **THE DECOMPOSITION** `L_all = L_principal + L_nonprincipal`, by definition of the
nonprincipal part. -/
theorem L_decomposition (Om O : Finset U) (m f : U → ℂ) :
    Lphys O f = Lprin Om m f + Lnonprin Om O m f := by
  rw [Lnonprin]; ring

/-! ## 3. The transfer identities -/

variable {O E : Finset U} {m d0 : U → ℂ}

/-- The principal functional of the original row is exactly the source mass `s`. -/
theorem Lprin_original (hdisj : Disjoint O E) (hd0 : ∀ u ∉ O, d0 u = 0) :
    Lprin (O ∪ E) m d0 = sourceMass O m d0 := by
  rw [Lprin, Finset.sum_union hdisj]
  have hE : ∑ u ∈ E, d0 u * m u = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    have : u ∉ O := fun h => (Finset.disjoint_left.mp hdisj h) hu
    rw [hd0 u this, zero_mul]
  rw [hE, add_zero, sourceMass]

/-- **SOURCE PRESERVATION.**  The full physical functional of the correction vanishes: the repair
inserts nothing at occupied sites. -/
theorem Lphys_repair_zero (hdisj : Disjoint O E) :
    Lphys O (repairCorrection O E m d0) = 0 := by
  refine Finset.sum_eq_zero fun v hv => ?_
  exact repairCorrection_of_not_mem (fun h => (Finset.disjoint_left.mp hdisj hv) h)

/-- **PRINCIPAL CANCELLATION.**  The principal functional of the correction is minus the source
mass. -/
theorem Lprin_repair (hdisj : Disjoint O E) (hG : gramEmpty E m ≠ 0) :
    Lprin (O ∪ E) m (repairCorrection O E m d0) = -sourceMass O m d0 := by
  rw [Lprin, Finset.sum_union hdisj]
  have hO : ∑ u ∈ O, repairCorrection O E m d0 u * m u = 0 := by
    refine Finset.sum_eq_zero fun u hu => ?_
    rw [repairCorrection_of_not_mem (fun h => (Finset.disjoint_left.mp hdisj hu) h), zero_mul]
  have hterm : ∀ u ∈ E, repairCorrection O E m d0 u * m u
      = (-sourceMass O m d0 / gramEmpty E m) * ((starRingEnd ℂ) (m u) * m u) := by
    intro u hu
    rw [repairCorrection, if_pos hu]
    ring
  have hE : ∑ u ∈ E, repairCorrection O E m d0 u * m u
      = (-sourceMass O m d0 / gramEmpty E m) * gramEmpty E m := by
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    rfl
  rw [hO, hE, zero_add, div_mul_cancel₀ _ hG]

/-- **THE EXACT RESEARCH CORRECTION.**
`L_principal(repair) = − L_principal(original row)`. -/
theorem Lprin_repair_eq_neg_original (hdisj : Disjoint O E) (hd0 : ∀ u ∉ O, d0 u = 0)
    (hG : gramEmpty E m ≠ 0) :
    Lprin (O ∪ E) m (repairCorrection O E m d0) = -Lprin (O ∪ E) m d0 := by
  rw [Lprin_repair hdisj hG, Lprin_original hdisj hd0]

/-- **THE TRANSFER IDENTITY.**
`L_nonprincipal(repair) = L_principal(original row)`. -/
theorem Lnonprin_repair_eq_Lprin_original (hdisj : Disjoint O E) (hd0 : ∀ u ∉ O, d0 u = 0)
    (hG : gramEmpty E m ≠ 0) :
    Lnonprin (O ∪ E) O m (repairCorrection O E m d0) = Lprin (O ∪ E) m d0 := by
  rw [Lnonprin, Lphys_repair_zero hdisj, Lprin_repair_eq_neg_original hdisj hd0 hG]
  ring

/-! ## 4. The repaired row -/

/-- The repaired row `d0 + a`. -/
def repairedRow (O E : Finset U) (m d0 : U → ℂ) (u : U) : ℂ :=
  d0 u + repairCorrection O E m d0 u

/-- The repaired row has vanishing principal functional. -/
theorem Lprin_repairedRow (hdisj : Disjoint O E) (hd0 : ∀ u ∉ O, d0 u = 0)
    (hG : gramEmpty E m ≠ 0) : Lprin (O ∪ E) m (repairedRow O E m d0) = 0 := by
  have hsplit : Lprin (O ∪ E) m (repairedRow O E m d0)
      = Lprin (O ∪ E) m d0 + Lprin (O ∪ E) m (repairCorrection O E m d0) := by
    rw [Lprin, Lprin, Lprin, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun u _ => by rw [repairedRow]; ring
  rw [hsplit, Lprin_repair_eq_neg_original hdisj hd0 hG]
  ring

/-- The repaired row has the **same** physical functional as the original row: the repair is a
source-preserving algebraic transform. -/
theorem Lphys_repairedRow (hdisj : Disjoint O E) :
    Lphys O (repairedRow O E m d0) = Lphys O d0 := by
  rw [Lphys, Lphys]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [repairedRow, repairCorrection_of_not_mem (fun h => (Finset.disjoint_left.mp hdisj hv) h),
    add_zero]

/-- **PRINCIPAL-TRANSFER STATEMENT.**  After the repair, the whole physical mass sits in the
nonprincipal functional: `L_nonprincipal(repaired) = L_phys(original)`. -/
theorem Lnonprin_repairedRow (hdisj : Disjoint O E) (hd0 : ∀ u ∉ O, d0 u = 0)
    (hG : gramEmpty E m ≠ 0) :
    Lnonprin (O ∪ E) O m (repairedRow O E m d0) = Lphys O d0 := by
  rw [Lnonprin, Lprin_repairedRow hdisj hd0 hG, Lphys_repairedRow hdisj, sub_zero]

/-! ## 5. Firewall: principal cancellation is not removal from the complete spectrum -/

/-- The two-site model: `U = Fin 2`, `O = {0}`, `E = {1}`, `m ≡ 1`, `d0 = δ₀`. -/
def testKernel : Fin 2 → ℂ := fun _ => 1

/-- The original row of the two-site model. -/
def testRow : Fin 2 → ℂ := fun u => if u = 0 then 1 else 0

theorem testGram : gramEmpty ({1} : Finset (Fin 2)) testKernel = 1 := by
  simp [gramEmpty, testKernel]

theorem testRow_support : ∀ u ∉ ({0} : Finset (Fin 2)), testRow u = 0 := by
  intro u hu
  fin_cases u <;> simp_all [testRow]

theorem testSource : sourceMass ({0} : Finset (Fin 2)) testKernel testRow = 1 := by
  simp [sourceMass, testKernel, testRow]

/-- **FIREWALL.**  For explicit finite data the repaired row has *zero* principal functional while
its complete physical functional is unchanged and nonzero: the principal contribution has been
transferred, not removed. -/
theorem principal_cancellation_is_not_removal :
    ∃ (O E : Finset (Fin 2)) (m d0 : Fin 2 → ℂ),
      Disjoint O E ∧ gramEmpty E m ≠ 0 ∧
      Lprin (O ∪ E) m (repairedRow O E m d0) = 0 ∧
      Lphys O (repairedRow O E m d0) ≠ 0 ∧
      Lnonprin (O ∪ E) O m (repairedRow O E m d0) ≠ 0 := by
  refine ⟨{0}, {1}, testKernel, testRow, by decide, ?_, ?_, ?_, ?_⟩
  · rw [testGram]; exact one_ne_zero
  · exact Lprin_repairedRow (by decide) testRow_support (by rw [testGram]; exact one_ne_zero)
  · rw [Lphys_repairedRow (by decide)]
    simp [Lphys, testRow]
  · rw [Lnonprin_repairedRow (by decide) testRow_support
      (by rw [testGram]; exact one_ne_zero)]
    simp [Lphys, testRow]

/-- **GENERAL FORM OF THE FIREWALL.**  Whenever the original row carries physical mass, the
repaired row still carries exactly that mass in its nonprincipal functional; annihilating the
principal component therefore cannot be read as a removal of the contribution. -/
theorem repair_transfers_rather_than_removes (hdisj : Disjoint O E) (hd0 : ∀ u ∉ O, d0 u = 0)
    (hG : gramEmpty E m ≠ 0) (hmass : Lphys O d0 ≠ 0) :
    Lprin (O ∪ E) m (repairedRow O E m d0) = 0 ∧
      Lnonprin (O ∪ E) O m (repairedRow O E m d0) ≠ 0 :=
  ⟨Lprin_repairedRow hdisj hd0 hG, by
    rw [Lnonprin_repairedRow hdisj hd0 hG]; exact hmass⟩

end

end Gate1B.R11.Frontier
