/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
closing the row identification  (B13)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted; in particular
`epM2Realisation`, `epM2RowIdentification`, `EPM2Bound` and the canonical owner
`J2ResidualCenteredBound` keep their original statements, and no analytic proposition is
inhabited here.

`Realisation.lean` reduced the exact bridge `epM2Realisation` to a single sub-bridge,
`epM2RowIdentification` (centered canonical kernel = EP-M2 row value), and proved that this
sub-bridge is load-bearing: it is **false for general realisation data** (`toyData`).  So the
only honest way to close it is to *realise* it — to exhibit explicit canonical data whose row
identification is a theorem.  That is what this module does.

The realisation is built from the objects already banked in this route:

* the canonical row kernel is the **divisor form** of the EP-M2 row,
  `K(⟨e,s⟩) = ∑_{z ∈ Z, e ∣ sz+2} β₅(z) · F((sz+2)/e)` with `F(N) = ∑_{d ∣ N} λ(d)`
  (`divRow`), read off the packet index through the chart `⟨e,s⟩ = Nat.pair e s`;
* the EP-M2 row value is the **Ramanujan form** of the same row,
  `R(e,s) = ∑_{z ∈ Z, e ∣ sz+2} β₅(z) · ∑_{0<q≤Q_max} a(q) c_q((sz+2)/e)`, centered
  (`ramRow`).

These are two genuinely different finite expressions, and the identification between them is
exactly the banked finite Ramanujan expansion `Fsum_eq_ramanujan_expansion`.  §1 proves the
row coefficient identity, §2 the chart bookkeeping identities, §3 assembles the realisation data
and proves **all seven** sub-bridges, hence `epM2RowIdentification` and `epM2Realisation`, for
this instance; §4 records the exact value of both families and a nondegeneracy criterion
(the instance is not the zero object); §5 attaches the EP-M2 programme to the canonical `j = 2`
owner — conditionally on `EPM2Bound`, which is **not** inhabited.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.Realisation

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Finset
open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. The row coefficient identification: divisor form = Ramanujan form -/

/-- The **divisor form** of the EP-M2 row: `∑_{z ∈ Z, e ∣ sz+2} β₅(z) F((sz+2)/e)` with
`F(N) = ∑_{d ∣ N} λ(d)` the truncated Möbius divisor sum. -/
noncomputable def divRow (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ) (e s : ℕ) : ℝ :=
  rowOp Z beta5 (fun N => ((Fsum I N : ℚ) : ℝ)) e s

/-- The **Ramanujan form** of the same row: the arithmetic input is replaced by its finite
Ramanujan expansion `∑_{0<q≤Q_max} a(q) c_q(N)`, with the sharp cutoff `Q_max = B₁B₂`. -/
noncomputable def ramRow (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ) (e s : ℕ) : ℝ :=
  rowOp Z beta5
    (fun N => ((∑ q ∈ Finset.Ioc 0 I.Qmax, aCoeff I q * ((ram q N : ℤ) : ℚ) : ℚ) : ℝ)) e s

/-- **`rowCoefficientIdentification`** — the divisor form and the Ramanujan form of the EP-M2
row are *equal*, exactly.  This is the arithmetic content of the row bridge: it is the banked
finite Ramanujan expansion, applied at every point `(sz+2)/e` of the row, all of which are
positive by `rowOp_arg_pos`. -/
theorem rowCoefficientIdentification (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ) (e s : ℕ) :
    divRow I Z beta5 e s = ramRow I Z beta5 e s := by
  unfold divRow ramRow rowOp
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : e ∣ s * z + 2
  · rw [if_pos h, if_pos h]
    simp only
    rw [Fsum_eq_ramanujan_expansion I (rowOp_arg_pos h)]
  · rw [if_neg h, if_neg h]

/-! ## 2. The chart and the canonical row kernel -/

/-- The EP-M2 chart: the index pair `(e, s)` is carried to the canonical packet index
`Nat.pair e s`. -/
def pairIdx (p : ℕ × ℕ) : ℕ := Nat.pair p.1 p.2

/-- **`rowIndexIdentification`** — the chart is injective, so the EP-M2 indexing does not
double-count canonical packet points. -/
theorem pairIdx_injective : Function.Injective pairIdx := by
  intro p q h
  have h' : (p.1, p.2) = (q.1, q.2) := by
    have := congrArg Nat.unpair h
    simpa [pairIdx, Nat.unpair_pair] using this
  exact Prod.ext (congrArg Prod.fst h') (congrArg Prod.snd h')

/-- The canonical row kernel, defined intrinsically on packet indices: the divisor-form row at
the pair decoded from the index. -/
noncomputable def canonicalRowKernel (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ) (n : ℕ) : ℝ :=
  divRow I Z beta5 (Nat.unpair n).1 (Nat.unpair n).2

/-- **`rowKernelIdentification`** — at a chart point the canonical row kernel is the divisor-form
row value of that index pair. -/
theorem canonicalRowKernel_pairIdx (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ) (p : ℕ × ℕ) :
    canonicalRowKernel I Z beta5 (pairIdx p) = divRow I Z beta5 p.1 p.2 := by
  simp [canonicalRowKernel, pairIdx, Nat.unpair_pair]

/-- The chart-point form of the coefficient identification: kernel value = Ramanujan row
value. -/
theorem canonicalRowKernel_eq_ramRow (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ) (p : ℕ × ℕ) :
    canonicalRowKernel I Z beta5 (pairIdx p) = ramRow I Z beta5 p.1 p.2 := by
  rw [canonicalRowKernel_pairIdx, rowCoefficientIdentification]

/-! ## 3. The realisation instance and its seven sub-bridges -/

/-- The **row realisation data**: canonical packet = chart image, canonical kernel = divisor-form
row, canonical source = outer weight times the centered kernel, EP-M2 row value = centered
Ramanujan-form row, normalisation = `hbCoeff 5 2 = −10`.  The centering constant `c` is a
parameter; it is matched to the packet kernel mean in §3.2. -/
noncomputable def rowData (I : Cutoffs) (Z : Finset ℕ) (beta5 W : ℕ → ℝ) (E S : ℝ → Finset ℕ)
    (c : ℝ) : RealisationData where
  pkt := fun x => ((E x) ×ˢ (S x)).image pairIdx
  g := fun n => W (Nat.unpair n).2 * (canonicalRowKernel I Z beta5 n - c)
  K := canonicalRowKernel I Z beta5
  mask := fun _ => true
  idx := pairIdx
  E := E
  S := S
  W := W
  R := fun _ e s => ramRow I Z beta5 e s - c
  nrm := (hbCoeff 5 2 : ℝ)

variable (I : Cutoffs) (Z : Finset ℕ) (beta5 W : ℕ → ℝ) (E S : ℝ → Finset ℕ) (c : ℝ)

theorem rowData_chart (x : ℝ) : (rowData I Z beta5 W E S c).chart x = (E x) ×ˢ (S x) := rfl

theorem rowData_indexSet : indexSetRealisation (rowData I Z beta5 W E S c) :=
  fun _ => Finset.Subset.refl _

theorem rowData_chartInjectivity : chartInjectivity (rowData I Z beta5 W E S c) := by
  intro _ p _ q _ h
  exact pairIdx_injective h

theorem rowData_mask : maskRealisation (rowData I Z beta5 W E S c) := by
  intro x n hn
  simp only [rowData, true_iff]
  exact hn

theorem rowData_sourceSupport : sourceSupportRealisation (rowData I Z beta5 W E S c) := by
  intro n hn
  exact absurd hn (by simp [rowData])

/-- **`rowSourceIdentification`** — at a chart point the canonical source coefficient is the
EP-M2 outer weight times the EP-M2 row value.  Proved, not assumed: it is the row coefficient
identification again. -/
theorem rowData_sourceWeight : sourceWeightRealisation (rowData I Z beta5 W E S c) := by
  intro x p _
  show W (Nat.unpair (pairIdx p)).2 * (canonicalRowKernel I Z beta5 (pairIdx p) - c)
      = W p.2 * (ramRow I Z beta5 p.1 p.2 - c)
  rw [canonicalRowKernel_eq_ramRow]
  simp [pairIdx, Nat.unpair_pair]

theorem rowData_normalisation : normalisationRealisation (rowData I Z beta5 W E S c) := rfl

/-- **`rowCenteringIdentification` ⇒ `epM2RowIdentification`.**  Once the centering constant is
the packet kernel mean, the remaining exact identification is discharged by the coefficient
identity of §1. -/
theorem rowData_rowIdentification
    (hmean : ∀ x, kernelMean ((rowData I Z beta5 W E S c).pkt x)
      (rowData I Z beta5 W E S c).K = c) :
    epM2RowIdentification (rowData I Z beta5 W E S c) := by
  intro x p _
  show canonicalRowKernel I Z beta5 (pairIdx p)
      - kernelMean ((rowData I Z beta5 W E S c).pkt x) (rowData I Z beta5 W E S c).K
      = ramRow I Z beta5 p.1 p.2 - c
  rw [hmean x, canonicalRowKernel_eq_ramRow]

/-- **`epM2Realisation` for the row realisation instance** — every sub-bridge is kernel-proved,
so the exact identification of the canonical centered `j = 2` residual family with the EP-M2 row
moment family holds for this data. -/
theorem rowData_epM2Realisation
    (hmean : ∀ x, kernelMean ((rowData I Z beta5 W E S c).pkt x)
      (rowData I Z beta5 W E S c).K = c) :
    epM2Realisation (rowData I Z beta5 W E S c).canonicalFamily
      (rowData I Z beta5 W E S c).epM2Family :=
  epM2Realisation_of_subBridges (rowData_indexSet I Z beta5 W E S c)
    (rowData_chartInjectivity I Z beta5 W E S c) (rowData_mask I Z beta5 W E S c)
    (rowData_sourceSupport I Z beta5 W E S c) (rowData_sourceWeight I Z beta5 W E S c)
    (rowData_normalisation I Z beta5 W E S c)
    (rowData_rowIdentification I Z beta5 W E S c hmean)

/-! ### 3.2  The canonical centering: the mean hypothesis is discharged -/

/-- The canonical centering constant of a fixed chart: the kernel mean over the packet. -/
noncomputable def rowCentering (I : Cutoffs) (Z : Finset ℕ) (beta5 : ℕ → ℝ)
    (E0 S0 : Finset ℕ) : ℝ :=
  kernelMean ((E0 ×ˢ S0).image pairIdx) (canonicalRowKernel I Z beta5)

/-- The **closed row realisation instance**: a fixed chart box `E0 × S0`, centered at its own
kernel mean.  No hypothesis is left over. -/
noncomputable def rowDataClosed (I : Cutoffs) (Z : Finset ℕ) (beta5 W : ℕ → ℝ)
    (E0 S0 : Finset ℕ) : RealisationData :=
  rowData I Z beta5 W (fun _ => E0) (fun _ => S0) (rowCentering I Z beta5 E0 S0)

theorem rowDataClosed_mean (E0 S0 : Finset ℕ) :
    ∀ x, kernelMean ((rowDataClosed I Z beta5 W E0 S0).pkt x)
      (rowDataClosed I Z beta5 W E0 S0).K = rowCentering I Z beta5 E0 S0 :=
  fun _ => rfl

/-- **GOLD A — `epM2RowIdentification` is proved** for the closed row realisation instance.
(The sub-bridge is false for general realisation data — see `epM2RowIdentification_load_bearing`
— so this realisation, not a universally quantified statement, is the exact content that was
missing.) -/
theorem epM2RowIdentification_rowDataClosed (E0 S0 : Finset ℕ) :
    epM2RowIdentification (rowDataClosed I Z beta5 W E0 S0) :=
  rowData_rowIdentification I Z beta5 W _ _ _ (rowDataClosed_mean I Z beta5 W E0 S0)

/-- **GOLD B — `epM2Realisation` is proved** for the closed row realisation instance: the
canonical centered `j = 2` residual family *is* the EP-M2 row moment family, exactly. -/
theorem epM2Realisation_rowDataClosed (E0 S0 : Finset ℕ) :
    epM2Realisation (rowDataClosed I Z beta5 W E0 S0).canonicalFamily
      (rowDataClosed I Z beta5 W E0 S0).epM2Family :=
  rowData_epM2Realisation I Z beta5 W _ _ _ (rowDataClosed_mean I Z beta5 W E0 S0)

/-! ## 4. The exact value of the realised families, and nondegeneracy -/

/-- Both families are the weighted square sum of the centered Ramanujan row, times `−10`. -/
theorem rowDataClosed_epM2Family_eq (E0 S0 : Finset ℕ) (x : ℝ) :
    (rowDataClosed I Z beta5 W E0 S0).epM2Family x
      = (hbCoeff 5 2 : ℝ)
        * ∑ p ∈ E0 ×ˢ S0, W p.2 * (ramRow I Z beta5 p.1 p.2 - rowCentering I Z beta5 E0 S0) ^ 2 :=
  rfl

/-- **Nondegeneracy criterion.**  If the outer weight is nonnegative on the chart and some chart
point carries a positive weight and a nonzero centered row value, then the realised family is
nonzero: the identification of §3 is not an identification of the zero object. -/
theorem rowDataClosed_ne_zero (E0 S0 : Finset ℕ) (x : ℝ)
    (hW : ∀ p ∈ E0 ×ˢ S0, 0 ≤ W p.2) {p0 : ℕ × ℕ} (hp0 : p0 ∈ E0 ×ˢ S0) (hW0 : 0 < W p0.2)
    (hR0 : ramRow I Z beta5 p0.1 p0.2 - rowCentering I Z beta5 E0 S0 ≠ 0) :
    (rowDataClosed I Z beta5 W E0 S0).epM2Family x ≠ 0 := by
  rw [rowDataClosed_epM2Family_eq, hbCoeff_five_two]
  have hpos : 0 < ∑ p ∈ E0 ×ˢ S0,
      W p.2 * (ramRow I Z beta5 p.1 p.2 - rowCentering I Z beta5 E0 S0) ^ 2 := by
    refine Finset.sum_pos' (fun p hp => ?_) ⟨p0, hp0, ?_⟩
    · exact mul_nonneg (hW p hp) (sq_nonneg _)
    · exact mul_pos hW0 (by positivity)
  intro h
  have : ((-10 : ℤ) : ℝ) ≠ 0 := by norm_num
  rcases mul_eq_zero.mp h with h' | h'
  · exact this h'
  · exact absurd h' (ne_of_gt hpos)

/-! ## 5. The attachment of the EP-M2 programme to the canonical `j = 2` owner -/

/-- **CANONICAL `j = 2` ATTACHMENT.**  For the closed row realisation instance the exact bridge
is discharged, so the EP-M2 analytic programme now feeds the *existing* canonical owner with no
exact gap left: an EP-M2 budget for the realised moment family gives the canonical
`J2ResidualCenteredBound` for the canonical centered `j = 2` family.

`EPM2Bound` is **not** inhabited here: only the attachment is established. -/
theorem j2_of_epM2Bound_rowDataClosed (E0 S0 : Finset ℕ) {S0' : ℕ}
    (hM : EPM2Bound (rowDataClosed I Z beta5 W E0 S0).epM2Family S0') :
    J2ResidualCenteredBound (rowDataClosed I Z beta5 W E0 S0).canonicalFamily S0' :=
  j2_of_epM2 (epM2Realisation_rowDataClosed I Z beta5 W E0 S0) hM

/-- The same attachment through the terminal decomposition: the three banked EP-M2 owners
(terminal, cross, low) now reach the canonical owner with **no** exact bridge left open. -/
theorem j2_of_terminal_parts_rowDataClosed (E0 S0 : Finset ℕ) {Mtop Cross Mlow : ℝ → ℝ}
    {S0' : ℕ}
    (hsplit : ∀ x, (rowDataClosed I Z beta5 W E0 S0).epM2Family x
      = Mtop x + 2 * Cross x + Mlow x)
    (htop : EPM2TopBound Mtop S0') (hcross : CrossTermBudget Cross S0')
    (hlow : LowRamanujanBudget Mlow S0') :
    J2ResidualCenteredBound (rowDataClosed I Z beta5 W E0 S0).canonicalFamily S0' :=
  j2_of_terminal_route (epM2Realisation_rowDataClosed I Z beta5 W E0 S0) hsplit htop hcross hlow

/-- **The attachment does not close the owner.**  `J2ResidualCenteredBound` is still refuted by
explicit families, and `EPM2TopBound` is still not inhabited: the analytic cut is unchanged by
this module. -/
theorem attachment_closes_no_owner :
    (∃ DB : ℝ → ℝ, ¬ J2ResidualCenteredBound DB 0)
      ∧ (∃ Mtop : ℝ → ℝ, ¬ EPM2TopBound Mtop 0) :=
  ⟨j2_owner_still_open, terminal_owner_still_open⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
