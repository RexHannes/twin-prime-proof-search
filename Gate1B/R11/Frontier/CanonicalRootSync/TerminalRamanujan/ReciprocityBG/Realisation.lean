/-
# Gate1B / R11 / Frontier / CanonicalRootSync / TerminalRamanujan / ReciprocityBG :
the exact sub-bridges of `epM2Realisation`  (B1)

Append-only module.  Nothing pre-existing is edited, renamed, weakened or deleted; in
particular `epM2Realisation`, `EPM2Bound` and the canonical owner `J2ResidualCenteredBound`
keep their original statements, and the canonical cut is untouched.

`epM2Realisation DB M` (banked in `CanonicalBridge.lean`) is the *exact identification* of the
canonical centered `j = 2` residual family with the EP-M2 raw moment family.  Up to now it was
carried as one single unanalysed missing bridge.  This module opens it up: a single data record
`RealisationData` carries the canonical packet, source weight and row kernel together with the
EP-M2 chart (index map, `e`- and `s`-ranges, weight, row values, normalisation, packet mask),
and the identification is decomposed into explicit sub-bridges

* `indexSetRealisation`      — the chart image sits inside the canonical packet;
* `chartInjectivity`         — the chart is injective on its box (no double counting);
* `maskRealisation`          — the packet mask cuts out exactly the chart image;
* `sourceSupportRealisation` — the canonical source vanishes off the mask;
* `sourceWeightRealisation`  — the canonical source coefficient is the weighted row value;
* `normalisationRealisation` — the two normalisations agree (`= hbCoeff 5 2 = −10`);
* `rowRealisation`           — the *centered canonical kernel* at a chart point is the EP-M2
                               row value.

§2 proves, in the kernel, that the conjunction of these implies `epM2Realisation`
(`epM2Realisation_of_subBridges`).  §3 exhibits the canonical instance `ofCanonical`, in which
`sourceWeightRealisation` and `normalisationRealisation` hold *by construction* and the three
chart conditions are pure bookkeeping, so that **exactly one** genuinely arithmetic
identification remains: `rowRealisation`, renamed `epM2RowIdentification`.  §4 proves that this
remaining bridge is load-bearing (a finite countermodel in which the other bridges hold and the
identification fails), so it may not be silently upgraded.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.CanonicalBridge

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG

open Finset
open Gate1B.R11.Frontier.CanonicalRootSync
open Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan

/-! ## 1. The realisation data and the sub-bridges -/

/-- All data entering the exact identification of the canonical centered `j = 2` residual with
the EP-M2 raw moment: the canonical side (`pkt`, `g`, `K`, `mask`), the EP-M2 side
(`E`, `S`, `W`, `R`, `nrm`) and the chart `idx` connecting them. -/
structure RealisationData where
  /-- the canonical packet at scale `x` -/
  pkt : ℝ → Finset ℕ
  /-- the canonical source weight -/
  g : ℕ → ℝ
  /-- the canonical row kernel -/
  K : ℕ → ℝ
  /-- the packet mask of the canonical chart -/
  mask : ℕ → Bool
  /-- the chart sending an EP-M2 index pair `(e, s)` to a canonical packet index -/
  idx : ℕ × ℕ → ℕ
  /-- the EP-M2 `e`-range at scale `x` -/
  E : ℝ → Finset ℕ
  /-- the EP-M2 `s`-range at scale `x` -/
  S : ℝ → Finset ℕ
  /-- the EP-M2 outer weight -/
  W : ℕ → ℝ
  /-- the EP-M2 row values -/
  R : ℝ → ℕ → ℕ → ℝ
  /-- the EP-M2 normalisation factor -/
  nrm : ℝ

namespace RealisationData

/-- The EP-M2 index box at scale `x`. -/
def chart (D : RealisationData) (x : ℝ) : Finset (ℕ × ℕ) := D.E x ×ˢ D.S x

/-- The canonical centered `j = 2` residual family attached to the data. -/
noncomputable def canonicalFamily (D : RealisationData) (x : ℝ) : ℝ :=
  dbCentered (D.pkt x) D.g D.K

/-- The EP-M2 raw moment family attached to the data. -/
def epM2Family (D : RealisationData) (x : ℝ) : ℝ :=
  D.nrm * moment (D.E x) (D.S x) D.W (D.R x)

end RealisationData

open RealisationData

/-- **Sub-bridge 1 — `indexSetRealisation`.**  Every chart point lands in the canonical
packet. -/
def indexSetRealisation (D : RealisationData) : Prop :=
  ∀ x, (D.chart x).image D.idx ⊆ D.pkt x

/-- **Sub-bridge 2 — `chartInjectivity`.**  The chart is injective on its box: the EP-M2
indexing does not double-count canonical packet points. -/
def chartInjectivity (D : RealisationData) : Prop :=
  ∀ x, ∀ p ∈ D.chart x, ∀ q ∈ D.chart x, D.idx p = D.idx q → p = q

/-- **Sub-bridge 3 — `maskRealisation`.**  Inside the canonical packet the mask cuts out
exactly the chart image. -/
def maskRealisation (D : RealisationData) : Prop :=
  ∀ x, ∀ n ∈ D.pkt x, (D.mask n = true ↔ n ∈ (D.chart x).image D.idx)

/-- **Sub-bridge 4 — `sourceSupportRealisation`.**  The canonical source weight vanishes off
the mask. -/
def sourceSupportRealisation (D : RealisationData) : Prop :=
  ∀ n, D.mask n = false → D.g n = 0

/-- **Sub-bridge 5 — `sourceWeightRealisation`.**  At a chart point the canonical source
coefficient is the EP-M2 outer weight times the EP-M2 row value. -/
def sourceWeightRealisation (D : RealisationData) : Prop :=
  ∀ x, ∀ p ∈ D.chart x, D.g (D.idx p) = D.W p.2 * D.R x p.1 p.2

/-- **Sub-bridge 6 — `normalisationRealisation`.**  The EP-M2 normalisation is the `j = 2`
coefficient `hbCoeff 5 2 = −10` of the K = 5 row. -/
def normalisationRealisation (D : RealisationData) : Prop :=
  D.nrm = (hbCoeff 5 2 : ℝ)

/-- **Sub-bridge 7 — `rowRealisation`.**  At a chart point the *centered* canonical kernel is
the EP-M2 row value.  This is the only sub-bridge carrying arithmetic content. -/
def rowRealisation (D : RealisationData) : Prop :=
  ∀ x, ∀ p ∈ D.chart x, D.K (D.idx p) - kernelMean (D.pkt x) D.K = D.R x p.1 p.2

/-! ## 2. The sub-bridges imply the exact identification -/

/-- The canonical centered residual is carried by the chart image: off the image the source
vanishes, by `maskRealisation` and `sourceSupportRealisation`. -/
theorem canonical_sum_over_chart {D : RealisationData} (hidx : indexSetRealisation D)
    (hmask : maskRealisation D) (hsupp : sourceSupportRealisation D) (x : ℝ) :
    ∑ n ∈ D.pkt x, D.g n * (D.K n - kernelMean (D.pkt x) D.K)
      = ∑ n ∈ (D.chart x).image D.idx, D.g n * (D.K n - kernelMean (D.pkt x) D.K) := by
  refine (Finset.sum_subset (hidx x) ?_).symm
  intro n hn hnot
  have hfalse : D.mask n = false := by
    cases hm : D.mask n with
    | false => rfl
    | true => exact absurd ((hmask x n hn).mp hm) hnot
  rw [hsupp n hfalse, zero_mul]

/-- **All sub-bridges ⇒ `epM2Realisation`.**  Kernel-proved: no bound, no approximation, no
replacement of either side by a looser object. -/
theorem epM2Realisation_of_subBridges {D : RealisationData}
    (hidx : indexSetRealisation D) (hinj : chartInjectivity D) (hmask : maskRealisation D)
    (hsupp : sourceSupportRealisation D) (hw : sourceWeightRealisation D)
    (hnrm : normalisationRealisation D) (hrow : rowRealisation D) :
    epM2Realisation D.canonicalFamily D.epM2Family := by
  intro x
  unfold RealisationData.canonicalFamily RealisationData.epM2Family dbCentered moment
  rw [hnrm, canonical_sum_over_chart hidx hmask hsupp x,
    Finset.sum_image (fun p hp q hq h => hinj x p hp q hq h)]
  congr 1
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p ∈ D.chart x := hp
  rw [hw x p hp', hrow x p hp']
  ring

/-! ## 3. The canonical instance: exactly one missing identification -/

/-- The canonical realisation instance: the EP-M2 outer weight is `1`, the EP-M2 row values are
*defined* to be the canonical source coefficients at the chart points, and the normalisation is
the K = 5 `j = 2` coefficient.  In this instance `sourceWeightRealisation` and
`normalisationRealisation` hold by construction. -/
def ofCanonical (pkt : ℝ → Finset ℕ) (g K : ℕ → ℝ) (mask : ℕ → Bool) (idx : ℕ × ℕ → ℕ)
    (E S : ℝ → Finset ℕ) : RealisationData where
  pkt := pkt
  g := g
  K := K
  mask := mask
  idx := idx
  E := E
  S := S
  W := fun _ => 1
  R := fun _ e s => g (idx (e, s))
  nrm := (hbCoeff 5 2 : ℝ)

variable (pkt : ℝ → Finset ℕ) (g K : ℕ → ℝ) (mask : ℕ → Bool) (idx : ℕ × ℕ → ℕ)
  (E S : ℝ → Finset ℕ)

theorem ofCanonical_sourceWeight :
    sourceWeightRealisation (ofCanonical pkt g K mask idx E S) := by
  intro x p _
  simp [ofCanonical]

theorem ofCanonical_normalisation :
    normalisationRealisation (ofCanonical pkt g K mask idx E S) := rfl

/-- **`epM2RowIdentification`** — the single remaining exact identification below EP-M2: at each
chart point the centered canonical kernel equals the EP-M2 row value.  MISSING EXACT BRIDGE —
stated, never inhabited, not an axiom.  Every other sub-bridge of `epM2Realisation` is either
kernel-proved for the canonical instance (`sourceWeightRealisation`,
`normalisationRealisation`) or pure chart bookkeeping (`indexSetRealisation`,
`chartInjectivity`, `maskRealisation`, `sourceSupportRealisation`). -/
def epM2RowIdentification (D : RealisationData) : Prop := rowRealisation D

/-- **The reduction of `epM2Realisation` to the single missing identification.**  For the
canonical instance, the chart bookkeeping plus `epM2RowIdentification` give the exact
identification; the two remaining sub-bridges have been discharged. -/
theorem epM2Realisation_ofCanonical
    (hidx : indexSetRealisation (ofCanonical pkt g K mask idx E S))
    (hinj : chartInjectivity (ofCanonical pkt g K mask idx E S))
    (hmask : maskRealisation (ofCanonical pkt g K mask idx E S))
    (hsupp : sourceSupportRealisation (ofCanonical pkt g K mask idx E S))
    (hrow : epM2RowIdentification (ofCanonical pkt g K mask idx E S)) :
    epM2Realisation (ofCanonical pkt g K mask idx E S).canonicalFamily
      (ofCanonical pkt g K mask idx E S).epM2Family :=
  epM2Realisation_of_subBridges hidx hinj hmask hsupp
    (ofCanonical_sourceWeight pkt g K mask idx E S)
    (ofCanonical_normalisation pkt g K mask idx E S) hrow

/-! ## 4. The remaining identification is load-bearing -/

/-- A one-point instance: packet `{0}`, source and kernel equal to `1`, chart collapsing to the
single index `0`, row value `1`. -/
def toyData : RealisationData where
  pkt := fun _ => {0}
  g := fun _ => 1
  K := fun _ => 1
  mask := fun _ => true
  idx := fun _ => 0
  E := fun _ => {0}
  S := fun _ => {0}
  W := fun _ => 1
  R := fun _ _ _ => 1
  nrm := (hbCoeff 5 2 : ℝ)

theorem toyData_chart (x : ℝ) : toyData.chart x = {((0 : ℕ), (0 : ℕ))} := rfl

/-- **The row identification may not be dropped.**  In `toyData` all the other sub-bridges hold,
yet the canonical family and the EP-M2 family differ: `epM2Realisation` fails.  Hence
`epM2RowIdentification` is genuinely load-bearing and is the exact remaining content of the
bridge. -/
theorem epM2RowIdentification_load_bearing :
    indexSetRealisation toyData ∧ chartInjectivity toyData ∧ maskRealisation toyData
      ∧ sourceSupportRealisation toyData ∧ sourceWeightRealisation toyData
      ∧ normalisationRealisation toyData
      ∧ ¬ epM2RowIdentification toyData
      ∧ ¬ epM2Realisation toyData.canonicalFamily toyData.epM2Family := by
  refine ⟨?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
  · intro x
    simp [toyData, RealisationData.chart]
  · intro x p hp q hq _
    rw [toyData_chart] at hp hq
    rw [Finset.mem_singleton] at hp hq
    rw [hp, hq]
  · intro x n hn
    have hn0 : n = 0 := by simpa [toyData] using hn
    subst hn0
    simp [toyData, RealisationData.chart]
  · intro n hn
    simp [toyData] at hn
  · intro x p _
    simp [toyData]
  · intro h
    have h0 := h 0 ((0 : ℕ), (0 : ℕ)) (by rw [toyData_chart]; exact Finset.mem_singleton_self _)
    simp [toyData, kernelMean] at h0
  · intro h
    have h0 := h 0
    have hcan : toyData.canonicalFamily 0 = 0 := by
      simp [RealisationData.canonicalFamily, toyData, dbCentered, kernelMean]
    have hep : toyData.epM2Family 0 = -10 := by
      simp [RealisationData.epM2Family, toyData, moment, hbCoeff_five_two]
    rw [hcan, hep] at h0
    norm_num at h0

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG
