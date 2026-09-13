/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the exact Wright prefix geometry  (P4)

Append-only module.  **Exponent geometry only** — purely rational arithmetic.  The Wright
analytic theorem is a named proposition and is *never* inhabited here.

* §1 the Wright interface region `θ = η + a + b ≤ 45/89 − ε_W` and the conditional membership
  statement (conditional only on the named Wright proposition);
* §2 the **universal η prefix**: if the *maximal* physical packet at block exponent `η` (both
  atoms at their physical ceiling `(1−η)/5`) lies in the Wright region, then

  ```
  η ≤ 47/267 − (5/3) ε_W .
  ```

  The computation is exact: `η + 2(1−η)/5 ≤ 45/89 − ε_W` gives `3η/5 ≤ 47/445 − ε_W`;
* §3 the converse geometry (the prefix is sharp) and the statement that Wright coverage of the
  whole physical `η`-range fails: for `η > 47/267` the maximal physical packet is outside the
  Wright region.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.KFiveAlgebra

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-! ## 1. The Wright interface region -/

/-- **The Wright interface region** at slack `ε_W`: total exponent at most `45/89 − ε_W`. -/
def WrightRegion (epsW : ℚ) (p : K5Packet) : Prop := p.theta ≤ 45/89 - epsW

instance (epsW : ℚ) (p : K5Packet) : Decidable (WrightRegion epsW p) := by
  unfold WrightRegion; infer_instance

/-- **The Wright analytic proposition**, indexed by the region it certifies: for every packet of
the region, the associated bilinear family enjoys the stated power saving.
EXTERNAL_ANALYTIC — stated, never inhabited, not an axiom. -/
def WrightAnalyticInput (epsW : ℚ) (form : K5Packet → ℝ → ℝ) (delta : ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ p : K5Packet, WrightRegion epsW p → ∀ x : ℝ, 3 ≤ x →
    |form p x| ≤ C * x ^ (1 - delta)

/-- **Conditional membership.**  A packet in the Wright region inherits the Wright saving —
conditional only on the named Wright proposition, which is not inhabited. -/
theorem wright_saving_of_region {epsW : ℚ} {form : K5Packet → ℝ → ℝ} {delta : ℝ}
    (hW : WrightAnalyticInput epsW form delta) {p : K5Packet} (hp : WrightRegion epsW p) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 3 ≤ x → |form p x| ≤ C * x ^ (1 - delta) := by
  obtain ⟨C, hC, h⟩ := hW
  exact ⟨C, hC, fun x hx => h p hp x hx⟩

/-! ## 2. The universal η prefix -/

/-- **The universal Wright η prefix** (exact rational geometry).  If the maximal physical packet
at block exponent `η` lies in the Wright region, then `η ≤ 47/267 − (5/3) ε_W`. -/
theorem wright_eta_prefix {eta epsW : ℚ} (h : WrightRegion epsW (maximalPacket eta)) :
    eta ≤ 47/267 - (5/3) * epsW := by
  unfold WrightRegion at h
  rw [maximalPacket_theta] at h
  linarith

/-- The prefix is exactly equivalent to Wright covering the maximal physical packet. -/
theorem wright_eta_prefix_iff (eta epsW : ℚ) :
    WrightRegion epsW (maximalPacket eta) ↔ eta ≤ 47/267 - (5/3) * epsW := by
  unfold WrightRegion
  rw [maximalPacket_theta]
  constructor <;> intro h <;> linarith

/-- **Wright does not cover the physical range.**  For `η` above the prefix the maximal physical
packet leaves the Wright region: the certified region really is only a prefix in `η`. -/
theorem wright_fails_above_prefix {eta epsW : ℚ} (h : 47/267 - (5/3) * epsW < eta) :
    ¬ WrightRegion epsW (maximalPacket eta) := by
  intro hW
  linarith [wright_eta_prefix hW]

/-- The prefix bound is strictly inside the retained physical `η`-range: `47/267 < 99/200`,
so the uncovered physical band `(47/267, 99/200)` is nonempty already at `ε_W = 0`. -/
theorem prefix_lt_physical_eta_ceiling : (47 : ℚ)/267 < 99/200 := by norm_num

/-- An explicit uncovered physical block exponent: `η = 2/5` is physical (as a block exponent)
and beyond the Wright prefix at every nonnegative slack. -/
theorem uncovered_eta_two_fifths {epsW : ℚ} (h : 0 ≤ epsW) :
    (2 : ℚ)/5 < 99/200 ∧ ¬ WrightRegion epsW (maximalPacket (2/5)) := by
  refine ⟨by norm_num, wright_fails_above_prefix ?_⟩
  linarith

end Gate1B.R11.Frontier.CanonicalRootSync
