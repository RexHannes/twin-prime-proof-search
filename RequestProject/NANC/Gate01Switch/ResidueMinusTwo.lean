import Mathlib
import RequestProject.VaughanPacketAlgebra

/-!
# Gate01Switch: the residue `-2` repair

The switched branch runs over the arithmetic progression `n ≡ -2 (mod q)`,
equivalently `q ∣ n + 2`.  The archive's `TwinPrimeProject.finiteDiscrepancy`
uses a *natural* residue `a` and the test `n % q = a % q`; there is no natural
number `a` with `a ≡ -2 (mod q)` for all `q` simultaneously, so the switched
discrepancy is defined here **directly by divisibility**.

Contents (all finite, all proved):

* `residueMinusTwoSet` — the finite index set `{n ≤ K : q ∣ n+2}`;
* `discrMinusTwo`      — the switched discrepancy `Δ_{c,E}(q;-2)`;
* `dvd_add_two_iff_zmod`, `dvd_add_two_iff_mod_eq` — the two equivalent
  residue formulations (`ZMod q` and a genuine natural residue
  `negTwoResidue q`, no negative natural is ever written);
* boundary behaviour at `n = 0`, `n = K`, `q = 1`, `q > K + 2`, together with
  the exact nonemptiness criterion.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open Finset

/-! ## The residue set -/

/-- `A_q = {n : 0 ≤ n ≤ K, q ∣ n + 2}`, as an explicit `Finset`. -/
def residueMinusTwoSet (K q : ℕ) : Finset ℕ :=
  (Finset.range (K + 1)).filter (fun n => q ∣ n + 2)

@[simp] theorem mem_residueMinusTwoSet {K q n : ℕ} :
    n ∈ residueMinusTwoSet K q ↔ n ≤ K ∧ q ∣ n + 2 := by
  simp [residueMinusTwoSet]

/-- The switched finite discrepancy `Δ_{c,E}(q;-2) = ∑_{n ≤ K, q ∣ n+2} c n - E q`. -/
def discrMinusTwo (K q : ℕ) (c E : ℕ → ℝ) : ℝ :=
  (∑ n ∈ residueMinusTwoSet K q, c n) - E q

/-! ## Equivalent residue formulations -/

/-- The `ZMod q` form: `q ∣ n + 2` iff `n = -2` in `ZMod q`. -/
theorem dvd_add_two_iff_zmod (q n : ℕ) : q ∣ n + 2 ↔ ((n : ZMod q) = -2) := by
  rw [← ZMod.natCast_eq_zero_iff (n + 2) q]
  push_cast
  constructor
  · intro hh; linear_combination hh
  · intro hh; rw [hh]; ring

/-- The canonical natural representative of `-2` modulo `q`.  No negative
natural number occurs. -/
def negTwoResidue (q : ℕ) : ℕ := (q - 2 % q) % q

theorem negTwoResidue_lt {q : ℕ} (hq : 0 < q) : negTwoResidue q < q :=
  Nat.mod_lt _ hq

/-- `negTwoResidue q + 2` is divisible by `q`: the representative really is `-2`. -/
theorem q_dvd_negTwoResidue_add_two {q : ℕ} (hq : 0 < q) : q ∣ negTwoResidue q + 2 := by
  have h2 : 2 % q ≤ 2 := Nat.mod_le _ _
  have hlt : 2 % q < q := Nat.mod_lt _ hq
  have hkey : q - 2 % q + 2 = q + q * (2 / q) := by
    have := Nat.div_add_mod 2 q
    omega
  have hmod : negTwoResidue q + 2 = (q - 2 % q) % q + 2 := rfl
  -- reduce to `q ∣ (q - 2 % q) + 2`
  have hstep : q ∣ (q - 2 % q) + 2 := by
    rw [hkey]; exact Dvd.dvd.add (dvd_refl q) ⟨2 / q, rfl⟩
  have : (q - 2 % q) % q + 2 ≡ (q - 2 % q) + 2 [MOD q] :=
    Nat.ModEq.add_right 2 (Nat.mod_modEq _ _)
  rw [hmod]
  exact (Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr hstep)))

theorem negTwoResidue_cast {q : ℕ} (hq : 0 < q) :
    ((negTwoResidue q : ℕ) : ZMod q) = -2 :=
  (dvd_add_two_iff_zmod q _).mp (q_dvd_negTwoResidue_add_two hq)

/-- The genuine natural-residue form: for `q > 0`, `q ∣ n + 2` iff `n` and the
canonical representative of `-2` have the same residue mod `q`. -/
theorem dvd_add_two_iff_mod_eq {q : ℕ} (hq : 0 < q) (n : ℕ) :
    q ∣ n + 2 ↔ n % q = negTwoResidue q := by
  constructor
  · intro h
    have h1 : q ∣ negTwoResidue q + 2 := q_dvd_negTwoResidue_add_two hq
    have : n ≡ negTwoResidue q [MOD q] := by
      have := Nat.ModEq.add_right_cancel' 2
        (show n + 2 ≡ negTwoResidue q + 2 [MOD q] from
          (Nat.modEq_zero_iff_dvd.mpr h).trans (Nat.modEq_zero_iff_dvd.mpr h1).symm)
      exact this
    have hlt := negTwoResidue_lt hq
    simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using this
  · intro h
    have h1 : q ∣ negTwoResidue q + 2 := q_dvd_negTwoResidue_add_two hq
    have hlt := negTwoResidue_lt hq
    have hmod : n ≡ negTwoResidue q [MOD q] := by
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using h
    have : n + 2 ≡ negTwoResidue q + 2 [MOD q] := hmod.add_right 2
    exact Nat.modEq_zero_iff_dvd.mp (this.trans (Nat.modEq_zero_iff_dvd.mpr h1))

/-! ## Boundary behaviour -/

/-- `n = 0` lies in the residue set exactly when `q ∣ 2`. -/
theorem zero_mem_residueMinusTwoSet_iff (K q : ℕ) :
    0 ∈ residueMinusTwoSet K q ↔ q ∣ 2 := by
  simp

/-- `n = K` lies in the residue set exactly when `q ∣ K + 2`. -/
theorem top_mem_residueMinusTwoSet_iff (K q : ℕ) :
    K ∈ residueMinusTwoSet K q ↔ q ∣ K + 2 := by
  simp

/-- For `q = 1` every `n ≤ K` occurs. -/
theorem residueMinusTwoSet_one (K : ℕ) :
    residueMinusTwoSet K 1 = Finset.range (K + 1) := by
  ext n; simp

/-- Above the range the residue set is empty. -/
theorem residueMinusTwoSet_eq_empty_of_gt {K q : ℕ} (hq : K + 2 < q) :
    residueMinusTwoSet K q = ∅ := by
  ext n
  simp only [mem_residueMinusTwoSet, Finset.notMem_empty, iff_false, not_and]
  intro hn hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- Inside the range the residue set is nonempty. -/
theorem residueMinusTwoSet_nonempty {K q : ℕ} (hq : 0 < q) (hle : q ≤ K + 2) :
    (residueMinusTwoSet K q).Nonempty := by
  rcases Nat.lt_or_ge q 2 with h | h
  · have hq1 : q = 1 := by omega
    exact ⟨0, by simp [hq1]⟩
  · exact ⟨q - 2, by
      refine mem_residueMinusTwoSet.mpr ⟨by omega, ?_⟩
      have : q - 2 + 2 = q := by omega
      rw [this]⟩

/-- Consequently the switched discrepancy above the range is exactly `-E q`. -/
theorem discrMinusTwo_of_gt {K q : ℕ} (hq : K + 2 < q) (c E : ℕ → ℝ) :
    discrMinusTwo K q c E = -E q := by
  simp [discrMinusTwo, residueMinusTwoSet_eq_empty_of_gt hq]

end Gate01Switch
end TwinPrimeProject
