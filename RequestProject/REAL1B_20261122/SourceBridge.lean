import RequestProject.REAL1B_20261122.Vaughan
import RequestProject.REAL1B_20261122.WeightedDecomposition

namespace REAL1B.Bridge
open TwinPrimeProject Vaughan
noncomputable section
open Classical

def shiftedPairs (X : ℝ) := ((interval X).image (fun n : ℕ => n-2)).filter
  (fun p => p.Prime ∧ (p+2).Prime)

theorem shiftedPairs_iff (X : ℝ) (p : ℕ) :
    p ∈ shiftedPairs X ↔ X < ((p+2:ℕ):ℝ) ∧ p+2 ≤ ⌊2*X⌋₊ ∧ p.Prime ∧ (p+2).Prime := by
  simp only [shiftedPairs, Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨n,hn,rfl⟩,hp⟩
    have h := Finset.mem_filter.mp hn
    have hl := Finset.mem_Icc.mp h.1
    rw [Nat.sub_add_cancel hl.1] at *
    exact ⟨h.2,hl.2,hp⟩
  · rintro ⟨hl,hh,hp,hq⟩
    exact ⟨⟨p+2, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega,hh⟩,hl⟩, by omega⟩,hp,hq⟩

theorem mass_eq_log_sum (X : ℝ) :
    mass X primeMask = ∑ p ∈ shiftedPairs X, Real.log p := by
  rw [twin_mass_reindex,shiftedPairs,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : p.Prime <;> by_cases k : (p+2).Prime <;> simp [theta,primeMask,h,k]

/-- Historical x=2X. Remove its proper-prime-power error before conversion.
On common pairs log(p+2) and log p differ; the two window differences are signed. -/
theorem historical_conversion (X : ℝ) (hX : 1 < 2*X) :
    ((∑ p ∈ dyadicPrimes (2*X), TwinPrimeWeightedDetector (2*X) p) -
      primePowerError (2*X)) * Real.log (2*X) - mass X primeMask =
    (∑ p ∈ dyadicTwinPrimes (2*X), (Real.log ((p:ℝ)+2) - Real.log p)) +
    (∑ p ∈ dyadicTwinPrimes (2*X) \ shiftedPairs X, Real.log p) -
    ∑ p ∈ shiftedPairs X \ dyadicTwinPrimes (2*X), Real.log p := by
  rw [weighted_decomposition hX, add_sub_cancel_right, Finset.sum_mul, mass_eq_log_sum]
  simp only [div_mul_cancel₀ _ (Real.log_pos hX).ne', Finset.sum_sub_distrib]
  let a := dyadicTwinPrimes (2*X)
  let b := shiftedPairs X
  have ha := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) (Finset.inter_subset_left : a ∩ b ⊆ a)
  have hb := Finset.sum_sdiff (f := fun p : ℕ => Real.log p) (Finset.inter_subset_right : a ∩ b ⊆ b)
  have da : a \ (a ∩ b) = a \ b := by ext p; simp
  have db : b \ (a ∩ b) = b \ a := by ext p; simp
  rw [da] at ha
  rw [db] at hb
  dsimp [a,b] at ha hb
  linarith

end
end REAL1B.Bridge

#print axioms REAL1B.Bridge.shiftedPairs_iff
#print axioms REAL1B.Bridge.mass_eq_log_sum
#print axioms REAL1B.Bridge.historical_conversion
