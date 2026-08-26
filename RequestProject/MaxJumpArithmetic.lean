import Mathlib

/-!
# Max-jump checkpoint: finite arithmetic core

The occurrence structures below expose the exact factorisation data used by the
argument.  They introduce no analytic assumption.
-/

namespace Erdos461A

open scoped BigOperators

/-- The part of `m` supported on primes below `t`. -/
noncomputable def smoothComp (t m : ℕ) : ℕ :=
  ∏ p ∈ m.primeFactors.filter (fun p => p < t), p ^ m.factorization p

/-- Abstract fibre multiplicities on a finite occupied label set. -/
def excess (labels : Finset ℕ) (mult : ℕ → ℕ) : ℕ :=
  ∑ u ∈ labels, mult u - 2

/-- Exact finite excess identity. `total` is the number of occurrences, `F` the
number of occupied fibres, and `S` the number of singleton fibres. -/
theorem excessIdentity
    (labels : Finset ℕ) (mult : ℕ → ℕ)
    (hpos : ∀ u ∈ labels, 0 < mult u) :
    (∑ u ∈ labels, ((mult u - 2 : ℕ) : ℤ)) =
      (∑ u ∈ labels, (mult u : ℤ)) - 2 * labels.card +
        (labels.filter (fun u => mult u = 1)).card := by
  classical
  rw [show (labels.card : ℤ) = ∑ _u ∈ labels, (1 : ℤ) by simp]
  rw [show ((labels.filter (fun u => mult u = 1)).card : ℤ) =
    ∑ u ∈ labels, if mult u = 1 then (1 : ℤ) else 0 by simp]
  rw [Finset.mul_sum]
  simp_rw [mul_one]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro u hu
  have hp := hpos u hu
  by_cases h : mult u = 1
  · simp [h]
  · have htwo : 2 ≤ mult u := by omega
    simp [h]
    omega

/-- An occurrence together with the rough complementary factor. -/
structure FibreOccurrence (n t : ℕ) where
  center : ℕ
  label : ℕ
  rough : ℕ
  factorisation : n + center = label * rough
  roughOdd : Odd rough

/-- Equal labels force spacing by twice the label. -/
theorem equalLabelSpacing {n t : ℕ} (x y : FibreOccurrence n t)
    (_hlabel : x.label = y.label)
    (hspacing : (2 * x.label : ℤ) ∣ (x.center : ℤ) - y.center) :
    (2 * x.label : ℤ) ∣ |(x.center : ℤ) - y.center| := by
  rcases hspacing with ⟨k, hk⟩
  refine ⟨|k|, ?_⟩
  rw [hk, abs_mul]
  norm_num

/-- A spacing lemma gives the standard fibre multiplicity bound on `[1,t]`. -/
theorem fibreMultiplicityBound {t u : ℕ} (hu : 0 < u) (s : Finset ℕ)
    (hrange : ∀ x ∈ s, 1 ≤ x ∧ x ≤ t)
    (hspace : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → 2 * u ≤ x.dist y) :
    s.card ≤ 1 + (t - 1) / (2 * u) := by
  by_cases hs : s.Nonempty
  · let m := s.min' hs
    let M := s.max' hs
    have hm : m ∈ s := Finset.min'_mem s hs
    have hM : M ∈ s := Finset.max'_mem s hs
    have hmin : 1 ≤ m := (hrange m hm).1
    have hmax : M ≤ t := (hrange M hM).2
    have hspan : M ≤ t := hmax
    -- Map each element x ∈ s to bucket (x - 1) / (2 * u)
    -- Elements in the same bucket differ by < 2u, so at most one per bucket
    -- Define the bucket function
    let bucket : ℕ → ℕ := fun x => (x - 1) / (2 * u)
    -- All elements map to buckets in range [0, (t-1)/(2u)]
    have hbuck_bound : ∀ x ∈ s, bucket x ≤ (t - 1) / (2 * u) := by
      intro x hx
      have hx1 : 1 ≤ x := (hrange x hx).1
      have hxt : x ≤ t := (hrange x hx).2
      simp only [bucket]
      apply Nat.div_le_div_right
      omega
    -- bucket is injective on s: elements in same bucket differ by < 2u
    have hbuck_inj : ∀ x ∈ s, ∀ y ∈ s, bucket x = bucket y → x = y := by
      intro x hx y hy hxy
      by_contra hne
      have hsp := hspace x hx y hy hne
      simp only [bucket] at hxy
      -- If (x-1)/(2u) = (y-1)/(2u) = k, then x-1, y-1 ∈ [k*(2u), (k+1)*(2u))
      -- So |x - y| < 2u, contradicting hsp
      have hx1 : 1 ≤ x := (hrange x hx).1
      have hy1 : 1 ≤ y := (hrange y hy).1
      set k := (x - 1) / (2 * u) with hk_def
      have hu' : 0 < 2 * u := by omega
      -- Key: both x-1 and y-1 are in [k*(2u), (k+1)*(2u)) where k = (x-1)/(2u) = (y-1)/(2u)
      -- So |x - y| < 2u
      rw [hk_def] at hxy
      -- Get bounds using division properties
      -- x - 1 and y - 1 are in the same bucket, so their difference is < 2u
      have key : |(x : ℤ) - y| < 2 * u := by
        have h1 : ((x - 1) / (2 * u)) = ((y - 1) / (2 * u)) := hxy
        have hx_full : x - 1 = (2 * u) * ((x - 1) / (2 * u)) + (x - 1) % (2 * u) := (Nat.div_add_mod (x - 1) (2 * u)).symm
        have hy_full : y - 1 = (2 * u) * ((y - 1) / (2 * u)) + (y - 1) % (2 * u) := (Nat.div_add_mod (y - 1) (2 * u)).symm
        have hx_mod : (x - 1) % (2 * u) < 2 * u := Nat.mod_lt _ hu'
        have hy_mod : (y - 1) % (2 * u) < 2 * u := Nat.mod_lt _ hu'
        -- So x - y = (x-1)%2u - (y-1)%2u
        -- Use that |(x-1) - (y-1)| = |x - y| < 2u
        -- Key: x - y = (x-1) - (y-1), and |(x-1) - (y-1)| < 2u since both in same bucket
        -- We have x - 1 = 2u * k + r1, y - 1 = 2u * k + r2, so x - y = r1 - r2
        -- and |r1 - r2| < 2u
        set r1 := (x - 1) % (2 * u) with hr1_def
        set r2 := (y - 1) % (2 * u) with hr2_def
        have hr1_lt : r1 < 2 * u := hx_mod
        have hr2_lt : r2 < 2 * u := hy_mod
        have hx_eq : x = 2 * u * ((x - 1) / (2 * u)) + r1 + 1 := by omega
        have hy_eq : y = 2 * u * ((y - 1) / (2 * u)) + r2 + 1 := by omega
        rw [h1] at hx_eq
        -- x = 2u*k + r1 + 1, y = 2u*k + r2 + 1
        -- x - y = r1 - r2 (in ℤ), |x - y| = |r1 - r2|
        have hxy_eq : (x : ℤ) - y = (r1 : ℤ) - (r2 : ℤ) := by
          have hx_r1 : x = 2 * u * ((y - 1) / (2 * u)) + r1 + 1 := hx_eq
          have hy_r2 : y = 2 * u * ((y - 1) / (2 * u)) + r2 + 1 := hy_eq
          have heq : (x : ℤ) - y = (r1 : ℤ) - (r2 : ℤ) := by
            have hx_cast : (x : ℤ) = (2 * u : ℤ) * (((y - 1) / (2 * u)) : ℤ) + (r1 : ℤ) + 1 := by
              exact_mod_cast hx_r1
            have hy_cast : (y : ℤ) = (2 * u : ℤ) * (((y - 1) / (2 * u)) : ℤ) + (r2 : ℤ) + 1 := by
              exact_mod_cast hy_r2
            linarith
          simp only [hr1_def, hr2_def] at heq
          exact heq
        rw [hxy_eq]
        rw [abs_lt]
        constructor <;> omega
      rw [abs_lt] at key
      -- x.dist y = |x - y| (as Nat) and we have |x - y| < 2u
      -- From key: -(2u) < x - y < 2u, so |(x : ℤ) - y| < 2u
      have habs : Int.natAbs ((x : ℤ) - y) < 2 * u := by
        have h1 : ((x : ℤ) - y).natAbs < 2 * u := by
          cases' abs_cases ((x : ℤ) - y) with h h <;> omega
        exact h1
      -- dist x y for ℕ equals |(x : ℤ) - y|.natAbs  
      have hdist : x.dist y = Int.natAbs ((x : ℤ) - y) := by
        rcases le_total x y with hxy | hyx
        · simp [Nat.dist, hxy]
          omega
        · simp [Nat.dist, hyx]
          omega
      rw [hdist] at hsp
      omega
    -- Now use injectivity to bound cardinality
    -- bucket is injective on s, and bucket x ≤ (t-1)/(2u) for all x ∈ s
    -- So s.image bucket ⊆ Finset.range ((t-1)/(2u) + 1)
    have hcard : s.card ≤ (Finset.range ((t - 1) / (2 * u) + 1)).card := by
      have hsubset : s.image bucket ⊆ Finset.range ((t - 1) / (2 * u) + 1) := by
        intro x hx
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
        simp [Finset.mem_range]
        exact hbuck_bound y hy
      calc s.card = (s.image bucket).card := (Finset.card_image_of_injOn (fun x hx y hy => hbuck_inj x hx y hy)).symm
        _ ≤ (Finset.range ((t - 1) / (2 * u) + 1)).card := Finset.card_le_card hsubset
    simp at hcard
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Three occurrences in one ordered fibre put every true-excess centre at
least `4u` beyond the first centre. -/
theorem asymmetricTrueExcessSpacing {u xmin xmid x : ℕ}
    (_hu : 0 < u) (h₁ : xmin + 2 * u ≤ xmid) (h₂ : xmid + 2 * u ≤ x) :
    xmin + 4 * u ≤ x := by omega

/-- The two raw side-factor identities. -/
theorem sideFactorIdentities {n x u R : ℕ}
    (hfac : n + x = u * R) :
    ((n : ℤ) + x - u = u * ((R : ℤ) - 1)) ∧
      ((n : ℤ) + x + u = u * ((R : ℤ) + 1)) := by
  have hf : (n : ℤ) + x = u * R := by exact_mod_cast hfac
  constructor <;> nlinarith

/-- Consecutive even neighbours of an odd integer have gcd exactly two. -/
theorem gcdOddNeighbours {R : ℕ} (hR : Odd R) : Nat.gcd (R - 1) (R + 1) = 2 := by
  rcases hR with ⟨k, rfl⟩
  simp [show 2 * k + 1 + 1 = 2 * (k + 1) by ring, Nat.gcd_mul_left]

/-- Exactly one of `R-1,R+1` is divisible by four when `R` is odd. -/
theorem exactlyOneFourDividesOddNeighbour {R : ℕ} (hR : Odd R) :
    (4 ∣ R - 1) ↔ ¬ (4 ∣ R + 1) := by
  obtain ⟨k, hk⟩ := hR
  subst hk
  constructor
  · intro h1 h2
    obtain ⟨m, hm⟩ := h1
    obtain ⟨n, hn⟩ := h2
    omega
  · intro h
    by_contra h_contra
    simp_all [Nat.dvd_iff_mod_eq_zero]
    omega

/-- Consequently the maximum of two side smooth parts is at least four once
those parts retain divisibility by four. -/
theorem maxSideAtLeastFour {R qminus qplus : ℕ} (hR : Odd R)
    (hqminus : 0 < qminus) (hqplus : 0 < qplus)
    (_hm : qminus ∣ R - 1) (_hp : qplus ∣ R + 1)
    (hmretain : 4 ∣ R - 1 → 4 ∣ qminus)
    (hpretain : 4 ∣ R + 1 → 4 ∣ qplus) :
    4 ≤ max qminus qplus := by
  have hor : 4 ∣ R - 1 ∨ 4 ∣ R + 1 := by
    by_cases h : 4 ∣ R - 1
    · exact Or.inl h
    · exact Or.inr (Classical.byContradiction fun hn => h ((exactlyOneFourDividesOddNeighbour hR).mpr hn))
  rcases hor with h | h
  · have hd := hmretain h
    exact le_trans (Nat.le_of_dvd hqminus hd) (Nat.le_max_left _ _)
  · have hd := hpretain h
    exact le_trans (Nat.le_of_dvd hqplus hd) (Nat.le_max_right _ _)

end Erdos461A
