import Mathlib

/-!
# HFMV Gate 1B, Module 1: the complementary divisor variable `l`

Source-native form.  The incidence constraint of the HFMV determinant bank is

  `u * v + 2 = d * p * l`,

i.e. the divisibility `d p ∣ u v + 2` together with the *named* complementary
divisor `l`.

Everything here is finite/algebraic and is stated over `ℤ` (so that no `Nat`
subtraction appears).  Positivity and dyadic range variants are proved
separately and are never assumed silently.
-/

namespace TwinPrimeProject
namespace HFMVGate1B

/-! ## 1. The complementary-divisor equivalence -/

/-- **Complementary divisor equivalence.**  `d p ∣ u v + 2` iff the incidence
equation `u v + 2 = d p l` is solvable in `l ∈ ℤ`. -/
theorem dvd_iff_exists_ell (u v d p : ℤ) :
    d * p ∣ u * v + 2 ↔ ∃ l : ℤ, u * v + 2 = d * p * l := by
  constructor
  · rintro ⟨l, hl⟩; exact ⟨l, hl⟩
  · rintro ⟨l, hl⟩; exact ⟨l, hl⟩

/-- **Source-native incidence predicate.** -/
def Incidence (u v d p l : ℤ) : Prop := u * v + 2 = d * p * l

/-- The incidence predicate is exactly the complementary-divisor form of the
divisibility. -/
theorem dvd_iff_exists_incidence (u v d p : ℤ) :
    d * p ∣ u * v + 2 ↔ ∃ l : ℤ, Incidence u v d p l :=
  dvd_iff_exists_ell u v d p

/-- The divisibility follows from any incidence. -/
theorem Incidence.dvd {u v d p l : ℤ} (h : Incidence u v d p l) :
    d * p ∣ u * v + 2 := ⟨l, h⟩

/-! ## 2. Uniqueness of `l` -/

/-- **Uniqueness of the complementary divisor** for a nonzero modulus `d p`. -/
theorem ell_unique {u v d p l l' : ℤ} (hdp : d * p ≠ 0)
    (h : Incidence u v d p l) (h' : Incidence u v d p l') : l = l' := by
  have : d * p * l = d * p * l' := by
    unfold Incidence at h h'; rw [← h, ← h']
  exact mul_left_cancel₀ hdp this

/-- Uniqueness of `l` for *positive* `d, p`, the case used for dyadic
variables. -/
theorem ell_unique_of_pos {u v d p l l' : ℤ} (hd : 0 < d) (hp : 0 < p)
    (h : Incidence u v d p l) (h' : Incidence u v d p l') : l = l' :=
  ell_unique (by positivity) h h'

/-- `l` is the exact quotient `(u v + 2) / (d p)`. -/
theorem ell_eq_div {u v d p l : ℤ} (hdp : d * p ≠ 0) (h : Incidence u v d p l) :
    l = (u * v + 2) / (d * p) := by
  unfold Incidence at h
  rw [h, Int.mul_ediv_cancel_left _ hdp]

/-- **Existence and uniqueness** of the complementary divisor. -/
theorem existsUnique_ell {u v d p : ℤ} (hdp : d * p ≠ 0) (hdvd : d * p ∣ u * v + 2) :
    ∃! l : ℤ, Incidence u v d p l := by
  obtain ⟨l, hl⟩ := (dvd_iff_exists_incidence u v d p).mp hdvd
  exact ⟨l, hl, fun l' hl' => ell_unique hdp hl' hl⟩

/-! ## 3. Positivity and dyadic range variants -/

/-- For positive `u, v, d, p` the complementary divisor is positive. -/
theorem ell_pos {u v d p l : ℤ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (hp : 0 < p)
    (h : Incidence u v d p l) : 0 < l := by
  unfold Incidence at h
  have hdp : 0 < d * p := mul_pos hd hp
  have h1 : 0 < u * v + 2 := by nlinarith [mul_pos hu hv]
  have h2 : 0 < d * p * l := by rw [← h]; exact h1
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_nonneg hdp.le (neg_nonneg.mpr hcon)]

/-- Equivalently, `1 ≤ l` in the positive range. -/
theorem one_le_ell {u v d p l : ℤ} (hu : 0 < u) (hv : 0 < v) (hd : 0 < d) (hp : 0 < p)
    (h : Incidence u v d p l) : 1 ≤ l := ell_pos hu hv hd hp h

/-- **Dyadic range bound.**  If `u ≤ U`, `v ≤ V` with all data positive, then
`d p l ≤ U V + 2`; in particular `l` is confined to a finite range once `d p`
is bounded below. -/
theorem ell_range {u v d p l U V : ℤ} (hu : 0 < u) (hv : 0 < v)
    (hU : u ≤ U) (hV : v ≤ V) (h : Incidence u v d p l) :
    d * p * l ≤ U * V + 2 := by
  unfold Incidence at h
  nlinarith [hu.le, hv.le]

/-- Dyadic upper bound on `l` itself: if additionally `0 < d p` then
`l ≤ U V + 2` divided by `d p`, in the multiplicative form
`(d p) * l ≤ U V + 2`, hence `l ≤ U V + 2` whenever `1 ≤ d p`. -/
theorem ell_le_of_one_le_modulus {u v d p l U V : ℤ} (hu : 0 < u) (hv : 0 < v)
    (hU : u ≤ U) (hV : v ≤ V) (hdp : 1 ≤ d * p) (hl : 0 < l)
    (h : Incidence u v d p l) : l ≤ U * V + 2 := by
  have hrange := ell_range hu hv hU hV h
  nlinarith

end HFMVGate1B
end TwinPrimeProject
