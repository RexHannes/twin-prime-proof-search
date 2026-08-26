import RequestProject.NANC.Gate01Consolidation.NonzeroOrthogonality

/-!
# BANK L / M — direct Gauss / character reassembly and non-unit stratification

**BANK L.**  With `c = q₁ q₂ m` the schematic character factors
`χ(x) χ(m + k r) conj χ(2k) χ(p₁p₂) conj χ(N)` combine into
`χ(x (m + k r) p₁ p₂) conj χ(2 k N)` (**CHAR-COMB**, `char_combine`).

The resulting finite theorem is *not* "the character sum is small": it is that
the congruence

`x (m + k r) p₁ p₂ ≡ 2 k N (mod c)`   (**GAUSS-CONG**)

pins down `x` **when the coefficient is a unit**, and that the additive sum over
the solution set then collapses to a single physical phase (**GAUSS-PHYS**,
**DIRECT-PHYS**).  The non-unit case is *not* ignored: it is treated in BANK M.

```text
DIRECT_GAUSS_CHARACTER_SUM_REMOVED = PROVED FINITE ALGEBRA
DIRECT_PHYSICAL_PHASE_POWER_SAVING = OPEN ANALYTIC
```

**BANK M.**  The classical stratification of `A x ≡ B (mod c)` by
`g = gcd(A, c)`: solvability iff `g ∣ B`, the solution set is one residue class
modulo `c/g`, and it consists of exactly `g` classes modulo `c`.  No analytic
saving is claimed from it.
-/

namespace TwinPrimeProject
namespace Gate01Consolidation

open Finset

/-! ## BANK L — character combination and the unit case -/

/-- **CHAR-COMB.**  The five schematic character factors combine into one
multiplicative character of the reassembled argument. -/
theorem char_combine {c : ℕ} (chi : MulChar (ZMod c) ℂ) (x m k r p₁ p₂ N : ZMod c) :
    chi x * chi (m + k * r) * (starRingEnd ℂ) (chi (2 * k)) * chi (p₁ * p₂)
        * (starRingEnd ℂ) (chi N)
      = chi (x * (m + k * r) * (p₁ * p₂)) * (starRingEnd ℂ) (chi (2 * k * N)) := by
  simp only [map_mul chi, map_mul (starRingEnd ℂ)]
  ring

/-- **GAUSS-CONG (unit case).**  If the coefficient `A` is a unit modulo `c`,
the congruence `A x ≡ B` has the unique solution `x = A⁻¹ B`. -/
theorem gaussReassembly_unit {c : ℕ} {A B : ZMod c} (hA : IsUnit A) (x : ZMod c) :
    A * x = B ↔ x = ((hA.unit⁻¹ : (ZMod c)ˣ) : ZMod c) * B := by
  constructor
  · rintro rfl
    rw [← mul_assoc]
    have h1 : ((hA.unit⁻¹ : (ZMod c)ˣ) : ZMod c) * A = 1 := by simp
    rw [h1, one_mul]
  · rintro rfl
    rw [← mul_assoc]
    have h1 : A * ((hA.unit⁻¹ : (ZMod c)ˣ) : ZMod c) = 1 := by simp
    rw [h1, one_mul]

/-- The additive character on `ZMod c`, `x ↦ e_c(x)`. -/
noncomputable def ecz (c : ℕ) (x : ZMod c) : ℂ := ec c (x.val : ℤ)

/-- **GAUSS-PHYS.**  In the unit case the additive sum over the solution set of
`A x ≡ B (mod c)` collapses to the single physical phase `e_c(A⁻¹ B)`. -/
theorem gauss_phys {c : ℕ} [NeZero c] {A B : ZMod c} (hA : IsUnit A) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod c => A * x = B), ecz c x
      = ecz c (((hA.unit⁻¹ : (ZMod c)ˣ) : ZMod c) * B) := by
  have hset : Finset.univ.filter (fun x : ZMod c => A * x = B)
      = {((hA.unit⁻¹ : (ZMod c)ˣ) : ZMod c) * B} := by
    ext x
    simp [gaussReassembly_unit hA x]
  rw [hset, Finset.sum_singleton]

/-- **DIRECT-PHYS.**  The instantiation `A = (m + k r) p₁ p₂`, `B = 2 k N`:
after the multiplicative characters are removed, the direct family carries the
single physical phase `e_c(2 k N · ((m + k r) p₁ p₂)⁻¹)`. -/
theorem direct_phys {c : ℕ} [NeZero c] {m k r p₁ p₂ N : ZMod c}
    (hA : IsUnit ((m + k * r) * (p₁ * p₂))) :
    ∑ x ∈ Finset.univ.filter (fun x : ZMod c => (m + k * r) * (p₁ * p₂) * x = 2 * k * N),
        ecz c x
      = ecz c (((hA.unit⁻¹ : (ZMod c)ˣ) : ZMod c) * (2 * k * N)) :=
  gauss_phys hA

/-- **GaussReassembly_nonunit_condition.**  If the coefficient is *not* a unit
the collapse above is unavailable: the solution set of `A x ≡ B` is then either
empty or has more than one element (it is a coset of the nontrivial kernel of
multiplication by `A`).  Concretely, non-uniqueness is witnessed by any nonzero
kernel element. -/
theorem gaussReassembly_nonunit_condition {c : ℕ} {A B : ZMod c} {x y : ZMod c}
    (hx : A * x = B) (hy : A * y = B) : A * (x - y) = 0 := by
  rw [mul_sub, hx, hy, sub_self]

/-! ## BANK M — non-unit linear congruence stratification -/

/-- **Solvability.**  `A x ≡ B (mod c)` is solvable iff `gcd(A, c) ∣ B`. -/
theorem linearCongruence_solvable_iff {A B : ℤ} {c : ℕ} :
    (∃ x : ℤ, A * x ≡ B [ZMOD (c : ℤ)]) ↔ ((Int.gcd A c : ℤ) ∣ B) := by
  constructor
  · rintro ⟨x, hx⟩
    have hdvd : (c : ℤ) ∣ B - A * x := Int.ModEq.dvd hx
    obtain ⟨y, hy⟩ := hdvd
    have hB : B = A * x + c * y := by linarith [hy]
    have h1 : (Int.gcd A c : ℤ) ∣ A := Int.gcd_dvd_left A (c : ℤ)
    have h2 : (Int.gcd A c : ℤ) ∣ (c : ℤ) := Int.gcd_dvd_right A (c : ℤ)
    rw [hB]
    exact dvd_add (h1.mul_right x) (h2.mul_right y)
  · rintro ⟨t, ht⟩
    have hbez : (Int.gcd A c : ℤ) = A * Int.gcdA A c + (c : ℤ) * Int.gcdB A c :=
      Int.gcd_eq_gcd_ab A c
    refine ⟨Int.gcdA A c * t, ?_⟩
    have : B - A * (Int.gcdA A c * t) = (c : ℤ) * (Int.gcdB A c * t) := by
      rw [ht, hbez]; ring
    exact (Int.modEq_iff_dvd.mpr ⟨Int.gcdB A c * t, this⟩)

/-- **Reduction to one residue class.**  If `x₀` solves `A x ≡ B (mod c)` and
`c > 0`, then the solutions are exactly the integers congruent to `x₀` modulo
`c / gcd(c, A)`. -/
theorem linearCongruence_solution_class {A B x₀ : ℤ} {c : ℕ} (hc : 0 < (c : ℤ))
    (h₀ : A * x₀ ≡ B [ZMOD (c : ℤ)]) (x : ℤ) :
    A * x ≡ B [ZMOD (c : ℤ)] ↔ x ≡ x₀ [ZMOD ((c : ℤ) / (Int.gcd (c : ℤ) A : ℤ))] := by
  constructor
  · intro hx
    exact Int.ModEq.cancel_left_div_gcd hc (hx.trans h₀.symm)
  · intro hx
    refine Int.ModEq.trans ?_ h₀
    have hg : (Int.gcd (c : ℤ) A : ℤ) ∣ A := Int.gcd_dvd_right (c : ℤ) A
    obtain ⟨A', hA'⟩ := hg
    have hgc : (Int.gcd (c : ℤ) A : ℤ) ∣ (c : ℤ) := Int.gcd_dvd_left (c : ℤ) A
    obtain ⟨c', hc'⟩ := hgc
    have hgpos : (0 : ℤ) < (Int.gcd (c : ℤ) A : ℤ) := by
      have : Int.gcd (c : ℤ) A ≠ 0 := by
        intro h
        have := Int.eq_zero_of_gcd_eq_zero_left h
        omega
      exact_mod_cast Nat.pos_of_ne_zero this
    have hdivc : (c : ℤ) / (Int.gcd (c : ℤ) A : ℤ) = c' :=
      (Int.eq_ediv_of_mul_eq_right (ne_of_gt hgpos) hc'.symm).symm
    rw [hdivc] at hx
    have hdvd : c' ∣ (x - x₀) := Int.ModEq.dvd hx.symm
    obtain ⟨k, hk⟩ := hdvd
    have : A * x - A * x₀ = (c : ℤ) * (A' * k) := by
      have : x - x₀ = c' * k := hk
      calc A * x - A * x₀ = A * (x - x₀) := by ring
        _ = A * (c' * k) := by rw [this]
        _ = (Int.gcd (c : ℤ) A : ℤ) * A' * (c' * k) := by rw [← hA']
        _ = ((Int.gcd (c : ℤ) A : ℤ) * c') * (A' * k) := by ring
        _ = (c : ℤ) * (A' * k) := by rw [← hc']
    exact (Int.modEq_iff_dvd.mpr ⟨-(A' * k), by linarith [this]⟩)

/-- **Counting.**  For `c = g c'` with `0 < c'` and `r < c'`, the residue class
`r` modulo `c'` meets `{0, …, c − 1}` in exactly `g` points.  Together with
`linearCongruence_solution_class` this is the classical statement that a
solvable congruence `A x ≡ B (mod c)` has exactly `g = gcd(A,c)` solutions
modulo `c`. -/
theorem card_residue_class_range (g c' r : ℕ) (hc' : 0 < c') (hr : r < c') :
    ((Finset.range (g * c')).filter (fun x => x % c' = r)).card = g := by
  have hset : (Finset.range (g * c')).filter (fun x => x % c' = r)
      = (Finset.range g).image (fun j => r + j * c') := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hx, hmod⟩
      refine ⟨x / c', ?_, ?_⟩
      · by_contra hcon
        push_neg at hcon
        have : g * c' ≤ (x / c') * c' := Nat.mul_le_mul_right c' hcon
        have hxx : (x / c') * c' ≤ x := Nat.div_mul_le_self x c'
        omega
      · have hdm := Nat.div_add_mod x c'
        rw [hmod] at hdm
        rw [Nat.mul_comm]
        omega
    · rintro ⟨j, hj, rfl⟩
      constructor
      · have : j + 1 ≤ g := hj
        have : (j + 1) * c' ≤ g * c' := Nat.mul_le_mul_right c' this
        nlinarith
      · simp [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]
  have hinj : Function.Injective (fun j => r + j * c') := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_right hc' (Nat.add_left_cancel hab)
  rw [hset, Finset.card_image_of_injective _ hinj, Finset.card_range]

end Gate01Consolidation
end TwinPrimeProject
