/-
# Gate 1B safe algebra bank — §3: on-shell multiplicative character saturation.

`χ` here is an arbitrary monoid homomorphism from the unit group `(ZMod n)ˣ`
into an arbitrary commutative group `G`.  Nothing analytic is assumed about it:
in particular no Dirichlet-character orthogonality, no conductor theory, no
large sieve.

The content is the *anti-loop certificate*: on the shell, the character value at
`q` is **identical** to the character value at `ℓ⁻¹(2 + r t v)`, at every tensor
power and for arbitrary integer exponents.  Consequently no amount of iterating
the character identity can produce new information — which is exactly what a
looping argument would silently assume.
-/
import Gate1B.Shell

namespace Gate1B

open Finset

/-! ## §3 (SAT1): the one-factor certificate -/

/-- **(SAT1)** If `q` and `a` are units of `ZMod n` with the *same* underlying
ring element, then for every homomorphism `χ` into a commutative group,
`χ(q) · χ(a)⁻¹ = 1`. -/
theorem on_shell_character_saturation {n : ℕ} {G : Type*} [CommGroup G]
    (chi : (ZMod n)ˣ →* G) (qu au : (ZMod n)ˣ)
    (h : ((qu : ZMod n)) = ((au : ZMod n))) :
    chi qu * (chi au)⁻¹ = 1 := by
  have hu : qu = au := Units.ext h
  simp [hu]

/-- **(SAT1) on the shell.**  Given the integer shell `q ℓ = t r v + 2`, unit
representatives `qu` for `q`, `lu` for `ℓ` and `au` for `2 + r t v`, the
character of `q` and the character of `ℓ⁻¹(2 + r t v)` coincide. -/
theorem shell_character_saturation {n : ℕ} {G : Type*} [CommGroup G]
    (chi : (ZMod n)ˣ →* G) {q l t r v : ℤ} (h : q * l = t * r * v + 2)
    (qu lu au : (ZMod n)ˣ)
    (hq : ((qu : ZMod n)) = (q : ZMod n))
    (hl : ((lu : ZMod n)) = (l : ZMod n))
    (ha : ((au : ZMod n)) = (2 + (r : ZMod n) * (t : ZMod n) * (v : ZMod n))) :
    chi qu * (chi (lu⁻¹ * au))⁻¹ = 1 := by
  refine on_shell_character_saturation chi qu (lu⁻¹ * au) ?_
  rw [hq, Units.val_mul, ha]
  exact shell_unit_form h lu hl

/-! ## §3 (SAT-k): the tensor-power certificate -/

/-- **(SAT-k)** On-shell multiplicative character saturation holds at every
tensor power: for a finite index set `s`, arbitrary moduli `n j`, arbitrary
homomorphisms `χ j` into a common commutative group and arbitrary **integer**
exponents `ε j` (in particular arbitrary signs `±1`), the product of the
saturated factors is `1`. -/
theorem on_shell_character_saturation_tensor {ι : Type*} (s : Finset ι)
    {G : Type*} [CommGroup G] {n : ι → ℕ} (chi : ∀ j, (ZMod (n j))ˣ →* G)
    (qu au : ∀ j, (ZMod (n j))ˣ) (eps : ι → ℤ)
    (h : ∀ j ∈ s, ((qu j : ZMod (n j))) = ((au j : ZMod (n j)))) :
    ∏ j ∈ s, (chi j (qu j) * (chi j (au j))⁻¹) ^ (eps j) = 1 := by
  refine Finset.prod_eq_one ?_
  intro j hj
  rw [on_shell_character_saturation (chi j) (qu j) (au j) (h j hj), one_zpow]

/-- Sign version of `SAT-k`: exponents `ε j ∈ {-1, +1}`. -/
theorem on_shell_character_saturation_signs {ι : Type*} (s : Finset ι)
    {G : Type*} [CommGroup G] {n : ι → ℕ} (chi : ∀ j, (ZMod (n j))ˣ →* G)
    (qu au : ∀ j, (ZMod (n j))ˣ) (eps : ι → ℤ) (heps : ∀ j ∈ s, eps j = 1 ∨ eps j = -1)
    (h : ∀ j ∈ s, ((qu j : ZMod (n j))) = ((au j : ZMod (n j)))) :
    ∏ j ∈ s, (chi j (qu j) * (chi j (au j))⁻¹) ^ (eps j) = 1 := by
  have := heps
  exact on_shell_character_saturation_tensor s chi qu au eps h

/-- **(SAT-k) on the shell.**  Every factor is produced from its own integer
shell equation `q j * ℓ j = t j * r j * v j + 2`. -/
theorem shell_character_saturation_tensor {ι : Type*} (s : Finset ι)
    {G : Type*} [CommGroup G] {n : ι → ℕ} (chi : ∀ j, (ZMod (n j))ˣ →* G)
    (q l t r v : ι → ℤ) (qu lu au : ∀ j, (ZMod (n j))ˣ) (eps : ι → ℤ)
    (hshell : ∀ j ∈ s, q j * l j = t j * r j * v j + 2)
    (hq : ∀ j ∈ s, ((qu j : ZMod (n j))) = ((q j : ZMod (n j))))
    (hl : ∀ j ∈ s, ((lu j : ZMod (n j))) = ((l j : ZMod (n j))))
    (ha : ∀ j ∈ s, ((au j : ZMod (n j)))
      = (2 + ((r j : ℤ) : ZMod (n j)) * ((t j : ℤ) : ZMod (n j)) * ((v j : ℤ) : ZMod (n j)))) :
    ∏ j ∈ s, (chi j (qu j) * (chi j ((lu j)⁻¹ * au j))⁻¹) ^ (eps j) = 1 := by
  refine Finset.prod_eq_one ?_
  intro j hj
  rw [shell_character_saturation (chi j) (hshell j hj) (qu j) (lu j) (au j)
    (hq j hj) (hl j hj) (ha j hj), one_zpow]

/-! ## Guard: saturation is a tautology, not a cancellation statement -/

/-- Anti-loop guard.  `SAT1` says the two character values are *equal*; it says
nothing about their common value being trivial.  Concretely there are data with
`χ(q) ≠ 1`, so no saving may ever be extracted from saturation alone. -/
theorem saturation_gives_no_value_information :
    ∃ (qu : (ZMod 5)ˣ), (MonoidHom.id (ZMod 5)ˣ) qu ≠ 1 := by
  refine ⟨(ZMod.unitOfCoprime 2 (by decide)), ?_⟩
  decide

end Gate1B
