import Mathlib
import RequestProject.PrimitiveLattice

/-!
# Primitive lattice solvability and progression (§6)

For fixed `a₁, a₂` the inner equation `D₁a₁b₁ − D₂a₂b₂ = h₀` reduces to the
linear congruence `(D₁a₁)·b₁ ≡ h₀ (mod D₂a₂)`.  We formalize:

* `PRIMITIVE_LATTICE_SOLVABILITY`: solvability criterion `g ∣ h₀`,
  `g = gcd(D₁a₁, D₂a₂)`.
* `PRIMITIVE_B1_PROGRESSION`: the solution set for `b₁` is a residue class
  modulo `c₁ = D₂a₂/g` with representative `β ≡ (h₀/g)·overline{D₁a₁/g}`.
* `PRIMITIVE_B2_RECONSTRUCTION`: reconstruction of `b₂`, kept separate from
  modular solvability.

Status: `LEAN_PROVED` (arithmetic core).
-/

namespace Banking.PrimitiveProgression

open Int

/-- The linear congruence coming from the inner equation.  From
`A·b₁ − C·b₂ = h₀` we get `A·b₁ ≡ h₀ (mod C)`; conversely every solution of
the congruence lifts to some integer `b₂`. -/
theorem congruence_of_inner (A C h₀ b₁ b₂ : ℤ) (h : A * b₁ - C * b₂ = h₀) :
    A * b₁ ≡ h₀ [ZMOD C] :=
  Int.modEq_iff_dvd.mpr ⟨-b₂, by linear_combination -h⟩

theorem inner_of_congruence (A C h₀ b₁ : ℤ) (h : A * b₁ ≡ h₀ [ZMOD C]) :
    ∃ b₂ : ℤ, A * b₁ - C * b₂ = h₀ := by
  obtain ⟨k, hk⟩ := Int.modEq_iff_dvd.mp h
  exact ⟨-k, by linear_combination -hk⟩

/-- `PRIMITIVE_LATTICE_SOLVABILITY` (§6).

The congruence `A·b₁ ≡ h₀ (mod C)` is solvable in `b₁` iff `g ∣ h₀`, where
`g = gcd(A, C)`. -/
theorem primitive_lattice_solvability (A C h₀ : ℤ) :
    (∃ b₁ : ℤ, A * b₁ ≡ h₀ [ZMOD C]) ↔ ((Int.gcd A C : ℤ) ∣ h₀) := by
  constructor
  · rintro ⟨b₁, hb⟩
    rw [Int.modEq_iff_dvd] at hb
    obtain ⟨k, hk⟩ := hb
    have : h₀ = A * b₁ + C * k := by linarith [hk]
    rw [this]
    exact dvd_add ((Int.gcd_dvd_left A C).mul_right b₁)
      ((Int.gcd_dvd_right A C).mul_right k)
  · intro hg
    obtain ⟨c, hc⟩ := hg
    refine ⟨(A.gcdA C) * c, ?_⟩
    rw [Int.modEq_iff_dvd]
    have hbez : (Int.gcd A C : ℤ) = A * A.gcdA C + C * A.gcdB C := Int.gcd_eq_gcd_ab A C
    exact ⟨A.gcdB C * c, by rw [hc, hbez]; ring⟩

/-- Reduction to the coprime core: with `A = g·A'`, `C = g·C'`, `h₀ = g·h'`
and `g ≠ 0`, the congruence modulo `C` is equivalent to the reduced congruence
modulo `C'`. -/
theorem congruence_reduce (g A' C' h' b₁ : ℤ) (hg : g ≠ 0) :
    ((g * A') * b₁ ≡ (g * h') [ZMOD (g * C')]) ↔ (A' * b₁ ≡ h' [ZMOD C']) := by
  rw [Int.modEq_iff_dvd, Int.modEq_iff_dvd]
  have : g * h' - g * A' * b₁ = g * (h' - A' * b₁) := by ring
  rw [this]
  exact mul_dvd_mul_iff_left hg

/-- `PRIMITIVE_B1_PROGRESSION` (§6).

Coprime core.  With `A'·u ≡ 1 (mod C')` (so `u = overline{A'}`), the reduced
congruence `A'·b₁ ≡ h' (mod C')` holds iff `b₁ ≡ h'·u (mod C')`.  The residue
`β := h'·u` is exactly the reported progression representative and the modulus
is `c₁ = C' = D₂a₂/g`. -/
theorem primitive_b1_progression (A' C' h' u b₁ : ℤ)
    (hu : A' * u ≡ 1 [ZMOD C']) :
    (A' * b₁ ≡ h' [ZMOD C']) ↔ (b₁ ≡ h' * u [ZMOD C']) := by
  constructor
  · intro h
    calc b₁ ≡ (A' * u) * b₁ [ZMOD C'] := by
              have := hu.mul_right b₁; simpa using this.symm
      _ = (A' * b₁) * u := by ring
      _ ≡ h' * u [ZMOD C'] := h.mul_right u
  · intro h
    calc A' * b₁ ≡ A' * (h' * u) [ZMOD C'] := h.mul_left A'
      _ = h' * (A' * u) := by ring
      _ ≡ h' * 1 [ZMOD C'] := hu.mul_left h'
      _ = h' := by ring

/-- The progression representative `β` (§6). -/
def beta (h' u : ℤ) : ℤ := h' * u

/-- `PRIMITIVE_B2_RECONSTRUCTION` (§6).

Given a solution `b₁` (i.e. the congruence holds so `C ∣ A·b₁ − h₀`), `b₂` is
reconstructed exactly by `C·b₂ = A·b₁ − h₀`, i.e. `b₂ = (D₁a₁b₁ − h₀)/(D₂a₂)`.
This is the positivity/integrality half, kept separate from solvability. -/
theorem primitive_b2_reconstruction (A C h₀ b₁ b₂ : ℤ)
    (h : A * b₁ - C * b₂ = h₀) : C * b₂ = A * b₁ - h₀ := by
  linarith [h]

theorem primitive_b2_div (A C h₀ b₁ b₂ : ℤ) (hC : C ≠ 0)
    (h : A * b₁ - C * b₂ = h₀) : b₂ = (A * b₁ - h₀) / C := by
  have hb : C * b₂ = A * b₁ - h₀ := by linarith [h]
  rw [← hb]
  exact (Int.mul_ediv_cancel_left b₂ hC).symm

end Banking.PrimitiveProgression
