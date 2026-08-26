import RequestProject.NANC.HFMVGate1B.HFMVDeterminant

/-!
# HFMV Gate 1B, Module 3: the exact tuple diagonal

The `v₁ = v₂` diagonal of the HFMV determinant configuration is an *exact
finite identity*: for incidences sharing the same `u`,

  `v₁ = v₂  →  d₁ p₁ l₁ = d₂ p₂ l₂`,

and (for `u ≠ 0`) conversely.  The diagonal pair set therefore splits exactly
into the squares of the `v`-fibres.

**No analytic negligibility is asserted here.**  The only upper bound proved is
conditional on an explicitly supplied divisor-counting hypothesis
(`FiberDivisorBound`), and `diagonalPairs_card_eq_sq_of_constant_v` records
that without such an input the diagonal is as large as `|T|²`.
-/

namespace TwinPrimeProject
namespace HFMVGate1B

open Finset

/-! ## 1. The diagonal identity -/

/-- A configuration tuple `(v, d, p, l)`. -/
abbrev Tuple := ℤ × ℤ × ℤ × ℤ

/-- The `v`-coordinate of a tuple. -/
def vOf (t : Tuple) : ℤ := t.1

/-- The product `d p l` of a tuple. -/
def prodOf (t : Tuple) : ℤ := t.2.1 * t.2.2.1 * t.2.2.2

/-- The tuple is incident to `u`: `u v + 2 = d p l`. -/
def IncidentTuple (u : ℤ) (t : Tuple) : Prop :=
  Incidence u t.1 t.2.1 t.2.2.1 t.2.2.2

/-- **Diagonal identity.**  Equal `v` forces equal `d p l`. -/
theorem diagonal_prod_eq {u : ℤ} {t₁ t₂ : Tuple}
    (h₁ : IncidentTuple u t₁) (h₂ : IncidentTuple u t₂) (hv : vOf t₁ = vOf t₂) :
    prodOf t₁ = prodOf t₂ := by
  unfold IncidentTuple Incidence at h₁ h₂
  unfold prodOf
  unfold vOf at hv
  rw [← h₁, ← h₂, hv]

/-- Explicit variable form of the diagonal identity. -/
theorem diagonal_prod_eq' {u v₁ v₂ d₁ p₁ l₁ d₂ p₂ l₂ : ℤ}
    (h₁ : Incidence u v₁ d₁ p₁ l₁) (h₂ : Incidence u v₂ d₂ p₂ l₂) (hv : v₁ = v₂) :
    d₁ * p₁ * l₁ = d₂ * p₂ * l₂ := by
  unfold Incidence at h₁ h₂
  rw [← h₁, ← h₂, hv]

/-- **Converse of the diagonal identity** for `u ≠ 0`: equal products force
equal `v`. -/
theorem diagonal_v_eq {u : ℤ} (hu : u ≠ 0) {t₁ t₂ : Tuple}
    (h₁ : IncidentTuple u t₁) (h₂ : IncidentTuple u t₂) (hK : prodOf t₁ = prodOf t₂) :
    vOf t₁ = vOf t₂ := by
  unfold IncidentTuple Incidence at h₁ h₂
  unfold prodOf at hK
  unfold vOf
  have : u * t₁.1 = u * t₂.1 := by rw [← hK] at h₂; linarith
  exact mul_left_cancel₀ hu this

/-! ## 2. The exact finite diagonal decomposition -/

/-- Pairs of tuples on the `v`-diagonal. -/
def diagonalPairs (T : Finset Tuple) : Finset (Tuple × Tuple) :=
  (T ×ˢ T).filter (fun x => vOf x.1 = vOf x.2)

/-- Pairs of tuples with equal product `d p l`. -/
def prodPairs (T : Finset Tuple) : Finset (Tuple × Tuple) :=
  (T ×ˢ T).filter (fun x => prodOf x.1 = prodOf x.2)

/-- **Exact identification of the two diagonals** for a family of tuples all
incident to a common nonzero `u`. -/
theorem diagonalPairs_eq_prodPairs {u : ℤ} (hu : u ≠ 0) {T : Finset Tuple}
    (hT : ∀ t ∈ T, IncidentTuple u t) : diagonalPairs T = prodPairs T := by
  ext x
  simp only [diagonalPairs, prodPairs, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨hx1, hx2⟩, hv⟩
    exact ⟨⟨hx1, hx2⟩, diagonal_prod_eq (hT _ hx1) (hT _ hx2) hv⟩
  · rintro ⟨⟨hx1, hx2⟩, hK⟩
    exact ⟨⟨hx1, hx2⟩, diagonal_v_eq hu (hT _ hx1) (hT _ hx2) hK⟩

/-- The `v`-fibre of a tuple family. -/
def vFiber (T : Finset Tuple) (v : ℤ) : Finset Tuple := T.filter (fun t => vOf t = v)

/-- The diagonal pair set is exactly the disjoint union of the fibre squares. -/
theorem diagonalPairs_fiber (T : Finset Tuple) (v : ℤ) :
    (diagonalPairs T).filter (fun x => vOf x.1 = v) = vFiber T v ×ˢ vFiber T v := by
  ext x
  simp only [diagonalPairs, vFiber, mem_filter, mem_product]
  constructor
  · rintro ⟨⟨⟨hx1, hx2⟩, hv⟩, hv1⟩
    exact ⟨⟨hx1, hv1⟩, hx2, by rw [← hv, hv1]⟩
  · rintro ⟨⟨hx1, hv1⟩, hx2, hv2⟩
    exact ⟨⟨⟨hx1, hx2⟩, by rw [hv1, hv2]⟩, hv1⟩

/-- **Exact tuple-diagonal decomposition (finite identity).**  The number of
diagonal pairs is the sum of the squares of the `v`-fibre sizes. -/
theorem diagonalPairs_card (T : Finset Tuple) :
    (diagonalPairs T).card = ∑ v ∈ T.image vOf, (vFiber T v).card ^ 2 := by
  have hmap : ∀ x ∈ diagonalPairs T, vOf x.1 ∈ T.image vOf := by
    intro x hx
    simp only [diagonalPairs, mem_filter, mem_product] at hx
    exact mem_image_of_mem vOf hx.1.1
  rw [card_eq_sum_card_fiberwise hmap]
  refine sum_congr rfl fun v _ => ?_
  rw [diagonalPairs_fiber T v, card_product, sq]

/-! ## 3. Conditional bound — analytic negligibility is NOT asserted -/

/-- **Supplied divisor-counting hypothesis.**  Every `v`-fibre has at most `D`
tuples.  This is an *input*: it is never proved here. -/
def FiberDivisorBound (T : Finset Tuple) (D : ℕ) : Prop :=
  ∀ v : ℤ, (vFiber T v).card ≤ D

/-- Under the supplied fibre bound, the diagonal has at most `D |T|` pairs. -/
theorem diagonalPairs_card_le {T : Finset Tuple} {D : ℕ} (h : FiberDivisorBound T D) :
    (diagonalPairs T).card ≤ D * T.card := by
  have hfib : T.card = ∑ v ∈ T.image vOf, (vFiber T v).card :=
    card_eq_sum_card_fiberwise (fun t ht => mem_image_of_mem vOf ht)
  rw [diagonalPairs_card, hfib, mul_sum]
  refine sum_le_sum fun v _ => ?_
  rw [sq]
  exact Nat.mul_le_mul_right _ (h v)

/-- **Guard against a silent upgrade.**  With no fibre input the diagonal is as
large as `|T|²`: for every `n` there is a family of `n` tuples all of whose
pairs are diagonal. -/
theorem diagonalPairs_card_eq_sq_of_constant_v (n : ℕ) :
    ∃ T : Finset Tuple, T.card = n ∧ (diagonalPairs T).card = n ^ 2 := by
  classical
  set f : ℕ → Tuple := fun k => ((1 : ℤ), (1 : ℤ), (1 : ℤ), (k : ℤ)) with hf
  have hinj : Function.Injective f := by
    intro a b hab
    simpa [hf] using hab
  refine ⟨(Finset.range n).image f, ?_, ?_⟩
  · rw [card_image_of_injective _ hinj, card_range]
  · have hall : diagonalPairs ((Finset.range n).image f)
        = ((Finset.range n).image f) ×ˢ ((Finset.range n).image f) := by
      ext x
      simp only [diagonalPairs, mem_filter, mem_product, and_iff_left_iff_imp]
      rintro ⟨hx1, hx2⟩
      simp only [mem_image] at hx1 hx2
      obtain ⟨a, _, ha⟩ := hx1
      obtain ⟨b, _, hb⟩ := hx2
      rw [← ha, ← hb]
      rfl
    rw [hall, card_product, card_image_of_injective _ hinj, card_range, sq]

end HFMVGate1B
end TwinPrimeProject
