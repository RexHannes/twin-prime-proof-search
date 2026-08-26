/-
# Gate 1B v8.2 — exact Kloosterman square mass

For an explicitly supplied additive character system modulo `q`, the total
square mass of the Kloosterman family in the first argument is *exactly*

    ∑_{A ∈ ZMod q} |S(A,B)|² = q · #(ZMod q)ˣ.

This is pure orthogonality: **no Weil bound and no individual bound on
`S(A,B)` is claimed or used.**  Note also that the hypothesis "`B` is a unit"
is *not* needed for the identity, and is therefore deliberately absent.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteKloosterman

namespace Gate1B.SafeAlgebra

open Finset

namespace AdditiveCharacterSystem

variable {q : ℕ} [NeZero q] (C : AdditiveCharacterSystem q)

/-- **Exact square mass of the Kloosterman family**, for every `B` (unit or
not). -/
theorem kloosterman_squareMass (B : ZMod q) :
    ∑ A : ZMod q, C.kloosterman A B * (starRingEnd ℂ) (C.kloosterman A B)
      = (q : ℂ) * (Fintype.card (ZMod q)ˣ) := by
  classical
  have hstep : ∀ (u v : (ZMod q)ˣ) (A : ZMod q),
      C.chi (A * (u : ZMod q) + B * ((u⁻¹ : (ZMod q)ˣ) : ZMod q)) *
          (starRingEnd ℂ) (C.chi (A * (v : ZMod q) + B * ((v⁻¹ : (ZMod q)ˣ) : ZMod q)))
        = C.chi (A * ((u : ZMod q) - (v : ZMod q))) *
            C.chi (B * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) - ((v⁻¹ : (ZMod q)ˣ) : ZMod q))) := by
    intro u v A
    rw [C.conj_eq, ← C.add, ← C.add]
    congr 1
    ring
  have h1 : ∀ A : ZMod q, C.kloosterman A B * (starRingEnd ℂ) (C.kloosterman A B)
      = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          C.chi (A * ((u : ZMod q) - v)) *
            C.chi (B * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) - ((v⁻¹ : (ZMod q)ˣ) : ZMod q))) := by
    intro A
    unfold kloosterman
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => hstep u v A
  calc ∑ A : ZMod q, C.kloosterman A B * (starRingEnd ℂ) (C.kloosterman A B)
      = ∑ A : ZMod q, ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          C.chi (A * ((u : ZMod q) - v)) *
            C.chi (B * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) - ((v⁻¹ : (ZMod q)ˣ) : ZMod q))) :=
        Finset.sum_congr rfl fun A _ => h1 A
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          C.chi (B * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) - ((v⁻¹ : (ZMod q)ˣ) : ZMod q))) *
            ∑ A : ZMod q, C.chi (A * ((u : ZMod q) - v)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun u _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun A _ => by ring
    _ = ∑ u : (ZMod q)ˣ, ∑ v : (ZMod q)ˣ,
          C.chi (B * (((u⁻¹ : (ZMod q)ˣ) : ZMod q) - ((v⁻¹ : (ZMod q)ˣ) : ZMod q))) *
            (if (u : ZMod q) - (v : ZMod q) = 0 then (q : ℂ) else 0) :=
        Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => by
          rw [C.orthogonality]
    _ = (q : ℂ) * (Fintype.card (ZMod q)ˣ) := by
        have hcoe : ∀ u v : (ZMod q)ˣ, ((u : ZMod q) - (v : ZMod q) = 0) ↔ u = v := by
          intro u v
          rw [sub_eq_zero]
          exact ⟨fun h => Units.ext h, fun h => by rw [h]⟩
        simp only [hcoe]
        simp [C.chi_zero, mul_comm]

/-- Real form of the exact square mass. -/
theorem kloosterman_squareMass_real (B : ZMod q) :
    ∑ A : ZMod q, ‖C.kloosterman A B‖ ^ 2 = (q : ℝ) * (Fintype.card (ZMod q)ˣ) := by
  have h := C.kloosterman_squareMass B
  have hre : ∀ A : ZMod q,
      (‖C.kloosterman A B‖ ^ 2 : ℂ)
        = C.kloosterman A B * (starRingEnd ℂ) (C.kloosterman A B) := by
    intro A
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self]
    simp [Complex.normSq_eq_norm_sq]
  have : ((∑ A : ZMod q, ‖C.kloosterman A B‖ ^ 2 : ℝ) : ℂ)
      = ((q : ℝ) * (Fintype.card (ZMod q)ˣ) : ℝ) := by
    push_cast
    rw [← h]
    exact Finset.sum_congr rfl fun A _ => hre A
  exact_mod_cast this

end AdditiveCharacterSystem

end Gate1B.SafeAlgebra
