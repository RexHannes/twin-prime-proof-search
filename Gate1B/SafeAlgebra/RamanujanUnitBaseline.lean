/-
# Gate 1B v8.2 — Ramanujan expansion of the unit indicator

**Tier 2 (hypothesis-carrying).**  Relative to an explicitly supplied additive
character system modulo `q`, the Ramanujan sums `c_q(a) = ∑_{u ∈ (ZMod q)ˣ}
χ(ua)` satisfy the exact Fourier identity

    ∑_{a ∈ ZMod q} c_q(-a) χ(an) = q · 1_{n is a unit},

whose zero-mode split is the standard baseline

    1_{unit}(n) / φ(q) = 1/q + (1/(q φ(q))) ∑_{a ≠ 0} c_q(-a) χ(an).

This is exact finite Fourier analysis: no bound on any Ramanujan sum is claimed
and no analytic input is used.
-/
import Mathlib
import Gate1B.SafeAlgebra.FiniteKloosterman

namespace Gate1B.SafeAlgebra

open Finset

namespace AdditiveCharacterSystem

variable {q : ℕ} [NeZero q] (C : AdditiveCharacterSystem q)

/-- The Ramanujan sum `c_q(a) = ∑_{u ∈ (ZMod q)ˣ} χ(ua)`. -/
noncomputable def ramanujan (a : ZMod q) : ℂ := ∑ u : (ZMod q)ˣ, C.chi ((u : ZMod q) * a)

/-- `c_q(0) = φ(q)`. -/
theorem ramanujan_zero : C.ramanujan 0 = (Fintype.card (ZMod q)ˣ : ℂ) := by
  simp [ramanujan, C.chi_zero]

/-- **Exact Ramanujan–Fourier identity for the unit indicator.** -/
theorem ramanujan_fourier (n : ZMod q) :
    ∑ a : ZMod q, C.ramanujan (-a) * C.chi (a * n)
      = (q : ℂ) * (if IsUnit n then 1 else 0) := by
  classical
  have h1 : ∀ a : ZMod q, C.ramanujan (-a) * C.chi (a * n)
      = ∑ u : (ZMod q)ˣ, C.chi (a * (n - (u : ZMod q))) := by
    intro a
    rw [ramanujan, Finset.sum_mul]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← C.add]
    congr 1
    ring
  calc ∑ a : ZMod q, C.ramanujan (-a) * C.chi (a * n)
      = ∑ a : ZMod q, ∑ u : (ZMod q)ˣ, C.chi (a * (n - (u : ZMod q))) :=
        Finset.sum_congr rfl fun a _ => h1 a
    _ = ∑ u : (ZMod q)ˣ, ∑ a : ZMod q, C.chi (a * (n - (u : ZMod q))) := Finset.sum_comm
    _ = ∑ u : (ZMod q)ˣ, (if n - (u : ZMod q) = 0 then (q : ℂ) else 0) :=
        Finset.sum_congr rfl fun u _ => C.orthogonality _
    _ = (q : ℂ) * (if IsUnit n then 1 else 0) := by
        by_cases hn : IsUnit n
        · obtain ⟨v, rfl⟩ := hn
          rw [if_pos ⟨v, rfl⟩, Finset.sum_eq_single v]
          · simp
          · intro b _ hb
            rw [if_neg]
            intro h
            exact hb (Units.ext (by linear_combination -h))
          · intro h
            exact absurd (Finset.mem_univ v) h
        · rw [if_neg hn]
          refine (Finset.sum_eq_zero fun u _ => ?_).trans (by ring)
          rw [if_neg]
          intro h
          exact hn ⟨u, by linear_combination -h⟩

/-- **The unit baseline.**  Splitting off the zero mode of the Ramanujan–Fourier
identity gives the `1/q` baseline plus the nonzero-frequency correction. -/
theorem unit_indicator_baseline (n : ZMod q)
    (hphi : (Fintype.card (ZMod q)ˣ : ℂ) ≠ 0) :
    (if IsUnit n then (1 : ℂ) else 0) / (Fintype.card (ZMod q)ˣ)
      = 1 / q + (1 / ((q : ℂ) * (Fintype.card (ZMod q)ˣ))) *
          ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0, C.ramanujan (-a) * C.chi (a * n) := by
  classical
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast (NeZero.ne q)
  have hsplit : ∑ a : ZMod q, C.ramanujan (-a) * C.chi (a * n)
      = (Fintype.card (ZMod q)ˣ : ℂ)
        + ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0, C.ramanujan (-a) * C.chi (a * n) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (0 : ZMod q))]
    simp [C.ramanujan_zero, C.chi_zero]
  have hmain := C.ramanujan_fourier n
  rw [hsplit] at hmain
  have hind : (if IsUnit n then (1 : ℂ) else 0)
      = ((Fintype.card (ZMod q)ˣ : ℂ)
          + ∑ a ∈ (Finset.univ : Finset (ZMod q)).erase 0,
              C.ramanujan (-a) * C.chi (a * n)) / q := by
    rw [hmain]; field_simp
  rw [hind]
  field_simp

end AdditiveCharacterSystem

end Gate1B.SafeAlgebra
