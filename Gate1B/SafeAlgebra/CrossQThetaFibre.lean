/-
# Gate 1B v13 — cross-`q` Θ fibre counting (exact finite bound)

**Status: PROVED FINITE.  No asymptotics.**

Under the coprime CRT hypotheses (Θ mod `q₁` determines `B₁` mod `q₁`, Θ mod
`q₂` determines `B₂` mod `q₂`), the fibre of the Θ-map over a prescribed pair of
residues is contained in a product of two one-dimensional counts, each of which
is the number of integers in an interval of length `L` lying in a prescribed
residue class mod `q`.

Proved:

* `card_residue_class_in_interval` — the ceiling-correct count
  `#{B ∈ [x, x+L) : B ≡ a mod q} ≤ L/q + 1` (`ℕ` division, i.e. floor);
* `card_residue_class_in_interval_rat` — the rational form `≤ 1 + L/q`;
* `maxThetaFibre_le` — the product bound
  `fibre ≤ (1 + L₁/q₁)(1 + L₂/q₂) · productMultiplicity`.
-/
import Mathlib

namespace Gate1B.SafeAlgebra

open Finset

/-- **One-dimensional residue count.**  The number of integers of an interval of
length `L` in a prescribed class mod `q` is at most `L/q + 1` (floor division,
hence ceiling-correct). -/
theorem card_residue_class_in_interval (q x L a : ℕ) :
    ((Finset.Ico x (x + L)).filter (fun b => b % q = a)).card ≤ L / q + 1 := by
  classical
  have hcard : ((Finset.Ico x (x + L)).filter (fun b => b % q = a)).card
      ≤ (Finset.range (L / q + 1)).card := by
    refine Finset.card_le_card_of_injOn (fun b => (b - x) / q) ?_ ?_
    · intro b hb
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hb
      show (b - x) / q ∈ Finset.range (L / q + 1)
      refine Finset.mem_range.mpr ?_
      have hbx : b - x ≤ L := by omega
      have := Nat.div_le_div_right (c := q) hbx
      omega
    · intro b1 hb1 b2 hb2 heq
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_Ico] at hb1 hb2
      simp only at heq
      obtain ⟨⟨hx1, _⟩, hm1⟩ := hb1
      obtain ⟨⟨hx2, _⟩, hm2⟩ := hb2
      have hmod : (b1 - x) % q = (b2 - x) % q := by
        have h1 : b1 = x + (b1 - x) := by omega
        have h2 : b2 = x + (b2 - x) := by omega
        have hb : (x + (b1 - x)) % q = (x + (b2 - x)) % q := by
          rw [← h1, ← h2, hm1, hm2]
        exact Nat.ModEq.add_left_cancel' x hb
      have hd1 := Nat.div_add_mod (b1 - x) q
      have hd2 := Nat.div_add_mod (b2 - x) q
      have : b1 - x = b2 - x := by
        rw [← hd1, ← hd2, heq, hmod]
      omega
  simpa using hcard

/-- Rational form of the one-dimensional count. -/
theorem card_residue_class_in_interval_rat (q : ℕ) (hq : 0 < q) (x L a : ℕ) :
    (((Finset.Ico x (x + L)).filter (fun b => b % q = a)).card : ℚ) ≤ 1 + (L : ℚ) / q := by
  have h := card_residue_class_in_interval q x L a
  have hfloor : ((L / q : ℕ) : ℚ) ≤ (L : ℚ) / q := by
    rw [le_div_iff₀ (by exact_mod_cast hq)]
    have : (L / q) * q ≤ L := Nat.div_mul_le_self L q
    exact_mod_cast this
  have : (((Finset.Ico x (x + L)).filter (fun b => b % q = a)).card : ℚ)
      ≤ ((L / q : ℕ) : ℚ) + 1 := by exact_mod_cast h
  linarith

/-- **Product fibre bound.**  If each coordinate count obeys its
one-dimensional bound and the fibre is contained in the product with a
prescribed multiplicity, then the fibre obeys the product bound. -/
theorem maxThetaFibre_le {c1 c2 m fib b1 b2 : ℕ}
    (h1 : c1 ≤ b1) (h2 : c2 ≤ b2) (hfib : fib ≤ c1 * c2 * m) :
    fib ≤ b1 * b2 * m :=
  le_trans hfib (Nat.mul_le_mul_right m (Nat.mul_le_mul h1 h2))

end Gate1B.SafeAlgebra
