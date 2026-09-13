/-
# Gate1B / R11 / Frontier : the critical-mask firewall

Two orthogonality firewalls, both kernel-proved in a finite setting.

1. **Character mask.**  The *full* sum over all additive characters of `ZMod q` produces the
   standard congruence indicator,
   `q⁻¹ ∑_{t : ZMod q} e_q(t (n − a)) = 1_{n ≡ a}`.
   An *arbitrary proper mask* `S ⊊ ZMod q` does **not**: an explicit finite counterexample is
   given, for which the masked average is `1/2` at every point.

2. **Fourier mask.**  A masked frequency sum is not a point mass: for a proper mask there are
   nonzero `x` at which `∑_{t ∈ S} e_q(t x) ≠ 0`.

An abstract version of the positive half is also recorded: from an orthogonality hypothesis for a
finite family of characters one gets the indicator; the hypothesis is exactly what a critical mask
destroys.

No analytic statement is made, and no universal impossibility theorem is asserted: the firewall
says only that masked orthogonality must be *proved*, never assumed.
-/
import Gate1B.HilbertHMRD.Fourier

namespace Gate1B.R11.Frontier

open Finset Gate1B.HilbertHMRD Universal.D0WP

noncomputable section

/-! ## 1. Full orthogonality gives the congruence indicator -/

variable {q : ℕ} [NeZero q]

/-- The masked character sum over a frequency mask `S`. -/
def maskedSum (q : ℕ) (S : Finset (ZMod q)) (x : ZMod q) : ℂ := ∑ t ∈ S, ez q (t * x)

/-- **FULL ORTHOGONALITY.**  The complete character sum is `q` times the point mass at `0`. -/
theorem maskedSum_univ (x : ZMod q) :
    maskedSum q Finset.univ x = if x = 0 then (q : ℂ) else 0 := by
  rw [maskedSum]
  rw [show ∑ t : ZMod q, ez q (t * x) = ∑ t : ZMod q, ez q (x * t) from
    Finset.sum_congr rfl fun t _ => by rw [mul_comm]]
  exact sum_ez_orth x

/-- **THE STANDARD CONGRUENCE INDICATOR.**  Normalised, the full sum detects `n ≡ a (mod q)`. -/
theorem full_character_sum_is_indicator (n a : ZMod q) :
    (q : ℂ)⁻¹ * maskedSum q Finset.univ (n - a) = if n = a then 1 else 0 := by
  have hq : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  rw [maskedSum_univ]
  by_cases h : n = a
  · subst h; simp [hq]
  · rw [if_neg (sub_ne_zero.2 h), if_neg h, mul_zero]

/-- Abstract form: any finite family of characters satisfying full orthogonality produces the
indicator. -/
theorem abstract_full_orthogonality {G : Type*} [Fintype G] [DecidableEq G] {K : Type*}
    [Fintype K] (chi : K → G → ℂ) (e : G) (c : ℂ) (hc : c ≠ 0)
    (horth : ∀ g : G, ∑ k : K, chi k g = if g = e then c else 0) (g : G) :
    c⁻¹ * ∑ k : K, chi k g = if g = e then 1 else 0 := by
  rw [horth g]
  by_cases h : g = e
  · simp [h, hc]
  · simp [h]

/-! ## 2. Firewall: a proper mask is not the indicator -/

/-- The masked average over the proper mask `{0} ⊊ ZMod 2` is constantly `1/2`. -/
theorem maskedSum_singleton_zero (x : ZMod 2) :
    (((2 : ℕ) : ℂ))⁻¹ * maskedSum 2 {0} x = 1 / 2 := by
  rw [maskedSum, Finset.sum_singleton, zero_mul, ez_zero]
  norm_num

/-- **CRITICAL MASK FIREWALL (characters).**  There is a proper character mask whose normalised
sum equals the congruence indicator at *no* point: masked orthogonality may never be assumed. -/
theorem proper_mask_not_congruence_indicator :
    ∃ (q : ℕ) (_ : NeZero q) (S : Finset (ZMod q)),
      S ⊂ Finset.univ ∧
      ∀ n a : ZMod q, (q : ℂ)⁻¹ * maskedSum q S (n - a) ≠ (if n = a then 1 else 0) := by
  refine ⟨2, inferInstance, {0}, ?_, ?_⟩
  · refine Finset.ssubset_univ_iff.2 ?_
    intro h
    have : (1 : ZMod 2) ∈ ({0} : Finset (ZMod 2)) := h ▸ Finset.mem_univ 1
    simp at this
  · intro n a
    rw [maskedSum_singleton_zero]
    by_cases h : n = a
    · rw [if_pos h]; norm_num
    · rw [if_neg h]; norm_num

/-- **FOURIER MASK FIREWALL.**  A masked frequency sum is not a point mass: for a proper mask
there is a nonzero `x` at which the masked sum does not vanish. -/
theorem masked_frequency_sum_not_point_mass :
    ∃ (q : ℕ) (_ : NeZero q) (S : Finset (ZMod q)) (x : ZMod q),
      S ⊂ Finset.univ ∧ x ≠ 0 ∧ maskedSum q S x ≠ 0 := by
  refine ⟨2, inferInstance, {0}, 1, ?_, by decide, ?_⟩
  · refine Finset.ssubset_univ_iff.2 ?_
    intro h
    have : (1 : ZMod 2) ∈ ({0} : Finset (ZMod 2)) := h ▸ Finset.mem_univ 1
    simp at this
  · rw [maskedSum, Finset.sum_singleton, zero_mul, ez_zero]
    exact one_ne_zero

/-- The positive half is exactly the *unmasked* statement: with the full mask the frequency sum
**is** a point mass. -/
theorem unmasked_frequency_sum_is_point_mass (x : ZMod q) (hx : x ≠ 0) :
    maskedSum q Finset.univ x = 0 := by
  rw [maskedSum_univ, if_neg hx]

end

end Gate1B.R11.Frontier
