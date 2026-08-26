import Mathlib

/-!
# Gate 1B / determinant-2 bank, optional Phase B: the finite Steinberg jet

An **explanatory, purely algebraic** finite two-state tensor model.  For each
prime index `p` there are two states `e0_p`, `e1_p`, and one forms the formal
product

  `∏_p (e0_p − z_p e1_p)`.

Expanding, the coefficient of the basis tensor labelled by the subset `T`
(the legs where `e1` is chosen) is `∏_{p ∈ T} (−z_p)`; this is `jetCoeff`.

Banked:

* `jetCoeff_one` — at `z ≡ 1` the coefficients are `(−1)^{|T|}`, i.e. the top
  alternating tensor;
* `jet_first_variation` — the algebraic first variation in one leg: perturbing
  `z_q` to `1 + h` changes the coefficient by `h` times the alternating
  coefficient exactly when `q ∈ T`;
* `jet_sum_first_variation` — summing over the differentiated leg gives
  `|T|` copies of the alternating coefficient ("one differentiated leg tensored
  with the remaining alternating legs").

**No representation theory, no Whittaker theory, and no analytic saving is
formalized.**
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Steinberg

open Finset

variable {ι : Type*} [DecidableEq ι] {R : Type*} [CommRing R]

/-- The coefficient of the basis tensor labelled by `T` in the formal product
`∏_p (e0_p − z_p e1_p)`. -/
def jetCoeff (z : ι → R) (T : Finset ι) : R := ∏ p ∈ T, (-(z p))

omit [DecidableEq ι] in
/-- **Top alternating tensor.**  At `z ≡ 1` the coefficients are `(−1)^{|T|}`. -/
theorem jetCoeff_one (T : Finset ι) :
    jetCoeff (fun _ => (1 : R)) T = (-1 : R) ^ T.card := by
  simp [jetCoeff]

/-- **Algebraic first variation.**  Perturbing the single leg `q` from `1` to
`1 + h` adds `h` times the alternating coefficient exactly when `q ∈ T`. -/
theorem jet_first_variation (T : Finset ι) (q : ι) (h : R) :
    jetCoeff (Function.update (fun _ => (1 : R)) q (1 + h)) T
      = jetCoeff (fun _ => (1 : R)) T
        + (if q ∈ T then h * jetCoeff (fun _ => (1 : R)) T else 0) := by
  classical
  by_cases hq : q ∈ T
  · rw [if_pos hq]
    have hsplit : jetCoeff (Function.update (fun _ => (1 : R)) q (1 + h)) T
        = (-(1 + h)) * ∏ p ∈ T.erase q, (-(Function.update (fun _ => (1 : R)) q (1 + h) p)) := by
      rw [jetCoeff, ← Finset.mul_prod_erase T _ hq, Function.update_self]
    have herase : ∏ p ∈ T.erase q, (-(Function.update (fun _ => (1 : R)) q (1 + h) p))
        = (-1 : R) ^ (T.erase q).card := by
      have hstep : ∀ p ∈ T.erase q,
          (-(Function.update (fun _ => (1 : R)) q (1 + h) p)) = (-1 : R) := by
        intro p hp
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hp)]
      rw [Finset.prod_congr rfl hstep, Finset.prod_const]
    obtain ⟨k, hk⟩ : ∃ k, T.card = k + 1 :=
      ⟨T.card - 1, (Nat.succ_pred_eq_of_pos (Finset.card_pos.2 ⟨q, hq⟩)).symm⟩
    rw [hsplit, herase, jetCoeff_one, Finset.card_erase_of_mem hq, hk, Nat.add_sub_cancel,
      pow_succ]
    ring
  · rw [if_neg hq, add_zero, jetCoeff, jetCoeff]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    rw [Function.update_of_ne (by rintro rfl; exact hq hp)]

/-- **Summed first variation.**  Summing the one-leg variations over an index
set `S ⊇ T` gives `|T|` copies of the alternating coefficient: one
differentiated leg tensored with all remaining alternating legs. -/
theorem jet_sum_first_variation {S T : Finset ι} (hTS : T ⊆ S) :
    ∑ q ∈ S, (if q ∈ T then jetCoeff (fun _ => (1 : R)) T else 0)
      = (T.card : R) * jetCoeff (fun _ => (1 : R)) T := by
  classical
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hTS, Finset.sum_const, nsmul_eq_mul]

end Steinberg
end Gate1BDet2
end TwinPrimeProject
