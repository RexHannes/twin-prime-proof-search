/-
# Gate1B / R11 / Frontier : the product-fibre pushforward

Purely algebraic source identity.  For each source position `v` let `N v ≥ 0` be the fibre count
`N_{k_i}(B_{i,v})` and let `b v` be the (signed, complex) source value, subject to the source
hypothesis `‖b v‖ ≤ N v`.  Put

    w v = b v / N v   if  N v ≠ 0,     w v = 0  otherwise.

Kernel-proved here:

* `b v = N v · w v` at *every* position (including the degenerate ones, where both sides vanish);
* `‖w v‖ ≤ 1`;
* the identity is an identity **after equal-product merging**: modelling the merging by a finite
  tuple space `T`, a product map `P : T → ι` and a selector `s : T → ℂ` with `‖s t‖ ≤ 1`, the
  pushforward `b = P_* s` satisfies `‖b v‖ ≤ #P⁻¹(v)`, so the identity above applies verbatim;
* **firewall**: the pushforward identity does *not* determine the selector.  Two different
  selectors with the same product-fibre pushforward are exhibited, so product-fibre equality is
  strictly weaker than tuplewise equality.
-/
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

namespace Gate1B.R11.Frontier

open Finset

noncomputable section

/-! ## 1. The abstract pushforward weight -/

variable {ι : Type*}

/-- The normalised source weight `w = b / N` (zero at degenerate positions). -/
def fibreWeight (N : ι → ℝ) (b : ι → ℂ) (v : ι) : ℂ :=
  if N v = 0 then 0 else b v / (N v : ℂ)

/-- **PRODUCT-FIBRE PUSHFORWARD IDENTITY** `b v = N v · w v`, valid at every position. -/
theorem pushforward_factorisation {N : ι → ℝ} {b : ι → ℂ} (v : ι) (hb : ‖b v‖ ≤ N v) : b v = (N v : ℂ) * fibreWeight N b v := by
  by_cases h : N v = 0
  · have hb0 : b v = 0 := by
      have : ‖b v‖ ≤ 0 := by rw [← h]; exact hb
      exact norm_le_zero_iff.mp this
    simp [fibreWeight, h, hb0]
  · have hne : (N v : ℂ) ≠ 0 := by exact_mod_cast h
    rw [fibreWeight, if_neg h, mul_div_cancel₀ _ hne]

/-- At an **occupied** source position (`N v ≠ 0`) the weight is literally the quotient. -/
theorem fibreWeight_of_occupied {N : ι → ℝ} {b : ι → ℂ} {v : ι} (h : N v ≠ 0) :
    fibreWeight N b v = b v / (N v : ℂ) := if_neg h

/-- **`‖w‖ ≤ 1`.** -/
theorem norm_fibreWeight_le_one {N : ι → ℝ} {b : ι → ℂ} (v : ι) (hb : ‖b v‖ ≤ N v) :
    ‖fibreWeight N b v‖ ≤ 1 := by
  by_cases h : N v = 0
  · simp [fibreWeight, h]
  · have hpos : 0 < N v := lt_of_le_of_ne (le_trans (norm_nonneg _) hb) (Ne.symm h)
    rw [fibreWeight, if_neg h, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
    exact div_le_one_of_le₀ hb hpos.le

/-! ## 2. Equal-product merging -/

variable {T : Type*} [Fintype T] [DecidableEq ι]

/-- The fibre of the product map over the position `v`. -/
def productFibre (P : T → ι) (v : ι) : Finset T := Finset.univ.filter (fun t => P t = v)

/-- The fibre count `N(v) = #P⁻¹(v)`. -/
def fibreCount (P : T → ι) (v : ι) : ℝ := ((productFibre P v).card : ℝ)

/-- The **pushforward** of a selector along the product map: this is exactly the
"equal-product merging" of the tuple data. -/
def pushforward (P : T → ι) (s : T → ℂ) (v : ι) : ℂ := ∑ t ∈ productFibre P v, s t

theorem fibreCount_nonneg (P : T → ι) (v : ι) : 0 ≤ fibreCount P v := by
  unfold fibreCount; positivity

/-- The source hypothesis is automatic after merging: `‖b v‖ ≤ N v` for a bounded selector. -/
theorem norm_pushforward_le_fibreCount {P : T → ι} {s : T → ℂ} (hs : ∀ t, ‖s t‖ ≤ 1) (v : ι) :
    ‖pushforward P s v‖ ≤ fibreCount P v := by
  refine le_trans (norm_sum_le _ _) ?_
  refine le_trans (Finset.sum_le_card_nsmul _ _ 1 fun t _ => hs t) ?_
  simp [fibreCount]

/-- **THE MERGED IDENTITY.**  After equal-product merging the source value factors exactly as
`b = N · w` with `‖w‖ ≤ 1`. -/
theorem merged_pushforward_factorisation {P : T → ι} {s : T → ℂ} (hs : ∀ t, ‖s t‖ ≤ 1) (v : ι) :
    pushforward P s v
        = (fibreCount P v : ℂ) * fibreWeight (fibreCount P) (pushforward P s) v ∧
      ‖fibreWeight (fibreCount P) (pushforward P s) v‖ ≤ 1 :=
  ⟨pushforward_factorisation v (norm_pushforward_le_fibreCount hs v),
    norm_fibreWeight_le_one v (norm_pushforward_le_fibreCount hs v)⟩

/-! ## 3. Firewall: merged equality is not tuplewise equality -/

/-- Two selectors on a two-element tuple space with the same product. -/
def selectorA : Fin 2 → ℂ := fun t => if t = 0 then 1 else 0

/-- The second selector: the mass sits on the other tuple. -/
def selectorB : Fin 2 → ℂ := fun t => if t = 0 then 0 else 1

/-- **PRODUCT-FIBRE FIREWALL.**  Product-fibre equality `P_* s = P_* s'` does **not** imply
tuplewise equality `s = s'`: an explicit pair of admissible selectors with identical pushforward
and different tuple values. -/
theorem productFibre_equality_ne_tuplewise_equality :
    ∃ (P : Fin 2 → Fin 1) (s s' : Fin 2 → ℂ),
      (∀ t, ‖s t‖ ≤ 1) ∧ (∀ t, ‖s' t‖ ≤ 1) ∧
      (∀ v, pushforward P s v = pushforward P s' v) ∧ s ≠ s' := by
  refine ⟨fun _ => 0, selectorA, selectorB, ?_, ?_, ?_, ?_⟩
  · intro t; fin_cases t <;> simp [selectorA]
  · intro t; fin_cases t <;> simp [selectorB]
  · intro v
    have hfib : productFibre (fun _ : Fin 2 => (0 : Fin 1)) v = Finset.univ := by
      ext t; simp [productFibre, Subsingleton.elim (0 : Fin 1) v]
    rw [pushforward, pushforward, hfib]
    simp [selectorA, selectorB, Fin.sum_univ_two]
  · intro h
    have := congrFun h 0
    simp [selectorA, selectorB] at this

/-- The same firewall in the form used downstream: the merged weight `w` is determined by the
merged source, but the tuple selector behind it is not. -/
theorem fibreWeight_does_not_determine_selector :
    ∃ (P : Fin 2 → Fin 1) (s s' : Fin 2 → ℂ),
      (∀ v, fibreWeight (fibreCount P) (pushforward P s) v
          = fibreWeight (fibreCount P) (pushforward P s') v) ∧ s ≠ s' := by
  obtain ⟨P, s, s', _, _, hpush, hne⟩ := productFibre_equality_ne_tuplewise_equality
  exact ⟨P, s, s', fun v => by rw [fibreWeight, fibreWeight, hpush v], hne⟩

end

end Gate1B.R11.Frontier
