/-
# Gate1B / R11 / Frontier : the modular relation of the critical mixed moment

Exact finite algebra obtained after opening a mixed moment between two occupied rows `i ≠ j`.

The only content that is *proved* here is the modular relation

    q_i A ≡ q_j B  (mod k)   →   ∃ ℓ : ℤ,  q_i A − q_j B = ℓ k,

together with its converse, the corresponding statement for the source row data
(`MixedIncidenceData`), and the elementary consequences (`k ∣ q_i A − q_j B`, and the sharpened
form after removing a common factor).

**Firewall.**  No size estimate is asserted.  In particular the number of solutions `ℓ` in a
range, or any heuristic "≍" for the incidence count, is *not* formalised here: the file records
an exact divisibility statement and nothing else, and the last theorem exhibits data where the
witness `ℓ` is as large as the trivial bound allows.
-/
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

namespace Gate1B.R11.Frontier

/-! ## 1. The modular relation -/

/-- **MIXED-INCIDENCE MODULAR RELATION.**  A congruence between the two opened row products is
exactly the existence of an integer `ℓ` with `q_i A − q_j B = ℓ k`. -/
theorem mixedIncidence_relation {qi qj A B k : ℤ} (h : qi * A ≡ qj * B [ZMOD k]) :
    ∃ ell : ℤ, qi * A - qj * B = ell * k := by
  obtain ⟨c, hc⟩ := h.dvd
  exact ⟨-c, by linarith [hc]⟩

/-- The converse: an integral relation `q_i A − q_j B = ℓ k` is a congruence mod `k`. -/
theorem mixedIncidence_relation_converse {qi qj A B k ell : ℤ}
    (h : qi * A - qj * B = ell * k) : qi * A ≡ qj * B [ZMOD k] :=
  Int.ModEq.symm (Int.modEq_iff_dvd.2 ⟨ell, by linarith⟩)

/-- The relation in divisibility form. -/
theorem mixedIncidence_dvd {qi qj A B k : ℤ} (h : qi * A ≡ qj * B [ZMOD k]) :
    k ∣ qi * A - qj * B := by
  obtain ⟨ell, hell⟩ := mixedIncidence_relation h
  exact ⟨ell, by linarith⟩

/-- The witness `ℓ` is unique when `k ≠ 0`. -/
theorem mixedIncidence_witness_unique {qi qj A B k ell ell' : ℤ} (hk : k ≠ 0)
    (h : qi * A - qj * B = ell * k) (h' : qi * A - qj * B = ell' * k) : ell = ell' := by
  have : ell * k = ell' * k := by rw [← h, h']
  exact mul_right_cancel₀ hk this

/-! ## 2. Source-level packaging -/

/-- The finite source data of a critical mixed moment: two rows with moduli `qi`, `qj`,
opened variables `A`, `B`, a common incidence modulus `k`, and the congruence produced by the
row/progression hypotheses. -/
structure MixedIncidenceData where
  /-- Modulus of the first row. -/
  qi : ℤ
  /-- Modulus of the second row. -/
  qj : ℤ
  /-- Opened variable of the first row. -/
  A : ℤ
  /-- Opened variable of the second row. -/
  B : ℤ
  /-- The incidence modulus. -/
  k : ℤ
  /-- The congruence supplied by the row/congruence hypotheses. -/
  congr_hyp : qi * A ≡ qj * B [ZMOD k]

/-- **The modular relation for source data.** -/
theorem MixedIncidenceData.relation (d : MixedIncidenceData) :
    ∃ ell : ℤ, d.qi * d.A - d.qj * d.B = ell * d.k :=
  mixedIncidence_relation d.congr_hyp

/-- After removing a common factor `g > 0` from both moduli and from `k`, the relation descends
with the same witness. -/
theorem mixedIncidence_descent {qi qj A B k g qi' qj' k' ell : ℤ} (hg : g ≠ 0)
    (hqi : qi = g * qi') (hqj : qj = g * qj') (hk : k = g * k')
    (h : qi * A - qj * B = ell * k) : qi' * A - qj' * B = ell * k' := by
  subst hqi; subst hqj; subst hk
  have hg' : g * (qi' * A - qj' * B) = g * (ell * k') := by ring_nf; ring_nf at h; linarith
  exact mul_left_cancel₀ hg hg'

/-! ## 3. Firewall: no size information -/

/-- **NO SIZE BOUND.**  The modular relation carries no information about the size of `ℓ`: for
every `L` there are admissible data whose (unique) witness exceeds `L`.  Hence a heuristic
incidence count may not be read off from this file. -/
theorem mixedIncidence_no_size_bound (L : ℤ) :
    ∃ d : MixedIncidenceData, d.k ≠ 0 ∧
      ∀ ell : ℤ, d.qi * d.A - d.qj * d.B = ell * d.k → L < ell := by
  refine ⟨{ qi := L + 1, qj := 0, A := 1, B := 0, k := 1,
            congr_hyp := Int.modEq_one }, one_ne_zero, ?_⟩
  intro ell hell
  simp at hell
  omega

end Gate1B.R11.Frontier
