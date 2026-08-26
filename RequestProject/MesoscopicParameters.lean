import Mathlib

/-!
# Mesoscopic finite-product bound (§12.7)

The F1 product calculation is valid *conditionally*: if every Heath–Brown block
`Yᵢ` satisfies `Yᵢ ≤ Y_mes` and the depth `K` is fixed, then the product of the
blocks is at most `Y_mes^K`.  This is the only part of the mesoscopic branch that
is unconditionally machine-checkable; the `X^{o(1)}` consequence is kept in
`LEDGER.md` because it is an asymptotic statement about the analytic threshold.
-/

namespace ShiftedMobiusBank

/-- §12.7 — finite-product bound over `Fin K`.  If `0 ≤ Y i ≤ Ymes` for each block
`i`, then `∏ Y i ≤ Ymes ^ K`. -/
theorem mesoscopic_finite_product_bound {K : ℕ} (Ymes : ℝ) (Y : Fin K → ℝ)
    (hnonneg : ∀ i, 0 ≤ Y i) (hbound : ∀ i, Y i ≤ Ymes) :
    ∏ i, Y i ≤ Ymes ^ K := by
  calc ∏ i, Y i ≤ ∏ _i : Fin K, Ymes :=
        Finset.prod_le_prod (fun i _ => hnonneg i) (fun i _ => hbound i)
    _ = Ymes ^ K := by simp

/-- §12.7 — the same bound indexed over a general finset, with the exponent equal
to the cardinality. -/
theorem mesoscopic_finite_product_bound' {ι : Type*} (s : Finset ι) (Ymes : ℝ)
    (Y : ι → ℝ) (hnonneg : ∀ i ∈ s, 0 ≤ Y i) (hbound : ∀ i ∈ s, Y i ≤ Ymes) :
    ∏ i ∈ s, Y i ≤ Ymes ^ s.card := by
  calc ∏ i ∈ s, Y i ≤ ∏ _i ∈ s, Ymes := Finset.prod_le_prod hnonneg hbound
    _ = Ymes ^ s.card := by simp

end ShiftedMobiusBank
