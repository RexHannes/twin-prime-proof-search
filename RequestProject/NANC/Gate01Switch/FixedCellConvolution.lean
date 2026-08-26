import RequestProject.NANC.Gate01Switch.GenericSwitched
import RequestProject.R9ConvolutionAlgebra

/-!
# Gate01Switch: the fixed `r = 9` cell convolution

## Source audit

The archive (`RequestProject/R9ConvolutionAlgebra.lean`) proves the *abstract*
`r = 9` symmetrisation identity
`r9OrderedBlockSum = κ • conv + r9RepeatedFactorCorrection`
(`TwinPrimeProject.r9BlockConvolutionDecomposition`), i.e. an ordered/distinct
label split with an explicit repeated-label correction.

It does **not** contain the coefficient formula

`c₉ = κ_j (α_j * β_{9-j}) + E_j`.  (C9)

Therefore (C9) is **not assumed** anywhere.  It is recorded as the explicit
predicate `R9CellConvolution` and used only as a *hypothesis*; the ledger marks
`R9_CELL_CONVOLUTION` as `SourceOpen`.

## Finite content

* `dconv` — the finite Dirichlet convolution `(α*β)(t) = ∑_{mn=t} α(m) β(n)`;
* `dconv_eq_r9Distinct`-free: no symmetrisation constant is invented;
* `R9CellConvolution` — the (C9) shape as an explicit predicate.
-/

namespace TwinPrimeProject
namespace Gate01Switch

open Finset

/-- The finite Dirichlet convolution `(α * β)(t) = ∑_{mn = t} α(m) β(n)`. -/
def dconv (a b : ℕ → ℝ) (t : ℕ) : ℝ :=
  ∑ x ∈ t.divisorsAntidiagonal, a x.1 * b x.2

@[simp] theorem dconv_zero (a b : ℕ → ℝ) : dconv a b 0 = 0 := by simp [dconv]

theorem dconv_comm (a b : ℕ → ℝ) (t : ℕ) : dconv a b t = dconv b a t := by
  rw [dconv, dconv, Nat.sum_divisorsAntidiagonal (f := fun m n => a m * b n),
    Nat.sum_divisorsAntidiagonal' (f := fun m n => b m * a n)]
  exact Finset.sum_congr rfl fun x _ => mul_comm _ _

/-- **(C9) as an explicit predicate.**  `c` has the fixed `r = 9` cell shape
`c = κ (α * β) + E` with respect to the given data.  This is *not* proved of any
archive coefficient: the archive has no such identity, so it is only ever used
as a hypothesis. -/
def R9CellConvolution (c : ℕ → ℝ) (kappa : ℝ) (a b : ℕ → ℝ) (Eterm : ℕ → ℝ) : Prop :=
  ∀ t, c t = kappa * dconv a b t + Eterm t

/-!
Deliberately, no `structure R9CellConvolutionStatement` packaging *arbitrary*
data is introduced: such a structure would be trivially inhabited (take
`κ = 1`, `E_j = 0`, `c = α * β`) and would therefore record nothing.  The honest
interface is the predicate `R9CellConvolution` applied to the *actual* source
data — which the archive does not supply.  Ledger: `R9_CELL_CONVOLUTION` is
`SourceOpen`.
-/

end Gate01Switch
end TwinPrimeProject
