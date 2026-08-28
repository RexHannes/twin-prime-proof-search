import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

/-!
# Phase A · centered residue kernel (`ENDPOINT-A-CENTERING45`)

**Finite algebra only.**  Nothing here is an estimate, and nothing here is
attached to a physical source.

The centered residue kernel on the unit residue system mod `ℓ` is

  `Δ_ℓ(u₁,u₂) = 1_{u₁ ≡ u₂ (ℓ)} − 1_{(u₁u₂, ℓ) = 1} / φ(ℓ)`.

It is implemented on `ZMod ℓ` (`centeredKernel`), which is the exact finite
residue system; the integer-level version `centeredKernelInt` is the pullback
along `Int.cast`, so the two agree by `centeredKernelInt_eq`.

## What is proved

* `centeredKernel_row_sum_units` — the **zero-row identity**: for a unit `x`,
  `∑_{y ∈ (ZMod ℓ)ˣ} Δ_ℓ(x, y) = 0`.
* `centeredKernel_symm` — symmetry.
* `sum_mul_conj_eq_sum_centered_mul_conj` — the **generic centering lemma**: if
  the residue discrepancy `E` has exact zero mean on a finite index set `S`,
  then testing against `A` and against its centering `A° = A − avg A` gives the
  same value.
* `centering_needs_zero_mean` — a counterguard: with nonzero mean the identity
  is false, so the zero-mean hypothesis is load-bearing.

## What is NOT proved

The physical Pure5 residue discrepancy is **absent from the repository**, so no
adapter from a physical discrepancy to the zero-mean hypothesis is created:

  `PURE5-COMPARISON-MAINTERM-PIN : SOURCE_OPEN`

remains exactly as recorded in the existing ledger.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace Centering

open Finset

/-! ## 1. The centered residue kernel -/

variable (l : ℕ)

/-- The centered residue kernel on `ZMod ℓ`:

  `Δ_ℓ(x,y) = 1_{x = y} − 1_{xy is a unit} / φ(ℓ)`.

On the unit residue system `1_{xy is a unit}` is exactly `1_{(u₁u₂,ℓ)=1}`. -/
noncomputable def centeredKernel [NeZero l] (x y : ZMod l) : ℂ :=
  (if x = y then 1 else 0) - (if IsUnit (x * y) then 1 else 0) / (l.totient : ℂ)

/-- The integer-level kernel, obtained by reduction mod `ℓ`. -/
noncomputable def centeredKernelInt [NeZero l] (u₁ u₂ : ℤ) : ℂ :=
  centeredKernel l (u₁ : ZMod l) (u₂ : ZMod l)

theorem centeredKernelInt_eq [NeZero l] (u₁ u₂ : ℤ) :
    centeredKernelInt l u₁ u₂ = centeredKernel l (u₁ : ZMod l) (u₂ : ZMod l) := rfl

/-- The kernel is symmetric. -/
theorem centeredKernel_symm [NeZero l] (x y : ZMod l) :
    centeredKernel l x y = centeredKernel l y x := by
  unfold centeredKernel
  rw [mul_comm x y]
  congr 1
  by_cases h : x = y
  · simp [h]
  · simp [h, Ne.symm h]

/-- On the unit system the kernel has the explicit two-term shape. -/
theorem centeredKernel_units [NeZero l] (x y : (ZMod l)ˣ) :
    centeredKernel l (x : ZMod l) (y : ZMod l)
      = (if (x : ZMod l) = (y : ZMod l) then 1 else 0) - 1 / (l.totient : ℂ) := by
  have hu : IsUnit ((x : ZMod l) * (y : ZMod l)) := by
    rw [← Units.val_mul]; exact Units.isUnit _
  simp [centeredKernel, hu]

/-! ## 2. The zero-row identity -/

/-- **`ENDPOINT-A-CENTERING45` (zero row).**  Summing the centered kernel over
the full unit residue system mod `ℓ` gives exactly `0`.

This is the exact finite statement that the kernel has been centred: the
congruence indicator contributes `1` and the principal (main) term contributes
`φ(ℓ)/φ(ℓ) = 1`. -/
theorem centeredKernel_row_sum_units [NeZero l] (x : (ZMod l)ˣ) :
    ∑ y : (ZMod l)ˣ, centeredKernel l (x : ZMod l) (y : ZMod l) = 0 := by
  classical
  have hcard : (Fintype.card (ZMod l)ˣ : ℂ) = (l.totient : ℂ) := by
    rw [ZMod.card_units_eq_totient l]
  have hpos : 0 < l := Nat.pos_of_ne_zero (NeZero.ne l)
  have htot : (l.totient : ℂ) ≠ 0 := by
    have : 0 < l.totient := Nat.totient_pos.2 hpos
    exact_mod_cast this.ne'
  rw [Finset.sum_congr rfl
    (fun y (_ : y ∈ Finset.univ) => centeredKernel_units l x y)]
  rw [Finset.sum_sub_distrib]
  have h1 : ∑ y : (ZMod l)ˣ, (if (x : ZMod l) = (y : ZMod l) then (1 : ℂ) else 0) = 1 := by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      have : (x : ZMod l) ≠ (y : ZMod l) := fun h => hy (Units.ext h.symm)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ x) h
  rw [h1, Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcard]
  field_simp
  ring

/-! ## 3. The generic centering lemma -/

variable {ι : Type*}

/-- The centering `A° = A − avg A` of a coefficient family on a finite set. -/
noncomputable def centeredCoeff (S : Finset ι) (A : ι → ℂ) (a : ι) : ℂ :=
  A a - (S.card : ℂ)⁻¹ * ∑ b ∈ S, A b

/-- **`ENDPOINT-A-CENTERING45` (generic centering).**  For any residue
discrepancy `E` with **exact zero mean** on `S`,

  `∑_{a ∈ S} A a · conj (E a) = ∑_{a ∈ S} A° a · conj (E a)`.

No property of `A` is used; the zero-mean hypothesis is the whole content. -/
theorem sum_mul_conj_eq_sum_centered_mul_conj (S : Finset ι) (A E : ι → ℂ)
    (hE : ∑ a ∈ S, E a = 0) :
    ∑ a ∈ S, A a * (starRingEnd ℂ) (E a)
      = ∑ a ∈ S, centeredCoeff S A a * (starRingEnd ℂ) (E a) := by
  classical
  have hconj : ∑ a ∈ S, (starRingEnd ℂ) (E a) = 0 := by
    rw [← map_sum, hE, map_zero]
  unfold centeredCoeff
  rw [Finset.sum_congr rfl (fun a _ => sub_mul _ _ _), Finset.sum_sub_distrib,
    ← Finset.mul_sum, hconj, mul_zero, sub_zero]

/-- **Counterguard.**  Without the zero-mean hypothesis the centering identity
is false: `S = {0}`, `A ≡ 1`, `E ≡ 1` gives `1 ≠ 0`. -/
theorem centering_needs_zero_mean :
    ∃ (S : Finset ℕ) (A E : ℕ → ℂ),
      ∑ a ∈ S, A a * (starRingEnd ℂ) (E a)
        ≠ ∑ a ∈ S, centeredCoeff S A a * (starRingEnd ℂ) (E a) := by
  refine ⟨{0}, fun _ => 1, fun _ => 1, ?_⟩
  simp [centeredCoeff]

/-- The centering of a family has exact zero mean, provided `S` is nonempty.
(This is the dual statement: centering the *other* factor is always legitimate.) -/
theorem sum_centeredCoeff (S : Finset ι) (A : ι → ℂ) (hS : S.Nonempty) :
    ∑ a ∈ S, centeredCoeff S A a = 0 := by
  classical
  have hcard : (S.card : ℂ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.2 hS).ne'
  unfold centeredCoeff
  rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  field_simp
  ring

end Centering
end CurrentProgramme
end TwinPrimeProject
