import Gate1B.FM722CenteredDualAxes
import Gate1B.FM722GeneratedDFTFourierSparsity

/-!
# Gate 1B · FM722 · the generated-DFT **cross-`q`** object and the open analytic
interface

This module contains

* §1 the finite atom `J(q)` of the generated-DFT cross-`q` object, built from
  an **arbitrary supplied** `λ₃`-weight, a prime index `π`, the DFT
  coefficients `α̂_q`, `γ̂_q` and the centred Kloosterman kernel `K_q(k,j;π)`;
* §2 the exact identity `J(q) = λ₃(q) · (physical centred packet at q)`,
  a deterministic consequence of the two-factor centred completion;
* §3 the finite family object, the diagonal mass, and the **cross-`q`
  covariance** `∑_{q₁ ≠ q₂} J(q₁) conj (J(q₂))` restricted by an *abstract*
  small-gcd predicate;
* §4 the deterministic split `total = diagonal + cross`;
* §5 the **uninhabited** analytic interface
  `FM722GeneratedDFTCenteredKloostermanCrossQBound`, which is the current
  analytic residual `FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45`.
  It is never inhabited: no axiom, no `sorry`, no instance and no default
  value is provided anywhere;
* §6 uninhabited literature-input structures (sparse-Fourier Kloosterman
  input, Blomer–Pascadi critical-block input).  These are *dictionary
  placeholders under research audit only*: no external theorem is asserted,
  and nothing is derived from the literature;
* §7 the deterministic **conditional compiler**: the interface implies the
  corresponding finite FM722 packet bound.  The analytic input itself is never
  derived.

No analytic bound is proved in this module.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier
open TwinPrimeProject.CurrentProgramme.HStarCentered

/-! ## 1. The generated-DFT atom `J(q)` -/

/-- The **generated-DFT atom** at a single modulus `q`:

```
  J(q) = λ₃(q) · q⁻² ∑_{k,j} α̂_q(k) γ̂_q(j) K_q(k,j;π).
```

The `λ₃`-weight is an arbitrary supplied coefficient; no property of it is
used or assumed. -/
noncomputable def crossQAtom (q : ℕ) [NeZero q] (lambda3 : ℂ)
    (alpha gamma : ZMod q → ℂ) (pi : (ZMod q)ˣ) : ℂ :=
  lambda3 * (((q : ℂ)) ^ 2)⁻¹ *
    ∑ k : ZMod q, ∑ j : ZMod q,
      dftHat q alpha k * dftHat q gamma j * centeredKloostermanKernel q k j pi

/-- The **physical centred packet** at a single modulus `q`:

```
  λ₃(q) ∑_{A,C} α(A) γ(C) Δ_q(A C π).
```
-/
noncomputable def physicalAtom (q : ℕ) [NeZero q] (lambda3 : ℂ)
    (alpha gamma : ZMod q → ℂ) (pi : (ZMod q)ˣ) : ℂ :=
  lambda3 * ∑ A : ZMod q, ∑ C : ZMod q,
    alpha A * gamma C * centeredProjector q (A * C * (pi : ZMod q))

/-! ## 2. The atom identity -/

/-- **Exact atom identity.**  The generated-DFT atom is *equal* to the physical
centred packet; this is the two-factor centred completion with the supplied
`λ₃`-weight attached. -/
theorem crossQAtom_eq_physicalAtom (q : ℕ) [NeZero q] (h2 : IsUnit (2 : ZMod q))
    (lambda3 : ℂ) (alpha gamma : ZMod q → ℂ) (pi : (ZMod q)ˣ) :
    crossQAtom q lambda3 alpha gamma pi = physicalAtom q lambda3 alpha gamma pi := by
  rw [crossQAtom, physicalAtom, twoFactor_centered_completion h2 alpha gamma pi]
  ring

/-! ## 3. The finite cross-`q` family -/

/-- A finite family of generated-DFT data: `n` moduli, each with its supplied
`λ₃`-weight, prime index `π`, and coefficient pair `(α, γ)`, together with an
**abstract** small-gcd predicate on pairs of indices. -/
structure CrossQFamily (n : ℕ) where
  /-- The moduli `q₁, …, qₙ`. -/
  modulus : Fin n → ℕ
  /-- Positivity of the moduli. -/
  modulus_pos : ∀ i, 0 < modulus i
  /-- The arbitrary supplied `λ₃`-weights. -/
  lambda3 : Fin n → ℂ
  /-- The `α`-coefficients modulo each `qᵢ`. -/
  alpha : (i : Fin n) → ZMod (modulus i) → ℂ
  /-- The `γ`-coefficients modulo each `qᵢ`. -/
  gamma : (i : Fin n) → ZMod (modulus i) → ℂ
  /-- The prime index `π` modulo each `qᵢ`, a unit. -/
  piIdx : (i : Fin n) → (ZMod (modulus i))ˣ
  /-- The abstract small-gcd predicate selecting the admissible cross pairs. -/
  smallGcd : Fin n → Fin n → Prop

/-- The atom `J(qᵢ)` of a family. -/
noncomputable def CrossQFamily.J {n : ℕ} (F : CrossQFamily n) (i : Fin n) : ℂ :=
  @crossQAtom (F.modulus i) ⟨(F.modulus_pos i).ne'⟩ (F.lambda3 i)
    (F.alpha i) (F.gamma i) (F.piIdx i)

/-- The physical packet at index `i`. -/
noncomputable def CrossQFamily.packet {n : ℕ} (F : CrossQFamily n) (i : Fin n) : ℂ :=
  @physicalAtom (F.modulus i) ⟨(F.modulus_pos i).ne'⟩ (F.lambda3 i)
    (F.alpha i) (F.gamma i) (F.piIdx i)

/-- **Family-level atom identity.** -/
theorem CrossQFamily.J_eq_packet {n : ℕ} (F : CrossQFamily n) (i : Fin n)
    (h2 : IsUnit (2 : ZMod (F.modulus i))) : F.J i = F.packet i := by
  letI : NeZero (F.modulus i) := ⟨(F.modulus_pos i).ne'⟩
  exact crossQAtom_eq_physicalAtom (F.modulus i) h2 _ _ _ _

open scoped Classical in
/-- The **cross-`q` covariance**

```
  ∑_{q₁ ≠ q₂, smallGcd} J(q₁) conj (J(q₂)).
```
-/
noncomputable def crossQCovariance {n : ℕ} (F : CrossQFamily n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i = j then 0
    else if F.smallGcd i j then F.J i * (starRingEnd ℂ) (F.J j) else 0

/-- The **diagonal mass** `∑_q |J(q)|²`. -/
noncomputable def crossQDiagonal {n : ℕ} (F : CrossQFamily n) : ℝ :=
  ∑ i : Fin n, ‖F.J i‖ ^ 2

open scoped Classical in
/-- The **total admissible covariance**: the diagonal together with the
admissible cross pairs. -/
noncomputable def crossQTotal {n : ℕ} (F : CrossQFamily n) : ℂ :=
  ∑ i : Fin n, ∑ j : Fin n,
    if i = j ∨ F.smallGcd i j then F.J i * (starRingEnd ℂ) (F.J j) else 0

/-! ## 4. The deterministic split -/

theorem crossQDiagonal_nonneg {n : ℕ} (F : CrossQFamily n) : 0 ≤ crossQDiagonal F :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem crossQDiagonal_cast {n : ℕ} (F : CrossQFamily n) :
    ((crossQDiagonal F : ℝ) : ℂ) = ∑ i : Fin n, F.J i * (starRingEnd ℂ) (F.J i) := by
  rw [crossQDiagonal]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.mul_conj]
  norm_cast
  exact (Complex.normSq_eq_norm_sq _).symm

/-- **Deterministic algebra.**  `total = diagonal + cross`. -/
theorem crossQTotal_split {n : ℕ} (F : CrossQFamily n) :
    crossQTotal F = ((crossQDiagonal F : ℝ) : ℂ) + crossQCovariance F := by
  classical
  rw [crossQDiagonal_cast, crossQTotal, crossQCovariance, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hpt : ∀ j : Fin n,
      (if i = j ∨ F.smallGcd i j then F.J i * (starRingEnd ℂ) (F.J j) else 0)
        = (if i = j then F.J i * (starRingEnd ℂ) (F.J j) else 0)
          + (if i = j then 0
              else if F.smallGcd i j then F.J i * (starRingEnd ℂ) (F.J j) else 0) := by
    intro j; by_cases h : i = j <;> simp [h]
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib]
  congr 1
  simp

/-! ## 5. The open analytic interface — UNINHABITED -/

/-- **OPEN ANALYTIC INTERFACE — never inhabited.**

`FM722GeneratedDFTCenteredKloostermanCrossQBound` is the current analytic
residual

```
FM722-GENERATEDDFT-CENTEREDKLOOSTERMAN-CROSSQ45
```

namely a power saving for the cross-`q` covariance of the generated-DFT
centred-Kloosterman atoms, relative to the diagonal mass, uniformly over
finite admissible families.

No axiom asserts it, no instance is constructed, no default value is provided,
and nothing downstream of it is claimed unconditionally. -/
structure FM722GeneratedDFTCenteredKloostermanCrossQBound where
  /-- The saving exponent. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- **The analytic field.**  The only unproved content of the interface. -/
  crossBound :
    ∀ (n : ℕ) (F : CrossQFamily n),
      (∀ i, IsUnit (2 : ZMod (F.modulus i))) →
        ‖crossQCovariance F‖ ≤ const * ((n : ℝ) ^ (-eta)) * crossQDiagonal F

/-! ## 6. Literature-input placeholders — UNINHABITED, research audit only -/

/-- **Dictionary placeholder — never inhabited.**  Intended slot for a
sparse-Fourier Kloosterman bound from the literature.  Nothing is asserted
here; the corresponding literature dictionary is *under research audit*, not
kernel-proved. -/
structure SparseFourierKloostermanBoundInput where
  /-- The saving exponent claimed by the intended literature input. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- The abstract input field, stated only for families whose DFT data
  satisfies a supplied sparsity predicate. -/
  sparseBound :
    ∀ (sparse : ∀ n : ℕ, CrossQFamily n → Prop) (n : ℕ) (F : CrossQFamily n),
      sparse n F → ‖crossQCovariance F‖ ≤ const * ((n : ℝ) ^ (-eta)) * crossQDiagonal F

/-- **Dictionary placeholder — never inhabited.**  Intended slot for a
Blomer–Pascadi critical-block bound.  Under research audit only. -/
structure BPCriticalBlockBoundInput where
  /-- The saving exponent claimed by the intended literature input. -/
  eta : ℝ
  eta_pos : 0 < eta
  /-- The implied constant. -/
  const : ℝ
  const_nonneg : 0 ≤ const
  /-- The abstract input field, stated only on a supplied critical-block
  predicate. -/
  criticalBlockBound :
    ∀ (criticalBlock : ∀ n : ℕ, CrossQFamily n → Prop) (n : ℕ) (F : CrossQFamily n),
      criticalBlock n F →
        ‖crossQCovariance F‖ ≤ const * ((n : ℝ) ^ (-eta)) * crossQDiagonal F

/-! ## 7. The deterministic conditional compiler -/

/-- **Conditional compiler.**  Given the analytic interface, the finite FM722
packet bound follows deterministically: the total admissible covariance is
controlled by the diagonal mass with the interface saving.

The analytic input is *not* derived anywhere. -/
theorem crossQTotal_bound_of_interface
    (I : FM722GeneratedDFTCenteredKloostermanCrossQBound)
    {n : ℕ} (F : CrossQFamily n) (h2 : ∀ i, IsUnit (2 : ZMod (F.modulus i))) :
    ‖crossQTotal F‖ ≤ (1 + I.const * ((n : ℝ) ^ (-I.eta))) * crossQDiagonal F := by
  have hcross := I.crossBound n F h2
  have hdiag := crossQDiagonal_nonneg F
  calc ‖crossQTotal F‖
      ≤ ‖((crossQDiagonal F : ℝ) : ℂ)‖ + ‖crossQCovariance F‖ := by
        rw [crossQTotal_split]; exact norm_add_le _ _
    _ = crossQDiagonal F + ‖crossQCovariance F‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hdiag]
    _ ≤ crossQDiagonal F + I.const * ((n : ℝ) ^ (-I.eta)) * crossQDiagonal F := by
        linarith
    _ = (1 + I.const * ((n : ℝ) ^ (-I.eta))) * crossQDiagonal F := by ring

/-- **Conditional compiler, physical form.**  Under the interface, the same
bound holds for the total admissible covariance written in terms of the
*physical* centred packets, since each atom equals its packet. -/
theorem packet_covariance_bound_of_interface
    (I : FM722GeneratedDFTCenteredKloostermanCrossQBound)
    {n : ℕ} (F : CrossQFamily n) (h2 : ∀ i, IsUnit (2 : ZMod (F.modulus i))) :
    ‖crossQTotal F‖ ≤ (1 + I.const * ((n : ℝ) ^ (-I.eta))) *
        ∑ i : Fin n, ‖F.packet i‖ ^ 2 := by
  have hrw : ∑ i : Fin n, ‖F.packet i‖ ^ 2 = crossQDiagonal F := by
    rw [crossQDiagonal]
    exact Finset.sum_congr rfl fun i _ => by rw [F.J_eq_packet i (h2 i)]
  rw [hrw]
  exact crossQTotal_bound_of_interface I F h2

end FM722
end CurrentProgramme
end TwinPrimeProject
