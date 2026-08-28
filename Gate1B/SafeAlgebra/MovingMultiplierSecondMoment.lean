/-
# Gate 1B v12 — the exact moving-multiplier second moment

**Status: PROVED_ALGEBRAIC (exact finite identity; no estimate).**

For a prime modulus `p`, an additive character system `C` and a complete
multiplicative character system `S` on `(ZMod p)ˣ` with a designated principal
character, this module proves the two *exact* identities

    ∑_{a mod p}   |B_a|² = p² · ProductResidueEnergy(α,β) −  p     ·|∑α|²|∑β|²,
    ∑_{a unit}    |B_a|² = p² · ProductResidueEnergy(α,β) − (p+1) ·|∑α|²|∑β|²,

where

    ProductResidueEnergy(α,β) = ∑_{r mod p} | ∑_{m·n ≡ r} α_m β_n |².

The constants `p` and `p+1` are **derived**, not assumed: they come out of the
repository's own normalisation (`gaussSumOf`, `MulCharSystem.hat`,
`AdditiveCharacterSystem.kloosterman`) via

* `gaussSum_mul_conj`      — |τ(χ)|² = p for every non-principal χ;
* `gaussSum_principal`     — τ(χ₀) = −1;
* `character_dual_parseval_real` — Parseval over the moving multiplier `a`.

The unit-support hypothesis on `α, β` is carried by the typing: they are
functions on the unit group.

**No asymptotic bound on `ProductResidueEnergy` is proved or assumed here.**
-/
import Mathlib
import Gate1B.SafeAlgebra.MovingMultiplierPrime

namespace Gate1B.SafeAlgebra

open Finset

/-! ## Summation over the units of a finite field -/

/-- In a finite `GroupWithZero`, summing over the units is summing over
everything and removing the value at `0`. -/
theorem sum_units_eq_sum_sub_zero {F : Type*} [GroupWithZero F] [Fintype F] [DecidableEq F]
    {M : Type*} [AddCommGroup M]
    (f : F → M) : ∑ u : Fˣ, f ((u : F)) = (∑ x : F, f x) - f 0 := by
  classical
  have h1 : ∑ u : Fˣ, f ((u : F)) = ∑ s : {a : F // a ≠ 0}, f ((s : F)) :=
    Fintype.sum_equiv (unitsEquivNeZero (G₀ := F))
      (fun u : Fˣ => f ((u : F))) (fun s : {a : F // a ≠ 0} => f ((s : F)))
      (by intro u; simp)
  have h2 : ∑ x ∈ Finset.univ.erase (0 : F), f x = ∑ s : {a : F // a ≠ 0}, f ((s : F)) :=
    Finset.sum_subtype (p := fun a : F => a ≠ 0) (Finset.univ.erase (0 : F))
      (by intro x; simp) f
  have h3 : ∑ x ∈ Finset.univ.erase (0 : F), f x + f 0 = ∑ x : F, f x :=
    Finset.sum_erase_add (Finset.univ : Finset F) f (Finset.mem_univ 0)
  rw [h1, ← h2, ← h3]
  abel

variable {p : ℕ} [Fact p.Prime] {Ch : Type*} [Fintype Ch] [DecidableEq Ch]

/-! ## Exact additive sums over the unit group -/

/-- The additive character summed over the **units** of `ZMod p`. -/
theorem sum_chi_units (C : AdditiveCharacterSystem p) (z : ZMod p) :
    ∑ u : (ZMod p)ˣ, C.chi ((u : ZMod p) * z)
      = (if z = 0 then (p : ℂ) else 0) - 1 := by
  classical
  have h := sum_units_eq_sum_sub_zero (F := ZMod p) (fun x => C.chi (x * z))
  rw [h, C.orthogonality z]
  simp [C.chi_zero]

/-- `∑_{u unit} e(u) = −1`. -/
theorem sum_chi_units_one (C : AdditiveCharacterSystem p) :
    ∑ u : (ZMod p)ˣ, C.chi ((u : ZMod p)) = -1 := by
  have h := sum_chi_units C 1
  simp only [mul_one] at h
  rw [h]
  have : (1 : ZMod p) ≠ 0 := one_ne_zero
  simp [this]

/-! ## Gauss sums at the given normalisation -/

/-- **The principal Gauss sum is `−1`.** -/
theorem gaussSum_principal (C : AdditiveCharacterSystem p)
    (S : MulCharSystem (ZMod p)ˣ Ch) (c₀ : Ch) (hc₀ : S.IsPrincipal c₀) :
    gaussSumOf C S c₀ = -1 := by
  unfold gaussSumOf
  rw [← sum_chi_units_one C]
  exact Finset.sum_congr rfl fun u _ => by rw [hc₀ u, one_mul]

/-- A non-principal character sums to zero over the unit group. -/
theorem sum_chi_eq_zero (S : MulCharSystem (ZMod p)ˣ Ch) (c c₀ : Ch)
    (hc₀ : S.IsPrincipal c₀) (hc : c ≠ c₀) :
    ∑ g : (ZMod p)ˣ, S.chi c g = 0 := by
  have h := S.orthogonality c c₀
  have h1 : ∀ g : (ZMod p)ˣ, S.chi c₀ g = 1 := hc₀
  simp only [h1, map_one, mul_one, if_neg hc] at h
  exact h

/-- **|τ(χ)|² = p for every non-principal χ** — exact, derived from the two
supplied orthogonality relations.  (No Weil bound is involved: this is the
elementary Gauss-sum modulus.) -/
theorem gaussSum_mul_conj (C : AdditiveCharacterSystem p)
    (S : MulCharSystem (ZMod p)ˣ Ch) (c c₀ : Ch) (hc₀ : S.IsPrincipal c₀) (hc : c ≠ c₀) :
    gaussSumOf C S c * (starRingEnd ℂ) (gaussSumOf C S c) = (p : ℂ) := by
  classical
  have expand : gaussSumOf C S c * (starRingEnd ℂ) (gaussSumOf C S c)
      = ∑ y : (ZMod p)ˣ, ∑ t : (ZMod p)ˣ,
          S.chi c t * C.chi ((y : ZMod p) * ((t : ZMod p) - 1)) := by
    unfold gaussSumOf
    rw [map_sum, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    -- reindex `x = t * y`
    rw [← Equiv.sum_comp (Equiv.mulRight y)
      (fun x : (ZMod p)ˣ => (S.chi c x * C.chi ((x : ZMod p))) *
        (starRingEnd ℂ) (S.chi c y * C.chi ((y : ZMod p))))]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hmul : (Equiv.mulRight y) t = t * y := rfl
    rw [hmul, S.map_mul, map_mul, C.conj_eq]
    have hchi : S.chi c t * S.chi c y * (starRingEnd ℂ) (S.chi c y) = S.chi c t := by
      rw [mul_assoc, S.chi_mul_conj, mul_one]
    have hadd : C.chi ((t : ZMod p) * (y : ZMod p)) * C.chi (-(y : ZMod p))
        = C.chi ((y : ZMod p) * ((t : ZMod p) - 1)) := by
      rw [← C.add]
      congr 1
      ring
    calc S.chi c t * S.chi c y * C.chi (((t * y : (ZMod p)ˣ) : ZMod p)) *
            ((starRingEnd ℂ) (S.chi c y) * C.chi (-(y : ZMod p)))
        = (S.chi c t * S.chi c y * (starRingEnd ℂ) (S.chi c y)) *
            (C.chi ((t : ZMod p) * (y : ZMod p)) * C.chi (-(y : ZMod p))) := by
          rw [Units.val_mul]; ring
      _ = S.chi c t * C.chi ((y : ZMod p) * ((t : ZMod p) - 1)) := by rw [hchi, hadd]
  rw [expand, Finset.sum_comm]
  have inner : ∀ t : (ZMod p)ˣ,
      ∑ y : (ZMod p)ˣ, S.chi c t * C.chi ((y : ZMod p) * ((t : ZMod p) - 1))
        = S.chi c t * ((if t = 1 then (p : ℂ) else 0) - 1) := by
    intro t
    rw [← Finset.mul_sum, sum_chi_units C ((t : ZMod p) - 1)]
    congr 2
    refine if_congr ?_ rfl rfl
    constructor
    · intro h
      refine Units.ext ?_
      rw [Units.val_one]
      linear_combination h
    · intro h
      rw [h, Units.val_one]
      ring
  simp_rw [inner]
  have split : ∀ t : (ZMod p)ˣ, S.chi c t * ((if t = 1 then (p : ℂ) else 0) - 1)
      = (if t = 1 then (p : ℂ) * S.chi c t else 0) - S.chi c t := by
    intro t
    by_cases h : t = 1
    · rw [if_pos h, if_pos h]
      ring
    · rw [if_neg h, if_neg h]
      ring
  simp_rw [split]
  rw [Finset.sum_sub_distrib, sum_chi_eq_zero S c c₀ hc₀ hc,
    Finset.sum_ite_eq' Finset.univ (1 : (ZMod p)ˣ) (fun t => (p : ℂ) * S.chi c t)]
  simp [S.chi_one]

/-- The real form: `‖τ(χ)‖² = p` for non-principal `χ`. -/
theorem gaussSum_norm_sq (C : AdditiveCharacterSystem p)
    (S : MulCharSystem (ZMod p)ˣ Ch) (c c₀ : Ch) (hc₀ : S.IsPrincipal c₀) (hc : c ≠ c₀) :
    ‖gaussSumOf C S c‖ ^ 2 = (p : ℝ) := by
  have h := gaussSum_mul_conj C S c c₀ hc₀ hc
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-! ## Dual Parseval over the moving multiplier -/

/-- **Parseval in the multiplier variable** (complex form). -/
theorem character_dual_parseval_complex {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
    (S : MulCharSystem G Ch) (F : Ch → ℂ) :
    ∑ a : G, (∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a)) *
        (starRingEnd ℂ) (∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a))
      = (Fintype.card G : ℂ) * ∑ c : Ch, F c * (starRingEnd ℂ) (F c) := by
  classical
  have expand : ∀ a : G,
      (∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a)) *
        (starRingEnd ℂ) (∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a))
        = ∑ c : Ch, ∑ d : Ch, (F c * (starRingEnd ℂ) (F d)) *
            ((starRingEnd ℂ) (S.chi c a) * S.chi d a) := by
    intro a
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  simp_rw [expand]
  rw [Finset.sum_comm]
  have key : ∀ c : Ch, ∑ a : G, ∑ d : Ch, (F c * (starRingEnd ℂ) (F d)) *
      ((starRingEnd ℂ) (S.chi c a) * S.chi d a)
      = (Fintype.card G : ℂ) * (F c * (starRingEnd ℂ) (F c)) := by
    intro c
    rw [Finset.sum_comm]
    have h : ∀ d : Ch, ∑ a : G, (F c * (starRingEnd ℂ) (F d)) *
        ((starRingEnd ℂ) (S.chi c a) * S.chi d a)
        = (F c * (starRingEnd ℂ) (F d)) * (if d = c then (Fintype.card G : ℂ) else 0) := by
      intro d
      rw [← Finset.mul_sum, ← S.orthogonality d c]
      exact congrArg _ (Finset.sum_congr rfl fun a _ => by ring)
    simp_rw [h, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ c
      (fun d => (F c * (starRingEnd ℂ) (F d)) * (Fintype.card G : ℂ))]
    simp [mul_comm]
  simp_rw [key, ← Finset.mul_sum]

/-- **Parseval in the multiplier variable** (real form). -/
theorem character_dual_parseval_real {G : Type*} [Fintype G] [DecidableEq G] [CommGroup G]
    (S : MulCharSystem G Ch) (F : Ch → ℂ) :
    ∑ a : G, ‖∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a)‖ ^ 2
      = (Fintype.card G : ℝ) * ∑ c : Ch, ‖F c‖ ^ 2 := by
  have h := character_dual_parseval_complex S F
  simp_rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h
  exact_mod_cast h

/-! ## The product residue energy -/

variable {q : ℕ} [NeZero q]

/-- The residue convolution `∑_{m·n ≡ r} α_m β_n`, the exact object appearing in
the product residue energy. -/
noncomputable def residueConvolution (alpha beta : (ZMod q)ˣ → ℂ) (r : ZMod q) : ℂ :=
  ∑ m : (ZMod q)ˣ, ∑ n : (ZMod q)ˣ,
    if (((m * n : (ZMod q)ˣ)) : ZMod q) = r then alpha m * beta n else 0

/-- The convolution on the unit group. -/
noncomputable def unitConvolution (alpha beta : (ZMod q)ˣ → ℂ) (g : (ZMod q)ˣ) : ℂ :=
  ∑ m : (ZMod q)ˣ, alpha m * beta (m⁻¹ * g)

/-- **ProductResidueEnergy** — the exact weighted multiplicative energy

    ∑_{r mod q} | ∑_{m·n ≡ r} α_m β_n |².

Defined exactly; **never estimated** in this bank. -/
noncomputable def productResidueEnergy (alpha beta : (ZMod q)ˣ → ℂ) : ℝ :=
  ∑ r : ZMod q, ‖residueConvolution alpha beta r‖ ^ 2

theorem residueConvolution_unit (alpha beta : (ZMod q)ˣ → ℂ) (g : (ZMod q)ˣ) :
    residueConvolution alpha beta ((g : ZMod q)) = unitConvolution alpha beta g := by
  classical
  unfold residueConvolution unitConvolution
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcond : ∀ n : (ZMod q)ˣ,
      (if (((m * n : (ZMod q)ˣ)) : ZMod q) = ((g : ZMod q)) then alpha m * beta n else 0)
        = (if n = m⁻¹ * g then alpha m * beta n else 0) := by
    intro n
    refine if_congr ?_ rfl rfl
    constructor
    · intro h
      have : m * n = g := Units.ext h
      rw [← this, inv_mul_cancel_left]
    · intro h
      rw [h, mul_inv_cancel_left]
  simp_rw [hcond]
  rw [Finset.sum_ite_eq' Finset.univ (m⁻¹ * g) (fun n => alpha m * beta n)]
  simp

/-- The `hat` transform turns the unit convolution into a product. -/
theorem hat_unitConvolution (S : MulCharSystem (ZMod q)ˣ Ch) (alpha beta : (ZMod q)ˣ → ℂ) (c : Ch) :
    S.hat (unitConvolution alpha beta) c = S.hat alpha c * S.hat beta c := by
  classical
  have lhs : S.hat (unitConvolution alpha beta) c
      = ∑ g : (ZMod q)ˣ, ∑ m : (ZMod q)ˣ,
          alpha m * beta (m⁻¹ * g) * (starRingEnd ℂ) (S.chi c g) := by
    unfold MulCharSystem.hat unitConvolution
    exact Finset.sum_congr rfl fun g _ => Finset.sum_mul _ _ _
  have rhs : S.hat alpha c * S.hat beta c
      = ∑ m : (ZMod q)ˣ, ∑ n : (ZMod q)ˣ,
          (alpha m * (starRingEnd ℂ) (S.chi c m)) * (beta n * (starRingEnd ℂ) (S.chi c n)) := by
    unfold MulCharSystem.hat
    exact Finset.sum_mul_sum _ _ _ _
  rw [lhs, rhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [← Equiv.sum_comp (Equiv.mulLeft m)
    (fun g : (ZMod q)ˣ => alpha m * beta (m⁻¹ * g) * (starRingEnd ℂ) (S.chi c g))]
  refine Finset.sum_congr rfl fun n _ => ?_
  have h : (Equiv.mulLeft m) n = m * n := rfl
  rw [h, inv_mul_cancel_left, S.map_mul, map_mul]
  ring


/-! ## The residue energy is the unit-group energy -/

theorem residueConvolution_zero_eq_zero (alpha beta : (ZMod p)ˣ → ℂ) :
    residueConvolution alpha beta 0 = 0 := by
  classical
  unfold residueConvolution
  refine Finset.sum_eq_zero fun m _ => Finset.sum_eq_zero fun n _ => ?_
  have h : (((m * n : (ZMod p)ˣ)) : ZMod p) ≠ 0 := Units.ne_zero _
  rw [if_neg h]

/-- The product residue energy is exactly the `ℓ²` energy of the unit-group
convolution. -/
theorem productResidueEnergy_eq_unit_energy (alpha beta : (ZMod p)ˣ → ℂ) :
    productResidueEnergy alpha beta
      = ∑ g : (ZMod p)ˣ, ‖unitConvolution alpha beta g‖ ^ 2 := by
  classical
  have h := sum_units_eq_sum_sub_zero (F := ZMod p)
    (fun r => ‖residueConvolution alpha beta r‖ ^ 2)
  simp only [residueConvolution_zero_eq_zero, norm_zero] at h
  have h2 : ∀ g : (ZMod p)ˣ, ‖residueConvolution alpha beta ((g : ZMod p))‖ ^ 2
      = ‖unitConvolution alpha beta g‖ ^ 2 := by
    intro g; rw [residueConvolution_unit]
  unfold productResidueEnergy
  rw [← Finset.sum_congr rfl (fun g (_ : g ∈ Finset.univ) => h2 g), h]
  norm_num

/-- Parseval bridge: the character energy of the product is `|G|` times the
product residue energy. -/
theorem sum_hat_sq_eq_card_mul_energy (S : MulCharSystem (ZMod p)ˣ Ch)
    (alpha beta : (ZMod p)ˣ → ℂ) :
    ∑ c : Ch, ‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2
      = (Fintype.card (ZMod p)ˣ : ℝ) * productResidueEnergy alpha beta := by
  have h := S.character_parseval (unitConvolution alpha beta)
  rw [productResidueEnergy_eq_unit_energy, ← h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hat_unitConvolution S alpha beta c, norm_mul, mul_pow]

/-- The Fourier coefficient at the principal character is the plain sum. -/
theorem hat_principal (S : MulCharSystem (ZMod p)ˣ Ch) (c₀ : Ch) (hc₀ : S.IsPrincipal c₀)
    (R : (ZMod p)ˣ → ℂ) : S.hat R c₀ = ∑ g : (ZMod p)ˣ, R g := by
  unfold MulCharSystem.hat
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [hc₀ g, map_one, mul_one]

/-! ## The exact second moment -/

/-- The value of the moving-multiplier form at the **non-unit** multiplier `0`. -/
theorem movingMultiplier_zero (C : AdditiveCharacterSystem p) (alpha beta : (ZMod p)ˣ → ℂ) :
    movingMultiplier C alpha beta 0
      = -((∑ m : (ZMod p)ˣ, alpha m) * (∑ n : (ZMod p)ˣ, beta n)) := by
  classical
  have hk : ∀ n : (ZMod p)ˣ, C.kloosterman 0 ((n : ZMod p)) = -1 := by
    intro n
    unfold AdditiveCharacterSystem.kloosterman
    have h1 : ∀ u : (ZMod p)ˣ,
        C.chi (0 * ((u : ZMod p)) + ((n : ZMod p)) * (((u⁻¹ : (ZMod p)ˣ) : ZMod p)))
          = C.chi ((((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * ((n : ZMod p))) := by
      intro u; rw [zero_mul, zero_add, mul_comm]
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => h1 u)]
    rw [← Equiv.sum_comp (Equiv.inv (ZMod p)ˣ)
      (fun u : (ZMod p)ˣ => C.chi ((((u⁻¹ : (ZMod p)ˣ) : ZMod p)) * ((n : ZMod p))))]
    have h2 : ∀ u : (ZMod p)ˣ,
        C.chi (((((Equiv.inv (ZMod p)ˣ) u)⁻¹ : (ZMod p)ˣ) : ZMod p) * ((n : ZMod p)))
          = C.chi (((u : ZMod p)) * ((n : ZMod p))) := by
      intro u
      have hu : ((Equiv.inv (ZMod p)ˣ) u)⁻¹ = u := by simp
      rw [hu]
    rw [Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => h2 u), sum_chi_units C ((n : ZMod p))]
    have hn : ((n : ZMod p)) ≠ 0 := Units.ne_zero _
    rw [if_neg hn]
    ring
  unfold movingMultiplier
  have hrow : ∀ m : (ZMod p)ˣ, ∑ n : (ZMod p)ˣ,
      alpha m * beta n * C.kloosterman (0 * ((m : ZMod p))) ((n : ZMod p))
        = -(alpha m * ∑ n : (ZMod p)ˣ, beta n) := by
    intro m
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [zero_mul, hk n]
    ring
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ Finset.univ) => hrow m), Finset.sum_neg_distrib,
    ← Finset.sum_mul]

/-- **EXACT MOVING-`a` SECOND MOMENT, unit multipliers.**

    ∑_{a ∈ (ZMod p)ˣ} |B_a|² = p²·ProductResidueEnergy(α,β) − (p+1)·|∑α|²·|∑β|².

Every constant is *derived* from the repository's own normalisation. -/
theorem movingMultiplier_second_moment_units (C : AdditiveCharacterSystem p)
    (S : MulCharSystem (ZMod p)ˣ Ch) (c₀ : Ch) (hc₀ : S.IsPrincipal c₀)
    (alpha beta : (ZMod p)ˣ → ℂ) :
    ∑ a : (ZMod p)ˣ, ‖movingMultiplier C alpha beta ((a : ZMod p))‖ ^ 2
      = (p : ℝ) ^ 2 * productResidueEnergy alpha beta
        - ((p : ℝ) + 1) * (‖∑ m : (ZMod p)ˣ, alpha m‖ ^ 2 * ‖∑ n : (ZMod p)ˣ, beta n‖ ^ 2) := by
  classical
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hp1 : ((p : ℝ)) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    linarith
  have hcardN : (Fintype.card (ZMod p)ˣ : ℝ) = (p : ℝ) - 1 := by
    rw [ZMod.card_units p]
    have h1 : (1 : ℕ) ≤ p := le_trans (by norm_num) hp2
    push_cast [Nat.cast_sub h1]
    ring
  set N : ℝ := (Fintype.card (ZMod p)ˣ : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set F : Ch → ℂ := fun c => (gaussSumOf C S c) ^ 2 * S.hat alpha c * S.hat beta c with hF
  have hB : ∀ a : (ZMod p)ˣ, movingMultiplier C alpha beta ((a : ZMod p))
      = (1 / (Fintype.card (ZMod p)ˣ : ℂ)) * ∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a) := by
    intro a
    rw [movingMultiplier_bilinear_expand' C S alpha beta a]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [hF]
    ring
  have hsum : ∑ a : (ZMod p)ˣ, ‖movingMultiplier C alpha beta ((a : ZMod p))‖ ^ 2
      = (1 / N) * ∑ c : Ch, ‖F c‖ ^ 2 := by
    have hstep : ∀ a : (ZMod p)ˣ, ‖movingMultiplier C alpha beta ((a : ZMod p))‖ ^ 2
        = (1 / N ^ 2) * ‖∑ c : Ch, F c * (starRingEnd ℂ) (S.chi c a)‖ ^ 2 := by
      intro a
      rw [hB a, norm_mul, mul_pow]
      congr 1
      rw [norm_div, norm_one]
      have hc : ‖((Fintype.card (ZMod p)ˣ : ℂ))‖ = N := by
        rw [hN]
        simp
      rw [hc, div_pow, one_pow]
    rw [Finset.sum_congr rfl (fun a (_ : a ∈ Finset.univ) => hstep a), ← Finset.mul_sum,
      character_dual_parseval_real S F, ← hN]
    rw [← mul_assoc]
    congr 1
    field_simp
  have hFnorm : ∀ c : Ch, ‖F c‖ ^ 2
      = (if c = c₀ then (1 : ℝ) else (p : ℝ) ^ 2) *
          (‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2) := by
    intro c
    have hexp : ‖F c‖ ^ 2
        = (‖gaussSumOf C S c‖ ^ 2) ^ 2 * (‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2) := by
      simp only [hF, norm_mul, norm_pow, mul_pow]
      ring
    rw [hexp]
    by_cases h : c = c₀
    · subst h
      rw [gaussSum_principal C S c hc₀, if_pos rfl]
      norm_num
    · rw [if_neg h, gaussSum_norm_sq C S c c₀ hc₀ h]
  have hsplit : ∑ c : Ch, ‖F c‖ ^ 2
      = (p : ℝ) ^ 2 * (∑ c : Ch, ‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2)
        - ((p : ℝ) ^ 2 - 1) * (‖S.hat alpha c₀‖ ^ 2 * ‖S.hat beta c₀‖ ^ 2) := by
    have hterm : ∀ c : Ch, ‖F c‖ ^ 2
        = (p : ℝ) ^ 2 * (‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2)
          + (if c = c₀ then
              -(((p : ℝ) ^ 2 - 1) * (‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2)) else 0) := by
      intro c
      rw [hFnorm c]
      by_cases h : c = c₀
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [Finset.sum_congr rfl (fun c (_ : c ∈ Finset.univ) => hterm c), Finset.sum_add_distrib,
      Finset.sum_ite_eq' Finset.univ c₀
        (fun c => -(((p : ℝ) ^ 2 - 1) * (‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2)))]
    simp only [Finset.mem_univ, if_true, ← Finset.mul_sum]
    ring
  have hE : ∑ c : Ch, ‖S.hat alpha c‖ ^ 2 * ‖S.hat beta c‖ ^ 2
      = N * productResidueEnergy alpha beta := sum_hat_sq_eq_card_mul_energy S alpha beta
  have hprinc : ‖S.hat alpha c₀‖ ^ 2 * ‖S.hat beta c₀‖ ^ 2
      = ‖∑ m : (ZMod p)ˣ, alpha m‖ ^ 2 * ‖∑ n : (ZMod p)ˣ, beta n‖ ^ 2 := by
    rw [hat_principal S c₀ hc₀ alpha, hat_principal S c₀ hc₀ beta]
  rw [hsum, hsplit, hE, hprinc, hcardN]
  field_simp
  ring

/-- **EXACT MOVING-`a` SECOND MOMENT, all residues.**

    ∑_{a mod p} |B_a|² = p²·ProductResidueEnergy(α,β) − p·|∑α|²·|∑β|².

Obtained from the unit version by adding the exactly computed term at `a = 0`. -/
theorem movingMultiplier_second_moment_all (C : AdditiveCharacterSystem p)
    (S : MulCharSystem (ZMod p)ˣ Ch) (c₀ : Ch) (hc₀ : S.IsPrincipal c₀)
    (alpha beta : (ZMod p)ˣ → ℂ) :
    ∑ a : ZMod p, ‖movingMultiplier C alpha beta a‖ ^ 2
      = (p : ℝ) ^ 2 * productResidueEnergy alpha beta
        - (p : ℝ) * (‖∑ m : (ZMod p)ˣ, alpha m‖ ^ 2 * ‖∑ n : (ZMod p)ˣ, beta n‖ ^ 2) := by
  classical
  have hsplit := sum_units_eq_sum_sub_zero (F := ZMod p)
    (fun a => ‖movingMultiplier C alpha beta a‖ ^ 2)
  have hzero : ‖movingMultiplier C alpha beta 0‖ ^ 2
      = ‖∑ m : (ZMod p)ˣ, alpha m‖ ^ 2 * ‖∑ n : (ZMod p)ˣ, beta n‖ ^ 2 := by
    rw [movingMultiplier_zero C alpha beta, norm_neg, norm_mul, mul_pow]
  simp only [hzero] at hsplit
  rw [movingMultiplier_second_moment_units C S c₀ hc₀ alpha beta] at hsplit
  linarith [hsplit]

end Gate1B.SafeAlgebra
