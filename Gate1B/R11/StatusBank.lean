/-
# Gate1B / R11 : status bank and physical-caller firewall

This module is the machine-checked ledger of the present formal banking run.  Each `bank_*`
declaration below is a *type ascription* of an already-proved theorem, so the kernel
re-checks that the claimed status matches an actual proof.  Nothing new is proved here.

The second half is the **firewall**: the physical obligations are recorded as explicit
propositions and are deliberately left uninhabited.  In particular

* `PhysicalHilbertCaller` — that a physical `Ω(kd−2)` source *is* a reciprocal Hilbert
  packet of the finite abstract shape — is never inhabited;
* `VectorMobiusPhysicalBound` and `GlobalModeLedger` are never inhabited;
* no theorem of this layer asserts global Gate 1B, full R11, or twin primes.

What *is* proved is the transport lemma: **if** a target were exhibited as a finite Hilbert
packet, **then** the kernel-proved HMRD bound would apply to it.  That is a conditional, and
its hypothesis is exactly the open obligation.
-/
import Gate1B.R11.VaughanCharts
import Gate1B.R11.Polytope611
import Gate1B.R11.CutoffConservation
import Gate1B.R11.Reciprocity
import Gate1B.R11.Bruhat
import Gate1B.R11.AffineParametrization
import Gate1B.HilbertHMRD.Core

namespace Gate1B.R11

open ArithmeticFunction Gate1B.HilbertHMRD

/-! ## 1. Kernel-proved ledger -/

/-- VAUGHAN IDENTITY: KERNEL-PROVED. -/
theorem bank_vaughan_identity :
    ∀ U V : ℕ, (vonMangoldt : ArithmeticFunction ℝ)
      = truncLE V vonMangoldt + truncLE U muR * ArithmeticFunction.log
        - truncLE U muR * truncLE V vonMangoldt * zetaR
        + truncGT U muR * truncGT V vonMangoldt * zetaR := vaughan_identity

/-- V*=2 MOBIUS-LOG: KERNEL-PROVED. -/
theorem bank_vTwo_mobius_log :
    ∀ {N : ℕ}, Odd N → ∀ U : ℕ, vonMangoldt N
      = (∑ d ∈ N.divisors.filter (fun d => d ≤ U), (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ))
        + ∑ d ∈ N.divisors.filter (fun d => U < d),
            (moebius d : ℝ) * Real.log ((N / d : ℕ) : ℝ) :=
  fun hN U => vTwo_vaughan_eq_mobius_log_split hN U

/-- FOUR-LANE = LONG-MOBIUS AT V=2: KERNEL-PROVED (literal equality). -/
theorem bank_chart_equivalence : ∀ U N : ℕ, FourLaneValue U 2 N = LongMobiusValue U N :=
  fourLaneValue_eq_longMobiusValue

/-- POLYTOPE `M ≤ 5/11` and UNIFORM `6/11`: KERNEL-PROVED. -/
theorem bank_polytope_611 :
    ∀ v : ExponentVector, v.Mblock ≤ 5 / 11 ∧ 6 / 11 ≤ 1 - v.Mblock ∧ 2 / 11 ≤ v.Lblock
      ∧ v.Mblock + v.Nblock + v.Lblock = 1 :=
  fun v => ⟨v.Mblock_le, v.one_sub_Mblock_ge, v.Lblock_ge, v.block_sum⟩

/-- PASCADI EXPONENT ARITHMETIC: KERNEL-PROVED as a finite rational dictionary only
(no analytic discrepancy estimate is stated or used). -/
theorem bank_pascadi_dictionary :
    ∀ v : ExponentVector,
      PascadiExponentConditions v.Mblock v.Nblock v.Lblock (1 - v.Mblock) (7 / 32) :=
  pascadi_conditions_of_polytope

/-- LONG-MOBIUS REINDEXING: KERNEL-PROVED. -/
theorem bank_longMobius_reindexing :
    ∀ {N : ℕ}, N ≠ 0 → ∀ U : ℕ, longMobiusLog U N
      = ∑ k ∈ N.divisors.filter (fun k => U < N / k),
          (moebius (N / k) : ℝ) * Real.log (k : ℝ) :=
  fun hN U => longMobiusLog_reindex hN U

/-- `A·B − k·d = −2`: KERNEL-PROVED. -/
theorem bank_determinant :
    ∀ {A B k d : ℕ}, A * B + 2 = k * d → (A : ℤ) * (B : ℤ) - (k : ℤ) * (d : ℤ) = -2 :=
  fun h => determinant_eq_neg_two h

/-- FOUR CROSS-GCDs: KERNEL-PROVED. -/
theorem bank_cross_gcds :
    ∀ {A B k d : ℕ}, Odd A → Odd B → A * B + 2 = k * d →
      Nat.gcd A k = 1 ∧ Nat.gcd A d = 1 ∧ Nat.gcd B k = 1 ∧ Nat.gcd B d = 1 :=
  fun hA hB h => determinant_pairwise_cross_coprime hA hB h

/-- AFFINE `t`-PARAMETRIZATION: KERNEL-PROVED (exact characterisation). -/
theorem bank_affine_parametrization :
    ∀ {A k B0 d0 : ℤ}, k ≠ 0 → IsCoprime k A → A * B0 + 2 = k * d0 → ∀ B d : ℤ,
      (A * B + 2 = k * d ↔ ∃! t : ℤ, B = B0 + k * t ∧ d = d0 + A * t) :=
  fun hk hcop h0 B d => determinant_minusTwo_solution_parametrization hk hcop h0 B d

/-- `KT = B` CONSERVATION: KERNEL-PROVED at the exponent level and as real powers. -/
theorem bank_cutoff_conservation :
    (∀ a u : ℚ, a + (u - a) = u ∧ (1 - u) + (u - a) = 1 - a ∧ u + (1 - u) = 1 ∧ a + (1 - a) = 1)
      ∧ ∀ {X : ℝ}, 0 < X → ∀ a u : ℝ,
        X ^ a * X ^ (u - a) = X ^ u ∧ X ^ (1 - u) * X ^ (u - a) = X ^ (1 - a) ∧
          X ^ u * X ^ (1 - u) = X ∧ X ^ a * X ^ (1 - a) = X :=
  ⟨exponent_conservation, fun hX a u => rpow_conservation hX a u⟩

/-- HYBRID MIN-LEMMA: KERNEL-PROVED. -/
theorem bank_hybrid_min :
    ∀ {a b K T B : ℝ}, 0 < a → 0 < b → 0 < K → 0 < T → 0 < B → K * T = B →
      min (T ^ (-a)) (K ^ (-b)) ≤ B ^ (-(a * b) / (a + b)) :=
  fun ha hb hK hT hB hKT => hybrid_min_le ha hb hK hT hB hKT

/-- RECIPROCITY: KERNEL-PROVED (in `ℝ/ℤ` and in exponential form, at the fixed shift `2`). -/
theorem bank_reciprocity :
    ∀ {A k A' k' : ℤ}, A ≠ 0 → k ≠ 0 → IsCoprime A k → k ∣ A * A' - 1 → A ∣ k * k' - 1 →
      ∀ h : ℤ, eMod k (-2 * h * A') = eMod A (2 * h * k') * eMod (A * k) (-2 * h) :=
  fun hA hk hcop hA' hk' h => reciprocity_exp hA hk hcop hA' hk' h

/-- SL2 BRUHAT: KERNEL-PROVED exactly as claimed (no sign or order repair was needed). -/
theorem bank_bruhat :
    ∀ {R : Type} [CommRing R] {A B k d lam dinv : R}, A * B - k * d = -2 → lam * (-2) = 1 →
      d * dinv = 1 →
      rescaled lam A k d B
        = bruhatU (lam * A * dinv) * bruhatD dinv d * bruhatS * bruhatU (B * dinv) :=
  fun hdet hlam hdinv => bruhat_factorisation hdet hlam hdinv

/-- TENSOR OPERATOR STABILITY: KERNEL-PROVED (both directions). -/
theorem bank_tensor_stability :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
      {I J : Type} [Fintype I] [Fintype J] (T : J → I → ℂ) (C : ℝ) (e : H), ‖e‖ = 1 →
      (HilbertL2Bound H T C ↔ ScalarL2Bound T C) :=
  fun T C e he => operatorNorm_tensor_identity_hilbert T C e he

/-- HILBERT-HMRD, both branches and their minimum: KERNEL-PROVED (finite, abstract). -/
theorem bank_hilbert_hmrd :
    ∀ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
      {s : ℕ} [NeZero s] (Dset Wset : Finset ℕ) (al be : ℕ → ℂ) (u v : ℕ → H)
      (xr yr : ℕ → ZMod s) (f : ZMod s → ℂ),
      (∀ x, ¬ IsUnit x → f x = 0) → (∀ x, ‖f x‖ ≤ 1) → ∀ P B1 : ℝ,
      (∀ m : ZMod s, ‖∑ d ∈ Dset, (al d * ez s (m * xr d)) • u d‖ ≤ P) →
      (∑ w ∈ Wset, ‖be w‖ * ‖v w‖ ≤ B1) →
      ∀ (A : ZMod s), IsUnit A → ∀ pin qin : ℕ → ZMod s,
      (∀ d ∈ Dset, ∀ w ∈ Wset, f (xr d * yr w) = ez s (A * (pin d * qin w))) →
      ∀ cD cW : ℝ,
      (∀ z : ZMod s, ((Dset.filter (fun d => pin d = z)).card : ℝ) ≤ cD) →
      (∀ z : ZMod s, ((Wset.filter (fun w => qin w = z)).card : ℝ) ≤ cW) →
      ‖packet s Dset Wset al be u v xr yr f‖
        ≤ min (Real.sqrt (Nat.totient s) * (P * B1))
            (Real.sqrt ((s : ℝ) * cD * cW)
              * (Real.sqrt (∑ d ∈ Dset, ‖al d‖ ^ 2 * ‖u d‖ ^ 2)
                * Real.sqrt (∑ w ∈ Wset, ‖be w‖ ^ 2 * ‖v w‖ ^ 2))) :=
  fun Dset Wset al be u v xr yr f hsupp hb P B1 hP hB1 A hA pin qin hphase cD cW hcD hcW =>
    packet_hmrd Dset Wset al be u v xr yr f hsupp hb P B1 hP hB1 A hA pin qin hphase cD cW hcD hcW

/-! ## 2. Physical-caller firewall (open obligations, deliberately uninhabited) -/

section Firewall

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The property of *being* a finite reciprocal Hilbert packet of the abstract shape, with a
unimodular phase supported on the units. -/
def IsHilbertPacket (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (s : ℕ)
    [NeZero s] (T : ℂ) : Prop :=
  ∃ (Dset Wset : Finset ℕ) (al be : ℕ → ℂ) (u v : ℕ → H) (xr yr : ℕ → ZMod s)
    (f : ZMod s → ℂ), (∀ x, ¬ IsUnit x → f x = 0) ∧ (∀ x, ‖f x‖ ≤ 1) ∧
      T = packet s Dset Wset al be u v xr yr f

/-- **OPEN OBLIGATION — the physical caller.**  That a physical source value `T` (e.g. one
built from `Ω(kd−2)`) is literally a finite reciprocal Hilbert packet.  This structure is
never inhabited in this development: no theorem here constructs a `PhysicalHilbertCaller`. -/
structure PhysicalHilbertCaller (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (s : ℕ) [NeZero s] (T : ℂ) : Prop where
  /-- The factorisation of the physical source as an abstract packet. -/
  factorisation : IsHilbertPacket H s T

/-- **Transport lemma (conditional).**  If a target is exhibited as a finite Hilbert packet
whose data satisfy the small-branch hypotheses, the kernel-proved HMRD small branch applies.
The hypothesis is exactly the open obligation: nothing here supplies it. -/
theorem hmrd_applies_of_physicalCaller {s : ℕ} [NeZero s] {T : ℂ}
    (hT : PhysicalHilbertCaller H s T) :
    ∃ (Dset : Finset ℕ) (Wset : Finset ℕ) (al be : ℕ → ℂ) (u v : ℕ → H)
      (xr yr : ℕ → ZMod s) (f : ZMod s → ℂ),
      T = packet s Dset Wset al be u v xr yr f ∧
        ∀ P B1 : ℝ, (∀ m : ZMod s, ‖∑ d ∈ Dset, (al d * ez s (m * xr d)) • u d‖ ≤ P) →
          (∑ w ∈ Wset, ‖be w‖ * ‖v w‖ ≤ B1) →
          ‖T‖ ≤ Real.sqrt (Nat.totient s) * (P * B1) := by
  obtain ⟨Dset, Wset, al, be, u, v, xr, yr, f, hsupp, hb, hTeq⟩ := hT.factorisation
  refine ⟨Dset, Wset, al, be, u, v, xr, yr, f, hTeq, ?_⟩
  intro P B1 hP hB1
  rw [hTeq]
  exact packet_small_branch Dset Wset al be u v xr yr f hsupp hb P B1 hP hB1

/-- **OPEN OBLIGATION — the physical vector-Möbius bound.**  A power saving for the physical
vector-valued Möbius sum.  Never inhabited here. -/
structure VectorMobiusPhysicalBound (Sfun : ℕ → H) (X eta : ℝ) : Prop where
  /-- The claimed power saving. -/
  saving : ‖∑ n ∈ Finset.range ⌈X⌉₊, Sfun n‖ ≤ X ^ (1 - eta)

/-- **OPEN OBLIGATION — the global mode ledger.**  That a declared list of modes exhausts
the global budget.  Never inhabited here. -/
structure GlobalModeLedger (modes : Finset ℕ) (weight : ℕ → ℝ) (budget : ℝ) : Prop where
  /-- Exhaustiveness of the declared modes. -/
  exhaustive : ∑ m ∈ modes, weight m = budget
  /-- No mode carries negative weight. -/
  nonneg : ∀ m ∈ modes, 0 ≤ weight m

end Firewall

end Gate1B.R11
