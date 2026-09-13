/-
# Gate1B / R11 / Frontier : the original occupied-row arithmetic kernel

The new current live first-moment architecture is based on the **original occupied arithmetic
rows**.  This module formalises that source exactly, with no analytic input.

For a row `i`:

* `rowAverage I ξ = |I|⁻¹ ∑_{v ∈ I} e_Q(−ξ v)` — the average of the additive character over the
  **actual row interval** `I` (not an idealised one);
* `freqMask R v = ∑_{ξ ∈ maskSet} c(ξ) · A_i(ξ) · e_Q(ξ v)` — the frequency mask built from those
  row averages;
* `arithFactor` retains the two arithmetic modes:
  * **far mode**: the progression `n ≡ a_i (mod q_i)`,
  * **medium mode**: the factor `η_q(n)/φ(q_i)`;
* `Gamma R v n = freqMask R v · arithFactor R n · phase R v n · endpoint R n` — mask, arithmetic
  mode, actual arithmetic phase and row endpoint;
* `Dpre R N v = ∑_n μ_odd(n) Γ_i(v,n)` and `Drow R N = bPerp I (Dpre R N)` — the row kernel with
  **mean subtraction** over the row interval (the projection `bPerp` is reused from the existing
  mean-zero module, not duplicated).

Kernel-proved: the exact mode expansions, the odd-support reduction, the vanishing of the row
mean, the full-mask evaluation `∑_ξ A_i(ξ) e_Q(ξ v) = (Q/|I|)·1_I(v)`, and the finite-sum
reassembly of a family of rows.  **No extra analytic cancellation is assumed**: the final section
exhibits admissible row data for which the trivial triangle bound is attained.
-/
import Gate1B.R11.Frontier.MeanZeroFourier
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

namespace Gate1B.R11.Frontier

open Finset Gate1B.HilbertHMRD Universal.D0WP

noncomputable section

variable {Q : ℕ} [NeZero Q]

/-! ## 1. Row averages of the additive character -/

/-- `A_i(ξ)`: the average of `e_Q(−ξ v)` over the **actual** row interval `I`. -/
def rowAverage (I : Finset (ZMod Q)) (xi : ZMod Q) : ℂ :=
  (I.card : ℂ)⁻¹ * ∑ v ∈ I, ez Q (-(xi * v))

/-- `A_i(0) = 1` on a nonempty row. -/
theorem rowAverage_zero (I : Finset (ZMod Q)) (hI : I.Nonempty) : rowAverage I 0 = 1 := by
  have hcard : (I.card : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_pos.mpr hI).ne'
  rw [rowAverage]
  have : ∀ v ∈ I, ez Q (-((0 : ZMod Q) * v)) = 1 := by
    intro v _; simp
  rw [Finset.sum_congr rfl this, Finset.sum_const, nsmul_eq_mul, mul_one,
    inv_mul_cancel₀ hcard]

/-! ## 2. The occupied-row source object -/

/-- The two arithmetic modes retained by the source. -/
inductive RowMode
  /-- Far mode: an actual progression `n ≡ a_i (mod q_i)`. -/
  | far
  /-- Medium mode: the factor `η_q(n)/φ(q_i)`. -/
  | medium
  deriving DecidableEq, Repr

/-- An **original occupied arithmetic row**. -/
structure OccupiedRow (Q : ℕ) where
  /-- The actual row interval. -/
  I : Finset (ZMod Q)
  /-- The row interval is nonempty. -/
  I_nonempty : I.Nonempty
  /-- The arithmetic mode. -/
  mode : RowMode
  /-- The frequency mask support. -/
  maskSet : Finset (ZMod Q)
  /-- The frequency mask coefficients. -/
  maskCoef : ZMod Q → ℂ
  /-- The row modulus `q_i`. -/
  q : ℕ
  /-- The modulus is positive. -/
  q_pos : 0 < q
  /-- The residue `a_i` of the far mode. -/
  a : ℕ
  /-- The medium-mode weight `η_q`. -/
  eta : ℕ → ℂ
  /-- The actual arithmetic phase. -/
  phase : ZMod Q → ℕ → ℂ
  /-- The row endpoint weight. -/
  endpoint : ℕ → ℂ

variable (R : OccupiedRow Q)

/-- The frequency mask of the row, built from the actual row averages `A_i(ξ)`. -/
def freqMask (v : ZMod Q) : ℂ :=
  ∑ xi ∈ R.maskSet, R.maskCoef xi * rowAverage R.I xi * ez Q (xi * v)

/-- The arithmetic factor of the row, in the two retained modes. -/
def arithFactor (n : ℕ) : ℂ :=
  match R.mode with
  | RowMode.far => if n % R.q = R.a % R.q then 1 else 0
  | RowMode.medium => R.eta n / (R.q.totient : ℂ)

/-- `Γ_i(v, n)`: mask × arithmetic mode × actual arithmetic phase × row endpoint. -/
def Gamma (v : ZMod Q) (n : ℕ) : ℂ :=
  freqMask R v * arithFactor R n * R.phase v n * R.endpoint n

/-- The odd Möbius coefficient `μ_odd(n)`. -/
def muOdd (n : ℕ) : ℂ := if Odd n then (ArithmeticFunction.moebius n : ℂ) else 0

theorem muOdd_even {n : ℕ} (hn : ¬ Odd n) : muOdd n = 0 := if_neg hn

/-- The row kernel **before** mean subtraction, `∑_n μ_odd(n) Γ_i(v,n)`. -/
def Dpre (N : Finset ℕ) (v : ZMod Q) : ℂ := ∑ n ∈ N, muOdd n * Gamma R v n

/-- The row kernel `D_i`, i.e. `Dpre` with mean subtraction over the actual row interval. -/
def Drow (N : Finset ℕ) : ZMod Q → ℂ := bPerp R.I (Dpre R N)

/-! ## 3. Exact expansions -/

omit [NeZero Q] in
/-- The mask factors out of the `n`-sum. -/
theorem Dpre_eq_mask_mul (N : Finset ℕ) (v : ZMod Q) :
    Dpre R N v
      = freqMask R v * ∑ n ∈ N, muOdd n * arithFactor R n * R.phase v n * R.endpoint n := by
  rw [Dpre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Gamma]; ring

omit [NeZero Q] in
/-- **FAR MODE.**  The arithmetic factor is exactly the progression restriction. -/
theorem Dpre_far (hmode : R.mode = RowMode.far) (N : Finset ℕ) (v : ZMod Q) :
    Dpre R N v = freqMask R v *
      ∑ n ∈ N.filter (fun n => n % R.q = R.a % R.q), muOdd n * R.phase v n * R.endpoint n := by
  rw [Dpre_eq_mask_mul]
  congr 1
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [arithFactor, hmode]
  by_cases h : n % R.q = R.a % R.q <;> simp [h]

omit [NeZero Q] in
/-- **MEDIUM MODE.**  The arithmetic factor is exactly `η_q(n)/φ(q_i)`. -/
theorem Dpre_medium (hmode : R.mode = RowMode.medium) (N : Finset ℕ) (v : ZMod Q) :
    Dpre R N v = freqMask R v *
      ((R.q.totient : ℂ)⁻¹ * ∑ n ∈ N, muOdd n * R.eta n * R.phase v n * R.endpoint n) := by
  rw [Dpre_eq_mask_mul]
  congr 1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [arithFactor, hmode]
  ring

omit [NeZero Q] in
/-- **ODD SUPPORT.**  Only odd `n` contribute. -/
theorem Dpre_odd_support (N : Finset ℕ) (v : ZMod Q) :
    Dpre R N v = ∑ n ∈ N.filter (fun n => Odd n), muOdd n * Gamma R v n := by
  rw [Dpre, Finset.sum_filter]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases h : Odd n
  · simp [h]
  · simp [h, muOdd_even h]

/-! ## 4. Mean subtraction and the row endpoint -/

omit [NeZero Q] in
/-- **MEAN SUBTRACTION.**  The row kernel has vanishing mean over the actual row interval. -/
theorem Drow_mean_zero (N : Finset ℕ) : ∑ v ∈ R.I, Drow R N v = 0 :=
  sum_bPerp_interval R.I (Dpre R N) R.I_nonempty

omit [NeZero Q] in
/-- The row kernel vanishes off the actual row interval: no value is invented outside the row. -/
theorem Drow_off_row (N : Finset ℕ) {v : ZMod Q} (hv : v ∉ R.I) : Drow R N v = 0 :=
  bPerp_of_not_mem hv

omit [NeZero Q] in
/-- On the row, `D_i` is exactly the source value minus the row mean. -/
theorem Drow_on_row (N : Finset ℕ) {v : ZMod Q} (hv : v ∈ R.I) :
    Drow R N v = Dpre R N v - lineMean R.I (Dpre R N) := if_pos hv

/-! ## 5. Full-mask evaluation -/

/-- **FULL-MASK IDENTITY.**  With the complete frequency mask and unit coefficients, the mask
built from the actual row averages is exactly `(Q/|I|)` times the indicator of the row interval.
(For a *proper* mask this fails; see `CriticalMaskFirewall`.) -/
theorem freqMask_univ (hmask : R.maskSet = Finset.univ) (hcoef : ∀ xi, R.maskCoef xi = 1)
    (v : ZMod Q) :
    freqMask R v = (R.I.card : ℂ)⁻¹ * (Q : ℂ) * (if v ∈ R.I then 1 else 0) := by
  have hterm : ∀ xi : ZMod Q, R.maskCoef xi * rowAverage R.I xi * ez Q (xi * v)
      = (R.I.card : ℂ)⁻¹ * ∑ v' ∈ R.I, ez Q (xi * (v - v')) := by
    intro xi
    rw [hcoef, one_mul, rowAverage, mul_assoc, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun v' _ => ?_
    rw [← ez_add]
    congr 1
    ring
  have hinner : ∀ v' ∈ R.I, ∑ xi : ZMod Q, ez Q (xi * (v - v'))
      = if v' = v then (Q : ℂ) else 0 := by
    intro v' _
    rw [show ∑ xi : ZMod Q, ez Q (xi * (v - v')) = ∑ xi : ZMod Q, ez Q ((v - v') * xi) from
      Finset.sum_congr rfl fun xi _ => by rw [mul_comm], sum_ez_orth]
    by_cases h : v' = v
    · rw [if_pos h, h, sub_self, if_pos rfl]
    · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h))]
  rw [freqMask, hmask,
    Finset.sum_congr rfl (fun xi (_ : xi ∈ (Finset.univ : Finset (ZMod Q))) => hterm xi),
    ← Finset.mul_sum, Finset.sum_comm, Finset.sum_congr rfl hinner,
    Finset.sum_ite_eq' R.I v (fun _ => (Q : ℂ))]
  by_cases hv : v ∈ R.I
  · rw [if_pos hv, if_pos hv, mul_one]
  · rw [if_neg hv, if_neg hv, mul_zero, mul_zero]

/-! ## 6. Reassembly of a family of rows -/

/-- The total pre-mean source of a finite family of occupied rows. -/
def DpreTotal {ι : Type*} (rows : Finset ι) (R : ι → OccupiedRow Q) (N : Finset ℕ)
    (v : ZMod Q) : ℂ := ∑ i ∈ rows, Dpre (R i) N v

omit [NeZero Q] in
/-- **REASSEMBLY (finite-sum identity).**  The total source is the double finite sum of the
per-row kernels, in either order.  No cancellation is claimed or used. -/
theorem DpreTotal_eq_double_sum {ι : Type*} (rows : Finset ι) (R : ι → OccupiedRow Q)
    (N : Finset ℕ) (v : ZMod Q) :
    DpreTotal rows R N v = ∑ n ∈ N, ∑ i ∈ rows, muOdd n * Gamma (R i) v n := by
  rw [DpreTotal, Finset.sum_comm]
  rfl

omit [NeZero Q] in
/-- The mean-subtracted total over a family of rows **sharing** the same row interval. -/
theorem DrowTotal_of_common_interval {ι : Type*} (rows : Finset ι) (R : ι → OccupiedRow Q)
    (N : Finset ℕ) (I : Finset (ZMod Q)) (hI : ∀ i ∈ rows, (R i).I = I) (v : ZMod Q) :
    ∑ i ∈ rows, Drow (R i) N v = bPerp I (DpreTotal rows R N) v := by
  have hmean : lineMean I (DpreTotal rows R N) = ∑ i ∈ rows, lineMean I (Dpre (R i) N) := by
    simp only [lineMean, DpreTotal, ← Finset.mul_sum]
    congr 1
    exact Finset.sum_comm
  by_cases hv : v ∈ I
  · have hterm : ∀ i ∈ rows, Drow (R i) N v = Dpre (R i) N v - lineMean I (Dpre (R i) N) := by
      intro i hi
      rw [Drow, bPerp, hI i hi, if_pos hv]
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, bPerp, if_pos hv, hmean]
    rfl
  · rw [bPerp_of_not_mem hv]
    refine Finset.sum_eq_zero fun i hi => ?_
    exact Drow_off_row (R i) N (by rw [hI i hi]; exact hv)

/-! ## 7. Firewall: no analytic cancellation is assumed -/

/-- An explicit admissible row: the full mask on `ZMod 2`, far mode with modulus `1`, unit phase
and unit endpoint. -/
def testRowDatum : OccupiedRow 2 where
  I := Finset.univ
  I_nonempty := ⟨0, Finset.mem_univ _⟩
  mode := RowMode.far
  maskSet := {0}
  maskCoef := fun _ => 1
  q := 1
  q_pos := Nat.one_pos
  a := 0
  eta := fun _ => 0
  phase := fun _ _ => 1
  endpoint := fun _ => 1

/-- **NO FREE CANCELLATION.**  For admissible source data the trivial triangle bound is attained:
the reassembly identity by itself provides no saving whatsoever. -/
theorem testRowDatum_freqMask : freqMask testRowDatum (0 : ZMod 2) = 1 := by
  rw [freqMask, show testRowDatum.maskSet = {0} from rfl, Finset.sum_singleton,
    show testRowDatum.maskCoef 0 = 1 from rfl, one_mul,
    rowAverage_zero testRowDatum.I testRowDatum.I_nonempty, zero_mul, ez_zero, mul_one]

theorem testRowDatum_arith : arithFactor testRowDatum 1 = 1 := by
  simp [arithFactor, testRowDatum]

theorem muOdd_one : muOdd 1 = 1 := by
  simp [muOdd]

/-- **NO FREE CANCELLATION.**  For admissible source data the trivial triangle bound is attained:
the reassembly identity by itself provides no saving whatsoever. -/
theorem reassembly_has_no_free_cancellation :
    ∃ (Rw : OccupiedRow 2) (N : Finset ℕ) (v : ZMod 2),
      ‖Dpre Rw N v‖ = ∑ n ∈ N, ‖muOdd n * Gamma Rw v n‖ ∧ Dpre Rw N v ≠ 0 := by
  refine ⟨testRowDatum, {1}, 0, ?_, ?_⟩
  · rw [Dpre, Finset.sum_singleton, Finset.sum_singleton]
  · rw [Dpre, Finset.sum_singleton, Gamma, testRowDatum_freqMask, testRowDatum_arith, muOdd_one,
      show testRowDatum.phase 0 1 = 1 from rfl, show testRowDatum.endpoint 1 = 1 from rfl]
    norm_num

end

end Gate1B.R11.Frontier
