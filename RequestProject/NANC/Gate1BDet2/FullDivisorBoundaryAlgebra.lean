import Mathlib

/-!
# Gate 1B / determinant-2 bank, Module 38: full divisor-boundary algebra

The classical exact convolution identities at the divisor boundary, in
Mathlib's `ArithmeticFunction` convention (`*` is Dirichlet convolution, `1` is
the delta function `δ_{n=1}`, and `↑zeta` is the constant-one function):

* `moebius_pmul_log`  :  `μ · log = − (μ * Λ)`  (pointwise product on the left);
* `moebius_mul_vonMangoldt_apply` : `(μ * Λ)(n) = − μ(n) log n`;
* `zeta_mul_moebius_mul_vonMangoldt` : `ζ * (μ * Λ) = Λ`, i.e. the requested
  `1 * (μ * Λ) = Λ` with `1` read as the constant-one arithmetic function.

The engine is the exact **logarithmic derivation identity**
`log_deriv : (f * g) · log = (f · log) * g + f * (g · log)`, proved from
`log (d e) = log d + log e` on the divisor antidiagonal.  An abstract
weighted-prime version `additive_weight_deriv` (any additive weight `L` valued
in a commutative ring) is banked as well, so nothing here depends on choosing
`Real.log`.

**Proof-theoretic guard.**  The divisor-boundary identity is exact algebra and
does *not* imply hard Gate-1B packet closure: see
`divisor_boundary_identity_does_not_imply_packet_closure`.  The propositions
`SourceExpectedTermIdentified` and `SourceZeroModeReconciled` are declared as
ordinary interfaces and are never inhabited.
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Boundary

open ArithmeticFunction ArithmeticFunction.Moebius

/-! ## 1. The logarithmic derivation identity -/

/-- **Derivation identity.**  Pointwise multiplication by `log` is a derivation
for Dirichlet convolution. -/
theorem log_deriv (f g : ArithmeticFunction ℝ) :
    (f * g).pmul ArithmeticFunction.log
      = (f.pmul ArithmeticFunction.log) * g + f * (g.pmul ArithmeticFunction.log) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · simp only [pmul_apply, mul_apply, add_apply, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    rw [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hne : x.1 * x.2 ≠ 0 := by rw [hx1]; exact hx2
    have hd : x.1 ≠ 0 := (Nat.mul_ne_zero_iff.1 hne).1
    have he : x.2 ≠ 0 := (Nat.mul_ne_zero_iff.1 hne).2
    have hlog : (ArithmeticFunction.log : ArithmeticFunction ℝ) n
        = ArithmeticFunction.log x.1 + ArithmeticFunction.log x.2 := by
      simp only [log_apply, ← hx1]
      push_cast
      rw [Real.log_mul (by exact_mod_cast hd) (by exact_mod_cast he)]
    rw [hlog]
    ring

/-- **Abstract weighted-prime version.**  For any additive weight `L` with
`L(d e) = L d + L e` on nonzero arguments, the same derivation identity holds
pointwise, in an arbitrary commutative ring.  (No `Real.log` is used; and no
hypothesis `n ≠ 0` is needed, the antidiagonal of `0` being empty.) -/
theorem additive_weight_deriv {R : Type*} [CommRing R] (L : ℕ → R)
    (hL : ∀ d e : ℕ, d ≠ 0 → e ≠ 0 → L (d * e) = L d + L e)
    (f g : ArithmeticFunction R) (n : ℕ) :
    (f * g) n * L n
      = ∑ x ∈ n.divisorsAntidiagonal, ((f x.1 * L x.1) * g x.2 + f x.1 * (g x.2 * L x.2)) := by
  rw [mul_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Nat.mem_divisorsAntidiagonal] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hne : x.1 * x.2 ≠ 0 := by rw [hx1]; exact hx2
  have hd : x.1 ≠ 0 := (Nat.mul_ne_zero_iff.1 hne).1
  have he : x.2 ≠ 0 := (Nat.mul_ne_zero_iff.1 hne).2
  have : L n = L x.1 + L x.2 := by rw [← hx1]; exact hL _ _ hd he
  rw [this]
  ring

/-! ## 2. The divisor-boundary identities -/

/-- **`μ · log = − (μ * Λ)`.** -/
theorem moebius_pmul_log :
    ((μ : ArithmeticFunction ℝ)).pmul ArithmeticFunction.log
      = - ((μ : ArithmeticFunction ℝ) * Λ) := by
  have key := log_deriv (μ : ArithmeticFunction ℝ) (↑zeta : ArithmeticFunction ℝ)
  rw [coe_moebius_mul_coe_zeta] at key
  have h1 : ((1 : ArithmeticFunction ℝ)).pmul ArithmeticFunction.log = 0 := by
    ext n
    by_cases hn : n = 1
    · subst hn; simp [pmul_apply]
    · simp [pmul_apply, ArithmeticFunction.one_apply_ne hn]
  have h2 : ((↑zeta : ArithmeticFunction ℝ)).pmul ArithmeticFunction.log
      = ArithmeticFunction.log := by
    rw [pmul_comm]; exact pmul_zeta _
  rw [h1, h2] at key
  have h3 : (μ : ArithmeticFunction ℝ) * ArithmeticFunction.log = Λ := by
    rw [mul_comm]; exact log_mul_moebius_eq_vonMangoldt
  rw [h3] at key
  have h4 : ((μ : ArithmeticFunction ℝ)).pmul ArithmeticFunction.log
      * (↑zeta : ArithmeticFunction ℝ) = -Λ := eq_neg_of_add_eq_zero_left key.symm
  have h5 := congrArg (fun F => F * (μ : ArithmeticFunction ℝ)) h4
  simp only [mul_assoc] at h5
  rw [mul_comm (↑zeta : ArithmeticFunction ℝ), coe_moebius_mul_coe_zeta, mul_one] at h5
  rw [h5]
  ring

/-- **`(μ * Λ)(n) = − μ(n) log n`.** -/
theorem moebius_mul_vonMangoldt_apply (n : ℕ) :
    ((μ : ArithmeticFunction ℝ) * Λ) n = -(μ n : ℝ) * Real.log n := by
  have h := congrArg (fun F : ArithmeticFunction ℝ => F n) moebius_pmul_log
  simp only [pmul_apply, log_apply, neg_apply, intCoe_apply] at h
  linarith [h]

/-- **`ζ * (μ * Λ) = Λ`** — the requested `1 * (μ * Λ) = Λ` with `1` read as the
constant-one arithmetic function `ζ` (Mathlib's `1` is the delta function). -/
theorem zeta_mul_moebius_mul_vonMangoldt :
    (↑zeta : ArithmeticFunction ℝ) * ((μ : ArithmeticFunction ℝ) * Λ) = Λ := by
  rw [← mul_assoc, mul_comm (↑zeta : ArithmeticFunction ℝ), coe_moebius_mul_coe_zeta, one_mul]

/-! ## 3. Interfaces and the proof-theoretic guard -/

/-- **OPEN INTERFACE.**  The source expected term is identified with the banked
centering term.  Never inhabited here. -/
def SourceExpectedTermIdentified (sourceExpected centering tol : ℝ) : Prop :=
  |sourceExpected - centering| ≤ tol

/-- **OPEN INTERFACE.**  The additive zero mode is reconciled with the source
term.  Never inhabited here. -/
def SourceZeroModeReconciled (zeroMode sourceTerm tol : ℝ) : Prop :=
  |zeroMode - sourceTerm| ≤ tol

/-- **OPEN INTERFACE.**  Hard Gate-1B packet closure. -/
def Gate1BPacketClosed (packetSum bound : ℝ) : Prop := |packetSum| ≤ bound

/-- **GUARD.**  The full divisor-boundary identity is exact algebra; it holds
unconditionally and therefore cannot imply hard Gate-1B packet closure, which
has false instances. -/
theorem divisor_boundary_identity_does_not_imply_packet_closure :
    ∃ packetSum bound : ℝ,
      (∀ n : ℕ, ((μ : ArithmeticFunction ℝ) * Λ) n = -(μ n : ℝ) * Real.log n)
        ∧ ¬ Gate1BPacketClosed packetSum bound := by
  refine ⟨1, 0, moebius_mul_vonMangoldt_apply, ?_⟩
  unfold Gate1BPacketClosed
  norm_num

end Boundary
end Gate1BDet2
end TwinPrimeProject
