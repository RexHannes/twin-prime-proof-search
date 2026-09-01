import Gate1B.VaughanLambda3P3Bridge

/-!
# Gate 1B · exact Vaughan centering algebra (comparison sequence kept abstract)

**Exact additive / convolution algebra only.  No analytic estimate, and no
choice of an authoritative analytic comparison sequence, is made here.**

## Contents

* §1 the exact Vaughan decomposition `Λ = P₁ − P₂ + P₃` in the real arithmetic
  function convolution ring, with

  - `vaughanP1R U V = Λ_{≤V}`,
  - `vaughanP2R U V = μ_{≤U} * Λ_{≤V} * ζ − μ_{≤U} * log`,
  - `vaughanP3R U V = (μ_{>U} * Λ_{>V}) * ζ`  (the hard high-high term);

  `vaughanP3R` is the real twin of `highHighP3` from
  `Gate1B.VaughanLambda3P3Bridge` and, exactly as there, it is `λ₃ * ζ` and
  **not** `λ₃`;

* §2 the generic centering identity in any additive commutative group and its
  instance `Λ − b = P₃ − (b − P₁ + P₂)` for an **arbitrary** comparison
  sequence `b`;

* §3 the shifted finite-pairing version of the centering identity, at the
  literal fixed shift `2`;

* §4 the **comparison role firewall**: `LocalRoughComparison` and
  `GlobalComparison` are distinct one-field wrappers, they are provably not
  identified, and every statement transporting one into the other carries the
  bridge hypothesis explicitly.

The top-level module `VaughanPacketAlgebra` (outside every library glob of this
repository, hence not importable) contains a real-valued Vaughan identity of
the same shape; it is left untouched.  Nothing here redefines `λ₃`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarTemplates

open Finset ArithmeticFunction
open scoped BigOperators

/-! ## 1. The exact Vaughan decomposition -/

/-- Real truncation `n ≤ Y`. -/
noncomputable def afTruncLER (Y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ Y then f n else 0
  map_zero' := by simp

/-- Real truncation `n > Y`. -/
noncomputable def afTruncGTR (Y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if Y < n then f n else 0
  map_zero' := by simp

@[simp] theorem afTruncLER_apply (Y : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    afTruncLER Y f n = if n ≤ Y then f n else 0 := rfl

@[simp] theorem afTruncGTR_apply (Y : ℕ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    afTruncGTR Y f n = if Y < n then f n else 0 := rfl

theorem afR_truncation_decomposition (Y : ℕ) (f : ArithmeticFunction ℝ) :
    f = afTruncLER Y f + afTruncGTR Y f := by
  ext n
  by_cases h : n ≤ Y
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_le h]

/-- Vaughan's `P₁` term. -/
noncomputable def vaughanP1R (_U V : ℕ) : ArithmeticFunction ℝ := afTruncLER V vonMangoldt

/-- Vaughan's `P₂` term. -/
noncomputable def vaughanP2R (U V : ℕ) : ArithmeticFunction ℝ :=
  afTruncLER U (↑moebius : ArithmeticFunction ℝ) * afTruncLER V vonMangoldt *
      (↑zeta : ArithmeticFunction ℝ)
    - afTruncLER U (↑moebius : ArithmeticFunction ℝ) * log

/-- Vaughan's hard `P₃` term `(μ_{>U} * Λ_{>V}) * ζ`. -/
noncomputable def vaughanP3R (U V : ℕ) : ArithmeticFunction ℝ :=
  afTruncGTR U (↑moebius : ArithmeticFunction ℝ) * afTruncGTR V vonMangoldt *
    (↑zeta : ArithmeticFunction ℝ)

/-- The high-high **modulus** coefficient on the real side (the real twin of
`highHighCoefficient`).  As in the complex bridge, this is `λ₃`, not `P₃`. -/
noncomputable def highHighCoefficientR (U V : ℕ) : ArithmeticFunction ℝ :=
  afTruncGTR U (↑moebius : ArithmeticFunction ℝ) * afTruncGTR V vonMangoldt

/-- `P₃ = λ₃ * ζ` on the real side as well: the same typing as the boxed
complex theorem `lambda3_conv_zeta_eq_highHighP3`. -/
theorem vaughanP3R_eq_coefficient_conv_zeta (U V : ℕ) :
    vaughanP3R U V = highHighCoefficientR U V * (↑zeta : ArithmeticFunction ℝ) := rfl

/-- **The exact Vaughan identity** `Λ = P₁ − P₂ + P₃` in the arithmetic
function convolution ring. -/
theorem exactVaughanIdentityR (U V : ℕ) :
    vonMangoldt = vaughanP1R U V - vaughanP2R U V + vaughanP3R U V := by
  have hmu :
      (afTruncLER U (↑moebius : ArithmeticFunction ℝ) +
          afTruncGTR U (↑moebius : ArithmeticFunction ℝ)) *
          (↑zeta : ArithmeticFunction ℝ) = 1 := by
    rw [← afR_truncation_decomposition]
    exact coe_moebius_mul_coe_zeta
  have hlog :
      (afTruncLER V vonMangoldt + afTruncGTR V vonMangoldt) *
          (↑zeta : ArithmeticFunction ℝ) = log := by
    rw [← afR_truncation_decomposition]
    exact vonMangoldt_mul_zeta
  rw [vaughanP1R, vaughanP2R, vaughanP3R]
  calc
    vonMangoldt = afTruncLER V vonMangoldt + afTruncGTR V vonMangoldt :=
      afR_truncation_decomposition V vonMangoldt
    _ = afTruncLER V vonMangoldt + 1 * afTruncGTR V vonMangoldt := by ring
    _ = afTruncLER V vonMangoldt +
        ((afTruncLER U (↑moebius : ArithmeticFunction ℝ) +
          afTruncGTR U (↑moebius : ArithmeticFunction ℝ)) *
          (↑zeta : ArithmeticFunction ℝ)) * afTruncGTR V vonMangoldt := by rw [hmu]
    _ = _ := by rw [← hlog]; ring

/-! ## 2. Centering against an abstract comparison sequence -/

/-- **The generic centering identity.**  Purely additive: no arithmetic input
whatsoever. -/
theorem centering_identity {A : Type*} [AddCommGroup A] (L P1 P2 P3 b : A)
    (h : L = P1 - P2 + P3) : L - b = P3 - (b - P1 + P2) := by
  rw [h]; abel

/-- **Vaughan centering.**  For an arbitrary comparison sequence `b`,

`Λ − b = P₃ − (b − P₁ + P₂)`.

No analytic property of `b` is used, assumed or asserted. -/
theorem vonMangoldt_centering (U V : ℕ) (b : ArithmeticFunction ℝ) :
    vonMangoldt - b = vaughanP3R U V - (b - vaughanP1R U V + vaughanP2R U V) :=
  centering_identity _ _ _ _ b (exactVaughanIdentityR U V)

/-- Pointwise form of the centering identity. -/
theorem vonMangoldt_centering_apply (U V : ℕ) (b : ArithmeticFunction ℝ) (n : ℕ) :
    Λ n - b n = vaughanP3R U V n - (b n - vaughanP1R U V n + vaughanP2R U V n) := by
  have h := congrArg (fun f : ArithmeticFunction ℝ => f n) (vonMangoldt_centering U V b)
  simpa using h

/-! ## 3. Shifted finite-pairing form -/

/-- **Centering under the fixed-shift finite pairing.**  The shift is the
literal `2`; nothing is averaged over shifts. -/
theorem shifted_pairing_centering (K U V : ℕ) (b : ArithmeticFunction ℝ) (g : ℕ → ℝ) :
    ∑ N ∈ Finset.Icc 2 (K + 2), (Λ N - b N) * g (N - 2) =
      ∑ N ∈ Finset.Icc 2 (K + 2), vaughanP3R U V N * g (N - 2)
        - ∑ N ∈ Finset.Icc 2 (K + 2),
            (b N - vaughanP1R U V N + vaughanP2R U V N) * g (N - 2) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [← sub_mul, vonMangoldt_centering_apply U V b N]

/-! ## 4. Comparison role firewall -/

/-- A **local rough** comparison sequence (packet-local role). -/
structure LocalRoughComparison where
  seq : ArithmeticFunction ℝ

/-- A **global** comparison sequence (global Ford–Maynard role). -/
structure GlobalComparison where
  seq : ArithmeticFunction ℝ

/-- **Firewall.**  The two comparison roles are not identified: there are data
whose underlying sequences differ.  No theorem of this bank equates them. -/
theorem localRough_not_identified_with_global :
    ∃ (l : LocalRoughComparison) (g : GlobalComparison), l.seq ≠ g.seq := by
  refine ⟨⟨0⟩, ⟨1⟩, ?_⟩
  intro h
  have h1 := congrArg (fun f : ArithmeticFunction ℝ => f 1) h
  simp at h1

/-- Transport between the two comparison roles is possible **only** through an
explicit bridge hypothesis, which is an argument of the theorem and is never
supplied inside this bank. -/
theorem centering_transport_of_bridge (U V : ℕ)
    (l : LocalRoughComparison) (g : GlobalComparison) (hbridge : l.seq = g.seq) :
    vonMangoldt - l.seq =
      vaughanP3R U V - (g.seq - vaughanP1R U V + vaughanP2R U V) := by
  rw [hbridge]
  exact vonMangoldt_centering U V g.seq

end HStarTemplates
end CurrentProgramme
end TwinPrimeProject
