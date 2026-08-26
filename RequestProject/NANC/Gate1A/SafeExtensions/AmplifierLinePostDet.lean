/-
# NANC Gate 1A v9 — the post-determinant along two amplifier lines

Both amplifier families run over the same coprime moduli `q1, q2`:

    ell1(t)  = ell10  + q2*t,   ell2(t)  = ell20  + q1*t,
    ell1'(t') = ell10' + q2*t',  ell2'(t') = ell20' + q1*t'.

With `P(t) = ell1(t)·ell2(t)` and the affine determinants
`Delta(t) = Delta0 + N*t`, `Delta'(t') = Delta0' + N'*t'`, the post-determinant
restricted to the two lines is

    OmegaLine(t,t') = delta'·P(t)·(Delta0' + N'*t') − delta·P'(t')·(Delta0 + N*t).

Banked here:

* `postDet_on_amplifierLines` — `OmegaLine` is the abstract `postDetOmega`
  evaluated on the two lines;
* `omegaLine_coeff_two` — the `t'²` coefficient equals `−delta·q1·q2·Delta(t)`;
* `omegaLine_natDegree_le_two`, `omegaLine_nonzero`;
* `omegaLine_zeroFiber_card_le_two` — at most two zeros in `t'`, over **any**
  finite set of `t'` (no interval hypothesis).

**FIREWALL.**  A degree-2 zero fibre is *fibre sparsity only*: no operator-norm
contraction, and no analytic gain, follows.
-/
import RequestProject.NANC.Gate1A.SafeExtensions.AmplifierLine
import RequestProject.NANC.Gate1A.SafeExtensions.PostDeterminant

namespace TwinPrimeProject.NANC.Gate1A.V9

open Polynomial

/-- The amplifier product `P(t) = ell1(t)·ell2(t)`, a degree-`≤ 2` integer
polynomial expression in `t`. -/
def ampProduct (q1 q2 ell10 ell20 t : ℤ) : ℤ := (ell10 + q2 * t) * (ell20 + q1 * t)

/-- `P(t)` written out as a quadratic in `t`. -/
theorem ampProduct_quadratic (q1 q2 ell10 ell20 t : ℤ) :
    ampProduct q1 q2 ell10 ell20 t
      = ell10 * ell20 + (ell10 * q1 + ell20 * q2) * t + (q1 * q2) * t ^ 2 := by
  unfold ampProduct; ring

/-- The post-determinant along the two amplifier lines. -/
def omegaLine (delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' : ℤ) : ℤ :=
  delta' * ampProduct q1 q2 ell10 ell20 t *
      (detDelta ell10' ell20' h1' h2 + detN h1' h2 q1 q2 * t')
    - delta * ampProduct q1 q2 ell10' ell20' t' *
      (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t)

/-- **`OmegaLine` is the abstract post-determinant on the two lines.** -/
theorem postDet_on_amplifierLines (delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' : ℤ) :
    omegaLine delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t'
      = postDetOmega delta delta' (ell10 + q2 * t) (ell20 + q1 * t)
          (ell10' + q2 * t') (ell20' + q1 * t') h1 h1' h2 := by
  unfold omegaLine ampProduct postDetOmega postDelta detDelta detN
  ring

/-- The `t'`-polynomial attached to a fixed `t`. -/
noncomputable def omegaLinePoly (delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t : ℤ) :
    Polynomial ℤ :=
  C (delta' * ampProduct q1 q2 ell10 ell20 t) *
      (C (detDelta ell10' ell20' h1' h2) + C (detN h1' h2 q1 q2) * X)
    - C delta * ((C ell10' + C q2 * X) * (C ell20' + C q1 * X)) *
      C (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t)

/-- Evaluating the polynomial recovers `OmegaLine`. -/
theorem omegaLinePoly_eval (delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' : ℤ) :
    (omegaLinePoly delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t).eval t'
      = omegaLine delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' := by
  unfold omegaLinePoly omegaLine ampProduct
  simp

/-- **The `t'²` coefficient** of the post-determinant along the lines is
`−delta·q1·q2·Delta(t)`. -/
theorem omegaLine_coeff_two (delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t : ℤ) :
    (omegaLinePoly delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t).coeff 2
      = -(delta * (q1 * q2) *
          (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t)) := by
  have hform : omegaLinePoly delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t
      = C (delta' * ampProduct q1 q2 ell10 ell20 t * detDelta ell10' ell20' h1' h2
            - delta * (ell10' * ell20')
              * (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t))
        + C (delta' * ampProduct q1 q2 ell10 ell20 t * detN h1' h2 q1 q2
            - delta * (ell10' * q1 + ell20' * q2)
              * (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t)) * X
        + C (-(delta * (q1 * q2)
              * (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t))) * X ^ 2 := by
    unfold omegaLinePoly
    simp only [C_mul, C_add, C_sub, C_neg]
    ring
  rw [hform]
  simp only [coeff_add, coeff_C, coeff_C_mul, coeff_X, coeff_X_pow]
  norm_num

/-- The polynomial has degree at most two. -/
theorem omegaLine_natDegree_le_two (delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t : ℤ) :
    (omegaLinePoly delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t).natDegree ≤ 2 := by
  unfold omegaLinePoly
  compute_degree

/-- **Nonvanishing.**  If `delta, q1, q2 ≠ 0` and `Delta(t) ≠ 0`, the
`t'`-polynomial is nonzero. -/
theorem omegaLine_nonzero {delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t : ℤ}
    (hd : delta ≠ 0) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0)
    (hDelta : detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t ≠ 0) :
    omegaLinePoly delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t ≠ 0 := by
  intro hzero
  have hc := omegaLine_coeff_two delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t
  rw [hzero] at hc
  simp only [coeff_zero] at hc
  have : delta * (q1 * q2) * (detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t) = 0 := by
    linarith [hc]
  rcases mul_eq_zero.mp this with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hd h'
    · rcases mul_eq_zero.mp h' with h'' | h''
      · exact hq1 h''
      · exact hq2 h''
  · exact hDelta h

/-- **Degree-2 zero fibre.**  For fixed `t`, the set of `t'` in *any* finite set
with `OmegaLine(t,t') = 0` has at most two elements. -/
theorem omegaLine_zeroFiber_card_le_two
    {delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t : ℤ}
    (hd : delta ≠ 0) (hq1 : q1 ≠ 0) (hq2 : q2 ≠ 0)
    (hDelta : detDelta ell10 ell20 h1 h2 + detN h1 h2 q1 q2 * t ≠ 0)
    (S : Finset ℤ) :
    (S.filter fun t' =>
        omegaLine delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' = 0).card ≤ 2 := by
  set p := omegaLinePoly delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t with hp
  have hp0 : p ≠ 0 := omegaLine_nonzero hd hq1 hq2 hDelta
  have hsub : (S.filter fun t' =>
      omegaLine delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' = 0)
        ⊆ p.roots.toFinset := by
    intro t' ht'
    rw [Finset.mem_filter] at ht'
    rw [Multiset.mem_toFinset, mem_roots hp0]
    have := omegaLinePoly_eval delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t'
    exact (by simpa [IsRoot, hp, this] using ht'.2)
  calc (S.filter fun t' =>
        omegaLine delta delta' q1 q2 ell10 ell20 ell10' ell20' h1 h1' h2 t t' = 0).card
      ≤ p.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card p.roots := p.roots.toFinset_card_le
    _ ≤ p.natDegree := card_roots' p
    _ ≤ 2 := omegaLine_natDegree_le_two _ _ _ _ _ _ _ _ _ _ _ _

end TwinPrimeProject.NANC.Gate1A.V9
