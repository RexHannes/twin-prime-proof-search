import Gate1B.FM722CenteredOneFactorCompletion

/-!
# Gate 1B · FM722 · Parseval normalisation, **full DFT support** versus the
**sparse inverse Fourier transform**, and the CRT DFT non-factorisation firewall

Exact finite Fourier algebra.  No analytic estimate is proved or assumed.

## The semantic distinction that this module formalises

A DFT coefficient vector `hatAlpha : ZMod q → ℂ` may have **full support**:
this is *allowed* and is exhibited by an explicit countermodel below.  What is
true — and what the FM722 argument actually uses — is that the *inverse*
transform is as sparse as the original datum:

```
  invDFT (hatAlpha) = q · alpha,     support (invDFT (hatAlpha)) ⊆ support (alpha).
```

Nothing here proves, or lets one prove, that `hatAlpha` itself has short
support.

## Contents

* §1 Parseval: `∑_k |hatAlpha(k)|² = q ∑_A |alpha(A)|²` (no hidden `q^{1/2}`);
* §2 `generatedDFT_sparseInverseFourier`: the inverse transform is supported in
  the support of `alpha`, with the cardinality bound;
* §3 the **full-support countermodel**: a one-point (interval) datum whose DFT
  is nonvanishing at *every* frequency;
* §4 the **CRT DFT firewall**: an explicit DFT vector mod `6` which is *not* a
  product `hatAlpha_2 ⊗ hatAlpha_3`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

variable {q : ℕ} [NeZero q]

/-! ## 1. Parseval normalisation -/

/-- **Parseval, complex form.** -/
theorem parseval_complex (alpha : ZMod q → ℂ) :
    (∑ k : ZMod q, dftHat q alpha k * (starRingEnd ℂ) (dftHat q alpha k))
      = (q : ℂ) * ∑ A : ZMod q, alpha A * (starRingEnd ℂ) (alpha A) := by
  classical
  have hexp : ∀ k : ZMod q,
      dftHat q alpha k * (starRingEnd ℂ) (dftHat q alpha k)
        = ∑ A : ZMod q, ∑ B : ZMod q,
            (alpha A * (starRingEnd ℂ) (alpha B)) * eM q (k * (B - A)) := by
    intro k
    rw [dftHat, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun B _ => ?_
    rw [map_mul, eM_conj]
    have hch : eM q (-(k * A)) * eM q (-(-(k * B))) = eM q (k * (B - A)) := by
      rw [← eM_add]; congr 1; ring
    calc alpha A * eM q (-(k * A)) * ((starRingEnd ℂ) (alpha B) * eM q (-(-(k * B))))
        = (alpha A * (starRingEnd ℂ) (alpha B)) * (eM q (-(k * A)) * eM q (-(-(k * B)))) := by
          ring
      _ = (alpha A * (starRingEnd ℂ) (alpha B)) * eM q (k * (B - A)) := by rw [hch]
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  have hin : ∀ A : ZMod q,
      (∑ k : ZMod q, ∑ B : ZMod q, (alpha A * (starRingEnd ℂ) (alpha B)) * eM q (k * (B - A)))
        = (q : ℂ) * (alpha A * (starRingEnd ℂ) (alpha A)) := by
    intro A
    rw [Finset.sum_comm]
    have hB : ∀ B : ZMod q,
        (∑ k : ZMod q, (alpha A * (starRingEnd ℂ) (alpha B)) * eM q (k * (B - A)))
          = (alpha A * (starRingEnd ℂ) (alpha B)) * (if B - A = 0 then (q : ℂ) else 0) := by
      intro B
      rw [← Finset.mul_sum, full_char_sum]
    rw [Finset.sum_congr rfl fun B _ => hB B, Finset.sum_eq_single A]
    · simp [mul_comm]
    · intro b _ hb
      have : b - A ≠ 0 := sub_ne_zero.mpr hb
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [Finset.sum_congr rfl fun A _ => hin A, ← Finset.mul_sum]

/-- **Parseval normalisation (norm form).**  `∑_k |hatAlpha(k)|² = q ∑_A
|alpha(A)|²`.  The whole normalisation is the single factor `q`; there is no
hidden `q^{1/2}`. -/
theorem parseval_norm (alpha : ZMod q → ℂ) :
    (∑ k : ZMod q, ‖dftHat q alpha k‖ ^ 2) = (q : ℝ) * ∑ A : ZMod q, ‖alpha A‖ ^ 2 := by
  have h := parseval_complex alpha
  simp only [Complex.mul_conj'] at h
  exact_mod_cast h

/-! ## 2. The sparse inverse Fourier transform -/

/-- **`generatedDFT_sparseInverseFourier`.**  If `alpha` is supported in a set
`I`, then the inverse transform of its DFT is supported in `I` as well — it is
literally `q · alpha`. -/
theorem generatedDFT_sparseInverseFourier (alpha : ZMod q → ℂ) (I : Finset (ZMod q))
    (hsupp : ∀ A : ZMod q, A ∉ I → alpha A = 0) :
    ∀ A : ZMod q, A ∉ I → invDFT q (dftHat q alpha) A = 0 := by
  intro A hA
  rw [invDFT_dftHat, hsupp A hA, mul_zero]

/-- Cardinality form: the support of the inverse transform has at most `#I`
elements. -/
theorem generatedDFT_sparseInverseFourier_card (alpha : ZMod q → ℂ) (I : Finset (ZMod q))
    (hsupp : ∀ A : ZMod q, A ∉ I → alpha A = 0) :
    (Finset.univ.filter (fun A : ZMod q => invDFT q (dftHat q alpha) A ≠ 0)).card ≤ I.card := by
  classical
  refine Finset.card_le_card ?_
  intro A hA
  by_contra hAI
  exact (Finset.mem_filter.mp hA).2
    (generatedDFT_sparseInverseFourier alpha I hsupp A hAI)

/-! ## 3. Full DFT support is allowed: an explicit countermodel -/

/-- The one-point (interval of length one) datum `δ₀`. -/
noncomputable def deltaZero (q : ℕ) [NeZero q] : ZMod q → ℂ := fun A => if A = 0 then 1 else 0

/-- Its support is a single point. -/
theorem deltaZero_support (A : ZMod q) (hA : A ≠ 0) : deltaZero q A = 0 := by
  simp [deltaZero, hA]

/-- **Full-support countermodel.**  The DFT of the one-point datum is the
constant `1`: it is nonzero at *every* frequency.  Hence a generated DFT vector
may have full support, and no short-support statement about `hatAlpha` is
available. -/
theorem dftHat_deltaZero (k : ZMod q) : dftHat q (deltaZero q) k = 1 := by
  classical
  rw [dftHat, Finset.sum_eq_single (0 : ZMod q)]
  · simp [deltaZero]
  · intro b _ hb; simp [deltaZero, hb]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The DFT of the one-point datum vanishes nowhere. -/
theorem dftHat_deltaZero_full_support (k : ZMod q) : dftHat q (deltaZero q) k ≠ 0 := by
  rw [dftHat_deltaZero]; exact one_ne_zero

/-! ## 4. The CRT DFT non-factorisation firewall -/

/-- The reduction maps `ZMod 6 → ZMod 2` and `ZMod 6 → ZMod 3`. -/
def red2 : ZMod 6 → ZMod 2 := fun k => ZMod.castHom (by norm_num) (ZMod 2) k

/-- The reduction map `ZMod 6 → ZMod 3`. -/
def red3 : ZMod 6 → ZMod 3 := fun k => ZMod.castHom (by norm_num) (ZMod 3) k

/-- An explicit frequency vector mod `6`, supported on `{0, 5}`. -/
noncomputable def crtTestHat : ZMod 6 → ℂ := fun k => if k = 0 ∨ k = 5 then 1 else 0

/-- `crtTestHat` really is a DFT vector: it is the DFT of the normalised
inverse transform of itself. -/
theorem crtTestHat_is_a_dft :
    dftHat 6 (fun A => ((6 : ℕ) : ℂ)⁻¹ * invDFT 6 crtTestHat A) = crtTestHat := by
  funext k
  exact dftHat_invDFT crtTestHat k

/-- **CRT DFT firewall.**  A DFT vector modulo `m·p` is *one* physical sum
carrying both additive characters; it does **not** factor as a product of a
DFT modulo `m` and a DFT modulo `p`.  Explicit countermodel modulo `6`. -/
theorem crt_dft_no_factorisation :
    ¬ ∃ (f : ZMod 2 → ℂ) (g : ZMod 3 → ℂ),
        ∀ k : ZMod 6, crtTestHat k = f (red2 k) * g (red3 k) := by
  rintro ⟨f, g, hfg⟩
  have c2_0 : red2 0 = 0 := by decide
  have c3_0 : red3 0 = 0 := by decide
  have c2_5 : red2 5 = 1 := by decide
  have c3_5 : red3 5 = 2 := by decide
  have c2_2 : red2 2 = 0 := by decide
  have c3_2 : red3 2 = 2 := by decide
  have c2_3 : red2 3 = 1 := by decide
  have c3_3 : red3 3 = 0 := by decide
  have v0 : crtTestHat 0 = 1 := by
    simp only [crtTestHat]; rw [if_pos (by decide)]
  have v5 : crtTestHat 5 = 1 := by
    simp only [crtTestHat]; rw [if_pos (by decide)]
  have v2 : crtTestHat 2 = 0 := by
    simp only [crtTestHat]; rw [if_neg (by decide)]
  have v3 : crtTestHat 3 = 0 := by
    simp only [crtTestHat]; rw [if_neg (by decide)]
  have h0 := hfg 0
  have h5 := hfg 5
  have h2 := hfg 2
  have h3 := hfg 3
  rw [v0, c2_0, c3_0] at h0
  rw [v5, c2_5, c3_5] at h5
  rw [v2, c2_2, c3_2] at h2
  rw [v3, c2_3, c3_3] at h3
  have hcontr : (1 : ℂ) = 0 := by
    calc (1 : ℂ) = (f 0 * g 0) * (f 1 * g 2) := by rw [← h0, ← h5]; ring
      _ = (f 0 * g 2) * (f 1 * g 0) := by ring
      _ = 0 := by rw [← h2, ← h3]; ring
  exact one_ne_zero hcontr

end FM722
end CurrentProgramme
end TwinPrimeProject
