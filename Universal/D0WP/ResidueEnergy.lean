/-
# Universal / D0WP — residue-class pushforward energy

**Status of this module: KERNEL_PROVED elementary counting and Cauchy–Schwarz.**

The provider pushes the dyadic `d0`-source and the dyadic prime `wp`-source onto
residue classes modulo the effective modulus `rSharp`:

```
Xres(u) = Σ_{d0 : inverse(d0) = u mod rSharp} α(d0),
Yres(v) = Σ_{wp : inverse(wp) = v mod rSharp} β(wp).
```

Two elementary facts are proved here, and nothing else:

* the **class multiplicity bound** `N_D(u) ≤ 1 + D / rSharp`, valid for any
  source contained in an interval of length `D` whose class map separates
  residues modulo `rSharp`;
* the **finite Cauchy energy bound**
  `Σ_u ‖Xres(u)‖² ≤ (1 + D/rSharp) Σ_d ‖α(d)‖²`.

No prime number theorem, no equidistribution input, and no analytic estimate is
used: the prime source is treated exactly like any other subset of the dyadic
interval.
-/
import Mathlib

namespace Universal.D0WP

open Finset

/-- **Class multiplicity (kernel-proved).**  A set of integers inside an
interval of length `D`, all lying in one residue class modulo `n`, has at most
`1 + D / n` elements. -/
theorem card_residue_class_le {n a D : ℕ} (hn : n ≠ 0) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico a (a + D))
    (hmod : ∀ d₁ ∈ S, ∀ d₂ ∈ S, d₁ ≡ d₂ [MOD n]) :
    S.card ≤ 1 + D / n := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero hn
  have hcard : (Finset.range (D / n + 1)).card = 1 + D / n := by simp [Nat.add_comm]
  rw [← hcard]
  refine Finset.card_le_card_of_injOn (fun d => (d - a) / n) ?_ ?_
  · intro d hd
    have hd' : d ∈ Finset.Ico a (a + D) := hS hd
    rw [Finset.mem_Ico] at hd'
    refine Finset.mem_range.mpr ?_
    show (d - a) / n < D / n + 1
    have h1 : (d - a) / n ≤ D / n := Nat.div_le_div_right (by omega)
    omega
  · intro d₁ h₁ d₂ h₂ heq
    simp only [Finset.mem_coe] at h₁ h₂
    have hd₁ : d₁ ∈ Finset.Ico a (a + D) := hS h₁
    have hd₂ : d₂ ∈ Finset.Ico a (a + D) := hS h₂
    rw [Finset.mem_Ico] at hd₁ hd₂
    have heq' : (d₁ - a) / n = (d₂ - a) / n := heq
    have key : ∀ x : ℕ, n * (x / n) ≤ x ∧ x < n * (x / n) + n := by
      intro x
      refine ⟨by rw [mul_comm]; exact Nat.div_mul_le_self _ _, ?_⟩
      calc x < n * (x / n + 1) := Nat.lt_mul_div_succ x hn0
        _ = n * (x / n) + n := by ring
    obtain ⟨hlo₁, hhi₁⟩ := key (d₁ - a)
    obtain ⟨hlo₂, hhi₂⟩ := key (d₂ - a)
    rw [heq'] at hlo₁ hhi₁
    set P := n * ((d₂ - a) / n) with hP
    have hclose : d₁ < d₂ + n ∧ d₂ < d₁ + n := by omega
    rcases le_total d₁ d₂ with hle | hle
    · have hdvd : n ∣ d₂ - d₁ := (Nat.modEq_iff_dvd' hle).mp (hmod d₁ h₁ d₂ h₂)
      have : d₂ - d₁ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega
    · have hdvd : n ∣ d₁ - d₂ := (Nat.modEq_iff_dvd' hle).mp (hmod d₂ h₂ d₁ h₁)
      have : d₁ - d₂ = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (by omega)
      omega

/-- **Fibrewise Cauchy energy bound (kernel-proved).**  If every fibre of the
class map has at most `B` elements, the pushed-forward `ℓ²` energy grows by at
most the factor `B`. -/
theorem fiber_energy_le {ι κ : Type*} [DecidableEq κ] [Fintype κ] [DecidableEq ι]
    (S : Finset ι) (cls : ι → κ) (α : ι → ℂ) (B : ℝ)
    (hB : ∀ u : κ, ((S.filter (fun d => cls d = u)).card : ℝ) ≤ B) :
    ∑ u : κ, ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖ ^ 2
      ≤ B * ∑ d ∈ S, ‖α d‖ ^ 2 := by
  have per : ∀ u : κ, ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖ ^ 2
      ≤ B * ∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖ ^ 2 := by
    intro u
    have h1 : ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖
        ≤ ∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖ := norm_sum_le _ _
    have h2 : (∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖) ^ 2
        ≤ ((S.filter (fun d => cls d = u)).card : ℝ)
            * ∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖ ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have h3 : ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖ ^ 2
        ≤ (∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖) ^ 2 := by
      have hnn : (0:ℝ) ≤ ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖ := norm_nonneg _
      nlinarith [norm_nonneg (∑ d ∈ S.filter (fun d => cls d = u), α d)]
    refine h3.trans (h2.trans ?_)
    exact mul_le_mul_of_nonneg_right (hB u) (by positivity)
  calc ∑ u : κ, ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖ ^ 2
      ≤ ∑ u : κ, B * ∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖ ^ 2 :=
        Finset.sum_le_sum (fun u _ => per u)
    _ = B * ∑ u : κ, ∑ d ∈ S.filter (fun d => cls d = u), ‖α d‖ ^ 2 := by
        rw [Finset.mul_sum]
    _ = B * ∑ d ∈ S, ‖α d‖ ^ 2 := by
        rw [Finset.sum_fiberwise S cls (fun d => ‖α d‖ ^ 2)]

/-- **Residue-class energy for a dyadic source (kernel-proved).**

If the source `S` lies in an interval of length `D` and the class map `cls`
separates residues modulo `n` (as the map `d ↦ inverse(d) mod n` does on units),
then

```
Σ_u ‖Xres(u)‖² ≤ (1 + D/n) Σ_{d ∈ S} ‖α d‖².
```
-/
theorem residue_pushforward_energy {n a D : ℕ} (hn : n ≠ 0) [NeZero n]
    (S : Finset ℕ) (hS : S ⊆ Finset.Ico a (a + D))
    (cls : ℕ → ZMod n) (α : ℕ → ℂ)
    (hsep : ∀ d₁ ∈ S, ∀ d₂ ∈ S, cls d₁ = cls d₂ → d₁ ≡ d₂ [MOD n]) :
    ∑ u : ZMod n, ‖∑ d ∈ S.filter (fun d => cls d = u), α d‖ ^ 2
      ≤ (1 + (D / n : ℕ) : ℝ) * ∑ d ∈ S, ‖α d‖ ^ 2 := by
  refine fiber_energy_le S cls α _ ?_
  intro u
  have hsub : S.filter (fun d => cls d = u) ⊆ Finset.Ico a (a + D) :=
    (Finset.filter_subset _ _).trans hS
  have hmod : ∀ d₁ ∈ S.filter (fun d => cls d = u),
      ∀ d₂ ∈ S.filter (fun d => cls d = u), d₁ ≡ d₂ [MOD n] := by
    intro d₁ h₁ d₂ h₂
    rw [Finset.mem_filter] at h₁ h₂
    exact hsep d₁ h₁.1 d₂ h₂.1 (h₁.2.trans h₂.2.symm)
  exact_mod_cast card_residue_class_le hn _ hsub hmod

end Universal.D0WP
