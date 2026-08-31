import Mathlib
import RequestProject.CurrentProgramme.StatusTypes
import Gate1B.ALineBetaU2Pushforward

/-!
# Gate 1B · C4Shift Fourier factorisation and the `q`-Fourier pushforward

**Phase D of the C4Shift consolidation.**  Append-only.

Everything proved here is exact: the real additive character `eR`, the exact
double-Fourier factorisation of the Γ-source, the exact `Ĥ` pushforward, and
purely structural compilers.  **The analytic estimate is not proved**: the
socket `C4ShiftQFourierPushforwardInput` and its stronger child
`C4ShiftPushforwardU2TransferInput` are structures that are never constructed.

## Contents

1. `eR` — the real-frequency additive character, with `eR_add`, `eR_conj` and
   the dictionary `ezExp_eq_eR` to the repository's `ezExp`.
2. `lineCoeff`, `KHat`, `CHat` — the line coefficient and the κ- and line
   Fourier transforms.  `TopBandKernelInput` (UNINHABITED) is the interface
   asserting `K = m_top`.
3. `GammaTwoLine`, `GammaTilde` and the **load-bearing factorisation**
   `GammaTilde_factorisation`.
4. `GammaHat` and the recovery identity `GammaTilde_eq_sum_GammaHat`.
5. `Hhat_exact_pushforward` — the exact `Ĥ_j(θ,v)` pushforward formula.
6. `C4ShiftQFourierPushforwardInput` — **UNINHABITED** analytic socket.
7. `C4ShiftPushforwardU2TransferInput` — **UNINHABITED**, stronger than
   source-minimal, OPEN.
8. `topBand_conditional_compiler` — a *conditional* structural compiler only.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace C4ShiftQFourier

open Finset FiniteLiftLocalTwist ALinePushforward

/-! ## 1. The real-frequency additive character -/

/-- `e(x) = exp(2πi x)` for a real frequency `x`. -/
noncomputable def eR (x : ℝ) : ℂ := Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ))

@[simp] theorem eR_zero : eR 0 = 1 := by simp [eR]

theorem eR_add (x y : ℝ) : eR (x + y) = eR x * eR y := by
  unfold eR
  rw [← Complex.exp_add]
  push_cast
  ring_nf

theorem eR_conj (x : ℝ) : (starRingEnd ℂ) (eR x) = eR (-x) := by
  unfold eR
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat, Complex.ofReal_neg]
  ring

/-- Dictionary: the repository's `ezExp` is `eR` at a rational frequency. -/
theorem ezExp_eq_eR (k : ℕ) (n : ℤ) : ezExp k n = eR ((n : ℝ) / (k : ℝ)) := by
  unfold ezExp eR
  congr 1
  push_cast
  ring

/-- Five-fold additivity, used by the factorisation. -/
theorem eR_add5 (a b c d e : ℝ) :
    eR (a + b + c + d + e) = eR a * eR b * eR c * eR d * eR e := by
  rw [eR_add, eR_add, eR_add, eR_add]

/-! ## 2. Line coefficient and the two Fourier transforms -/

/-- The line coefficient `c_{u,s,ℓ}(t) = c4j(A₀ + ℓ t) · W(t)`. -/
noncomputable def lineCoeff (c4j : ℤ → ℂ) (Wt : ℤ → ℂ) (A0 : ℤ) (ell : ℕ) (t : ℤ) : ℂ :=
  c4j (A0 + (ell : ℤ) * t) * Wt t

/-- The κ-transform `K(ξ) = ∑_h κ(h) e(−h ξ)`. -/
noncomputable def KHat (H : Finset ℤ) (kappa : ℤ → ℂ) (xi : ℝ) : ℂ :=
  ∑ h ∈ H, kappa h * eR (-((h : ℝ) * xi))

/-- The line transform `C_{u,s,ℓ}(ξ) = ∑_t c(t) e(−ξ t)`. -/
noncomputable def CHat (T : Finset ℤ) (c : ℤ → ℂ) (xi : ℝ) : ℂ :=
  ∑ t ∈ T, c t * eR (-(xi * (t : ℝ)))

/-- **UNINHABITED interface.**  The identification of the κ-transform with the
literal top-band multiplier `m_top` is *not* available in this repository. -/
structure TopBandKernelInput where
  /-- The `h`-support. -/
  H : Finset ℤ
  /-- The `h`-kernel. -/
  kappa : ℤ → ℂ
  /-- The claimed top-band multiplier. -/
  mTop : ℝ → ℂ
  /-- The identification itself (**not proved anywhere**). -/
  identification : ∀ xi : ℝ, KHat H kappa xi = mTop xi

/-! ## 3. The Γ-source and its double Fourier transform -/

section Gamma

variable (S T H : Finset ℤ)

/-- The index set of the two-line Γ-source: `(s, t₁, t₂, h₁, h₂)`. -/
def gammaIndex : Finset (ℤ × ℤ × ℤ × ℤ × ℤ) := S ×ˢ (T ×ˢ (T ×ˢ (H ×ˢ H)))

/-- The `w`-coordinate `w = ν_s + s t₁ + h₁`. -/
def wCoord (nu : ℤ → ℤ) (i : ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ :=
  nu i.1 + i.1 * i.2.1 + i.2.2.2.1

/-- The `g`-coordinate `g = s(t₂ − t₁) + (h₂ − h₁)`. -/
def gCoord (i : ℤ × ℤ × ℤ × ℤ × ℤ) : ℤ :=
  i.1 * (i.2.2.1 - i.2.1) + (i.2.2.2.2 - i.2.2.2.1)

/-- The source value attached to a tuple. -/
noncomputable def gammaVal (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ)
    (i : ℤ × ℤ × ℤ × ℤ × ℤ) : ℂ :=
  c i.1 i.2.1 * (starRingEnd ℂ) (c i.1 i.2.2.1) *
    kappa i.2.2.2.1 * (starRingEnd ℂ) (kappa i.2.2.2.2)

/-- **The two-line Γ-source** (all source fields retained). -/
noncomputable def GammaTwoLine (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ) (nu : ℤ → ℤ)
    (w g : ℤ) : ℂ :=
  ∑ i ∈ gammaIndex S T H,
    (if w = wCoord nu i ∧ g = gCoord i then gammaVal c kappa i else 0)

/-- The double Fourier transform of Γ. -/
noncomputable def GammaTilde (Wf Gf : Finset ℤ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ)
    (nu : ℤ → ℤ) (alpha eta : ℝ) : ℂ :=
  ∑ w ∈ Wf, ∑ g ∈ Gf,
    GammaTwoLine S T H c kappa nu w g * eR (-(alpha * (w : ℝ)) - eta * (g : ℝ))

/-- The one-frequency transform `Γ̂_g(α) = ∑_w Γ(w,g) e(−α w)`. -/
noncomputable def GammaHat (Wf : Finset ℤ) (c : ℤ → ℤ → ℂ) (kappa : ℤ → ℂ)
    (nu : ℤ → ℤ) (g : ℤ) (alpha : ℝ) : ℂ :=
  ∑ w ∈ Wf, GammaTwoLine S T H c kappa nu w g * eR (-(alpha * (w : ℝ)))

end Gamma

/-- Fibrewise collapse of a `(w,g)`-indexed sum of indicators. -/
theorem sum_indicator_fibre {ι : Type*} [DecidableEq ι] (Wf Gf : Finset ℤ) (Idx : Finset ι)
    (Wc Gc : ι → ℤ) (val : ι → ℂ) (phi : ℤ → ℤ → ℂ)
    (hW : ∀ i ∈ Idx, Wc i ∈ Wf) (hG : ∀ i ∈ Idx, Gc i ∈ Gf) :
    ∑ w ∈ Wf, ∑ g ∈ Gf,
        (∑ i ∈ Idx, (if w = Wc i ∧ g = Gc i then val i else 0)) * phi w g
      = ∑ i ∈ Idx, val i * phi (Wc i) (Gc i) := by
  classical
  have h1 : ∀ w ∈ Wf, ∀ g ∈ Gf,
      (∑ i ∈ Idx, (if w = Wc i ∧ g = Gc i then val i else 0)) * phi w g
        = ∑ i ∈ Idx, (if w = Wc i ∧ g = Gc i then val i * phi (Wc i) (Gc i) else 0) := by
    intro w _ g _
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : w = Wc i ∧ g = Gc i
    · rw [if_pos h, if_pos h, h.1, h.2]
    · rw [if_neg h, if_neg h, zero_mul]
  rw [Finset.sum_congr rfl (fun w hw => Finset.sum_congr rfl (fun g hg => h1 w hw g hg))]
  rw [Finset.sum_comm]
  have h2 : ∀ g ∈ Gf, ∑ w ∈ Wf, ∑ i ∈ Idx,
      (if w = Wc i ∧ g = Gc i then val i * phi (Wc i) (Gc i) else 0)
      = ∑ i ∈ Idx, (if g = Gc i then val i * phi (Wc i) (Gc i) else 0) := by
    intro g _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    by_cases hg : g = Gc i
    · have hcond : ∀ w : ℤ, (w = Wc i ∧ g = Gc i) ↔ (w = Wc i) := by
        intro w; simp [hg]
      calc ∑ w ∈ Wf, (if w = Wc i ∧ g = Gc i then val i * phi (Wc i) (Gc i) else 0)
          = ∑ w ∈ Wf, (if w = Wc i then val i * phi (Wc i) (Gc i) else 0) :=
            Finset.sum_congr rfl fun w _ => by rw [if_congr (hcond w) rfl rfl]
        _ = val i * phi (Wc i) (Gc i) := by
            rw [Finset.sum_ite_eq' Wf (Wc i) (fun _ => val i * phi (Wc i) (Gc i)),
              if_pos (hW i hi)]
        _ = if g = Gc i then val i * phi (Wc i) (Gc i) else 0 := by rw [if_pos hg]
    · simp [hg]
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_ite_eq' Gf (Gc i) (fun _ => val i * phi (Wc i) (Gc i)), if_pos (hG i hi)]

/-- Unfolding the 5-fold product index into nested sums. -/
theorem sum_prod5 {A : Type*} [AddCommMonoid A] (S T H : Finset ℤ)
    (F : ℤ × ℤ × ℤ × ℤ × ℤ → A) :
    ∑ i ∈ S ×ˢ (T ×ˢ (T ×ˢ (H ×ˢ H))), F i
      = ∑ s ∈ S, ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ h₁ ∈ H, ∑ h₂ ∈ H, F (s, t₁, t₂, h₁, h₂) := by
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [Finset.sum_product]

/-- Exact factorisation of a 5-fold nested sum whose summand is a product of
factors depending on disjoint groups of variables. -/
theorem sum5_factor (S T H : Finset ℤ) (A : ℤ → ℂ) (B C : ℤ → ℤ → ℂ) (D E : ℤ → ℂ) :
    ∑ s ∈ S, ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ h₁ ∈ H, ∑ h₂ ∈ H,
        (A s * B s t₁ * C s t₂ * D h₁ * E h₂)
      = (∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂) *
          ∑ s ∈ S, (A s * (∑ t₁ ∈ T, B s t₁) * (∑ t₂ ∈ T, C s t₂)) := by
  have level2 : ∀ s t₁ t₂ h₁ : ℤ,
      ∑ h₂ ∈ H, (A s * B s t₁ * C s t₂ * D h₁ * E h₂)
        = (A s * B s t₁ * C s t₂ * D h₁) * (∑ h₂ ∈ H, E h₂) := by
    intro s t₁ t₂ h₁; rw [Finset.mul_sum]
  have level3 : ∀ s t₁ t₂ : ℤ,
      ∑ h₁ ∈ H, ∑ h₂ ∈ H, (A s * B s t₁ * C s t₂ * D h₁ * E h₂)
        = (A s * B s t₁ * C s t₂) * ((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂)) := by
    intro s t₁ t₂
    rw [Finset.sum_congr rfl (fun h₁ _ => level2 s t₁ t₂ h₁), ← Finset.sum_mul,
      ← Finset.mul_sum]
    ring
  have level4 : ∀ s t₁ : ℤ,
      ∑ t₂ ∈ T, ∑ h₁ ∈ H, ∑ h₂ ∈ H, (A s * B s t₁ * C s t₂ * D h₁ * E h₂)
        = (A s * B s t₁) * ((∑ t₂ ∈ T, C s t₂) *
            ((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂))) := by
    intro s t₁
    rw [Finset.sum_congr rfl (fun t₂ _ => level3 s t₁ t₂)]
    have : ∀ t₂ : ℤ, (A s * B s t₁ * C s t₂) * ((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂))
        = (A s * B s t₁) * (((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂)) * C s t₂) := by
      intro t₂; ring
    rw [Finset.sum_congr rfl (fun t₂ _ => this t₂), ← Finset.mul_sum, ← Finset.mul_sum]
    ring
  have level5 : ∀ s : ℤ,
      ∑ t₁ ∈ T, ∑ t₂ ∈ T, ∑ h₁ ∈ H, ∑ h₂ ∈ H, (A s * B s t₁ * C s t₂ * D h₁ * E h₂)
        = ((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂)) *
            (A s * (∑ t₁ ∈ T, B s t₁) * (∑ t₂ ∈ T, C s t₂)) := by
    intro s
    rw [Finset.sum_congr rfl (fun t₁ _ => level4 s t₁)]
    have : ∀ t₁ : ℤ, (A s * B s t₁) * ((∑ t₂ ∈ T, C s t₂) *
          ((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂)))
        = (A s * ((∑ t₂ ∈ T, C s t₂) * ((∑ h₁ ∈ H, D h₁) * (∑ h₂ ∈ H, E h₂)))) * B s t₁ := by
      intro t₁; ring
    rw [Finset.sum_congr rfl (fun t₁ _ => this t₁), ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl (fun s _ => level5 s), ← Finset.mul_sum]

/-- **The load-bearing double-Fourier factorisation.**

`Γ̃_{u,ℓ}(α, η) = K(α−η) · conj K(−η) · ∑_s e(−α ν_s) C_s(s(α−η)) conj C_s(−s η)`.

Every sign is kernel-checked. -/
theorem GammaTilde_factorisation (S T H Wf Gf : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (alpha eta : ℝ)
    (hW : ∀ i ∈ gammaIndex S T H, wCoord nu i ∈ Wf)
    (hG : ∀ i ∈ gammaIndex S T H, gCoord i ∈ Gf) :
    GammaTilde S T H Wf Gf c kappa nu alpha eta
      = KHat H kappa (alpha - eta) * (starRingEnd ℂ) (KHat H kappa (-eta)) *
          ∑ s ∈ S, eR (-(alpha * ((nu s : ℤ) : ℝ))) *
            CHat T (c s) ((s : ℝ) * (alpha - eta)) *
            (starRingEnd ℂ) (CHat T (c s) (-((s : ℝ) * eta))) := by
  classical
  -- Step 1: collapse the `(w,g)` sums.
  have step1 : GammaTilde S T H Wf Gf c kappa nu alpha eta
      = ∑ i ∈ gammaIndex S T H, gammaVal c kappa i *
          eR (-(alpha * ((wCoord nu i : ℤ) : ℝ)) - eta * ((gCoord i : ℤ) : ℝ)) := by
    unfold GammaTilde GammaTwoLine
    exact sum_indicator_fibre Wf Gf (gammaIndex S T H) (wCoord nu) gCoord
      (gammaVal c kappa) (fun w g => eR (-(alpha * (w : ℝ)) - eta * (g : ℝ))) hW hG
  -- Step 2: split the phase into the five independent factors.
  have hsplit : ∀ i : ℤ × ℤ × ℤ × ℤ × ℤ,
      gammaVal c kappa i *
          eR (-(alpha * ((wCoord nu i : ℤ) : ℝ)) - eta * ((gCoord i : ℤ) : ℝ))
        = (eR (-(alpha * ((nu i.1 : ℤ) : ℝ)))) *
            (c i.1 i.2.1 * eR (-((i.1 : ℝ) * (alpha - eta) * (i.2.1 : ℝ)))) *
            ((starRingEnd ℂ) (c i.1 i.2.2.1) * eR (-((i.1 : ℝ) * eta * (i.2.2.1 : ℝ)))) *
            (kappa i.2.2.2.1 * eR (-((alpha - eta) * (i.2.2.2.1 : ℝ)))) *
            ((starRingEnd ℂ) (kappa i.2.2.2.2) * eR (-(eta * (i.2.2.2.2 : ℝ)))) := by
    intro i
    have hph : eR (-(alpha * ((wCoord nu i : ℤ) : ℝ)) - eta * ((gCoord i : ℤ) : ℝ))
        = eR (-(alpha * ((nu i.1 : ℤ) : ℝ))) *
            eR (-((i.1 : ℝ) * (alpha - eta) * (i.2.1 : ℝ))) *
            eR (-((i.1 : ℝ) * eta * (i.2.2.1 : ℝ))) *
            eR (-((alpha - eta) * (i.2.2.2.1 : ℝ))) *
            eR (-(eta * (i.2.2.2.2 : ℝ))) := by
      rw [← eR_add5]
      congr 1
      unfold wCoord gCoord
      push_cast
      ring
    rw [hph]
    unfold gammaVal
    ring
  rw [step1, Finset.sum_congr rfl (fun i _ => hsplit i)]
  -- Step 3: nested sums and factorisation.
  unfold gammaIndex
  rw [sum_prod5 S T H
    (fun i => (eR (-(alpha * ((nu i.1 : ℤ) : ℝ)))) *
      (c i.1 i.2.1 * eR (-((i.1 : ℝ) * (alpha - eta) * (i.2.1 : ℝ)))) *
      ((starRingEnd ℂ) (c i.1 i.2.2.1) * eR (-((i.1 : ℝ) * eta * (i.2.2.1 : ℝ)))) *
      (kappa i.2.2.2.1 * eR (-((alpha - eta) * (i.2.2.2.1 : ℝ)))) *
      ((starRingEnd ℂ) (kappa i.2.2.2.2) * eR (-(eta * (i.2.2.2.2 : ℝ)))))]
  rw [sum5_factor S T H
    (fun s => eR (-(alpha * ((nu s : ℤ) : ℝ))))
    (fun s t => c s t * eR (-((s : ℝ) * (alpha - eta) * (t : ℝ))))
    (fun s t => (starRingEnd ℂ) (c s t) * eR (-((s : ℝ) * eta * (t : ℝ))))
    (fun h => kappa h * eR (-((alpha - eta) * (h : ℝ))))
    (fun h => (starRingEnd ℂ) (kappa h) * eR (-(eta * (h : ℝ))))]
  -- Step 4: identify the four factors.
  have hK1 : ∑ h ∈ H, kappa h * eR (-((alpha - eta) * (h : ℝ))) = KHat H kappa (alpha - eta) := by
    unfold KHat
    exact Finset.sum_congr rfl fun h _ => by rw [mul_comm (alpha - eta) ((h : ℝ))]
  have hK2 : ∑ h ∈ H, (starRingEnd ℂ) (kappa h) * eR (-(eta * (h : ℝ)))
      = (starRingEnd ℂ) (KHat H kappa (-eta)) := by
    unfold KHat
    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_mul, eR_conj]
    congr 2
    ring
  have hC1 : ∀ s : ℤ, ∑ t ∈ T, c s t * eR (-((s : ℝ) * (alpha - eta) * (t : ℝ)))
      = CHat T (c s) ((s : ℝ) * (alpha - eta)) := by
    intro s
    unfold CHat
    exact Finset.sum_congr rfl fun t _ => by rw [mul_assoc]
  have hC2 : ∀ s : ℤ, ∑ t ∈ T, (starRingEnd ℂ) (c s t) * eR (-((s : ℝ) * eta * (t : ℝ)))
      = (starRingEnd ℂ) (CHat T (c s) (-((s : ℝ) * eta))) := by
    intro s
    unfold CHat
    rw [map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, eR_conj]
    congr 2
    ring
  rw [hK1, hK2]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by rw [hC1 s, hC2 s]


/-- **Recovery of `Γ̃` from `Γ̂` in `η`.**  Exact identity. -/
theorem GammaTilde_eq_sum_GammaHat (S T H Wf Gf : Finset ℤ) (c : ℤ → ℤ → ℂ)
    (kappa : ℤ → ℂ) (nu : ℤ → ℤ) (alpha eta : ℝ) :
    GammaTilde S T H Wf Gf c kappa nu alpha eta
      = ∑ g ∈ Gf, GammaHat S T H Wf c kappa nu g alpha * eR (-(eta * (g : ℝ))) := by
  unfold GammaTilde GammaHat
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [mul_assoc, ← eR_add]
  congr 2

/-! ## 5. The exact `Ĥ` pushforward -/

/-- The abstract pushed coefficient `H(q,v)` as a fibrewise sum over
`((u,ℓ), w)`. -/
noncomputable def HcoefPush (Upairs : Finset (ℤ × ℤ)) (Wset : Finset ℤ)
    (coef : (ℤ × ℤ) → ℤ → ℂ) (ycan : ℤ × ℤ → ℤ) (q : ℤ) : ℂ :=
  ∑ i ∈ Upairs ×ˢ Wset,
    (if q = ycan i.1 + i.1.1 * i.2 then coef i.1 i.2 else 0)

/-- **Exact `Ĥ_j(θ,v)` pushforward.**

`∑_q H(q,v) e(−θ q) = ∑_{(u,ℓ)} e(−θ y_{u,ℓ}) ∑_w coef(u,ℓ,w) e(−(uθ) w)`.

No analytic estimate is used. -/
theorem Hhat_exact_pushforward (Upairs : Finset (ℤ × ℤ)) (Wset : Finset ℤ) (Qs : Finset ℤ)
    (coef : (ℤ × ℤ) → ℤ → ℂ) (ycan : ℤ × ℤ → ℤ) (theta : ℝ)
    (hmaps : ∀ i ∈ Upairs ×ˢ Wset, ycan i.1 + i.1.1 * i.2 ∈ Qs) :
    ∑ q ∈ Qs, HcoefPush Upairs Wset coef ycan q * eR (-(theta * (q : ℝ)))
      = ∑ p ∈ Upairs, eR (-(theta * ((ycan p : ℤ) : ℝ))) *
          ∑ w ∈ Wset, coef p w * eR (-(((p.1 : ℝ) * theta) * (w : ℝ))) := by
  classical
  have hcollapse : ∑ q ∈ Qs, HcoefPush Upairs Wset coef ycan q * eR (-(theta * (q : ℝ)))
      = ∑ i ∈ Upairs ×ˢ Wset,
          coef i.1 i.2 * eR (-(theta * ((ycan i.1 + i.1.1 * i.2 : ℤ) : ℝ))) := by
    unfold HcoefPush
    have h1 : ∀ q ∈ Qs,
        (∑ i ∈ Upairs ×ˢ Wset, (if q = ycan i.1 + i.1.1 * i.2 then coef i.1 i.2 else 0)) *
            eR (-(theta * (q : ℝ)))
          = ∑ i ∈ Upairs ×ˢ Wset,
              (if q = ycan i.1 + i.1.1 * i.2 then
                coef i.1 i.2 * eR (-(theta * ((ycan i.1 + i.1.1 * i.2 : ℤ) : ℝ))) else 0) := by
      intro q _
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : q = ycan i.1 + i.1.1 * i.2
      · rw [if_pos h, if_pos h, h]
      · rw [if_neg h, if_neg h, zero_mul]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_ite_eq' Qs (ycan i.1 + i.1.1 * i.2)
      (fun _ => coef i.1 i.2 * eR (-(theta * ((ycan i.1 + i.1.1 * i.2 : ℤ) : ℝ)))),
      if_pos (hmaps i hi)]
  rw [hcollapse, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hsplit : eR (-(theta * ((ycan p : ℤ) : ℝ))) * eR (-(((p.1 : ℝ) * theta) * (w : ℝ)))
      = eR (-(theta * ((ycan p + p.1 * w : ℤ) : ℝ))) := by
    rw [← eR_add]
    congr 1
    push_cast
    ring
  show coef p w * eR (-(theta * ((ycan p + p.1 * w : ℤ) : ℝ))) = _
  rw [← hsplit]
  ring

/-! ## 6–7. The analytic sockets (UNINHABITED) -/

/-- **UNINHABITED analytic socket** for the C4Shift `q`-Fourier pushforward.

The bound field is the discrete-Haar form of

`∫_θ [ ∑_v | ∑_{u ∣ v} |a₄(u)|² ∑_ℓ e(−θ y_{u,ℓ}) Γ̂_{u,ℓ,v/u}(uθ) |² ]^{1/2}
   ≤ naturalBound`,

whose research value is `Y^{3/4} log^C X`.  **Lean does not prove this
estimate**; the structure is never constructed. -/
structure C4ShiftQFourierPushforwardInput where
  /-- Number of discrete frequencies (discrete Haar measure on the torus). -/
  P : ℕ
  /-- The shift support. -/
  Vset : Finset ℤ
  /-- For each `v`, the physical `(u, ℓ)` pairs with `u ∣ v` and `u` in range. -/
  Upairs : ℤ → Finset (ℤ × ℤ)
  /-- The `u`-side coefficient. -/
  a4 : ℤ → ℂ
  /-- The canonical reciprocal residue `y_{u,ℓ}`. -/
  ycan : ℤ × ℤ → ℤ
  /-- The `w`-support. -/
  Wset : Finset ℤ
  /-- The Γ-source, indexed by `v`, the pair `(u,ℓ)` and `w`. -/
  Gam : ℤ → (ℤ × ℤ) → ℤ → ℂ
  /-- The transform whose norm is estimated. -/
  Hh : ℕ → ℤ → ℂ
  /-- `Hh` really is the exact pushforward of the source fields. -/
  pushforward : ∀ (k : ℕ) (v : ℤ), Hh k v
    = ∑ p ∈ Upairs v, ((‖a4 p.1‖ ^ 2 : ℝ) : ℂ) *
        eR (-(((k : ℝ) / (P : ℝ)) * ((ycan p : ℤ) : ℝ))) *
        ∑ w ∈ Wset, Gam v p w * eR (-(((p.1 : ℝ) * ((k : ℝ) / (P : ℝ))) * (w : ℝ)))
  /-- The natural bound (research value `Y^{3/4} log^C X`). -/
  naturalBound : ℝ
  /-- **The analytic estimate itself — never proved here.** -/
  bound : (1 / (P : ℝ)) * ∑ k ∈ Finset.range P,
      Real.sqrt (∑ v ∈ Vset, ‖Hh k v‖ ^ 2) ≤ naturalBound

/-- **UNINHABITED, STRONGER THAN SOURCE-MINIMAL, OPEN.**

The `L²` transfer `∑_{q,v} |H(q,v)|² ≤ naturalSquaredBound`. -/
structure C4ShiftPushforwardU2TransferInput where
  /-- The `q`-support. -/
  Qs : Finset ℤ
  /-- The shift support. -/
  Vset : Finset ℤ
  /-- The pushed coefficient. -/
  Hqv : ℤ → ℤ → ℂ
  /-- The claimed squared bound. -/
  naturalSquaredBound : ℝ
  /-- **The analytic estimate itself — never proved here.** -/
  bound : ∑ q ∈ Qs, ∑ v ∈ Vset, ‖Hqv q v‖ ^ 2 ≤ naturalSquaredBound

/-! ## 8. The conditional structural compiler -/

/-- An abstract top-band operator conclusion: a value together with a bound it
satisfies.  Producing one is *not* a closure of anything; it merely records that
a bound has been derived from its hypotheses. -/
structure TopBandOperatorConclusion where
  /-- The bounded quantity. -/
  value : ℂ
  /-- The bound. -/
  bound : ℝ
  /-- The derivation. -/
  holds : ‖value‖ ≤ bound

/-- **Conditional compiler.**  *If* the (uninhabited) C4Shift `q`-Fourier
pushforward socket is inhabited, *and* the (uninhabited) β-`U²` input is
inhabited on the same grid and shift support, *then* the abstract top-band
operator conclusion is inhabited, with bound
`betaBound · P · naturalBound`.

This proves **no** analytic statement: both antecedents are uninhabited in this
repository, and Gate 1B is not closed by it. -/
noncomputable def topBand_conditional_compiler
    (Iq : C4ShiftQFourierPushforwardInput) (J : BetaU2Input)
    (hP : J.P = Iq.P) (hV : J.Vset = Iq.Vset) (hb : 0 ≤ J.betaBound)
    (hPpos : 0 < Iq.P) :
    TopBandOperatorConclusion := by
  classical
  refine ⟨∑ k ∈ Finset.range J.P, ∑ v ∈ J.Vset, Iq.Hh k v * J.Cc k v,
    J.betaBound * ((Iq.P : ℝ) * Iq.naturalBound), ?_⟩
  have h1 := dual_cauchy_of_betaU2 J Iq.Hh
  have hsum : ∑ k ∈ Finset.range J.P, Real.sqrt (∑ v ∈ J.Vset, ‖Iq.Hh k v‖ ^ 2)
      ≤ (Iq.P : ℝ) * Iq.naturalBound := by
    have hPR : (0 : ℝ) < (Iq.P : ℝ) := by exact_mod_cast hPpos
    have h2 := Iq.bound
    rw [hP, hV]
    have := mul_le_mul_of_nonneg_left h2 (le_of_lt hPR)
    calc ∑ k ∈ Finset.range Iq.P, Real.sqrt (∑ v ∈ Iq.Vset, ‖Iq.Hh k v‖ ^ 2)
        = (Iq.P : ℝ) * ((1 / (Iq.P : ℝ)) *
            ∑ k ∈ Finset.range Iq.P, Real.sqrt (∑ v ∈ Iq.Vset, ‖Iq.Hh k v‖ ^ 2)) := by
          field_simp
      _ ≤ (Iq.P : ℝ) * Iq.naturalBound := this
  exact h1.trans (mul_le_mul_of_nonneg_left hsum hb)

/-! ## 9. Status metadata for this phase (metadata only — never evidence) -/

open Status in
/-- Status rows contributed by the C4Shift Fourier frontier. -/
def statusRows : List LedgerEntry :=
  [ ⟨"C4SHIFT-GAMMATILDE-FACTORISATION45", Status.provedAlgebraic,
     "FORMALLY BANKED, KERNEL-PROVED WITH EVERY SIGN CHECKED: GammaTilde_factorisation."⟩,
    ⟨"C4SHIFT-HHAT-EXACT-PUSHFORWARD45", Status.provedAlgebraic,
     "FORMALLY BANKED. Hhat_exact_pushforward: exact (q -> (u,ell,w)) change of variables with the split phase. No analytic estimate."⟩,
    ⟨"C4SHIFT-TOPBAND-KERNEL-INPUT45", Status.sourceOpen,
     "UNINHABITED. TopBandKernelInput (identification of the kappa-transform with the literal top-band multiplier)."⟩,
    ⟨"C4SHIFT-QFOURIER-PUSHFORWARD45", Status.analyticOpen,
     "ANALYTIC OPEN / UNINHABITED. C4ShiftQFourierPushforwardInput, whose bound field is the discrete-Haar form of the research natural bound Y^(3/4) log^C X. Never constructed."⟩,
    ⟨"C4SHIFT-PUSHFORWARD-U2-TRANSFER45", Status.analyticOpen,
     "STRONGER THAN SOURCE-MINIMAL; OPEN / UNINHABITED. C4ShiftPushforwardU2TransferInput."⟩,
    ⟨"C4SHIFT-CONDITIONAL-COMPILER45", Status.conditionalCompiler,
     "topBand_conditional_compiler is an implication from two UNINHABITED inputs. It does NOT close Gate 1B and does NOT close the local major-tree match."⟩ ]

/-- No row of this phase is `closed`. -/
theorem statusRows_no_closed : ∀ e ∈ statusRows, e.status ≠ Status.closed := by decide

end C4ShiftQFourier
end CurrentProgramme
end TwinPrimeProject
