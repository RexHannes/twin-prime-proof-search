/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the combined conductor  (J8)

Append-only module; exact algebra only, no analytic estimate.

Two finite reciprocal phases with coprime reduced moduli `m` (source) and `c` (core) combine
into **one shifted reciprocal phase**.  The construction is explicit:

* the CRT shift `t₀` satisfies the two congruence conditions `m ∣ t₀` and `t₀ ≡ w (mod c)`,
  where `w` is the core shift (`z + ek` written as `e + w` after removing the unit `k`);
* the effective modulus is `q_eff = m·c` and the effective numerator is
  `A_eff = A·c + B·m`;
* with `X` the inverse of `e + t₀` modulo `q_eff`,

```
e_m(A ē) · e_c(B (e+w)⁻¹)  =  e_{q_eff}(A_eff · (e+t₀)⁻¹).
```

§1 constructs the shift, §2 proves the combination in `ℚ / ℤ` and for the exponential, §3 gives
the exact small-label instantiation `w = z k̄`, and §4 isolates the *general-label* statement as
exactly one explicit proposition `CombinedConductorRealisation`, which is **never inhabited** —
the general case is not claimed.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.Conductor

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The CRT shift -/

/-- **Existence of the CRT shift `t₀`** satisfying the two congruence conditions `m ∣ t₀` and
`t₀ ≡ w (mod c)`, for coprime moduli. -/
theorem exists_crt_shift {m c : ℤ} (h : IsCoprime m c) (w : ℤ) :
    ∃ t0 : ℤ, m ∣ t0 ∧ t0 ≡ w [ZMOD c] := by
  obtain ⟨α, β, hαβ⟩ := h
  refine ⟨w * (α * m), ⟨w * α, by ring⟩, ?_⟩
  have : w * (α * m) - w = c * (-(w * β)) := by
    have : α * m = 1 - β * c := by linarith [hαβ]
    rw [this]; ring
  exact Int.modEq_iff_dvd.mpr ⟨w * β, by linarith [this]⟩

/-! ## 2. The combined conductor identity -/

/-- The effective modulus `q_eff = m c`. -/
def qEff (m c : ℤ) : ℤ := m * c

/-- The effective numerator `A_eff = A c + B m`. -/
def aEff (A B m c : ℤ) : ℤ := A * c + B * m

/-- **Two local reciprocal phases combine into one.**  If `Em` and `Ec` are the local inverses
used by the two phases and `X` is congruent to each of them modulo the respective modulus, then
the sum of the two phases equals, in `ℚ / ℤ`, the single phase with modulus `q_eff = mc` and
numerator `A_eff = Ac + Bm` at `X`. -/
theorem combine_two_phases {A B Em Ec X m c : ℤ} (hm : m ≠ 0) (hc : c ≠ 0)
    (h1 : Em ≡ X [ZMOD m]) (h2 : Ec ≡ X [ZMOD c]) :
    CongMod1 (sourcePhase A Em m + crtPhase B Ec c) (sourcePhase (aEff A B m c) X (qEff m c)) := by
  obtain ⟨s, hs⟩ : m ∣ Em - X := Int.ModEq.dvd h1.symm
  obtain ⟨r, hr⟩ : c ∣ Ec - X := Int.ModEq.dvd h2.symm
  refine ⟨A * s + B * r, ?_⟩
  have hmq : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm
  have hcq : ((c : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hc
  have hsq : ((Em : ℤ) : ℚ) - ((X : ℤ) : ℚ) = ((m : ℤ) : ℚ) * ((s : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hs
  have hrq : ((Ec : ℤ) : ℚ) - ((X : ℤ) : ℚ) = ((c : ℤ) : ℚ) * ((r : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun t : ℤ => (t : ℚ)) hr
  unfold sourcePhase crtPhase aEff qEff
  push_cast
  field_simp
  linear_combination ((A : ℚ) * (c : ℚ)) * hsq + ((m : ℚ) * (B : ℚ)) * hrq

/-- **The shifted-reciprocal form.**  With the CRT shift `t₀` (`m ∣ t₀`, `t₀ ≡ w (mod c)`), the
source phase at `e` and the core phase at `e + w` are phases of the *same* argument `e + t₀`
modulo their own moduli, so they combine into the single shifted reciprocal
`e_{q_eff}(A_eff · (e+t₀)⁻¹)`. -/
theorem combined_conductor_shifted {A B e w t0 Em Ec X m c : ℤ} (hm : m ≠ 0) (hc : c ≠ 0)
    (ht0m : m ∣ t0) (ht0c : t0 ≡ w [ZMOD c])
    (hEm : IsInverseMod e Em m) (hEc : IsInverseMod (e + w) Ec c)
    (hX : IsInverseMod (e + t0) X (qEff m c)) :
    CongMod1 (sourcePhase A Em m + crtPhase B Ec c)
      (sourcePhase (aEff A B m c) X (qEff m c)) := by
  -- `X` inverts `e` modulo `m`
  have hXm : IsInverseMod e X m := by
    have hdvd : m ∣ qEff m c := ⟨c, rfl⟩
    have h0 : (e + t0) * X ≡ 1 [ZMOD m] := Int.ModEq.of_dvd hdvd hX
    have het : e + t0 ≡ e [ZMOD m] :=
      Int.modEq_iff_dvd.mpr (by simpa using (dvd_neg.mpr ht0m))
    calc e * X ≡ (e + t0) * X [ZMOD m] := (het.symm).mul_right X
      _ ≡ 1 [ZMOD m] := h0
  -- `X` inverts `e + w` modulo `c`
  have hXc : IsInverseMod (e + w) X c := by
    have hdvd : c ∣ qEff m c := ⟨m, by unfold qEff; ring⟩
    have h0 : (e + t0) * X ≡ 1 [ZMOD c] := Int.ModEq.of_dvd hdvd hX
    have het : e + t0 ≡ e + w [ZMOD c] := (Int.ModEq.refl e).add ht0c
    calc (e + w) * X ≡ (e + t0) * X [ZMOD c] := (het.symm).mul_right X
      _ ≡ 1 [ZMOD c] := h0
  exact combine_two_phases hm hc (isInverseMod_unique hEm hXm) (isInverseMod_unique hEc hXc)

/-- Exponential form: the product of the two finite reciprocal phases is one shifted
reciprocal. -/
theorem ee_combined_conductor {A B e w t0 Em Ec X m c : ℤ} (hm : m ≠ 0) (hc : c ≠ 0)
    (ht0m : m ∣ t0) (ht0c : t0 ≡ w [ZMOD c])
    (hEm : IsInverseMod e Em m) (hEc : IsInverseMod (e + w) Ec c)
    (hX : IsInverseMod (e + t0) X (qEff m c)) :
    ee (sourcePhase A Em m) * ee (crtPhase B Ec c)
      = ee (sourcePhase (aEff A B m c) X (qEff m c)) := by
  rw [← ee_add]
  exact ee_congr (combined_conductor_shifted hm hc ht0m ht0c hEm hEc hX)

/-! ## 3. The small-label instantiation -/

/-- **The small-label case `z + e k`.**  If `k` is invertible modulo `c` with inverse `kbar`,
then `z + ek ≡ k(e + w) (mod c)` with `w = z·kbar`, so the second reciprocal factor is a phase in
the shifted argument `e + w` and §2 applies verbatim. -/
theorem smallLabel_shift {z e k kbar c : ℤ} (hk : IsInverseMod k kbar c) :
    z + e * k ≡ k * (e + z * kbar) [ZMOD c] := by
  have h1 : k * (e + z * kbar) - (z + e * k) = z * (k * kbar - 1) := by ring
  have h2 : c ∣ k * kbar - 1 := Int.ModEq.dvd hk.symm
  exact Int.modEq_iff_dvd.mpr (by rw [h1]; exact h2.mul_left z)

/-! ## 4. The general-label case is *not* claimed -/

/-- **`CombinedConductorRealisation`** — the single explicit proposition carrying the *general*
small-label combination: for a general label the two reduced conductors need not be coprime and
the combination requires a finite split into residue classes, which is not established here.
MISSING EXACT BRIDGE — stated, never inhabited, not an axiom. -/
def CombinedConductorRealisation (m c : ℤ) : Prop :=
  ∀ A B Em Ec : ℤ, ∃ Aeff X : ℤ,
    CongMod1 (sourcePhase A Em m + crtPhase B Ec c) (sourcePhase Aeff X (qEff m c))

/-- The coprime case of the general statement is discharged by §2 (choose `X` to be any common
inverse witness): the remaining content of `CombinedConductorRealisation` is genuinely the
non-coprime, general-label case. -/
theorem combinedConductorRealisation_of_common_residue {m c : ℤ} (hm : m ≠ 0) (hc : c ≠ 0)
    (hX : ∀ Em Ec : ℤ, ∃ X : ℤ, Em ≡ X [ZMOD m] ∧ Ec ≡ X [ZMOD c]) :
    CombinedConductorRealisation m c := by
  intro A B Em Ec
  obtain ⟨X, h1, h2⟩ := hX Em Ec
  exact ⟨aEff A B m c, X, combine_two_phases hm hc h1 h2⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
