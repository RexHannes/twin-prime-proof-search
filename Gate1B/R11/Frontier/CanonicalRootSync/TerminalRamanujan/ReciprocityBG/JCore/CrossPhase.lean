/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : the exact cross phase  (J6)

Append-only module; exact algebra in the additive circle `ℚ / ℤ`, plus the complex-exponential
form derived from the banked `ee`-calculus of `CRTPhase.lean`.  No analytic statement.

The JCORE cross phase of a pair of core points is carried by three *separately defined* pieces:

* the **source residue** factor `e_z(A_s ē)`;
* the **second reciprocal CRT** factor `e_c(B_c · (z+ek)⁻¹)`;
* the **determinant** factor `e(−2Δ / (e D z ℓ u ũ))`, `ℓ = [v, ṽ]`.

§1 defines the three phases, each inverse being taken modulo the modulus in which it is
legitimate, and proves that each local phase is well defined modulo that modulus.  §2 proves the
**exact determinant identity** `detPhase = (−2/(eDz)) · (n/(uv) − ñ/(ũṽ))`, which is the genuine
content: the determinant factor is exactly the normalised frequency difference of
`Determinant.lean`.  §3 gives the factorisation of the exponential.  §4 records that **no
cross-copy coprimality** (`(u,ṽ)=1`, `(ũ,v)=1`) is used: the factorisation is exhibited on data
where both fail.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.CleanSupport

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. The three local phases and their legitimacy -/

/-- `b` is an inverse of `a` modulo `m`. -/
def IsInverseMod (a b m : ℤ) : Prop := a * b ≡ 1 [ZMOD m]

/-- **Inverses are unique modulo their own modulus.**  This is why every phase below may be
written with "the" local inverse. -/
theorem isInverseMod_unique {a b b' m : ℤ} (h : IsInverseMod a b m) (h' : IsInverseMod a b' m) :
    b ≡ b' [ZMOD m] := by
  have hd : m ∣ a * (b - b') := by
    have h1 : m ∣ a * b - 1 := Int.ModEq.dvd h.symm
    have h2 : m ∣ a * b' - 1 := Int.ModEq.dvd h'.symm
    have : a * (b - b') = (a * b - 1) - (a * b' - 1) := by ring
    rw [this]
    exact dvd_sub h1 h2
  have : m ∣ b - b' := dvd_of_unit_mul h hd
  exact (Int.modEq_iff_dvd.mpr (by simpa [neg_sub] using (dvd_neg.mpr this)))

/-- The **source residue phase** `A_s ē / z`, with `ē` an inverse of `e` modulo `z`. -/
def sourcePhase (As ebar : ℤ) (z : ℤ) : ℚ := ((As * ebar : ℤ) : ℚ) / ((z : ℤ) : ℚ)

/-- The **second reciprocal CRT phase** `B_c · (z+ek)⁻¹ / c`, with the inverse taken modulo the
core conductor `c`. -/
def crtPhase (Bc cinv : ℤ) (c : ℤ) : ℚ := ((Bc * cinv : ℤ) : ℚ) / ((c : ℤ) : ℚ)

/-- The **determinant phase** `−2Δ / (e D z ℓ u ũ)`, `ℓ = [v, ṽ]`. -/
def detPhase (eDz : ℤ) (i j : Core) : ℚ :=
  ((-2 * Delta i j : ℤ) : ℚ) / (((eDz : ℤ) : ℚ) * (((lcmPart i j * i.u * j.u : ℕ) : ℚ)))

/-- **The source phase is well defined modulo `z`**: replacing the local inverse by a congruent
residue does not change the phase in `ℚ / ℤ`. -/
theorem sourcePhase_congr {As ebar ebar' z : ℤ} (hz : (z : ℚ) ≠ 0) (h : ebar ≡ ebar' [ZMOD z]) :
    CongMod1 (sourcePhase As ebar z) (sourcePhase As ebar' z) := by
  obtain ⟨t, ht⟩ : z ∣ ebar - ebar' := Int.ModEq.dvd h.symm
  refine ⟨As * t, ?_⟩
  have hzint : (As * ebar - As * ebar' : ℤ) = z * (As * t) := by linear_combination As * ht
  have hq : ((As * ebar : ℤ) : ℚ) - ((As * ebar' : ℤ) : ℚ)
      = ((z : ℤ) : ℚ) * ((As * t : ℤ) : ℚ) := by
    exact_mod_cast congrArg (fun m : ℤ => (m : ℚ)) hzint
  unfold sourcePhase
  rw [div_sub_div_same, hq]
  field_simp

/-- **The core phase is well defined modulo `c`.** -/
theorem crtPhase_congr {Bc cinv cinv' c : ℤ} (hc : (c : ℚ) ≠ 0) (h : cinv ≡ cinv' [ZMOD c]) :
    CongMod1 (crtPhase Bc cinv c) (crtPhase Bc cinv' c) :=
  sourcePhase_congr hc h

/-! ## 2. The determinant factor is the normalised frequency difference -/

/-- **Exact determinant identity.**  The determinant phase is exactly `−2/(eDz)` times the
rational-frequency difference of the two core copies. -/
theorem detPhase_eq_freq_diff {eDz : ℤ} (hne : ((eDz : ℤ) : ℚ) ≠ 0) {i j : Core}
    (hiu : 0 < i.u) (hiv : 0 < i.v) (hju : 0 < j.u) (hjv : 0 < j.v) :
    detPhase eDz i j = (-2 / ((eDz : ℤ) : ℚ)) * (freq i - freq j) := by
  have hl : 0 < lcmPart i j := Nat.lcm_pos hiv hjv
  have hden : (((lcmPart i j * i.u * j.u : ℕ) : ℚ)) ≠ 0 := by
    have : 0 < lcmPart i j * i.u * j.u := Nat.mul_pos (Nat.mul_pos hl hiu) hju
    positivity
  rw [freq_sub_eq_delta_div hiu hiv hju hjv]
  unfold detPhase
  push_cast
  field_simp

/-- **On the unequal-frequency owner the determinant phase is nonzero.** -/
theorem detPhase_ne_zero {eDz : ℤ} (hne : ((eDz : ℤ) : ℚ) ≠ 0) {i j : Core}
    (hiu : 0 < i.u) (hiv : 0 < i.v) (hju : 0 < j.u) (hjv : 0 < j.v)
    (h : UnequalRationalFrequency i j) : detPhase eDz i j ≠ 0 := by
  rw [detPhase_eq_freq_diff hne hiu hiv hju hjv]
  have hfr : freq i - freq j ≠ 0 := by
    intro h0
    exact h (by unfold EqualRationalFrequency; linarith)
  exact mul_ne_zero (div_ne_zero (by norm_num) hne) hfr

/-! ## 3. The exact cross-phase factorisation -/

/-- **The JCORE cross-phase factorisation.**  If the phase difference of the two copies splits
into the source residue phase, the second reciprocal CRT phase and the determinant phase — the
decomposition supplied as an explicit hypothesis, never as a fabricated analytic input — then the
exponential factorises into the three corresponding factors, the last one being exactly
`e(−2Δ/(eDzℓuũ))`.

No cross-copy coprimality is assumed anywhere in this statement. -/
theorem crossPhase_factorisation {Theta : ℚ} {As ebar z Bc cinv c eDz : ℤ} {i j : Core}
    (hdec : Theta = sourcePhase As ebar z + crtPhase Bc cinv c + detPhase eDz i j) :
    ee Theta = ee (sourcePhase As ebar z) * ee (crtPhase Bc cinv c) * ee (detPhase eDz i j) := by
  rw [hdec, ee_add, ee_add]

/-- The same factorisation up to the additive circle: a phase congruent mod 1 to the three-part
decomposition has the factorised exponential. -/
theorem crossPhase_factorisation_mod1 {Theta : ℚ} {As ebar z Bc cinv c eDz : ℤ} {i j : Core}
    (hdec : CongMod1 Theta
      (sourcePhase As ebar z + crtPhase Bc cinv c + detPhase eDz i j)) :
    ee Theta = ee (sourcePhase As ebar z) * ee (crtPhase Bc cinv c) * ee (detPhase eDz i j) := by
  rw [ee_congr hdec, ee_add, ee_add]

/-! ## 4. No cross-copy coprimality is used -/

/-- **The factorisation holds on data violating both cross-copy coprimalities.**  With
`u = ṽ = 2` and `ũ = v = 2` we have `(u, ṽ) = 2` and `(ũ, v) = 2`, and the cross-phase
factorisation is still available: the simplifying hypotheses `(u,ṽ)=1`, `(ũ,v)=1` are not needed
and are not assumed. -/
theorem crossPhase_without_cross_coprimality :
    ∃ i j : Core, 1 < Nat.gcd i.u j.v ∧ 1 < Nat.gcd j.u i.v
      ∧ ∀ (As ebar z Bc cinv c eDz : ℤ) (Theta : ℚ),
          Theta = sourcePhase As ebar z + crtPhase Bc cinv c + detPhase eDz i j →
          ee Theta = ee (sourcePhase As ebar z) * ee (crtPhase Bc cinv c)
            * ee (detPhase eDz i j) := by
  refine ⟨⟨1, 2, 2⟩, ⟨1, 2, 2⟩, by norm_num, by norm_num, ?_⟩
  intro As ebar z Bc cinv c eDz Theta h
  exact crossPhase_factorisation h

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
