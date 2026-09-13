/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : exact conductor lowering  (J7)

Append-only module; exact algebra only.  **No analytic estimate** is formalised here: no Weil
bound, no incomplete-sum bound, no external theorem.

§1 proves the elementary additive-character identity behind source-conductor lowering,

```
e_z(A ē) = e_m((A/g) ē),        g = (A, z),   m = z/g,
```

first as an exact identity of rational phases and then for the exponential.  §2 applies the same
lemma to the second (core) conductor `g_c = (B_c, c)`, `c_eff = c/g_c`.  §3 records the exact
complete-period identity for the additive character: the full period mean is `1` when the
modulus divides the frequency and `0` otherwise — stated only in the form in which it is true.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.CrossPhase

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-! ## 1. Source-conductor lowering -/

/-- **Exact conductor lowering for the source phase.**  If `g ∣ A` and `g ∣ z` with `g ≠ 0`, the
phase with modulus `z` and numerator `A` equals the phase with the reduced modulus `z/g` and
reduced numerator `A/g`. -/
theorem sourcePhase_lower {A z g ebar : ℤ} (hg : g ≠ 0) (hA : g ∣ A) (hz : g ∣ z) :
    sourcePhase A ebar z = sourcePhase (A / g) ebar (z / g) := by
  obtain ⟨A', rfl⟩ := hA
  obtain ⟨z', rfl⟩ := hz
  unfold sourcePhase
  rw [Int.mul_ediv_cancel_left _ hg, Int.mul_ediv_cancel_left _ hg]
  rcases eq_or_ne z' 0 with rfl | hz'
  · simp
  · have hgq : ((g : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hg
    have hz'q : ((z' : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hz'
    push_cast
    field_simp

/-- The gcd form: with `g = (A, z)` and `m = z/g` the source phase has modulus exactly `m`. -/
theorem sourcePhase_gcd_lower {A z ebar : ℤ} (h : Int.gcd A z ≠ 0) :
    sourcePhase A ebar z
      = sourcePhase (A / (Int.gcd A z : ℤ)) ebar (z / (Int.gcd A z : ℤ)) :=
  sourcePhase_lower (by exact_mod_cast h) (Int.gcd_dvd_left A z) (Int.gcd_dvd_right A z)

/-- Exponential form of source-conductor lowering. -/
theorem ee_sourcePhase_lower {A z g ebar : ℤ} (hg : g ≠ 0) (hA : g ∣ A) (hz : g ∣ z) :
    ee (sourcePhase A ebar z) = ee (sourcePhase (A / g) ebar (z / g)) := by
  rw [sourcePhase_lower hg hA hz]

/-! ## 2. Core-conductor lowering -/

/-- The reduced core conductor `c_eff = c / (B_c, c)`. -/
def cEff (Bc c : ℤ) : ℤ := c / (Int.gcd Bc c : ℤ)

/-- The reduced core numerator `B_c / (B_c, c)`. -/
def bEff (Bc c : ℤ) : ℤ := Bc / (Int.gcd Bc c : ℤ)

/-- **Exact conductor lowering for the second (core) reciprocal factor.** -/
theorem crtPhase_lower {Bc c cinv : ℤ} (h : Int.gcd Bc c ≠ 0) :
    crtPhase Bc cinv c = crtPhase (bEff Bc c) cinv (cEff Bc c) :=
  sourcePhase_lower (A := Bc) (z := c) (g := (Int.gcd Bc c : ℤ)) (by exact_mod_cast h)
    (Int.gcd_dvd_left Bc c) (Int.gcd_dvd_right Bc c)

/-! ## 3. The exact complete-period identity -/

/-- `e(k) = 1` for an integer phase. -/
theorem ee_intCast (k : ℤ) : ee (k : ℚ) = 1 := by
  unfold ee
  have : ((k : ℚ) : ℂ) = (k : ℂ) := by push_cast; ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/-- Powers of the additive character. -/
theorem ee_pow (q : ℚ) : ∀ t : ℕ, ee q ^ t = ee ((t : ℚ) * q)
  | 0 => by simp [ee]
  | (t + 1) => by
      rw [pow_succ, ee_pow q t, ← ee_add]
      congr 1
      push_cast
      ring

/-- `e(q) = 1` exactly when the phase is an integer. -/
theorem ee_eq_one_iff (q : ℚ) : ee q = 1 ↔ ∃ k : ℤ, q = (k : ℚ) := by
  constructor
  · intro h
    rw [ee, Complex.exp_eq_one_iff] at h
    obtain ⟨n, hn⟩ := h
    refine ⟨n, ?_⟩
    field_simp at hn
    exact_mod_cast hn
  · rintro ⟨k, rfl⟩
    exact ee_intCast k

/-- **The exact complete-period identity.**  The additive character of frequency `A/z` summed
over a full period is `z` when `z ∣ A`, and `0` otherwise.  Nothing is claimed about incomplete
sums. -/
theorem sum_period (A : ℤ) {z : ℕ} (hz : 0 < z) :
    ∑ t ∈ Finset.range z, ee (((A * t : ℤ) : ℚ) / ((z : ℤ) : ℚ))
      = if (z : ℤ) ∣ A then (z : ℂ) else 0 := by
  have hzq : ((z : ℤ) : ℚ) ≠ 0 := by
    have : (z : ℚ) ≠ 0 := by positivity
    exact_mod_cast this
  set ζ : ℂ := ee (((A : ℤ) : ℚ) / ((z : ℤ) : ℚ)) with hζ
  have hterm : ∀ t : ℕ, ee (((A * t : ℤ) : ℚ) / ((z : ℤ) : ℚ)) = ζ ^ t := by
    intro t
    rw [hζ, ee_pow]
    congr 1
    push_cast
    ring
  have hζz : ζ ^ z = 1 := by
    rw [hζ, ee_pow]
    have : ((z : ℚ)) * (((A : ℤ) : ℚ) / ((z : ℤ) : ℚ)) = ((A : ℤ) : ℚ) := by
      push_cast at hzq ⊢
      field_simp
    rw [this]
    exact ee_intCast A
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  by_cases hdvd : (z : ℤ) ∣ A
  · have hζ1 : ζ = 1 := by
      obtain ⟨k, hk⟩ := hdvd
      rw [hζ, hk]
      have : (((z : ℤ) * k : ℤ) : ℚ) / ((z : ℤ) : ℚ) = (k : ℚ) := by
        push_cast at hzq ⊢
        field_simp
      rw [this]
      exact ee_intCast k
    rw [if_pos hdvd, hζ1]
    simp
  · have hζne : ζ ≠ 1 := by
      intro h1
      rw [hζ, ee_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      apply hdvd
      refine ⟨k, ?_⟩
      have h3 : ((A : ℤ) : ℚ) = (k : ℚ) * ((z : ℤ) : ℚ) := by
        rw [div_eq_iff hzq] at hk
        exact hk
      have h4 : (A : ℤ) = k * (z : ℤ) := by exact_mod_cast h3
      rw [h4]; ring
    rw [if_neg hdvd, geom_sum_eq hζne, hζz]
    simp

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
