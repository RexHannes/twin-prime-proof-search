import Gate1B.HNESawtoothSmallR

/-!
# Gate 1B · the AP-index congruence `d·h ≡ r·s (mod g_r)`

This is the principal **unconditional arithmetic theorem** of the current HNE
frontier.  Everything here is exact; no analytic input is used and none is
created.

## Contents

* §1 the exact `C_r` factorisation in `ZMod g` and the AP-index equivalence
  `C_r ≡ 0  ⟺  d·h ≡ r·s (mod g)` on the clean unit sector;
* §2 the integer/divisibility form `hne_apIndex_congruence`;
* §3 `HNEAPIndexPacket`, with the physical inequalities carried as `Prop`
  fields and never auto-proved;
* §4 the abstract AP-index operator interface, keeping the source coefficient
  `C4j` explicit;
* §5 `HNEAPIndexSourceEnergy` as an explicit proposition, **not** proved, with
  a countermodel showing that no coefficient-blind `K/g` bound follows from
  cardinality;
* §6 the `k = 0` projective-equality branch: `d·h = r·s` forces a common
  primitive ratio.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HNEAPIndex

open Finset

/-! ## 1. The AP-index equivalence in `ZMod g` -/

variable {g : ℕ}

/-- **Exact `C_r` factorisation.**  With `s·sinv = 1`,

`C_r = 2·dinv·(d·h·sinv − r) = 2·dinv·sinv·(d·h − r·s)`. -/
theorem Cr_factorisation (d h s sinv dinv r C : ZMod g) (hs : s * sinv = 1)
    (hC : C = 2 * dinv * (d * h * sinv - r)) :
    C = 2 * dinv * sinv * (d * h - r * s) := by
  subst hC
  linear_combination (2 * dinv * r) * hs

/-- The reciprocal factorisation: on the clean unit sector, `d·h − r·s` is an
explicit unit multiple of `C_r`. -/
theorem apIndex_key_identity (d h s sinv dinv twoinv r C : ZMod g)
    (h2 : (2 : ZMod g) * twoinv = 1) (hd : d * dinv = 1) (hs : s * sinv = 1)
    (hC : C = 2 * dinv * (d * h * sinv - r)) :
    twoinv * d * s * C = d * h - r * s := by
  subst hC
  linear_combination (d * dinv * s * (d * h * sinv - r)) * h2 +
    (s * (d * h * sinv - r)) * hd + (d * h) * hs

/-- **AP-index congruence in `ZMod g`.**  On the clean unit/odd sector
(`2`, `d` and `s` invertible),

`C_r = 0  ⟺  d·h = r·s`. -/
theorem apIndex_congruence_zmod (d h s sinv dinv twoinv r C : ZMod g)
    (h2 : (2 : ZMod g) * twoinv = 1) (hd : d * dinv = 1) (hs : s * sinv = 1)
    (hC : C = 2 * dinv * (d * h * sinv - r)) :
    C = 0 ↔ d * h = r * s := by
  constructor
  · intro hC0
    have hkey := apIndex_key_identity d h s sinv dinv twoinv r C h2 hd hs hC
    rw [hC0, mul_zero] at hkey
    linear_combination -hkey
  · intro hEq
    rw [Cr_factorisation d h s sinv dinv r C hs hC]
    have : d * h - r * s = 0 := by rw [hEq]; ring
    rw [this, mul_zero]

/-! ## 2. The integer form -/

/-- **BOXED (§34 of the specification): `hne_apIndex_congruence`.**  With `C_r`
the small-`r` reciprocal numerator, and `2`, `d`, `s` invertible modulo `g`,

```
g ∣ C_r   ⟺   d·h ≡ r·s (mod g).
```

Exact and unconditional. -/
theorem hne_apIndex_congruence {d h s sinv dinv twoinv r C : ℤ}
    (h2 : (g : ℤ) ∣ 2 * twoinv - 1) (hd : (g : ℤ) ∣ d * dinv - 1)
    (hs : (g : ℤ) ∣ s * sinv - 1)
    (hC : C = 2 * dinv * (d * h * sinv - r)) :
    (g : ℤ) ∣ C ↔ (g : ℤ) ∣ d * h - r * s := by
  have H2 : (2 : ZMod g) * (twoinv : ℤ) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (2 * twoinv - 1) g).mpr h2
    push_cast at this
    linear_combination this
  have HD : ((d : ℤ) : ZMod g) * (dinv : ℤ) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (d * dinv - 1) g).mpr hd
    push_cast at this
    linear_combination this
  have HS : ((s : ℤ) : ZMod g) * (sinv : ℤ) = 1 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (s * sinv - 1) g).mpr hs
    push_cast at this
    linear_combination this
  have HC : ((C : ℤ) : ZMod g)
      = 2 * ((dinv : ℤ) : ZMod g) *
          (((d : ℤ) : ZMod g) * ((h : ℤ) : ZMod g) * ((sinv : ℤ) : ZMod g)
            - ((r : ℤ) : ZMod g)) := by
    rw [hC]; push_cast; ring
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd C g,
    ← ZMod.intCast_zmod_eq_zero_iff_dvd (d * h - r * s) g]
  have := apIndex_congruence_zmod (g := g) ((d : ℤ) : ZMod g) ((h : ℤ) : ZMod g)
    ((s : ℤ) : ZMod g) ((sinv : ℤ) : ZMod g) ((dinv : ℤ) : ZMod g)
    ((twoinv : ℤ) : ZMod g) ((r : ℤ) : ZMod g) ((C : ℤ) : ZMod g) H2 HD HS HC
  rw [this]
  constructor
  · intro hEq; push_cast; linear_combination hEq
  · intro hEq; push_cast at hEq; linear_combination hEq

/-! ## 3. The current HNE AP-index packet -/

/-- The current HNE AP-index packet.  The physical inequalities are `Prop`
fields: none of them is auto-proved. -/
structure HNEAPIndexPacket where
  /-- The modulus `ℓ`. -/
  l : ℕ
  /-- The divisor `d`. -/
  d : ℤ
  /-- The residue `ρ`. -/
  rho : ℤ
  /-- The sawtooth integer `r`. -/
  rSaw : ℤ
  /-- The AP index `h`. -/
  h : ℤ
  /-- The parameter `s`. -/
  s : ℤ
  /-- The parameter `u`. -/
  u : ℤ
  /-- The small-`r` reciprocal numerator. -/
  Cr : ℤ
  /-- `g_r = gcd(C_r, ℓ)`. -/
  gr : ℕ
  /-- `q_r = ℓ / g_r`. -/
  qr : ℕ
  /-- The unit assumptions on the clean sector. -/
  unitAssumptions : Prop
  /-- `|r| ≤ d L^B`: the small-`r` condition. -/
  smallRCondition : Prop
  /-- `q_r < Y^{3/2} L^C`: the low-effective-conductor condition. -/
  lowEffectiveConductorCondition : Prop
  /-- The large-`g` condition. -/
  largeGCondition : Prop

/-! ## 4. The AP-index operator interface -/

/-- The current residual operator, represented abstractly:

```
∑ σ̂(...) · C4j(...) · e_{q_r}((C_r/g_r)·u⁻¹)
```

restricted to the AP-index congruence `d·h ≡ r·s (mod g_r)`.  The source
coefficient `C4j` is an explicit parameter; it is never modelled as
arbitrary. -/
noncomputable def apIndexOperator {ι : Type*} [DecidableEq ι] (H : Finset ι)
    (cls : ι → ZMod g) (target : ZMod g)
    (sigmaHat C4j : ι → ℂ) (phase : ι → ℂ) : ℂ :=
  ∑ i ∈ H with cls i = target, sigmaHat i * C4j i * phase i

/-! ## 5. The AP source-energy proposition: interface only -/

/-- **Explicit proposition, deliberately unproved.**  The AP-index
source-energy hypothesis: one residue class carries at most a `K/g` share of
the total coefficient energy. -/
def HNEAPIndexSourceEnergy {ι : Type*} [DecidableEq ι] (g : ℕ) (H : Finset ι)
    (cls : ι → ZMod g) (C4j : ι → ℂ) (K : ℝ) : Prop :=
  ∀ x : ZMod g, ∑ i ∈ H with cls i = x, ‖C4j i‖ ^ 2
    ≤ (K / g) * ∑ i ∈ H, ‖C4j i‖ ^ 2

/-- **Countermodel.**  No coefficient-blind `K/g` energy bound follows from
cardinality: arbitrary coefficients can saturate a single residue class.  Here
`g = 2`, `K = 1`, and all the mass sits in one class. -/
theorem apIndexSourceEnergy_not_from_cardinality :
    ¬ HNEAPIndexSourceEnergy (ι := Fin 1) 2 Finset.univ (fun _ => 0)
        (fun _ => 1) 1 := by
  intro hcon
  have h := hcon 0
  norm_num at h

/-! ## 6. The `k = 0` projective-equality branch -/

/-- **Primitive ratio reduction.**  If `d·h = r·s` with `d, r > 0`, then after
dividing by `g = gcd(d,r)` the two product pairs share a primitive ratio:
`h = (r/g)·t` and `s = (d/g)·t` for a common `t`. -/
theorem k0_projective_primitive_ratio {d h r s : ℕ} (hd : 0 < d) (hr : 0 < r)
    (heq : d * h = r * s) :
    ∃ t : ℕ, h = (r / Nat.gcd d r) * t ∧ s = (d / Nat.gcd d r) * t := by
  set g := Nat.gcd d r with hgdef
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left r hd
  have hdg : g ∣ d := Nat.gcd_dvd_left d r
  have hrg : g ∣ r := Nat.gcd_dvd_right d r
  set d' := d / g with hd'
  set r' := r / g with hr'
  have hdd : d = g * d' := (Nat.mul_div_cancel' hdg).symm
  have hrr : r = g * r' := (Nat.mul_div_cancel' hrg).symm
  have hcop : Nat.Coprime d' r' := Nat.coprime_div_gcd_div_gcd hgpos
  have hmul : d' * h = r' * s := by
    have : g * (d' * h) = g * (r' * s) := by
      calc g * (d' * h) = (g * d') * h := by ring
        _ = d * h := by rw [← hdd]
        _ = r * s := heq
        _ = (g * r') * s := by rw [← hrr]
        _ = g * (r' * s) := by ring
    exact Nat.eq_of_mul_eq_mul_left hgpos this
  have hr'pos : 0 < r' := by
    rcases Nat.eq_zero_or_pos r' with h0 | h0
    · rw [h0, mul_zero] at hrr; omega
    · exact h0
  have hdvd : r' ∣ h := by
    have : r' ∣ h * d' := ⟨s, by rw [mul_comm h d', hmul]⟩
    exact (Nat.Coprime.dvd_of_dvd_mul_right hcop.symm this)
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t, ht, ?_⟩
  have : r' * (d' * t) = r' * s := by
    calc r' * (d' * t) = d' * (r' * t) := by ring
      _ = d' * h := by rw [ht]
      _ = r' * s := hmul
  exact (Nat.eq_of_mul_eq_mul_left hr'pos this).symm

end HNEAPIndex
end CurrentProgramme
end TwinPrimeProject
