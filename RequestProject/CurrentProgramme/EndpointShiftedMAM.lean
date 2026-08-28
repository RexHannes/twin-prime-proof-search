import Mathlib
import RequestProject.CurrentProgramme.EndpointShiftedDeterminant

/-!
# Shifted MAM packets and the shifted-MAM sockets

Concrete finite packets for the shifted determinant shell

```
d·p·ℓ - u·v = 2 + u·ℓ·hSh
```

together with the (never inhabited) analytic sockets built on them.

Banked here:

* `ShiftedMAMSourceData` — concrete finite data (`a4`, `μ`, prime weight, `b5`,
  source weight, and the five finite supports).  No free `Prop` field: the shell
  is a *decidable predicate inside the summation*.
* `ShiftedMAMSourceData.C` — the shifted packet `C_h`; `nativePacket = C 0`.
* `shiftedMAM_zero_eq_native` — the zero shift *is* the native packet.
* `NativePure5SourceAdapter` — the uninhabited source adapter identifying `C 0`
  with the literal physical native Pure5/MAM object, which is **absent** from
  this repository.
* `finiteShift_sameArithmeticArchitecture` — for shifts `0, +1, -1` the shell has
  the same modulus data and the same two residues; *values* are not claimed
  equal (`finiteShift_values_may_differ`).
* the sockets `MidKShiftAveragedMAMInput`, `TopKFiniteShiftMAMInput` and the
  umbrella `ShiftedMAMFamilyInput`, with the logical specialisations
  family → native, family → top-`k`, family → mid-`k`.

No analytic estimate is proved and no socket is inhabited.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace ShiftedMAM

open Finset ShiftedDet

/-! ## 1. Concrete shifted packet data -/

/-- Finite source data for the shifted MAM packets.  Every field is concrete
data; the shell is imposed by a decidable predicate in the summation, not by a
`Prop` field. -/
structure ShiftedMAMSourceData where
  /-- `u`-support. -/
  Usupp : Finset ℤ
  /-- `ℓ`-support. -/
  Lsupp : Finset ℤ
  /-- `d`-support. -/
  Dsupp : Finset ℤ
  /-- `p`-support. -/
  Psupp : Finset ℤ
  /-- `v`-support. -/
  Vsupp : Finset ℤ
  /-- The `2|2` coefficient on the `u`-side. -/
  a4 : ℤ → ℂ
  /-- The Möbius weight. -/
  muWeight : ℤ → ℂ
  /-- The prime weight. -/
  primeWeight : ℤ → ℂ
  /-- The `v`-side coefficient. -/
  b5 : ℤ → ℂ
  /-- The source weight at the slots `(u,ℓ,d,p,v,hSh)`. -/
  sourceWeight : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℂ

namespace ShiftedMAMSourceData

variable (S : ShiftedMAMSourceData)

/-- The index box of the packet. -/
def box : Finset (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  S.Usupp ×ˢ S.Lsupp ×ˢ S.Dsupp ×ˢ S.Psupp ×ˢ S.Vsupp

/-- The shell at shift `hSh`: `d p ℓ - u v = 2 + u ℓ hSh`. -/
def shell (hSh : ℤ) : Finset (ℤ × ℤ × ℤ × ℤ × ℤ) :=
  S.box.filter fun x =>
    x.2.2.1 * x.2.2.2.1 * x.2.1 - x.1 * x.2.2.2.2 = 2 + x.1 * x.2.1 * hSh

/-- **The shifted MAM packet `C_h`.** -/
noncomputable def C (hSh : ℤ) : ℂ :=
  ∑ x ∈ S.shell hSh,
    S.a4 x.1 * S.muWeight x.2.2.1 * S.primeWeight x.2.2.2.1 * S.b5 x.2.2.2.2 *
      S.sourceWeight x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2 hSh

/-- The native packet is the zero-shift packet. -/
noncomputable def nativePacket : ℂ := S.C 0

/-- **`shiftedMAM_zero_eq_native`.**  The shift-`0` packet is literally the
native packet.  (The identification with the *physical* native Pure5 object is a
separate, uninhabited adapter.) -/
theorem shiftedMAM_zero_eq_native : S.C 0 = S.nativePacket := rfl

/-- Membership in the shell is exactly the shell equation together with
membership in the box. -/
theorem mem_shell {hSh : ℤ} {x : ℤ × ℤ × ℤ × ℤ × ℤ} :
    x ∈ S.shell hSh ↔ x ∈ S.box ∧
      x.2.2.1 * x.2.2.2.1 * x.2.1 - x.1 * x.2.2.2.2 = 2 + x.1 * x.2.1 * hSh := by
  simp [shell]

end ShiftedMAMSourceData

/-! ## 2. The native source adapter (uninhabited) -/

/-- **`NativePure5SourceAdapter`.**  Identification of the zero-shift packet with
a *given* physical native value.  The literal physical Pure5 / `4M|5D` MAM object
is absent from this repository, so this adapter is never inhabited.

`FINITE-SHIFT-STABILITY45 : SOURCE / DICTIONARY`. -/
structure NativePure5SourceAdapter (S : ShiftedMAMSourceData) (physicalNative : ℂ) where
  /-- The identification.  NOT SUPPLIED. -/
  identified : S.C 0 = physicalNative

/-- **`nativeAdapter_not_automatic`.**  The adapter cannot be manufactured: for a
physical value differing from the packet it is provably empty. -/
theorem nativeAdapter_not_automatic (S : ShiftedMAMSourceData) :
    IsEmpty (NativePure5SourceAdapter S (S.C 0 + 1)) := by
  constructor
  rintro ⟨h⟩
  have : (0 : ℂ) = 1 := by linear_combination h
  norm_num at this

/-! ## 3. Finite-shift architecture stability -/

/-- **`finiteShift_sameArithmeticArchitecture`.**  For the shifts `0, +1, -1`
(indeed for every shift) the shell keeps the same moduli `u, ℓ` and forces the
same two residues `d p ℓ ≡ 2 (mod u)` and `u v ≡ -2 (mod ℓ)`.

Only the *arithmetic architecture* is claimed identical; no equality of `β` or
`b5` values is asserted. -/
theorem finiteShift_sameArithmeticArchitecture (u ell d₀ p₀ d₁ p₁ d₂ p₂ v : ℤ)
    (h₀ : d₀ * p₀ * ell - u * v = 2 + u * ell * 0)
    (h₁ : d₁ * p₁ * ell - u * v = 2 + u * ell * 1)
    (h₂ : d₂ * p₂ * ell - u * v = 2 + u * ell * (-1)) :
    (d₀ * p₀ * ell ≡ 2 [ZMOD u] ∧ d₁ * p₁ * ell ≡ 2 [ZMOD u] ∧
      d₂ * p₂ * ell ≡ 2 [ZMOD u]) ∧ (u * v ≡ -2 [ZMOD ell]) := by
  refine ⟨⟨shiftedMAM_mod_u u ell d₀ p₀ v 0 h₀, shiftedMAM_mod_u u ell d₁ p₁ v 1 h₁,
    shiftedMAM_mod_u u ell d₂ p₂ v (-1) h₂⟩, shiftedMAM_mod_ell u ell d₀ p₀ v 0 h₀⟩

/-- **Firewall.**  Equal architecture does *not* mean equal values: the shifted
packets at `0` and `1` can differ. -/
theorem finiteShift_values_may_differ :
    ∃ S : ShiftedMAMSourceData, S.C 0 ≠ S.C 1 := by
  classical
  refine ⟨⟨{1}, {1}, {1}, {3}, {1}, fun _ => 1, fun _ => 1, fun _ => 1, fun _ => 1,
    fun _ _ _ _ _ _ => 1⟩, ?_⟩
  have hC0 : (ShiftedMAMSourceData.mk {1} {1} {1} {3} {1} (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) (fun _ _ _ _ _ _ => 1)).C 0 = 1 := by
    simp [ShiftedMAMSourceData.C, ShiftedMAMSourceData.shell, ShiftedMAMSourceData.box,
      Finset.filter_singleton]
  have hC1 : (ShiftedMAMSourceData.mk {1} {1} {1} {3} {1} (fun _ => 1) (fun _ => 1)
      (fun _ => 1) (fun _ => 1) (fun _ _ _ _ _ _ => 1)).C 1 = 0 := by
    simp [ShiftedMAMSourceData.C, ShiftedMAMSourceData.shell, ShiftedMAMSourceData.box]
  rw [hC0, hC1]
  norm_num

/-! ## 4. The shifted-MAM sockets (all uninhabited) -/

/-- **`ShiftedMAMFamilyInput`** — the umbrella socket.  A bound for a weighted
family of shifted packets.

`SHIFTED-MAM-FAMILY45 : OPEN_ANALYTIC / UNINHABITED`. -/
structure ShiftedMAMFamilyInput (S : ShiftedMAMSourceData) where
  /-- The finite shift family. -/
  shiftSet : Finset ℤ
  /-- The shift weights. -/
  weight : ℤ → ℂ
  /-- The target. -/
  target : ℝ
  /-- The analytic assertion.  NOT SUPPLIED. -/
  bound : ‖∑ h ∈ shiftSet, weight h * S.C h‖ ≤ target

/-- **`MidKShiftAveragedMAMInput`** — the mid-`k` socket: a weighted average over
a long shift set.

`RANKONE-MIDK-SHIFTAVERAGED-MAM45 : OPEN_ANALYTIC`. -/
structure MidKShiftAveragedMAMInput (S : ShiftedMAMSourceData) where
  /-- The long shift set. -/
  shiftSet : Finset ℤ
  /-- The band-kernel weights. -/
  weight : ℤ → ℂ
  /-- The target. -/
  target : ℝ
  /-- The analytic assertion.  NOT SUPPLIED. -/
  bound : ‖∑ h ∈ shiftSet, weight h * S.C h‖ ≤ target

/-- **`TopKFiniteShiftMAMInput`** — the top-`k` socket: a *uniform* bound over a
finite shift set which explicitly contains the zero shift.

`RANKONE-TOPK-FINITESHIFT-MAM45 : OPEN_ANALYTIC`. -/
structure TopKFiniteShiftMAMInput (S : ShiftedMAMSourceData) where
  /-- The finite shift set. -/
  shiftSet : Finset ℤ
  /-- The `r = 0` child is explicitly present. -/
  zero_mem : (0 : ℤ) ∈ shiftSet
  /-- The target. -/
  target : ℝ
  /-- The uniform analytic assertion.  NOT SUPPLIED. -/
  bound : ∀ h ∈ shiftSet, ‖S.C h‖ ≤ target

/-- The top-`k` socket does control the native packet: that is what the `r = 0`
child is for. -/
theorem topK_controls_native (S : ShiftedMAMSourceData) (I : TopKFiniteShiftMAMInput S) :
    ‖S.nativePacket‖ ≤ I.target :=
  I.bound 0 I.zero_mem

/-! ## 5. Logical specialisations of the umbrella socket -/

/-- Family socket at the singleton `{0}` gives the native bound. -/
theorem family_singleton_gives_native (S : ShiftedMAMSourceData)
    (I : ShiftedMAMFamilyInput S) (hset : I.shiftSet = {0}) (hw : I.weight 0 = 1) :
    ‖S.nativePacket‖ ≤ I.target := by
  have h := I.bound
  rw [hset, Finset.sum_singleton, hw, one_mul] at h
  exact h

/-- Family sockets over the singletons of a finite shift set containing `0`
assemble into the top-`k` socket. -/
def family_gives_topK (S : ShiftedMAMSourceData) (shifts : Finset ℤ)
    (hzero : (0 : ℤ) ∈ shifts) (target : ℝ)
    (I : ∀ h ∈ shifts, ShiftedMAMFamilyInput S)
    (hset : ∀ h (hh : h ∈ shifts), (I h hh).shiftSet = {h})
    (hw : ∀ h (hh : h ∈ shifts), (I h hh).weight h = 1)
    (ht : ∀ h (hh : h ∈ shifts), (I h hh).target = target) :
    TopKFiniteShiftMAMInput S where
  shiftSet := shifts
  zero_mem := hzero
  target := target
  bound := by
    intro h hh
    have hb := (I h hh).bound
    rw [hset h hh, Finset.sum_singleton, hw h hh, one_mul, ht h hh] at hb
    exact hb

/-- A family socket carrying band-kernel weights *is* a mid-`k` socket. -/
def family_gives_midK (S : ShiftedMAMSourceData) (I : ShiftedMAMFamilyInput S) :
    MidKShiftAveragedMAMInput S where
  shiftSet := I.shiftSet
  weight := I.weight
  target := I.target
  bound := I.bound

/-! ## 6. Non-vacuity firewalls -/

/-- Any inhabitant of the umbrella socket forces a nonnegative target. -/
theorem familyInput_target_nonneg (S : ShiftedMAMSourceData)
    (I : ShiftedMAMFamilyInput S) : 0 ≤ I.target :=
  le_trans (norm_nonneg _) I.bound

/-- **`shiftedMAMFamilyInput_not_automatic`.**  For a negative target the socket
is provably empty; no compiler can manufacture it. -/
theorem shiftedMAMFamilyInput_not_automatic (S : ShiftedMAMSourceData) :
    IsEmpty {I : ShiftedMAMFamilyInput S // I.target = -1} := by
  constructor
  rintro ⟨I, hI⟩
  have := familyInput_target_nonneg S I
  rw [hI] at this
  norm_num at this

/-- The top-`k` socket is not automatic either. -/
theorem topKInput_not_automatic (S : ShiftedMAMSourceData) :
    IsEmpty {I : TopKFiniteShiftMAMInput S // I.target = -1} := by
  constructor
  rintro ⟨I, hI⟩
  have h := I.bound 0 I.zero_mem
  rw [hI] at h
  have := norm_nonneg (S.C 0)
  linarith

/-- The mid-`k` socket is not automatic either. -/
theorem midKInput_not_automatic (S : ShiftedMAMSourceData) :
    IsEmpty {I : MidKShiftAveragedMAMInput S // I.target = -1} := by
  constructor
  rintro ⟨I, hI⟩
  have h := I.bound
  rw [hI] at h
  have := norm_nonneg (∑ x ∈ I.shiftSet, I.weight x * S.C x)
  linarith

end ShiftedMAM
end CurrentProgramme
end TwinPrimeProject
