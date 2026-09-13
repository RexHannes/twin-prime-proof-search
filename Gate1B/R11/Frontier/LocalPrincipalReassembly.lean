/-
# Gate1B / R11 / Frontier : exact reassembly and sign of the local principal correction

Append-only module.  **Exact finite algebra only.**

The modulus-lifting identity (banked in `ResidueModulusLift`) produces, besides the lifted
centered kernel, the extra summand

```
LocalPrincipalCorrection h d n  =  u_d(n)/φ(d) · ( u_h(n)/φ(h) − δ_h(n) ) ,
```

which is proved *not* to vanish in general.  It is therefore tracked here, not dropped:

* `selected_row_lift_split` — the exact split of a lifted selected row: the row of the derived
  (residue-restricted) caller equals the row of the lifted centered caller **plus** the exact
  local principal row.  This is the reassembly identity, with no absolute values taken;
* `localPrincipalCorrection_three_*` — at `h = 3` the correction is computed exactly on each of
  the three residue classes.  Its sign is explicit: it is `−1/2` times the principal profile on
  the selected class `n ≡ 1 (3)`, `+1/2` times the principal profile on `n ≡ 2 (3)`, and `0` on
  multiples of `3`;
* `localPrincipalCorrection_three_pairs_cancel` — hence **mod-3 sign pairing**: the correction
  cancels exactly between the two unit classes whenever the principal profile agrees on the
  paired points.  This is a genuine cancellation of the local principal term, not an estimate;
* `localPrincipalRow_of_paired_window` — the consequence for a whole finite window that is a
  disjoint union of such pairs: the local principal row is exactly `0`.

No analytic statement is proved and no open proposition is inhabited.
-/
import Gate1B.R11.Frontier.Mod3TargetAlgebra

namespace Gate1B.R11.Frontier

open Finset

/-! ## 1. The exact reassembly of a lifted selected row -/

/-- **Exact lifted-row split.**  For `gcd(h,d) = 1`, the row of the residue-restricted caller
splits exactly into the lifted centered row and the local principal row. -/
theorem selected_row_lift_split (a : ℕ → ℚ) (Ns : Finset ℕ) {h d : ℕ}
    (hcop : Nat.Coprime h d) :
    ∑ n ∈ Ns, a n * (deltaSel h n * centeredSel d n)
      = (∑ n ∈ Ns, a n * centeredSel (h * d) n)
        + ∑ n ∈ Ns, a n * LocalPrincipalCorrection h d n := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [modulus_lift_identity hcop n]
  ring

/-- The same split for the modulo-3 derived caller, in terms of the selected indicator `I₃`. -/
theorem selected_row_lift_split_three (a : ℕ → ℚ) (Ns : Finset ℕ) {d : ℕ}
    (hcop : Nat.Coprime 3 d) :
    ∑ n ∈ Ns, a n * (I3 n * centeredSel d n)
      = (∑ n ∈ Ns, a n * centeredSel (3 * d) n)
        + ∑ n ∈ Ns, a n * LocalPrincipalCorrection 3 d n :=
  selected_row_lift_split a Ns hcop

/-! ## 2. The exact value and sign of the correction at `h = 3` -/

theorem uSel_three_of_mod_ne_zero {n : ℕ} (hn : n % 3 ≠ 0) : uSel 3 n = 1 := by
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  have hg : Nat.gcd n 3 = 1 := by
    rw [Nat.gcd_comm, Nat.gcd_rec]
    rcases h with h | h <;> rw [h] <;> rfl
  simp [uSel, hg]

theorem uSel_three_of_dvd {n : ℕ} (hn : n % 3 = 0) : uSel 3 n = 0 := by
  have hg : Nat.gcd n 3 = 3 := by
    rw [Nat.gcd_comm, Nat.gcd_rec, hn]
    rfl
  simp [uSel, hg]

theorem deltaSel_three_eq_one {n : ℕ} (hn : n % 3 = 1) : deltaSel 3 n = 1 := by
  rw [deltaSel, if_pos (by omega : (3 : ℕ) ∣ n + 2)]

theorem deltaSel_three_eq_zero {n : ℕ} (hn : n % 3 ≠ 1) : deltaSel 3 n = 0 := by
  rw [deltaSel, if_neg (by omega : ¬ (3 : ℕ) ∣ n + 2)]

/-- **Exact value on the selected class.**  On `n ≡ 1 (3)` the correction is `−1/2` times the
principal profile: its sign is opposite to the principal term. -/
theorem localPrincipalCorrection_three_selected (d : ℕ) {n : ℕ} (hn : n % 3 = 1) :
    LocalPrincipalCorrection 3 d n = -(uSel d n / (Nat.totient d : ℚ)) / 2 := by
  have h3 : Nat.totient 3 = 2 := by decide
  rw [LocalPrincipalCorrection, uSel_three_of_mod_ne_zero (by omega), deltaSel_three_eq_one hn, h3]
  push_cast
  ring

/-- **Exact value on the complementary unit class.**  On `n ≡ 2 (3)` the correction is `+1/2`
times the principal profile. -/
theorem localPrincipalCorrection_three_unselected (d : ℕ) {n : ℕ} (hn : n % 3 = 2) :
    LocalPrincipalCorrection 3 d n = (uSel d n / (Nat.totient d : ℚ)) / 2 := by
  have h3 : Nat.totient 3 = 2 := by decide
  rw [LocalPrincipalCorrection, uSel_three_of_mod_ne_zero (by omega),
    deltaSel_three_eq_zero (by omega), h3]
  push_cast
  ring

/-- **Exact vanishing on multiples of 3.** -/
theorem localPrincipalCorrection_three_zero (d : ℕ) {n : ℕ} (hn : n % 3 = 0) :
    LocalPrincipalCorrection 3 d n = 0 := by
  rw [LocalPrincipalCorrection, uSel_three_of_dvd hn, deltaSel_three_eq_zero (by omega)]
  simp

/-- The sign on the selected class: the correction is nonpositive there. -/
theorem localPrincipalCorrection_three_selected_nonpos (d : ℕ) {n : ℕ} (hn : n % 3 = 1)
    (hd : 0 < Nat.totient d) : LocalPrincipalCorrection 3 d n ≤ 0 := by
  rw [localPrincipalCorrection_three_selected d hn]
  have hu : 0 ≤ uSel d n := uSel_nonneg d n
  have hphi : (0 : ℚ) < (Nat.totient d : ℚ) := by exact_mod_cast hd
  have : 0 ≤ uSel d n / (Nat.totient d : ℚ) := div_nonneg hu (le_of_lt hphi)
  linarith

/-- The sign on the complementary unit class: the correction is nonnegative there. -/
theorem localPrincipalCorrection_three_unselected_nonneg (d : ℕ) {n : ℕ} (hn : n % 3 = 2)
    (hd : 0 < Nat.totient d) : 0 ≤ LocalPrincipalCorrection 3 d n := by
  rw [localPrincipalCorrection_three_unselected d hn]
  have hu : 0 ≤ uSel d n := uSel_nonneg d n
  have hphi : (0 : ℚ) < (Nat.totient d : ℚ) := by exact_mod_cast hd
  have : 0 ≤ uSel d n / (Nat.totient d : ℚ) := div_nonneg hu (le_of_lt hphi)
  linarith

/-! ## 3. Mod-3 sign pairing: the correction cancels exactly -/

/-- **Mod-3 sign pairing.**  The local principal correction cancels *exactly* between the two
unit classes at any pair of points carrying the same principal profile. -/
theorem localPrincipalCorrection_three_pairs_cancel {d n1 n2 : ℕ} (h1 : n1 % 3 = 1)
    (h2 : n2 % 3 = 2) (hu : uSel d n1 = uSel d n2) :
    LocalPrincipalCorrection 3 d n1 + LocalPrincipalCorrection 3 d n2 = 0 := by
  rw [localPrincipalCorrection_three_selected d h1,
    localPrincipalCorrection_three_unselected d h2, hu]
  ring

/-- **The local principal row of a paired window is exactly `0`.**  If a finite window is
partitioned by an involution `σ` pairing each `n ≡ 1 (3)` with a point `σ n ≡ 2 (3)` carrying the
same principal profile and the same coefficient, the whole local principal row cancels. -/
theorem localPrincipalRow_of_paired_window (a : ℕ → ℚ) (d : ℕ) (S : Finset ℕ) (sigma : ℕ → ℕ)
    (hmaps : ∀ n ∈ S, sigma n ∈ S)
    (hinv : ∀ n ∈ S, sigma (sigma n) = n)
    (hne : ∀ n ∈ S, sigma n ≠ n)
    (hclass : ∀ n ∈ S, (n % 3 = 1 ∧ sigma n % 3 = 2) ∨ (n % 3 = 2 ∧ sigma n % 3 = 1))
    (hu : ∀ n ∈ S, uSel d n = uSel d (sigma n))
    (ha : ∀ n ∈ S, a n = a (sigma n)) :
    ∑ n ∈ S, a n * LocalPrincipalCorrection 3 d n = 0 := by
  refine Finset.sum_involution (fun n _ => sigma n) ?_ (fun n hn _ => hne n hn)
    (fun n hn => hmaps n hn) (fun n hn => hinv n hn)
  intro n hn
  have hune : uSel d n = uSel d (sigma n) := hu n hn
  have hane : a n = a (sigma n) := ha n hn
  rcases hclass n hn with ⟨hn1, hs2⟩ | ⟨hn2, hs1⟩
  · rw [localPrincipalCorrection_three_selected d hn1,
      localPrincipalCorrection_three_unselected d hs2, ← hune, ← hane]
    ring
  · rw [localPrincipalCorrection_three_unselected d hn2,
      localPrincipalCorrection_three_selected d hs1, ← hune, ← hane]
    ring

end Gate1B.R11.Frontier
