import RequestProject.NANC.Gate1BDet2.Det2AdditiveReciprocalFrame

/-!
# Gate 1B / determinant-2 bank, Module 32: the finite reciprocal Fourier operator

For `m > 0` and an integer `c`, the finite kernel

  `F_{m,c}(x, y) = e_m (c x y)`,   `x, y ∈ ZMod m`,

is studied *exactly*.  Banked here:

* the **Gram relation** `∑_{y} e_m (c (x − x') y) = m · 1_{c(x−x') = 0}`
  (`gram_sum`);
* the **block structure**: with `g = gcd(c, m)` and `m' = m / g`, the Gram
  kernel is supported exactly on `x ≡ x' (mod m')` (`gram_support_int_iff`,
  `nat_dvd_mul_iff_div_gcd_dvd`);
* the **block size**: the kernel `{z : c z = 0}` has exactly `g` elements
  (`card_mul_kernel`), hence every Gram block is a `g × g` all-ones block
  scaled by `m`, and every row of `F F*` sums to `m g` (`gram_row_sum`);
* the **coprime case**: `gcd(c, m) = 1` gives `F F* = m · I`, i.e. the
  normalised kernel `m^{-1/2} F` has orthonormal rows (`gram_coprime`,
  `normalized_kernel_unitary_rows`).

The operator-norm identity `‖F_{m,c}‖ = √(m g)` is *not* proved; it is left as
the ordinary interface Prop `ReciprocalOperatorNormIdentity`, never inhabited.
The exact Gram/row-sum statements above are the finite content that would imply
it.  **No analytic Gate-1B estimate is inferred from this module.**
-/

namespace TwinPrimeProject
namespace Gate1BDet2
namespace Recip

open Finset

/-! ## 1. The kernel and its Gram relation -/

/-- The finite reciprocal Fourier kernel `F_{m,c}(x, y) = e_m (c x y)`. -/
noncomputable def fourierKernel (m : ℕ) [NeZero m] (c : ℤ) (x y : ZMod m) : ℂ :=
  addPhase m ((c : ZMod m) * x * y)

variable {m : ℕ} [NeZero m]

/-- **Gram relation.**  `∑_{y mod m} e_m (c (x − x') y)` equals `m` if
`c (x − x') = 0` in `ZMod m`, and `0` otherwise. -/
theorem gram_sum (c : ℤ) (x x' : ZMod m) :
    ∑ y : ZMod m, addPhase m ((c : ZMod m) * (x - x') * y)
      = if (c : ZMod m) * (x - x') = 0 then (m : ℂ) else 0 := by
  have := sum_addPhase_mul (q := m) ((c : ZMod m) * (x - x'))
  simpa [mul_comm] using this

/-- The Gram relation written directly on the kernel: the `(x, x')` entry of
`F F*` is `m · 1_{c(x−x') = 0}` (the conjugate of a phase is the opposite
phase, here recorded by the parameter change `c ↦ −c`). -/
theorem gram_kernel_entry (c : ℤ) (x x' : ZMod m) :
    ∑ y : ZMod m, fourierKernel m c x y * fourierKernel m (-c) x' y
      = if (c : ZMod m) * (x - x') = 0 then (m : ℂ) else 0 := by
  rw [← gram_sum c x x']
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [fourierKernel, fourierKernel, ← addPhase_add]
  congr 1
  push_cast
  ring

/-! ## 2. Block structure: support of the Gram kernel -/

/-- **Block support, integer form.**  For `n ≠ 0` and integers `c, t`,
`n ∣ c t` if and only if `(n / gcd(c, n)) ∣ t`. -/
theorem dvd_mul_iff_div_gcd_dvd {c t n : ℤ} (hn : n ≠ 0) :
    n ∣ c * t ↔ (n / (Int.gcd c n : ℤ)) ∣ t := by
  have hgne : Int.gcd c n ≠ 0 := by simpa [Int.gcd_eq_zero_iff] using fun _ => hn
  have hg0 : (0 : ℤ) < (Int.gcd c n : ℤ) := by
    exact_mod_cast Nat.pos_of_ne_zero hgne
  set g : ℤ := (Int.gcd c n : ℤ) with hg
  obtain ⟨c', hc'⟩ : g ∣ c := Int.gcd_dvd_left c n
  obtain ⟨n', hn'⟩ : g ∣ n := Int.gcd_dvd_right c n
  have hdivc : c / g = c' := by rw [hc']; exact Int.mul_ediv_cancel_left _ (ne_of_gt hg0)
  have hdivn : n / g = n' := by rw [hn']; exact Int.mul_ediv_cancel_left _ (ne_of_gt hg0)
  have hcop : IsCoprime c' n' := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have := Int.gcd_div_gcd_div_gcd (i := c) (j := n) (Nat.pos_of_ne_zero hgne)
    rwa [hdivc, hdivn] at this
  rw [hdivn]
  constructor
  · intro h
    rw [hc', hn'] at h
    have h2 : n' ∣ c' * t :=
      (mul_dvd_mul_iff_left (a := g) (ne_of_gt hg0)).1 (by simpa [mul_assoc] using h)
    exact hcop.symm.dvd_of_dvd_mul_left h2
  · rintro ⟨s, hs⟩
    exact ⟨c' * s, by rw [hs, hc', hn']; ring⟩

/-- **Block support in `ZMod m`.**  With `g = gcd(c, m)`, the Gram kernel is
supported exactly on the residue classes `x ≡ x' (mod m/g)`. -/
theorem gram_support_int_iff (c t : ℤ) :
    ((c : ZMod m) * (t : ZMod m) = 0) ↔ ((m : ℤ) / (Int.gcd c (m : ℤ) : ℤ)) ∣ t := by
  have hm : ((m : ℤ)) ≠ 0 := Int.natCast_ne_zero.2 (NeZero.ne m)
  rw [← dvd_mul_iff_div_gcd_dvd hm]
  constructor
  · intro h
    have h' : ((c * t : ℤ) : ZMod m) = 0 := by push_cast; simpa using h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (c * t) m).1 h'
  · intro h
    have h' : ((c * t : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (c * t) m).2 h
    push_cast at h'
    simpa using h'

omit [NeZero m] in
/-- The same support statement in `ℕ`-quotient form: `m ∣ c i` iff
`(m / gcd(c, m)) ∣ i`. -/
theorem nat_dvd_mul_iff_div_gcd_dvd {c i : ℕ} (hm : 0 < m) :
    m ∣ c * i ↔ (m / Nat.gcd c m) ∣ i := by
  have h := dvd_mul_iff_div_gcd_dvd (c := (c : ℤ)) (t := (i : ℤ)) (n := (m : ℤ))
    (by exact_mod_cast hm.ne')
  have hgcd : Int.gcd (c : ℤ) (m : ℤ) = Nat.gcd c m := by simp
  rw [hgcd] at h
  have hdiv : ((m : ℤ) / (Nat.gcd c m : ℤ)) = ((m / Nat.gcd c m : ℕ) : ℤ) :=
    Int.ofNat_ediv_ofNat
  rw [hdiv] at h
  exact_mod_cast h

/-! ## 3. Block size: the kernel has exactly `gcd(c, m)` elements -/

/-- The multiples of `m'` below `g * m'` are exactly `g` in number. -/
theorem card_multiples_range {g m' : ℕ} (hm' : 0 < m') :
    ((Finset.range (g * m')).filter (fun i => m' ∣ i)).card = g := by
  classical
  have himg : (Finset.range g).image (fun i => m' * i)
      = (Finset.range (g * m')).filter (fun i => m' ∣ i) := by
    ext j
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, ⟨i, rfl⟩⟩
      nlinarith
    · rintro ⟨hj, i, rfl⟩
      refine ⟨i, ?_, rfl⟩
      by_contra hcon
      push_neg at hcon
      nlinarith
  rw [← himg, Finset.card_image_of_injective _
    (fun a b hab => Nat.eq_of_mul_eq_mul_left hm' hab), Finset.card_range]

/-- **Block size.**  For `m > 0` the number of `z ∈ ZMod m` with `c z = 0`
equals `g = gcd(c, m)`. -/
theorem card_mul_kernel (c : ℕ) :
    (Finset.univ.filter (fun z : ZMod m => (c : ZMod m) * z = 0)).card = Nat.gcd c m := by
  classical
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  set g := Nat.gcd c m with hgdef
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right c hm
  set m' := m / g with hm'def
  have hm'0 : 0 < m' := Nat.div_pos (Nat.le_of_dvd hm (Nat.gcd_dvd_right c m)) hg0
  have hmul : g * m' = m := Nat.mul_div_cancel' (Nat.gcd_dvd_right c m)
  have hstep : (Finset.univ.filter (fun z : ZMod m => (c : ZMod m) * z = 0)).card
      = ((Finset.range m).filter (fun i => m' ∣ i)).card := by
    refine Finset.card_nbij' (fun z => ZMod.val z) (fun i => (i : ZMod m)) ?_ ?_ ?_ ?_
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt z, ?_⟩
      have hz' : m ∣ c * z.val := by
        have : ((c * z.val : ℕ) : ZMod m) = 0 := by
          push_cast
          rw [ZMod.natCast_val, ZMod.cast_id]
          exact hz
        exact (ZMod.natCast_eq_zero_iff _ _).1 this
      exact (nat_dvd_mul_iff_div_gcd_dvd hm).1 hz'
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have hd : m ∣ c * i := (nat_dvd_mul_iff_div_gcd_dvd hm).2 hi.2
      have h0 : ((c * i : ℕ) : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 hd
      push_cast at h0
      exact h0
    · intro z _
      simp [ZMod.natCast_val, ZMod.cast_id]
    · intro i hi
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      exact ZMod.val_natCast_of_lt hi.1
  rw [hstep, ← hmul, card_multiples_range hm'0]

/-- **Row sum of `F F*`.**  Every row of the Gram matrix sums to `m g`.  This is
the exact finite statement of which `‖F_{m,c}‖ = √(m g)` is the operator-norm
shadow. -/
theorem gram_row_sum (c : ℕ) (x : ZMod m) :
    ∑ x' : ZMod m, (if (c : ZMod m) * (x - x') = 0 then (m : ℂ) else 0)
      = (m : ℂ) * (Nat.gcd c m : ℂ) := by
  classical
  have hbij : ∑ x' : ZMod m, (if (c : ZMod m) * (x - x') = 0 then (m : ℂ) else 0)
      = ∑ z : ZMod m, (if (c : ZMod m) * z = 0 then (m : ℂ) else 0) :=
    Fintype.sum_equiv (Equiv.subLeft x) _ _ (fun z => by simp [Equiv.subLeft])
  rw [hbij, ← Finset.sum_filter, Finset.sum_const, card_mul_kernel c]
  simp [mul_comm]

/-! ## 4. The coprime case: unitarity of the normalised kernel -/

/-- **Coprime case.**  If `gcd(c, m) = 1` then the Gram matrix is `m · I`. -/
theorem gram_coprime {c : ℤ} (hc : Int.gcd c (m : ℤ) = 1) (x x' : ZMod m) :
    ∑ y : ZMod m, addPhase m ((c : ZMod m) * (x - x') * y)
      = if x = x' then (m : ℂ) else 0 := by
  rw [gram_sum]
  by_cases h : x = x'
  · simp [h]
  · rw [if_neg h, if_neg]
    intro hc0
    set t : ℤ := ((x - x').val : ℤ) with ht0
    have ht : ((t : ℤ) : ZMod m) = x - x' := by
      rw [ht0]; push_cast; simp [ZMod.natCast_val, ZMod.cast_id]
    rw [← ht] at hc0
    have hdvd : ((m : ℤ) / (Int.gcd c (m : ℤ) : ℤ)) ∣ t := (gram_support_int_iff c t).1 hc0
    rw [hc] at hdvd
    simp only [Nat.cast_one, Int.ediv_one] at hdvd
    have hz : ((t : ℤ) : ZMod m) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd t m).2 hdvd
    rw [ht] at hz
    exact h (by linear_combination (norm := abel) hz)

/-- **Normalised unitarity (row form).**  For `gcd(c, m) = 1` the rows of the
normalised kernel `m^{-1/2} F` are orthonormal. -/
theorem normalized_kernel_unitary_rows {c : ℤ} (hc : Int.gcd c (m : ℤ) = 1) (x x' : ZMod m) :
    (m : ℂ)⁻¹ * ∑ y : ZMod m, addPhase m ((c : ZMod m) * (x - x') * y)
      = if x = x' then (1 : ℂ) else 0 := by
  have hm : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne m)
  rw [gram_coprime hc]
  by_cases h : x = x' <;> simp [h, inv_mul_cancel₀ hm]

/-! ## 5. Interface: the operator-norm identity -/

/-- **OPEN INTERFACE.**  The operator-norm identity `‖F_{m,c}‖ = √(m g)`.
It is *not* inhabited here; only the exact Gram and row-sum statements above are
banked. -/
def ReciprocalOperatorNormIdentity (opNorm : ℝ) (m g : ℕ) : Prop :=
  opNorm = Real.sqrt ((m : ℝ) * (g : ℝ))

/-- **GUARD.**  The interface is not automatic: a numerical value can of course
fail it. -/
theorem reciprocalOperatorNormIdentity_not_automatic :
    ¬ ReciprocalOperatorNormIdentity 0 1 1 := by
  unfold ReciprocalOperatorNormIdentity
  norm_num

end Recip
end Gate1BDet2
end TwinPrimeProject
