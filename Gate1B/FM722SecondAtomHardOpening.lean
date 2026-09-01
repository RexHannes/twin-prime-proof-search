import Gate1B.FM722AtomTypeInterface

/-!
# Gate 1B · FM722 · the **hard second-atom opening**

The core kernel theorem of this delta.

Setting: the determinant line `A b − ell q = −2` through `(q₀ , b₀)`, and an
odd second atom `y` coprime to `ell` (the coprimality is *derived* from
oddness by `odd_divisor_isCoprime_ell`, not assumed).

Hard opening: choose the residue `s₀ mod y` with `y ∣ b₀ + ell s₀`, write
`s = s₀ + y r`, and set

```
  q₁ = q₀ + A s₀ ,      c₁ = (b₀ + ell s₀)/y .
```

Then along the fibre

```
  q = q₁ + (A y) r ,      c = c₁ + ell r ,
```

and the **determinant is preserved with the new slope `A y`**:

```
  (A y) c₁ − ell q₁ = −2 .
```

The reparametrisation is an exact *bijective* fibre change: §4 proves the
converse, i.e. `y ∣ b₀ + ell s` holds **iff** `s = s₀ + y r` for some `r`.

## Semantic guard

Opening a second atom preserves the determinant.  It does **not** improve any
analytic quantity, and it does **not** lengthen the line — see the capacity
firewall in `Gate1B.FM722LongLineLengthLedger`.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

/-! ## 1. The opening residue -/

/-- **Existence of the opening residue.**  If `gcd(y, ell) = 1` there is an
`s₀` with `y ∣ b₀ + ell s₀`. -/
theorem exists_opening_residue (ell b0 y : ℤ) (hco : IsCoprime y ell) :
    ∃ s0 : ℤ, y ∣ b0 + ell * s0 := by
  obtain ⟨u, v, huv⟩ := hco
  refine ⟨-(v * b0), ⟨b0 * u, ?_⟩⟩
  have : u * y + v * ell = 1 := huv
  linear_combination (-b0) * this

/-- **Uniqueness of the opening residue modulo `y`.** -/
theorem opening_residue_unique (ell b0 y s s0 : ℤ) (hco : IsCoprime y ell)
    (h0 : y ∣ b0 + ell * s0) (h : y ∣ b0 + ell * s) : y ∣ s - s0 := by
  have hdiff : y ∣ ell * (s - s0) := by
    have := dvd_sub h h0
    simpa [mul_sub] using this
  exact hco.dvd_of_dvd_mul_left hdiff

/-! ## 2. The hard fibre coordinates -/

/-- The modulus coordinate along the hard fibre: `q₀ + A(s₀ + y r) = q₁ + (A y) r`. -/
theorem hard_opening_q (A q0 s0 y r : ℤ) :
    q0 + A * (s0 + y * r) = (q0 + A * s0) + (A * y) * r := by ring

/-- The `c`-coordinate along the hard fibre: if `y c₁ = b₀ + ell s₀` then
`y (c₁ + ell r) = b₀ + ell (s₀ + y r)`. -/
theorem hard_opening_c (ell b0 s0 y c1 r : ℤ) (hc1 : y * c1 = b0 + ell * s0) :
    y * (c1 + ell * r) = b0 + ell * (s0 + y * r) := by
  linear_combination hc1

/-- **BOXED — FM722-LONGLINE-TWOATOM-HARD-DETERMINANT-PRESERVATION45.**
If `A b₀ − ell q₀ = −2` and `y c₁ = b₀ + ell s₀`, then with
`q₁ = q₀ + A s₀` the hard opening preserves the determinant with new slope
`A y`:

```
  (A y) c₁ − ell q₁ = −2 .
```
-/
theorem hard_opening_determinant (A ell q0 b0 y s0 c1 : ℤ)
    (h0 : A * b0 - ell * q0 = -2) (hc1 : y * c1 = b0 + ell * s0) :
    (A * y) * c1 - ell * (q0 + A * s0) = -2 := by
  linear_combination h0 + A * hc1

/-- The whole hard fibre carries determinant `-2`. -/
theorem hard_opening_determinant_at (A ell q0 b0 y s0 c1 r : ℤ)
    (h0 : A * b0 - ell * q0 = -2) (hc1 : y * c1 = b0 + ell * s0) :
    (A * y) * (c1 + ell * r) - ell * ((q0 + A * s0) + (A * y) * r) = -2 := by
  linear_combination h0 + A * hc1

/-! ## 3. The hard opening as a structure -/

/-- **`HardSecondAtomOpening`.**  The result of a hard second-atom opening:
the *new slope is `A · y`* and the line variable spacing has changed.  Finite
data plus a determinant certificate; no analytic field. -/
structure HardSecondAtomOpening where
  /-- The old slope. -/
  A : ℤ
  /-- The `b`-side slope (unchanged by a hard opening). -/
  ell : ℤ
  /-- The opened second atom. -/
  y : ℤ
  /-- The new modulus anchor. -/
  q1 : ℤ
  /-- The new `c`-anchor. -/
  c1 : ℤ
  /-- The opening residue used. -/
  s0 : ℤ
  /-- Oddness certificate. -/
  yOdd : Odd y
  /-- Nondegeneracy certificate. -/
  yNe : y ≠ 0
  /-- **Determinant certificate with the new slope `A y`.** -/
  det : (A * y) * c1 - ell * q1 = -2

namespace HardSecondAtomOpening

variable (H : HardSecondAtomOpening)

/-- **The hard opening changes the slope to `A · y`.** -/
def newSlope : ℤ := H.A * H.y

/-- The modulus point of the opened line at fibre parameter `r`. -/
def qAt (r : ℤ) : ℤ := H.q1 + H.newSlope * r

/-- The `c`-point of the opened line at fibre parameter `r`. -/
def cAt (r : ℤ) : ℤ := H.c1 + H.ell * r

@[simp] theorem newSlope_def : H.newSlope = H.A * H.y := rfl

/-- Determinant `-2` all along the opened fibre. -/
theorem det_at (r : ℤ) : H.newSlope * H.cAt r - H.ell * H.qAt r = -2 := by
  have := H.det
  simp only [qAt, cAt, newSlope]
  linear_combination this

end HardSecondAtomOpening

/-! ## 4. The hard opening is a bijective fibre change -/

/-- **FM722-LONGLINE-TWOATOM-HARD-BIJECTION.**  With `gcd(y, ell) = 1` and one
opening residue `s₀`, the divisibility fibre is *exactly* the arithmetic
progression `s₀ + y ℤ`; the hard reparametrisation is therefore an exact
bijective change of fibre variable, not merely an implication. -/
theorem hard_opening_fibre_iff (ell b0 y s0 : ℤ) (hco : IsCoprime y ell)
    (h0 : y ∣ b0 + ell * s0) (s : ℤ) :
    y ∣ b0 + ell * s ↔ ∃ r : ℤ, s = s0 + y * r := by
  constructor
  · intro h
    obtain ⟨r, hr⟩ := opening_residue_unique ell b0 y s s0 hco h0 h
    exact ⟨r, by linarith⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨c1, hc1⟩ := h0
    exact ⟨c1 + ell * r, by linear_combination hc1⟩

/-- Every fibre parameter `r` produces a genuine point of the original
determinant line with `y ∣ b`. -/
theorem hard_opening_converse (A ell q0 b0 y s0 c1 r : ℤ)
    (h0 : A * b0 - ell * q0 = -2) (hc1 : y * c1 = b0 + ell * s0) :
    y ∣ b0 + ell * (s0 + y * r) ∧
      A * (b0 + ell * (s0 + y * r)) - ell * (q0 + A * (s0 + y * r)) = -2 := by
  refine ⟨⟨c1 + ell * r, ?_⟩, det2_line_forward A ell q0 b0 h0 (s0 + y * r)⟩
  linear_combination -hc1

/-! ## 5. The deterministic hard compiler -/

/-- **FM722 hard second-atom data compiler (conditional, deterministic).**
Given two-atom incidence data, an opening residue `s₀` and an explicit
quotient `c₁` with `y c₁ = b₀ + ell s₀`, this constructs the hard opening and
its determinant certificate.  Nothing analytic is produced. -/
def compileHard (I : TwoAtomIncidenceData) (s0 c1 : ℤ)
    (hc1 : I.y * c1 = I.bAt s0) : HardSecondAtomOpening where
  A := I.A
  ell := I.ell
  y := I.y
  q1 := I.q0 + I.A * s0
  c1 := c1
  s0 := s0
  yOdd := I.yOdd
  yNe := I.yNe
  det := hard_opening_determinant I.A I.ell I.q0 I.b0 I.y s0 c1 I.det hc1

@[simp] theorem compileHard_newSlope (I : TwoAtomIncidenceData) (s0 c1 : ℤ)
    (hc1 : I.y * c1 = I.bAt s0) :
    (compileHard I s0 c1 hc1).newSlope = I.A * I.y := rfl

/-- The compiled hard opening reproduces the original modulus points. -/
theorem compileHard_qAt (I : TwoAtomIncidenceData) (s0 c1 : ℤ)
    (hc1 : I.y * c1 = I.bAt s0) (r : ℤ) :
    (compileHard I s0 c1 hc1).qAt r = I.qAt (s0 + I.y * r) := by
  simp only [compileHard, HardSecondAtomOpening.qAt, HardSecondAtomOpening.newSlope,
    TwoAtomIncidenceData.qAt]
  ring

/-- The compiled hard opening reproduces the original `b`-points, divided by
the opened atom. -/
theorem compileHard_cAt (I : TwoAtomIncidenceData) (s0 c1 : ℤ)
    (hc1 : I.y * c1 = I.bAt s0) (r : ℤ) :
    I.y * (compileHard I s0 c1 hc1).cAt r = I.bAt (s0 + I.y * r) := by
  simp only [compileHard, HardSecondAtomOpening.cAt, TwoAtomIncidenceData.bAt]
  simp only [TwoAtomIncidenceData.bAt] at hc1
  linear_combination hc1

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
