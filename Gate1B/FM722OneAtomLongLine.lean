import Gate1B.FM722LongLineDiophantine

/-!
# Gate 1B · FM722 · the **one-atom determinant-`(-2)` long line**

The one-atom specialisation of `Gate1B.FM722LongLineDiophantine`: the slope of
the line is the *single opened atom product*

```
  A = pi · z ,
```

with `pi` the prime index of the atom and `z` the opened atom modulus.

**Everything here is finite data plus integer algebra.**  The structure
`OneAtomDeterminant2Data` carries *no analytic field*: no size, no range, no
inequality.  Analytic statements appear only as explicit hypotheses of
downstream interfaces, never as fields of this datum.

## Semantic guard

An inhabitant of `OneAtomDeterminant2Data` is a *determinant certificate*.  It
is **not** a statement that the corresponding line is long, and it is **not**
an analytic saving.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

/-! ## 1. Anchor metadata (finite labels only) -/

/-- The anchor side of the physical `+2` shift.  A finite label, carrying no
analytic content. -/
inductive AnchorSide
  | lower
  | upper
  deriving DecidableEq, Repr

/-- The sign convention of the determinant certificate.  Finite label. -/
inductive DetSign
  | minusTwo
  deriving DecidableEq, Repr

/-! ## 2. The one-atom determinant datum -/

/-- **`OneAtomDeterminant2Data`.**  The finite one-atom long-line datum:
the prime index `pi`, the opened atom `z`, the line slope `ell`, an anchor
point `(qz , bz)`, finite anchor/sign metadata, and the determinant
certificate `(pi z) bz − ell qz = −2`.

There is deliberately **no analytic inequality field**. -/
structure OneAtomDeterminant2Data where
  /-- The prime index of the opened atom. -/
  pi : ℤ
  /-- The opened atom modulus. -/
  z : ℤ
  /-- The line slope on the `b`-side. -/
  ell : ℤ
  /-- The anchor value of the modulus variable. -/
  qz : ℤ
  /-- The anchor value of the `b`-variable. -/
  bz : ℤ
  /-- Which side of the physical shift the anchor sits on (finite label). -/
  side : AnchorSide
  /-- The determinant sign convention (finite label). -/
  sign : DetSign
  /-- **The determinant certificate.** -/
  det : (pi * z) * bz - ell * qz = -2

namespace OneAtomDeterminant2Data

variable (D : OneAtomDeterminant2Data)

/-- The one-atom slope `A = pi · z`. -/
def slope : ℤ := D.pi * D.z

/-- The modulus point of the line at parameter `s`. -/
def qAt (s : ℤ) : ℤ := D.qz + D.slope * s

/-- The `b`-point of the line at parameter `s`. -/
def bAt (s : ℤ) : ℤ := D.bz + D.ell * s

@[simp] theorem slope_def : D.slope = D.pi * D.z := rfl

/-- **The one-atom line stays on the determinant.** -/
theorem det_at (s : ℤ) : D.slope * D.bAt s - D.ell * D.qAt s = -2 := by
  simpa [qAt, bAt, slope] using
    det2_line_forward (D.pi * D.z) D.ell D.qz D.bz D.det s

/-- **Exhaustiveness of the one-atom parametrisation** under the two explicit
hypotheses `A ≠ 0` and `gcd(A, ell) = 1`. -/
theorem det_iff (hA : D.slope ≠ 0) (hco : IsCoprime D.slope D.ell) (q b : ℤ) :
    (D.slope * b - D.ell * q = -2) ↔ ∃ s : ℤ, q = D.qAt s ∧ b = D.bAt s := by
  simpa [qAt, bAt, slope] using
    det2_line_iff (D.pi * D.z) D.ell D.qz D.bz q b hA hco D.det

end OneAtomDeterminant2Data

/-! ## 3. Non-vacuity -/

/-- An explicit inhabitant: `pi = 1`, `z = 3`, `ell = 1`, `bz = 1`, `qz = 5`,
so `3 · 1 − 1 · 5 = −2`. -/
def oneAtomExample : OneAtomDeterminant2Data where
  pi := 1
  z := 3
  ell := 1
  qz := 5
  bz := 1
  side := AnchorSide.lower
  sign := DetSign.minusTwo
  det := by decide

/-- The one-atom determinant datum is inhabited: the bank is not vacuous. -/
theorem oneAtomDeterminant2Data_nonempty : Nonempty OneAtomDeterminant2Data :=
  ⟨oneAtomExample⟩

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
