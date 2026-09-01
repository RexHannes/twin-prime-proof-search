import Gate1B.FM722SecondAtomHardOpening

/-!
# Gate 1B · FM722 · **iterated determinant-`(-2)` opening**

The algebraic generalisation of the hard second-atom opening to a finite list
of opened atoms.

A *determinant-`(-2)` state* over a fixed `b`-slope `ell` is a triple
`(A, c, q)` with

```
  A · c − ell · q = −2 .
```

Opening an atom `y` coprime to `ell` produces a new state with

```
  A_{r+1} = A_r · y ,
```

again of determinant `-2`.  Iterating over a finite list of atoms multiplies
the slope by the product of the list.

## Semantic guard

This is **pure algebra**.  No analytic usefulness is claimed: multiplying the
slope by `y` is not an improvement, and the length of the resulting line is
*not* addressed here (see `Gate1B.FM722LongLineLengthLedger`).
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

/-- A determinant-`(-2)` state over the fixed `b`-slope `ell`. -/
structure Det2State (ell : ℤ) where
  /-- The current slope. -/
  A : ℤ
  /-- The current `c`-anchor. -/
  c : ℤ
  /-- The current modulus anchor. -/
  q : ℤ
  /-- The determinant certificate. -/
  det : A * c - ell * q = -2

/-- An odd atom dividing the current `c`-anchor is automatically coprime to
`ell`. -/
theorem odd_dividing_atom_coprime {ell : ℤ} (st : Det2State ell) (y : ℤ)
    (hodd : Odd y) (hy : y ∣ st.c) : IsCoprime y ell :=
  odd_divisor_isCoprime_ell st.A ell st.q st.c y hy hodd st.det

/-- **One opening step.**  Opening an atom `y` coprime to `ell` produces a new
determinant-`(-2)` state whose slope is exactly `A · y`. -/
theorem det2_open_one {ell : ℤ} (st : Det2State ell) (y : ℤ) (hco : IsCoprime y ell) :
    ∃ st' : Det2State ell, st'.A = st.A * y := by
  obtain ⟨s0, hs0⟩ := exists_opening_residue ell st.c y hco
  obtain ⟨c1, hc1⟩ := hs0
  refine ⟨⟨st.A * y, c1, st.q + st.A * s0, ?_⟩, rfl⟩
  exact hard_opening_determinant st.A ell st.q st.c y s0 c1 st.det hc1.symm

/-- **FM722-LONGLINE-ITERATED-DETERMINANT2.**  Opening a finite list of atoms,
each coprime to `ell`, produces a determinant-`(-2)` state whose slope is the
original slope times the product of the list. -/
theorem det2_open_list {ell : ℤ} :
    ∀ (ys : List ℤ), (∀ y ∈ ys, IsCoprime y ell) → ∀ st : Det2State ell,
      ∃ st' : Det2State ell, st'.A = st.A * ys.prod := by
  intro ys
  induction ys with
  | nil => intro _ st; exact ⟨st, by simp⟩
  | cons y ys ih =>
      intro hco st
      obtain ⟨st1, h1⟩ := det2_open_one st y (hco y (by simp))
      obtain ⟨st2, h2⟩ := ih (fun z hz => hco z (by simp [hz])) st1
      refine ⟨st2, ?_⟩
      rw [h2, h1, List.prod_cons]
      ring

/-- The odd specialisation: a list of odd atoms, each dividing the `c`-anchor
of the state it is opened at, may be opened one atom at a time. -/
theorem det2_open_odd_step {ell : ℤ} (st : Det2State ell) (y : ℤ)
    (hodd : Odd y) (hy : y ∣ st.c) :
    ∃ st' : Det2State ell, st'.A = st.A * y :=
  det2_open_one st y (odd_dividing_atom_coprime st y hodd hy)

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
