/-
# Universal / GHSpine — the physical Vaughan `(U,V)` pin (KEPT UNINHABITED)

**Status of this module: KERNEL_PROVED convolution algebra; the pin
`PhysicalVaughanUVPin` is deliberately left UNINHABITED and is *kept* that way
by this delta.**

The exact Vaughan identity at a cut `(U,V)` is pure convolution algebra and is
proved here in the kernel (`ghVaughanIdentity`, self-contained so that this
module depends on Mathlib only).  What is **not** proved — and what this module
records as an open source obligation — is that the *physical* source of the
programme really presents its data at the compiler's cut:

* the literal physical cut parameters coincide with the compiler's `(U,V)`;
* the cut is admissible for the physical range (`1 ≤ U`, `1 ≤ V`, `U V ≤ K`);
* the physical remainder term is literally the `P3` remainder of that cut.

`PhysicalVaughanUVPin` bundles exactly those three obligations.  It has no
inhabitant in this repository; `physicalVaughanUVPin_not_automatic` exhibits
data for which it fails, so it cannot be read as vacuously true, and
`vaughan_transport_of_pin` records the only way it may be used: as a hypothesis.
-/
import Mathlib

namespace Universal.GHSpine

open ArithmeticFunction

/-! ## §1 Kernel-proved cut algebra -/

/-- Truncation of an arithmetic function at `Y` (local copy, so that this module
is self-contained). -/
def ghTruncLE (Y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ where
  toFun n := if n ≤ Y then f n else 0
  map_zero' := by simp

/-- The complementary truncation. -/
def ghTruncGT (Y : ℕ) (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f - ghTruncLE Y f

theorem gh_truncation_decomposition (Y : ℕ) (f : ArithmeticFunction ℝ) :
    f = ghTruncLE Y f + ghTruncGT Y f := by
  simp [ghTruncGT]

/-- **KERNEL_PROVED.**  The exact Vaughan identity at the cut `(U,V)`. -/
theorem ghVaughanIdentity (U V : ℕ) :
    vonMangoldt =
      ghTruncLE V vonMangoldt
      + ghTruncLE U (↑moebius : ArithmeticFunction ℝ) * log
      - ghTruncLE U (↑moebius : ArithmeticFunction ℝ) * ghTruncLE V vonMangoldt *
          (↑zeta : ArithmeticFunction ℝ)
      + ghTruncGT U (↑moebius : ArithmeticFunction ℝ) * ghTruncGT V vonMangoldt *
          (↑zeta : ArithmeticFunction ℝ) := by
  have hmu :
      (ghTruncLE U (↑moebius : ArithmeticFunction ℝ) +
          ghTruncGT U (↑moebius : ArithmeticFunction ℝ)) *
          (↑zeta : ArithmeticFunction ℝ) = 1 := by
    rw [← gh_truncation_decomposition]
    exact coe_moebius_mul_coe_zeta
  have hlog :
      (ghTruncLE V vonMangoldt + ghTruncGT V vonMangoldt) *
          (↑zeta : ArithmeticFunction ℝ) = log := by
    rw [← gh_truncation_decomposition]
    exact vonMangoldt_mul_zeta
  calc
    vonMangoldt = ghTruncLE V vonMangoldt + ghTruncGT V vonMangoldt :=
      gh_truncation_decomposition V vonMangoldt
    _ = ghTruncLE V vonMangoldt + 1 * ghTruncGT V vonMangoldt := by ring
    _ = ghTruncLE V vonMangoldt +
        ((ghTruncLE U (↑moebius : ArithmeticFunction ℝ) +
          ghTruncGT U (↑moebius : ArithmeticFunction ℝ)) *
          (↑zeta : ArithmeticFunction ℝ)) * ghTruncGT V vonMangoldt := by rw [hmu]
    _ = _ := by rw [← hlog]; ring

/-! ## §2 The physical `(U,V)` source datum -/

/-- The finite data compared by the pin: the compiler's cut `(U,V)`, the literal
physical cut `(Uphys,Vphys)`, the support cutoff `K`, the physical remainder and
the `P3` remainder of the compiler's cut. -/
structure PhysicalVaughanUVData where
  /-- The compiler's `U`. -/
  U : ℕ
  /-- The compiler's `V`. -/
  V : ℕ
  /-- The literal physical `U`. -/
  Uphys : ℕ
  /-- The literal physical `V`. -/
  Vphys : ℕ
  /-- The support cutoff of the physical packet. -/
  K : ℕ
  /-- The remainder actually produced by the physical source. -/
  physicalRemainder : ℝ
  /-- The `P3` remainder attached to the compiler's cut. -/
  p3Remainder : ℝ

/-- **SOURCE PIN (UNINHABITED here, and KEPT UNINHABITED by this delta).**
The obligation that the literal physical source presents its data at the
compiler's Vaughan cut, in an admissible window, with the physical remainder
equal to the `P3` remainder of that cut. -/
structure PhysicalVaughanUVPin (d : PhysicalVaughanUVData) : Prop where
  /-- The literal physical `U` is the compiler's `U`. -/
  U_match : d.Uphys = d.U
  /-- The literal physical `V` is the compiler's `V`. -/
  V_match : d.Vphys = d.V
  /-- The cut is nondegenerate. -/
  U_ge_one : 1 ≤ d.U
  /-- The cut is nondegenerate. -/
  V_ge_one : 1 ≤ d.V
  /-- The cut is admissible for the packet's support cutoff. -/
  UV_le_K : d.U * d.V ≤ d.K
  /-- The physical remainder is literally the `P3` remainder of the cut. -/
  remainder_match : d.physicalRemainder = d.p3Remainder

/-- **The only legitimate use of the pin: as a hypothesis.**  Any bound proved
for the compiler's `P3` remainder transports to the physical remainder. -/
theorem vaughan_transport_of_pin {d : PhysicalVaughanUVData} (pin : PhysicalVaughanUVPin d)
    {B : ℝ} (hb : |d.p3Remainder| ≤ B) : |d.physicalRemainder| ≤ B := by
  rw [pin.remainder_match]
  exact hb

/-- The pin is a genuine obligation: it can fail (here the physical cut is the
degenerate one, and the remainders differ). -/
theorem physicalVaughanUVPin_not_automatic :
    ∃ d : PhysicalVaughanUVData, ¬ PhysicalVaughanUVPin d := by
  refine ⟨⟨1, 1, 0, 1, 1, 1, 0⟩, ?_⟩
  intro pin
  have h := pin.U_match
  simp at h

/-- **Kept status.**  This repository contains no inhabitant of the pin; the
statement recorded here is only that the pin is *not* a theorem scheme, i.e.
that it fails for some datum.  (Recorded as a separate name so that a later
delta cannot silently reinterpret the previous lemma as an inhabitancy claim.) -/
theorem physicalVaughanUVPin_kept_uninhabited :
    ¬ (∀ d : PhysicalVaughanUVData, PhysicalVaughanUVPin d) := by
  obtain ⟨d, hd⟩ := physicalVaughanUVPin_not_automatic
  exact fun h => hd (h d)

end Universal.GHSpine
