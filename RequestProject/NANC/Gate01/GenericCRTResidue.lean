import RequestProject.NANC.Gate01.CanonicalCongruence

/-!
# Gate 0–1 finite bank: the generic CRT residue for `p ≠ q`

Generic common-weight coprime stratum.  Integers `r ≠ 0`, `k`, `m`,
`m' = m + k r`, a shifted root `w`, and edge values `A`, `B` linked by

`r * A = m * w + 2`,  `r * B = m' * w + 2`.

The finite content banked here is:

* the edge relation `m * B = m' * A - 2 k` (equivalently `m' A - m B = 2k`),
  which is the fixed-shift determinant already in the bank, restated in the
  form used by the CRT step;
* `q ∣ B ↔ m' * (p n') ≡ 2k (mod q)` when `A = p n'` and `gcd(q, m) = 1`;
* the resulting residue `n' ≡ 2 k m̄' p̄ (mod q)`;
* the `m`-side residue `p n' ≡ α ≡ 2 r̄ (mod m)`;
* the CRT amalgamation `p n' ≡ w✦ (mod q m)`, hence `n' ≡ w✦ p̄ (mod q m)`,
  where `w✦ ≡ 2 k m̄' (mod q)` and `w✦ ≡ α (mod m)`.

Everything is finite integer algebra.  Nothing here covers the
inverse-failure or same-prime strata.

Status label: `GENERIC_CRT_RESIDUE_BANKED`.
-/

namespace RouteAFibreFrame
namespace Gate01

/-- **Edge relation.**  From `r A = m w + 2`, `r B = m' w + 2` and `m' = m + k r`
(with `r ≠ 0`) one gets the fixed-shift determinant `m' A - m B = 2 k`. -/
theorem edge_determinant {r k m mPrime w A B : ℤ} (hr : r ≠ 0)
    (hm' : mPrime = m + k * r) (hA : r * A = m * w + 2) (hB : r * B = mPrime * w + 2) :
    mPrime * A - m * B = 2 * k := by
  have h : r * (mPrime * A - m * B) = r * (2 * k) := by
    have : mPrime * (r * A) - m * (r * B) = r * (2 * k) := by
      rw [hA, hB, hm']; ring
    linarith [this, (by ring : r * (mPrime * A - m * B) = mPrime * (r * A) - m * (r * B))]
  exact mul_left_cancel₀ hr h

/-- The `B`-edge expressed through the `A`-edge: `m * B = m' * A - 2k`. -/
theorem m_mul_B_eq {r k m mPrime w A B : ℤ} (hr : r ≠ 0)
    (hm' : mPrime = m + k * r) (hA : r * A = m * w + 2) (hB : r * B = mPrime * w + 2) :
    m * B = mPrime * A - 2 * k := by
  have := edge_determinant hr hm' hA hB
  linarith

/-- **Joint-hit criterion.**  With `A = p n'` and `q` coprime to `m`,
`q ∣ B` if and only if `m' p n' ≡ 2k (mod q)`. -/
theorem q_dvd_B_iff {q m mPrime A B k p nPrime : ℤ}
    (hcop : IsCoprime q m) (hfac : A = p * nPrime)
    (hedge : m * B = mPrime * A - 2 * k) :
    q ∣ B ↔ mPrime * (p * nPrime) ≡ 2 * k [ZMOD q] := by
  constructor
  · intro h
    have h1 : q ∣ mPrime * (p * nPrime) - 2 * k := by
      rw [← hfac, ← hedge]; exact h.mul_left m
    exact Int.modEq_iff_dvd.mpr (by simpa using h1.neg_right)
  · intro h
    have h1 : q ∣ mPrime * (p * nPrime) - 2 * k := by
      simpa using (Int.modEq_iff_dvd.mp h).neg_right
    have h2 : q ∣ m * B := by rw [hedge, hfac]; exact h1
    exact (hcop.dvd_of_dvd_mul_left h2)

/-- **`q`-side residue.**  Under the joint-hit criterion, with inverses `s` of
`m'` and `u` of `p` modulo `q`, the cofactor satisfies `n' ≡ 2 k s u (mod q)`. -/
theorem nPrime_residue_mod_q {q mPrime p nPrime k s u : ℤ}
    (hs : mPrime * s ≡ 1 [ZMOD q]) (hu : p * u ≡ 1 [ZMOD q])
    (hhit : mPrime * (p * nPrime) ≡ 2 * k [ZMOD q]) :
    nPrime ≡ 2 * k * s * u [ZMOD q] := by
  have h1 : (s * u) * (mPrime * (p * nPrime)) ≡ (s * u) * (2 * k) [ZMOD q] :=
    hhit.mul_left (s * u)
  have h2 : (mPrime * s) * ((p * u) * nPrime) ≡ 1 * (1 * nPrime) [ZMOD q] :=
    hs.mul (hu.mul_right nPrime)
  have h3 : (s * u) * (mPrime * (p * nPrime)) = (mPrime * s) * ((p * u) * nPrime) := by ring
  calc nPrime = 1 * (1 * nPrime) := by ring
    _ ≡ (mPrime * s) * ((p * u) * nPrime) [ZMOD q] := h2.symm
    _ = (s * u) * (mPrime * (p * nPrime)) := h3.symm
    _ ≡ (s * u) * (2 * k) [ZMOD q] := h1
    _ = 2 * k * s * u := by ring

/-- **`m`-side residue.**  `A = α + m t` gives `p n' = A ≡ α (mod m)`. -/
theorem p_nPrime_mod_m {m t alpha p nPrime A : ℤ} (hA : A = alpha + m * t)
    (hfac : A = p * nPrime) : p * nPrime ≡ alpha [ZMOD m] := by
  refine Int.modEq_iff_dvd.mpr ?_
  exact ⟨-t, by rw [← hfac, hA]; ring⟩

/-- **CRT amalgamation.**  If `w✦ ≡ 2 k s (mod q)` and `w✦ ≡ α (mod m)`, and the
`q`-side and `m`-side residues hold, then `p n' ≡ w✦ (mod q m)`. -/
theorem p_nPrime_mod_qm {q m p nPrime k s u alpha wStar : ℤ}
    (hcop : Nat.Coprime q.natAbs m.natAbs)
    (hwq : wStar ≡ 2 * k * s [ZMOD q]) (hwm : wStar ≡ alpha [ZMOD m])
    (hq : nPrime ≡ 2 * k * s * u [ZMOD q]) (hu : p * u ≡ 1 [ZMOD q])
    (hm : p * nPrime ≡ alpha [ZMOD m]) :
    p * nPrime ≡ wStar [ZMOD q * m] := by
  have hq' : p * nPrime ≡ wStar [ZMOD q] := by
    have h1 : p * nPrime ≡ p * (2 * k * s * u) [ZMOD q] := hq.mul_left p
    have h2 : (p * u) * (2 * k * s) ≡ 1 * (2 * k * s) [ZMOD q] := hu.mul_right _
    calc p * nPrime ≡ p * (2 * k * s * u) [ZMOD q] := h1
      _ = (p * u) * (2 * k * s) := by ring
      _ ≡ 1 * (2 * k * s) [ZMOD q] := h2
      _ = 2 * k * s := by ring
      _ ≡ wStar [ZMOD q] := hwq.symm
  have hm' : p * nPrime ≡ wStar [ZMOD m] := hm.trans hwm.symm
  exact (Int.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨hq', hm'⟩

/-- **Generic CRT residue.**  With an inverse `v` of `p` modulo `q m`, the
cofactor is pinned: `n' ≡ w✦ p̄ (mod q m)`. -/
theorem nPrime_residue_mod_qm {q m p nPrime wStar v : ℤ}
    (hv : p * v ≡ 1 [ZMOD q * m]) (h : p * nPrime ≡ wStar [ZMOD q * m]) :
    nPrime ≡ wStar * v [ZMOD q * m] := by
  have h1 : v * (p * nPrime) ≡ v * wStar [ZMOD q * m] := h.mul_left v
  have h2 : (p * v) * nPrime ≡ 1 * nPrime [ZMOD q * m] := hv.mul_right nPrime
  calc nPrime = 1 * nPrime := by ring
    _ ≡ (p * v) * nPrime [ZMOD q * m] := h2.symm
    _ = v * (p * nPrime) := by ring
    _ ≡ v * wStar [ZMOD q * m] := h1
    _ = wStar * v := by ring

end Gate01
end RouteAFibreFrame
