/-
# NANC Gate 1A v9.2/v9.4 — the corrected fixed-quotient CRT

The source-exact fixed-quotient variable is

    d = m + k*r,

and the **corrected** clean fixed-quotient congruences are

    m*s ≡ 2      (mod p*r)
    d*s + c ≡ 0  (mod q),

with `c = ±2` fixed by the global Fourier-sign convention (`c = 2` for the
authoritative one-sided phase `e_q(-2h·inverse(p*r*d))`).

**PERMANENT FIREWALL.**  The older transcription

    r*d*s + c ≡ 0 (mod q)

is *not* the same physical congruence: `oldNew_congruence_not_interchangeable`
exhibits an explicit `(q, r, d, c, s)` satisfying the corrected congruence and
failing the old one.  After Fourier transformation the two `q`-frequency
coordinates differ by multiplication by the unit `r`
(`oldNewQCoordinate_unitEquiv`), which is an `ℓ²`-isometry of the frequency
line (`oldNewQCoordinate_l2Preserved`) — but a unit change *at a later Fourier
coordinate* does not make the old physical source congruence source-exact.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V92

open Finset

/-! ## 1. The corrected fixed-quotient data -/

/-- **Corrected fixed-quotient data.**  All congruences are stated with the
source-exact variable `d = m + k*r`, and with the corrected `q`-congruence
`d*s + c ≡ 0` (no spurious factor `r`). -/
structure CorrectedFixedQuotientData where
  /-- The clean prime factor. -/
  p : ℤ
  /-- The `q`-modulus. -/
  q : ℤ
  /-- The moving family index. -/
  r : ℤ
  /-- The `m`-variable. -/
  m : ℤ
  /-- The shift parameter. -/
  k : ℤ
  /-- The source-exact variable. -/
  d : ℤ
  /-- The quotient root. -/
  s : ℤ
  /-- The sign convention constant (`c = ±2`). -/
  c : ℤ
  /-- `d` is the source-exact combination. -/
  d_eq : d = m + k * r
  /-- `m` is a unit mod `p*r`. -/
  m_unit : IsCoprime m (p * r)
  /-- `d` is a unit mod `q`. -/
  d_unit : IsCoprime d q
  /-- The two moduli are coprime. -/
  moduli_coprime : IsCoprime (p * r) q
  /-- The `p*r`-congruence. -/
  mod_pr : (p * r) ∣ (m * s - 2)
  /-- The corrected `q`-congruence. -/
  mod_q : q ∣ (d * s + c)

/-- **Uniqueness of the corrected fixed-quotient root.**  Under the pairwise
coprimality/unit hypotheses, the root `s` is unique modulo `p*q*r`. -/
theorem correctedFixedQuotient_unique {p q r m d c s s' : ℤ}
    (hm : IsCoprime m (p * r)) (hd : IsCoprime d q) (hcop : IsCoprime (p * r) q)
    (h1 : (p * r) ∣ (m * s - 2)) (h2 : q ∣ (d * s + c))
    (h1' : (p * r) ∣ (m * s' - 2)) (h2' : q ∣ (d * s' + c)) :
    (p * q * r) ∣ (s - s') := by
  have hpr : (p * r) ∣ m * (s - s') := by
    have : m * (s - s') = (m * s - 2) - (m * s' - 2) := by ring
    rw [this]
    exact dvd_sub h1 h1'
  have hprs : (p * r) ∣ (s - s') := (hm.symm).dvd_of_dvd_mul_left hpr
  have hq : q ∣ d * (s - s') := by
    have : d * (s - s') = (d * s + c) - (d * s' + c) := by ring
    rw [this]
    exact dvd_sub h2 h2'
  have hqs : q ∣ (s - s') := (hd.symm).dvd_of_dvd_mul_left hq
  have := hcop.mul_dvd hprs hqs
  have hrw : p * r * q = p * q * r := by ring
  rwa [hrw] at this

/-- Uniqueness, stated for the packaged data. -/
theorem CorrectedFixedQuotientData.root_unique (D : CorrectedFixedQuotientData) {s' : ℤ}
    (h1' : (D.p * D.r) ∣ (D.m * s' - 2)) (h2' : D.q ∣ (D.d * s' + D.c)) :
    (D.p * D.q * D.r) ∣ (D.s - s') :=
  correctedFixedQuotient_unique D.m_unit D.d_unit D.moduli_coprime D.mod_pr D.mod_q h1' h2'

/-! ## 2. The old `r*d*s` convention firewall -/

/-- **FIREWALL (explicit counterexample).**  The corrected congruence
`d*s + c ≡ 0 (mod q)` and the old congruence `r*d*s + c ≡ 0 (mod q)` are not
interchangeable: for `q = 5, r = 2, d = 1, c = 2, s = 3` the corrected
congruence holds and the old one fails. -/
theorem oldNew_congruence_not_interchangeable :
    ((5 : ℤ) ∣ (1 * 3 + 2)) ∧ ¬ ((5 : ℤ) ∣ (2 * 1 * 3 + 2)) := by
  refine ⟨⟨1, by norm_num⟩, ?_⟩
  intro h
  omega

/-- The two solution sets genuinely differ as sets of roots modulo `q`. -/
theorem oldNew_rootSets_differ :
    ∃ (q r d c s : ℤ), q ∣ (d * s + c) ∧ ¬ q ∣ (r * d * s + c) :=
  ⟨5, 2, 1, 2, 3, oldNew_congruence_not_interchangeable.1,
    oldNew_congruence_not_interchangeable.2⟩

/-- **Old/new `q`-frequency coordinates.**  After Fourier transformation the old
and corrected `q`-coordinates differ by multiplication by `r`, which is a
permutation of `ZMod q` whenever `r` is a unit. -/
theorem oldNewQCoordinate_unitEquiv {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) :
    Function.Bijective (fun mu : ZMod q => (r : ZMod q) * mu) := by
  refine ⟨fun x y hxy => ?_, fun y => ⟨((r⁻¹ : (ZMod q)ˣ) : ZMod q) * y, ?_⟩⟩
  · have := congrArg (fun z => ((r⁻¹ : (ZMod q)ˣ) : ZMod q) * z) hxy
    simpa [← mul_assoc] using this
  · simp [← mul_assoc]

/-- **The unit change of `q`-coordinate is an `ℓ²` isometry.**  (It therefore
changes no dual support length, no number of dual variables, no `PB` scalar
prefactor and no `ℓ²` norm.)  This does *not* make the old source congruence
source-exact. -/
theorem oldNewQCoordinate_l2Preserved {q : ℕ} [NeZero q] (r : (ZMod q)ˣ) (co : ZMod q → ℂ) :
    ∑ mu : ZMod q, ‖co ((r : ZMod q) * mu)‖ ^ 2 = ∑ mu : ZMod q, ‖co mu‖ ^ 2 :=
  Fintype.sum_equiv (Equiv.ofBijective _ (oldNewQCoordinate_unitEquiv r)) _ _ fun _ => rfl

/-- The number of `q`-frequencies is likewise unchanged. -/
theorem oldNewQCoordinate_card_preserved {q : ℕ} [NeZero q] (r : (ZMod q)ˣ)
    (S : Finset (ZMod q)) :
    (S.image fun mu => (r : ZMod q) * mu).card = S.card :=
  Finset.card_image_of_injective S (oldNewQCoordinate_unitEquiv r).1

end TwinPrimeProject.NANC.Gate1A.V92
