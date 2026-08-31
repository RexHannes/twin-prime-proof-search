import Mathlib
import RequestProject.CurrentProgramme.DetLineAdditiveMinorCrosspairSocket

/-!
# Gate 1B · additive-minor source adapter, coprimality seal and `Λ = μ ∗ log`

**Append-only delta layer.**  Nothing in the historical bank is modified.

This module contains three strictly finite/algebraic blocks.

## 1. `ADDMIN-ONE-SIDED-MU-LOG45`

The exact divisor identity `Λ(n) = ∑_{ab = n} μ(a) log b` (Mathlib's
`ArithmeticFunction.moebius_mul_log_eq_vonMangoldt`, unfolded to the literal
`divisorsAntidiagonal` sum), together with the one-sided source expansion of a
defect source of the shape `δ(s) = (Λ(s) − 1) · W(s/Y) / log s`.

*No* Type-I / Type-II analytic estimate is formalised.

## 2. `ADDMIN-ACTUAL-DEFECT-SOURCE45`

The repository does **not** contain literal definitions named `delta_j`,
`lambda_j`, `rho_j` or `Pi_ell`: the additive-minor layer carries them only as
abstract fields of `AdditiveMinorCrosspairData` (`Pi`, `deltaHat`, `rhoHat`).
Consequently the physical source packet is exposed here as an **uninhabited**
adapter `AddMinActualDefectSourceInput`, whose fields are exactly the two source
equations
```
δ_j(s)          = (Λ(s) − 1) · W_j(s/Y) / log s ,
ρ̂_{j,ℓ}(m)      = (1 − Π_ℓ(m)) · δ̂_{j,ℓ}(m) ,
```
and *not* a synthetic replacement.  The second equation is already available in
the actual additive-minor data (`AdditiveMinorCrosspairData.rhoHat_form`), so the
adapter records only the genuinely missing first one plus its compatibility.

## 3. Source coprimality seal

`N := u · A`, `q_ℓ := ℓ · M`.  The reciprocity layer needs `gcd(N, q_ℓ) = 1`.
This is **not** derivable from a size comparison such as `N < M` — `N = uA` may
be far larger than `M` — and the countermodel
`size_alone_does_not_give_coprimality` records that explicitly.  The genuine
routing conditions (`M` prime and `M ∤ uA`; `gcd(uA, ℓ) = 1`) are collected in
the **uninhabited** source interface `AddMinCleanCoprimalityInput`, from which
the three sealed lemmas are kernel-proved.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace AddMinSource

open Finset ArithmeticFunction

/-! ## 1. `Λ = μ ∗ log` — reused from Mathlib, unfolded to a divisor sum -/

/-- **`ADDMIN-ONE-SIDED-MU-LOG45` (exact divisor identity).**

`Λ(n) = ∑_{a b = n} μ(a) · log b`.  This is Mathlib's
`ArithmeticFunction.moebius_mul_log_eq_vonMangoldt`, written out as a literal
sum over `n.divisorsAntidiagonal`; no new arithmetic-function theory is
introduced. -/
theorem vonMangoldt_eq_moebius_log_divisorSum (n : ℕ) :
    (ArithmeticFunction.vonMangoldt n : ℝ)
      = ∑ x ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * Real.log x.2 := by
  have h := congrArg (fun f => f n)
    (ArithmeticFunction.moebius_mul_log_eq_vonMangoldt)
  simp only [ArithmeticFunction.mul_apply, ArithmeticFunction.log_apply,
    ArithmeticFunction.intCoe_apply] at h
  exact h.symm

/-- The same identity in the `(d, p)` naming of the programme: the inner
variables are the Möbius variable `d` and the "prime" variable `p`. -/
theorem oneSided_muLog_expansion (s : ℕ) :
    (ArithmeticFunction.vonMangoldt s : ℝ)
      = ∑ dp ∈ s.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius dp.1 : ℤ) : ℝ) * Real.log dp.2 :=
  vonMangoldt_eq_moebius_log_divisorSum s

/-- **The one-sided defect-source expansion.**  For a source of the literal shape
`δ(s) = (Λ(s) − 1) · W(s/Y) / log s`, the `Λ` factor expands into the exact
`μ(d) log p` double sum.  Pure rewriting: no estimate. -/
theorem defectSource_muLog_form (W : ℝ → ℂ) (Y : ℝ) (s : ℕ) :
    (((ArithmeticFunction.vonMangoldt s - 1 : ℝ) : ℂ) * W (s / Y)) / (Real.log s : ℂ)
      = ((((∑ dp ∈ s.divisorsAntidiagonal,
            ((ArithmeticFunction.moebius dp.1 : ℤ) : ℝ) * Real.log dp.2) - 1 : ℝ) : ℂ)
          * W (s / Y)) / (Real.log s : ℂ) := by
  rw [← vonMangoldt_eq_moebius_log_divisorSum s]

/-! ## 2. The actual defect-source adapter (UNINHABITED) -/

/-- **`AddMinActualDefectSourceInput` — UNINHABITED source adapter.**

The literal physical packet `δ_j`, `Π_ℓ`, `ρ̂_{j,ℓ}` is *not* present in this
repository as a concrete definition, so it is exposed as an interface whose
fields are exactly the two source equations.  It is never constructed here, and
no synthetic replacement is claimed to be the physical source. -/
structure AddMinActualDefectSourceInput where
  /-- The smooth cut-off `W_j`. -/
  W : ℝ → ℂ
  /-- The source scale `Y`. -/
  Y : ℝ
  /-- The physical defect source `δ_j`. -/
  delta : ℕ → ℂ
  /-- The source support (the "precise source range"). -/
  range : Finset ℕ
  /-- **The first source equation.**  `δ_j(s) = (Λ(s) − 1) W_j(s/Y) / log s`. -/
  delta_eq : ∀ s ∈ range,
    delta s = (((ArithmeticFunction.vonMangoldt s - 1 : ℝ) : ℂ) * W (s / Y))
      / (Real.log s : ℂ)
  /-- The broad-minor multiplier `Π_ℓ`. -/
  Pi : ℤ → ℝ
  /-- The companion transform `δ̂_{j,ℓ}`. -/
  deltaHat : ℤ → ℂ
  /-- The additive-minor transform `ρ̂_{j,ℓ}`. -/
  rhoHat : ℤ → ℂ
  /-- **The second source equation.**  `ρ̂ = (1 − Π) δ̂`. -/
  rhoHat_eq : ∀ m : ℤ, rhoHat m = (1 - (Pi m : ℂ)) * deltaHat m

/-- The adapter is an assumption, not a theorem: it yields exactly the two source
equations it declares, in the `μ log` form. -/
theorem defectSource_adapter_muLog (I : AddMinActualDefectSourceInput)
    {s : ℕ} (hs : s ∈ I.range) :
    I.delta s
      = ((((∑ dp ∈ s.divisorsAntidiagonal,
            ((ArithmeticFunction.moebius dp.1 : ℤ) : ℝ) * Real.log dp.2) - 1 : ℝ) : ℂ)
          * I.W (s / I.Y)) / (Real.log s : ℂ) := by
  rw [I.delta_eq s hs, defectSource_muLog_form]

/-- The adapter's `ρ̂` field is the *actual* multiplier form; nothing else is
assumed about it. -/
theorem defectSource_adapter_rhoHat (I : AddMinActualDefectSourceInput) (m : ℤ) :
    I.rhoHat m = (1 - (I.Pi m : ℂ)) * I.deltaHat m := I.rhoHat_eq m

/-! ## 3. The source coprimality seal -/

/-- **`AddMinCleanCoprimalityInput` — UNINHABITED source interface.**

The exact routing conditions the reciprocity layer needs.  They are *not*
fabricated from a size comparison: the two nontrivial fields are

* `M_not_dvd` : the conductor prime `M` does not occur in the source product
  `u · A` (physical box separation);
* `coprime_uA_ell` : the source product is coprime to the finite lift `ℓ`.

These are the smallest missing source lemmas. -/
structure AddMinCleanCoprimalityInput where
  /-- The source variable `u`. -/
  u : ℕ
  /-- The source variable `A`. -/
  A : ℕ
  /-- The finite lift times conductor, `ℓ = c e`. -/
  ell : ℕ
  /-- The prime modulus `M`. -/
  M : ℕ
  /-- `M` is prime. -/
  M_prime : Nat.Prime M
  /-- `u A` is nonzero. -/
  uA_pos : 0 < u * A
  /-- **Physical box separation:** `M` does not occur in the source product. -/
  M_not_dvd : ¬ (M ∣ u * A)
  /-- **Lift separation:** the source product is coprime to `ℓ`. -/
  coprime_uA_ell : Nat.Coprime (u * A) ell

namespace AddMinCleanCoprimalityInput

variable (S : AddMinCleanCoprimalityInput)

/-- `N = u · A`. -/
def N : ℕ := S.u * S.A

/-- `q_ℓ = ℓ · M`. -/
def qell : ℕ := S.ell * S.M

/-- **`cleanSector_coprime_N_ell`.**  `gcd(N, ℓ) = 1`. -/
theorem cleanSector_coprime_N_ell : Nat.Coprime S.N S.ell := S.coprime_uA_ell

/-- **`cleanSector_coprime_N_M`.**  `gcd(N, M) = 1`, from `M` prime and `M ∤ N`
— **not** from any size comparison. -/
theorem cleanSector_coprime_N_M : Nat.Coprime S.N S.M :=
  (Nat.Prime.coprime_iff_not_dvd S.M_prime).2 S.M_not_dvd |>.symm

/-- **`cleanSector_coprime_N_qell`.**  `gcd(N, q_ℓ) = 1` with `q_ℓ = ℓ M`. -/
theorem cleanSector_coprime_N_qell : Nat.Coprime S.N S.qell :=
  Nat.Coprime.mul_right S.cleanSector_coprime_N_ell S.cleanSector_coprime_N_M

/-- `N` is positive. -/
theorem N_pos : 0 < S.N := S.uA_pos

end AddMinCleanCoprimalityInput

/-! ## 4. Coprimality firewall -/

/-- **Firewall / countermodel.**  Positivity of `N` together with primality of
`M` does *not* give `gcd(N, M) = 1`: take `N = M = 5`.  In particular the
coprimality seal may not be justified by "`N` is small" reasoning; the source
routing condition `M ∤ uA` is genuinely needed. -/
theorem size_alone_does_not_give_coprimality :
    ¬ ∀ N M : ℕ, 0 < N → Nat.Prime M → Nat.Coprime N M := by
  intro h
  have := h 5 5 (by norm_num) (by norm_num)
  simp [Nat.Coprime] at this

/-- **Firewall.**  The source product `u · A` really can exceed `M`, so the false
justification "`N < M`" is unavailable: e.g. `u = A = M = 7` gives `uA = 49 > 7`
(and is not coprime to `M`, which is exactly why `M ∤ uA` must come from the
physical box separation). -/
theorem source_product_can_exceed_M :
    ∃ u A M : ℕ, Nat.Prime M ∧ M < u * A ∧ ¬ Nat.Coprime (u * A) M :=
  ⟨7, 7, 7, by norm_num, by norm_num, by decide⟩

end AddMinSource
end CurrentProgramme
end TwinPrimeProject
