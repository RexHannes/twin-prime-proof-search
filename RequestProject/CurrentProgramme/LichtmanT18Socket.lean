import Mathlib.Tactic

/-!
# Phase E · the Lichtman Theorem 1.8 **socket** (`ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45`)

**The external theorem is NOT formalised, NOT assumed, and NOT axiomatised.**
This module contains only

* a *data schema* describing what a proposed dictionary from the physical mixed
  endpoint model into the external theorem's variables would have to provide,
  and
* a *norm-obligation record* recording that the external theorem does **not**
  depend on one ordinary `‖b‖₂` alone.

Both are **uninhabited**: no term of either type is constructed anywhere in this
repository, and neither is used as a hypothesis of any unconditional statement.

The theorem-slot names are deliberately distinct from the physical variables:
`rL, sL, nL, cL, dL` are the slots; `m, m', r, s, ℓ, k, j` are physical.

Status:

```
ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45 : SOURCE_OPEN / UNINHABITED
LICHTMAN-T18-COEFF-NORM-DICTIONARY45         : SOURCE_OPEN
```
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace LichtmanSocket

open Finset

/-! ## 1. The physical index of the mixed endpoint model -/

/-- One physical index of the mixed `2|2` endpoint model: the two `m`-variables,
the two `(r,s)`-variables, the modulus `ℓ`, the Hilbert/`k`-parameter and the
mixed-index multiplier `j`. -/
structure PhysicalIndex where
  /-- first `m`-variable -/
  m : ℤ
  /-- second `m`-variable -/
  m' : ℤ
  /-- first `γ`-variable -/
  r : ℤ
  /-- second `γ`-variable -/
  s : ℤ
  /-- the modulus -/
  l : ℕ
  /-- the `k`-parameter -/
  k : ℤ
  /-- the mixed-index multiplier, `ν = jℓ` -/
  j : ℤ
  deriving DecidableEq

/-! ## 2. The dictionary schema (UNINHABITED) -/

/-- **UNINHABITED SOURCE SCHEMA.**  A proposed dictionary from the physical
mixed endpoint model into the external theorem's variables.

Every field is concrete data, an equality, or a predicate; there is no free
`Prop` placeholder that could be discharged with `True`.

Constructing a term of this type is exactly the open source obligation
`ENDPOINT-MIXED-2x2-LICHTMAN-T18-DICTIONARY45`.  **No term is constructed.** -/
structure LichtmanT18Dictionary where
  /-- the external theorem's parameter `a` -/
  a : ℕ
  /-- the external theorem's fixed modulus `q₀` -/
  q0 : ℕ
  /-- fixed residue class for the `c`-slot -/
  c0 : ℤ
  /-- fixed residue class for the `d`-slot -/
  d0 : ℤ
  /-- physical `→ rL` -/
  rL : PhysicalIndex → ℤ
  /-- physical `→ sL` -/
  sL : PhysicalIndex → ℤ
  /-- physical `→ nL` -/
  nL : PhysicalIndex → ℤ
  /-- physical `→ cL` -/
  cL : PhysicalIndex → ℤ
  /-- physical `→ dL` -/
  dL : PhysicalIndex → ℤ
  /-- the theorem's smooth weight `g(c,d,n,r,s)` -/
  g : ℤ → ℤ → ℤ → ℤ → ℤ → ℂ
  /-- the theorem's coefficient `b_{n,r,s}` -/
  b : ℤ → ℤ → ℤ → ℂ
  /-- the physical phase that the dictionary claims to represent -/
  physPhase : PhysicalIndex → ℂ
  /-- range field for the `n`-slot -/
  Nrange : ℝ
  /-- range field for the `r`-slot -/
  Rrange : ℝ
  /-- range field for the `s`-slot -/
  Srange : ℝ
  /-- range field for the `c`-slot -/
  Crange : ℝ
  /-- range field for the `d`-slot -/
  Drange : ℝ
  /-- the theorem's coprimality condition -/
  coprimality : ∀ x : PhysicalIndex, IsCoprime (cL x * dL x) (nL x * rL x * sL x)
  /-- `c ≡ c₀ (mod q₀)` -/
  cClass : ∀ x : PhysicalIndex, (cL x) % (q0 : ℤ) = c0
  /-- `d ≡ d₀ (mod q₀)` -/
  dClass : ∀ x : PhysicalIndex, (dL x) % (q0 : ℤ) = d0
  /-- support/range condition for `n` -/
  nRange : ∀ x : PhysicalIndex, |((nL x : ℝ))| ≤ Nrange
  /-- support/range condition for `r` -/
  rRange : ∀ x : PhysicalIndex, |((rL x : ℝ))| ≤ Rrange
  /-- support/range condition for `s` -/
  sRange : ∀ x : PhysicalIndex, |((sL x : ℝ))| ≤ Srange
  /-- support/range condition for `c` -/
  cRange : ∀ x : PhysicalIndex, |((cL x : ℝ))| ≤ Crange
  /-- support/range condition for `d` -/
  dRange : ∀ x : PhysicalIndex, |((dL x : ℝ))| ≤ Drange
  /-- **the phase identity**: the physical phase is literally the theorem's
  summand at the mapped variables -/
  phaseIdentity : ∀ x : PhysicalIndex,
    physPhase x = g (cL x) (dL x) (nL x) (rL x) (sL x) * b (nL x) (rL x) (sL x)

/-- **UNINHABITED PHYSICAL PIN.**  A dictionary is only *about* the physical
model once its `physPhase` is pinned to the actual summand of the mixed
coefficient `bMix`.  Since the physical `β = μ_D ⋆ Λ_P` endpoint source is
absent from the repository, this pin is left open.

```
ENDPOINT-BETA-PHYSICAL-DICTIONARY45 : SOURCE_BLOCKED / UNINHABITED
```
-/
structure LichtmanT18PhysicalPin (α : ℤ → ℂ) (Z : ℤ → ℕ → ℤ → ℂ) where
  /-- the proposed dictionary -/
  dict : LichtmanT18Dictionary
  /-- the pin to the actual mixed summand -/
  pinned : ∀ x : PhysicalIndex,
    dict.physPhase x = α x.m * (starRingEnd ℂ) (α x.m') *
      Z (x.m * x.r) x.l x.k * (starRingEnd ℂ) (Z (x.m' * x.s) x.l x.k)

/-! ### Counterguards for the dictionary schema -/

/-- **Counterguard.**  The phase identity is load-bearing: a dictionary with a
vanishing smooth weight forces a vanishing physical phase, so the schema cannot
be satisfied by an arbitrary phase. -/
theorem dictionary_phase_not_free (D : LichtmanT18Dictionary)
    (hg : D.g = fun _ _ _ _ _ => 0) (x : PhysicalIndex) : D.physPhase x = 0 := by
  rw [D.phaseIdentity x, hg]
  simp

/-- **Counterguard.**  The residue-class fields are load-bearing: two indices
mapped into the `c`-slot must be congruent mod `q₀`. -/
theorem dictionary_cClass_rigid (D : LichtmanT18Dictionary)
    (x y : PhysicalIndex) : (D.cL x) % (D.q0 : ℤ) = (D.cL y) % (D.q0 : ℤ) := by
  rw [D.cClass x, D.cClass y]

/-- **Counterguard.**  A physical pin determines the dictionary's phase; it
cannot be chosen after the fact.  If two pins share a dictionary they agree on
the physical summand. -/
theorem physicalPin_determines_phase {α : ℤ → ℂ} {Z : ℤ → ℕ → ℤ → ℂ}
    (P Q : LichtmanT18PhysicalPin α Z) (h : P.dict = Q.dict) (x : PhysicalIndex) :
    P.dict.physPhase x = Q.dict.physPhase x := by rw [h]

/-! ## 3. The `b` / `tilde-b` norm obligation (UNINHABITED) -/

/-- **UNINHABITED SOURCE-OBLIGATION RECORD.**

  `LICHTMAN-T18-COEFF-NORM-DICTIONARY45 : SOURCE_OPEN.`

The external theorem does **not** depend on one ordinary `‖b‖₂` alone: it also
requires control of a divisor-transformed coefficient family `tildeB(n'')`
supported on `n'' ∣ a^∞`.  This record states exactly what would have to be
supplied.  The literal definition of `tildeB` is **not guessed**: it is a data
field, because the external theorem has not been transcribed into this
repository. -/
structure LichtmanT18CoeffNorms where
  /-- the external theorem's parameter `a` -/
  a : ℕ
  /-- the ordinary coefficient family `b_{n,r,s}` -/
  b : ℤ → ℤ → ℤ → ℂ
  /-- the finite support of `b` used for the norms -/
  bSupport : Finset (ℤ × ℤ × ℤ)
  /-- the ordinary `ℓ²` norm -/
  bNorm : ℝ
  /-- `bNorm` really is the `ℓ²` norm of `b` on its support -/
  bNormPin : bNorm ^ 2 = ∑ t ∈ bSupport, ‖b t.1 t.2.1 t.2.2‖ ^ 2
  /-- the divisor-transformed family, indexed by `n''` -/
  tildeB : ℤ → ℤ → ℤ → ℤ → ℂ
  /-- its `ℓ²` norm, as a function of `n''` -/
  tildeBNorm : ℤ → ℝ
  /-- `tildeBNorm` really is the `ℓ²` norm of the transformed family -/
  tildeBNormPin : ∀ n'' : ℤ,
    (tildeBNorm n'') ^ 2 = ∑ t ∈ bSupport, ‖tildeB n'' t.1 t.2.1 t.2.2‖ ^ 2
  /-- the divisor support condition `n'' ∣ a^∞` -/
  tildeSupport : ∀ n'' : ℤ, (∃ t ∈ bSupport, tildeB n'' t.1 t.2.1 t.2.2 ≠ 0) →
    ∃ e : ℕ, n'' ∣ ((a : ℤ)) ^ e
  /-- the level the external theorem requires of the transformed norms -/
  requiredBound : ℝ
  /-- the required uniform norm bound -/
  normsAdmissible : ∀ n'' : ℤ, tildeBNorm n'' ≤ requiredBound

/-- **Firewall (why the extra norm family is a genuine obligation).**  An
ordinary `ℓ²` norm does **not** determine the norm of a transformed family: two
coefficient vectors with equal `ℓ²` norms can have transformed vectors of
different `ℓ²` norms.  Hence `bNorm` alone cannot discharge the
`tildeB`-obligation. -/
theorem transformed_norm_not_determined_by_l2 :
    ∃ (f g : Fin 2 → ℂ) (T : (Fin 2 → ℂ) → (Fin 2 → ℂ)),
      (∑ i, ‖f i‖ ^ 2 = ∑ i, ‖g i‖ ^ 2) ∧
        (∑ i, ‖T f i‖ ^ 2 ≠ ∑ i, ‖T g i‖ ^ 2) := by
  refine ⟨![1, 0], ![0, 1], fun u => ![u 0, 0], ?_, ?_⟩ <;>
    simp [Fin.sum_univ_two]

end LichtmanSocket
end CurrentProgramme
end TwinPrimeProject
