import Mathlib

/-!
# Gate 1B · canonical balanced-R9 comparison source (append-only)

**Everything proved in this module is exact algebra**: an identity between
coordinate decompositions, the definition of the canonical occupancy model, an
exact finite multinomial identity for the canonical total mass, and the exact
`p = 2` correction identity.  No analytic estimate is proved here, none is
assumed, and no asymptotic statement occurs anywhere in the file.

## Contents

* §1 the fresh balanced-R9 coordinate decomposition
  `π_i = f_i + δ_i − e_i^{pp}`, `δ_i = λ_i + ρ_i`, `m_i^{can} = f_i + λ_i`, and
  the boxed identity `π_i = m_i^{can} + ρ_i − e_i^{pp}`
  (`coordinate_eq_canonical_add_remainder`);
* §2 the canonical occupancy model `b9CellCan` with **explicit** factorial
  normalisation, and `b9Can` as a finite sum over the physical occupancy
  family;
* §3 the total-mass functional as an **interface** (`TotalMass`), never
  inhabited here, together with the exact cell mass formula;
* §4 the exact finite degree-nine multinomial identity
  `∑_n b9Can(n) = (1/9!)·(∑_λ ∑_n m_λ^{can}(n))^9` on the complete occupancy
  family, and the exact finite polynomial for an arbitrary subfamily;
* §5 the zero-frequency `ρ`-mass: **exposed as a projector interface**, with
  the derived mass relation `∑ m^{can} = ∑ π + ∑ e^{pp}`;
* §6 the exact `p = 2` correction `c9 − b9CanOdd = (c9 − b9Can) + Δ₂`, with an
  explicit firewall that `Δ₂` is **not** claimed to be small.

The coefficient objects are `ArithmeticFunction ℂ`, so that the Dirichlet
convolution is the ring multiplication and associativity/commutativity are
kernel facts rather than assumptions.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace CanonicalR9

open Finset ArithmeticFunction

/-! ## 0. Scalar scaling of a coefficient sequence

`ArithmeticFunction ℂ` carries no `ℂ`-scalar action in Mathlib, so the
factorial normalisation is implemented by an explicit scaling operator.  It is
*not* silently absorbed anywhere. -/

/-- Scaling of a coefficient sequence by a complex scalar. -/
noncomputable def cScale (c : ℂ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => c * f n, by simp⟩

@[simp] theorem cScale_apply (c : ℂ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    cScale c f n = c * f n := rfl

/-! ## 1. The fresh balanced-R9 coordinate decomposition -/

section Coordinates

variable {A : Type*} [AddCommGroup A]

/-- **BOXED (§4 of the specification).**  With

```
pi_i     = f_i + delta_i - e_i_pp,
delta_i  = lambda_i + rho_i,
m_i_can  = f_i + lambda_i,
```

the coordinate is exactly the canonical model plus the first remainder:

```
pi_i = m_i_can + rho_i - e_i_pp.
```

This is an exact identity, with no analytic approximation. -/
theorem coordinate_eq_canonical_add_remainder
    (pi f delta e lam rho mcan : A)
    (hpi : pi = f + delta - e) (hdelta : delta = lam + rho)
    (hm : mcan = f + lam) :
    pi = mcan + rho - e := by
  subst hpi; subst hdelta; subst hm; abel

/-- The same identity for a whole family of coordinates. -/
theorem coordinate_eq_canonical_add_remainder_family {ι : Type*}
    (pi f delta e lam rho mcan : ι → A)
    (hpi : ∀ i, pi i = f i + delta i - e i)
    (hdelta : ∀ i, delta i = lam i + rho i)
    (hm : ∀ i, mcan i = f i + lam i) :
    ∀ i, pi i = mcan i + rho i - e i := fun i =>
  coordinate_eq_canonical_add_remainder _ _ _ _ _ _ _ (hpi i) (hdelta i) (hm i)

/-- The first remainder `ε_i := ρ_i − e_i^{pp}`, so that `π_i = m_i^{can} + ε_i`. -/
def firstRemainder (rho e : A) : A := rho - e

theorem coordinate_eq_canonical_add_firstRemainder
    (pi f delta e lam rho mcan : A)
    (hpi : pi = f + delta - e) (hdelta : delta = lam + rho)
    (hm : mcan = f + lam) :
    pi = mcan + firstRemainder rho e := by
  rw [coordinate_eq_canonical_add_remainder pi f delta e lam rho mcan hpi hdelta hm,
    firstRemainder]
  abel

end Coordinates

/-! ## 2. The canonical occupancy model

The factorial normalisation is kept **explicit**: the labelled source
`m_λ^{can}` is never silently replaced by a symmetric source. -/

variable {Lab : Type*} [DecidableEq Lab]

/-- The canonical occupancy cell

```
b9CellCan(m) = 1/(∏_λ m_λ!) · (Dirichlet) ∏_λ (m_λ^{can})^{* m_λ}.
```

The convolution power is the ring power in `ArithmeticFunction ℂ`, i.e. the
Dirichlet convolution power. -/
noncomputable def b9CellCan (s : Finset Lab) (mcan : Lab → ArithmeticFunction ℂ)
    (occ : Lab → ℕ) : ArithmeticFunction ℂ :=
  cScale ((∏ l ∈ s, ((occ l).factorial : ℂ))⁻¹) (∏ l ∈ s, (mcan l) ^ (occ l))

/-- The canonical comparison sequence: the finite sum of the canonical cells
over the physical occupancy family. -/
noncomputable def b9Can (s : Finset Lab) (mcan : Lab → ArithmeticFunction ℂ)
    (family : Finset (Lab → ℕ)) : ArithmeticFunction ℂ :=
  ∑ occ ∈ family, b9CellCan s mcan occ

omit [DecidableEq Lab] in
theorem b9Can_empty (s : Finset Lab) (mcan : Lab → ArithmeticFunction ℂ) :
    b9Can s mcan ∅ = 0 := by simp [b9Can]

omit [DecidableEq Lab] in
theorem b9Can_singleton (s : Finset Lab) (mcan : Lab → ArithmeticFunction ℂ)
    (occ : Lab → ℕ) : b9Can s mcan {occ} = b9CellCan s mcan occ := by
  simp [b9Can]

/-! ## 3. The total-mass functional interface

`∑_n f(n)` is **not** definable for an arbitrary `ArithmeticFunction ℂ`, so the
total mass is exposed as an interface with exactly the algebraic properties
used below.  It is never inhabited in this module. -/

/-- Interface for a total-mass functional: additive, multiplicative for the
Dirichlet convolution, normalised at `1`, and homogeneous for `cScale`. -/
structure TotalMass where
  /-- The functional itself. -/
  m : ArithmeticFunction ℂ → ℂ
  /-- Additivity. -/
  m_add : ∀ f g, m (f + g) = m f + m g
  /-- Multiplicativity for the Dirichlet convolution. -/
  m_mul : ∀ f g, m (f * g) = m f * m g
  /-- Normalisation at the Dirichlet unit. -/
  m_one : m 1 = 1
  /-- Homogeneity. -/
  m_scale : ∀ c f, m (cScale c f) = c * m f

namespace TotalMass

variable (T : TotalMass)

theorem m_zero : T.m 0 = 0 := by
  have h := T.m_add 0 0
  simp at h
  exact h

theorem m_sub (f g : ArithmeticFunction ℂ) : T.m (f - g) = T.m f - T.m g := by
  have h := T.m_add (f - g) g
  simp at h
  rw [h]; ring

theorem m_prod (s : Finset Lab) (g : Lab → ArithmeticFunction ℂ) :
    T.m (∏ l ∈ s, g l) = ∏ l ∈ s, T.m (g l) := by
  classical
  induction s using Finset.induction with
  | empty => simp [T.m_one]
  | insert a s ha ih => simp [Finset.prod_insert ha, T.m_mul, ih]

theorem m_pow (f : ArithmeticFunction ℂ) (k : ℕ) : T.m (f ^ k) = (T.m f) ^ k := by
  induction k with
  | zero => simp [T.m_one]
  | succ k ih => rw [pow_succ, T.m_mul, ih, pow_succ]

theorem m_sum (s : Finset Lab) (g : Lab → ArithmeticFunction ℂ) :
    T.m (∑ l ∈ s, g l) = ∑ l ∈ s, T.m (g l) := by
  classical
  induction s using Finset.induction with
  | empty => simp [T.m_zero]
  | insert a s ha ih => simp [Finset.sum_insert ha, T.m_add, ih]

end TotalMass

/-- Exact mass of a canonical occupancy cell. -/
theorem mass_b9CellCan (T : TotalMass) (s : Finset Lab)
    (mcan : Lab → ArithmeticFunction ℂ) (occ : Lab → ℕ) :
    T.m (b9CellCan s mcan occ)
      = (∏ l ∈ s, ((occ l).factorial : ℂ))⁻¹ * ∏ l ∈ s, (T.m (mcan l)) ^ (occ l) := by
  rw [b9CellCan, T.m_scale, T.m_prod]
  simp [T.m_pow]

/-! ## 4. Exact canonical total-mass algebra -/

/-- **Exact finite multinomial identity.**  For the complete degree-nine
occupancy family `s.piAntidiag 9`,

```
∑_occ (∏_λ occ_λ!)⁻¹ ∏_λ T_λ^{occ_λ} = (1/9!) (∑_λ T_λ)^9.
```

This is an exact polynomial identity in the coordinate masses `T_λ`; no
asymptotic statement is involved. -/
theorem canonical_totalMass_multinomial (s : Finset Lab) (T : Lab → ℂ) :
    ∑ occ ∈ s.piAntidiag 9,
        (∏ l ∈ s, ((occ l).factorial : ℂ))⁻¹ * ∏ l ∈ s, (T l) ^ (occ l)
      = ((Nat.factorial 9 : ℕ) : ℂ)⁻¹ * (∑ l ∈ s, T l) ^ 9 := by
  classical
  rw [Finset.sum_pow_eq_sum_piAntidiag s T 9, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro occ hocc
  have hsum : ∑ l ∈ s, occ l = 9 := (Finset.mem_piAntidiag.mp hocc).1
  have hspec := Nat.multinomial_spec s occ
  rw [hsum] at hspec
  have hfac : ((∏ l ∈ s, (occ l).factorial : ℕ) : ℂ) * ((Nat.multinomial s occ : ℕ) : ℂ)
      = ((Nat.factorial 9 : ℕ) : ℂ) := by
    exact_mod_cast congrArg (fun k : ℕ => (k : ℂ)) hspec
  have hne : ((∏ l ∈ s, (occ l).factorial : ℕ) : ℂ) ≠ 0 := by
    have : (0 : ℕ) < ∏ l ∈ s, (occ l).factorial :=
      Finset.prod_pos fun l _ => Nat.factorial_pos _
    exact_mod_cast Nat.cast_ne_zero.mpr this.ne'
  have hcast : (∏ l ∈ s, ((occ l).factorial : ℂ))
      = ((∏ l ∈ s, (occ l).factorial : ℕ) : ℂ) := by push_cast; ring
  rw [hcast]
  field_simp
  rw [← hfac]
  ring

/-- The same statement for the canonical model, under a total-mass interface:
the canonical total mass is the exact degree-nine polynomial in the coordinate
masses. -/
theorem canonical_b9Can_totalMass (T : TotalMass) (s : Finset Lab)
    (mcan : Lab → ArithmeticFunction ℂ) :
    T.m (b9Can s mcan (s.piAntidiag 9))
      = ((Nat.factorial 9 : ℕ) : ℂ)⁻¹ * (∑ l ∈ s, T.m (mcan l)) ^ 9 := by
  classical
  rw [b9Can, T.m_sum]
  rw [Finset.sum_congr rfl (fun occ _ => mass_b9CellCan T s mcan occ)]
  exact canonical_totalMass_multinomial s (fun l => T.m (mcan l))

/-- **Subfamily version.**  If the physical occupancy set is only a subset of
the complete family, the canonical total mass is the exact finite polynomial
attached to that subset — no asymptotic replacement is made. -/
theorem canonical_b9Can_totalMass_subfamily (T : TotalMass) (s : Finset Lab)
    (mcan : Lab → ArithmeticFunction ℂ) (family : Finset (Lab → ℕ)) :
    T.m (b9Can s mcan family)
      = ∑ occ ∈ family,
          (∏ l ∈ s, ((occ l).factorial : ℂ))⁻¹ * ∏ l ∈ s, (T.m (mcan l)) ^ (occ l) := by
  classical
  rw [b9Can, T.m_sum]
  exact Finset.sum_congr rfl fun occ _ => mass_b9CellCan T s mcan occ

/-! ## 5. Zero-frequency `ρ` mass

The statement "the major projector has value `1` at zero frequency" is not
derivable from anything formalised in this repository, so it is exposed as an
explicit interface field, exactly as the specification requires. -/

/-- Interface for a major-arc projector whose value at the zero frequency is
`1`, i.e. which preserves total mass. -/
structure ZeroFrequencyProjector (T : TotalMass) where
  /-- The projector. -/
  proj : ArithmeticFunction ℂ → ArithmeticFunction ℂ
  /-- Value `1` at zero frequency: the projector preserves total mass. -/
  mass_proj : ∀ f, T.m (proj f) = T.m f

/-- `∑_n ρ_i(n) = 0` for the broad-major remainder `ρ = δ − λ`, `λ = proj δ`. -/
theorem rho_totalMass_eq_zero (T : TotalMass) (P : ZeroFrequencyProjector T)
    (delta lam rho : ArithmeticFunction ℂ)
    (hlam : lam = P.proj delta) (hrho : rho = delta - lam) :
    T.m rho = 0 := by
  subst hrho; subst hlam
  rw [T.m_sub, P.mass_proj]
  ring

/-- The derived mass relation `∑ m^{can} = ∑ π + ∑ e^{pp}`. -/
theorem canonical_mass_relation (T : TotalMass)
    (pi mcan rho e : ArithmeticFunction ℂ)
    (hpi : pi = mcan + rho - e) (hrho : T.m rho = 0) :
    T.m mcan = T.m pi + T.m e := by
  subst hpi
  rw [T.m_sub, T.m_add, hrho]
  ring

/-! ## 6. The `p = 2` canonical correction -/

/-- `Δ₂(n) := b9Can(n)` on even `n`, `0` on odd `n`. -/
noncomputable def Delta2 (b : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if 2 ∣ n then b n else 0, by simp⟩

@[simp] theorem Delta2_apply (b : ArithmeticFunction ℂ) (n : ℕ) :
    Delta2 b n = if 2 ∣ n then b n else 0 := rfl

/-- The odd part of the canonical comparison sequence. -/
noncomputable def b9CanOdd (b : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  b - Delta2 b

/-- **Exact `p = 2` correction identity.**

```
c9 − b9CanOdd = (c9 − b9Can) + Δ₂.
```

The odd support of `c9` mentioned in the specification is *not needed*: the
identity is a ring identity valid for every `c9`.  (The odd support of `c9` is
what makes the identity *useful*, not what makes it *true*.) -/
theorem canonical_p2_correction (c b : ArithmeticFunction ℂ) :
    c - b9CanOdd b = (c - b) + Delta2 b := by
  rw [b9CanOdd]; ring

/-- `b9CanOdd` is genuinely supported on odd integers. -/
theorem b9CanOdd_eq_zero_of_even (b : ArithmeticFunction ℂ) {n : ℕ} (hn : 2 ∣ n) :
    b9CanOdd b n = 0 := by
  show b n - Delta2 b n = 0
  simp [hn]

/-- **Firewall.**  `Δ₂` is not claimed to be small: it can be as large as the
comparison sequence itself.  It is routed to an explicit `q = 2` local-owner
interface, never estimated here. -/
theorem Delta2_not_small : ∃ b : ArithmeticFunction ℂ, Delta2 b 2 = 1 := by
  refine ⟨⟨fun n => if n = 2 then 1 else 0, by norm_num⟩, ?_⟩
  norm_num

/-- The `q = 2` local owner is an interface, never an estimate. -/
structure QTwoLocalOwner where
  /-- The budget assigned to the `p = 2` correction. -/
  budget : ℝ
  /-- The obligation: the `p = 2` correction is owned inside its budget.  This
  field is never supplied in this module. -/
  owned : Prop

end CanonicalR9
end CurrentProgramme
end TwinPrimeProject
