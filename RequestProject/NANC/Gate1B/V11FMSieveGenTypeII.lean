import RequestProject.NANC.Gate1B.V11GeneratedExpression

/-!
# V11 · Gate 1B — the project-local FM-SieveGen Type-II predicate

A **new v11 mathematical predicate**.  It is *not* called `FordMaynardTheorem`,
`FullFMTypeII` or `Proposition722`: none of those objects exists in this
repository, and nothing here claims to be them.

The schematic object formalised is the equation-(7.23)-style sum

    ∑_{n₁,…,n_N}  [∏_j n_j ∈ physical range]
                  [∏_{j ∈ E} n_j ∈ Type-II interval]
                  w(∏_j n_j)  ∏_j x_j(n_j),

for a bounded number `N` of factors, a nonempty selected subset `E`, explicit
factor ranges, an explicit sequence `w` and a supplied target.

Two predicates are defined:

* `FMSieveGenTypeIIAtScale` — the bound for **arbitrary** 1-bounded factor
  functions `x_j`;
* `FMPerronGeneratedTypeIIAtScale` — the bound for factor functions carrying an
  `FMPerronGenerated` certificate.

The mechanical implication SieveGen ⟹ Generated is proved.  **The converse is
not claimed anywhere.**
-/

namespace TwinPrimeProject
namespace Gate1BV11

open Finset

/-- The finite data of an FM-SieveGen Type-II configuration with `N` factors. -/
structure FMSieveGenData (N : ℕ) where
  /-- The nonempty selected subset of factor indices. -/
  E : Finset (Fin N)
  /-- `E` is nonempty. -/
  E_nonempty : E.Nonempty
  /-- Lower endpoint of the `j`-th factor range. -/
  lo : Fin N → ℕ
  /-- Upper endpoint of the `j`-th factor range. -/
  hi : Fin N → ℕ
  /-- Lower endpoint of the physical product range. -/
  physLo : ℕ
  /-- Upper endpoint of the physical product range. -/
  physHi : ℕ
  /-- Lower endpoint of the selected-product Type-II interval. -/
  typeIILo : ℕ
  /-- Upper endpoint of the selected-product Type-II interval. -/
  typeIIHi : ℕ
  /-- The actual `w_n` sequence. -/
  w : ℕ → ℂ
  /-- The target / log-budget parameter. -/
  target : ℝ

variable {N : ℕ}

/-- The box of admissible factor tuples. -/
def factorBox (d : FMSieveGenData N) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun j => Finset.Icc (d.lo j) (d.hi j)

/-- The physical-range indicator. -/
def physIndicator (d : FMSieveGenData N) (n : Fin N → ℕ) : ℂ :=
  if (∏ j, n j) ∈ Finset.Icc d.physLo d.physHi then 1 else 0

/-- The selected-product Type-II indicator. -/
def typeIIIndicator (d : FMSieveGenData N) (n : Fin N → ℕ) : ℂ :=
  if (∏ j ∈ d.E, n j) ∈ Finset.Icc d.typeIILo d.typeIIHi then 1 else 0

/-- **The FM-SieveGen Type-II sum.** -/
noncomputable def sieveGenValue (d : FMSieveGenData N) (x : Fin N → ℕ → ℂ) : ℂ :=
  ∑ n ∈ factorBox d,
    physIndicator d n * typeIIIndicator d n * d.w (∏ j, n j) * ∏ j, x j (n j)

/-- **FM-SieveGen Type-II at scale** — the bound for *arbitrary* 1-bounded factor
functions.  This is the strong, project-local predicate. -/
def FMSieveGenTypeIIAtScale (d : FMSieveGenData N) : Prop :=
  ∀ x : Fin N → ℕ → ℂ, (∀ j n, ‖x j n‖ ≤ 1) → ‖sieveGenValue d x‖ ≤ d.target

/-- **FM-Perron-generated Type-II at scale** — the bound only for factor
functions equipped with a generated-grammar certificate.  Strictly weaker
quantification. -/
def FMPerronGeneratedTypeIIAtScale (d : FMSieveGenData N) : Prop :=
  ∀ x : Fin N → ℕ → ℂ, (∀ j, FMPerronGeneratedUnit (x j)) → ‖sieveGenValue d x‖ ≤ d.target

/-- **SieveGen ⟹ Generated.**  Mechanical, but the direction that matters for
the programme: any proof of the arbitrary-coefficient statement also proves the
generated one. -/
theorem fmPerronGeneratedTypeII_of_sieveGen (d : FMSieveGenData N)
    (h : FMSieveGenTypeIIAtScale d) : FMPerronGeneratedTypeIIAtScale d := by
  intro x hx
  exact h x fun j n => (hx j).2 n

/-! ### Non-vacuity guards -/

/-- The one-factor configuration with all indicators active on `{1}`, weight `1`
and target `0`. -/
noncomputable def toyData : FMSieveGenData 1 where
  E := Finset.univ
  E_nonempty := ⟨0, Finset.mem_univ 0⟩
  lo := fun _ => 1
  hi := fun _ => 1
  physLo := 1
  physHi := 1
  typeIILo := 1
  typeIIHi := 1
  w := fun _ => 1
  target := 0

/-- The toy value at the constant factor function is `1`. -/
theorem sieveGenValue_toy :
    sieveGenValue toyData (fun _ => semAtom (.constant 1)) = 1 := by
  classical
  have hbox : factorBox toyData = {fun _ => 1} := by
    ext n
    simp [factorBox, toyData, Finset.mem_singleton, le_antisymm_iff]
  simp only [sieveGenValue]
  rw [hbox]
  simp [physIndicator, typeIIIndicator, toyData, semAtom]

/-- **The predicate is not vacuously true.**  For the toy configuration with
target `0` the generated Type-II bound fails, so no compiler can produce it
without genuine analytic input. -/
theorem fmPerronGeneratedTypeII_toy_fails : ¬ FMPerronGeneratedTypeIIAtScale toyData := by
  intro h
  have hx : ∀ _j : Fin 1, FMPerronGeneratedUnit (semAtom (.constant 1)) := fun _ =>
    fmPerronGeneratedUnit_atom (.constant 1) (by simp [GenAtom.Admissible])
  have := h (fun _ => semAtom (.constant 1)) hx
  rw [sieveGenValue_toy] at this
  norm_num [toyData] at this

/-- …and the same for the stronger SieveGen predicate. -/
theorem fmSieveGenTypeII_toy_fails : ¬ FMSieveGenTypeIIAtScale toyData := fun h =>
  fmPerronGeneratedTypeII_toy_fails (fmPerronGeneratedTypeII_of_sieveGen _ h)

end Gate1BV11
end TwinPrimeProject
