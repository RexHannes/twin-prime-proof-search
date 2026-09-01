import Gate1B.FM722OneAtomLongLine

/-!
# Gate 1B · FM722 · **atom-type metadata and two-atom incidence data**

Two finite interfaces, both purely combinatorial.

* §1 `GammaAtomMetadata` — a *tagging interface* for the source classes of a
  generated `Γ`-atom.  It records an atom class, a finite support, a
  coefficient and a multiplicative provenance label.
* §2 `PhysicalGammaAtomFactorisation` — the **uninhabited** statement that a
  *physical* `Γ`-factor really is a product of tagged atoms.  This bank does
  not assert that every physical `Γ`-factor carries such a tag, and never
  constructs a term of this type.
* §3 `TwoAtomIncidenceData` — the finite incidence datum of the two-atom
  long line: slope `A`, line slope `ell`, anchor `(q₀ , b₀)`, the second atom
  `y`, the line parameter set, the atom coefficient, the residual `Γ`
  cofactor, the centred-model weight, the determinant certificate and the
  odd/coprimality certificates.  **No analytic bound field.**

## Semantic guard

An atom metadata interface is **not** a physical source realisation.  Tagging
an atom is a bookkeeping act; it proves nothing about the actual generated
`Γ`-factor.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722LongLine

/-! ## 1. Atom classes and metadata -/

/-- Source classes of a generated `Γ`-atom.  A finite enumeration used only as
a label. -/
inductive AtomClass
  | mobius
  | model
  | primeOrdered
  | smooth
  | residual
  deriving DecidableEq, Repr

/-- Multiplicative provenance of an atom: which multiplicative factor of the
generated source it was cut from.  Finite label. -/
inductive AtomProvenance
  | headFactor
  | tailFactor
  | crossFactor
  deriving DecidableEq, Repr

/-- **`GammaAtomMetadata`.**  Tagging interface for one generated `Γ`-atom:
class, finite support, coefficient, provenance.  No analytic field. -/
structure GammaAtomMetadata where
  /-- The source class of the atom. -/
  cls : AtomClass
  /-- The finite support of the atom. -/
  support : Finset ℤ
  /-- The coefficient carried by the atom. -/
  coeff : ℂ
  /-- The multiplicative provenance of the atom. -/
  provenance : AtomProvenance

/-- Metadata is inhabited: it is a bookkeeping type, not a claim. -/
theorem gammaAtomMetadata_nonempty : Nonempty GammaAtomMetadata :=
  ⟨⟨AtomClass.mobius, ∅, 0, AtomProvenance.headFactor⟩⟩

/-! ## 2. The physical realisation (never inhabited) -/

/-- **`PhysicalGammaAtomFactorisation` (UNINHABITED interface).**  The claim
that a given physical `Γ`-factor `G` literally factors, on a finite index set,
as the product of the tagged atoms of a supplied metadata family, each atom
being supported where its metadata says.

No term of this type is constructed anywhere in this bank: the repository
source does not supply this classification, and it is not assumed. -/
structure PhysicalGammaAtomFactorisation (G : ℤ → ℂ) where
  /-- The finite atom index. -/
  idx : Finset ℕ
  /-- The metadata of each atom. -/
  tag : ℕ → GammaAtomMetadata
  /-- The atom functions. -/
  atom : ℕ → ℤ → ℂ
  /-- Each atom is supported inside the support recorded by its metadata. -/
  supported : ∀ i ∈ idx, ∀ n : ℤ, n ∉ (tag i).support → atom i n = 0
  /-- The physical factor is exactly the product of the tagged atoms. -/
  reconstruct : ∀ n : ℤ, G n = ∏ i ∈ idx, atom i n

/-! ## 3. Two-atom incidence data -/

/-- **`TwoAtomIncidenceData`.**  The finite incidence datum for a second-atom
opening of the determinant-`(-2)` long line.  Purely finite: the only
propositional fields are the determinant certificate and the odd/coprimality
certificates.  **No analytic bound field exists in this structure.** -/
structure TwoAtomIncidenceData where
  /-- The current line slope `A` (for the one-atom line, `A = pi · z`). -/
  A : ℤ
  /-- The `b`-side slope. -/
  ell : ℤ
  /-- The modulus anchor. -/
  q0 : ℤ
  /-- The `b`-anchor. -/
  b0 : ℤ
  /-- The second atom to be opened. -/
  y : ℤ
  /-- The finite set of admissible line parameters. -/
  params : Finset ℤ
  /-- The coefficient carried by the atom. -/
  atomCoeff : ℂ
  /-- The residual `Γ` cofactor attached to the line. -/
  gammaCofactor : ℤ → ℂ
  /-- The centred-model weight subtracted from the arithmetic weight. -/
  modelWeight : ℤ → ℂ
  /-- Metadata of the second atom. -/
  atomMeta : GammaAtomMetadata
  /-- **Determinant certificate.** -/
  det : A * b0 - ell * q0 = -2
  /-- **Oddness certificate for the second atom.** -/
  yOdd : Odd y
  /-- **Nondegeneracy of the second atom.** -/
  yNe : y ≠ 0

namespace TwoAtomIncidenceData

variable (I : TwoAtomIncidenceData)

/-- The arithmetic `b`-value at line parameter `s`. -/
def bAt (s : ℤ) : ℤ := I.b0 + I.ell * s

/-- The modulus value at line parameter `s`. -/
def qAt (s : ℤ) : ℤ := I.q0 + I.A * s

/-- Every point of the incidence line carries determinant `-2`. -/
theorem det_at (s : ℤ) : I.A * I.bAt s - I.ell * I.qAt s = -2 :=
  det2_line_forward I.A I.ell I.q0 I.b0 I.det s

/-- **Coprimality of the second atom with `ell`,** derived (not assumed) from
oddness and the determinant certificate, whenever `y` divides the `b`-value at
some line parameter. -/
theorem y_coprime_ell (s : ℤ) (hy : I.y ∣ I.bAt s) : IsCoprime I.y I.ell :=
  odd_divisor_isCoprime_ell I.A I.ell (I.qAt s) (I.bAt s) I.y hy I.yOdd (I.det_at s)

end TwoAtomIncidenceData

end FM722LongLine
end CurrentProgramme
end TwinPrimeProject
