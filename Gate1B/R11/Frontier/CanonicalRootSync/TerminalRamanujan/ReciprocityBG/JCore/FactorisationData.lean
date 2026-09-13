/-
# Gate1B / R11 / Frontier / … / ReciprocityBG / JCore : effective-modulus factorisation data
(J9)

Append-only module; exact algebra only.  **No** Wu–Xi / Shen / Bourgain–Garaev style analytic
estimate is formalised, assumed or named as a theorem here: this module only carries a finite
record describing a factorisation of the effective modulus `q_eff` into pairwise-coprime blocks,
for use by a later consumer.

No `sorry`, no `admit`, no custom axiom, no `native_decide`, no `unsafe`, no `opaque`.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore.CombinedConductor

namespace Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore

open Finset

/-- **Factorisation data for the effective modulus.**  The five blocks are the reduced source
block, the common core block, the two private core blocks and the small-label block; the record
carries their pairwise coprimality as fields, so a consumer may use them without re-deriving
anything. -/
structure QEffFactorisation where
  /-- reduced source block -/
  src : ℕ
  /-- common core block -/
  common : ℕ
  /-- first private core block -/
  priv1 : ℕ
  /-- second private core block -/
  priv2 : ℕ
  /-- small-label block -/
  label : ℕ
  /-- all blocks are positive -/
  pos : 0 < src ∧ 0 < common ∧ 0 < priv1 ∧ 0 < priv2 ∧ 0 < label
  /-- source vs core blocks -/
  cop_src_common : Nat.Coprime src common
  /-- source vs first private block -/
  cop_src_priv1 : Nat.Coprime src priv1
  /-- source vs second private block -/
  cop_src_priv2 : Nat.Coprime src priv2
  /-- source vs label block -/
  cop_src_label : Nat.Coprime src label
  /-- common vs first private block -/
  cop_common_priv1 : Nat.Coprime common priv1
  /-- common vs second private block -/
  cop_common_priv2 : Nat.Coprime common priv2
  /-- common vs label block -/
  cop_common_label : Nat.Coprime common label
  /-- the two private blocks -/
  cop_priv : Nat.Coprime priv1 priv2
  /-- first private vs label -/
  cop_priv1_label : Nat.Coprime priv1 label
  /-- second private vs label -/
  cop_priv2_label : Nat.Coprime priv2 label

namespace QEffFactorisation

/-- The effective modulus assembled from the blocks. -/
def modulus (D : QEffFactorisation) : ℕ := D.src * D.common * D.priv1 * D.priv2 * D.label

/-- The core (non-source) part of the effective modulus. -/
def corePart (D : QEffFactorisation) : ℕ := D.common * D.priv1 * D.priv2 * D.label

/-- Exact multiplicative decomposition: source block times core part. -/
theorem modulus_eq (D : QEffFactorisation) : D.modulus = D.src * D.corePart := by
  unfold modulus corePart
  ring

/-- The source block is coprime to the whole core part. -/
theorem cop_src_corePart (D : QEffFactorisation) : Nat.Coprime D.src D.corePart :=
  ((D.cop_src_common.mul_right D.cop_src_priv1).mul_right D.cop_src_priv2).mul_right
    D.cop_src_label

/-- The effective modulus is positive. -/
theorem modulus_pos (D : QEffFactorisation) : 0 < D.modulus := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := D.pos
  unfold modulus
  positivity

/-- Each block divides the effective modulus. -/
theorem src_dvd (D : QEffFactorisation) : D.src ∣ D.modulus := by
  rw [modulus_eq]; exact Dvd.intro _ rfl

theorem corePart_dvd (D : QEffFactorisation) : D.corePart ∣ D.modulus := by
  rw [modulus_eq]; exact Dvd.intro_left _ rfl

end QEffFactorisation

/-- **The clean-support consequence.**  On clean source/core support the source variable is
coprime to both second denominators, which is the coprimality a block factorisation of the
effective modulus consumes.  (Exact statement only; no size estimate is attached.) -/
theorem cleanSupport_gives_block_coprimality {o : Outer} {i j : Core} (h : CleanSupport o i j) :
    Nat.Coprime o.z i.v ∧ Nat.Coprime o.z j.v :=
  ⟨cleanSupport_coprime_left h, cleanSupport_coprime_right h⟩

end Gate1B.R11.Frontier.CanonicalRootSync.TerminalRamanujan.ReciprocityBG.JCore
