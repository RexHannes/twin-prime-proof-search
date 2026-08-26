/-
# NANC Gate 1A v9.4 — quotient recombination interface

The corrected route splits the exact source into a *main packet* and an *error
packet*,

    exactSource = mainPacket + errorPacket,

and recombines them.  The recombination step itself is finite and exact: the
energy of a sum of two packets is at most twice the sum of their energies.
The two genuinely analytic ingredients — the normalization of the main packet
and the size of the error packet — are recorded as **certificate fields**, not
as theorems.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

variable {Idx : Type*} [Fintype Idx]

/-- Finite energy of a packet. -/
noncomputable def packetEnergy (f : Idx → ℂ) : ℝ := ∑ i, ‖f i‖ ^ 2

theorem packetEnergy_nonneg (f : Idx → ℂ) : 0 ≤ packetEnergy f :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **Exact finite recombination.**  Splitting a source into a main and an
error packet costs at most a factor `2` in energy. -/
theorem packetEnergy_split (f g : Idx → ℂ) :
    packetEnergy (fun i => f i + g i) ≤ 2 * packetEnergy f + 2 * packetEnergy g := by
  have hpt : ∀ i : Idx, ‖f i + g i‖ ^ 2 ≤ 2 * ‖f i‖ ^ 2 + 2 * ‖g i‖ ^ 2 := by
    intro i
    have htri : ‖f i + g i‖ ≤ ‖f i‖ + ‖g i‖ := norm_add_le _ _
    nlinarith [sq_nonneg (‖f i‖ - ‖g i‖), norm_nonneg (f i + g i), norm_nonneg (f i),
      norm_nonneg (g i)]
  unfold packetEnergy
  calc ∑ i, ‖f i + g i‖ ^ 2 ≤ ∑ i, (2 * ‖f i‖ ^ 2 + 2 * ‖g i‖ ^ 2) :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = 2 * ∑ i, ‖f i‖ ^ 2 + 2 * ∑ i, ‖g i‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- A **quotient recombination certificate**.  The two analytic inputs (the
main-packet normalization and the error-packet bound) are hypotheses carried by
the structure; nothing analytic is proved here. -/
structure QuotientRecombinationCertificate (Idx : Type*) [Fintype Idx] where
  /-- The exact source. -/
  exactSource : Idx → ℂ
  /-- The main packet. -/
  mainPacket : Idx → ℂ
  /-- The error packet. -/
  errorPacket : Idx → ℂ
  /-- The exact splitting identity. -/
  splits : ∀ i, exactSource i = mainPacket i + errorPacket i
  /-- Main-packet normalization (analytic input). -/
  mainBound : ℝ
  mainNormalization : packetEnergy mainPacket ≤ mainBound
  /-- Error-packet bound (analytic input). -/
  errorBound : ℝ
  errorControl : packetEnergy errorPacket ≤ errorBound

namespace QuotientRecombinationCertificate

variable (C : QuotientRecombinationCertificate Idx)

/-- **Recombination bound.**  The certificate yields a finite bound on the
exact source energy. -/
theorem source_energy_le : packetEnergy C.exactSource ≤ 2 * C.mainBound + 2 * C.errorBound := by
  have hsplit : C.exactSource = fun i => C.mainPacket i + C.errorPacket i := by
    funext i; exact C.splits i
  rw [hsplit]
  refine (packetEnergy_split C.mainPacket C.errorPacket).trans ?_
  have h1 := C.mainNormalization
  have h2 := C.errorControl
  linarith

end QuotientRecombinationCertificate

/-- Firewall: the factor `2` is genuinely needed — the split is not an
isometry.  With `f = g` the split energy is exactly `4` times either half. -/
theorem packetEnergy_split_factor_needed :
    packetEnergy (fun _ : Fin 1 => (1 : ℂ) + 1) = 4 ∧ packetEnergy (fun _ : Fin 1 => (1 : ℂ)) = 1 := by
  refine ⟨?_, by simp [packetEnergy]⟩
  simp only [packetEnergy, Finset.univ_unique, Finset.sum_singleton]
  norm_num

end TwinPrimeProject.NANC.Gate1A.V94
