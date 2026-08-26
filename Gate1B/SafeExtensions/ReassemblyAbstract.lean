/-
# Gate 1B v8.2 — abstract reassembly

A face-by-face reassembly compiler: if every face of a finite decomposition
carries a certificate bounding it by its own budget, the assembled quantity is
bounded by the sum of the budgets.

This is bookkeeping only.  **No face certificate is inhabited in this project.**
The open rows are listed in the comment below.

Open rows (no certificate constructed):

* the PV medium face;
* the large-sieve face;
* the overlap face;
* the axis face;
* the GCD-β face;
* the exceptional 2-adic face.
-/
import Mathlib

namespace Gate1B.SafeExtensions

open Finset

/-- A face of the reassembly, carrying its quantity and its budget. -/
structure GateFace where
  /-- The quantity attached to the face. -/
  value : ℝ
  /-- The budget recorded for the face. -/
  budget : ℝ

/-- A certificate that a face respects its budget.  Uninhabited in this
project. -/
structure GateFaceCertificate (F : GateFace) : Prop where
  /-- The face value is at most the face budget. -/
  value_le : F.value ≤ F.budget

/-- **Reassembly compiler.**  Certificates for all faces give the assembled
bound. -/
theorem reassemble_of_face_certificates {J : Type*} (s : Finset J) (F : J → GateFace)
    (h : ∀ j ∈ s, GateFaceCertificate (F j)) :
    ∑ j ∈ s, (F j).value ≤ ∑ j ∈ s, (F j).budget :=
  Finset.sum_le_sum fun j hj => (h j hj).value_le

/-- A certificate is not automatic: a face can exceed its budget. -/
theorem gateFaceCertificate_not_automatic :
    ∃ F : GateFace, ¬ GateFaceCertificate F := by
  refine ⟨⟨1, 0⟩, ?_⟩
  intro h
  have := h.value_le
  norm_num at this

/-- The compiler does not manufacture certificates: from the assembled
conclusion alone one cannot recover a face certificate. -/
theorem reassembly_not_self_certifying :
    ∃ (F : Fin 2 → GateFace),
      (∑ j, (F j).value ≤ ∑ j, (F j).budget) ∧ ¬ GateFaceCertificate (F 0) := by
  refine ⟨![⟨1, 0⟩, ⟨0, 1⟩], ?_, ?_⟩
  · simp [Fin.sum_univ_two]
  · intro h
    have := h.value_le
    norm_num at this

end Gate1B.SafeExtensions
