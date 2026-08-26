import RequestProject.HalfSieveArithmeticBridge
import RequestProject.HalfSieveAnalyticInterfaces
import RequestProject.HalfSieveKernelUniqueness
import RequestProject.LinearKernelCatalan
import RequestProject.T0GStratification

namespace HalfSieve

lemma halfSieveFiniteCoreBanked :
    fullCutoffMass (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  simpa using fullCutoffMass_eq_primeIndicator (fun _ : Fin 1 => (1 : ℝ)) (by simp) (by simp)

lemma halfSieveParityProjectionBanked :
    halfKernel (fun _ : Fin 1 => (1 : ℝ)) = 1 := by
  exact halfKernel_singleton _ (by simp) (by simp)

lemma p7CertificateBanked : p7 0 = 1 ∧ p7 (1 / 2) = 0 := ⟨p7_zero, p7_half⟩

lemma p7CorrectedEqualCellsBanked :
    equalCellCoeff 12 p7Rat ≠ 0 ∧ equalCellCoeff 14 p7Rat ≠ 0 :=
  ⟨p7_equalCell_twelve_ne_zero, p7_equalCell_fourteen_ne_zero⟩

lemma linearKernelCatalanChecksBanked :
    equalCellCoeff 6 linearKernelRat = 2 ∧ equalCellCoeff 12 linearKernelRat = -42 :=
  ⟨linearKernel_C6, linearKernel_C12⟩

end HalfSieve
