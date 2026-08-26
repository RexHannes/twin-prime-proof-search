import RequestProject.Options
namespace TwinPrimeProject.NANC
open scoped BigOperators

theorem prime_reinjection_identity {P G : Type} [AddCommGroup G]
    (s : Finset P) (a b w : P → G) (hw : ∀ p ∈ s, w p = a p - b p) :
    -∑ p ∈ s, w p = (∑ p ∈ s, b p) - ∑ p ∈ s, a p := by
  have hs : (∑ p ∈ s, w p) = ∑ p ∈ s, (a p - b p) := Finset.sum_congr rfl hw
  rw [hs, Finset.sum_sub_distrib]
  abel
end NANC
