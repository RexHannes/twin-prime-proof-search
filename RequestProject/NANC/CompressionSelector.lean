import RequestProject.Options
namespace TwinPrimeProject.NANC
structure CompressedData (S R : Type) [DecidableEq S] [DecidableEq R] where
  smoothQ : Finset S
  roughQ : Finset R
  smoothM : Finset S
  roughM : Finset R

def compress {S R : Type} [DecidableEq S] [DecidableEq R]
    (fullSmooth : Finset S) (fullRough : Finset R)
    (e : Finset S) (K : Finset R) : CompressedData S R :=
  ⟨e, K, fullSmooth \ e, fullRough \ K⟩

theorem compression_selector_zero_one {S R : Type} [DecidableEq S] [DecidableEq R]
    (fullSmooth : Finset S) (fullRough : Finset R) :
    Function.Injective (fun x : Finset S × Finset R =>
      compress fullSmooth fullRough x.1 x.2) := by
  intro x y h
  cases x with | mk e K =>
    cases y with | mk e' K' =>
      simp_all [compress]
end NANC
