import Mathlib

namespace NANC

structure SupportModel where
  Smooth : Type
  Rough : Type
  smoothFin : Fintype Smooth
  roughFin : Fintype Rough
  smoothDecEq : DecidableEq Smooth
  roughDecEq : DecidableEq Rough

structure SideData (M : SupportModel) where
  qSmooth : Finset M.Smooth
  qRough : Finset M.Rough
  mSmooth : Finset M.Smooth
  mRough : Finset M.Rough

instance (M : SupportModel) : Fintype M.Smooth := M.smoothFin
instance (M : SupportModel) : Fintype M.Rough := M.roughFin
instance (M : SupportModel) : DecidableEq M.Smooth := M.smoothDecEq
instance (M : SupportModel) : DecidableEq M.Rough := M.roughDecEq

def compress (M : SupportModel) (x : Finset M.Smooth × Finset M.Rough) : SideData M :=
  { qSmooth := x.1
    qRough := x.2
    mSmooth := Finset.univ \ x.1
    mRough := Finset.univ \ x.2 }

 theorem compress_injective (M : SupportModel) : Function.Injective (compress M) := by
  intro x y h
  have h1 : x.1 = y.1 := congrArg SideData.qSmooth h
  have h2 : x.2 = y.2 := congrArg SideData.qRough h
  exact Prod.ext h1 h2

/-- The fixed certificate has one preimage at most: its selector is genuinely zero/one. -/
theorem compression_selector_zero_one (M : SupportModel) (d : SideData M) :
    ({x | compress M x = d} : Set (Finset M.Smooth × Finset M.Rough)).Subsingleton := by
  intro x hx y hy
  exact compress_injective M (hx.trans hy.symm)

end NANC
