import RequestProject.Options
namespace TwinPrimeProject.NANC

structure ROWReciprocalConcentrationInput where
  concentrationBound : Prop

structure ROWClosureFromConcentration where
  reciprocalConcentration : Prop
  rowClosed : Prop
  assemble : reciprocalConcentration → rowClosed

theorem row_closed_from_reciprocal_concentration (H : ROWClosureFromConcentration)
    (h : H.reciprocalConcentration) : H.rowClosed := H.assemble h
end TwinPrimeProject.NANC
