import RequestProject.EqualCellFiniteDifference

namespace HalfSieve

/-- Explicit proof-carrying interface. It deliberately has no global inhabitant. -/
structure HalfSieveAnalyticInput (Collar Shifted Ford : Prop) : Prop where
  collarEstimate : Collar
  shiftedParityEstimate : Shifted
  fordGeometryMargin : Ford

structure VStarInput (ExactReassembly BDH Propagated : Prop) : Prop where
  exactReassembly : ExactReassembly
  bdhBound : BDH
  propagatedBound : Propagated

structure T0StarInput (Reciprocity Stratification Fourier Compensation LargeSieve
    ExponentClosure Propagated : Prop) : Prop where
  reciprocityIdentity : Reciprocity
  gcdStratification : Stratification
  localFourierExpansion : Fourier
  compensationBound : Compensation
  characterLargeSieve : LargeSieve
  exponentClosure : ExponentClosure
  propagatedP3Bound : Propagated

structure ShiftedOrbitInput (CRT Orbit Translation : Prop) : Prop where
  crtReciprocity : CRT
  orbitIdentity : Orbit
  translationBound : Translation

structure FordAssemblyInput (Partition Sectors Margin : Prop) : Prop where
  completeCellPartition : Partition
  allAnalyticSectors : Sectors
  strictMargin : Margin

theorem useCollarEstimate {Collar Shifted Ford : Prop}
    (h : HalfSieveAnalyticInput Collar Shifted Ford) : Collar := h.collarEstimate

theorem useVStar {E B P : Prop} (h : VStarInput E B P) : P := h.propagatedBound

theorem useT0Star {R S F C L X P : Prop} (h : T0StarInput R S F C L X P) : P :=
  h.propagatedP3Bound

theorem useShiftedOrbit {C O T : Prop} (h : ShiftedOrbitInput C O T) : T := h.translationBound

theorem conditionalHalfSieveAssembly {Collar Shifted Ford Conclusion : Prop}
    (h : HalfSieveAnalyticInput Collar Shifted Ford)
    (assemble : Collar → Shifted → Ford → Conclusion) : Conclusion :=
  assemble h.collarEstimate h.shiftedParityEstimate h.fordGeometryMargin

end HalfSieve
