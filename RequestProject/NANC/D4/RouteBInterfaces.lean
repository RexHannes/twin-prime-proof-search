namespace NANC.D4

structure Prop44AnalyticInput where statement : Prop
structure MellinSeparationInput where
  smoothMellinInversion : Prop
  uniformProp44InFrequency : Prop
  truncationControl : Prop
structure PerronSeparationInput where
  sharpCutSeparation : Prop
  boundaryErrorControl : Prop
structure PrimeBoxSiegelWalfiszInput where statement : Prop
structure RouteBAnalyticApplication where statement : Prop

end NANC.D4
