import RequestProject.Options
namespace TwinPrimeProject.NANC

structure FCPTAssembly
    (TypeI TypeII VStar T0Star ROW SameR CDV Census69 CensusR2R3 CensusR9 FinalMargin FCPT : Prop) where
  assemble : TypeI → TypeII → VStar → T0Star → ROW → SameR → CDV →
    Census69 → CensusR2R3 → CensusR9 → FinalMargin → FCPT

theorem fcpt_from_all_dependencies
    {TypeI TypeII VStar T0Star ROW SameR CDV Census69 CensusR2R3 CensusR9 FinalMargin FCPT : Prop}
    (H : FCPTAssembly TypeI TypeII VStar T0Star ROW SameR CDV Census69 CensusR2R3 CensusR9 FinalMargin FCPT)
    (h1 : TypeI) (h2 : TypeII) (hv : VStar) (ht : T0Star) (hr : ROW) (hs : SameR)
    (hc : CDV) (h69 : Census69) (h23 : CensusR2R3) (h9 : CensusR9) (hm : FinalMargin) : FCPT :=
  H.assemble h1 h2 hv ht hr hs hc h69 h23 h9 hm

structure OpenFCPTGates where
  reciprocalConcentrationROW : Prop
  cdvMixedCovariance : Prop
  direct69PatternCensus : Prop
  r2r3AtomCensus : Prop
  fullR9Census : Prop
  fordTypeII : Prop
  finalMarginPositive : Prop
end TwinPrimeProject.NANC
