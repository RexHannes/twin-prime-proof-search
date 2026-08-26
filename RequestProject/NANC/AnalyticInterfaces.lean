import RequestProject.Options
namespace TwinPrimeProject.NANC

structure ResidueAwareFordTypeIInput where
  statement : Prop
  proof : statement
structure DivisorWeightedMaximalBVInput where
  statement : Prop
  proof : statement
structure IntervalUniformResidueSieveInput where
  statement : Prop
  proof : statement
structure TypeILargePrimeTailInput where
  statement : Prop
  proof : statement
structure TypeIEvenModulusBranchInput where
  statement : Prop
  proof : statement

theorem useResidueAwareFordTypeI (H : ResidueAwareFordTypeIInput) : H.statement := H.proof
theorem useDivisorWeightedMaximalBV (H : DivisorWeightedMaximalBVInput) : H.statement := H.proof
theorem useIntervalUniformResidueSieve (H : IntervalUniformResidueSieveInput) : H.statement := H.proof
theorem useTypeILargePrimeTail (H : TypeILargePrimeTailInput) : H.statement := H.proof
theorem useTypeIEvenModulusBranch (H : TypeIEvenModulusBranchInput) : H.statement := H.proof

structure ConditionalAssembly (InputA InputB Conclusion : Prop) where
  assemble : InputA → InputB → Conclusion

theorem useConditionalAssembly {A B C : Prop} (H : ConditionalAssembly A B C)
    (ha : A) (hb : B) : C := H.assemble ha hb
end TwinPrimeProject.NANC
