import RequestProject.Options
namespace TwinPrimeProject.NANC
structure VStarAssembly (ZeroFrequencyReassembly LargeSieveBound VStarConclusion : Prop) where
  assemble : ZeroFrequencyReassembly → LargeSieveBound → VStarConclusion

theorem vstar_closed_from_interface {Z L V : Prop} (H : VStarAssembly Z L V)
    (hz : Z) (hl : L) : V := H.assemble hz hl
end TwinPrimeProject.NANC
