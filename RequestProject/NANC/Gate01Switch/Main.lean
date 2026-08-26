import RequestProject.NANC.Gate01Switch.ResidueMinusTwo
import RequestProject.NANC.Gate01Switch.Lambda3
import RequestProject.NANC.Gate01Switch.SwitchedOperator
import RequestProject.NANC.Gate01Switch.DivisorPairs
import RequestProject.NANC.Gate01Switch.PrimePowerStructure
import RequestProject.NANC.Gate01Switch.RepeatedPrime
import RequestProject.NANC.Gate01Switch.GenericSwitched
import RequestProject.NANC.Gate01Switch.ExponentGeometry
import RequestProject.NANC.Gate01Switch.FixedCellConvolution
import RequestProject.NANC.Gate01Switch.Q5Equation
import RequestProject.NANC.Gate01Switch.WellFactorable
import RequestProject.NANC.Gate01Switch.VaughanSwitchIdentity
import RequestProject.NANC.Gate01Switch.AnalyticInterfaces
import RequestProject.NANC.Gate01Switch.Ledger

/-!
# Gate01Switch: aggregator

The switched high-`P₃` finite bank, incremental on top of the direct/root bank
in `RequestProject/NANC/Gate01Root/`.  The two banks are kept strictly
separate: no direct and switched analytic operator is ever merged.

Everything proved here is finite algebra: residue sets, divisor reindexings,
prime-power and repeated-prime splits, the Q5 support equation, a local
well-factorability obstruction, and rational exponent geometry.  The analytic
statements (`PrimePowerSparseBound`, `RepeatedPrimeSparseBound`,
`Q5ShiftedProductAnalyticStatement`, the two dictionaries,
`Gate0SwitchedCoverageStatement`, `Gate1BSwitchedAnalyticStatement`,
`Gate0ExhaustiveOperatorCoverageStatement`) exist only as definitions of
hypotheses and are never inhabited.

No claim of Gate 0–4 closure, Type II, FCPT, Hardy–Littlewood or twin primes is
made anywhere.
-/
