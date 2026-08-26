/-
# Universal safe algebra — anti-free-gain counterexamples (re-export)

Proved in `UniversalV8/Countermodels.lean`.  The Gate1B anti-Cartesian counterexample is
NOT duplicated here; it remains `Gate1B.shell_sum_ne_cartesian_sum` in the existing bank.
-/
import UniversalV8.Countermodels

namespace Universal.SafeAlgebra

export UniversalV8 (identical_packets_have_family_congestion identical_packets_gap
  signs_do_not_force_cancellation signed_family_can_attain_maximum)

end Universal.SafeAlgebra
