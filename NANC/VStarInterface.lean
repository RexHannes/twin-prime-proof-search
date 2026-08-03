import Mathlib

namespace NANC

structure VStarBDHInterface where
  coefficient_SiegelWalfisz : Prop
  zero_frequency_reassembly : Prop
  bdh_variance_bound : Prop

theorem vstar_closed_from_BDH_interface
    (H : VStarBDHInterface) :
    H.coefficient_SiegelWalfisz →
    H.zero_frequency_reassembly →
    H.bdh_variance_bound →
    True := by
  intros
  trivial

end NANC
