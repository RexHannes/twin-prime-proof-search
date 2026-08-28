import Mathlib.Tactic
import RequestProject.FixedCertificateAlgebra

/-!
# Phase G2 / G3 · R9 leakage direction and `P_ε` finite arithmetic

## G2 — corrected R9 interpretation (direction of the membership statement)

The *false* "R9 death certificate" is **not** resurrected.  The corrected
reading recorded here is:

* `R(P)` consists of vectors with **no proper subsum in the Type-II window**;
* a balanced R9 coordinate `1/9` lies in that window;
* therefore the balanced R9 vector is **not** in `R(P)`;
* hence it is **outside** `C(R(P))`;
* that is precisely **leakage**, not disqualification from leakage.

The exact definitions of `R(P)`, `C(R(P))` and the leakage set are **absent
from the repository** (searched: `RealFordGrammarCertificate`, `Proposition
7.22`, `(7.23)`, `C(R)`, `R(P)`, `G(d;n)`).  Consequently the membership
statement is *not* formalised as a theorem about the physical Ford objects.
Instead `R9LeakageDirection` below is a **source-pending dictionary**: an
abstract statement of the corrected direction, parameterised by whatever the
literal source objects turn out to be.  It has no inhabitant here.

Status:
* `R9-LEAKAGE-MEMBERSHIP` : SOURCE_OPEN, direction corrected;
* `R9-GDN-SPECIALIZATION` : SOURCE_OPEN (`G(d;n)` absent — promotion stopped).

## G3 — the finite arithmetic, which *is* source-independent

With `ν = 1/6`, `ε ≤ 1/600`, `η < 1/90`:

* `r9_coordinate_not_tiny`   : `1/9 - η > ε`;
* `r9_coordinate_not_large`  : `1/9 + η < 1/2 - ε`;
* `r9_four_below_cut`        : `4(1/9 + η) < 1/2 - ε`;
* `r9_five_above_cut`        : `5(1/9 - η) > 1/2 - ε`;
* `r9_H_value_seventy`       : `∑_{j=0}^{4} (-1)^j C(9,j) = 70`, *reusing* the
  banked `k0EqualFactorR9Value70` rather than re-proving it.

The number `70` is **not** identified with a physical Ford coefficient: that
identification needs the literal `G(d;n)` specialisation, which is absent.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace R9

/-! ## 1. Parameter constraints -/

/-- The `P_ε` / R9 parameter window.  All bounds are exact rationals. -/
structure Params where
  /-- The `ε` of `P_ε`. -/
  eps : ℚ
  /-- The coordinate perturbation `η`. -/
  eta : ℚ
  eps_pos : 0 < eps
  eta_pos : 0 < eta
  eps_le : eps ≤ 1 / 600
  eta_lt : eta < 1 / 90

/-- `ν = 1/6` is the fixed sieve parameter of the route. -/
def nu : ℚ := 1 / 6

theorem nu_value : nu = 1 / 6 := rfl

/-! ## 2. The separation facts -/

variable (P : Params)

/-- **G3.**  An R9 coordinate `1/9 - η` is **not tiny**: it exceeds `ε`, so it
cannot be assembled out of the total tiny mass. -/
theorem r9_coordinate_not_tiny : P.eps < 1 / 9 - P.eta := by
  have h1 := P.eps_le
  have h2 := P.eta_lt
  linarith

/-- **G3.**  An R9 coordinate `1/9 + η` is **not large**: it is below the
`1/2 - ε` large-component threshold. -/
theorem r9_coordinate_not_large : 1 / 9 + P.eta < 1 / 2 - P.eps := by
  have h1 := P.eps_le
  have h2 := P.eta_lt
  linarith

/-- **G3, `H(n) = 70` cutoff arithmetic, lower side.**  Four R9 coordinates lie
strictly below the `1/2 - ε` cut. -/
theorem r9_four_below_cut : 4 * (1 / 9 + P.eta) < 1 / 2 - P.eps := by
  have h1 := P.eps_le
  have h2 := P.eta_lt
  linarith

/-- **G3, `H(n) = 70` cutoff arithmetic, upper side.**  Five R9 coordinates lie
strictly above the `1/2 - ε` cut. -/
theorem r9_five_above_cut : 1 / 2 - P.eps < 5 * (1 / 9 - P.eta) := by
  have h1 := P.eps_le
  have h2 := P.eta_lt
  have h3 := P.eps_pos
  linarith

/-- The window is nonempty: `ε = 1/600`, `η = 1/100` satisfies all constraints. -/
def sampleParams : Params where
  eps := 1 / 600
  eta := 1 / 100
  eps_pos := by norm_num
  eta_pos := by norm_num
  eps_le := by norm_num
  eta_lt := by norm_num

/-! ## 3. The alternating value `70` (reused, not re-proved) -/

/-- **G3.**  `∑_{j=0}^{4} (-1)^j C(9,j) = 70`.  Reuses the banked
`TwinPrimeProject.FixedCertificate.k0EqualFactorR9Value70`. -/
theorem r9_H_value_seventy :
    ∑ j ∈ Finset.range 5, (-1 : ℤ) ^ j * (Nat.choose 9 j) = 70 :=
  TwinPrimeProject.FixedCertificate.k0EqualFactorR9Value70

/-- **Firewall.**  The value `70` is a binomial alternating sum and nothing
more until the literal `G(d;n)` specialisation is supplied.  Recorded as a
theorem so that no module can quietly assert the identification: the alternating
sum for the *neighbouring* cutoff is a different number, so the value depends on
the cutoff convention and must be pinned by the source. -/
theorem seventy_depends_on_cutoff :
    ∑ j ∈ Finset.range 5, (-1 : ℤ) ^ j * (Nat.choose 9 j) = 70 ∧
      ∑ j ∈ Finset.range 4, (-1 : ℤ) ^ j * (Nat.choose 9 j) = -56 ∧
        (70 : ℤ) ≠ -56 := by
  refine ⟨r9_H_value_seventy, ?_, by norm_num⟩
  norm_num [Finset.sum_range_succ, Nat.choose]

/-! ## 4. Source-pending dictionary for the corrected leakage direction -/

/-- **SOURCE-PENDING DICTIONARY (G2).**  The corrected R9 leakage direction,
stated abstractly over whatever the literal Ford objects are:

* `inWindow` : the Type-II window predicate on coordinates;
* `RP`       : the set `R(P)` — vectors with no proper subsum in the window;
* `CRP`      : the cone/closure `C(R(P))`;
* `leakage`  : the leakage set.

The corrected claim is: a balanced R9 vector `v` whose coordinate `1/9` lies in
the window is **not** in `R(P)`, hence not in `C(R(P))`, hence **in** the
leakage set.

This structure is **UNINHABITED** in this repository: `R(P)`, `C(R(P))` and the
leakage set are not present, so no instance can be built without improvising
the source. -/
structure R9LeakageDirection (V : Type*) where
  /-- The Type-II window predicate on a coordinate. -/
  inWindow : ℚ → Prop
  /-- `R(P)`. -/
  RP : Set V
  /-- `C(R(P))`. -/
  CRP : Set V
  /-- The leakage set. -/
  leakage : Set V
  /-- The balanced R9 vector. -/
  balancedR9 : V
  /-- `1/9` lies in the Type-II window (this is the corrected input). -/
  ninth_in_window : inWindow (1 / 9)
  /-- Membership in `R(P)` forbids a coordinate in the window; the balanced R9
  vector has one, so it is outside `R(P)`. -/
  balanced_not_in_RP : balancedR9 ∉ RP
  /-- `C(R(P))` is generated by `R(P)`, so the balanced vector is outside it. -/
  balanced_not_in_CRP : balancedR9 ∉ CRP
  /-- Being outside `C(R(P))` is exactly leakage — **not** disqualification. -/
  outside_CRP_is_leakage : ∀ v : V, v ∉ CRP → v ∈ leakage

/-- **G2, deterministic compiler.**  From a supplied leakage dictionary, the
balanced R9 vector *is* a leakage packet.  The dictionary is not supplied. -/
theorem balancedR9_is_leakage {V : Type*} (d : R9LeakageDirection V) :
    d.balancedR9 ∈ d.leakage :=
  d.outside_CRP_is_leakage _ d.balanced_not_in_CRP

/-- **G2 firewall / anti-death-certificate.**  The *old* direction — "the
balanced R9 vector is outside `C(R(P))`, therefore it is disqualified from
leakage" — is refuted by the dictionary: outside `C(R(P))` implies leakage.
There is no dictionary in which both hold and the leakage set is where the
packet must go. -/
theorem r9_death_certificate_refuted {V : Type*} (d : R9LeakageDirection V) :
    ¬ (d.balancedR9 ∉ d.leakage) :=
  fun h => h (balancedR9_is_leakage d)

end R9
end CurrentProgramme
end TwinPrimeProject
