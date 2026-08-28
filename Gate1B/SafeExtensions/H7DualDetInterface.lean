/-
# Gate 1B v8.4 — H7 dual-determinant analytic interface

**COMMENTS ONLY.  ZERO DECLARATIONS.**  Status: ANALYTIC_INTERFACE_ONLY
(uninhabited).

The analytic estimate

    `D₇(C)  ≪_A  Y⁹ log^{-A} X`

is **not** declared, **not** axiomatised and **not** used anywhere in this bank.
This file records its exact source and status only.

EXACT SOURCE OF THE COORDINATES.

* seven centered defect coordinates `δ₁, …, δ₇`;
* one model coordinate;
* the dual `n`-coordinate produced by the hybrid `h`-Poisson transform
  (`Gate1B/SafeExtensions/HybridHPoisson.lean`, conditional);
* the determinant `n N - p d ℓ = 2`
  (`Gate1B/SafeAlgebra/H7DualDeterminant.lean`, proved).

CURRENT STATUS.

* fixed-power wall: REMOVED at natural scale — the capacity exponent is `0`
  (`Gate1B/SafeAlgebra/H7DualDetCapacity.lean`, CAPACITY_ONLY);
* arbitrary-log cancellation: OPEN — no mechanism for it is formalised, and the
  firewall `Gate1B/SafeExtensions/H7LogClosureFirewall.lean` forbids inferring
  it from the capacity statement;
* the full-divisor projector child reconstructs the H7 determinant geometry
  (`Gate1B/SafeAlgebra/H7SelfDuality.lean`), which is an anti-loop certificate:
  it shows the route returns to the same shape, so no analytic gain may be
  claimed from the reassociation.

LABEL: `H7-DUALDET-ONEDEFECT45`.
-/
import Mathlib
