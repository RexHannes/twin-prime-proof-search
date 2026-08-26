/-
# NANC Gate 1A v9.3/v9.4 — band-limited prime participation: the finite layer

**Circularity repair.**  The BPP mechanism must *not* start from
`A_X = sup over prime rows of a(r,X)` and then assume that the continuous
maximum is comparable to it.  Here the order is reversed:

* a `ParticipationEnvelope` carries a **continuous-envelope magnitude**
  `Menv X` with an unconditional upper bound `|c r X| ≤ Menv X` (all rows) and a
  **plateau** certificate: a finite set of rows on which
  `c0 * Menv X ≤ |c r X|`;
* from these the *discrete* participation inequality

      P * A_X ≤ ∑_r |c r X|,      P = c0 * (plateau card),

  is **derived** (`ParticipationEnvelope.participation_of_plateau`), for **any**
  `A_X` dominated by `Menv X` — in particular for the prime supremum, which is
  therefore obtained afterwards, not assumed.

`PrimeParticipationCertificate` is the analytic interface: it carries the
participation lower bound as a *field*.  Nothing here proves a prime-counting
statement; the intended analytic route (uniform smoothness → degree `R^{1/4}`
Fourier truncation → Bernstein plateau of `r`-length `R^{3/4}` → short-interval
prime asymptotics → `P = R^{3/4-o(1)}`) is documentation only and appears in no
theorem statement.
-/
import Mathlib

namespace TwinPrimeProject.NANC.Gate1A.V94

open Finset

variable {Row State : Type*} [Fintype Row] [Fintype State] [DecidableEq Row]

/-- **Continuous-envelope participation data.**  `Menv` is the (continuous)
envelope magnitude, `plateau X` a finite set of rows on which the amplitude is
at least `c0` times the envelope. -/
structure ParticipationEnvelope (Row State : Type*) [Fintype Row] [Fintype State] where
  /-- The row amplitude. -/
  c : Row → State → ℝ
  /-- The continuous-envelope magnitude. -/
  Menv : State → ℝ
  /-- Envelope nonnegativity. -/
  Menv_nonneg : ∀ X, 0 ≤ Menv X
  /-- Unconditional envelope upper bound (all rows). -/
  upper : ∀ r X, |c r X| ≤ Menv X
  /-- The plateau constant. -/
  c0 : ℝ
  /-- Plateau constant positivity. -/
  c0_pos : 0 < c0
  /-- The plateau rows. -/
  plateau : State → Finset Row
  /-- The plateau lower bound. -/
  plateau_lower : ∀ X, ∀ r ∈ plateau X, c0 * Menv X ≤ |c r X|

namespace ParticipationEnvelope

variable (E : ParticipationEnvelope Row State)

/-- **Derived discrete participation.**  For any candidate magnitude `A X`
dominated by the continuous envelope, the `ℓ¹` row mass dominates
`c0 · (plateau card) · A X`.  The prime supremum is obtained *afterwards* by
taking `A X = sup over prime rows`, which is dominated by `Menv X` by
`E.upper`. -/
theorem participation_of_plateau (A : State → ℝ) (hA : ∀ X, A X ≤ E.Menv X)
    (hA0 : ∀ X, 0 ≤ A X) (X : State) :
    (E.c0 * ((E.plateau X).card : ℝ)) * A X ≤ ∑ r, |E.c r X| := by
  have hplateau : (E.c0 * ((E.plateau X).card : ℝ)) * A X
      ≤ ∑ r ∈ E.plateau X, |E.c r X| := by
    have hterm : ∀ r ∈ E.plateau X, E.c0 * A X ≤ |E.c r X| := by
      intro r hr
      exact le_trans (mul_le_mul_of_nonneg_left (hA X) (le_of_lt E.c0_pos))
        (E.plateau_lower X r hr)
    calc (E.c0 * ((E.plateau X).card : ℝ)) * A X
        = ∑ _r ∈ E.plateau X, E.c0 * A X := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ r ∈ E.plateau X, |E.c r X| := Finset.sum_le_sum hterm
  refine hplateau.trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) ?_)
  intro r _ _
  exact abs_nonneg _

/-- The prime supremum is dominated by the continuous envelope: this is the
*consequence*, never the hypothesis. -/
theorem sup_le_envelope (S : Finset Row) (hS : S.Nonempty) (X : State) :
    S.sup' hS (fun r => |E.c r X|) ≤ E.Menv X :=
  Finset.sup'_le hS _ fun r _ => E.upper r X

end ParticipationEnvelope

/-- **Analytic interface.**  The band-limited prime-participation certificate:
the participation lower bound `P ≤ participation X` for active states is a
*field*, to be supplied externally.  No prime-counting theorem is proved or
assumed anywhere in this repository. -/
structure PrimeParticipationCertificate (Row State : Type*) [Fintype Row] [Fintype State] where
  /-- The active states. -/
  Active : State → Prop
  /-- The (integer) participation count. -/
  participation : State → ℕ
  /-- The abstract participation parameter. -/
  P : ℝ
  /-- Positivity of the parameter. -/
  P_pos : 0 < P
  /-- The participation lower bound on active states. -/
  active_participation : ∀ X, Active X → P ≤ (participation X : ℝ)
  /-- The row amplitude. -/
  a : Row → State → ℝ
  /-- Amplitude nonnegativity. -/
  a_nonneg : ∀ r X, 0 ≤ a r X
  /-- The candidate magnitude. -/
  A : State → ℝ
  /-- Magnitude nonnegativity. -/
  A_nonneg : ∀ X, 0 ≤ A X
  /-- The discrete participation inequality, in the form used by the finite
  compiler. -/
  participation_mass : ∀ X, P * A X ≤ ∑ r, a r X

end TwinPrimeProject.NANC.Gate1A.V94
