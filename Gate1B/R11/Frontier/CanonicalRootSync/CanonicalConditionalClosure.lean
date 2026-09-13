/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the conditional closure theorem  (P10)

Append-only module.  This is the strongest **purely formal** conditional theorem available after
the canonical-root reconciliation.  Its hypotheses are of exactly two kinds and are kept apart:

* **exact bridges** (identities, each one either proved elsewhere in this layer or supplied as an
  explicit pointwise identity of the chart): the canonical root identity, the K = 5 rank
  decomposition of the root, and the centered/principal split of the `j = 2` branch;
* **analytic interfaces** (never inhabited, no axiom): the canonical root error budget, the four
  non-`j=2` branch budgets, the exact-principal budget, and the single surviving `j = 2` owner
  `J2ResidualCenteredBound`.

The conclusion is the R11 scalar target.  **No hypothesis of this theorem is inhabited anywhere
in the repository**, and the theorem is stated so that the true current analytic cut is visible
in its binder list.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.J2ResidualOperator

namespace Gate1B.R11.Frontier.CanonicalRootSync

/-- **The R11 scalar target**: the canonical root family obeys the `x L^{−S₀}` budget. -/
def R11ScalarTarget (Root : ℝ → ℝ) (S0 : ℕ) : Prop := ScalarBudget Root S0

/-- **The canonical-route closure theorem.**

If

* `F = Root + Err`                              (canonical root identity, exact);
* `Root = B₁ + B₂ + B₃ + B₄ + B₅`               (K = 5 rank decomposition, exact);
* `B₂ = Cen + Prin`                             (centered/principal split of `j = 2`, exact);
* `Err`, `B₁`, `B₃`, `B₄`, `B₅` and `Prin` obey their budgets    (analytic interfaces);
* `Cen` obeys `J2ResidualCenteredBound`         (the single surviving `j = 2` analytic owner);

then the R11 scalar target holds for `F`.

None of the analytic hypotheses is inhabited. -/
theorem r11_of_canonical_route
    {F Root Err B1 B2 B3 B4 B5 Cen Prin : ℝ → ℝ} {S0 : ℕ}
    (hroot : ∀ x, F x = Root x + Err x)
    (hdecomp : ∀ x, Root x = B1 x + B2 x + B3 x + B4 x + B5 x)
    (hj2 : ∀ x, B2 x = Cen x + Prin x)
    (hErr : CanonicalRootErrorBudget Err S0)
    (hB1 : ScalarBudget B1 (S0 + 2)) (hB3 : ScalarBudget B3 (S0 + 2))
    (hB4 : ScalarBudget B4 (S0 + 2)) (hB5 : ScalarBudget B5 (S0 + 2))
    (hPrin : ScalarBudget Prin (S0 + 2))
    (hCen : J2ResidualCenteredBound Cen S0) :
    R11ScalarTarget F S0 := by
  have hB2 : ScalarBudget B2 (S0 + 2) :=
    scalarBudget_congr hj2 (scalarBudget_add hCen hPrin)
  have hRoot : ScalarBudget Root (S0 + 2) := by
    refine scalarBudget_congr hdecomp ?_
    exact scalarBudget_add (scalarBudget_add (scalarBudget_add (scalarBudget_add hB1 hB2) hB3) hB4)
      hB5
  have hRoot' : ScalarBudget Root S0 := scalarBudget_mono (by omega) hRoot
  exact scalarBudget_of_parts hroot hRoot' hErr

/-- **The route is not vacuous**: its exact bridges are simultaneously satisfiable (they are
identities, satisfied by the tautological chart), so the theorem is not an empty implication.
Only the analytic hypotheses are open. -/
theorem canonical_route_bridges_satisfiable :
    ∃ (F Root Err B1 B2 B3 B4 B5 Cen Prin : ℝ → ℝ),
      (∀ x, F x = Root x + Err x) ∧ (∀ x, Root x = B1 x + B2 x + B3 x + B4 x + B5 x)
        ∧ (∀ x, B2 x = Cen x + Prin x) := by
  refine ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0,
    fun _ => 0, fun _ => 0, fun _ => 0, fun _ => by ring, fun _ => by ring, fun _ => by ring⟩

/-- **The analytic cut is genuinely load-bearing.**  Dropping the `j = 2` owner is not possible:
there are charts satisfying every exact bridge and every other analytic hypothesis for which the
target fails.  (Take every branch, the principal part and the error zero except the `j = 2`
centered part, which is `x`; the remaining hypotheses hold trivially, the target does not.)
Here `S₀ = 1`. -/
theorem j2_owner_is_load_bearing :
    ∃ (F Root Err B1 B2 B3 B4 B5 Cen Prin : ℝ → ℝ),
      (∀ x, F x = Root x + Err x) ∧ (∀ x, Root x = B1 x + B2 x + B3 x + B4 x + B5 x)
        ∧ (∀ x, B2 x = Cen x + Prin x)
        ∧ CanonicalRootErrorBudget Err 1
        ∧ ScalarBudget B1 3 ∧ ScalarBudget B3 3 ∧ ScalarBudget B4 3 ∧ ScalarBudget B5 3
        ∧ ScalarBudget Prin 3
        ∧ ¬ J2ResidualCenteredBound Cen 1
        ∧ ¬ R11ScalarTarget F 1 :=
  ⟨fun x => x, fun x => x, fun _ => 0, fun _ => 0, fun x => x, fun _ => 0, fun _ => 0,
    fun _ => 0, fun x => x, fun _ => 0, fun _ => by ring, fun _ => by ring, fun _ => by ring,
    zero_budgeted 3, zero_budgeted 3, zero_budgeted 3, zero_budgeted 3, zero_budgeted 3,
    zero_budgeted 3, identity_not_budgeted 2, identity_not_budgeted 0⟩

end Gate1B.R11.Frontier.CanonicalRootSync
