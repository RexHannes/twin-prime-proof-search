/-
# Gate1B / R11 / Frontier / CanonicalRootSync : the Pascadi 4/7 capacity firewall  (P5)

Append-only module.  **Exact rational linear arithmetic only.**  No source theorem is used and
none is inhabited: the firewall is a statement about the *capacity* of the three-atom Pascadi
exponent architecture, i.e. about what its three exponent inequalities can possibly imply.

Design (deliberately explicit, so that nothing is smuggled in):

* §1 a Pascadi condition set is **declared data**: three linear rows in the three atom exponents
  together with right-hand sides of the form `const − slack · ε_P`.  The literal condition set
  used by the current architecture is recorded as `pascadiLiteral`; it is *declared*, not
  derived, and it is the only place in this development where those numbers occur;
* §2 a **dual certificate** (nonnegative multipliers) and the general theorem that a certificate
  forces a ceiling on `θ = η + a + b`.  This is ordinary LP duality, kernel-proved;
* §3 the literal certificate for `pascadiLiteral`, hence the **firewall**

  ```
  PascadiCallable ⟹ θ = η + a + b ≤ 4/7 − 6 ε_P ,
  ```

  proved for **all six permutations** of the three atoms (callability is by definition the
  disjunction over the six orderings);
* §4 the consequence: no packet with `θ > 4/7` is Pascadi-callable — the same three-atom
  architecture cannot cross the physical `4/7` ceiling.
-/
import Gate1B.R11.Frontier.CanonicalRootSync.KFiveAlgebra

namespace Gate1B.R11.Frontier.CanonicalRootSync

open Finset

/-! ## 1. Pascadi condition sets as declared data -/

/-- A three-atom Pascadi exponent condition set: three linear rows in `(x, y, z)` with
right-hand sides `const − slack · ε_P`.  This is *data*, not a theorem. -/
structure PascadiConditions where
  /-- the coefficient of the first slot in each row -/
  cx : Fin 3 → ℚ
  /-- the coefficient of the second slot in each row -/
  cy : Fin 3 → ℚ
  /-- the coefficient of the third slot in each row -/
  cz : Fin 3 → ℚ
  /-- the constant part of each right-hand side -/
  rhsConst : Fin 3 → ℚ
  /-- the `ε_P`-slack of each right-hand side -/
  rhsSlack : Fin 3 → ℚ

/-- The three inequalities of a condition set, evaluated at an ordered atom triple. -/
def PascadiConditions.holdsAt (D : PascadiConditions) (epsP x y z : ℚ) : Prop :=
  ∀ i : Fin 3, D.cx i * x + D.cy i * y + D.cz i * z ≤ D.rhsConst i - D.rhsSlack i * epsP

/-- **The literal three-atom Pascadi condition set of the current architecture.**  Declared data,
written for an ordered atom triple `(x, y, z)` (the first slot is the one carrying the block):

```
row 1 (first condition)     2x + y + z ≤ 6/7 − 6 ε_P
row 2 (capacity condition)       y + z ≤ 2/7 − 6 ε_P
row 3 (sparse support)       x        ≤ 1/2 −   ε_P
```

Only rows 1–2 are used by the firewall certificate; row 3 is part of callability and is recorded
so that the predicate is the literal one.  The numbers are *declared* here — they are the only
place in this development where the Pascadi architecture's constants occur — and they are
calibrated by `pascadi_ceiling_sharp` below: the ceiling `4/7` is attained exactly at the
maximal physical packet `η = 2/7`, `a = b = 1/7`. -/
def pascadiLiteral : PascadiConditions where
  cx := ![2, 0, 1]
  cy := ![1, 1, 0]
  cz := ![1, 1, 0]
  rhsConst := ![6/7, 2/7, 1/2]
  rhsSlack := ![6, 6, 1]

/-! ## 2. Dual certificates and the general ceiling theorem -/

/-- A **dual certificate** that a condition set forces the ceiling `θ ≤ ceilConst − ceilSlack ε_P`
on nonnegative atom triples: nonnegative multipliers whose combination dominates `x + y + z`
and whose right-hand side is at most the claimed ceiling. -/
structure CeilingCertificate (D : PascadiConditions) (ceilConst ceilSlack : ℚ) where
  /-- the nonnegative multipliers -/
  lam : Fin 3 → ℚ
  /-- nonnegativity -/
  lam_nonneg : ∀ i, 0 ≤ lam i
  /-- the combination dominates the first slot -/
  dom_x : 1 ≤ ∑ i, lam i * D.cx i
  /-- the combination dominates the second slot -/
  dom_y : 1 ≤ ∑ i, lam i * D.cy i
  /-- the combination dominates the third slot -/
  dom_z : 1 ≤ ∑ i, lam i * D.cz i
  /-- the constant part of the combined right-hand side -/
  rhs_const : ∑ i, lam i * D.rhsConst i ≤ ceilConst
  /-- the slack part of the combined right-hand side -/
  rhs_slack : ceilSlack ≤ ∑ i, lam i * D.rhsSlack i

/-- **General ceiling theorem (LP duality).**  If a condition set admits a dual certificate then
every nonnegative atom triple satisfying the conditions obeys the certified ceiling. -/
theorem theta_le_of_certificate {D : PascadiConditions} {ceilConst ceilSlack : ℚ}
    (cert : CeilingCertificate D ceilConst ceilSlack) {epsP x y z : ℚ}
    (heps : 0 ≤ epsP) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : D.holdsAt epsP x y z) :
    x + y + z ≤ ceilConst - ceilSlack * epsP := by
  have key : ∀ i : Fin 3,
      cert.lam i * (D.cx i * x + D.cy i * y + D.cz i * z)
        ≤ cert.lam i * (D.rhsConst i - D.rhsSlack i * epsP) := fun i =>
    mul_le_mul_of_nonneg_left (h i) (cert.lam_nonneg i)
  have hsum :
      ∑ i, cert.lam i * (D.cx i * x + D.cy i * y + D.cz i * z)
        ≤ ∑ i, cert.lam i * (D.rhsConst i - D.rhsSlack i * epsP) :=
    Finset.sum_le_sum fun i _ => key i
  have hL :
      ∑ i, cert.lam i * (D.cx i * x + D.cy i * y + D.cz i * z)
        = (∑ i, cert.lam i * D.cx i) * x + (∑ i, cert.lam i * D.cy i) * y
          + (∑ i, cert.lam i * D.cz i) * z := by
    simp [Fin.sum_univ_three]; ring
  have hR :
      ∑ i, cert.lam i * (D.rhsConst i - D.rhsSlack i * epsP)
        = (∑ i, cert.lam i * D.rhsConst i) - (∑ i, cert.lam i * D.rhsSlack i) * epsP := by
    simp [Fin.sum_univ_three]; ring
  rw [hL, hR] at hsum
  have h1 : x ≤ (∑ i, cert.lam i * D.cx i) * x := by nlinarith [cert.dom_x]
  have h2 : y ≤ (∑ i, cert.lam i * D.cy i) * y := by nlinarith [cert.dom_y]
  have h3 : z ≤ (∑ i, cert.lam i * D.cz i) * z := by nlinarith [cert.dom_z]
  have h4 : (∑ i, cert.lam i * D.rhsSlack i) * epsP ≥ ceilSlack * epsP := by
    nlinarith [cert.rhs_slack]
  linarith [cert.rhs_const]

/-! ## 3. The literal certificate and the firewall -/

/-- The dual certificate for the literal condition set: the multipliers `(1/2, 1/2, 0)` give
exactly the ceiling `4/7 − 6 ε_P`. -/
def pascadiLiteralCertificate : CeilingCertificate pascadiLiteral (4/7) 6 where
  lam := ![1/2, 1/2, 0]
  lam_nonneg := by intro i; fin_cases i <;> norm_num
  dom_x := by norm_num [pascadiLiteral, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  dom_y := by norm_num [pascadiLiteral, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  dom_z := by norm_num [pascadiLiteral, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  rhs_const := by norm_num [pascadiLiteral, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]
  rhs_slack := by norm_num [pascadiLiteral, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- **Pascadi callability**: the literal three conditions hold for *some* assignment of the three
atoms `(η, a, b)` to the three slots — i.e. the disjunction over all six permutations. -/
def PascadiCallable (epsP : ℚ) (p : K5Packet) : Prop :=
  pascadiLiteral.holdsAt epsP p.eta p.a p.b ∨ pascadiLiteral.holdsAt epsP p.eta p.b p.a ∨
  pascadiLiteral.holdsAt epsP p.a p.eta p.b ∨ pascadiLiteral.holdsAt epsP p.a p.b p.eta ∨
  pascadiLiteral.holdsAt epsP p.b p.eta p.a ∨ pascadiLiteral.holdsAt epsP p.b p.a p.eta

/-- **The Pascadi 4/7 capacity firewall.**  For a physical packet and nonnegative slack,
callability in *any* of the six permutations forces `θ = η + a + b ≤ 4/7 − 6 ε_P`.
The same three-atom architecture therefore cannot cross the physical `4/7` ceiling. -/
theorem pascadi_capacity_firewall {epsP : ℚ} {p : K5Packet}
    (heps : 0 ≤ epsP) (hp : PhysicalK5 p) (hcall : PascadiCallable epsP p) :
    p.theta ≤ 4/7 - 6 * epsP := by
  obtain ⟨he, -, ha, hb, -, -⟩ := hp
  have base : ∀ x y z : ℚ, 0 ≤ x → 0 ≤ y → 0 ≤ z → pascadiLiteral.holdsAt epsP x y z →
      x + y + z ≤ 4/7 - 6 * epsP := fun x y z hx hy hz h =>
    theta_le_of_certificate pascadiLiteralCertificate heps hx hy hz h
  unfold K5Packet.theta
  rcases hcall with h | h | h | h | h | h
  · linarith [base _ _ _ he ha hb h]
  · linarith [base _ _ _ he hb ha h]
  · linarith [base _ _ _ ha he hb h]
  · linarith [base _ _ _ ha hb he h]
  · linarith [base _ _ _ hb he ha h]
  · linarith [base _ _ _ hb ha he h]

/-! ## 4. The contrapositive: the ceiling as an exclusion principle -/

/-- **Above the ceiling, Pascadi is not callable.**  A physical packet with `θ > 4/7 − 6 ε_P`
fails every one of the six permutations of the literal conditions. -/
theorem not_pascadiCallable_of_theta_large {epsP : ℚ} {p : K5Packet}
    (heps : 0 ≤ epsP) (hp : PhysicalK5 p) (hth : 4/7 - 6 * epsP < p.theta) :
    ¬ PascadiCallable epsP p := fun hcall => by
  linarith [pascadi_capacity_firewall heps hp hcall]

/-- **The literal condition set is not vacuous.**  A small physical packet is Pascadi-callable,
so the firewall is a genuine capacity statement about a satisfiable condition set, not an empty
implication. -/
theorem pascadiCallable_nonvacuous :
    PhysicalK5 ⟨1/10, 1/10, 1/10⟩ ∧ PascadiCallable (1/100) ⟨1/10, 1/10, 1/10⟩ := by
  refine ⟨by norm_num [PhysicalK5], Or.inl ?_⟩
  intro i
  fin_cases i <;> norm_num [pascadiLiteral]

/-- **The `4/7` ceiling is sharp for the literal architecture.**  The maximal physical packet
`η = 2/7`, `a = b = 1/7` is physical, is Pascadi-callable at zero slack, and has `θ = 4/7`
exactly: the firewall constant is calibrated, not padded. -/
theorem pascadi_ceiling_sharp :
    PhysicalK5 ⟨2/7, 1/7, 1/7⟩ ∧ PascadiCallable 0 ⟨2/7, 1/7, 1/7⟩
      ∧ (K5Packet.theta ⟨2/7, 1/7, 1/7⟩) = 4/7 := by
  refine ⟨by norm_num [PhysicalK5], Or.inl ?_, by norm_num [K5Packet.theta]⟩
  intro i
  fin_cases i <;> norm_num [pascadiLiteral]

/-- The firewall bites strictly inside the physical range: the physical ceiling `697/1000`
computed in `KFiveAlgebra` is strictly above `4/7`, so physical packets above the Pascadi
capacity exist as a matter of exponent geometry. -/
theorem pascadi_ceiling_below_physical_ceiling : (4 : ℚ)/7 < 697/1000 := by norm_num

end Gate1B.R11.Frontier.CanonicalRootSync
