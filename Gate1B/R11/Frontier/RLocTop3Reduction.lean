/-
# Gate1B / R11 / Frontier : the exact reduction of `R_loc-top,3` to a residue-variation input

Append-only module.  **Exact finite linear algebra only** — no analytic statement is proved and
no open proposition is inhabited.

The previous layer defined the current formal frontier object

```
R_loc-top,3  =  E_λ*( Q₃ W )  =  selectedConsumer λ Ds Ns ( tableSource K (Q₃ W) ) .
```

Everything in this module is aimed at one question: *what is the weakest exact theorem that
suffices for the physical `R_loc-top,3` bound?*  The answer proved here is a genuine reduction,
obtained **without taking absolute values before the exact cancellation is used**:

1. `RlocTop3_eq_pair_rowConsumer` — the residual is exactly the pairing of the residue-aware top
   `Q₃ W` against the *selected row consumer*
   `rowConsumer x = selectedConsumer λ Ds Ns (K x)`;
2. `resAvg_self_adjoint`, `subT_self_adjoint`, `Q3_self_adjoint` — the residue-aware averages are
   self-adjoint for the counting pairing, hence the top projection can be **moved off the source
   and onto the consumer**;
3. `RlocTop3_eq_pair_Q3_rowConsumer` — therefore

   ```
   R_loc-top,3  =  ⟨ W , Q₃ (rowConsumer) ⟩ ,
   ```

   an identity: no estimate has been used, and the raw (uncentered) source `W` now appears;
4. `Q3_of_residueDetermined` — `Q₃` annihilates every function of the residue vector alone.
   Consequently only the *deviation of the row consumer from a residue-determined profile* can
   contribute, and `RlocTop3_eq_zero_of_residueDetermined_rowConsumer` is an exact vanishing
   theorem for the residue-determined case;
5. `RLocTop3Bound_of_residue_approximation` — the **deterministic reduction**: an ℓ^∞ residue
   approximation of the row consumer with error `ε`, an ℓ¹ mass bound `Mw` for the *raw* source,
   and the arithmetic inequality `Mw · 2^r · ε ≤ C x L^{-S₀}` give `RLocTop3Bound`.

The remaining input is isolated as the never-inhabited interface `RowConsumerResidueProfile`
(§6): *the selected row consumer is uniformly approximable by a function of the residue vector.*
This is strictly narrower than an "all bounded sequences" hypothesis: it constrains only the
finitely many numbers `selectedConsumer λ Ds Ns (K x)`, `x` in the prime-coordinate table.
-/
import Gate1B.R11.Frontier.ResidueAwareTopTelescoping

namespace Gate1B.R11.Frontier

open Finset

namespace ResidueProj

/-! ## 1. Elementary linearity and size facts for the residue-aware averages -/

section Basic

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  {res : ∀ i, α i → ℕ}

omit [(i : ι) → Fintype (α i)] in
/-- An average of numbers bounded by `M` over a nonempty index set is bounded by `M`. -/
theorem abs_coordAvg_le {j : ι} {s : Finset (α j)} (hs : s.Nonempty) {W : (∀ i, α i) → ℚ}
    {M : ℚ} (hW : ∀ z, |W z| ≤ M) (x : ∀ i, α i) : |coordAvg j s W x| ≤ M := by
  have hcard : (0 : ℚ) < (s.card : ℚ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  unfold coordAvg
  rw [abs_div, abs_of_pos hcard, div_le_iff₀ hcard]
  calc |∑ y ∈ s, W (Function.update x j y)| ≤ ∑ y ∈ s, |W (Function.update x j y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _y ∈ s, M := Finset.sum_le_sum fun y _ => hW _
    _ = M * (s.card : ℚ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

theorem abs_resAvg_le {j : ι} {W : (∀ i, α i) → ℚ} {M : ℚ} (hW : ∀ z, |W z| ≤ M)
    (x : ∀ i, α i) : |resAvg res j W x| ≤ M :=
  abs_coordAvg_le (resFib_nonempty j x) hW x

/-- `subT` is linear on differences. -/
theorem subT_sub (j : ι) (W V : (∀ i, α i) → ℚ) :
    subT res j (fun z => W z - V z) = fun x => subT res j W x - subT res j V x := by
  funext x
  unfold subT
  rw [resAvg_sub]
  ring

@[simp] theorem subT_zero (j : ι) : subT res j (fun _ => (0 : ℚ)) = fun _ => (0 : ℚ) := by
  funext x
  simp [subT]

/-- `Q₃` is linear on differences. -/
theorem Q3_sub (l : List ι) (W V : (∀ i, α i) → ℚ) :
    Q3 res l (fun z => W z - V z) = fun x => Q3 res l W x - Q3 res l V x := by
  induction l generalizing W V with
  | nil => rfl
  | cons j l ih =>
      rw [Q3_cons, ih, subT_sub, Q3_cons, Q3_cons]

@[simp] theorem Q3_zero (l : List ι) : Q3 res l (fun _ => (0 : ℚ)) = fun _ => (0 : ℚ) := by
  induction l with
  | nil => rfl
  | cons j l ih => rw [Q3_cons, ih, subT_zero]

/-- Crude but exact size bound: the `r`-fold residue-aware difference of a function bounded by
`M` is bounded by `2^r M`. -/
theorem abs_Q3_le (l : List ι) {W : (∀ i, α i) → ℚ} {M : ℚ} (hM : 0 ≤ M)
    (hW : ∀ z, |W z| ≤ M) (x : ∀ i, α i) : |Q3 res l W x| ≤ 2 ^ l.length * M := by
  induction l generalizing W M x with
  | nil => simpa using hW x
  | cons j l ih =>
      have hstep : ∀ z, |Q3 res l W z| ≤ 2 ^ l.length * M := fun z => ih hM hW z
      rw [Q3_cons]
      unfold subT
      calc |Q3 res l W x - resAvg res j (Q3 res l W) x|
          ≤ |Q3 res l W x| + |resAvg res j (Q3 res l W) x| := by
            simpa [sub_eq_add_neg, abs_neg] using
              abs_add_le (Q3 res l W x) (-resAvg res j (Q3 res l W) x)
        _ ≤ 2 ^ l.length * M + 2 ^ l.length * M :=
            add_le_add (hstep x) (abs_resAvg_le hstep x)
        _ = 2 ^ (j :: l).length * M := by
            simp only [List.length_cons, pow_succ]
            ring

/-! ### Commutation of `(I − T_j)` with the top projection -/

/-- `(I − T_j)` and `(I − T_k)` commute for independent coordinates. -/
theorem subT_subT_comm {j k : ι} (hjk : j ≠ k) (W : (∀ i, α i) → ℚ) :
    subT res j (subT res k W) = subT res k (subT res j W) := by
  funext x
  unfold subT
  rw [resAvg_sub, resAvg_sub, resAvg_comm hjk]
  ring

/-- `(I − T_j)` commutes with the residue-aware top projection over a list avoiding `j`. -/
theorem Q3_subT_comm {j : ι} {l : List ι} (hj : j ∉ l) (W : (∀ i, α i) → ℚ) :
    Q3 res l (subT res j W) = subT res j (Q3 res l W) := by
  induction l generalizing W with
  | nil => rfl
  | cons k l ih =>
      have hk : j ≠ k := fun h => hj (by simp [h])
      have hl : j ∉ l := fun h => hj (by simp [h])
      calc Q3 res (k :: l) (subT res j W) = subT res k (Q3 res l (subT res j W)) := rfl
        _ = subT res k (subT res j (Q3 res l W)) := by rw [ih hl]
        _ = subT res j (subT res k (Q3 res l W)) := subT_subT_comm (Ne.symm hk) _
        _ = subT res j (Q3 res (k :: l) W) := rfl

end Basic

/-! ## 2. Self-adjointness of the residue-aware averages -/

section SelfAdjoint

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  {res : ∀ i, α i → ℕ}

/-- The counting pairing of two table functions. -/
def pairQ (W g : (∀ i, α i) → ℚ) : ℚ := ∑ x, W x * g x

theorem pairQ_sub_left (W V g : (∀ i, α i) → ℚ) :
    pairQ (fun x => W x - V x) g = pairQ W g - pairQ V g := by
  unfold pairQ
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem pairQ_sub_right (W g h : (∀ i, α i) → ℚ) :
    pairQ W (fun x => g x - h x) = pairQ W g - pairQ W h := by
  unfold pairQ
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The fibre-swap involution `(x, y) ↦ (x[j := y], x_j)` on pairs. -/
def swapUpd (j : ι) (p : (∀ i, α i) × α j) : (∀ i, α i) × α j :=
  (Function.update p.1 j p.2, p.1 j)

omit [Fintype ι] [(i : ι) → Fintype (α i)] in
theorem swapUpd_involutive (j : ι) : Function.Involutive (swapUpd (α := α) j) := by
  intro p
  simp [swapUpd, Function.update_idem]

omit [Fintype ι] in
/-- Fibrewise expansion of `T_j U · V` as a full sum over the second coordinate. -/
theorem sum_fib_left (j : ι) (U V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    ∑ y : α j, (if res j y = res j (x j) then
        U (Function.update x j y) * V x / ((resFib res j (res j (x j))).card : ℚ) else 0)
      = resAvg res j U x * V x := by
  classical
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun y : α j => res j y = res j (x j))
      = resFib res j (res j (x j)) := rfl
  rw [hfil]
  unfold resAvg coordAvg
  rw [← Finset.sum_div, ← Finset.sum_mul]
  ring

omit [Fintype ι] in
/-- Fibrewise expansion of `U · T_j V` as a full sum over the second coordinate. -/
theorem sum_fib_right (j : ι) (U V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    ∑ y : α j, (if res j y = res j (x j) then
        U x * V (Function.update x j y) / ((resFib res j (res j (x j))).card : ℚ) else 0)
      = U x * resAvg res j V x := by
  classical
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun y : α j => res j y = res j (x j))
      = resFib res j (res j (x j)) := rfl
  rw [hfil]
  unfold resAvg coordAvg
  rw [← Finset.sum_div, ← Finset.mul_sum]
  ring

/-- **`T_j` is self-adjoint** for the counting pairing.  This is the exact statement that lets
the residue-aware top projection be moved off the source and onto the consumer. -/
theorem resAvg_self_adjoint (j : ι) (W g : (∀ i, α i) → ℚ) :
    pairQ (resAvg res j W) g = pairQ W (resAvg res j g) := by
  classical
  have hL : pairQ (resAvg res j W) g
      = ∑ p : (∀ i, α i) × α j, (if res j p.2 = res j (p.1 j) then
          W (Function.update p.1 j p.2) * g p.1
            / ((resFib res j (res j (p.1 j))).card : ℚ) else 0) := by
    unfold pairQ
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => (sum_fib_left j W g x).symm
  have hR : pairQ W (resAvg res j g)
      = ∑ p : (∀ i, α i) × α j, (if res j p.2 = res j (p.1 j) then
          W p.1 * g (Function.update p.1 j p.2)
            / ((resFib res j (res j (p.1 j))).card : ℚ) else 0) := by
    unfold pairQ
    rw [Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun x _ => (sum_fib_right j W g x).symm
  rw [hL, hR]
  refine Fintype.sum_bijective (swapUpd (α := α) j) (swapUpd_involutive j).bijective _ _ ?_
  rintro ⟨x, y⟩
  have h1 : (Function.update x j y) j = y := by simp
  by_cases hy : res j y = res j (x j)
  · have h2 : Function.update (Function.update x j y) j (x j) = x := by
      simp [Function.update_idem]
    simp only [swapUpd, h1, h2, hy]
  · simp only [swapUpd, h1, if_neg hy,
      if_neg (fun h : res j (x j) = res j y => hy h.symm)]

/-- `(I − T_j)` is self-adjoint. -/
theorem subT_self_adjoint (j : ι) (W g : (∀ i, α i) → ℚ) :
    pairQ (subT res j W) g = pairQ W (subT res j g) := by
  unfold subT
  rw [pairQ_sub_left, pairQ_sub_right, resAvg_self_adjoint]

/-- **`Q₃` is self-adjoint** on an eligible coordinate list without repetitions. -/
theorem Q3_self_adjoint {l : List ι} (hl : l.Nodup) (W g : (∀ i, α i) → ℚ) :
    pairQ (Q3 res l W) g = pairQ W (Q3 res l g) := by
  induction l generalizing W g with
  | nil => rfl
  | cons j l ih =>
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      have hnd : l.Nodup := (List.nodup_cons.mp hl).2
      rw [Q3_cons, subT_self_adjoint, ih hnd, Q3_subT_comm hj, Q3_cons]

end SelfAdjoint

/-! ## 3. Residue-determined consumers are annihilated -/

section ResidueDetermined

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  {res : ∀ i, α i → ℕ}

/-- A table function determined by the residue vector alone. -/
def ResidueDetermined (res : ∀ i, α i → ℕ) (g : (∀ i, α i) → ℚ) : Prop :=
  ∀ x y : (∀ i, α i), (∀ i, res i (x i) = res i (y i)) → g x = g y

/-- A residue-determined function is fixed by every residue-aware average. -/
theorem resAvg_of_residueDetermined {g : (∀ i, α i) → ℚ} (hg : ResidueDetermined res g)
    (j : ι) (x : ∀ i, α i) : resAvg res j g x = g x := by
  refine coordAvg_of_const (resFib_nonempty j x) _ fun y hy => ?_
  refine hg _ _ fun i => ?_
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self]
    exact mem_resFib.mp hy
  · rw [Function.update_of_ne hij]

/-- Hence `(I − T_j)` annihilates it. -/
theorem subT_of_residueDetermined {g : (∀ i, α i) → ℚ} (hg : ResidueDetermined res g) (j : ι) :
    subT res j g = fun _ => (0 : ℚ) := by
  funext x
  unfold subT
  rw [resAvg_of_residueDetermined hg]
  ring

/-- **`Q₃` annihilates every residue-determined consumer** (on a nonempty eligible list).  This
is the exact cancellation that must be used *before* any absolute value is taken. -/
theorem Q3_of_residueDetermined {g : (∀ i, α i) → ℚ} (hg : ResidueDetermined res g)
    {l : List ι} (hne : l ≠ []) : Q3 res l g = fun _ => (0 : ℚ) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons j l ih =>
      rcases l with _ | ⟨k, l'⟩
      · rw [Q3_cons, Q3_nil, subT_of_residueDetermined hg]
      · rw [Q3_cons, ih (by simp), subT_zero]

end ResidueDetermined

/-! ## 4. The exact fibrewise form of `R_loc-top,3` -/

section Reduction

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  {res : ∀ i, α i → ℕ}

/-- **The selected row consumer.**  For each cell `x` of the prime-coordinate table, the finite
selected consumer of the row `K x` of the pairing kernel.  These finitely many rationals are the
only way the kernel enters `R_loc-top,3`. -/
def rowConsumer (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (K : (∀ i, α i) → ℕ → ℚ)
    (x : ∀ i, α i) : ℚ :=
  selectedConsumer lam Ds Ns (K x)

/-- **Exact fibrewise identity.**  The residual is the pairing of the residue-aware top against
the selected row consumer. -/
theorem RlocTop3_eq_pair_rowConsumer (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) (l : List ι) (W : (∀ i, α i) → ℚ) :
    RlocTop3 lam Ds Ns K res l W = pairQ (Q3 res l W) (rowConsumer lam Ds Ns K) := by
  simp only [RlocTop3, selectedCenteredFunctional, Wres3, tableSource, selectedConsumer,
    pairQ, rowConsumer]
  calc ∑ d ∈ Ds, lam d * ∑ n ∈ Ns, (∑ x, Q3 res l W x * K x n) * centeredSel d n
      = ∑ d ∈ Ds, ∑ n ∈ Ns, ∑ x, Q3 res l W x * (lam d * (K x n * centeredSel d n)) := by
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun x _ => by ring
    _ = ∑ d ∈ Ds, ∑ x, ∑ n ∈ Ns, Q3 res l W x * (lam d * (K x n * centeredSel d n)) :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ x, ∑ d ∈ Ds, ∑ n ∈ Ns, Q3 res l W x * (lam d * (K x n * centeredSel d n)) :=
        Finset.sum_comm
    _ = ∑ x, Q3 res l W x * ∑ d ∈ Ds, lam d * ∑ n ∈ Ns, K x n * centeredSel d n := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]

/-- **The exact reduction theorem.**  Moving the (self-adjoint) residue-aware top projection off
the source and onto the consumer:

```
R_loc-top,3  =  ⟨ W , Q₃ (row consumer) ⟩ .
```

No estimate is used; the raw, *uncentered* source `W` appears on the left of the pairing. -/
theorem RlocTop3_eq_pair_Q3_rowConsumer (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) {l : List ι} (hl : l.Nodup)
    (W : (∀ i, α i) → ℚ) :
    RlocTop3 lam Ds Ns K res l W = pairQ W (Q3 res l (rowConsumer lam Ds Ns K)) := by
  rw [RlocTop3_eq_pair_rowConsumer, Q3_self_adjoint hl]

/-- **Exact vanishing.**  If the selected row consumer depends only on the residue vector then
`R_loc-top,3` is exactly `0` — not merely small. -/
theorem RlocTop3_eq_zero_of_residueDetermined_rowConsumer (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) {l : List ι} (hl : l.Nodup) (hne : l ≠ [])
    (W : (∀ i, α i) → ℚ) (h : ResidueDetermined res (rowConsumer lam Ds Ns K)) :
    RlocTop3 lam Ds Ns K res l W = 0 := by
  rw [RlocTop3_eq_pair_Q3_rowConsumer lam Ds Ns K res hl W, Q3_of_residueDetermined h hne]
  simp [pairQ]

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (α i)] in
/-- A residue-determined pairing kernel gives a residue-determined row consumer. -/
theorem residueDetermined_rowConsumer_of_kernel (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ}
    (hK : ∀ n, ResidueDetermined res (fun x => K x n)) :
    ResidueDetermined res (rowConsumer lam Ds Ns K) := by
  intro x y hxy
  unfold rowConsumer selectedConsumer
  refine Finset.sum_congr rfl fun d _ => ?_
  refine congrArg _ (Finset.sum_congr rfl fun n _ => ?_)
  have h : K x n = K y n := hK n x y hxy
  rw [h]

end Reduction

/-! ## 5. The deterministic reduction to a residue-variation input -/

section Budget

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  [∀ i, Nonempty (α i)] {res : ∀ i, α i → ℕ}

/-- **The deterministic reduction.**  Suppose

* `rho` is a residue-determined profile and the selected row consumer is within `ε` of it,
  uniformly over the table;
* the raw source has ℓ¹ mass at most `Mw`;
* `Mw · 2^r · ε ≤ C x L^{-S₀}` where `r = |J|` is the number of eligible coordinates.

Then the physical bound `RLocTop3Bound` holds.  Everything except the first bullet is exact
finite arithmetic, so the first bullet is the **weakest remaining input**. -/
theorem RLocTop3Bound_of_residue_approximation (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) {l : List ι} (hl : l.Nodup) (hne : l ≠ [])
    (W : (∀ i, α i) → ℚ) {rho : (∀ i, α i) → ℚ} (hrho : ResidueDetermined res rho)
    {eps Mw : ℚ} (heps : ∀ z, |rowConsumer lam Ds Ns K z - rho z| ≤ eps)
    (hW : ∑ x, |W x| ≤ Mw) {xr L S0 C : ℝ}
    (hfinal : ((Mw * 2 ^ l.length * eps : ℚ) : ℝ) ≤ C * xr * L ^ (-S0)) :
    RLocTop3Bound lam Ds Ns K res l W xr L S0 C := by
  classical
  have hepsnn : 0 ≤ eps := le_trans (abs_nonneg _) (heps (Classical.arbitrary _))
  have hMwnn : 0 ≤ Mw := le_trans (Finset.sum_nonneg fun x _ => abs_nonneg _) hW
  -- 1. the exact identity, with the residue-determined profile removed for free
  have hid : RlocTop3 lam Ds Ns K res l W
      = pairQ W (Q3 res l (fun z => rowConsumer lam Ds Ns K z - rho z)) := by
    rw [RlocTop3_eq_pair_Q3_rowConsumer lam Ds Ns K res hl W, Q3_sub]
    have hz : Q3 res l rho = fun _ => (0 : ℚ) := Q3_of_residueDetermined hrho hne
    rw [hz]
    simp
  -- 2. the pointwise bound on the residue-aware difference of the deviation
  have hpt : ∀ x, |Q3 res l (fun z => rowConsumer lam Ds Ns K z - rho z) x|
      ≤ 2 ^ l.length * eps := fun x => abs_Q3_le l hepsnn heps x
  -- 3. assemble
  have habs : |RlocTop3 lam Ds Ns K res l W| ≤ Mw * 2 ^ l.length * eps := by
    rw [hid]
    unfold pairQ
    calc |∑ x, W x * Q3 res l (fun z => rowConsumer lam Ds Ns K z - rho z) x|
        ≤ ∑ x, |W x * Q3 res l (fun z => rowConsumer lam Ds Ns K z - rho z) x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ x, |W x| * (2 ^ l.length * eps) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hpt x) (abs_nonneg _)
      _ = (∑ x, |W x|) * (2 ^ l.length * eps) := by rw [← Finset.sum_mul]
      _ ≤ Mw * (2 ^ l.length * eps) := by
          refine mul_le_mul_of_nonneg_right hW ?_
          positivity
      _ = Mw * 2 ^ l.length * eps := by ring
  unfold RLocTop3Bound
  refine le_trans ?_ hfinal
  rw [← Rat.cast_abs]
  exact_mod_cast habs

end Budget

/-! ## 6. The isolated remaining input -/

section Interface

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  [∀ i, Nonempty (α i)]

/-- **`RowConsumerResidueProfile`** — the isolated remaining input for `R_loc-top,3`.

It says exactly this: *there is a profile depending only on the residue vector which approximates
the selected row consumer uniformly to within `eps`.*  It quantifies over nothing but the finitely
many numbers `selectedConsumer λ Ds Ns (K x)`.  It is **never inhabited** in this repository and
is not an axiom. -/
def RowConsumerResidueProfile (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) (eps : ℚ) : Prop :=
  ∃ profile : (∀ i, α i) → ℚ,
    ResidueDetermined res profile ∧ ∀ z, |rowConsumer lam Ds Ns K z - profile z| ≤ eps

/-- **The frontier is exactly this input.**  `RowConsumerResidueProfile` together with the
finite arithmetic budget gives the physical bound. -/
theorem RLocTop3Bound_of_profile {lam : ℕ → ℚ} {Ds Ns : Finset ℕ}
    {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ} {eps Mw : ℚ} {l : List ι}
    (hl : l.Nodup) (hne : l ≠ []) (W : (∀ i, α i) → ℚ)
    (h : RowConsumerResidueProfile lam Ds Ns K res eps)
    (hW : ∑ x, |W x| ≤ Mw) {xr L S0 C : ℝ}
    (hfinal : ((Mw * 2 ^ l.length * eps : ℚ) : ℝ) ≤ C * xr * L ^ (-S0)) :
    RLocTop3Bound lam Ds Ns K res l W xr L S0 C := by
  obtain ⟨rho, hdet, happrox⟩ := h
  exact RLocTop3Bound_of_residue_approximation lam Ds Ns K res hl hne W hdet happrox hW hfinal

/-- **The intrinsic form of the remaining input**: the selected row consumer varies by at most
`eps` between two cells of the table with the same residue vector.  No auxiliary profile occurs:
this is a statement about the physical pairing kernel alone. -/
def RowConsumerResidueOscillation (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) (eps : ℚ) : Prop :=
  ∀ x y : (∀ i, α i), (∀ i, res i (x i) = res i (y i)) →
    |rowConsumer lam Ds Ns K x - rowConsumer lam Ds Ns K y| ≤ eps

open Classical in
/-- A canonical representative of a residue vector. -/
noncomputable def resPick (res : ∀ i, α i → ℕ) (w : ι → ℕ) : ∀ i, α i :=
  if h : ∃ y : (∀ i, α i), (fun i => res i (y i)) = w then h.choose else Classical.arbitrary _

theorem resPick_spec (res : ∀ i, α i → ℕ) (x : ∀ i, α i) (i : ι) :
    res i (resPick res (fun i => res i (x i)) i) = res i (x i) := by
  classical
  have h : ∃ y : (∀ i, α i), (fun i => res i (y i)) = fun i => res i (x i) := ⟨x, rfl⟩
  have hpick : resPick res (fun i => res i (x i)) = h.choose := dif_pos h
  rw [hpick]
  exact congrFun h.choose_spec i

/-- **The two forms of the remaining input agree (one direction).**  A residue-fibre oscillation
bound produces a residue-determined profile with the same `eps`. -/
theorem rowConsumerResidueProfile_of_oscillation {lam : ℕ → ℚ} {Ds Ns : Finset ℕ}
    {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ} {eps : ℚ}
    (h : RowConsumerResidueOscillation lam Ds Ns K res eps) :
    RowConsumerResidueProfile lam Ds Ns K res eps := by
  classical
  refine ⟨fun x => rowConsumer lam Ds Ns K (resPick res fun i => res i (x i)), ?_, ?_⟩
  · intro x y hxy
    have hv : (fun i => res i (x i)) = fun i => res i (y i) := funext hxy
    show rowConsumer lam Ds Ns K (resPick res fun i => res i (x i))
      = rowConsumer lam Ds Ns K (resPick res fun i => res i (y i))
    rw [hv]
  · intro z
    exact h z _ fun i => (resPick_spec res z i).symm

omit [Fintype ι] [DecidableEq ι] [(i : ι) → Fintype (α i)] [∀ (i : ι), Nonempty (α i)] in
/-- **The converse direction**, with the loss of a factor `2`: a profile of accuracy `eps` gives
an oscillation bound `2 eps`. -/
theorem rowConsumerResidueOscillation_of_profile {lam : ℕ → ℚ} {Ds Ns : Finset ℕ}
    {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ} {eps : ℚ}
    (h : RowConsumerResidueProfile lam Ds Ns K res eps) :
    RowConsumerResidueOscillation lam Ds Ns K res (2 * eps) := by
  obtain ⟨rho, hdet, happrox⟩ := h
  intro x y hxy
  have hrho : rho x = rho y := hdet x y hxy
  have h1 := happrox x
  have h2 := happrox y
  have hx := abs_le.mp h1
  have hy := abs_le.mp h2
  rw [abs_le]
  constructor <;> [linarith [hrho]; linarith [hrho]]

/-- **The single-hypothesis form of the frontier.**  The physical `R_loc-top,3` bound follows
from the residue-fibre oscillation bound for the selected row consumer together with the finite
arithmetic budget.  Every step except the oscillation hypothesis is kernel-proved. -/
theorem RLocTop3Bound_of_oscillation {lam : ℕ → ℚ} {Ds Ns : Finset ℕ}
    {K : (∀ i, α i) → ℕ → ℚ} {res : ∀ i, α i → ℕ} {eps Mw : ℚ} {l : List ι}
    (hl : l.Nodup) (hne : l ≠ []) (W : (∀ i, α i) → ℚ)
    (h : RowConsumerResidueOscillation lam Ds Ns K res eps)
    (hW : ∑ x, |W x| ≤ Mw) {xr L S0 C : ℝ}
    (hfinal : ((Mw * 2 ^ l.length * eps : ℚ) : ℝ) ≤ C * xr * L ^ (-S0)) :
    RLocTop3Bound lam Ds Ns K res l W xr L S0 C :=
  RLocTop3Bound_of_profile hl hne W (rowConsumerResidueProfile_of_oscillation h) hW hfinal

/-- The exact **required budget** for `R_loc-top,3`, in the form used downstream: with `r = |J|`
eligible coordinates and raw ℓ¹ source mass `Mw`, the residue-variation error must satisfy
`eps ≤ C x L^{-S₀} / (Mw 2^r)`. -/
def RLocTop3RequiredBudget (Mw eps : ℚ) (r : ℕ) (xr L S0 C : ℝ) : Prop :=
  ((Mw * 2 ^ r * eps : ℚ) : ℝ) ≤ C * xr * L ^ (-S0)

end Interface

/-! ## 7. Sharpness: the isolated input cannot simply be dropped -/

section Sharpness

/-- A one-coordinate table with two cells lying in the **same** residue class. -/
abbrev sharpCell : Type := ∀ _ : Fin 1, Fin 2

/-- The constant residue map: both cells are in the same class, so `T = P` here. -/
def sharpRes : ∀ _ : Fin 1, Fin 2 → ℕ := fun _ _ => 0

/-- A mean-zero source on the two cells. -/
def sharpW : sharpCell → ℚ := fun x => if x 0 = 0 then 1 else -1

/-- A pairing kernel that is *not* determined by the residue vector. -/
def sharpK : sharpCell → ℕ → ℚ := fun x _ => if x 0 = 0 then 1 else 0

/-- **Sharpness.**  With a genuinely non-residue-determined kernel the residual is nonzero, so
the residue-aware algebra alone does not kill `R_loc-top,3`: the isolated input
`RowConsumerResidueProfile` is load-bearing, not bookkeeping. -/
theorem sharp_RlocTop3_eq_one :
    RlocTop3 (fun _ => 1) {2} {0} sharpK sharpRes [0] sharpW = 1 := by
  have hsum : ∀ f : sharpCell → ℚ, ∑ x, f x = f (fun _ => 0) + f (fun _ => 1) := by
    intro f
    rw [← Equiv.sum_comp (Equiv.funUnique (Fin 1) (Fin 2)).symm f, Fin.sum_univ_two]
    rfl
  simp only [RlocTop3, selectedCenteredFunctional, selectedConsumer, Wres3, tableSource,
    Finset.sum_singleton]
  rw [hsum]
  norm_num [Q3, subT, resAvg, coordAvg, resFib, sharpW, sharpK, sharpRes, centeredSel,
    deltaSel, uSel, hsum]

theorem sharp_RlocTop3_ne_zero :
    RlocTop3 (fun _ => 1) {2} {0} sharpK sharpRes [0] sharpW ≠ 0 := by
  rw [sharp_RlocTop3_eq_one]
  norm_num

/-- Consequently there is an instance of the frontier data in which the residual does not
vanish. -/
theorem residue_awareness_alone_does_not_kill_RlocTop3 :
    ∃ (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (K : sharpCell → ℕ → ℚ)
      (res : ∀ _ : Fin 1, Fin 2 → ℕ) (l : List (Fin 1)) (W : sharpCell → ℚ),
      l.Nodup ∧ l ≠ [] ∧ RlocTop3 lam Ds Ns K res l W ≠ 0 :=
  ⟨fun _ => 1, {2}, {0}, sharpK, sharpRes, [0], sharpW, by simp, by simp,
    sharp_RlocTop3_ne_zero⟩

end Sharpness

end ResidueProj

end Gate1B.R11.Frontier
