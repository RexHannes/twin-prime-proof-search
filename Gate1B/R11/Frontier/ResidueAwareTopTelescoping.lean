/-
# Gate1B / R11 / Frontier : residue-aware top telescoping and the current residual `R_loc-top,3`

Append-only module of the residue-aware delta.  **Exact finite linear algebra only.**

Banked here:

* the exact telescoping decomposition

  ```
  Q_old W − Q₃ W
      = ∑_{t=1}^r  [∏_{s<t}(I − T_{j_s})] (T_{j_t} − P_{j_t}) [∏_{s>t}(I − P_{j_s})] W ,
  ```

  both in recursive form (`telescope`) and in the literal indexed form (`telescope_explicit`);
* the two structural facts that make it a genuine decomposition: no term reintroduces an already
  removed ordinary average component (`binAvg_Qold_eq_zero`, re-ascribed here), and `Q₃ W` stays
  centered under every `T_j` (`resAvg_Q3_eq_zero`);
* the current exact residual: `W_res3 = Q₃ W` and `R_locTop3 = E_λ*(W_res3)` for the selected
  centered functional `E_λ*`;
* the **no-double-charge** additive decomposition of the source into the already-owned ordinary
  component, the residue-refinement difference and the residue-aware top.

`RLocTop3Bound` — the analytic estimate for `R_locTop3` — is a proposition that is **never
inhabited** here and is not an axiom.  Its status is OPEN.
-/
import Gate1B.R11.Frontier.ResidueAwareProjection

namespace Gate1B.R11.Frontier

open Finset

namespace ResidueProj

section Telescoping

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  {res : ∀ i, α i → ℕ}

/-! ## 1. Averages commute with finite sums -/

omit [(i : ι) → Fintype (α i)] in
theorem coordAvg_sum {κ : Type*} (j : ι) (s : Finset (α j)) (S : Finset κ)
    (G : κ → (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    coordAvg j s (fun z => ∑ k ∈ S, G k z) x = ∑ k ∈ S, coordAvg j s (G k) x := by
  unfold coordAvg
  rw [Finset.sum_comm, Finset.sum_div]

theorem resAvg_sum {κ : Type*} (j : ι) (S : Finset κ) (G : κ → (∀ i, α i) → ℚ)
    (x : ∀ i, α i) :
    resAvg res j (fun z => ∑ k ∈ S, G k z) x = ∑ k ∈ S, resAvg res j (G k) x :=
  coordAvg_sum _ _ _ _ _

theorem subT_sum {κ : Type*} (j : ι) (S : Finset κ) (G : κ → (∀ i, α i) → ℚ)
    (x : ∀ i, α i) :
    subT res j (fun z => ∑ k ∈ S, G k z) x = ∑ k ∈ S, subT res j (G k) x := by
  unfold subT
  rw [resAvg_sum, ← Finset.sum_sub_distrib]

/-! ## 2. The telescoping decomposition -/

/-- The residue-aware telescoping sum, in recursive form.  Its `j :: l` clause is exactly the
`t`-th term of the displayed decomposition:
`(T_j − P_j)(∏_{s>t}(I−P))W` followed by `(I − T_j)` applied to the remaining terms. -/
def telescope (res : ∀ i, α i → ℕ) : List ι → ((∀ i, α i) → ℚ) → ((∀ i, α i) → ℚ)
  | [], _ => fun _ => 0
  | j :: l, W => fun x =>
      (resAvg res j (Qold l W) x - binAvg j (Qold l W) x)
        + subT res j (telescope res l W) x

@[simp] theorem telescope_nil (W : (∀ i, α i) → ℚ) :
    telescope res [] W = fun _ => (0 : ℚ) := rfl

@[simp] theorem telescope_cons (j : ι) (l : List ι) (W : (∀ i, α i) → ℚ) :
    telescope res (j :: l) W = fun x =>
      (resAvg res j (Qold l W) x - binAvg j (Qold l W) x)
        + subT res j (telescope res l W) x := rfl

/-- **The exact residue-aware telescoping identity**: `Q_old W − Q₃ W = telescope W`. -/
theorem Qold_sub_Q3_eq_telescope (l : List ι) (W : (∀ i, α i) → ℚ) :
    (fun x => Qold l W x - Q3 res l W x) = telescope res l W := by
  induction l generalizing W with
  | nil => funext x; simp
  | cons j l ih =>
      funext x
      have hIH : (fun z => Qold l W z - Q3 res l W z) = telescope res l W := ih W
      show Qold (j :: l) W x - Q3 res (j :: l) W x = telescope res (j :: l) W x
      rw [telescope_cons, Qold_cons, Q3_cons]
      show (Qold l W x - binAvg j (Qold l W) x) - (Q3 res l W x - resAvg res j (Q3 res l W) x)
        = (resAvg res j (Qold l W) x - binAvg j (Qold l W) x)
          + subT res j (telescope res l W) x
      rw [← hIH]
      show _ = _ + ((Qold l W x - Q3 res l W x)
        - resAvg res j (fun z => Qold l W z - Q3 res l W z) x)
      rw [resAvg_sub]
      ring

/-- The literal indexed form of the decomposition:  with `j_t = l[t]`, prefix `l.take t` and
suffix `l.drop (t+1)`,

```
Q_old W − Q₃ W = ∑_{t < r} (∏_{s<t}(I − T_{j_s})) (T_{j_t} − P_{j_t}) (∏_{s>t}(I − P_{j_s})) W .
```
-/
theorem telescope_explicit (j0 : ι) (l : List ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    telescope res l W x
      = ∑ t ∈ Finset.range l.length,
          Q3 res (l.take t)
            (fun z => resAvg res (l.getD t j0) (Qold (l.drop (t + 1)) W) z
              - binAvg (l.getD t j0) (Qold (l.drop (t + 1)) W) z) x := by
  induction l generalizing W x with
  | nil => simp
  | cons j l ih =>
      have hlen : (j :: l).length = l.length + 1 := rfl
      rw [hlen, Finset.sum_range_succ']
      have h0 : Q3 res ((j :: l).take 0)
          (fun z => resAvg res ((j :: l).getD 0 j0) (Qold ((j :: l).drop 1) W) z
            - binAvg ((j :: l).getD 0 j0) (Qold ((j :: l).drop 1) W) z) x
          = resAvg res j (Qold l W) x - binAvg j (Qold l W) x := by
        simp
      have hstep : ∀ s : ℕ,
          Q3 res ((j :: l).take (s + 1))
            (fun z => resAvg res ((j :: l).getD (s + 1) j0) (Qold ((j :: l).drop (s + 2)) W) z
              - binAvg ((j :: l).getD (s + 1) j0) (Qold ((j :: l).drop (s + 2)) W) z) x
            = subT res j (Q3 res (l.take s)
                (fun z => resAvg res (l.getD s j0) (Qold (l.drop (s + 1)) W) z
                  - binAvg (l.getD s j0) (Qold (l.drop (s + 1)) W) z)) x := by
        intro s
        simp [List.take_succ_cons, Q3_cons]
      rw [h0, Finset.sum_congr rfl fun s _ => hstep s]
      rw [telescope_cons]
      have hsum : ∑ s ∈ Finset.range l.length,
          subT res j (Q3 res (l.take s)
            (fun z => resAvg res (l.getD s j0) (Qold (l.drop (s + 1)) W) z
              - binAvg (l.getD s j0) (Qold (l.drop (s + 1)) W) z)) x
          = subT res j (telescope res l W) x := by
        rw [← subT_sum]
        refine congrArg (fun (V : (∀ i, α i) → ℚ) => subT res j V x) ?_
        funext z
        rw [ih W z]
      rw [hsum]
      ring

/-! ## 3. Nothing is reintroduced, nothing is charged twice -/

/-- No term of the decomposition reintroduces an already removed ordinary average component:
the suffix factor `∏_{s>t}(I − P_{j_s})W` is annihilated by every `P_k`, `k` in the suffix. -/
theorem suffix_stays_P_centered [∀ i, Nonempty (α i)] {k : ι} {l : List ι} (hl : l.Nodup)
    (hk : k ∈ l) (W : (∀ i, α i) → ℚ) :
    (fun x => binAvg k (Qold l W) x) = fun _ => (0 : ℚ) :=
  binAvg_Qold_eq_zero hl hk W

/-- `Q₃ W` remains centered under every residue-aware average of the eligible set. -/
theorem residual_stays_T_centered {k : ι} {l : List ι} (hl : l.Nodup) (hk : k ∈ l)
    (W : (∀ i, α i) → ℚ) :
    (fun x => resAvg res k (Q3 res l W) x) = fun _ => (0 : ℚ) :=
  resAvg_Q3_eq_zero hl hk W

/-- **No-double-charge decomposition.**  The source splits *exactly* into the already-owned
ordinary component, the residue-refinement difference, and the residue-aware top; the three are
distinct linear components and their sum is the source. -/
theorem no_double_charge (l : List ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    W x = (W x - Qold l W x) + (Qold l W x - Q3 res l W x) + Q3 res l W x := by
  ring

/-- The middle component of the no-double-charge decomposition is exactly the telescoping sum. -/
theorem no_double_charge_middle (l : List ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    W x = (W x - Qold l W x) + telescope res l W x + Q3 res l W x := by
  rw [← congrFun (Qold_sub_Q3_eq_telescope l W) x]
  ring

/-! ## 4. The current exact residual `R_loc-top,3` -/

/-- `W_res3 = Q₃ W`, the residue-aware top of the source. -/
def Wres3 (res : ∀ i, α i → ℕ) (l : List ι) (W : (∀ i, α i) → ℚ) : (∀ i, α i) → ℚ :=
  Q3 res l W

variable [Fintype ι]

/-- The source coefficient attached to a table function by a pairing kernel. -/
def tableSource (K : (∀ i, α i) → ℕ → ℚ) (W : (∀ i, α i) → ℚ) (n : ℕ) : ℚ :=
  ∑ x : (∀ i, α i), W x * K x n

/-- **The selected centered functional** `E_λ*`: the finite selected consumer of the source
coefficient attached to a table function. -/
def selectedCenteredFunctional (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (K : (∀ i, α i) → ℕ → ℚ)
    (W : (∀ i, α i) → ℚ) : ℚ :=
  selectedConsumer lam Ds Ns (tableSource K W)

/-- `E_λ*` is additive. -/
theorem selectedCenteredFunctional_add (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (W V : (∀ i, α i) → ℚ) :
    selectedCenteredFunctional lam Ds Ns K (fun x => W x + V x)
      = selectedCenteredFunctional lam Ds Ns K W + selectedCenteredFunctional lam Ds Ns K V := by
  unfold selectedCenteredFunctional
  rw [← selectedConsumer_add]
  refine congrArg _ ?_
  funext n
  unfold tableSource
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- **`R_loc-top,3`** — the current exact residual: the selected centered functional applied to
the residue-aware top `W_res3 = Q₃ W`.  This is a *definition*; no estimate is asserted. -/
def RlocTop3 (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (K : (∀ i, α i) → ℕ → ℚ)
    (res : ∀ i, α i → ℕ) (l : List ι) (W : (∀ i, α i) → ℚ) : ℚ :=
  selectedCenteredFunctional lam Ds Ns K (Wres3 res l W)

/-- The residual is, by definition, the selected consumer of the residue-aware top. -/
theorem RlocTop3_def (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (K : (∀ i, α i) → ℕ → ℚ)
    (res : ∀ i, α i → ℕ) (l : List ι) (W : (∀ i, α i) → ℚ) :
    RlocTop3 lam Ds Ns K res l W
      = selectedConsumer lam Ds Ns (tableSource K (Q3 res l W)) := rfl

/-- **The exact three-component reassembly of the selected consumer.**  Nothing is charged
twice: the ordinary component, the residue-refinement difference and `R_loc-top,3` add up to the
full selected consumer of the source. -/
theorem selectedConsumer_three_component (lam : ℕ → ℚ) (Ds Ns : Finset ℕ)
    (K : (∀ i, α i) → ℕ → ℚ) (res : ∀ i, α i → ℕ) (l : List ι) (W : (∀ i, α i) → ℚ) :
    selectedCenteredFunctional lam Ds Ns K W
      = selectedCenteredFunctional lam Ds Ns K (fun x => W x - Qold l W x)
        + selectedCenteredFunctional lam Ds Ns K (telescope res l W)
        + RlocTop3 lam Ds Ns K res l W := by
  have h1 : (fun x => W x)
      = fun x => ((W x - Qold l W x) + telescope res l W x) + Q3 res l W x := by
    funext x
    exact no_double_charge_middle l W x
  rw [RlocTop3, Wres3]
  calc selectedCenteredFunctional lam Ds Ns K W
      = selectedCenteredFunctional lam Ds Ns K
          (fun x => ((W x - Qold l W x) + telescope res l W x) + Q3 res l W x) := by
        rw [← h1]
    _ = selectedCenteredFunctional lam Ds Ns K
          (fun x => (W x - Qold l W x) + telescope res l W x)
        + selectedCenteredFunctional lam Ds Ns K (Q3 res l W) :=
        selectedCenteredFunctional_add _ _ _ _ _ _
    _ = (selectedCenteredFunctional lam Ds Ns K (fun x => W x - Qold l W x)
          + selectedCenteredFunctional lam Ds Ns K (telescope res l W))
        + selectedCenteredFunctional lam Ds Ns K (Q3 res l W) := by
        rw [selectedCenteredFunctional_add]

/-- **The analytic estimate for `R_loc-top,3`.**  A proposition — *never inhabited* in this
repository, and not an axiom.  Status: OPEN. -/
def RLocTop3Bound (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (K : (∀ i, α i) → ℕ → ℚ)
    (res : ∀ i, α i → ℕ) (l : List ι) (W : (∀ i, α i) → ℚ) (x L S0 C : ℝ) : Prop :=
  |((RlocTop3 lam Ds Ns K res l W : ℚ) : ℝ)| ≤ C * x * L ^ (-S0)

end Telescoping

end ResidueProj

end Gate1B.R11.Frontier
