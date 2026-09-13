/-
# Gate1B / R11 / Frontier : residue-aware local prime-bin projections

Append-only module of the residue-aware delta.  **Exact finite linear algebra only.**

On a finite Cartesian prime-coordinate table `∀ i, α i` (each coordinate a finite prime bin,
equipped with a residue map `res i : α i → ℕ`, in practice the residue modulo `3`) we define

```
P_j W   =  the ordinary within-bin average in coordinate j,
T_j W   =  the within-bin AND same-residue average in coordinate j,
```

and bank the exact projection algebra

```
P_j² = P_j ,   T_j² = T_j ,   P_j T_j = P_j ,   T_j P_j = P_j ,
```

together with commutation of the actions of independent coordinates, and the two top projections

```
Q_old = ∏_{j ∈ J} (I − P_j) ,     Q₃ = ∏_{j ∈ J} (I − T_j) ,      Q₃ Q_old = Q₃ .
```

No analytic statement occurs in this module.
-/
import Gate1B.R11.Frontier.Mod3TargetAlgebra

namespace Gate1B.R11.Frontier

open Finset

namespace ResidueProj

/-! ## 1. Coordinate averages -/

section CoordAvg

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*}

/-- The average of `W` over a finite set `s` of values of the `j`-th prime coordinate. -/
def coordAvg (j : ι) (s : Finset (α j)) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) : ℚ :=
  (∑ y ∈ s, W (Function.update x j y)) / (s.card : ℚ)

/-- Two functions agreeing along the averaged fibre have the same average. -/
theorem coordAvg_congr {j : ι} {s : Finset (α j)} {W V : (∀ i, α i) → ℚ} {x : ∀ i, α i}
    (h : ∀ y ∈ s, W (Function.update x j y) = V (Function.update x j y)) :
    coordAvg j s W x = coordAvg j s V x := by
  unfold coordAvg
  exact congrArg (· / (s.card : ℚ)) (Finset.sum_congr rfl h)

/-- An average of a function that is constant along the fibre is that constant. -/
theorem coordAvg_of_const {j : ι} {s : Finset (α j)} {W : (∀ i, α i) → ℚ} {x : ∀ i, α i}
    (hs : s.Nonempty) (c : ℚ) (h : ∀ y ∈ s, W (Function.update x j y) = c) :
    coordAvg j s W x = c := by
  have hcard : (s.card : ℚ) ≠ 0 := by
    have := Finset.card_pos.mpr hs
    exact_mod_cast this.ne'
  unfold coordAvg
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-- Averaging is linear: differences. -/
theorem coordAvg_sub (j : ι) (s : Finset (α j)) (W V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    coordAvg j s (fun z => W z - V z) x = coordAvg j s W x - coordAvg j s V x := by
  unfold coordAvg
  rw [← sub_div, ← Finset.sum_sub_distrib]

/-- Averaging is linear: sums. -/
theorem coordAvg_add (j : ι) (s : Finset (α j)) (W V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    coordAvg j s (fun z => W z + V z) x = coordAvg j s W x + coordAvg j s V x := by
  unfold coordAvg
  rw [← add_div, ← Finset.sum_add_distrib]

@[simp] theorem coordAvg_zero (j : ι) (s : Finset (α j)) (x : ∀ i, α i) :
    coordAvg j s (fun _ => (0 : ℚ)) x = 0 := by
  simp [coordAvg]

/-- A coordinate average does not depend on the value of that coordinate. -/
theorem coordAvg_update (j : ι) (s : Finset (α j)) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i)
    (y : α j) : coordAvg j s W (Function.update x j y) = coordAvg j s W x := by
  unfold coordAvg
  refine congrArg (· / (s.card : ℚ)) (Finset.sum_congr rfl fun z _ => ?_)
  rw [Function.update_idem]

/-- Averages over two *fixed* sets in two different coordinates commute. -/
theorem coordAvg_comm {j k : ι} (hjk : j ≠ k) (s : Finset (α j)) (t : Finset (α k))
    (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    coordAvg j s (coordAvg k t W) x = coordAvg k t (coordAvg j s W) x := by
  unfold coordAvg
  have hL : ∀ y : α j, (∑ z ∈ t, W (Function.update (Function.update x j y) k z))
      / (t.card : ℚ) = (∑ z ∈ t, W (Function.update (Function.update x k z) j y))
      / (t.card : ℚ) := by
    intro y
    refine congrArg (· / (t.card : ℚ)) (Finset.sum_congr rfl fun z _ => ?_)
    rw [Function.update_comm hjk y z x]
  rw [Finset.sum_congr rfl fun y _ => hL y]
  rw [← Finset.sum_div, ← Finset.sum_div, div_div, div_div, Finset.sum_comm, mul_comm]

end CoordAvg

/-! ## 2. The two local prime-bin projections -/

section Projections

variable {ι : Type*} [DecidableEq ι] {α : ι → Type*} [∀ i, Fintype (α i)]
  {res : ∀ i, α i → ℕ}

/-- The residue fibre of the `j`-th coordinate. -/
def resFib (res : ∀ i, α i → ℕ) (j : ι) (c : ℕ) : Finset (α j) :=
  Finset.univ.filter fun y => res j y = c

/-- `P_j` : the ordinary within-bin average in coordinate `j`. -/
def binAvg (j : ι) (W : (∀ i, α i) → ℚ) : (∀ i, α i) → ℚ :=
  coordAvg j Finset.univ W

/-- `T_j` : the within-bin **and same-residue** average in coordinate `j`. -/
def resAvg (res : ∀ i, α i → ℕ) (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) : ℚ :=
  coordAvg j (resFib res j (res j (x j))) W x

omit [DecidableEq ι] in
theorem mem_resFib {j : ι} {c : ℕ} {y : α j} : y ∈ resFib res j c ↔ res j y = c := by
  simp [resFib]

omit [DecidableEq ι] in
theorem resFib_nonempty (j : ι) (x : ∀ i, α i) : (resFib res j (res j (x j))).Nonempty :=
  ⟨x j, mem_resFib.mpr rfl⟩

@[simp] theorem binAvg_zero (j : ι) (x : ∀ i, α i) : binAvg j (fun _ => (0 : ℚ)) x = 0 := by
  simp [binAvg]

@[simp] theorem resAvg_zero (j : ι) (x : ∀ i, α i) :
    resAvg res j (fun _ => (0 : ℚ)) x = 0 := by
  simp [resAvg]

theorem binAvg_sub (j : ι) (W V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    binAvg j (fun z => W z - V z) x = binAvg j W x - binAvg j V x :=
  coordAvg_sub _ _ _ _ _

theorem resAvg_sub (j : ι) (W V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    resAvg res j (fun z => W z - V z) x = resAvg res j W x - resAvg res j V x :=
  coordAvg_sub _ _ _ _ _

theorem binAvg_add (j : ι) (W V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    binAvg j (fun z => W z + V z) x = binAvg j W x + binAvg j V x :=
  coordAvg_add _ _ _ _ _

theorem resAvg_add (j : ι) (W V : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    resAvg res j (fun z => W z + V z) x = resAvg res j W x + resAvg res j V x :=
  coordAvg_add _ _ _ _ _

theorem binAvg_update (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) (y : α j) :
    binAvg j W (Function.update x j y) = binAvg j W x :=
  coordAvg_update _ _ _ _ _

/-- The residue-aware average is invariant under moves inside the residue fibre. -/
theorem resAvg_update (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) {y : α j}
    (hy : res j y = res j (x j)) :
    resAvg res j W (Function.update x j y) = resAvg res j W x := by
  unfold resAvg
  rw [Function.update_self, hy]
  exact coordAvg_update _ _ _ _ _

/-- `P_j² = P_j`. -/
theorem binAvg_idem [∀ i, Nonempty (α i)] (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    binAvg j (binAvg j W) x = binAvg j W x :=
  coordAvg_of_const Finset.univ_nonempty _ fun y _ => binAvg_update j W x y

/-- `T_j² = T_j`. -/
theorem resAvg_idem (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    resAvg res j (resAvg res j W) x = resAvg res j W x :=
  coordAvg_of_const (resFib_nonempty j x) _ fun _ hy =>
    resAvg_update j W x (mem_resFib.mp hy)

/-- `T_j P_j = P_j`. -/
theorem resAvg_binAvg (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    resAvg res j (binAvg j W) x = binAvg j W x :=
  coordAvg_of_const (resFib_nonempty j x) _ fun y _ => binAvg_update j W x y

/-- `P_j T_j = P_j`: the ordinary average of a residue-aware average is the ordinary average. -/
theorem binAvg_resAvg (j : ι) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    binAvg j (resAvg res j W) x = binAvg j W x := by
  unfold binAvg coordAvg
  refine congrArg (· / ((Finset.univ : Finset (α j)).card : ℚ)) ?_
  classical
  have hmaps : ∀ y ∈ (Finset.univ : Finset (α j)), res j y ∈ Finset.image (res j) Finset.univ :=
    fun y _ => Finset.mem_image_of_mem _ (Finset.mem_univ y)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
      (fun y => resAvg res j W (Function.update x j y)),
    ← Finset.sum_fiberwise_of_maps_to hmaps (fun y => W (Function.update x j y))]
  refine Finset.sum_congr rfl fun c hc => ?_
  have hfil : (Finset.univ : Finset (α j)).filter (fun y => res j y = c) = resFib res j c := rfl
  obtain ⟨y0, -, hy0⟩ := Finset.mem_image.mp hc
  have hne : (resFib res j c).Nonempty := ⟨y0, mem_resFib.mpr hy0⟩
  have hcard : ((resFib res j c).card : ℚ) ≠ 0 := by
    have := Finset.card_pos.mpr hne
    exact_mod_cast this.ne'
  have hval : ∀ y ∈ resFib res j c,
      resAvg res j W (Function.update x j y)
        = (∑ z ∈ resFib res j c, W (Function.update x j z)) / ((resFib res j c).card : ℚ) := by
    intro y hy
    unfold resAvg coordAvg
    rw [Function.update_self, mem_resFib.mp hy]
    refine congrArg (· / ((resFib res j c).card : ℚ)) (Finset.sum_congr rfl fun z _ => ?_)
    rw [Function.update_idem]
  rw [hfil, Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  field_simp

/-! ### Commutation of independent coordinates -/

/-- `P_j P_k = P_k P_j` for independent coordinates. -/
theorem binAvg_comm {j k : ι} (hjk : j ≠ k) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    binAvg j (binAvg k W) x = binAvg k (binAvg j W) x :=
  coordAvg_comm hjk _ _ _ _

/-- `P_j T_k = T_k P_j` for independent coordinates. -/
theorem binAvg_resAvg_comm {j k : ι} (hjk : j ≠ k) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    binAvg j (resAvg res k W) x = resAvg res k (binAvg j W) x := by
  have hL : binAvg j (resAvg res k W) x
      = coordAvg j Finset.univ (coordAvg k (resFib res k (res k (x k))) W) x := by
    refine coordAvg_congr fun y _ => ?_
    simp only [resAvg, Function.update_of_ne (Ne.symm hjk)]
  rw [hL, coordAvg_comm hjk]
  rfl

/-- `T_j T_k = T_k T_j` for independent coordinates. -/
theorem resAvg_comm {j k : ι} (hjk : j ≠ k) (W : (∀ i, α i) → ℚ) (x : ∀ i, α i) :
    resAvg res j (resAvg res k W) x = resAvg res k (resAvg res j W) x := by
  have hL : resAvg res j (resAvg res k W) x
      = coordAvg j (resFib res j (res j (x j)))
          (coordAvg k (resFib res k (res k (x k))) W) x := by
    refine coordAvg_congr fun y _ => ?_
    simp only [resAvg, Function.update_of_ne (Ne.symm hjk)]
  have hR : resAvg res k (resAvg res j W) x
      = coordAvg k (resFib res k (res k (x k)))
          (coordAvg j (resFib res j (res j (x j))) W) x := by
    refine coordAvg_congr fun z _ => ?_
    simp only [resAvg, Function.update_of_ne hjk]
  rw [hL, hR, coordAvg_comm hjk]

/-! ## 3. The two top projections -/

/-- `I − P_j`. -/
def subP (j : ι) (W : (∀ i, α i) → ℚ) : (∀ i, α i) → ℚ := fun x => W x - binAvg j W x

/-- `I − T_j`. -/
def subT (res : ∀ i, α i → ℕ) (j : ι) (W : (∀ i, α i) → ℚ) : (∀ i, α i) → ℚ :=
  fun x => W x - resAvg res j W x

/-- `Q_old = ∏_{j ∈ J} (I − P_j)`, over an ordered eligible coordinate list. -/
def Qold : List ι → ((∀ i, α i) → ℚ) → ((∀ i, α i) → ℚ)
  | [], W => W
  | j :: l, W => subP j (Qold l W)

/-- `Q₃ = ∏_{j ∈ J} (I − T_j)`, over an ordered eligible coordinate list. -/
def Q3 (res : ∀ i, α i → ℕ) : List ι → ((∀ i, α i) → ℚ) → ((∀ i, α i) → ℚ)
  | [], W => W
  | j :: l, W => subT res j (Q3 res l W)

@[simp] theorem Qold_nil (W : (∀ i, α i) → ℚ) : (Qold [] W : (∀ i, α i) → ℚ) = W := rfl

@[simp] theorem Qold_cons (j : ι) (l : List ι) (W : (∀ i, α i) → ℚ) :
    Qold (j :: l) W = subP j (Qold l W) := rfl

@[simp] theorem Q3_nil (W : (∀ i, α i) → ℚ) : Q3 res [] W = W := rfl

@[simp] theorem Q3_cons (j : ι) (l : List ι) (W : (∀ i, α i) → ℚ) :
    Q3 res (j :: l) W = subT res j (Q3 res l W) := rfl

/-- `(I − T_j)(I − P_j) = (I − T_j)`: one coordinate. -/
theorem subT_subP_self (j : ι) (W : (∀ i, α i) → ℚ) :
    subT res j (subP j W) = subT res j W := by
  funext x
  unfold subT subP
  rw [resAvg_sub, resAvg_binAvg]
  ring

/-- `(I − P_j)` and `(I − T_k)` commute for independent coordinates. -/
theorem subT_subP_comm {j k : ι} (hjk : j ≠ k) (W : (∀ i, α i) → ℚ) :
    subT res k (subP j W) = subP j (subT res k W) := by
  funext x
  unfold subT subP
  rw [resAvg_sub, binAvg_sub, binAvg_resAvg_comm hjk]
  ring

/-- `(I − P_j)` commutes with the whole residue-aware top projection over a list avoiding `j`. -/
theorem Q3_subP_comm {j : ι} {l : List ι} (hj : j ∉ l) (W : (∀ i, α i) → ℚ) :
    Q3 res l (subP j W) = subP j (Q3 res l W) := by
  induction l generalizing W with
  | nil => rfl
  | cons k l ih =>
      have hk : j ≠ k := fun h => hj (by simp [h])
      have hl : j ∉ l := fun h => hj (by simp [h])
      rw [Q3_cons, ih hl, subT_subP_comm hk, Q3_cons]

/-- **`Q₃ Q_old = Q₃`.**  The residue-aware top projection absorbs the ordinary one. -/
theorem Q3_Qold {l : List ι} (hl : l.Nodup) (W : (∀ i, α i) → ℚ) :
    Q3 res l (Qold l W) = Q3 res l W := by
  induction l generalizing W with
  | nil => rfl
  | cons j l ih =>
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      have hnd : l.Nodup := (List.nodup_cons.mp hl).2
      rw [Qold_cons, Q3_cons, Q3_subP_comm hj, ih hnd, subT_subP_self, Q3_cons]

/-! ## 4. Already removed components stay removed -/

/-- The ordinary top projection is centered under every ordinary average it removed. -/
theorem binAvg_Qold_eq_zero [∀ i, Nonempty (α i)] {k : ι} {l : List ι} (hl : l.Nodup)
    (hk : k ∈ l) (W : (∀ i, α i) → ℚ) :
    (fun x => binAvg k (Qold l W) x) = fun _ => (0 : ℚ) := by
  induction l generalizing W with
  | nil => exact absurd hk (by simp)
  | cons j l ih =>
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      have hnd : l.Nodup := (List.nodup_cons.mp hl).2
      funext x
      rcases List.mem_cons.mp hk with rfl | hk'
      · show binAvg k (subP k (Qold l W)) x = 0
        unfold subP
        rw [binAvg_sub, binAvg_idem]
        ring
      · have hne : k ≠ j := fun h => hj (h ▸ hk')
        have hzero := ih hnd hk' W
        show binAvg k (subP j (Qold l W)) x = 0
        unfold subP
        rw [binAvg_sub, binAvg_comm hne]
        have h1 : binAvg j (fun z => binAvg k (Qold l W) z) x = 0 := by
          rw [hzero]; simp
        have h2 : binAvg k (Qold l W) x = 0 := congrFun hzero x
        rw [h1, h2]
        ring

/-- The residue-aware top projection is centered under every residue-aware average it removed:
`Q₃ W` remains centered under every `T_j`, `j ∈ J`. -/
theorem resAvg_Q3_eq_zero {k : ι} {l : List ι} (hl : l.Nodup) (hk : k ∈ l)
    (W : (∀ i, α i) → ℚ) : (fun x => resAvg res k (Q3 res l W) x) = fun _ => (0 : ℚ) := by
  induction l generalizing W with
  | nil => exact absurd hk (by simp)
  | cons j l ih =>
      have hj : j ∉ l := (List.nodup_cons.mp hl).1
      have hnd : l.Nodup := (List.nodup_cons.mp hl).2
      funext x
      rcases List.mem_cons.mp hk with rfl | hk'
      · show resAvg res k (subT res k (Q3 res l W)) x = 0
        unfold subT
        rw [resAvg_sub, resAvg_idem]
        ring
      · have hne : k ≠ j := fun h => hj (h ▸ hk')
        have hzero := ih hnd hk' W
        show resAvg res k (subT res j (Q3 res l W)) x = 0
        unfold subT
        rw [resAvg_sub, resAvg_comm hne]
        have h1 : resAvg res j (fun z => resAvg res k (Q3 res l W) z) x = 0 := by
          rw [hzero]; simp
        have h2 : resAvg res k (Q3 res l W) x = 0 := congrFun hzero x
        rw [h1, h2]
        ring

end Projections

end ResidueProj

end Gate1B.R11.Frontier
