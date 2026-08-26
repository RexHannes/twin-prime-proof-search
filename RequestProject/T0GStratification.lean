import RequestProject.Main

namespace HalfSieve

open scoped BigOperators

/-- Slots whose prime label divides the shift. -/
def activeSlots (p : Fin 3 → ℕ) (h : ℕ) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => p i ∣ h)

/-- Product of exactly the active prime labels. -/
def activeProduct (p : Fin 3 → ℕ) (h : ℕ) : ℕ :=
  ∏ i ∈ activeSlots p h, p i

lemma mem_activeSlots_iff (p : Fin 3 → ℕ) (h : ℕ) (i : Fin 3) :
    i ∈ activeSlots p h ↔ p i ∣ h := by
  simp [activeSlots]

lemma outside_activeSlots_not_dvd (p : Fin 3 → ℕ) (h : ℕ) (i : Fin 3)
    (hi : i ∉ activeSlots p h) : ¬ p i ∣ h := by
  simpa [mem_activeSlots_iff] using hi

lemma activeProduct_dvd (p : Fin 3 → ℕ) (h : ℕ)
    (hprime : ∀ i, Nat.Prime (p i))
    (hinj : Function.Injective p) : activeProduct p h ∣ h := by
  rw [activeProduct]
  have hcoprime : ∀ s : Finset (Fin 3), (∀ i ∈ s, p i ∣ h) → (∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (p i) (p j)) → (∏ i ∈ s, p i) ∣ h := by
    intro s hs hdvd
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s' ha ih =>
      have hpa : p a ∣ h := hs a (Finset.mem_insert_self a s')
      have hps' : ∀ i ∈ s', p i ∣ h := fun i hi => hs i (Finset.mem_insert_of_mem hi)
      have hcop' : ∀ i ∈ s', ∀ j ∈ s', i ≠ j → Nat.Coprime (p i) (p j) := fun i hi j hj hij => hdvd i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hprod_dvd : ∏ i ∈ s', p i ∣ h := ih hps' hcop'
      have hcop_pa_prod : Nat.Coprime (p a) (∏ i ∈ s', p i) := by
        apply Nat.Coprime.prod_right
        intro i hi
        exact hdvd a (Finset.mem_insert_self a s') i (Finset.mem_insert_of_mem hi) (by
          intro rfl
          exact ha hi)
      rw [Finset.prod_insert ha]
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop_pa_prod hpa hprod_dvd
  have hdiv : ∀ i ∈ activeSlots p h, p i ∣ h := fun i hi => by simp [mem_activeSlots_iff] at hi; exact hi
  have hcop : ∀ i ∈ activeSlots p h, ∀ j ∈ activeSlots p h, i ≠ j → Nat.Coprime (p i) (p j) := by
    intro i hi j hj hij
    exact Nat.coprime_primes (hprime i) (hprime j) |>.mpr (hinj.ne hij)
  exact hcoprime _ hdiv hcop

/-- The exact active subsets occurring up to `H` form the image of the active-slot map. -/
lemma exactActiveSubset_partition (p : Fin 3 → ℕ) (H : ℕ) (S : Finset (Fin 3)) :
    S ∈ (Finset.Icc 1 H).image (activeSlots p) ↔
      ∃ h ∈ Finset.Icc 1 H, activeSlots p h = S := by
  simp [eq_comm]

lemma exactActiveSubset_unique (p : Fin 3 → ℕ) (h : ℕ) (S T : Finset (Fin 3))
    (hS : activeSlots p h = S) (hT : activeSlots p h = T) : S = T := by
  rw [← hS, ← hT]

/-- Elementary count of positive multiples in a finite interval. -/
lemma multiples_Icc_card_le (g H : ℕ) (hg : 0 < g) :
    ((Finset.Icc 1 H).filter (fun h => g ∣ h)).card ≤ H / g + 1 := by
  set S := (Finset.Icc 1 H).filter (fun h => g ∣ h) with hS_def
  have hS_sub : S ⊆ Finset.image (fun k => g * k) (Finset.Icc 1 (H / g)) := by
    intro x hx
    simp only [hS_def, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, hxH⟩, hxdiv⟩ := hx
    obtain ⟨k, rfl⟩ := hxdiv
    simp only [Finset.mem_image, Finset.mem_Icc]
    refine ⟨k, ⟨by nlinarith, ?_⟩, rfl⟩
    exact Nat.le_div_iff_mul_le hg |>.mpr (by rw [mul_comm]; exact hxH)
  have hcard_image : (Finset.image (fun k => g * k) (Finset.Icc 1 (H / g))).card ≤ (Finset.Icc 1 (H / g)).card := Finset.card_image_le
  calc S.card ≤ (Finset.image (fun k => g * k) (Finset.Icc 1 (H / g))).card := Finset.card_le_card hS_sub
    _ ≤ (Finset.Icc 1 (H / g)).card := hcard_image
    _ = H / g := Nat.card_Icc (a := 1) (b := H / g) ▸ rfl
    _ ≤ H / g + 1 := Nat.le_succ _

end HalfSieve
