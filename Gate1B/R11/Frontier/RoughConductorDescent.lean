/-
# Gate1B / R11 / Frontier : rough-conductor finite combinatorics

**No analytic input, and in particular no custom large-sieve axiom.**  What is formalised here
is exactly the finite/combinatorial part of the rough-conductor reduction:

1. Möbius inclusion–exclusion `1_{gcd(n,r)=1} = ∑_{e ∣ gcd(n,r)} μ(e)`;
2. the exact **conductor descent** of a twisted sum with explicit interval support,
   ```
   ∑_{n < T} a_n χ*(n) 1_{(n,r)=1}
     = ∑_{e ∣ r} μ(e) χ*(e) ∑_{m : e m < T} a_{e m} χ*(m),
   ```
   for any completely multiplicative `χ*`;
3. the **imprimitive character factorisation** in Mathlib's `DirichletCharacter` framework:
   for `q = f · r` with `gcd(f, r) = 1` and `χ = changeLevel χ*`,
   `χ(n) = χ*(n) · 1_{gcd(n,r)=1}`;
4. the two combined: the finite conductor descent for a genuine imprimitive Dirichlet character.

The library owner for the *analytic* step (the primitive multiplicative large sieve) is **not**
supplied here; see `Gate1B.R11.Frontier.RoughModulusInterface`, where it appears as an explicit
hypothesis and never as an axiom.
-/
import Mathlib

namespace Gate1B.R11.Frontier

open ArithmeticFunction Finset

/-! ## 1. Inclusion–exclusion -/

/-- `∑_{e ∣ n} μ(e) = 1_{n = 1}`. -/
theorem sum_moebius_divisors (n : ℕ) :
    ∑ e ∈ n.divisors, (moebius e : ℤ) = if n = 1 then 1 else 0 := by
  have h2 := congrArg (fun f : ArithmeticFunction ℤ => f n)
    ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h2
  exact h2

/-- **INCLUSION–EXCLUSION** `1_{gcd(n,r)=1} = ∑_{e ∣ gcd(n,r)} μ(e)` (over `ℂ`). -/
theorem indicator_coprime_eq_sum_moebius (n r : ℕ) :
    ((if Nat.gcd n r = 1 then 1 else 0 : ℂ)) = ∑ e ∈ (Nat.gcd n r).divisors, (moebius e : ℂ) := by
  have hcast : ((∑ e ∈ (Nat.gcd n r).divisors, moebius e : ℤ) : ℂ)
      = ((if Nat.gcd n r = 1 then (1 : ℤ) else 0 : ℤ) : ℂ) := by
    rw [sum_moebius_divisors]
  push_cast at hcast
  rw [← hcast]

/-! ## 2. The exact conductor descent, with explicit interval support -/

/-- **CONDUCTOR DESCENT (finite, exact).**  For any completely multiplicative `χ*`,
`∑_{n<T} a_n χ*(n) 1_{(n,r)=1} = ∑_{e ∣ r} μ(e) χ*(e) ∑_{m : e m < T} a_{e m} χ*(m)`.
The inner interval `{m : e m < T}` is the explicit representation of `m < T/e`. -/
theorem conductor_descent (r T : ℕ) (hr : r ≠ 0) (a : ℕ → ℂ) (chiStar : ℕ → ℂ)
    (hmul : ∀ x y, chiStar (x * y) = chiStar x * chiStar y) :
    ∑ n ∈ Finset.range T, a n * chiStar n * (if Nat.gcd n r = 1 then 1 else 0)
      = ∑ e ∈ r.divisors, (moebius e : ℂ) * chiStar e *
          ∑ m ∈ (Finset.range T).filter (fun m => e * m < T), a (e * m) * chiStar m := by
  have hdiv : ∀ n : ℕ, (Nat.gcd n r).divisors = r.divisors.filter (· ∣ n) := by
    intro n
    ext e
    simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩; exact ⟨⟨h2, hr⟩, h1⟩
    · rintro ⟨⟨h2, -⟩, h1⟩
      exact ⟨⟨h1, h2⟩, Nat.gcd_ne_zero_right hr⟩
  calc ∑ n ∈ Finset.range T, a n * chiStar n * (if Nat.gcd n r = 1 then 1 else 0)
      = ∑ n ∈ Finset.range T, ∑ e ∈ r.divisors,
          (if e ∣ n then (moebius e : ℂ) * (a n * chiStar n) else 0) := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [indicator_coprime_eq_sum_moebius n r, hdiv n, Finset.sum_filter, Finset.mul_sum]
        exact Finset.sum_congr rfl fun e _ => by split <;> ring
    _ = ∑ e ∈ r.divisors, ∑ n ∈ (Finset.range T).filter (fun n => e ∣ n),
          (moebius e : ℂ) * (a n * chiStar n) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun e _ => (Finset.sum_filter _ _).symm
    _ = ∑ e ∈ r.divisors, (moebius e : ℂ) * chiStar e *
          ∑ m ∈ (Finset.range T).filter (fun m => e * m < T), a (e * m) * chiStar m := by
        refine Finset.sum_congr rfl fun e he => ?_
        have he0 : e ≠ 0 := by
          rcases Nat.mem_divisors.mp he with ⟨hdvd, -⟩
          rintro rfl
          exact hr (Nat.eq_zero_of_zero_dvd hdvd)
        rw [Finset.mul_sum]
        refine Finset.sum_nbij' (fun n => n / e) (fun m => e * m) ?_ ?_ ?_ ?_ ?_
        · intro n hn
          simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
          obtain ⟨hlt, hdvd⟩ := hn
          have hc : e * (n / e) = n := Nat.mul_div_cancel' hdvd
          exact ⟨lt_of_le_of_lt (Nat.div_le_self n e) hlt, by rw [hc]; exact hlt⟩
        · intro m hm
          simp only [Finset.mem_filter, Finset.mem_range] at hm ⊢
          exact ⟨hm.2, Dvd.intro _ rfl⟩
        · intro n hn
          simp only [Finset.mem_filter] at hn
          exact Nat.mul_div_cancel' hn.2
        · intro m _
          exact Nat.mul_div_cancel_left m (Nat.pos_of_ne_zero he0)
        · intro n hn
          simp only [Finset.mem_filter] at hn
          have hrec : e * (n / e) = n := Nat.mul_div_cancel' hn.2
          have hchi : chiStar n = chiStar e * chiStar (n / e) := by rw [← hmul, hrec]
          rw [hrec, hchi]
          ring

/-! ## 3. Imprimitive character factorisation -/

/-- A character lifted from level `f` to level `q` is the lifted value times the unit indicator. -/
theorem changeLevel_natCast {f q : ℕ} [NeZero q] (hfq : f ∣ q)
    (chiStar : DirichletCharacter ℂ f) (n : ℕ) :
    (DirichletCharacter.changeLevel hfq chiStar) (n : ZMod q)
      = chiStar (n : ZMod f) * (if IsUnit ((n : ZMod q)) then 1 else 0) := by
  by_cases hu : IsUnit ((n : ZMod q))
  · obtain ⟨u, hu'⟩ := hu
    rw [if_pos ⟨u, hu'⟩, mul_one, ← hu',
      DirichletCharacter.changeLevel_eq_cast_of_dvd chiStar hfq u, hu']
    congr 1
    exact ZMod.cast_natCast hfq n
  · rw [if_neg hu, mul_zero, MulChar.map_nonunit _ hu]

/-- **IMPRIMITIVE CHARACTER DESCENT.**  For `q = f · r` with `gcd(f, r) = 1` and `χ` induced by
the character `χ*` of level `f`, `χ(n) = χ*(n) · 1_{gcd(n,r)=1}`. -/
theorem imprimitive_factorisation {f r : ℕ} (hf : f ≠ 0) (hr : r ≠ 0)
    (chiStar : DirichletCharacter ℂ f) (n : ℕ) :
    haveI : NeZero (f * r) := ⟨Nat.mul_ne_zero hf hr⟩
    (DirichletCharacter.changeLevel (Dvd.intro r rfl) chiStar) (n : ZMod (f * r))
      = chiStar (n : ZMod f) * (if Nat.gcd n r = 1 then 1 else 0) := by
  haveI : NeZero (f * r) := ⟨Nat.mul_ne_zero hf hr⟩
  haveI : NeZero f := ⟨hf⟩
  rw [changeLevel_natCast]
  by_cases hnf : Nat.Coprime n f
  · have hunit : IsUnit ((n : ZMod (f * r))) ↔ Nat.gcd n r = 1 := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right]
      exact ⟨fun h => h.2, fun h => ⟨hnf, h⟩⟩
    by_cases hcop : Nat.gcd n r = 1
    · rw [if_pos (hunit.2 hcop), if_pos hcop]
    · rw [if_neg (fun h => hcop (hunit.1 h)), if_neg hcop]
  · have hzero : chiStar (n : ZMod f) = 0 := by
      refine MulChar.map_nonunit _ ?_
      rw [ZMod.isUnit_iff_coprime]
      exact hnf
    rw [hzero, zero_mul, zero_mul]

/-! ## 4. Conductor descent for a genuine imprimitive Dirichlet character -/

/-- **FINITE CONDUCTOR DESCENT for a Dirichlet character.**  With `q = f · r`, `χ` induced from
level `f`, the twisted sum over the interval `[0, T)` descends to the primitive character with an
explicit `μ`-weighted sum over `e ∣ r` and explicit inner interval support. -/
theorem dirichlet_conductor_descent {f r : ℕ} (hf : f ≠ 0) (hr : r ≠ 0)
    (chiStar : DirichletCharacter ℂ f) (a : ℕ → ℂ) (T : ℕ) :
    haveI : NeZero (f * r) := ⟨Nat.mul_ne_zero hf hr⟩
    ∑ n ∈ Finset.range T, a n * (DirichletCharacter.changeLevel (Dvd.intro r rfl) chiStar)
        (n : ZMod (f * r))
      = ∑ e ∈ r.divisors, (moebius e : ℂ) * chiStar (e : ZMod f) *
          ∑ m ∈ (Finset.range T).filter (fun m => e * m < T),
            a (e * m) * chiStar (m : ZMod f) := by
  haveI : NeZero (f * r) := ⟨Nat.mul_ne_zero hf hr⟩
  have hmul : ∀ x y : ℕ, chiStar ((x * y : ℕ) : ZMod f)
      = chiStar (x : ZMod f) * chiStar (y : ZMod f) := by
    intro x y
    push_cast
    exact map_mul _ _ _
  have hstep : ∀ n ∈ Finset.range T,
      a n * (DirichletCharacter.changeLevel (Dvd.intro r rfl) chiStar) (n : ZMod (f * r))
        = a n * chiStar (n : ZMod f) * (if Nat.gcd n r = 1 then 1 else 0) := by
    intro n _
    rw [imprimitive_factorisation hf hr chiStar n]
    ring
  rw [Finset.sum_congr rfl hstep]
  exact conductor_descent r T hr a (fun n => chiStar (n : ZMod f)) hmul

end Gate1B.R11.Frontier
