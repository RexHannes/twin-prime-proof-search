/-
# Gate1B / R11 / Frontier : the principal tail, its coefficient convolution, and the
zero/one/two-large-divisor owners

Append-only module of the minimal-gap-kernel delta.

Kernel-proved here (finite / algebraic only):

* the coefficient convolution identity used by the analytic principal theorem,
  `μ(d)/φ(d)·1_{(d,r)=1} = ((μ/id) * h_r)(d)`, together with the exact local factors

  ```
  h_r(p^a) = p^{-a}                if p | r,
  h_r(p^a) = -1/(p^a (p-1))        if p ∤ r;
  ```

* the finite owner identity `λ₀ − λ₁ + λ₂ = μ` on the declared source domain (at most two
  large prime factors), and the exact principal reassembly
  `MAIN₀ − MAIN₁ + MAIN₂ = ∑_n Ω_C(n) Π(n;z_C)`.

**Not** proved here, and never inhabited: the arbitrary-log Mertens bound, the principal-tail
estimate `Π(n;z) ≪ L^{-J}` and the complete principal bound `O(x L^{-S₀-2})`.  They are recorded
as *propositions* (`PrincipalTailBound`, `CompletePrincipalBound`) to be supplied as explicit
hypotheses — external analytic input, no custom axiom.
-/
import Gate1B.R11.Frontier.CompleteDivisorFibre

namespace Gate1B.R11.Frontier

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-! ## 0. Möbius sums -/

theorem sum_moebius_real (n : ℕ) : ∑ d ∈ n.divisors, (μ d : ℝ) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f n) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  by_cases hn1 : n = 1
  · subst hn1; simp
  · rw [if_neg hn1]
    rw [if_neg hn1] at h
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h

/-! ## 1. The three arithmetic functions -/

/-- `d ↦ μ(d)/d`. -/
noncomputable def muDivId : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else (μ d : ℝ) / (d : ℝ), by simp⟩

/-- `d ↦ 1/d`. -/
noncomputable def oneDivId : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else 1 / (d : ℝ), by simp⟩

/-- `d ↦ μ(d)/φ(d)·1_{gcd(d,r)=1}`, the principal coefficient. -/
noncomputable def muDivPhi (r : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun d => if d = 0 then 0 else
    if Nat.gcd d r = 1 then (μ d : ℝ) / (Nat.totient d : ℝ) else 0, by simp⟩

/-- The local factor function `h_r := (1/id) * (μ/φ · 1_{(·,r)=1})`. -/
noncomputable def hLocal (r : ℕ) : ArithmeticFunction ℝ := oneDivId * muDivPhi r

/-! ## 2. The Dirichlet inverse of `μ/id` -/

theorem muDivId_mul_oneDivId : muDivId * oneDivId = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (f := fun i j => muDivId i * oneDivId j)]
  have hn0 : n ≠ 0 := hn.ne'
  have key : ∀ d ∈ n.divisors, muDivId d * oneDivId (n / d) = (1 / (n : ℝ)) * (μ d : ℝ) := by
    intro d hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    have hnd0 : n / d ≠ 0 := by
      have := Nat.div_pos (Nat.le_of_dvd hn hdvd) (Nat.pos_of_ne_zero hd0)
      omega
    have hcast : ((n / d : ℕ) : ℝ) = (n : ℝ) / (d : ℝ) := by
      rw [Nat.cast_div hdvd (by exact_mod_cast hd0)]
    simp only [muDivId, oneDivId, ArithmeticFunction.coe_mk, if_neg hd0, if_neg hnd0, hcast]
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn0
    field_simp
  rw [Finset.sum_congr rfl key, ← Finset.mul_sum, sum_moebius_real,
    ArithmeticFunction.one_apply]
  by_cases hn1 : n = 1
  · subst hn1; norm_num
  · simp [hn1]

/-- **Principal coefficient convolution.**  `μ(d)/φ(d)·1_{(d,r)=1} = ((μ/id) * h_r)(d)`. -/
theorem muDivId_mul_hLocal (r : ℕ) : muDivId * hLocal r = muDivPhi r := by
  rw [hLocal, ← mul_assoc, muDivId_mul_oneDivId, one_mul]

/-- Pointwise form of the convolution identity. -/
theorem muDivPhi_apply_eq_conv (r d : ℕ) :
    (if d = 0 then 0 else if Nat.gcd d r = 1 then (μ d : ℝ) / (Nat.totient d : ℝ) else 0)
      = (muDivId * hLocal r) d := by
  rw [muDivId_mul_hLocal]
  rfl

/-! ## 3. The local factors -/

private theorem sum_range_two_of_vanishing {F : ℕ → ℝ} (h : ∀ j, 2 ≤ j → F j = 0) :
    ∀ a, 1 ≤ a → ∑ j ∈ Finset.range (a + 1), F j = F 0 + F 1 := by
  intro a
  induction a with
  | zero => intro h0; omega
  | succ n ih =>
      intro _
      rw [Finset.sum_range_succ]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · rw [ih hn, h (n + 1) (by omega), add_zero]

theorem hLocal_prime_pow {r p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    hLocal r (p ^ a) =
      (1 / (p : ℝ) ^ a) + (1 / (p : ℝ) ^ (a - 1)) * muDivPhi r p := by
  have hp0 : (p : ℝ) ≠ 0 := by
    have := hp.pos; positivity
  rw [hLocal, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal' (f := fun i j => oneDivId i * muDivPhi r j)]
  rw [Nat.sum_divisors_prime_pow hp
      (f := fun d => oneDivId (p ^ a / d) * muDivPhi r d)]
  have hvanish : ∀ j, 2 ≤ j →
      oneDivId (p ^ a / p ^ j) * muDivPhi r (p ^ j) = 0 := by
    intro j hj
    have hmu : (μ (p ^ j) : ℤ) = 0 := by
      refine ArithmeticFunction.moebius_eq_zero_of_not_squarefree ?_
      intro hsq
      have : p * p ∣ p ^ j := by
        calc p * p = p ^ 2 := by ring
          _ ∣ p ^ j := pow_dvd_pow p hj
      exact hp.one_lt.ne' (Nat.isUnit_iff.1 (hsq p this))
    have hpj0 : p ^ j ≠ 0 := pow_ne_zero _ hp.ne_zero
    simp only [muDivPhi, ArithmeticFunction.coe_mk, if_neg hpj0]
    by_cases hg : Nat.gcd (p ^ j) r = 1
    · rw [if_pos hg]
      have : ((μ (p ^ j) : ℤ) : ℝ) = 0 := by exact_mod_cast hmu
      rw [this]
      simp
    · rw [if_neg hg]; ring
  rw [sum_range_two_of_vanishing hvanish a ha]
  have h0 : oneDivId (p ^ a / p ^ 0) * muDivPhi r (p ^ 0) = 1 / (p : ℝ) ^ a := by
    have hpa0 : p ^ a ≠ 0 := pow_ne_zero _ hp.ne_zero
    simp only [pow_zero, Nat.div_one, oneDivId, muDivPhi, ArithmeticFunction.coe_mk,
      if_neg hpa0]
    norm_num
  have h1 : oneDivId (p ^ a / p ^ 1) * muDivPhi r (p ^ 1)
      = (1 / (p : ℝ) ^ (a - 1)) * muDivPhi r p := by
    have hdiv : p ^ a / p ^ 1 = p ^ (a - 1) := Nat.pow_div ha hp.pos
    have hpa0 : p ^ (a - 1) ≠ 0 := pow_ne_zero _ hp.ne_zero
    rw [hdiv, pow_one]
    simp only [oneDivId, ArithmeticFunction.coe_mk, if_neg hpa0]
    push_cast
    ring
  rw [h0, h1]

/-- The local factor at a prime dividing `r`. -/
theorem hLocal_prime_pow_dvd {r p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hpr : p ∣ r) :
    hLocal r (p ^ a) = 1 / (p : ℝ) ^ a := by
  have hg : Nat.gcd p r ≠ 1 := by
    rw [Nat.gcd_eq_left hpr]
    exact hp.one_lt.ne'
  have hz : muDivPhi r p = 0 := by
    simp only [muDivPhi, ArithmeticFunction.coe_mk, if_neg hp.ne_zero, if_neg hg]
  rw [hLocal_prime_pow hp ha, hz, mul_zero, add_zero]

/-- The local factor at a prime not dividing `r`. -/
theorem hLocal_prime_pow_not_dvd {r p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) (hpr : ¬ p ∣ r) :
    hLocal r (p ^ a) = -(1 / ((p : ℝ) ^ a * ((p : ℝ) - 1))) := by
  have hg : Nat.gcd p r = 1 := (Nat.Prime.coprime_iff_not_dvd hp).2 hpr
  have hval : muDivPhi r p = -(1 / ((p : ℝ) - 1)) := by
    simp only [muDivPhi, ArithmeticFunction.coe_mk, if_neg hp.ne_zero, if_pos hg,
      ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp]
    have : ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 := by
      have := hp.one_lt
      push_cast [Nat.cast_sub (by omega : 1 ≤ p)]
      ring
    rw [this]
    push_cast
    ring
  have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  have hpne : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  rw [hLocal_prime_pow hp ha, hval]
  have hsplit : (p : ℝ) ^ a = (p : ℝ) ^ (a - 1) * (p : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [hsplit]
  field_simp
  ring

/-! ## 4. The principal tail and the reduced-residue average -/

/-- `Π(n;z) = ∑_{z<d≤n+2, (d,2n)=1} μ(d)/φ(d) log((n+2)/d)`, over a declared finite `d`-range. -/
noncomputable def piTail (Ds : Finset ℕ) (z : ℝ) (n : ℕ) : ℝ :=
  ∑ d ∈ Ds, (if z < (d : ℝ) ∧ d ≤ n + 2 ∧ Nat.gcd d (2 * n) = 1 then
    (μ d : ℝ) / (Nat.totient d : ℝ) * Real.log (((n + 2 : ℕ) : ℝ) / (d : ℝ)) else 0)

/-- `A_r(Y) = ∑_{d ≤ Y, (d,r)=1} μ(d)/φ(d)`. -/
noncomputable def Ares (r Y : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 Y, (if Nat.gcd d r = 1 then (μ d : ℝ) / (Nat.totient d : ℝ) else 0)

/-- `A_r(Y)` is the partial sum of the convolution `(μ/id) * h_r`: an exact finite restatement. -/
theorem Ares_eq_conv (r Y : ℕ) :
    Ares r Y = ∑ d ∈ Finset.Icc 1 Y, (muDivId * hLocal r) d := by
  refine Finset.sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := by
    rw [Finset.mem_Icc] at hd; omega
  rw [← muDivPhi_apply_eq_conv r d, if_neg hd0]

/-! ## 5. The zero/one/two-large-divisor owners -/

/-- The number of prime factors of `d` above the threshold `z`. -/
noncomputable def bigPrimeCount (z : ℝ) (d : ℕ) : ℕ :=
  (d.primeFactors.filter (fun p : ℕ => z < (p : ℝ))).card

/-- The owner coefficients of the zero/one/two-large-divisor classes. -/
noncomputable def lambdaClass (z : ℝ) (k : ℕ) (d : ℕ) : ℝ :=
  if bigPrimeCount z d = k then (-1 : ℝ) ^ k * (μ d : ℝ) else 0

/-- **Finite owner identity.**  On the declared source domain (at most two large prime factors)
`λ₀ − λ₁ + λ₂ = μ`. -/
theorem lambda_owner_identity {z : ℝ} {d : ℕ} (h : bigPrimeCount z d ≤ 2) :
    lambdaClass z 0 d - lambdaClass z 1 d + lambdaClass z 2 d = (μ d : ℝ) := by
  unfold lambdaClass
  interval_cases hc : bigPrimeCount z d <;> norm_num

/-- The principal object of the `k`-th large-divisor class. -/
noncomputable def mainClass (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z : ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Ns, Ω n * ∑ d ∈ Ds,
    (if bigPrimeCount z d = k then
      (if z < (d : ℝ) ∧ d ≤ n + 2 ∧ Nat.gcd d (2 * n) = 1 then
        (-1 : ℝ) ^ k * ((μ d : ℝ) / (Nat.totient d : ℝ)) *
          Real.log (((n + 2 : ℕ) : ℝ) / (d : ℝ)) else 0)
     else 0)

/-- **Exact principal reassembly** (conditional finite-sum/source identity):
`MAIN₀ − MAIN₁ + MAIN₂ = ∑_n Ω_C(n) Π(n;z_C)` on the declared source domain. -/
theorem main_reassembly {Ds Ns : Finset ℕ} {Ω : ℕ → ℝ} {z : ℝ}
    (hdom : ∀ d ∈ Ds, bigPrimeCount z d ≤ 2) :
    mainClass Ds Ns Ω z 0 - mainClass Ds Ns Ω z 1 + mainClass Ds Ns Ω z 2
      = ∑ n ∈ Ns, Ω n * piTail Ds z n := by
  unfold mainClass piTail
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc := hdom d hd
  by_cases hguard : z < (d : ℝ) ∧ d ≤ n + 2 ∧ Nat.gcd d (2 * n) = 1
  · simp only [if_pos hguard]
    rcases (by omega : bigPrimeCount z d = 0 ∨ bigPrimeCount z d = 1 ∨ bigPrimeCount z d = 2)
      with h | h | h <;> simp [h]
  · simp [hguard]

/-! ## 6. The analytic inputs, as propositions only -/

/-- The principal-tail estimate `Π(n;z) ≪ L^{-J}`.  **External analytic input**: a proposition,
never inhabited here, never an axiom. -/
def PrincipalTailBound (Ds : Finset ℕ) (z : ℝ) (Ns : Finset ℕ) (L : ℝ) (J : ℝ) (C : ℝ) : Prop :=
  ∀ n ∈ Ns, |piTail Ds z n| ≤ C * L ^ (-J)

/-- The complete principal bound `O(x L^{-S₀-2})`.  **External analytic input**: a proposition,
never inhabited here, never an axiom. -/
def CompletePrincipalBound (Ds Ns : Finset ℕ) (Ω : ℕ → ℝ) (z x L S0 C : ℝ) : Prop :=
  |mainClass Ds Ns Ω z 0 - mainClass Ds Ns Ω z 1 + mainClass Ds Ns Ω z 2|
    ≤ C * x * L ^ (-S0 - 2)

/-- The *only* legal use of the analytic inputs: if the principal-tail bound is supplied on the
declared domain, it transports through the exact reassembly. -/
theorem complete_principal_of_weighted_bound {Ds Ns : Finset ℕ} {Ω : ℕ → ℝ} {z L C x S0 : ℝ}
    (hdom : ∀ d ∈ Ds, bigPrimeCount z d ≤ 2)
    (hbound : |∑ n ∈ Ns, Ω n * piTail Ds z n| ≤ C * x * L ^ (-S0 - 2)) :
    CompletePrincipalBound Ds Ns Ω z x L S0 C := by
  unfold CompletePrincipalBound
  rw [main_reassembly hdom]
  exact hbound

end Gate1B.R11.Frontier
