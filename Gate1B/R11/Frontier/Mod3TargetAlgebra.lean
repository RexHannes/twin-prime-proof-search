/-
# Gate1B / R11 / Frontier : the modulo-3 selector algebra and the direct-residue firewall

Append-only module of the residue-aware delta.  **Exact finite algebra only.**

Banked here:

* the residue-restricted long coefficients `b₁, b₂` and the exact selector identity

  ```
  1_{p ≡ a (3)} · b(R)  =  b_{−a}(R) + I₃(pR) · ( b_a(R) − b_{−a}(R) )      (a ∈ {1,2}),
  ```

  valid for every `p, R` prime to `3` — where `I₃(n) = 1_{n ≡ −2 (3)}` is the *same* selected
  congruence indicator as in the modulus-lifting module;
* the equivalent `χ₃` form, with `χ₃` completely multiplicative on the units;
* the record that the modulo-3 caller is a **derived** caller, obtained from the modulus-lifting
  identity at `h = 3`, and not a reversal of the direct-residue warning;
* the **direct-residue firewall**: an explicit finite countermodel in which conditioning on one
  residue class destroys an exact mean-zero relation.

No analytic prime asymptotic and no arbitrary-log saving is proved here; the analytic caller is
carried by the never-inhabited interface `Mod3CenteredCaller`.
-/
import Gate1B.R11.Frontier.ResidueModulusLift

namespace Gate1B.R11.Frontier

open Finset

/-! ## 1. Residue selectors -/

/-- The residue selector `1_{n ≡ c (mod 3)}`. -/
def indMod3 (c n : ℕ) : ℚ := if n % 3 = c then 1 else 0

/-- The residue-restricted long coefficient `b_c(R) = 1_{R ≡ c (3)} · b(R)`. -/
def bRes (b : ℕ → ℚ) (c R : ℕ) : ℚ := indMod3 c R * b R

/-- The selected congruence indicator at the lifted modulus `3`:  `I₃(n) = 1_{n ≡ −2 (3)}`. -/
def I3 (n : ℕ) : ℚ := deltaSel 3 n

theorem I3_eq_one_iff (n : ℕ) : I3 n = 1 ↔ n % 3 = 1 := by
  unfold I3 deltaSel
  constructor
  · intro h
    by_cases hd : (3 : ℕ) ∣ n + 2
    · omega
    · rw [if_neg hd] at h; norm_num at h
  · intro h
    rw [if_pos (by omega : (3 : ℕ) ∣ n + 2)]

theorem I3_eq_zero_iff (n : ℕ) : I3 n = 0 ↔ n % 3 ≠ 1 := by
  unfold I3 deltaSel
  constructor
  · intro h hn
    rw [if_pos (by omega : (3 : ℕ) ∣ n + 2)] at h
    norm_num at h
  · intro h
    rw [if_neg (by omega : ¬ (3 : ℕ) ∣ n + 2)]

/-! ## 2. The exact selector identity -/

/-- **The modulo-3 selector identity.**  For `a ∈ {1,2}` and `p, R` prime to `3`:

```
1_{p ≡ a (3)} b(R) = b_{3−a}(R) + I₃(pR) ( b_a(R) − b_{3−a}(R) ) .
```

Exact finite algebra: no hypothesis on `b`, no analytic content. -/
theorem mod3_selector_identity (b : ℕ → ℚ) (a p R : ℕ) (ha : a = 1 ∨ a = 2)
    (hp : p % 3 ≠ 0) (hR : R % 3 ≠ 0) :
    indMod3 a p * b R = bRes b (3 - a) R + I3 (p * R) * (bRes b a R - bRes b (3 - a) R) := by
  have hmul : (p * R) % 3 = (p % 3) * (R % 3) % 3 := Nat.mul_mod p R 3
  have hdvd : ((3 : ℕ) ∣ p * R + 2) ↔ (p * R) % 3 = 1 := by omega
  have hp3 : p % 3 = 1 ∨ p % 3 = 2 := by omega
  have hR3 : R % 3 = 1 ∨ R % 3 = 2 := by omega
  simp only [bRes, I3, deltaSel, indMod3, hdvd, hmul]
  rcases ha with rfl | rfl <;> rcases hp3 with h1 | h1 <;> rcases hR3 with h2 | h2 <;>
    simp [h1, h2]

/-- The mod-3 quadratic character, as an exact rational-valued function. -/
def chi3 (n : ℕ) : ℚ := if n % 3 = 1 then 1 else if n % 3 = 2 then -1 else 0

/-- `χ₃` is completely multiplicative. -/
theorem chi3_mul (m n : ℕ) : chi3 (m * n) = chi3 m * chi3 n := by
  have hmul : (m * n) % 3 = (m % 3) * (n % 3) % 3 := Nat.mul_mod m n 3
  have hm : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  have hn : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  unfold chi3
  rcases hm with h1 | h1 | h1 <;> rcases hn with h2 | h2 | h2 <;> simp [hmul, h1, h2]

/-- The selector in `χ₃` form on the units: `1_{n ≡ 1 (3)} = (1 + χ₃(n))/2`. -/
theorem indMod3_one_eq_chi3 (n : ℕ) (hn : n % 3 ≠ 0) : indMod3 1 n = (1 + chi3 n) / 2 := by
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  simp only [indMod3, chi3]
  rcases h with h | h <;> simp [h]

/-- The selector in `χ₃` form on the units: `1_{n ≡ 2 (3)} = (1 − χ₃(n))/2`. -/
theorem indMod3_two_eq_chi3 (n : ℕ) (hn : n % 3 ≠ 0) : indMod3 2 n = (1 - chi3 n) / 2 := by
  have h : n % 3 = 1 ∨ n % 3 = 2 := by omega
  simp only [indMod3, chi3]
  rcases h with h | h <;> simp [h]

/-- **The `χ₃` form of the selector identity.**  For `a ∈ {1,2}` and `p` prime to `3`:
`1_{p ≡ a (3)} b(R) = ((1 + χ₃(a)χ₃(p))/2) · b(R)`. -/
theorem mod3_selector_chi3_form (b : ℕ → ℚ) (a p R : ℕ) (ha : a = 1 ∨ a = 2) (hp : p % 3 ≠ 0) :
    indMod3 a p * b R = ((1 + chi3 a * chi3 p) / 2) * b R := by
  have h : p % 3 = 1 ∨ p % 3 = 2 := by omega
  unfold indMod3 chi3
  rcases ha with rfl | rfl <;> rcases h with h | h <;> simp [h]

/-! ## 3. The modulo-3 caller is a *derived* caller -/

/-- **The modulo-3 centered caller is derived by modulus lifting.**  Applying the selected
congruence indicator `I₃` to the centered kernel at modulus `d` produces the centered kernel at
the lifted modulus `3d` *plus the local principal correction* — it is not a free operation. -/
theorem mod3_caller_via_modulus_lifting {d : ℕ} (hcop : Nat.Coprime 3 d) (n : ℕ) :
    I3 n * centeredSel d n = centeredSel (3 * d) n + LocalPrincipalCorrection 3 d n :=
  modulus_lift_identity hcop n

/-- **`Mod3CenteredCaller`** — the external / conditional analytic interface for the modulo-3
centered caller.  Never inhabited here, and not an axiom. -/
structure Mod3CenteredCaller (lam : ℕ → ℚ) (Ds Ns : Finset ℕ) (a : ℕ → ℚ)
    (x L S0 C : ℝ) : Prop where
  /-- The claimed analytic saving for the residue-restricted (lifted) consumer. -/
  saving : |((selectedConsumer lam Ds Ns (fun n => I3 n * a n) : ℚ) : ℝ)| ≤ C * x * L ^ (-S0)

/-! ## 4. The direct-residue firewall -/

/-- An exact finite mean-zero relation on a finite window. -/
def MeanZeroOn (S : Finset ℕ) (c : ℕ → ℚ) : Prop := ∑ n ∈ S, c n = 0

/-- The finite countermodel coefficient: `+1` at `1`, `−1` at `2`, `0` elsewhere. -/
def residueCounterCoeff (n : ℕ) : ℚ := if n = 1 then 1 else if n = 2 then -1 else 0

/-- **Direct-residue firewall.**  Conditioning on one residue class modulo `3` can destroy an
exact mean-zero relation: the displayed finite coefficient has total mass `0` on `[0,6)` but mass
`1` on the class `n ≡ 1 (3)`. -/
theorem residue_restriction_can_destroy_mean_zero :
    ∃ (S : Finset ℕ) (c : ℕ → ℚ), MeanZeroOn S c ∧ ¬ MeanZeroOn (S.filter (fun n => n % 3 = 1)) c := by
  refine ⟨Finset.range 6, residueCounterCoeff, ?_, ?_⟩
  · unfold MeanZeroOn residueCounterCoeff
    norm_num [Finset.sum_range_succ]
  · have hfil : (Finset.range 6).filter (fun n => n % 3 = 1) = {1, 4} := by decide
    unfold MeanZeroOn residueCounterCoeff
    rw [hfil]
    norm_num

/-- Hence: "prime coefficient restricted to `p ≡ 1 (3)`" is **not** automatically an ordinary
mean-zero (Siegel–Walfisz type) coefficient of the original caller. -/
theorem restricted_residue_not_automatically_meanZero :
    ¬ ∀ (S : Finset ℕ) (c : ℕ → ℚ), MeanZeroOn S c → MeanZeroOn (S.filter (fun n => n % 3 = 1)) c := by
  obtain ⟨S, c, h1, h2⟩ := residue_restriction_can_destroy_mean_zero
  exact fun h => h2 (h S c h1)

end Gate1B.R11.Frontier
