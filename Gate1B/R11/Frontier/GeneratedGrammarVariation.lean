/-
# Gate1B / R11 / Frontier : amplitude and finite prime-path variation for the generated grammar

Append-only module of the generated-grammar delta.  **Finite algebra only** — no analytic
conclusion (no `x L^{-A}`) is kernel-proved anywhere.

The repository's actual grammar is reused: `GenAtom`, `GenExpr`, `semExpr`, `cost`, `dconv` from
`V11FMPerronGrammar` / `V11GeneratedExpression`.

Banked here:

* the **amplitude budget** `a(E) = cost 2^r E` with its structural recursion
  (`a(f+g) ≤ a f + a g`, `a(f·g) ≤ a f · a g`, `a(c·f) ≤ ‖c‖ a f`, `a(f ∗ g) ≤ 2^r a f a g`)
  and its soundness (`‖semExpr E n‖ ≤ a(E)` on the declared window);
* the **finite prime-path variation** `pathVar` and the scaled functionals
  `scaledVar ps e f = pathVar ps (p ↦ f (p·e))`, `divVar ps R f = ∑_{e | R} scaledVar ps e f`,
  with the exact combinatorial inequalities for constants, sharp intervals, monotone ramps,
  products, sums, scalar multiplication and convolution;
* the structural bound `v(E) ≤ a(E) · T(E)` for the declared variation-controlled sub-grammar;
* the **zero-extension cost** at prime divisors of `R` (`≤ 2 ω(R) a(E)`), specialised to the
  eleven-prime source;
* the **evaluation-point firewall**: the unshifted predecessor variation theorem does *not*
  imply anything at the shifted point `pR + 2`.

*Audit note.*  The research bank states the convolution constant as `2^{r-1}`.  What is
kernel-proved here is the sharp divisor-sum form `scaledVar_dconv_le` (no constant loss at all)
and the corollary with constant `2^r`; the literal `2^{r-1}` is **not** proved with this
normalisation and is not claimed.
-/
import Gate1B.R11.Frontier.GeneratedGrammarFreshPrime

namespace Gate1B.R11.Frontier

open Finset TwinPrimeProject.Gate1BV11

/-! ## 1. The amplitude budget -/

/-- The amplitude budget of a generated expression at squarefree rank `r`: the repository's
deterministic `cost` with divisor bound `2^r`. -/
noncomputable def ampBudget (r : ℕ) (E : GenExpr) : ℝ := cost ((2 : ℝ) ^ r) E

theorem ampBudget_nonneg (r : ℕ) (E : GenExpr) : 0 ≤ ampBudget r E :=
  cost_nonneg (by positivity) E

theorem ampBudget_atom (r : ℕ) (a : GenAtom) : ampBudget r (.atom a) = 1 := rfl

theorem ampBudget_add_le (r : ℕ) (f g : GenExpr) :
    ampBudget r (.add f g) ≤ ampBudget r f + ampBudget r g := le_of_eq rfl

theorem ampBudget_mul_le (r : ℕ) (f g : GenExpr) :
    ampBudget r (.mul f g) ≤ ampBudget r f * ampBudget r g := le_of_eq rfl

theorem ampBudget_smul_le (r : ℕ) (c : ℂ) (f : GenExpr) :
    ampBudget r (.smul c f) ≤ ‖c‖ * ampBudget r f := le_of_eq rfl

theorem ampBudget_conv_le (r : ℕ) (f g : GenExpr) :
    ampBudget r (.conv f g) ≤ (2 : ℝ) ^ r * (ampBudget r f * ampBudget r g) := le_of_eq rfl

/-- **Soundness of the amplitude budget** on the declared window. -/
theorem norm_semExpr_le_ampBudget {N r : ℕ} (hN : 1 ≤ N)
    (hD : ∀ n ≤ N, (n.divisors.card : ℝ) ≤ (2 : ℝ) ^ r) (E : GenExpr) (hE : E.Admissible)
    {n : ℕ} (hn : n ≤ N) : ‖semExpr E n‖ ≤ ampBudget r E :=
  norm_semExpr_le_cost N hN ((2 : ℝ) ^ r) hD E hE n hn

/-! ## 2. The finite prime-path variation -/

/-- The total variation of `f` along a finite ordered path of evaluation parameters. -/
noncomputable def pathVar : List ℕ → (ℕ → ℂ) → ℝ
  | [], _ => 0
  | [_], _ => 0
  | a :: b :: t, f => ‖f b - f a‖ + pathVar (b :: t) f

@[simp] theorem pathVar_nil (f : ℕ → ℂ) : pathVar [] f = 0 := rfl

@[simp] theorem pathVar_singleton (a : ℕ) (f : ℕ → ℂ) : pathVar [a] f = 0 := rfl

@[simp] theorem pathVar_cons_cons (a b : ℕ) (t : List ℕ) (f : ℕ → ℂ) :
    pathVar (a :: b :: t) f = ‖f b - f a‖ + pathVar (b :: t) f := rfl

theorem pathVar_nonneg (l : List ℕ) (f : ℕ → ℂ) : 0 ≤ pathVar l f := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' => exact add_nonneg (norm_nonneg _) ih

/-- Two functions agreeing on the path have the same variation. -/
theorem pathVar_congr {l : List ℕ} {f g : ℕ → ℂ} (h : ∀ n ∈ l, f n = g n) :
    pathVar l f = pathVar l g := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' =>
          have hb : f b = g b := h b (by simp)
          have ha : f a = g a := h a (by simp)
          rw [pathVar_cons_cons, pathVar_cons_cons, ha, hb,
            ih fun n hn => h n (List.mem_cons_of_mem _ hn)]

/-- Constants have zero variation. -/
@[simp] theorem pathVar_const (l : List ℕ) (c : ℂ) : pathVar l (fun _ => c) = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' => simp [ih]

/-- The variation of a sum is at most the sum of variations. -/
theorem pathVar_add_le (l : List ℕ) (f g : ℕ → ℂ) :
    pathVar l (fun n => f n + g n) ≤ pathVar l f + pathVar l g := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' =>
          have hstep : ‖(f b + g b) - (f a + g a)‖ ≤ ‖f b - f a‖ + ‖g b - g a‖ := by
            have : (f b + g b) - (f a + g a) = (f b - f a) + (g b - g a) := by ring
            rw [this]
            exact norm_add_le _ _
          simp only [pathVar_cons_cons]
          linarith [ih]

/-- The variation of a difference is at most the sum of variations. -/
theorem pathVar_sub_le (l : List ℕ) (f g : ℕ → ℂ) :
    pathVar l (fun n => f n - g n) ≤ pathVar l f + pathVar l g := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' =>
          have hstep : ‖(f b - g b) - (f a - g a)‖ ≤ ‖f b - f a‖ + ‖g b - g a‖ := by
            have : (f b - g b) - (f a - g a) = (f b - f a) - (g b - g a) := by ring
            rw [this]
            exact norm_sub_le _ _
          simp only [pathVar_cons_cons]
          linarith [ih]

/-- Scalar multiplication scales the variation. -/
theorem pathVar_smul (l : List ℕ) (c : ℂ) (f : ℕ → ℂ) :
    pathVar l (fun n => c * f n) = ‖c‖ * pathVar l f := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' =>
          have : c * f b - c * f a = c * (f b - f a) := by ring
          simp only [pathVar_cons_cons, this, norm_mul, ih]
          ring

/-- Multiplication by a constant on the right. -/
theorem pathVar_mul_const (l : List ℕ) (c : ℂ) (f : ℕ → ℂ) :
    pathVar l (fun n => f n * c) = ‖c‖ * pathVar l f := by
  have h : (fun n => f n * c) = fun n => c * f n := by funext n; ring
  rw [h, pathVar_smul]

/-- Subtracting from a constant does not change the variation. -/
theorem pathVar_const_sub (l : List ℕ) (c : ℂ) (f : ℕ → ℂ) :
    pathVar l (fun n => c - f n) = pathVar l f := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil => simp
      | cons b t' =>
          have : (c - f b) - (c - f a) = -(f b - f a) := by ring
          simp only [pathVar_cons_cons, this, norm_neg, ih]

/-- The product rule for the finite path variation. -/
theorem pathVar_mul_le (l : List ℕ) (f g : ℕ → ℂ) (Af Ag : ℝ)
    (hf : ∀ n ∈ l, ‖f n‖ ≤ Af) (hg : ∀ n ∈ l, ‖g n‖ ≤ Ag) :
    pathVar l (fun n => f n * g n) ≤ Ag * pathVar l f + Af * pathVar l g := by
  induction l with
  | nil => simp
  | cons a t ih =>
      cases t with
      | nil =>
          simp only [pathVar_singleton, mul_zero, add_zero]
          norm_num
      | cons b t' =>
          have hfb : ‖f b‖ ≤ Af := hf b (by simp)
          have hga : ‖g a‖ ≤ Ag := hg a (by simp)
          have hAf : 0 ≤ Af := le_trans (norm_nonneg _) hfb
          have hAg : 0 ≤ Ag := le_trans (norm_nonneg _) hga
          have hstep : ‖f b * g b - f a * g a‖ ≤ Ag * ‖f b - f a‖ + Af * ‖g b - g a‖ := by
            have hsplit : f b * g b - f a * g a = (f b - f a) * g a + f b * (g b - g a) := by
              ring
            calc ‖f b * g b - f a * g a‖
                ≤ ‖(f b - f a) * g a‖ + ‖f b * (g b - g a)‖ := by
                  rw [hsplit]; exact norm_add_le _ _
              _ = ‖f b - f a‖ * ‖g a‖ + ‖f b‖ * ‖g b - g a‖ := by
                  rw [norm_mul, norm_mul]
              _ ≤ ‖f b - f a‖ * Ag + Af * ‖g b - g a‖ := by
                  gcongr
              _ = Ag * ‖f b - f a‖ + Af * ‖g b - g a‖ := by ring
          have ihb := ih (fun n hn => hf n (List.mem_cons_of_mem _ hn))
            (fun n hn => hg n (List.mem_cons_of_mem _ hn))
          simp only [pathVar_cons_cons]
          nlinarith [pathVar_nonneg (b :: t') f, pathVar_nonneg (b :: t') g]

/-- Variation of a finite sum of functions. -/
theorem pathVar_sum_le {κ : Type*} (l : List ℕ) (S : Finset κ) (G : κ → ℕ → ℂ) :
    pathVar l (fun n => ∑ k ∈ S, G k n) ≤ ∑ k ∈ S, pathVar l (G k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert k S hk ih =>
      have hfun : (fun n => ∑ j ∈ insert k S, G j n)
          = fun n => G k n + ∑ j ∈ S, G j n := by
        funext n
        rw [Finset.sum_insert hk]
      rw [hfun, Finset.sum_insert hk]
      exact le_trans (pathVar_add_le l (G k) (fun n => ∑ j ∈ S, G j n)) (by linarith)

/-! ## 3. Monotone paths: constants, sharp intervals, ramps -/

/-- **Monotone bookkeeping.**  A `[0,1]`-valued monotone real function has path variation at
most `1` along an increasing path. -/
theorem pathVar_of_monotone_le (l : List ℕ) (hl : l.IsChain (· < ·)) (H : ℕ → ℝ)
    (hmono : Monotone H) (h0 : ∀ n, 0 ≤ H n) (h1 : ∀ n, H n ≤ 1) :
    pathVar l (fun n => ((H n : ℝ) : ℂ)) ≤ 1 := by
  have key : ∀ (t : List ℕ) (a : ℕ), List.IsChain (· < ·) (a :: t) →
      pathVar (a :: t) (fun n => ((H n : ℝ) : ℂ)) ≤ 1 - H a := by
    intro t
    induction t with
    | nil => intro a _; simpa using h1 a
    | cons b t' ih =>
        intro a hchain
        have hab : a < b := (List.isChain_cons_cons.mp hchain).1
        have hrest : List.IsChain (· < ·) (b :: t') := (List.isChain_cons_cons.mp hchain).2
        have hmon : H a ≤ H b := hmono hab.le
        have hstep : ‖((H b : ℝ) : ℂ) - ((H a : ℝ) : ℂ)‖ = H b - H a := by
          rw [show ((H b : ℝ) : ℂ) - ((H a : ℝ) : ℂ) = (((H b - H a : ℝ)) : ℂ) by push_cast; ring,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        have := ih b hrest
        rw [pathVar_cons_cons, hstep]
        linarith
  cases l with
  | nil => simp
  | cons a t =>
      have := key t a hl
      linarith [h0 a]

/-- The sharp interval indicator, as a difference of two monotone `{0,1}` functions. -/
theorem boxCutoff_eq_sub {lo hi : ℕ} (h : lo ≤ hi) :
    semAtom (.boxCutoff lo hi)
      = fun n => (((if lo ≤ n then (1 : ℝ) else 0) : ℝ) : ℂ)
          - (((if hi < n then (1 : ℝ) else 0) : ℝ) : ℂ) := by
  funext n
  simp only [semAtom]
  by_cases h1 : lo ≤ n
  · by_cases h2 : n ≤ hi
    · rw [if_pos ⟨h1, h2⟩, if_pos h1, if_neg (by omega)]
      norm_num
    · rw [if_neg (by omega), if_pos h1, if_pos (by omega)]
      norm_num
  · rw [if_neg (by omega), if_neg h1, if_neg (by omega)]
    norm_num

/-- `rampR` is antitone. -/
theorem rampR_antitone {a b : ℕ} (hab : a < b) : Antitone (rampR a b) := by
  intro m n hmn
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  have hden : (0 : ℝ) < (b : ℝ) - a := by linarith
  rcases le_or_gt n a with hn1 | hn1
  · have hm1 : m ≤ a := le_trans hmn hn1
    have e1 : rampR a b n = 1 := by simp [rampR, hn1]
    have e2 : rampR a b m = 1 := by simp [rampR, hm1]
    rw [e1, e2]
  · have hna : ¬ n ≤ a := by omega
    rcases le_or_gt m a with hm1 | hm1
    · have e2 : rampR a b m = 1 := by simp [rampR, hm1]
      rw [e2]
      exact (rampR_mem_unitInterval a b n hab).2
    · have hma : ¬ m ≤ a := by omega
      rcases le_or_gt b m with hbm | hbm
      · have hbn : b ≤ n := le_trans hbm hmn
        have e1 : rampR a b n = 0 := by simp [rampR, hbn, hna]
        have e2 : rampR a b m = 0 := by simp [rampR, hbm, hma]
        rw [e1, e2]
      · have hbm' : ¬ b ≤ m := by omega
        have hmval : rampR a b m = ((b : ℝ) - m) / ((b : ℝ) - a) := by
          simp [rampR, hma, hbm']
        rcases le_or_gt b n with hbn | hbn
        · have e1 : rampR a b n = 0 := by simp [rampR, hbn, hna]
          rw [e1, hmval]
          have hmb : (m : ℝ) ≤ (b : ℝ) := by exact_mod_cast (le_of_lt hbm)
          exact div_nonneg (by linarith) (le_of_lt hden)
        · have hbn' : ¬ b ≤ n := by omega
          have hnval : rampR a b n = ((b : ℝ) - n) / ((b : ℝ) - a) := by
            simp [rampR, hna, hbn']
          rw [hmval, hnval]
          have hmnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
          gcongr

/-! ### The variation-controlled sub-grammar -/

/-- The atoms whose finite path variation is controlled.  The Möbius atom, the Mellin twist and
the perfect-power pullback are **excluded**: they have no bounded finite variation, and no claim
about them is made. -/
def VarControlledAtom : GenAtom → Prop
  | .constant _ => True
  | .boxCutoff lo hi => lo ≤ hi
  | .smoothWeight _ _ => True
  | .mobius => False
  | .mellinTwist _ => False
  | .perfectPowerPullback _ => False

/-- The variation-controlled sub-grammar: generated expressions all of whose atoms are
variation-controlled. -/
def VarControlled : GenExpr → Prop
  | .atom a => VarControlledAtom a
  | .mul f g => VarControlled f ∧ VarControlled g
  | .add f g => VarControlled f ∧ VarControlled g
  | .smul _ f => VarControlled f
  | .conv f g => VarControlled f ∧ VarControlled g

/-- The declared variation budget `T(E)` of a generated expression. -/
noncomputable def varBudget : GenExpr → ℝ
  | .atom _ => 2
  | .mul f g => varBudget f + varBudget g
  | .add f g => max (varBudget f) (varBudget g)
  | .smul _ f => varBudget f
  | .conv f g => varBudget f + varBudget g

theorem varBudget_nonneg (E : GenExpr) : 0 ≤ varBudget E := by
  induction E with
  | atom a => norm_num [varBudget]
  | mul f g hf hg => simpa [varBudget] using add_nonneg hf hg
  | add f g hf hg => simp only [varBudget]; exact le_max_of_le_left hf
  | smul c f hf => simpa [varBudget] using hf
  | conv f g hf hg => simpa [varBudget] using add_nonneg hf hg

/-! ## 4. Scaled path variation functionals -/

/-- The variation of `f` along the fresh-prime path scaled by `e`:  `p ↦ f (p·e)`. -/
noncomputable def scaledVar (ps : List ℕ) (e : ℕ) (f : ℕ → ℂ) : ℝ :=
  pathVar ps (fun p => f (p * e))

/-- The divisor-summed variation functional at base `R`. -/
noncomputable def divVar (ps : List ℕ) (R : ℕ) (f : ℕ → ℂ) : ℝ :=
  ∑ e ∈ R.divisors, scaledVar ps e f

theorem scaledVar_nonneg (ps : List ℕ) (e : ℕ) (f : ℕ → ℂ) : 0 ≤ scaledVar ps e f :=
  pathVar_nonneg _ _

theorem divVar_nonneg (ps : List ℕ) (R : ℕ) (f : ℕ → ℂ) : 0 ≤ divVar ps R f :=
  Finset.sum_nonneg fun _ _ => scaledVar_nonneg _ _ _

/-- The variation of an atom along a scaled increasing path is at most `2`. -/
theorem scaledVar_atom_le (a : GenAtom) (ha : a.Admissible) (hc : VarControlledAtom a)
    (ps : List ℕ) (hps : ps.IsChain (· < ·)) (e : ℕ) :
    scaledVar ps e (semAtom a) ≤ 2 := by
  unfold scaledVar
  match a with
  | .constant c =>
      simp [semAtom]
  | .boxCutoff lo hi =>
      have hlohi : lo ≤ hi := hc
      have hfun : (fun p => semAtom (.boxCutoff lo hi) (p * e))
          = fun p => (((if lo ≤ p * e then (1 : ℝ) else 0) : ℝ) : ℂ)
              - (((if hi < p * e then (1 : ℝ) else 0) : ℝ) : ℂ) := by
        funext p
        rw [boxCutoff_eq_sub hlohi]
      have hmono1 : Monotone (fun p : ℕ => if lo ≤ p * e then (1 : ℝ) else 0) := by
        intro u v huv
        dsimp only
        by_cases hu : lo ≤ u * e
        · rw [if_pos hu, if_pos (le_trans hu (Nat.mul_le_mul_right e huv))]
        · rw [if_neg hu]
          split <;> norm_num
      have hmono2 : Monotone (fun p : ℕ => if hi < p * e then (1 : ℝ) else 0) := by
        intro u v huv
        dsimp only
        by_cases hu : hi < u * e
        · rw [if_pos hu, if_pos (lt_of_lt_of_le hu (Nat.mul_le_mul_right e huv))]
        · rw [if_neg hu]
          split <;> norm_num
      have h01 : ∀ n : ℕ, (0 : ℝ) ≤ (if lo ≤ n * e then (1 : ℝ) else 0) := by
        intro n; split <;> norm_num
      have h11 : ∀ n : ℕ, (if lo ≤ n * e then (1 : ℝ) else 0) ≤ 1 := by
        intro n; split <;> norm_num
      have h02 : ∀ n : ℕ, (0 : ℝ) ≤ (if hi < n * e then (1 : ℝ) else 0) := by
        intro n; split <;> norm_num
      have h12 : ∀ n : ℕ, (if hi < n * e then (1 : ℝ) else 0) ≤ 1 := by
        intro n; split <;> norm_num
      have h1 := pathVar_of_monotone_le ps hps _ hmono1 h01 h11
      have h2 := pathVar_of_monotone_le ps hps _ hmono2 h02 h12
      have h3 := pathVar_sub_le ps (fun p => (((if lo ≤ p * e then (1 : ℝ) else 0) : ℝ) : ℂ))
        (fun p => (((if hi < p * e then (1 : ℝ) else 0) : ℝ) : ℂ))
      rw [hfun]
      linarith
  | .smoothWeight u v =>
      have huv : u < v := ha
      have hfun : (fun p => semAtom (.smoothWeight u v) (p * e))
          = fun p => ((1 : ℝ) : ℂ) - (((1 - rampR u v (p * e) : ℝ)) : ℂ) := by
        funext p
        simp only [semAtom]
        push_cast
        ring
      have hmono : Monotone (fun p : ℕ => 1 - rampR u v (p * e)) := by
        intro s t hst
        dsimp only
        have := rampR_antitone huv (Nat.mul_le_mul_right e hst)
        linarith
      have h0 : ∀ n : ℕ, (0 : ℝ) ≤ 1 - rampR u v (n * e) := by
        intro n
        have := (rampR_mem_unitInterval u v (n * e) huv).2
        linarith
      have h1' : ∀ n : ℕ, 1 - rampR u v (n * e) ≤ 1 := by
        intro n
        have := (rampR_mem_unitInterval u v (n * e) huv).1
        linarith
      have h1 := pathVar_of_monotone_le ps hps _ hmono h0 h1'
      rw [hfun, pathVar_const_sub]
      linarith
  | .mobius => exact hc.elim
  | .mellinTwist _ => exact hc.elim
  | .perfectPowerPullback _ => exact hc.elim

/-- **The convolution variation inequality** (sharp divisor-sum form, no constant loss). -/
theorem scaledVar_dconv_le (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) (R : ℕ) (hR : R ≠ 0)
    (hpR : ∀ p ∈ ps, ¬ p ∣ R) (F G : ℕ → ℂ) (AF AG : ℝ)
    (hF : ∀ d ∈ R.divisors, ‖F d‖ ≤ AF) (hG : ∀ d ∈ R.divisors, ‖G d‖ ≤ AG)
    (e : ℕ) (he : e ∈ R.divisors) :
    scaledVar ps e (dconv F G)
      ≤ AG * (∑ d ∈ e.divisors, scaledVar ps d F)
        + AF * (∑ d ∈ e.divisors, scaledVar ps d G) := by
  classical
  have heR : e ∣ R := (Nat.mem_divisors.mp he).1
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hR (zero_dvd_iff.mp heR)
  have hsub : e.divisors ⊆ R.divisors := Nat.divisors_subset_of_dvd hR heR
  -- rewrite the convolution along the path
  have hrw : ∀ p ∈ ps, dconv F G (p * e)
      = ∑ d ∈ e.divisors, (F (p * d) * G (e / d) + F d * G (p * (e / d))) := by
    intro p hp
    have hpe : ¬ p ∣ e := fun h => hpR p hp (dvd_trans h heR)
    rw [dconv_fresh_prime F G (hps p hp) he0 hpe]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
    rw [Nat.mul_div_assoc p hdvd]
  unfold scaledVar
  rw [pathVar_congr hrw]
  refine le_trans (pathVar_sum_le ps e.divisors
    (fun d p => F (p * d) * G (e / d) + F d * G (p * (e / d)))) ?_
  have hterm : ∀ d ∈ e.divisors,
      pathVar ps (fun p => F (p * d) * G (e / d) + F d * G (p * (e / d)))
        ≤ AG * scaledVar ps d F + AF * scaledVar ps (e / d) G := by
    intro d hd
    have hdR : d ∈ R.divisors := hsub hd
    have hdvd : d ∣ e := (Nat.mem_divisors.mp hd).1
    have hedR : e / d ∈ R.divisors :=
      Nat.mem_divisors.mpr ⟨dvd_trans (Nat.div_dvd_of_dvd hdvd) heR, hR⟩
    have h1 : pathVar ps (fun p => F (p * d) * G (e / d)) ≤ AG * scaledVar ps d F := by
      rw [pathVar_mul_const]
      exact mul_le_mul_of_nonneg_right (hG _ hedR) (pathVar_nonneg _ _)
    have h2 : pathVar ps (fun p => F d * G (p * (e / d))) ≤ AF * scaledVar ps (e / d) G := by
      rw [pathVar_smul]
      exact mul_le_mul_of_nonneg_right (hF _ hdR) (pathVar_nonneg _ _)
    have := pathVar_add_le ps (fun p => F (p * d) * G (e / d))
      (fun p => F d * G (p * (e / d)))
    linarith
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  have hswap : ∑ d ∈ e.divisors, AF * scaledVar ps (e / d) G
      = ∑ d ∈ e.divisors, AF * scaledVar ps d G :=
    Nat.sum_div_divisors e (fun d => AF * scaledVar ps d G)
  rw [hswap]
  exact le_of_eq (by simp only [scaledVar])


/-! ## 5. Amplitude/variation equalities of the constructors -/

theorem ampBudget_mul (r : ℕ) (f g : GenExpr) :
    ampBudget r (.mul f g) = ampBudget r f * ampBudget r g := rfl

theorem ampBudget_add (r : ℕ) (f g : GenExpr) :
    ampBudget r (.add f g) = ampBudget r f + ampBudget r g := rfl

theorem ampBudget_smul (r : ℕ) (c : ℂ) (f : GenExpr) :
    ampBudget r (.smul c f) = ‖c‖ * ampBudget r f := rfl

theorem ampBudget_conv (r : ℕ) (f g : GenExpr) :
    ampBudget r (.conv f g) = (2 : ℝ) ^ r * (ampBudget r f * ampBudget r g) := rfl

/-! ## 6. The structural variation bound `v(E) ≤ a(E) · T(E)` -/

/-- **The structural variation theorem for the generated grammar.**  On the declared window, for
a squarefree-rank-`r` base `R`, an increasing path of fresh primes, and every variation-controlled
admissible generated expression `E`:

```
scaledVar ps e (semExpr E) ≤ a(E) · T(E)      for every  e | R .
```

All hypotheses are explicit and finite; the evaluation points are the **unshifted** `p·e`. -/
theorem scaledVar_semExpr_le {N r : ℕ} (hN : 1 ≤ N)
    (hD : ∀ n ≤ N, (n.divisors.card : ℝ) ≤ (2 : ℝ) ^ r)
    {R : ℕ} (hR : R ≠ 0) (hRcard : (R.divisors.card : ℝ) ≤ (2 : ℝ) ^ r)
    (hdivN : ∀ d ∈ R.divisors, d ≤ N)
    (ps : List ℕ) (hchain : ps.IsChain (· < ·)) (hprime : ∀ p ∈ ps, p.Prime)
    (hpR : ∀ p ∈ ps, ¬ p ∣ R) (hptN : ∀ p ∈ ps, ∀ d ∈ R.divisors, p * d ≤ N) :
    ∀ E : GenExpr, E.Admissible → VarControlled E →
      ∀ e ∈ R.divisors, scaledVar ps e (semExpr E) ≤ ampBudget r E * varBudget E := by
  intro E
  induction E with
  | atom a =>
      intro hadm hvc e _
      have h := scaledVar_atom_le a hadm hvc ps hchain e
      have hA : ampBudget r (GenExpr.atom a) = 1 := ampBudget_atom r a
      have hV : varBudget (GenExpr.atom a) = 2 := rfl
      rw [hA, hV]
      simpa [semExpr] using h
  | mul f g hf hg =>
      intro hadm hvc e he
      have h1 := hf hadm.1 hvc.1 e he
      have h2 := hg hadm.2 hvc.2 e he
      have hbf : ∀ p ∈ ps, ‖semExpr f (p * e)‖ ≤ ampBudget r f := fun p hp =>
        norm_semExpr_le_ampBudget hN hD f hadm.1 (hptN p hp e he)
      have hbg : ∀ p ∈ ps, ‖semExpr g (p * e)‖ ≤ ampBudget r g := fun p hp =>
        norm_semExpr_le_ampBudget hN hD g hadm.2 (hptN p hp e he)
      have hmul := pathVar_mul_le ps (fun p => semExpr f (p * e)) (fun p => semExpr g (p * e))
        (ampBudget r f) (ampBudget r g) hbf hbg
      have hs1 : ampBudget r g * scaledVar ps e (semExpr f)
          ≤ ampBudget r g * (ampBudget r f * varBudget f) :=
        mul_le_mul_of_nonneg_left h1 (ampBudget_nonneg r g)
      have hs2 : ampBudget r f * scaledVar ps e (semExpr g)
          ≤ ampBudget r f * (ampBudget r g * varBudget g) :=
        mul_le_mul_of_nonneg_left h2 (ampBudget_nonneg r f)
      have hgoal : scaledVar ps e (semExpr (.mul f g))
          = pathVar ps (fun p => semExpr f (p * e) * semExpr g (p * e)) := rfl
      rw [hgoal, ampBudget_mul, show varBudget (.mul f g) = varBudget f + varBudget g from rfl]
      have hsv1 : scaledVar ps e (semExpr f) = pathVar ps (fun p => semExpr f (p * e)) := rfl
      have hsv2 : scaledVar ps e (semExpr g) = pathVar ps (fun p => semExpr g (p * e)) := rfl
      rw [hsv1] at hs1
      rw [hsv2] at hs2
      nlinarith [hmul, hs1, hs2]
  | add f g hf hg =>
      intro hadm hvc e he
      have h1 := hf hadm.1 hvc.1 e he
      have h2 := hg hadm.2 hvc.2 e he
      have hadd := pathVar_add_le ps (fun p => semExpr f (p * e)) (fun p => semExpr g (p * e))
      have hmax1 : varBudget f ≤ max (varBudget f) (varBudget g) := le_max_left _ _
      have hmax2 : varBudget g ≤ max (varBudget f) (varBudget g) := le_max_right _ _
      have hb1 : ampBudget r f * varBudget f
          ≤ ampBudget r f * max (varBudget f) (varBudget g) :=
        mul_le_mul_of_nonneg_left hmax1 (ampBudget_nonneg r f)
      have hb2 : ampBudget r g * varBudget g
          ≤ ampBudget r g * max (varBudget f) (varBudget g) :=
        mul_le_mul_of_nonneg_left hmax2 (ampBudget_nonneg r g)
      have hgoal : scaledVar ps e (semExpr (.add f g))
          = pathVar ps (fun p => semExpr f (p * e) + semExpr g (p * e)) := rfl
      rw [hgoal, ampBudget_add,
        show varBudget (.add f g) = max (varBudget f) (varBudget g) from rfl]
      have hsv1 : scaledVar ps e (semExpr f) = pathVar ps (fun p => semExpr f (p * e)) := rfl
      have hsv2 : scaledVar ps e (semExpr g) = pathVar ps (fun p => semExpr g (p * e)) := rfl
      rw [hsv1] at h1
      rw [hsv2] at h2
      nlinarith [hadd, h1, h2, hb1, hb2]
  | smul c f hf =>
      intro hadm hvc e he
      have h1 := hf hadm hvc e he
      have hgoal : scaledVar ps e (semExpr (.smul c f))
          = pathVar ps (fun p => c * semExpr f (p * e)) := rfl
      rw [hgoal, pathVar_smul, ampBudget_smul,
        show varBudget (.smul c f) = varBudget f from rfl]
      have hsv1 : scaledVar ps e (semExpr f) = pathVar ps (fun p => semExpr f (p * e)) := rfl
      rw [hsv1] at h1
      have := mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
      nlinarith [this]
  | conv f g hf hg =>
      intro hadm hvc e he
      have heR : e ∣ R := (Nat.mem_divisors.mp he).1
      have hsub : e.divisors ⊆ R.divisors := Nat.divisors_subset_of_dvd hR heR
      have hF : ∀ d ∈ R.divisors, ‖semExpr f d‖ ≤ ampBudget r f := fun d hd =>
        norm_semExpr_le_ampBudget hN hD f hadm.1 (hdivN d hd)
      have hG : ∀ d ∈ R.divisors, ‖semExpr g d‖ ≤ ampBudget r g := fun d hd =>
        norm_semExpr_le_ampBudget hN hD g hadm.2 (hdivN d hd)
      have hconv := scaledVar_dconv_le ps hprime R hR hpR (semExpr f) (semExpr g)
        (ampBudget r f) (ampBudget r g) hF hG e he
      have hcard : (e.divisors.card : ℝ) ≤ (2 : ℝ) ^ r := by
        refine le_trans ?_ hRcard
        exact_mod_cast Finset.card_le_card hsub
      have hsum1 : ∑ d ∈ e.divisors, scaledVar ps d (semExpr f)
          ≤ (2 : ℝ) ^ r * (ampBudget r f * varBudget f) := by
        refine le_trans (Finset.sum_le_sum fun d hd => hf hadm.1 hvc.1 d (hsub hd)) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (ampBudget_nonneg r f) (varBudget_nonneg f))
      have hsum2 : ∑ d ∈ e.divisors, scaledVar ps d (semExpr g)
          ≤ (2 : ℝ) ^ r * (ampBudget r g * varBudget g) := by
        refine le_trans (Finset.sum_le_sum fun d hd => hg hadm.2 hvc.2 d (hsub hd)) ?_
        rw [Finset.sum_const, nsmul_eq_mul]
        exact mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (ampBudget_nonneg r g) (varBudget_nonneg g))
      have hstep1 : ampBudget r g * (∑ d ∈ e.divisors, scaledVar ps d (semExpr f))
          ≤ ampBudget r g * ((2 : ℝ) ^ r * (ampBudget r f * varBudget f)) :=
        mul_le_mul_of_nonneg_left hsum1 (ampBudget_nonneg r g)
      have hstep2 : ampBudget r f * (∑ d ∈ e.divisors, scaledVar ps d (semExpr g))
          ≤ ampBudget r f * ((2 : ℝ) ^ r * (ampBudget r g * varBudget g)) :=
        mul_le_mul_of_nonneg_left hsum2 (ampBudget_nonneg r f)
      have hgoal : scaledVar ps e (semExpr (.conv f g))
          = scaledVar ps e (dconv (semExpr f) (semExpr g)) := rfl
      rw [hgoal, ampBudget_conv, show varBudget (.conv f g) = varBudget f + varBudget g from rfl]
      nlinarith [hconv, hstep1, hstep2]

/-- The `2^r` corollary of the convolution inequality, in the shape of the research bank.
**Audit note:** the constant kernel-proved here is `2^r`; the literal `2^{r-1}` of the informal
bank is *not* proved with this normalisation. -/
theorem scaledVar_dconv_le_two_pow (ps : List ℕ) (hps : ∀ p ∈ ps, p.Prime) {R : ℕ} (hR : R ≠ 0)
    (hpR : ∀ p ∈ ps, ¬ p ∣ R) (r : ℕ) (hRcard : (R.divisors.card : ℝ) ≤ (2 : ℝ) ^ r)
    (F G : ℕ → ℂ) (AF AG vF vG : ℝ) (hAF : 0 ≤ AF) (hAG : 0 ≤ AG) (hvF : 0 ≤ vF) (hvG : 0 ≤ vG)
    (hF : ∀ d ∈ R.divisors, ‖F d‖ ≤ AF) (hG : ∀ d ∈ R.divisors, ‖G d‖ ≤ AG)
    (hvarF : ∀ d ∈ R.divisors, scaledVar ps d F ≤ vF)
    (hvarG : ∀ d ∈ R.divisors, scaledVar ps d G ≤ vG)
    (e : ℕ) (he : e ∈ R.divisors) :
    scaledVar ps e (dconv F G) ≤ (2 : ℝ) ^ r * (AG * vF + AF * vG) := by
  have heR : e ∣ R := (Nat.mem_divisors.mp he).1
  have hsub : e.divisors ⊆ R.divisors := Nat.divisors_subset_of_dvd hR heR
  have hcard : (e.divisors.card : ℝ) ≤ (2 : ℝ) ^ r := by
    refine le_trans ?_ hRcard
    exact_mod_cast Finset.card_le_card hsub
  have hconv := scaledVar_dconv_le ps hps R hR hpR F G AF AG hF hG e he
  have h1 : ∑ d ∈ e.divisors, scaledVar ps d F ≤ (2 : ℝ) ^ r * vF := by
    refine le_trans (Finset.sum_le_sum fun d hd => hvarF d (hsub hd)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hvF
  have h2 : ∑ d ∈ e.divisors, scaledVar ps d G ≤ (2 : ℝ) ^ r * vG := by
    refine le_trans (Finset.sum_le_sum fun d hd => hvarG d (hsub hd)) ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hcard hvG
  nlinarith [hconv, mul_le_mul_of_nonneg_left h1 hAG, mul_le_mul_of_nonneg_left h2 hAF]

/-! ## 7. Zero-extension cost -/

/-- The head indicator of a path. -/
def headInd (P : ℕ → Bool) : List ℕ → ℝ
  | [] => 0
  | a :: _ => if P a then 1 else 0

/-- A function supported on `P` has small path variation: at most `2A` per `P`-point. -/
theorem pathVar_supported (P : ℕ → Bool) (H : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hsupp : ∀ n, P n = false → H n = 0) (hbd : ∀ n, ‖H n‖ ≤ A) (l : List ℕ) :
    pathVar l H + A * headInd P l ≤ 2 * A * (l.countP P : ℝ) := by
  have hpt : ∀ n : ℕ, ‖H n‖ ≤ A * (if P n then 1 else 0) := by
    intro n
    by_cases h : P n
    · simpa [h] using hbd n
    · have : P n = false := by simpa using h
      simp [hsupp n this, h]
  induction l with
  | nil => simp [headInd]
  | cons a t ih =>
      cases t with
      | nil =>
          simp only [pathVar_singleton, headInd, List.countP_cons, List.countP_nil, zero_add]
          by_cases h : P a
          · simp [h]
            linarith
          · simp [h]
      | cons b t' =>
          have hstep : ‖H b - H a‖ ≤ A * (if P a then 1 else 0) + A * (if P b then 1 else 0) := by
            calc ‖H b - H a‖ ≤ ‖H b‖ + ‖H a‖ := norm_sub_le _ _
              _ ≤ A * (if P b then 1 else 0) + A * (if P a then 1 else 0) :=
                  add_le_add (hpt b) (hpt a)
              _ = A * (if P a then 1 else 0) + A * (if P b then 1 else 0) := by ring
          have hIH := ih
          have hcount : ((a :: b :: t').countP P : ℝ)
              = (if P a then 1 else 0) + ((b :: t').countP P : ℝ) := by
            rw [List.countP_cons]
            by_cases h : P a
            · simp [h]
              ring
            · simp [h]
          have hheadb : headInd P (b :: t') = (if P b then 1 else 0) := rfl
          have hheada : headInd P (a :: b :: t') = (if P a then 1 else 0) := rfl
          rw [pathVar_cons_cons, hheada, hcount]
          rw [hheadb] at hIH
          nlinarith [hstep, hIH]

/-- **Zero-extension cost.**  Replacing `f` by its zero extension at the `P`-points of the path
costs at most `2A` per `P`-point. -/
theorem pathVar_zero_extension_le (P : ℕ → Bool) (f : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hbd : ∀ n, ‖f n‖ ≤ A) (l : List ℕ) :
    pathVar l (fun n => if P n then 0 else f n)
      ≤ pathVar l f + 2 * A * (l.countP P : ℝ) := by
  set H : ℕ → ℂ := fun n => if P n then -f n else 0 with hHdef
  have hsupp : ∀ n, P n = false → H n = 0 := by
    intro n hn
    simp [hHdef, hn]
  have hbdH : ∀ n, ‖H n‖ ≤ A := by
    intro n
    by_cases h : P n
    · simpa [hHdef, h] using hbd n
    · simpa [hHdef, h] using hA
  have hsum : (fun n => if P n then (0 : ℂ) else f n) = fun n => f n + H n := by
    funext n
    by_cases h : P n <;> simp [hHdef, h]
  have hvar := pathVar_supported P H A hA hsupp hbdH l
  have hhead : 0 ≤ A * headInd P l := by
    cases l with
    | nil => simp [headInd]
    | cons a t =>
        have : (0 : ℝ) ≤ (if P a then (1 : ℝ) else 0) := by split <;> norm_num
        exact mul_nonneg hA (by simpa [headInd] using this)
  rw [hsum]
  have := pathVar_add_le l f H
  linarith

/-- On a path of distinct primes, at most `ω(R)` points divide `R`. -/
theorem countP_dvd_le_omega {l : List ℕ} (hnd : l.Nodup) (hp : ∀ p ∈ l, p.Prime) {R : ℕ}
    (hR : R ≠ 0) : l.countP (fun p => decide (p ∣ R)) ≤ R.primeFactors.card := by
  classical
  have hfil : (l.filter (fun p => decide (p ∣ R))).Nodup := hnd.filter _
  have hsub : (l.filter (fun p => decide (p ∣ R))).toFinset ⊆ R.primeFactors := by
    intro q hq
    rw [List.mem_toFinset, List.mem_filter] at hq
    exact Nat.mem_primeFactors.mpr ⟨hp q hq.1, by simpa using hq.2, hR⟩
  calc l.countP (fun p => decide (p ∣ R))
      = (l.filter (fun p => decide (p ∣ R))).length := by rw [List.countP_eq_length_filter]
    _ = (l.filter (fun p => decide (p ∣ R))).toFinset.card :=
        (List.toFinset_card_of_nodup hfil).symm
    _ ≤ R.primeFactors.card := Finset.card_le_card hsub

/-- **The zero-extension cost at the prime divisors of `R`**: at most `2 ω(R) A`. -/
theorem zero_extension_cost_omega {l : List ℕ} (hnd : l.Nodup) (hp : ∀ p ∈ l, p.Prime) {R : ℕ}
    (hR : R ≠ 0) (f : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A) (hbd : ∀ n, ‖f n‖ ≤ A) :
    pathVar l (fun n => if decide (n ∣ R) then 0 else f n)
      ≤ pathVar l f + 2 * (R.primeFactors.card : ℝ) * A := by
  have h1 := pathVar_zero_extension_le (fun p => decide (p ∣ R)) f A hA hbd l
  have h2 : (l.countP (fun p => decide (p ∣ R)) : ℝ) ≤ (R.primeFactors.card : ℝ) := by
    exact_mod_cast countP_dvd_le_omega hnd hp hR
  nlinarith [h1, h2]

/-- The eleven-prime source specialisation: the zero extension costs at most `22 A`. -/
theorem zero_extension_cost_eleven {l : List ℕ} (hnd : l.Nodup) (hp : ∀ p ∈ l, p.Prime) {R : ℕ}
    (hR : R ≠ 0) (homega : R.primeFactors.card = 11) (f : ℕ → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (hbd : ∀ n, ‖f n‖ ≤ A) :
    pathVar l (fun n => if decide (n ∣ R) then 0 else f n) ≤ pathVar l f + 22 * A := by
  have := zero_extension_cost_omega hnd hp hR f A hA hbd
  rw [homega] at this
  norm_num at this ⊢
  linarith

/-! ## 8. The evaluation-point firewall -/

/-- **Evaluation-point firewall.**  There is an admissible generated expression with *zero*
variation along the unshifted path `p ↦ E(p)` and *nonzero* variation along the shifted path
`p ↦ E(p+2)`.  The unshifted predecessor variation theorem therefore says nothing about shifted
evaluation. -/
theorem unshifted_variation_does_not_imply_shifted :
    ∃ (E : GenExpr) (l : List ℕ), E.Admissible
      ∧ pathVar l (fun p => semExpr E p) = 0
      ∧ pathVar l (fun p => semExpr E (p + 2)) ≠ 0 := by
  refine ⟨.atom (.boxCutoff 0 4), [1, 3], trivial, ?_, ?_⟩
  · norm_num [pathVar, semExpr, semAtom]
  · norm_num [pathVar, semExpr, semAtom]

/-- The two evaluation points are genuinely different: no universal equivalence may be
inhabited. -/
theorem semExpr_shift_not_universal :
    ¬ ∀ (E : GenExpr) (n : ℕ), semExpr E n = semExpr E (n + 2) := by
  intro h
  have := h (.atom (.boxCutoff 0 4)) 3
  norm_num [semExpr, semAtom] at this


end Gate1B.R11.Frontier
