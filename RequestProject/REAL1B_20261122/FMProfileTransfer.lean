import RequestProject.REAL1B_20261122.FMLowerLedger
import RequestProject.REAL1B_20261122.FMBoxGeometry

/-! Finite parts of the Gold 4.64–4.65 transfer to the fixed five-prime source. -/
namespace REAL1B.FM.Profile
open Filter Vaughan Source Closing Analytic ArithmeticFunction
noncomputable section
open Classical

def smooth (z : ℝ) (k : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ k → (p:ℝ) ≤ z
def smoothMask (z : ℝ) (k : ℕ) : ℝ := if smooth z k then 1 else 0

theorem smooth_mask_mul (z : ℝ) (m n : ℕ) : smoothMask z (m*n) = smoothMask z m * smoothMask z n := by
  have h : smooth z (m*n) ↔ smooth z m ∧ smooth z n := by
    constructor
    · intro h
      exact ⟨fun p hp hd => h p hp (dvd_mul_of_dvd_left hd n),
        fun p hp hd => h p hp (dvd_mul_of_dvd_right hd m)⟩
    · rintro ⟨h₁,h₂⟩ p hp hd
      exact (hp.dvd_mul.mp hd).elim (h₁ p hp) (h₂ p hp)
  by_cases hm : smooth z m <;> by_cases hn : smooth z n <;> simp [smoothMask,h,hm,hn]

def restrictSmooth (z : ℝ) (f : AF) : AF := ⟨fun k => smoothMask z k * f k, by simp⟩

theorem smooth_convolution (z : ℝ) (f g : AF) :
    restrictSmooth z (f*g) = restrictSmooth z f * restrictSmooth z g := by
  ext k
  change smoothMask z k * (f*g) k = _
  rw [ArithmeticFunction.mul_apply,ArithmeticFunction.mul_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  change smoothMask z k * (f p.1 * g p.2) = smoothMask z p.1 * f p.1 * (smoothMask z p.2 * g p.2)
  rw [← (Nat.mem_divisorsAntidiagonal.mp hp).1,smooth_mask_mul]
  ring

theorem squarefree_mask_obstruction : Squarefree (2:ℕ) ∧ ¬ Squarefree ((2:ℕ)*2) := by
  refine ⟨Nat.prime_two.squarefree,fun h => ?_⟩
  have := h 2 (dvd_refl (2*2))
  norm_num at this

/-- Exact difference between a primitive principal and a total main, at each genuine modulus. -/
def primitive (x : ℝ) (d : ℕ) (f : ℕ → ℝ) := total (x/2) (fun n => if n.Coprime d then f n else 0)
def collision (x : ℝ) (d : ℕ) (f : ℕ → ℝ) := total (x/2) (fun n => if n.Coprime d then 0 else f n)

theorem primitive_correction (x : ℝ) (d : ℕ) (f : ℕ → ℝ) :
    total (x/2) f / d.totient - primitive x d f / d.totient = collision x d f / d.totient := by
  rw [← sub_div]
  congr 1
  unfold primitive collision total
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n _
  change (f n - (if n.Coprime d then f n else 0)) = (if n.Coprime d then 0 else f n)
  split_ifs <;> ring

theorem shared_prime {n d : ℕ} {x : ℝ} (hn : n ∈ interval (x/2)) (hb : boxes n) (hd : ¬n.Coprime d) :
    ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ p ∣ d ∧ 0.04 * Real.log n < Real.log p := by
  obtain ⟨p,hp,h₁,h₂⟩ := Nat.Prime.not_coprime_iff_dvd.mp hd
  exact ⟨p,hp,h₁,h₂,boxes_prime_size (by exact_mod_cast (show 1<n by have := (window hn).2.2; omega)) hb hp h₁⟩

def roughProfile (x : ℝ) := total (x/2) (fun n =>
  sieve (cutU x) (n-2) * Real.log (n-2:ℕ) * Direct.psi x n)

theorem prime_le_rough (hψ : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), 0 ≤ Direct.psi x n) :
    ∀ᶠ x : ℝ in atTop, Direct.primeBox x ≤ roughProfile x := by
  filter_upwards [box_prime_source,small_power (by norm_num : (0.24:ℝ) ≤ 1/2),hψ] with x he hu hnon
  rw [he]
  unfold primeSum roughProfile total
  apply Finset.sum_le_sum
  intro n hn
  apply mul_le_mul_of_nonneg_right _ (hnon n hn)
  by_cases hp : (n-2).Prime
  · have hz : Sifted (cutU x) (n-2) := fun p h hd => (Nat.prime_dvd_prime_iff_eq h hp).mp hd ▸ hu n hn
    simp [theta,hp,sieve,hz]
  · simp only [theta,if_neg hp]
    unfold sieve
    split_ifs <;> simp [Real.log_natCast_nonneg]

def reference (x : ℝ) := (H2.series/2) * scale x
def Normalization : Prop := negligible (fun x => Sb x - reference x) scale

theorem scale_lower (h : Normalization) : ScaleLower := by
  have hp := H2.series_pos
  refine ⟨H2.series/4,by linarith,?_⟩
  filter_upwards [h (H2.series/4) (by linarith)] with x hx
  unfold reference at hx
  linarith only [(abs_le.mp hx).1]

/-- The rough-source estimate is supplied against the independent reference mass. -/
theorem profile_upper (hn : Normalization)
    (hψ : ∀ᶠ x : ℝ in atTop, ∀ n ∈ interval (x/2), 0 ≤ Direct.psi x n)
    (hrough : ∀ e : ℝ, 0 < e → ∀ᶠ x : ℝ in atTop,
      roughProfile x ≤ Direct.cStar * Direct.J * reference x + e * Sb x) : Direct.ProfileUpper := by
  let C := Direct.cStar * Direct.J
  have hdiff := negligible_comparator hn (scale_lower hn)
  intro e he
  have ht : 0 < e/(2*(|C|+1)) := div_pos he (by positivity)
  filter_upwards [hrough (e/2) (by linarith),prime_le_rough hψ,hdiff _ ht,
    comparator_pos (scale_lower hn)] with x hr hp hd hs
  have hbound : |C*(reference x - Sb x)| ≤ e/2*Sb x := by
    rw [abs_mul,abs_sub_comm (reference x)]
    calc
      _ ≤ (|C|+1) * |Sb x - reference x| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
      _ ≤ (|C|+1)*(e/(2*(|C|+1))*Sb x) := mul_le_mul_of_nonneg_left hd (by positivity)
      _ = _ := by field_simp [ne_of_gt (by positivity : 0 < |C|+1)]
  change _ ≤ (C+e)*Sb x
  change _ ≤ C*reference x + _ at hr
  linarith only [hp,hr,(abs_le.mp hbound).2]

end
end REAL1B.FM.Profile
#print axioms REAL1B.FM.Profile.smooth_convolution
#print axioms REAL1B.FM.Profile.squarefree_mask_obstruction
#print axioms REAL1B.FM.Profile.primitive_correction
#print axioms REAL1B.FM.Profile.shared_prime
#print axioms REAL1B.FM.Profile.prime_le_rough
#print axioms REAL1B.FM.Profile.scale_lower
#print axioms REAL1B.FM.Profile.profile_upper
