import Gate1B.PuncturedFourierFrame

/-!
# Gate 1B · the **centred additive projector** and its zero mode

Exact finite Fourier algebra over `ZMod q`.  No analytic estimate is proved or
assumed.

For `q > 0` the *centred* projector is

```
  Δ_q(n) = 1_{n = −2}  −  P_q(n),
```

where `P_q` is the **unit-sector principal model**, the normalised indicator of
the unit sector `(ZMod q)ˣ` with total mass `1`.  The point of the module is the
exact vanishing of the **zero additive frequency**:

```
  Δ̂_q(0) = ∑_{n mod q} Δ_q(n) = 0,
```

equivalently, in Ramanujan-sum form,

```
  e_q(0) − c_q(0)/φ(q) = 0,          c_q(h) = ∑_{a mod q, a unit} e_q(−h a).
```

## Contents

* §1 the finite Ramanujan sum `ramanujanSum` and `c_q(0) = φ(q)`;
* §2 the unit-sector principal model `unitPrincipal` (total mass `1`);
* §3 the centred projector, its zero-frequency vanishing, and the Fourier
  coefficient in Ramanujan form;
* §4 the **two-copy zero-mode cancellation**: the four signed pieces
  `II − IP − PI + PP` cancel at the double zero frequency, and any two-copy mode
  with one coordinate at frequency zero vanishes.

The additive character `e_q` is the repository's existing `eM` from
`Gate1B.PuncturedFourierFrame`; nothing is redefined.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace HStarCentered

open Finset
open TwinPrimeProject.CurrentProgramme.PuncturedFourier

variable {q : ℕ} [NeZero q]

/-! ## 1. The finite Ramanujan sum -/

/-- The finite **Ramanujan sum** `c_q(h) = ∑_{a mod q, a unit} e_q(−h a)`. -/
noncomputable def ramanujanSum (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ, eM q (-(h * (a : ZMod q)))

/-- `c_q(0) = φ(q)`. -/
theorem ramanujanSum_zero (q : ℕ) [NeZero q] :
    ramanujanSum q 0 = (q.totient : ℂ) := by
  classical
  simp only [ramanujanSum, zero_mul, neg_zero, eM_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [ZMod.card_units_eq_totient q]

theorem totient_cast_ne_zero (q : ℕ) [NeZero q] : ((q.totient : ℂ)) ≠ 0 := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have : 0 < q.totient := Nat.totient_pos.2 hq
  exact_mod_cast this.ne'

/-! ## 2. The unit-sector principal model -/

/-- The **unit-sector principal model**: the normalised indicator of the unit
sector, `P_q(n) = 1/φ(q)` if `n` is a unit and `0` otherwise. -/
noncomputable def unitPrincipal (q : ℕ) [NeZero q] (n : ZMod q) : ℂ :=
  ∑ a : (ZMod q)ˣ, if (a : ZMod q) = n then (1 / (q.totient : ℂ)) else 0

/-- The principal model has total mass `1`. -/
theorem unitPrincipal_total_mass (q : ℕ) [NeZero q] :
    ∑ n : ZMod q, unitPrincipal q n = 1 := by
  classical
  simp only [unitPrincipal]
  rw [Finset.sum_comm]
  have h : ∀ a : (ZMod q)ˣ,
      (∑ n : ZMod q, if (a : ZMod q) = n then (1 / (q.totient : ℂ)) else 0)
        = 1 / (q.totient : ℂ) := by
    intro a
    simp
  rw [Finset.sum_congr rfl fun a _ => h a]
  rw [Finset.sum_const, Finset.card_univ, ZMod.card_units_eq_totient q,
    nsmul_eq_mul]
  have hne := totient_cast_ne_zero q
  field_simp

/-! ## 3. The centred projector and its zero mode -/

/-- The **centred additive projector** `Δ_q(n) = 1_{n = −2} − P_q(n)`. -/
noncomputable def centeredProjector (q : ℕ) [NeZero q] (n : ZMod q) : ℂ :=
  (if n = -2 then (1 : ℂ) else 0) - unitPrincipal q n

/-- The additive Fourier coefficient of the centred projector at frequency
`h`. -/
noncomputable def centeredFourier (q : ℕ) [NeZero q] (h : ZMod q) : ℂ :=
  ∑ n : ZMod q, centeredProjector q n * eM q (h * n)

/-- **BOXED zero-mode identity (mass form).**  The centred projector has total
mass zero. -/
theorem centeredProjector_total_mass_zero (q : ℕ) [NeZero q] :
    ∑ n : ZMod q, centeredProjector q n = 0 := by
  classical
  simp only [centeredProjector, Finset.sum_sub_distrib]
  rw [unitPrincipal_total_mass]
  simp

/-- **BOXED zero-mode identity (Fourier form).**  `Δ̂_q(0) = 0`. -/
theorem centeredFourier_zero_eq_zero (q : ℕ) [NeZero q] :
    centeredFourier q 0 = 0 := by
  simp only [centeredFourier, zero_mul, eM_zero, mul_one]
  exact centeredProjector_total_mass_zero q

/-- **BOXED, Ramanujan form.**  The prompt's target identity: the centred
coefficient at additive frequency `h = 0` is exactly zero,

`e_q(0) − c_q(0)/φ(q) = 0`. -/
theorem eM_zero_sub_ramanujanSum_zero_div_totient (q : ℕ) [NeZero q] :
    eM q 0 - ramanujanSum q 0 / (q.totient : ℂ) = 0 := by
  rw [ramanujanSum_zero, eM_zero, div_self (totient_cast_ne_zero q), sub_self]

/-- The centred Fourier coefficient in closed Ramanujan form:
`Δ̂_q(h) = e_q(−2h) − c_q(−h)/φ(q)`. -/
theorem centeredFourier_eq_ramanujan_form (q : ℕ) [NeZero q] (h : ZMod q) :
    centeredFourier q h = eM q (h * (-2)) - ramanujanSum q (-h) / (q.totient : ℂ) := by
  classical
  have hne := totient_cast_ne_zero q
  have hI : (∑ n : ZMod q, (if n = -2 then (1 : ℂ) else 0) * eM q (h * n))
      = eM q (h * (-2)) := by
    rw [Finset.sum_eq_single (-2 : ZMod q)]
    · simp
    · intro b _ hb; simp [hb]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  have hP : (∑ n : ZMod q, unitPrincipal q n * eM q (h * n))
      = ramanujanSum q (-h) / (q.totient : ℂ) := by
    simp only [unitPrincipal, Finset.sum_mul]
    rw [Finset.sum_comm, ramanujanSum, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_eq_single ((a : ZMod q))]
    · rw [show -(-h * (a : ZMod q)) = h * (a : ZMod q) by ring]
      simp only [if_pos trivial]
      ring
    · intro b _ hb; simp [Ne.symm hb]
    · intro hb; exact absurd (Finset.mem_univ _) hb
  simp only [centeredFourier, centeredProjector, sub_mul, Finset.sum_sub_distrib]
  rw [hI, hP]

/-! ## 4. Two-copy zero-mode cancellation -/

/-- The two-copy additive mode of a pair of one-copy coefficient functions. -/
noncomputable def twoCopyMode (F G : ZMod q → ℂ) (h1 h2 : ZMod q) : ℂ :=
  (∑ n : ZMod q, F n * eM q (h1 * n)) * (∑ n : ZMod q, G n * eM q (h2 * n))

/-- **A two-copy mode with one coordinate at a vanishing one-copy frequency
vanishes.** -/
theorem twoCopyMode_eq_zero_of_second_zero {F G : ZMod q → ℂ} {h1 h2 : ZMod q}
    (hG : (∑ n : ZMod q, G n * eM q (h2 * n)) = 0) :
    twoCopyMode F G h1 h2 = 0 := by
  simp [twoCopyMode, hG]

/-- **The centred two-copy mode at the double zero frequency vanishes.** -/
theorem centered_twoCopyMode_zero_zero (q : ℕ) [NeZero q] :
    twoCopyMode (centeredProjector q) (centeredProjector q) 0 0 = 0 :=
  twoCopyMode_eq_zero_of_second_zero
    (by simpa [centeredFourier] using centeredFourier_zero_eq_zero q)

/-- The four signed pieces of the two-copy expansion of a centred product,
`Δ ⊗ Δ = I⊗I − I⊗P − P⊗I + P⊗P`, evaluated at the double zero frequency: the
common normalisation is the total mass `m` of each one-copy piece, and the
signed sum `+1 −1 −1 +1` cancels it exactly. -/
theorem four_signed_pieces_cancel (mI mP : ℂ) (h : mI = mP) :
    (mI * mI) - (mI * mP) - (mP * mI) + (mP * mP) = 0 := by
  rw [h]; ring

/-- The four signed pieces named as in the report (`II`, `IP`, `PI`, `PP`),
for the indicator part `I` and the principal model `P` of the centred
projector: both have total mass `1`, so the signed sum vanishes. -/
theorem centered_four_pieces_cancel (q : ℕ) [NeZero q] :
    (∑ n : ZMod q, if n = -2 then (1 : ℂ) else 0) *
        (∑ n : ZMod q, if n = -2 then (1 : ℂ) else 0)
      - (∑ n : ZMod q, if n = -2 then (1 : ℂ) else 0) *
        (∑ n : ZMod q, unitPrincipal q n)
      - (∑ n : ZMod q, unitPrincipal q n) *
        (∑ n : ZMod q, if n = -2 then (1 : ℂ) else 0)
      + (∑ n : ZMod q, unitPrincipal q n) * (∑ n : ZMod q, unitPrincipal q n)
      = 0 := by
  classical
  have hI : (∑ n : ZMod q, if n = -2 then (1 : ℂ) else 0) = 1 := by simp
  have hP : (∑ n : ZMod q, unitPrincipal q n) = 1 := unitPrincipal_total_mass q
  rw [hI, hP]; ring

end HStarCentered
end CurrentProgramme
end TwinPrimeProject
