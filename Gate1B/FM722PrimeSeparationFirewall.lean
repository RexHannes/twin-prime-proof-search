import Mathlib

/-!
# Gate 1B · FM722 · the **prime-separation firewall**

Purely finite arithmetic over `ℕ`.  No analytic content.

In the cross-`q` configuration the two moduli share the gcd part `g`,

```
  q₁ = g r₁,     q₂ = g r₂,     gcd(r₁, r₂) = 1,
```

and each carries a prime `wp_i ∣ r_i`.  Then the two primes must be different:
a common prime would divide `gcd(r₁, r₂) = 1`, forcing `wp = 1`, contradicting
primality.
-/

namespace TwinPrimeProject
namespace CurrentProgramme
namespace FM722

/-- A prime dividing both members of a coprime pair is impossible. -/
theorem no_common_prime_of_coprime {r1 r2 wp : ℕ} (hcop : Nat.Coprime r1 r2)
    (h1 : wp ∣ r1) (h2 : wp ∣ r2) (hp : wp.Prime) : False := by
  have hdvd : wp ∣ Nat.gcd r1 r2 := Nat.dvd_gcd h1 h2
  rw [Nat.Coprime] at hcop
  rw [hcop] at hdvd
  exact hp.one_lt.ne' (Nat.dvd_one.mp hdvd)

/-- **Prime separation (usable consequence).**  With `q₁ = g r₁`, `q₂ = g r₂`
and `gcd(r₁, r₂) = 1`, primes `wp₁ ∣ r₁` and `wp₂ ∣ r₂` are distinct.

Both primality hypotheses are part of the source statement and are kept; the
proof only needs primality of `wp₁`. -/
theorem prime_separation {r1 r2 wp1 wp2 : ℕ} (hcop : Nat.Coprime r1 r2)
    (h1 : wp1 ∣ r1) (h2 : wp2 ∣ r2) (hp1 : wp1.Prime) (hp2 : wp2.Prime) :
    wp1 ≠ wp2 := by
  intro heq
  exact no_common_prime_of_coprime hcop h1 (heq ▸ h2) hp1

/-- The same statement in the `q = g r` form used by the cross-`q` object. -/
theorem prime_separation_gcd_form {g r1 r2 q1 q2 wp1 wp2 : ℕ}
    (hq1 : q1 = g * r1) (hq2 : q2 = g * r2) (hcop : Nat.Coprime r1 r2)
    (h1 : wp1 ∣ r1) (h2 : wp2 ∣ r2) (hp1 : wp1.Prime) (hp2 : wp2.Prime) :
    wp1 ≠ wp2 ∧ q1 = g * r1 ∧ q2 = g * r2 :=
  ⟨prime_separation hcop h1 h2 hp1 hp2, hq1, hq2⟩

end FM722
end CurrentProgramme
end TwinPrimeProject
