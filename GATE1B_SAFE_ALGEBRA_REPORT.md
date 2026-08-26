# GATE 1B SAFE ALGEBRA BANK — FINAL REPORT

```text
LEAN VERSION:
leanprover/lean4:v4.28.0

MATHLIB COMMIT:
8f9d9cff6bd728b17a24e163c9402775d9e6a365   (tag v4.28.0, as pinned by lakefile.toml)

Shell congruence:
PROVED        (Gate1B.shell_sub, Gate1B.shell_unit_form, Gate1B.shell_mod_rsq)

Character saturation:
PROVED        (Gate1B.on_shell_character_saturation, Gate1B.shell_character_saturation)

All-moment saturation:
PROVED        (Gate1B.on_shell_character_saturation_tensor,
               Gate1B.on_shell_character_saturation_signs,
               Gate1B.shell_character_saturation_tensor)

C45 integer identity:
PROVED        (Gate1B.c45_identity)

C45 divisibility equivalence:
PROVED        (Gate1B.c45_dvd_iff; converse needs u ≠ 0, shown load-bearing by
               Gate1B.c45_converse_needs_u_ne_zero)

Zero-defect diagonal lemma:
PROVED        (Gate1B.zero_defect_diagonal, Gate1B.q_eq_of_defect_zero_of_l_eq;
               (ZD-HYP) is an explicit hypothesis and is shown load-bearing by
               Gate1B.zero_defect_needs_size_hypothesis)

Additive C45 coordinate:
PROVED        (Gate1B.add_c45_int, Gate1B.add_c45_zmod, Gate1B.add_c45_rsq)

Local prime-square lift:
PROVED        (Gate1B.local_prime_square_lift, Gate1B.exists_local_lift_coordinate,
               Gate1B.local_lift_of_shell)

Local density:
PROVED        (Gate1B.card_local_diagonal, Gate1B.card_local_square,
               Gate1B.local_density_eq, Gate1B.local_diagonal_density)

Four-prime CRT factorization:
PROVED        (Gate1B.prod_sq_dvd_iff, Gate1B.four_prime_sq_dvd_iff,
               Gate1B.four_local_collision)

Anti-Cartesian counterexample:
PROVED        (Gate1B.shell_sum_ne_cartesian_sum,
               Gate1B.shell_sum_ne_cartesian_sum_explicit,
               Gate1B.shell_sum_explicit_values)

SORRY COUNT:
0

AXIOM COUNT:
0   (no user axiom, no `opaque`, no `@[implemented_by]`, no `native_decide`.
     `#print axioms` on every principal theorem, run in Gate1B/Status.lean,
     reports at most propext / Classical.choice / Quot.sound.)

FILES:
Gate1B/Shell.lean
Gate1B/CharacterSaturation.lean
Gate1B/C45.lean
Gate1B/AdditiveCoordinate.lean
Gate1B/PrimeSquareLift.lean
Gate1B/LocalDensity.lean
Gate1B/CRTProduct.lean
Gate1B/AntiCartesian.lean
Gate1B/Interfaces.lean          (comments only — no declarations)
Gate1B/Status.lean              (axiom audit)

ANALYTIC CLAIMS BANKED:
NONE
```

## Statement-by-statement notes

1. **§1 shell.** `q ℓ = t r v + 2 ↔ q ℓ − t r v = 2` over `ℤ`; no interpretation.
2. **§2 (S1).** Stated with `ℓ` represented as a genuine unit `lu` of `ZMod n`,
   the conclusion being `q = lu⁻¹ (2 + r t v)`; the `r²` instance builds the unit
   from `IsCoprime ℓ r`. No informal modular division occurs.
3. **§3 (SAT1, SAT-k).** `χ` is an arbitrary monoid homomorphism from `(ZMod n)ˣ`
   into an arbitrary commutative group; the tensor version allows arbitrary
   moduli, arbitrary homomorphisms and arbitrary **integer** exponents, so the
   signs `εⱼ ∈ {−1, +1}` are a special case. A guard theorem records that
   saturation is an equality of values, not a triviality of values: it produces
   no cancellation and no moment bound.
4. **§4 (C45-ID).** `D = u(v₁ℓ₂ − v₂ℓ₁)` exactly, from the two shells.
5. **§5 (C45).** Both directions; the converse requires `u ≠ 0` and a countermodel
   shows that hypothesis cannot be dropped (`u = 0` satisfies both shells,
   `u² ∣ D`, yet `u ∤ v₁ℓ₂ − v₂ℓ₁`).
6. **§6 (ZD).** `(ZD-HYP)` `2|ℓ₁ − ℓ₂| < ℓ₁ℓ₂` is an explicit theorem hypothesis;
   the conclusion is `(q₁, ℓ₁) = (q₂, ℓ₂)`. The `ℓ₁ = ℓ₂` branch is separated and
   needs no size hypothesis. A countermodel (`q₁,q₂,ℓ₁,ℓ₂ = 1,0,1,2`) shows
   `(ZD-HYP)` is load-bearing.
7. **§7 (ADD-C45).** Proved by multiplying by the unit `ℓ₁ℓ₂`, in both an
   integer-inverse form and a `ZMod R` unit form.
8. **§8 (LOCAL-LIFT).** `s² ∣ D ↔ x₁ ≡ x₂ (mod s)`. In addition,
   `exists_local_lift_coordinate` shows the local coordinate exists precisely on
   the shell modulo `s`.
9. **§9 local density.** Finite counting only: diagonal card `s`, ambient card
   `s²`, density `1/s`; a guard notes the `s = 1` case where the density is `1`.
10. **§10 CRT.** Multiplicativity along any pairwise-coprime family, specialised
    to four labelled distinct primes, then combined with §8 into the exact
    four-local-collision equivalence. **No independence is inferred**; the guard
    `local_conditions_not_independent` exhibits two density-`1/2` conditions whose
    conjunction has density `1/2`.
11. **§11 anti-Cartesian.** Both a general schema (any two points with distinct
    first and second coordinates) and an explicit numerical instance with the two
    sums evaluated to `0` and `1`.
12. **§12 interface-only items.** `MAM45`, `SIGNED_C45`, `ASPE45`, `PSC45`,
    `ADDITIVE_PSQ_C45`, `ZHAO_SQUARE_MODULUS_LARGE_SIEVE`, `E(q)`, `Z_E(q)`,
    `KAPPA4`, `FIXED_SWITCHED_REASSEMBLY` appear only as comments in
    `Gate1B/Interfaces.lean`; there is no declaration of any kind in that file, so
    none of them can be inhabited by accident. `PSQ-SYNC45 PASS` and Gate-1B
    closure are not banked.

## Gate 1A safe algebra bank (companion, same discipline)

Added under `Gate1A/SafeAlgebra/`, reusing the generic finite lemmas of the
Gate-1B bank rather than duplicating them.

| Item | Statement | Status |
| --- | --- | --- |
| Outer projective defect | `Dproj = Z₁L₂ − Z₂L₁`; vanishes exactly on the collision relation and exactly on equal `ratioClass` | PROVED |
| PB expansion | `Dproj = Q(a₁L₂ − a₂L₁) + P₀(n₁L₂ − n₂L₁)` for `Zᵢ = Q aᵢ + P₀ nᵢ` | PROVED |
| Common-divisor divisibility | `d ∣ Q`, `d ∣ P₀` ⟹ `d ∣ Dproj` | PROVED |
| Projective rigidity (zero-defect) | positive `Lᵢ` and primitive `(Zᵢ, Lᵢ)` with `Dproj = 0` ⟹ `(Z₁,L₁) = (Z₂,L₂)`; primitivity shown load-bearing | PROVED |
| Additive projective coordinate | `R ∣ Dproj ↔ Z₁L₁⁻¹ ≡ Z₂L₂⁻¹ (mod R)`, integer and unit forms | PROVED |
| Local prime-square lift | `s² ∣ Dproj ↔ x₁ ≡ x₂ (mod s)` for local jets over a common leading residue | PROVED |
| Four-prime CRT / four-local collision | `u² ∣ Dproj ↔ ∀ i, x₁ᵢ ≡ x₂ᵢ (mod sᵢ)` | PROVED |
| Finite counts | each projective-coordinate fibre has exactly one point; diagonal count `s` | PROVED |
| Anti-Cartesian guards | collision relation ≠ product of projections, in relation form and in sum form | PROVED |
| Saturation (anti-loop) | equal projective coordinates ⟹ equal character values, at every tensor power with arbitrary integer coefficients; guard that this gives no value information | PROVED |
| Gate-1A analytic interfaces | `flatProfileSourceLegality`, `correctedPBAnalytic`, `hZeroFirewallBound`, `exceptionalSectorsBound`, `sourceCoherence` | OPEN — comments only, never inhabited |

Files: `Gate1A/SafeAlgebra/ProjectiveDefect.lean`,
`Gate1A/SafeAlgebra/Saturation.lean`,
`Gate1A/SafeAlgebra/Interfaces.lean` (comments only),
`Gate1A/SafeAlgebra/Status.lean` (axiom audit).
Sorry count 0, axiom count 0, analytic claims banked: NONE. Gate-1A closure
remains conditional exactly as before (`Gate1A.Delta4.gate1a_of_final_interfaces`);
nothing in the new material changes its status.
