# GATE 1B · C4SHIFT CENTERED AP 5/8 — APPEND-ONLY SAFE BANK REPORT

Mode: **APPEND-ONLY EXACT ALGEBRA / FINITE FOURIER / STATUS UPDATE.**

No analytic estimate is proved. Every analytic obligation stays in an
**uninhabited** source socket.

---

## PREVIOUS LEAFWISE BANK PRESERVED

The three previously banked modules

* `Gate1B/C4ShiftLeafwiseOneMinor.lean`
* `Gate1B/CurrentStatusGate1BC4ShiftLeafwise.lean`
* `Gate1B/AxiomAuditGate1BC4ShiftLeafwise.lean`

were **not edited** (not even their imports). Their content — deterministic
major-arc ownership, character diagonalisation, the tuple-level one-minor
projector `P₁ₘ`, the `(h,K)` AP-index normal form, the `ℓ`-normalisation
firewall — is imported unchanged.

Both existing analytic sockets remain **uninhabited**:

* `C4ShiftLeafwise.C4ShiftOneMinorPushedEnergyInput`
* `C4ShiftLeafwise.C4ShiftOneMinorAPIndexRestrictionInput`

New modules added:

* `Gate1B/C4ShiftCenteredAPKernel.lean` (exact algebra / finite Fourier)
* `Gate1B/CurrentStatusGate1BC4ShiftCenteredAP58.lean` (new status layer)
* `Gate1B/AxiomAuditGate1BC4ShiftCenteredAP58.lean` (axiom audit)

---

## NEW EXACT CENTERED KERNEL

### §1 — exact one-minor AP phase identity — `C4SHIFT-1M-APKERNEL45` : FORMAL PASS

With `h = k₁ − k₂`, `K = k₁ + k₂`, `v` an inverse of `2 (mod ℓ)`,
`w = (us)⁻¹` and `A₀ = −2w`:

```
centered_ap_phase_identity :
  v·(k₁+k₂)·(A₁−A₂) + v·(k₁−k₂)·(A₁+A₂+4w)
    = k₁·(A₁−A₀) − k₂·(A₂−A₀)        (in ZMod ℓ)
```

together with

```
centered_A0_spec        :  us·w = 1  →  A₀ = −2w  →  us·A₀ = −2
centered_target_of_unit :  IsUnit us → us·A = −2 → us·A₀ = −2 → A = A₀
```

### §2 — full `h,K` orthogonality

```
Rfull ℓ A₁ A₂ A₀ := ℓ⁻² · Σ_{k₁,k₂ mod ℓ} e_ℓ(k₁(A₁−A₀) − k₂(A₂−A₀))

Rfull_eq_indicator : Rfull = 1_{ℓ ∣ A₁−A₀} · 1_{ℓ ∣ A₂−A₀}
Rfull_eq_one_of_unit : under us·A_i ≡ −2 and us·A₀ ≡ −2 with us a unit, Rfull = 1
```

No analytic assumption is used.

### §3 — sampled double-major operators — `C4SHIFT-1M-CENTERED-KERNEL45` : FORMAL PASS

```
M⁺_{ℓ,ξ}(n) = ℓ⁻¹ Σ_{k mod ℓ} M₄((ξ−k)/ℓ) e_ℓ(kn)
M⁻_{ℓ,ξ}(n) = ℓ⁻¹ Σ_{k mod ℓ} M₄((ξ−k)/ℓ) e_ℓ(−kn)

RMM_factor  : R_MM(A₁,A₂) = M⁺_{ℓ,ξ₁}(A₁−A₀) · M⁻_{ℓ,ξ₂}(A₂−A₀)
R1m_centered: R_1m = R_full − R_MM
```

with `ξ₁ = s(uθ−η)`, `ξ₂ = −sη` supplied at the call site (the identities are
proved for arbitrary `ξ₁, ξ₂`).

### §4 — owner decomposition — `C4SHIFT-1M-LEAFWISE-CENTERING45` : FORMAL DECOMPOSITION PASS

```
m⁺ = APδ⁺ − M⁺ ,  m⁻ = APδ⁻ − M⁻

R1m_owner_decomposition :
  R_1m = m⁺·M⁻ + M⁺·m⁻ + m⁺·m⁻
```

Owners recorded exactly as `ownerMm`, `ownermM`, `ownermm`
(`R1m_owners`). **No analytic bound is attached to any owner.**

---

## AP-INDEX FOURIER

### §5 — major-projector aliasing — `C4SHIFT-MAJORPROJECTOR-HKFOURIER45` : FORMAL ALGEBRAIC PASS

For the finite Fourier model `M4model(x) = Σ_{r ∈ R} M̂₄(r) e(rx)`:

```
Mplus_aliasing  : M⁺_{ℓ,ξ}(n) = Σ_{r ∈ R, r ≡ n (mod ℓ)}  M̂₄(r) e(rξ/ℓ)
Mminus_aliasing : M⁻_{ℓ,ξ}(n) = Σ_{r ∈ R, r ≡ −n (mod ℓ)} M̂₄(r) e(rξ/ℓ)
```

This is the exact finite analogue of the `ℤ`-indexed aliasing identity: the
repository's representation of `M₄` is finite, so the finite analogue is what
is proved. **No decay and no total major-arc measure is formalised.**

---

## PHYSICAL 2+2 SHIFT

### §7 — `C4SHIFT-2PLUS2-PHYSICAL-SHIFT45` : FORMAL PASS

`Physical2Plus2Shift` carries the actual shifted tuple source:

```
A₁ = X₁Z₁ ,  A₂ = X₂Z₂
shift      : X₂Z₂ − X₁Z₁ = ℓ·r
rne        : r ≠ 0                (tuple-level source restriction, never relaxed)
gdef       : g = s·r + h₂ − h₁
```

Proved from it:

```
shift_A       : A₂ − A₁ = ℓ·r
shift_product : X₂Z₂ − X₁Z₁ = ℓ·r
g_relation    : g = s·r + h₂ − h₁
```

`|g| > L^{B₁}` is **not** formalised (it is not represented as an explicit
source predicate in the repository).

---

## BEZOUT NORMAL FORM

### §8 — `C4SHIFT-BEZOUT-2PLUS2-NORMALFORM45` : FORMAL PASS

```
bezout_2plus2_normalform :
  X₁ = d·a , X₂ = d·b , d = g₀·d₀ , ℓ = g₀·ℓ₀ , g₀ ≠ 0 , d₀ ≠ 0 ,
  IsCoprime d₀ ℓ₀ , X₂Z₂ − X₁Z₁ = ℓ·r
    ⟹  d₀ ∣ r  ∧  ∃ r₀, r = d₀·r₀ ∧ b·Z₂ − a·Z₁ = ℓ₀·r₀
```

The intermediate identity `d₀(bZ₂ − aZ₁) = ℓ₀ r` is derived by cancelling `g₀`;
`d₀ ∣ r` uses coprimality of `d₀` and `ℓ₀`, and the final equation is obtained
by cancelling `d₀`.

### §9 — `C4SHIFT-BEZOUT-SOLUTION-LINE45` : FORMAL PASS

```
bezout_solution_line_forward :
  b Z₂⁰ − a Z₁⁰ = rhs  ⟹  b(Z₂⁰+at) − a(Z₁⁰+bt) = rhs

bezout_solution_line_converse :
  IsCoprime a b, a ≠ 0, b Z₂⁰ − a Z₁⁰ = rhs, b Z₂ − a Z₁ = rhs
    ⟹  ∃ t, Z₁ = Z₁⁰ + b t ∧ Z₂ = Z₂⁰ + a t

bezout_line_card_bound :
  b > 0, T nonempty, ∀ t ∈ T, lo ≤ Z₁⁰ + b t ≤ hi
    ⟹  (#T − 1)·b ≤ hi − lo
```

The cardinality bound is the exact box count along the line (via `min'`/`max'`
and `Int.card_Icc`). **No square-root cancellation along `t` is claimed.**

---

## ANALYTIC FIREWALL

* **State count.** `ell_state_count_no_saving` :
  `ℓ⁻² · #{(k₁,k₂) mod ℓ} = 1`. Recorded explicitly in the new status file as
  **NO AUTOMATIC 1/ℓ² SAVING**.
* **Nonzero-shift firewall.** `Physical2Plus2Shift.true_diagonal_excluded` :
  `r ≠ 0` and `ℓ ≠ 0` exclude the *true* product diagonal `A₁ = A₂`. This is
  **not** the congruence: `congruence_mod_ell` shows `ℓ ∣ A₂ − A₁` always holds
  on the source, and `congruence_not_equality` gives an explicit witness
  (`ℓ = 5`, `A₁ = 0`, `A₂ = 5`) that congruence does not imply equality. The
  distinction is load-bearing and is recorded as its own status row.
* **No analytic inhabitant.** The new socket
  `C4ShiftOffdiagCenteredAP58GramInput` is never constructed; only the trivial
  conditional consumer `centeredAP58_conditional_consumer` exists. The two
  previous sockets remain uninhabited.
* **5/8 scaling is research metadata only.** Four-product size `Y⁴`, AP modulus
  `ℓ ~ Y^{5/2}`, nominal level `5/8`, physical AP-line length `T = Y⁴/ℓ ~
  Y^{3/2}`, required norm `Y^{3/4}L^C = T^{1/2}L^C`, current coefficient-blind
  norm `Y^{3/2}L^{C₀} = T·L^{C₀}`. None of this is formalised as a real-power
  claim.

---

## STATUS SUPERSESSION

```
C4SHIFT-ONE-FOURPRODUCT-MINOR45      : OLD CLOSURE RETRACTED.
C4SHIFT-ONE-MINOR-PUSHED-ENERGY45    : STRICTLY REDUCED /
                                       OLD FIRST RESIDUAL SUPERSEDED.
                                       (NOT false — its analyticOpen row in the
                                        previous layer is preserved and is
                                        witnessed by
                                        `previous_layer_preserved`.)
C4SHIFT-1M-APKERNEL45                : FORMAL PASS.
C4SHIFT-1M-CENTERED-KERNEL45         : FORMAL PASS.
C4SHIFT-MAJORPROJECTOR-HKFOURIER45   : FORMAL ALGEBRAIC PASS.
C4SHIFT-1M-LEAFWISE-CENTERING45      : FORMAL DECOMPOSITION PASS /
                                       NO ANALYTIC CLOSURE.
C4SHIFT-2PLUS2-PHYSICAL-SHIFT45      : FORMAL PASS.
C4SHIFT-NONZERO-SHIFT-FIREWALL45     : FORMAL PASS.
C4SHIFT-BEZOUT-2PLUS2-NORMALFORM45   : FORMAL PASS.
C4SHIFT-BEZOUT-SOLUTION-LINE45       : FORMAL PASS.
C4SHIFT-ELL-STATECOUNT-FIREWALL45    : NO AUTOMATIC 1/ell^2 SAVING.
C4SHIFT-5/8-SCALING45                : RESEARCH METADATA ONLY.
C4SHIFT-QFOURIER-PUSHFORWARD45       : OPEN.
TOPBAND                              : OPEN.
PURE5                                : NOT RUN.
GATE1B                               : OPEN.
```

No CLOSED analytic row exists (`no_closed_analytic_row`, `no_closed_rows`,
`ledger_is_honest`).

---

## CURRENT RESIDUAL

```
CURRENT FIRST EXACT ANALYTIC RESIDUAL :
  C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45

EQUIVALENT SHARPER NAME :
  C4SHIFT-1M-BEZOUT-2PLUS2-GRAM45

PARALLEL LOCAL RESIDUAL :
  TOPBAND-BROAD-MAJOR-TREE-MATCH45 : SOURCE OPEN.
```

The socket `C4ShiftOffdiagCenteredAP58GramInput` retains, as literal fields:
the AP modulus `ℓ`, the sampled frequencies `ξ₁, ξ₂`, the projector `M₄`, the
centered residue `A₀`, the physical `2+2` source (with `r ≠ 0`), the Bézout
data `a, b, ℓ₀, r₀` with `IsCoprime a b` and `b Z₂ − a Z₁ = ℓ₀ r₀`, the actual
`α_j / γ_j` coefficients, a linked top-band source predicate, and the pushed
`L¹_θ ℓ²_v` target expressed through the three owners `mM`, `Mm`, `mm`.

---

## AXIOM AUDIT

`Gate1B/AxiomAuditGate1BC4ShiftCenteredAP58.lean` prints axioms for all 52
principal new declarations. The union of reported axioms is exactly

```
{ propext, Classical.choice, Quot.sound }
```

with many declarations depending on none. There is **no** `sorryAx`, no
`sorry`, no `admit`, no `axiom`, no `opaque`, no `unsafe`, no `native_decide`
and no `@[implemented_by]` in any new module.

---

## BUILD

Targeted builds (the global build is still blocked by the pre-existing,
unrelated missing module `RequestProject/FixedCertificateAlgebra.lean`, which
was **not** repaired and which no new module imports):

```
lake build Gate1B.C4ShiftCenteredAPKernel                  ✔ 8042 jobs
lake build Gate1B.CurrentStatusGate1BC4ShiftCenteredAP58   ✔ 8082 jobs
lake build Gate1B.AxiomAuditGate1BC4ShiftCenteredAP58      ✔ 8083 jobs
```

All succeed with zero errors.

---

## COMMITS

The delta is committed as a single append-only commit adding the three new
Lean modules and this report. No pre-existing file was modified.

## PUSH

Pushed to `origin`.

---

## FINAL

```
GATE1B OPEN.

FIRST EXACT ANALYTIC RESIDUAL:
C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45.

PARALLEL LOCAL RESIDUAL:
TOPBAND-BROAD-MAJOR-TREE-MATCH45.
```
