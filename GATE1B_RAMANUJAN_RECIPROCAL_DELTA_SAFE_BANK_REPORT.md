# GATE 1B — RAMANUJAN–RECIPROCAL DELTA SAFE BANK REPORT

Append-only delta layer.  Four new Lean modules plus one axiom-audit module; no
historical file was modified.

PREVIOUS GATE1B BANK:
PRESERVED.  `CurrentStatusGate1BAdditiveMinor.lean` **was already present** and
is imported unchanged (together with `CurrentStatusGate1BFiniteLift`,
`CurrentStatusShiftedMAMOperator`, `CurrentStatusHighKShift`).  Nothing was
rewritten, renamed, weakened or re-proved.

ACTUAL DEFECT SOURCE:
SOURCE OPEN / ADAPTER UNINHABITED.  A repository-wide search finds **no literal
definitions** named `delta_j`, `lambda_j`, `rho_j` or `Pi_ell`; the additive-minor
layer carries them only as abstract fields (`Pi`, `deltaHat`, `rhoHat`) of
`AdditiveMinorCrosspairData`.  Therefore no synthetic replacement was created.
`AddMinSource.AddMinActualDefectSourceInput` is an **uninhabited** adapter whose
fields are exactly the two source equations
`δ_j(s) = (Λ(s)−1) W_j(s/Y)/log s` and `ρ̂_{j,ℓ}(m) = (1−Π_ℓ(m)) δ̂_{j,ℓ}(m)`.
The conditional compiler `defectSource_adapter_muLog` (adapter → μ·log form) is
kernel-proved.  The second equation is *already* available in the actual
additive-minor data (`AdditiveMinorCrosspairData.rhoHat_form`) and is reused.

MU*LOG:
KERNEL-PROVED, REUSED FROM MATHLIB.  `AddMinSource.vonMangoldt_eq_moebius_log_divisorSum`:
`Λ(n) = ∑_{ab=n} μ(a) log b`, obtained from
`ArithmeticFunction.moebius_mul_log_eq_vonMangoldt` and unfolded to the literal
`divisorsAntidiagonal` sum; `oneSided_muLog_expansion` and
`defectSource_muLog_form` give the one-sided source expansion.  No Type-I/II
analytic estimate was formalised.

gcd(uA,ell):
`cleanSector_coprime_N_ell` — kernel-proved **from the source interface field**
`coprime_uA_ell`.

gcd(uA,M):
`cleanSector_coprime_N_M` — kernel-proved from `M` prime together with the
routing condition `M ∤ uA` (physical box separation).  It is **not** justified by
`N < M`: `size_alone_does_not_give_coprimality` (`N = M = 5`) and
`source_product_can_exceed_M` (`u = A = M = 7`, `uA = 49 > M`, not coprime)
refute that route in Lean.

gcd(uA,qell):
`cleanSector_coprime_N_qell` — `gcd(uA, ℓM) = 1`, kernel-proved from the two
above.

COPRIMALITY RESIDUAL:
The two hypotheses `M ∤ uA` and `gcd(uA, ℓ) = 1` are **not** derivable from
anything currently in the repository, because the physical source boxes are not
defined here.  They are collected in the uninhabited interface
`AddMinCleanCoprimalityInput`, and every reciprocal theorem that needs them takes
them as printed hypotheses.  These are the smallest missing source lemmas.

RAMANUJAN DIVISOR IDENTITY:
KERNEL-PROVED.  `ramanujanC rRam B = ∑_{x mod rRam, gcd(x,rRam)=1} e_{rRam}(xB)`
(built from the repository's additive character `ezExp`), Hölder form
`ramanujanC_hoelder`, and
`ramanujan_divisor_sum : ∑_{rRam ∣ N} c_{rRam}(B) = if N ∣ B then N else 0`
with the two explicit branches `_of_dvd` / `_of_not_dvd`.  The indicator is not
hidden in a definition.  The divisor variable is named `rRam` throughout.

MODULAR INVERSE QUOTIENT:
KERNEL-PROVED.  `exists_int_inverse` (Bézout), `zmod_inv_mul_cancel`
(`N⁻¹·(N·t) = t` in `ZMod q`), `inv_quotient` (`q ∣ invN·(N t) − t`) and
`ezExp_inv_quotient` (`e_q(m invN (N t)) = e_q(m t)`).  No ambiguous integer
division remains anywhere in the normal form.

RAMANUJAN RECIPROCITY:
KERNEL-PROVED.  `addMin_ramanujan_reciprocity`:
`1_{N∣B} e_q(m B/N) = (1/N) e_q(m N⁻¹ B) ∑_{rRam ∣ N} c_{rRam}(B)`,
proved by the two cases (`N ∤ B`: both sides zero; `B = N t`: divisor sum `= N`,
inverse phase `=` quotient phase).  Hypotheses printed: `0 < N`,
`q ∣ N·invN − 1`.

INVERSE REDUCTION qell -> M:
KERNEL-PROVED.  `inv_reduction_qell_to_M` (`M ∣ q_ℓ` transports the congruence)
and `inv_unique_mod_M` (any two inverses agree mod `M`), so the reduction of
`invN_{q_ℓ}` to `ZMod M` *is* `invN_M`.  The identification was **not** assumed.

RECIPROCAL PHASE NORMAL FORM:
KERNEL-PROVED.  With `B_det = ℓ(dp − uh) − 2` and `q_ℓ = ℓM`:
`phase_split_qell`, `ezExp_M_inv_reduction`, `phase_split_rRam` and
`reciprocal_phase_normalForm`:
`e_{q_ℓ}(m invN B_det) · e_{rRam}(x B_det)
   = constantPhase(−2) · phase_Θ(dp − uh)`, with
`Θ = m invN_M / M + x ℓ / rRam` realised as a product of additive characters
(no real representatives).  The fixed shift `2` is carried in the constant phase;
nothing is averaged over shifts.  Assembled into the companion compiler
`addMin_companion_ramanujan_normalForm`, which rewrites the companion transform
as a sum over the tuples `(u,A,d,p,h)`, the moving divisors `rRam ∣ uA` and the
units `x mod rRam`.  The literal rough transform `roughTransform` keeps
`μ(d)`, `log p`, `κ(h)`, `u` and `Θ` separate.

QUOTIENT COUPLING:
REMOVED from the rough coefficient.  `old_representation_depends_on_quotient`
shows in Lean that the old phase `e_q(m·B/N)` genuinely varied with `N`;
`reciprocal_summand_is_quotient_free` shows the new summand takes no quotient
argument.

NEW COUPLING:
moving `rRam ∣ uA` + reciprocal `(uA)⁻¹` phase (reduced from `mod q_ℓ` to
`mod M`) + `roughTransform(Θ)` at the same `Θ`.  Recorded explicitly
(`new_coupling_is_present`, ledger row
`DETLINE-ADDMIN-QUOTIENT-REMOVAL-FIREWALL45`); it is **not** claimed to be
removed.

COMPLETE RAMANUJAN REASSEMBLY:
`ramanujan_reassembly_is_divisibility_projector` :
`(1/N) ∑_{rRam ∣ N} c_{rRam}(B) = 1_{N ∣ B}` — summing the whole family returns
the original physical divisibility projector.  Recorded as a representation
loop; **no** analytic TT\* loop is claimed.

OLD ADDITIVE-MINOR FRONTIER:
`DETLINE-NEARPRIM-ADDITIVE-MINOR-CROSSPAIR45` —
SUPERSEDED AS CONTROLLING FRONTIER / STRICTLY REDUCED; **NOT FALSE**
(`historical_additiveMinor_frontier_not_false`, and its original `analyticOpen`
row is preserved in the previous layer:
`previous_additiveMinor_layer_preserved`).

CURRENT FIRST EXACT RESIDUAL:
`DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45` — ANALYTIC_OPEN.

ANALYTIC SOCKET:
UNINHABITED.  `AddMinRamanujanSocket.DetLineAddMinRamanujanReciprocalCrosspairInput`,
over the source-preserving configuration `RamanujanReciprocalConfig` which keeps
`e`, `c`, `ℓ = ce`, `q_ℓ = ℓM`, `m`, `ρ̂(m)`, `u`, `A`, `rRam ∣ uA`,
`x mod rRam` unit, `inv(uA)` mod `q_ℓ` and mod `M`, `Θ`, `μ(d)`, `log p`,
`κ(h)` and `roughTransform`.  No `L²` abstraction was substituted, and no
inhabitant is constructed anywhere in the repository.

RESEARCH METADATA (not formalised, not marked false):
* `DETLINE-ADDMIN-ONE-SIDED-VAUGHAN45` — NONCLOSING AS STANDALONE ROUTE.
* `DETLINE-ADDMIN-MOBIUS-PRIME-DISPERSION45` — NO POINTWISE ONE-SIDED CLOSURE AT
  CURRENT RESEARCH BOUNDS.
* `DETLINE-COMPANION-ADDMIN-ENERGY45` — OPEN, stronger sufficient route.
* `DETLINE-ADDMIN-DOUBLE-SOURCE-RANKGAIN45` — REPRESENTATION LOOP.

TOPBAND:
OPEN.  PURE5: OPEN.  GATE1B: OPEN.

TARGETED BUILDS:
PASS for all five new modules
(`AddMinSourceCoprimalityMuLog`, `AddMinRamanujanReciprocity`,
`DetLineAddMinRamanujanReciprocalSocket`,
`CurrentStatusGate1BRamanujanReciprocal`,
`AxiomAuditGate1BRamanujanReciprocal`), 8069 jobs, 0 errors.  No `sorry`,
`admit`, `axiom`, `opaque`, `unsafe`, `native_decide` or `@[implemented_by]` in
the new files.

GLOBAL BUILD:
STILL BLOCKED BY THE PRE-EXISTING, UNRELATED LEGACY FAILURE: the missing module
`RequestProject.FixedCertificateAlgebra`, imported by the legacy files
`R9LeakageArithmetic.lean` and root-level `K0K1Status.lean`.  Not repaired
(out of scope, append-only run); none of the new modules imports it.

AXIOM AUDIT:
`RequestProject/CurrentProgramme/AxiomAuditGate1BRamanujanReciprocal.lean` —
48 principal declarations printed; the union of all reported axioms is exactly
`{propext, Classical.choice, Quot.sound}`.  No `sorryAx`, no `Lean.ofReduceBool`.

FINAL FIREWALL:

    This layer proves/reproves only exact finite arithmetic, modular inverse,
    Ramanujan and phase-normal-form algebra.

    It does NOT prove the required source-coupled arbitrary-log
    Ramanujan–reciprocal crosspair estimate.

    Therefore TOPBAND, PURE5 and GATE1B remain OPEN.

    GATE1B OPEN — FIRST EXACT RESEARCH RESIDUAL:
    DETLINE-ADDMIN-RAMANUJAN-RECIPROCAL-CROSSPAIR45.
