/-
# Gate 1B safe extensions — SOURCE INTERFACES (comments only)

THIS FILE CONTAINS NO DECLARATIONS.

```text
NPL_OFF45                      ANALYTIC INTERFACE — OPEN
  required: |E_off| <= R * B2 * C2 * log^{-B}
  shared-p topology            OPEN
  shared-d / cross-role        OPEN
  all-coprime topology         OPEN

NPL45_GLOBAL                   OPEN
NPL_SIGNED_TRANSPORT45         OPEN
ROUTE_BV45                     SOURCE-OPEN (routing multiplicity not supplied)
LC_BV45_ANALYTIC_APPLICATION   external analytic theorem
LC_REASSEMBLY45                OPEN
RLS45                          OPEN
C4_SFL45                       external analytic theorem
DRAPPEAU_FAMILY_TRANSCRIPTION  external analytic theorem
PASCADI_NONABELIAN_APPLICATION external analytic theorem
BLOMER_PASCADI_APPLICATION     external analytic theorem
E(q), Z_E(q), KAPPA4           open / source missing
SOURCE_FACE_COMPLETENESS       OPEN
FIXED_SWITCHED_REASSEMBLY      OPEN
GATE1B_CLOSED                  OPEN — no theorem of this name exists
FULL_TYPE_II                   not inferred
TWIN_PRIMES                    not inferred
```

Reuse note: the centered factorisation identity
`ρ_{dp} = ρ_d ρ_p + ρ_d/p + ρ_p/d` for coprime `d, p` is ALREADY banked in this project as
`Gate01Consolidation.rho_mul_coprime` (RequestProject/NANC/Gate01Consolidation/
CRTCentering.lean) and is deliberately NOT duplicated here.
-/
