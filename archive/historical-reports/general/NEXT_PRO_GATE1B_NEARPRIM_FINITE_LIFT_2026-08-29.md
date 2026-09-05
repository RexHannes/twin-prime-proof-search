# GOLD CLOSE 1B — near-primitive finite-lift phase decorrelation

GATE 1B ONLY. Do mathematics, not bookkeeping.

## Current first exact residual

`DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45`.

### Bank — do not reopen

- determinant shell and character transfer;
- source-minimal high-conductor pairing;
- `C<=Y` conductor range power closed;
- principal / low conductor / exceptional / finite-profile routers;
- rare spikes and amplitude-imbalanced packets routed;
- ordinary character geometry is unitary / natural scale;
- one unrestricted `TT*` / old Gram is a representation loop;
- conductor-local exact-lift energies;
- `DETLINE-LARGE-LIFT-DISPERSION45`: closed;
- all `e >= (log X)^(B_A)` closed with arbitrary log saving;
- mixed/two-copy lift dispersion creates no new rank;
- surviving range `1 <= e <= (log X)^(B_A)`, `ell=ce~R`, `c~R/e=R log^(-O_A(1))`;
- finite lifts introduce only polylogarithmically many local additive/coprimality twists.

At exact lift `e`, current natural bound is

`|T_j(e)| << X e^(-3/2) log^(C0) X`.

At `e=1` this is only natural scale. Required: `X log^(-A) X`.

Do not merely restate that a relative phase gap is needed.

## Stage A — compress the finite lift completely

For each `e <= log^(B_A) X`, use the exact local decompositions

`1_{uAs=-2 mod e} = e^(-1) sum_{nu mod e} e_e(nu(uAs+2))`

and

`1_{(s,e)=1} = sum_{a|(s,e)} mu(a)`.

Prove that the whole finite-lift family is a polylogarithmic combination of source-exact near-primitive core packets with fixed local twists. Track the total `e,nu,a` cost.

If the local twists can be absorbed into the existing coefficient classes with only `log^(O_A(1))` cost, bank:

`DETLINE-FINITELIFT-LOCAL-TWIST-COMPRESSION45: PASS`.

If not, print the first literal obstruction and stop.

## Stage B — remove the primitive-projector bookkeeping

For fixed `(c,e)`, start from the primitive projector

`P_c(s1,s2)=sum_{r|(c,s1-s2)} phi(r) mu(c/r)`.

Use the near-primitive no-wrap fact `c > 4 max|s|^2`.

Separate exactly:

1. the `r=c` diagonal `s1=s2` contribution;
2. all proper-divisor projector pieces.

Test whether every proper-divisor piece is already a lower-conductor/local-profile child and can be routed with arbitrary logarithmic saving.

If yes, reduce the hard finite-lift theorem to the physical correlation

`sum_{c~R/e} sum_s rho_j(s) conjugate(C_{j,ce}(s))`

with the exact weights/prefactors printed.

Call this reduction only if literal:

`DETLINE-NEARPRIM-PRIMITIVE-PROJECTOR-TO-PHYSICAL45: PASS`.

## Stage C — exploit what broad-minor actually means

Open the exact definition

`rho_j = delta_j - lambda_j`,

where `delta_j` is the actual prime-minus-model source and `lambda_j` is the broad additive-major projection/inverse kernel.

Do not replace `rho_j` by arbitrary coefficients.

Print the exact additive Fourier/projection statement satisfied by `rho_j`.

Determine whether there is an exact or quantitative orthogonality:

`<rho_j, P_major F> = 0` or `<< Y log^(-A) X * ||F||`

for the actual major span used in the recursive major tree.

This step must distinguish the internal broad-minor projection from the later physical comparison/main-term match. Do not use `TOPBAND-BROAD-MAJOR-TREE-MATCH45` as an unproved cancellation input.

## Stage D — compute the additive spectrum of the determinant companion

For fixed `ell=ce`, define

`C_{j,ell}(s) = sum_{u,A,d,p,h: dp ell-uAs=2+u ell h} a4(u)c4,j(A) mu(d) log p kappa(h) W`.

Compute its additive Fourier transform in `s`:

`Chat_{j,ell}(alpha)=sum_s C_{j,ell}(s) e(alpha s)`.

Use the exact shell in the form

`ell (dp-u h) = u A s + 2`.

Derive a source-exact normal form for `Chat` before applying any estimate.

Test whether the spectrum splits as

`C = C_major + C_minor`

where:

- `C_major` lies in the already-defined broad-major span and is annihilated by `rho_j`;
- `C_minor` has an independently provable arbitrary-log or fixed-power norm saving.

If this works, close the physical correlation directly.

## Stage E — if a minor spectrum remains, attack it rather than returning to characters

For the exact minor-spectrum normal form from Stage D, test in this order:

1. additive large sieve / dual large sieve in the `c~R/e` family;
2. dispersion in the divisor relation `ell(dp-u h)=uAs+2`;
3. Poisson/completion only if it generates a literal Kloosterman or trace kernel;
4. Möbius-sensitive cancellation while `mu(d)` remains linear;
5. prime uniqueness / divisor-switch only if it removes a genuinely free dimension.

Do not invoke Burgess, Motohashi, MQW, Blomer–Pascadi, Gate 1A, or a generic trace theorem unless the literal source after Stage D matches its hypotheses slot-for-slot.

Do not use another unrestricted `TT*` if it simply returns the old rank-two determinant surface.

## Stage F — binary closure test

Attempt to prove uniformly for `j=1,...,5` and `1<=e<=log^(B_A)X`:

`sum_{c~R/e} sum_s rho_j(s) conjugate(C_{j,ce}(s)) <<_A X log^(-A) X / log^(B_A+10) X`

(or the exact normalized equivalent sufficient after summing finite lift/local twist cells).

If yes:

- `DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45: CLOSED`;
- `DETLINE-HIGHCOND-BETA-RHO-CROSSPAIR45: CLOSED`;
- `TOPBAND-BETA-BROADMINOR-DETLINE45: CLOSED` for all five leaves;
- then close `TOPBAND-BETA-ONE-REMAINDER-CRT-PAIRING45` and `TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45` if their remaining work is only the already-banked reconstruction.

Only then run the independent local theorem `TOPBAND-BROAD-MAJOR-TREE-MATCH45`.

## Stage G — only if the finite-lift theorem closes

If analytic recursive-major-tree closure and local broad-major match both pass, continue sequentially:

`SHIFTED-MAM-TOPBAND45 -> RANKONE-ENDPOINT-ALLK45 -> PURE5 -> lower defects -> NearPrim -> r>1 -> QK56 -> source reassembly -> GATE1B`.

At the first literal failure, stop and print one exact residual.

## Stage H — if Stage F fails

Do not return `DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45` unchanged.

Print the smallest theorem exposed by the additive-spectrum analysis, preferably one of the form

`DETLINE-NEARPRIM-ADDITIVE-MINOR-SPECTRUM45`

or a still narrower source-exact child, with:

- exact variables/ranges;
- exact Fourier kernel;
- coefficient norms;
- current bound;
- required saving;
- whether the missing mechanism is additive-major concentration, additive-minor dispersion, Möbius cancellation, or another literal phenomenon.

## Required output

- FINITE-LIFT LOCAL TWIST COMPRESSION: ...
- PRIMITIVE PROJECTOR PROPER-DIVISOR ROUTING: ...
- PHYSICAL CORRELATION NORMAL FORM: ...
- BROAD-MINOR ORTHOGONALITY: ...
- COMPANION ADDITIVE FOURIER TRANSFORM: ...
- MAJOR-SPECTRUM PART: ...
- MINOR-SPECTRUM PART: ...
- ADDITIVE/DISPERSION PROVIDER: ...
- FINITE-LIFT PHASE DECORRELATION: ...
- `DETLINE-NEARPRIM-FINITELIFT-DENSE-SATURATION45`: ...
- `DETLINE-HIGHCOND-BETA-RHO-CROSSPAIR45`: ...
- `TOPBAND-BETA-BROADMINOR-DETLINE45`: ...
- `TOPBAND-RECURSIVE-MAJOR-TREE-PAIRING45`: ...
- `TOPBAND-BROAD-MAJOR-TREE-MATCH45`: NOT RUN unless analytic child closes.
- `GATE1B`: OPEN unless every required downstream child literally closes.

Final line:

`GATE1B OPEN — FIRST EXACT RESIDUAL: <smallest surviving source-exact theorem>`

Only if every Gate-1B child actually closes: `GATE1B CLOSED`.
