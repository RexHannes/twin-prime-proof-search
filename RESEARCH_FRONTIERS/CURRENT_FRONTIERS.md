# CURRENT RESEARCH FRONTIERS

Last reconciled: 2026-08-30

Purpose: current-state locator for Gate 1B and Erdős #287. This is not itself a proof. Historical provenance belongs in the append-only proof indexes. The directory is mirrored in both research repositories.

---

## Gate 1B

**Status:** `GATE1B OPEN`

**Current first analytic residual (research-exact; quantitative promotion audit pending):**

`C4SHIFT-BEZOUT-DUAL-R0ELL45`

**Parent strictly reduced:** `C4SHIFT-OFFDIAG-CENTERED-AP5/8-GRAM45`.

**Parallel local/source residual:**

`C4SHIFT-BEZOUT-ZEROMODE-LOCALMATCH45`, as the current Bézout-fibre component of `TOPBAND-BROAD-MAJOR-TREE-MATCH45`.

**True target:**

\[
\|\widehat H_j^\perp\|_{L^1_\theta\ell_v^2}\ll Y^{3/4}L^C.
\]

### Latest exact geometry

On the clean determinant-two sector,

\[
(A_i,\ell)=1,\qquad X_i\mid A_i
\]

forces

\[
(d,\ell)=1,
\]

so the previous `g0, d0, ell0` bookkeeping disappears from the analytic child. With

\[
X_1=da,\quad X_2=db,\quad (a,b)=1,
\]

and `r=d r0`, the physical shift is exactly

\[
bZ_2-aZ_1=\ell r_0.
\]

A Bézout parametrisation is

\[
Z_1=\ell r_0\kappa_{a,b}+bt,\qquad
Z_2=\ell r_0\bar b_a+at,
\]

with physical line length `T_d ~ d` in interior packets.

The physical AP condition becomes one residue independent of `r0`:

\[
t\equiv -2\overline{usdab}\pmod\ell.
\]

The run reports a rigidity statement that for fixed `(d,a,b,ell)` at most one physical `(r0,t)` survives. This statement is source-critical and should be checked in the next promotion audit including the possibility that two admissible `t` values differ by a multiple of `ell`.

### Centered t-dual decomposition

The exact cyclic Fourier coefficient of the centered line kernel is

\[
\widehat K_{\rm cent}(\nu)
=
\frac{e_\ell(-\nu\tau)}{\ell}
\left[1-\frac1\ell\sum_{k\bmod\ell}
\mathcal M_1(k+\nu\bar c)\overline{\mathcal M_2(k)}\right],
\]

where `c=dab mod ell` and `tau=A0 inverse(c) mod ell`.

The zero dual mode is **not zero**; it is routed to the local/source branch:

`C4SHIFT-BEZOUT-ZEROMODE-LOCALMATCH45`.

The analytic branch retains only `nu != 0` and has reciprocal phase

\[
e_\ell\!\left(2\nu\overline{usdab}\right)
\]

against the exact shifted two-coordinate gamma source.

After opening

\[
\gamma_j(Z)=\sum_{xy=Z}g_{j,1}(x)g_{j,2}(y),
\]

the source satisfies

\[
bx_2y_2-a x_1y_1=\ell r_0
\]

and the nonzero dual phase can be represented using

\[
e_\ell(\nu t)=e_\ell(\nu\bar b\,x_1y_1).
\]

No literal published/banked Kloosterman provider has yet been matched to this coupled source.

### Provisional quantitative D-census (PROMOTION AUDIT PENDING)

Let

\[
T=Y^{3/2}L^{O(1)},\qquad d\sim D.
\]

The latest run claims the source-energy estimate

\[
\mathcal N_D
\ll
Y^{3/4}\sqrt{\min(D,T/D)}L^C.
\]

Consequences claimed in that run:

- boundary bands `D <= L^B` or `D >= T L^{-B}` close;
- central band `L^B < D < T L^{-B}` remains;
- worst point `D=T^{1/2}=Y^{3/4}` gives achieved `Y^(9/8)` versus required `Y^(3/4)`;
- residual deficit is reduced from `Y^(3/4)=X^(1/12)` to `Y^(3/8)=X^(1/24)`.

These are **provisional analytic promotions** until a narrow hostile audit checks the rigidity/multiplicity step and the row/column norm derivation. Do not yet treat the boundary closure or `X^(1/24)` deficit as publication-banked.

### Current missing mechanism

Joint cancellation of the nonzero `t`-dual reciprocal phase

\[
e_\ell\!\left(2\nu\overline{usdab}\right)
\]

against the exact shifted two-coordinate gamma source, preserving the coupled `r0, ell` family. The kernel itself has no `r0` phase, so any `r0` gain must come from the gamma-line source.

### Do not reopen

- pointwise one-four-product minor norm promotion — retracted;
- scalar minor `L2` energy — natural scale only;
- false additive factorisation of Dirichlet convolution;
- old reciprocal-residue incidence tax;
- `r=0` positive diagonal;
- generic `5/8` BV as a substitute for the source-exact theorem.

### Next action

Before a broader construction run, hostile-audit the D-census promotion: fixed `(d,a,b,ell)` physical multiplicity, alpha/gamma source-energy claims, row/column bounds, boundary-D closure, and the claimed `X^(1/24)` residual. If it passes, attack `C4SHIFT-BEZOUT-DUAL-R0ELL45` directly.

---

## Erdős Problem #287

**Status:** `ERDOS287 OPEN`.

**Uniform `k=0`:** open. **FCL:** not reached.

**Current first main-line residual (research-exact Case-B child; promotion audit pending):**

`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45`.

**Parent strictly reduced:**

`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45`.

### Latest primitive-fraction reduction

For fixed `d`, with `M=G/d`, the primitive frequencies

\[
\frac{t}{dm},\qquad m\asymp M,\quad (m,d)=1,\quad (t,dm)=1
\]

have spacing

\[
\Delta_d\ge \frac1{4dM^2}=\frac{d}{4G^2}.
\]

Thus the fixed-`d` separated additive large sieve has candidate constant

\[
A+\frac{G^2}{d}.
\]

The latest run also reports:

\[
\rho(a)=\mathbf 1_{P^+(a)\le Y_\rho}|V(a/A)|,
\qquad 0\le\rho(a)\ll1,
\]

so the weighted reduction costs no logarithm, and from

\[
E_g\ll(gB+B^2)L^{C_E}
\]

one gets

\[
\sum_{m\asymp G/d}\frac{E_{dm}}{m^2}
\ll dB\left(1+\frac BG\right)L^{C_E}.
\]

Using `lambda_H=mu*Omega_H`, with the reported smooth dyadic projector normalisation,

\[
S_1:=\sum_{d\le CG}\frac{|\lambda_H(d)|}{d}\ll L,
\qquad
S_2:=\sum_{d\le CG}\frac{|\lambda_H(d)|}{d^2}\ll H^{-1}.
\]

Hence the research candidate global estimate is

\[
|Q_H|
\ll
B\left(1+\frac BG\right)L^{C_E}
\left[
A\log\left(\frac{2G}{H}\right)+\frac{G^2}{H}
\right].
\]

With `AB\asymp X`, the sharp normalised ratio is

\[
\frac{|Q_H|}{AB^2}
\ll
L^{C_E+1}\left(\frac1B+\frac1G\right)
+
L^{C_E}
\left(
\frac{G^2}{HX}+\frac{G}{HA}
\right).
\]

### Case-B narrowing

The latest run reports fixed-power lower bounds on the surviving `A,B` source cells and

\[
G>X^{1/2-\eta_0}.
\]

Consequently the `1/B` and `1/G` terms close at fixed-power strength. The only surviving coefficient-blind obstruction is the small-shared-gcd strip

\[
\boxed{
H\lesssim
L^{C_E+K_*}
\max\left(\frac{G^2}{X},\frac GA\right)
},
\qquad K_*=6+2\eta+C_{\rm route}.
\]

Equivalently, up to fixed logarithmic cushions,

\[
\kappa\le\max\{0,2\theta-1,\theta-\alpha\}+o(1).
\]

This is `CASE B — H-CRITICAL CORE REMAINS`.

**Promotion firewall:** spacing, weighted large sieve, `S1/S2`, the `A,B` fixed-margin source pin, and the global Case-B bound are currently `RESEARCH PASS CANDIDATE / ARISTOTLE PROMOTION AUDIT PENDING`. Do not yet label the analytic child publication-banked.

### Retained structure in the critical child

- `mu(m)` remains unspent;
- `t mod dm` remains primitive;
- reciprocal-`b` source remains;
- friable `a` remains;
- exact signed `lambda_H(d)/d^2` projector remains.

Therefore this is **not** a fixed-Chowla obstruction at present.

### Short-lift correction

The earlier analytic promotion `DET1-SHORTLIFT-EULER-COLLAPSE45` is **retracted by later hostile audit**. The exact profile/Euler algebra survives, but `SHORTLIFT-EULER-UNIFORM-SAVING45` remains open/repair: the repaired contour bound does not close physical polynomial lift cells. Historical provenance is preserved in the proof index.

### Next attack

First exploit the exact projector before generic dual dispersion:

\[
\lambda_H(d)=\sum_{e\mid d}\mu(d/e)\Omega_H(e),\qquad d=ek,
\]

then test

\[
n=km.
\]

Since `dm=en`, the modulus becomes independent of `k`; on contributing coprime squarefree terms `mu(n)=mu(k)mu(m)`. The next constructive run should test whether the signed `k`-sum collapses to an exact Möbius pair-projector on `(n_1,n_2)`, yielding a rigid gcd normal form and possible diagonal annihilation in the genuinely small-`H` region. Only if an off-diagonal core survives should it open the reciprocal-`b` source and test fused determinant/CRT dispersion.

Detailed research snapshot: `ERDOS287_PRIMITIVEFRACTION_CASEB_2026-08-30.md`.

---

## Mandatory update rule

Whenever either programme changes frontier, update this file and append the corresponding proof index with status, parent/children, deriving run, hostile-audit status, Lean provenance if banked, supersessions/retractions, key equations, current/required bounds, missing mechanism, and next attack. Never delete historical provenance.