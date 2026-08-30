# Erdős #287 — Primitive-Fraction Case-B Narrowing

Date: 2026-08-30

Status firewall: **ERDOS287 OPEN**. This file records the latest research derivation. The analytic promotions below are `RESEARCH PASS CANDIDATE / PROMOTION AUDIT PENDING` until the dedicated Aristotle/source audit verifies the literal projector and source-range hypotheses. Nothing here is a claim that Erdős #287 is proved.

---

## 1. Previous first residual

The run began from

`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-MOBIUS-GRAM45`

with exact one-level shared-gcd operator

\[
\mathcal Q_H
=
\sum_d \frac{\lambda_H(d)}{d^2}
\sum_{a\asymp A}\rho(a)
\left|
\sum_{m\asymp G/d,(m,d)=1}
\frac{\mu(m)}m
\sum_{t\bmod dm}^{*}\widetilde G_{dm}(t)e_{dm}(ta)
\right|^2.
\]

The old `r=1` pole/defect route was deliberately not resumed.

---

## 2. Primitive-fraction spacing

For fixed `d`, put `M=G/d`. The primitive frequencies are

\[
\frac{t}{dm},\qquad M\le m<2M,\quad (m,d)=1,\quad (t,dm)=1.
\]

Each fraction is reduced. For two distinct frequencies,

\[
\Delta_d
\ge \frac{1}{d m_1m_2}
\ge \frac{1}{4dM^2}
=
\frac{d}{4G^2}.
\]

Hence the candidate fixed-`d` separated additive large sieve is

\[
\sum_{a\in I_A}
\left|
\sum_{m,t}c_{m,t}e\!\left(\frac{at}{dm}\right)
\right|^2
\ll
\left(A+\frac{G^2}{d}\right)
\sum_{m,t}|c_{m,t}|^2.
\]

Candidate node:

`DET1-ONELEVEL-PRIMITIVEFRACTION-SPACING45`.

---

## 3. Source weight

The run reports

\[
\rho(a)=\mathbf 1_{P^+(a)\le Y_\rho}|V(a/A)|,
\]

with fixed smooth dyadic `V`, so

\[
0\le \rho(a)\ll1,
\qquad
\sum_a\rho(a)\ll A,
\qquad
\sum_a\rho(a)^2\ll A.
\]

Thus the weighted large-sieve reduction costs `L^0`; no friability theorem is needed for this upper bound.

---

## 4. Projector harmonic norms

The run uses the exact convolution

\[
\lambda_H=\mu*\Omega_H,
\qquad
\lambda_H(d)=\sum_{e\mid d}\mu(d/e)\Omega_H(e),
\]

with `Omega_H` supported on `e \asymp H` and claims the source normalisation

\[
|\Omega_H(e)|\ll1,
\qquad
\sum_e\frac{|\Omega_H(e)|}{e}\ll1,
\qquad
\sum_e\frac{|\Omega_H(e)|}{e^2}\ll\frac1H.
\]

Conditional on that literal source normalisation,

\[
S_1:=\sum_{d\le CG}\frac{|\lambda_H(d)|}{d}
\ll \log\!\left(\frac{2G}{H}\right)\ll L,
\]

and

\[
S_2:=\sum_{d\le CG}\frac{|\lambda_H(d)|}{d^2}
\ll \frac1H.
\]

**Promotion pin:** the dedicated Aristotle audit must verify the exact `Omega_H` definition and harmonic norms before formal banking.

---

## 5. Coefficient energy

From the banked reciprocal-level energy shape

\[
E_g:=\sum_{t\bmod g}^{*}|\widetilde G_g(t)|^2
\ll (gB+B^2)L^{C_E},
\]

and `dm \asymp G`, the run derives

\[
\sum_{m\asymp G/d}\frac{E_{dm}}{m^2}
\ll
 dB\left(1+\frac BG\right)L^{C_E}.
\]

No extra logarithm arises from the dyadic `m`-sum.

---

## 6. Global coefficient-blind bound

For fixed `d`,

\[
\mathfrak G_{H,d}
\ll
(Ad+G^2)
B\left(1+\frac BG\right)L^{C_E}.
\]

After the exact projector sum, the sharp candidate global estimate is

\[
|\mathcal Q_H|
\ll
B\left(1+\frac BG\right)L^{C_E}
\left[
A\log\!\left(\frac{2G}{H}\right)
+
\frac{G^2}{H}
\right].
\]

A common-log envelope is

\[
|\mathcal Q_H|
\ll
B\left(1+\frac BG\right)
\left(A+\frac{G^2}{H}\right)L^{C_E+1}.
\]

With `AB \asymp X`, the sharp normalised ratio is

\[
\frac{|\mathcal Q_H|}{AB^2}
\ll
L^{C_E+1}\left(\frac1B+\frac1G\right)
+
L^{C_E}
\left(
\frac{G^2}{HX}
+
\frac{G}{HA}
\right).
\]

---

## 7. Case-B classification

The run reports that on the surviving fixed-margin source cells

\[
A\ge X^{\eta_A},\qquad B\ge X^{\eta_B}
\]

for fixed positive source margins, and

\[
G>X^{1/2-\eta_0}.
\]

Therefore the `1/B` and `1/G` terms are fixed-power small and beat every required fixed logarithmic power.

The remaining two terms fail uniformly unless

\[
H\gg \frac{G^2}{X}L^{C_E+K_*},
\qquad
H\gg \frac GA L^{C_E+K_*},
\]

where

\[
K_*:=6+2\eta+C_{\rm route}.
\]

Hence the surviving union is

\[
\boxed{
H\lesssim
L^{C_E+K_*}
\max\!\left(\frac{G^2}{X},\frac GA\right)
}
\]

with an individual branch omitted whenever its right-hand side is below `1`.

Exponentially,

\[
\boxed{
\kappa
\le
\max\{0,2\theta-1,\theta-\alpha\}+o(1)
}.
\]

Classification:

`CASE B — H-CRITICAL CORE REMAINS`.

---

## 8. New first exact residual

Research child:

`287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45`.

It retains the source-specific structure

- `mu(m)`;
- primitive `t mod dm`;
- reciprocal-`b` source;
- friable `a`;
- exact signed `lambda_H(d)/d^2` projector.

It is **not** a fixed-Chowla problem at this stage.

---

## 9. Preferred next constructive exploit

Do not return to the old pole/defect route. Before generic dual large-sieve technology, expand the exact projector:

\[
\lambda_H(d)=\sum_{e\mid d}\mu(d/e)\Omega_H(e),
\qquad d=ek.
\]

Then test the fusion

\[
n=km.
\]

Because `dm=ekm=en`, the modulus becomes independent of `k`. On contributing squarefree terms, `(m,ek)=1` implies `(m,k)=1`, so

\[
\mu(n)=\mu(k)\mu(m).
\]

The next Pro should determine whether this converts the outer signed `k`-sum into an exact Möbius pair-projector on `(n_1,n_2)`, potentially forcing a rigid gcd normal form and annihilating the ordinary diagonal in the genuinely small-`H` region.

Preferred next targets:

- `DET1-SHAREDGCD-PROJECTOR-UNFOLD45`;
- `DET1-SHAREDGCD-KM-FUSION45`;
- `DET1-SHAREDGCD-MOBIUS-PAIRPROJECTOR45`;
- `DET1-SHAREDGCD-FUSED-DIAGONAL-ANNIHILATION45`.

Only if an off-diagonal core survives should the run then open `Gtilde` in reciprocal `b` and test fused determinant / CRT dispersion.

---

## 10. Short-lift correction firewall

A previous research index entry promoted `DET1-SHORTLIFT-EULER-COLLAPSE45`. The later hostile audit invalidated that analytic promotion: the proposed uniform contour bound does not close physical polynomial lift cells. The exact profile algebra remains useful, but `SHORTLIFT-EULER-UNIFORM-SAVING45` is open/repair rather than banked analytic PASS.

This retraction must be preserved append-only in the proof index.

---

## 11. Current status

- `ERDOS287`: **OPEN**.
- Generic coefficient-blind primitive-fraction lane: **research PASS candidate, promotion audit pending**.
- `1/B`, `1/G`: **research-closed on the claimed fixed-margin source cells; source pin to be checked by Aristotle**.
- First main-line residual: `287-K0-SP2-DET1-SHAREDGCD-ONELEVEL-PRIMITIVEFRACTION-CRITICAL45`.
- Remaining mechanism: exploit the exact signed projector inside the small-`H` strip rather than spending Möbius cancellation globally.
