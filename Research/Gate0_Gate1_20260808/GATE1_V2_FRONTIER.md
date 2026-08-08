# Gate 1 — V2 Analytic Frontier and Repair Ledger

> **Verdict: OPEN GENERIC SOURCE ESTIMATE.** Many finite/degenerate/resonant sectors are closed or repaired; the generic globally coupled source estimate remains open.

## 1. V2 parameters and target

At

\[
V_2=(5/18,25/72),
\]

use

\[
M=X^{24/72},\quad R=X^{20/72},\quad L=X^{25/72},
\]

\[
H=X^{22/72},\quad D=X^{28/72},\quad K=X^{4/72}.
\]

Exact identities:

\[
DH=L^2,\qquad RK=M,\qquad MK=D.
\]

Target:

\[
\boxed{\mathcal T=ML^4/H=MDL^2=X^{102/72}.}
\]

Original generic trivial/source scale:

\[
M^2D^2=X^{104/72}.
\]

Therefore the **true intrinsic V2 deficit** is

\[
\boxed{X^{2/72}=X^{1/36}.}
\]

This line supersedes any statement saying that V2 intrinsically requires `X^(1/3)` saving.

---

# 2. Banked / repaired finite algebra

## AFF

\[
\boxed{m'\alpha-m\beta=2k.}
\]

Status:

```text
PROVED AT MATHEMATICAL LEVEL
```

## ROOT-COLLAPSE

With the CRT root `T_{pq}(e)`, the banked exact phase identity is the root-collapse identity linking the graph phase to

\[
e_{pq}(hT_{pq}(e)).
\]

Status:

```text
PROVED AT MATHEMATICAL LEVEL
```

## DCRT

The `pm'` reciprocal kernel admits a CRT split into its `p` and `m'` components under the generic coprimality hypotheses.

Status:

```text
PROVED AT MATHEMATICAL LEVEL
```

## Large-prime local branching

For the affine values on the current ranges, a nonzero value cannot have three distinct retained primes in the `L` box. Thus the local retained-prime branching is at most two.

Status:

```text
PROVED AT MATHEMATICAL LEVEL
```

---

# 3. Row-frequency injectivity — corrected proof

A previous prose repair contained an invalid modular term-dropping step. Do **not** bank that proof verbatim.

For fixed `p,m'`, suppose two rows have the same frequency:

\[
k_1\overline{m_1}\equiv k_2\overline{m_2}\pmod{pm'}.
\]

Cross multiplication gives

\[
pm'\mid k_1m_2-k_2m_1.
\]

On V2 ranges,

\[
|k_1m_2-k_2m_1|\ll KM=D=X^{28/72}
\]

whereas

\[
pm'\asymp LM=X^{49/72}.
\]

Hence, for large `X`, the congruence forces the integer equality

\[
k_1m_2=k_2m_1.
\]

Under the generic coprimality conditions `(k_i,m_i)=1`, this forces

\[
m_1=m_2,\qquad k_1=k_2,
\]

and then from

\[
m'=m_i+k_ir_i
\]

with `k_i != 0`,

\[
r_1=r_2.
\]

Status:

```text
LEMMA REPAIRABLE / SHOULD BE LEAN-BANKED BY SIZE + gcd ARGUMENT
```

---

# 4. Input-frequency injectivity

For fixed `p,m'`, define the input frequency by the residue corresponding to

\[
-2h\overline q\pmod{pm'}.
\]

Equality of two input frequencies yields a divisibility condition for

\[
h_1q_2-h_2q_1
\]

modulo `pm'/gcd(2,m')`. The V2 gap

\[
HL=X^{47/72}<LM=X^{49/72}
\]

provides the required size forcing for sufficiently small fixed epsilon. With `0<|h|<q` and prime `q`, equality forces equality of the `(h,q)` pair.

Status:

```text
REPAIRED — PARITY/gcd(2,m') MUST BE TRACKED
```

---

# 5. Fixed-(p,m') Fourier contraction

For fixed `p,m'`, the phase factorizes as

\[
e_{pm'}(s_{r,k}n_{h,q}),
\]

with injective row and input frequencies. Restricted Parseval gives

\[
\boxed{
\sum_{(r,k)\in\mathcal E(m')}
\omega_{m',r,k}|V_{p,m'}(r,k)|^2
\ll
\frac{ML^2}{H}X^{o(1)}.
}
\]

Status:

```text
PROVED AT MATHEMATICAL LEVEL; FINITE FOURIER CORE SHOULD BE LEAN-BANKED
```

Important interpretation: this is a **sector tool**, not a global norm replacement.

---

# 6. Closed / substantially closed sectors at V2

## p-diagonal

Summing the fixed-block estimate over `m'` and `p` gives

\[
\frac{M^2L^3}{H}
=
\mathcal T\frac ML
=
\mathcal T X^{-1/72}.
\]

Status:

```text
CLOSED WITH X^(-1/72) MARGIN
```

## p-resonance

For

\[
p\ne p',\qquad p\equiv p'\pmod{m'},
\]

interval counting gives approximately `L^2/M` resonant pairs per `m'`. Combining with the fixed-block estimate closes this family at the target scale.

Status:

```text
CLOSED AT TARGET SCALE; BOUNDARY-TIGHT
```

## determinant zero / single-zero sectors

Earlier root-difference analysis closes the double-zero and single-zero determinant sectors with power savings.

Status:

```text
CLOSED IN CURRENT ROOT FRAMEWORK
```

## exact swap exceptional frequency

The exact equality frequency family reduces to the diagonal or prime-swap family and is power-saved by direct source counting.

Status:

```text
CLOSED
```

## same-p / same-q / repeated-prime / gcd strata

These are treated as lower-dimensional/collision strata in the current ledger and are not the generic analytic frontier.

Status:

```text
CLOSED OR ROUTED AS EXCEPTIONS, SUBJECT TO FINAL SOURCE TALLY
```

---

# 7. True source frontier versus route-induced losses

## True source target

The generic source problem requires only

\[
\boxed{X^{1/36}}
\]

saving at V2 over the original trivial/source scale.

## Pairwise Fourier + Cauchy route

If the fixed-block estimate is applied independently to every cross pair `(p,p')`, then summing over `m' p p'` gives

\[
\frac{M^2L^4}{H}
=
M\mathcal T.
\]

Therefore that **particular route** needs

\[
X^{1/3}
\]

additional saving.

Status:

```text
OVER-LOSSY ROUTE — DO NOT REDEFINE THIS AS THE INTRINSIC V2 BARRIER
```

---

# 8. MIX2 identity and correction

Let the full-c character decomposition have edge factor `C_c(chi)` and directional factor `D_c(chi)`.

Writing these as multiplicative Fourier transforms of functions `f_c` and `g_c` on the unit group gives the exact identity

\[
\boxed{
\sum_{\chi\bmod c}|C_c(\chi)|^2|D_c(\chi)|^2
=
\varphi(c)\,\|f_c*_\times g_c\|_2^2.
}
\]

Equivalently, expanding character orthogonality gives the multiplicative collision congruence

\[
\boxed{z_1A_1\equiv z_2A_2\pmod c.}
\]

Status:

```text
EXACT ALGEBRA / USEFUL COLLISION CENSUS
```

However, the previously proposed per-block MIX2 estimate does **not** by itself imply the global Gate-1 target after summing all modulus blocks and applying Cauchy. It loses too much global sign/modulus interaction.

Status:

```text
MIX2 AS GLOBAL CLOSURE: RETRACTED
```

Do not spend a major analytic run proving MIX2 alone unless it is used inside a source-preserving signed reassembly.

---

# 9. Full-c character ingredients

The current research archive records:

\[
\sum_{\chi\bmod c}|C_{m,\chi}|^2
\ll
\varphi(c)M X^{o(1)},
\]

coming from full-c edge injectivity, and a directional contraction of the form

\[
|D_{q_1,q_2,m,\chi}|
\ll
\frac{L^2\sqrt M}{H}X^{o(1)}.
\]

These are genuine local pieces of cancellation.

The historic obstruction is **global reassembly**: taking absolute values / blockwise Cauchy destroys the local gain.

Current research target:

```text
PRESERVE CHARACTER / MODULUS / RANK-ONE SIGNS THROUGH REASSEMBLY
```

rather than replacing them with arbitrary operator norms.

---

# 10. Pascadi / Kloosterman dictionary — corrected status

The exact Fourier-Kloosterman identity

\[
e_c(A\bar z)
=
\frac1c\sum_{u\bmod c}S(u,A;c)e_c(-uz)
\]

is valid and supplies a formal bridge to bilinear Kloosterman sums.

However, direct Fourier expansion generally spreads the edge sequence across the full modulus. A useful application of a scalar interval-supported bilinear Kloosterman theorem therefore requires a **source-specific support/norm dictionary**.

The formal exponent calculation showing that hypothetical slots of lengths roughly `(L^2,M)` would have enough V2 margin is only conditional. The actually verified source dispersion variables need not have those short independent interval supports.

Status:

```text
LITERATURE INTERFACE CANDIDATE
NOT A BANKED THEOREM MATCH
```

Do not claim Gate 1 from Pascadi/Bettin-Chandee/Wright until the exact coefficient slots, intervals, norms, and modulus dependence are proved from source.

---

# 11. Current generic analytic target

Preserve the exact source rank-one structure and prove

\[
\boxed{
\sup_{|b_p|,|d_q|\le1}
\sum_e\omega_e
\left|
\sum_{p,q}b_pd_qA_{e,p,q}
\right|^2
\ll
\frac{ML^4}{H}X^{o(1)}.
}
\]

At V2 only `X^(1/36)` saving is required over the original generic trivial/source scale.

The desired proof must not:

- enlarge to an arbitrary `(p,q)` matrix;
- take pairwise `p,p'` Cauchy and then call the resulting `X^(1/3)` loss intrinsic;
- discard source row-weight structure without proof;
- invoke a scalar Kloosterman theorem without an exact coefficient/support dictionary;
- reuse one average twice.

---

# 12. Current honest Gate-1 verdict

```text
AFF / ROOT / DCRT:                         BANKED MATHEMATICAL ALGEBRA
ROW FREQUENCY:                             REPAIRED; LEANIFY CORRECT PROOF
INPUT FREQUENCY:                           REPAIRED
FIXED-BLOCK FOURIER:                       PROVED MATHEMATICALLY
P-DIAGONAL:                                CLOSED X^(-1/72)
P-RESONANCE:                               CLOSED AT TARGET SCALE
DETERMINANT / COLLISION DEGENERACIES:       SUBSTANTIALLY CLOSED
MIX2 IDENTITY:                             PROVED ALGEBRA
MIX2 GLOBAL CLOSURE:                       RETRACTED
DIRECT SHORT-SUPPORT PASCADI MATCH:         NOT CERTIFIED
GENERIC GLOBALLY COUPLED SOURCE ESTIMATE:   OPEN
TRUE V2 REQUIRED SAVING:                   X^(1/36)
```

Therefore:

```text
GATE 1 V2: OPEN GENERIC ANALYTIC FRONTIER
```

No Type-II or twin-prime conclusion follows from this checkpoint.