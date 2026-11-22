# Gold 4.60 · Ford–Maynard joint signed complement

On the joint signed branch, a bound for the weighted sum $Q_E$ with any fixed positive saving would imply infinitely many twin primes, subject to the supporting analytic estimates below. The final estimate is open. [Lean source](../../RequestProject/REAL1B_20261122/FMClosing.lean)

## Exact source

The physical output is $n\in(x/2,x]$, with input $k=n-2$. The source weight $\Phi=F-G$ uses the original $H_\epsilon$, marked kernel $K$, good set and retained ranks. The favorable good-set term $G$ is part of every evaluation of $\Phi$. The comparator $S_b$ and twin mass $T$ come from the [existing FM source](../../RequestProject/REAL1B_20261122/FMSource.lean). The only declaration from the H2 namespace used here is the common twin-prime singular series. The closing theorem takes zero H2 analytic hypotheses.

Fix $0<a<1$, $U=V=x^{0.24}$, $D=x^{0.49}$ and $w=\exp((\log x)^a)$. The grouped weight at $k$ is $R_w(k)\mu(k)^2 B_{U,D}(k)\Phi(k+2)$, where $B_{U,D}$ sums $\log\ell\,\mu(m)$ over primes $\ell\mid k$ with $\ell>U$, $m\mid k/\ell$, $m>U$ and $m\ell>D$. This includes each positive cofactor $k/(m\ell)$ with its actual multiplicity.

The joint paper selects squarefree outputs with five ordered prime factors. The first four coordinates $\log p_j/\log n$ lie strictly inside the selected hundredth-grid cells. The predicate `admissible` encodes Part A (2.1), including the fifth-coordinate restrictions. The supplied selection has 1,566 boxes. The input side of $E$ further requires squarefreeness and $P^-(k)>U$. The companion $A(\psi)$ uses the original prime-input weight on all selected **output** boxes. It carries neither of the additional input masks. The three-prime chamber in the separate Gold 4.59 Signed Strip manuscript has its own estimates.

## Dependency ledger

Each tolerance is fixed before the scale tends to infinity. The paper status records the source's written argument. An analytic proposition used as a Lean hypothesis remains to be proved in Lean.

| Status | Lean name | Statement and source |
|---|---|---|
| PAPER_PROVED_NOT_FORMALIZED | `LowerLedger` | $C_\kappa+T\ge(0.999892775499-o(1))S_b$. Gold 4.57 lower ledger transferred to the intrinsic covariance using Gold 4.58 (U6), (U8)–(U9). The fixed roughness companion cancels before this transfer. |
| PAPER_PROVED_NOT_FORMALIZED | `Reduction a` | $\lvert C_\kappa-\mathcal U\rvert=o(S_b)$. Gold 4.58 (U1), (U4)–(U5) and its full native Type-I, short-product, presieve and squarefree-input estimates. The code uses the physical expression in (U1). |
| PAPER_PROVED_NOT_FORMALIZED | `Joint a` | $\mathcal U_E-0.02A(\psi)\le(-0.00048+o(1))S_b$. Gold 4.59 **Joint Signed** Part A (2.1) and research report §§1–4. The written proof uses the coefficient range $2\le\Phi\le6$, the negative rough-input population and the upper cost of the positive triangle exception. The numerical rounding is checked in Lean. |
| PAPER_PROVED_NOT_FORMALIZED | eventual positivity of `Sb` | Gold 4.57 source normalization $S_b\sim\mathfrak S_2 x/(2\log x)$. The endpoint explicitly requires eventual positivity. |
| OPEN_ARITHMETIC | `ComplementBound a κ` | For a fixed $\kappa>0$, $Q_E=\mathcal U_{E^c}+0.02A(\psi)\le(1.000372775499-\kappa+o(1))S_b$. Gold 4.59 Joint Signed §4 gives this Gold 4.60 target. |
| LEAN_PROVED | `source_split`, `signed_identity` | At each scale $\mathcal U=\mathcal U_E+\mathcal U_{E^c}$ and $\mathcal U-Q_E=\mathcal U_E-0.02A(\psi)$. |
| LEAN_PROVED | `one_large_switch`, `coeff_prime`, `coeff_semiprime` | The grouped coefficient selects the unique large prime when there is one. For $U\ge1$ it vanishes on prime inputs. For $k=pq$ with distinct primes $p,q>U$ and $pq>D$, it equals $-\log k$. |
| LEAN_PROVED | `first_index_lower`, `margin_certificate` | The box inequalities imply $i_1\ge4$. The paper's exact rational margin exceeds $0.00048$, and $0.999892775499+0.00048=1.000372775499$. |
| LEAN_PROVED | `complement_pair_balance`, `complement_bound_iff_pair_budget` | The open bound is equivalent to the signed budget below. The support and weights are shared on the two sides. |
| LEAN_PROVED | `eventual_reserve`, `infinite_of_joint_complement` | For each $e>0$, eventually $T\ge(\kappa-e)S_b$. Taking $e=\kappa/2$ and using eventual $S_b>0$ produces twin primes on unbounded scales. |

## A source-specific form of the open estimate

Within the literal complement, take the semiprime inputs $k=pq$ of the coefficient theorem above. Write $M_-$ and $M_+$ for the masses of $\max(-\Phi,0)$ and $\max(\Phi,0)$ on precisely these inputs, weighted by $R_w(k)\mu(k)^2\log k$. Lean proves both masses nonnegative. Let $R$ sum the original signed weight over every other input in the complement. Lean checks the finite equality

$$Q_E=R+M_- -M_+ +0.02A(\psi).$$

Consequently the remaining estimate is equivalent to

$$R+M_-+0.02A(\psi)\le (1.000372775499-\kappa+o(1))S_b+M_+.$$

This exposes the sign that a source estimate must deliver. A negative output weight at a semiprime contributes to the cost $M_-$. The algebra supplies no estimate for the relative sizes of the two masses.

## Source editions

- *REAL1B Gold 4.57FM Research Note*, 22 November 2026, source contract and complete accounting.
- *REAL1B Gold 4.58 FM Complete Proofs*, 23 November 2026, exact owner normalization and unified accepted theorem.
- *REAL1B Gold 4.59 FM Joint Signed Proofs*, 23 November 2026, Part A §2 (2.1), and *REAL1B Gold 4.59 FM Joint Signed Report*, §§1–5. The matching project verifier names its selector `positive_boxes()`.
