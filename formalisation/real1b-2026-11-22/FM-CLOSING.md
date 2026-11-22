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

The Gold 4.59 paper supplies a more detailed version of the Joint input. At its fixed sieve levels Part A §7.1, the rough-population coefficient is $68853556/62497500025$. Its triangle cost is $153125/248769792$. Lean proves their exact difference in `fixed_level_certificate` and proves `joint59_of_source_estimates` from `RoughSupply59`, `TriangleCost`, `CoefficientAssembly` and eventual comparator positivity. These population and assembly estimates still require Lean proofs. The 4.59 and 4.60 derivations use the identical prime companion and triangle charge.

## Stronger local estimate in Gold 4.60

The *Gold 4.60 Joint Closure Evolutionary Proof Report*, §§A–E (23 November 2026), applies a box-dependent distribution level to the same output boxes, input mask, and companion. It reports a local margin of $0.00207$. The earlier $0.00048$ result remains independently callable as `infinite_of_joint_complement`.

| Status | Lean name | Precise role |
|---|---|---|
| LEAN_PROVED | `boxes_prime_size`, `boxes_sifted`, `prime_companion_eq_raw` | Every prime dividing a selected output has $\log p>0.04\log n$. Eventually the original output presieve is automatic on the boxes. Its prime companion equals the paper's raw log-weighted prime-input sum. |
| LEAN_PROVED | `selected_without_presieve` | For fixed $a<1$, eventually $w<U$. The selected source then equals the stated squarefree, $U$-rough sum with the redundant subpower presieve removed. |
| PAPER_PROVED_NOT_FORMALIZED | `RoughSupply` | For each fixed $e>0$, eventually $0.02\log x\,N_\psi\ge(0.0026942415488-e)S_b$. Report §§B–C transfer fixed-box distribution and a lower sieve to the shifted rough inputs. This is the main analytic input specific to the stronger variant. |
| PAPER_PROVED_NOT_FORMALIZED | `TriangleCost` | For each $e>0$, eventually $0.49\log x\,M_\psi\le(153125/248769792+e)S_b$. Section D inherits the positive rank-four triangle exception, with all three short pairs and the full output weight. |
| PAPER_PROVED_NOT_FORMALIZED | `CoefficientAssembly a` | Section D combines the coefficient bound, prime-input log correction and bounded errors. It bounds $\mathcal U_E-0.02 A_\psi$ by the triangle cost minus the rough population term, up to $o(S_b)$. |
| LEAN_PROVED | `cubic_log_lower`, `boxwise_rounding` | For $0<z<1$, $2(z+z^3/3)<\log((1+z)/(1-z))$. The proved inequality justifies the downward logarithm approximation. The stated lower coefficient minus the exact triangle cost exceeds $0.00207$. |
| LEAN_PROVED | `joint60_of_source_estimates`, `gold60_lower` | From the three named analytic estimates and eventual comparator positivity, the joint margin follows. The lower ledger and reduction then imply $Q_E+T\ge(1.001962775499-o(1))S_b$. |
| OPEN_ARITHMETIC | `Complement60 a κ` | Independently bound the same $Q_E$ by $(1.001962775499-\kappa+o(1))S_b$ for a fixed $\kappa>0$. |
| LEAN_PROVED | `reserve60`, `infinite_of_boxwise_complement` | The independent upper bound and the listed supporting estimates imply $T\ge(\kappa-o(1))S_b$ and twin-prime infinitude. |

Both verification commands run a separate exact-rational check of the finite sum over admissible boxes, including the boxwise level selection, the cubic lower bound and the full triangle charge. This calculation certifies the numerical coefficient. The assertions about the distribution of actual primes are Lean theorem parameters. [Rational checker](boxwise.py)

The paper's distribution inputs are Fouvry Theorem 1′ for the boxes admitting a short prime and Liu–Park–Song Theorem 3.2 for the fallback level. Their transfer to these shifted, normalized boxes is part of the manuscript's analytic obligation. [Fouvry](https://people.math.ethz.ch/~kowalski/fouvry-bombieri-vinogradov.pdf) · [Liu–Park–Song](https://link.springer.com/article/10.1007/s40993-017-0089-3)

## A source-specific form of the open estimate

Within the literal complement, take the semiprime inputs $k=pq$ of the coefficient theorem above. Write $M_-$ and $M_+$ for the masses of $\max(-\Phi,0)$ and $\max(\Phi,0)$ on precisely these inputs, weighted by $R_w(k)\mu(k)^2\log k$. Lean proves both masses nonnegative. Let $R$ sum the original signed weight over every other input in the complement. Lean checks the finite equality

$$Q_E=R+M_- -M_+ +0.02A(\psi).$$

Consequently the remaining estimate is equivalent to

$$R+M_-+0.02A(\psi)\le (1.000372775499-\kappa+o(1))S_b+M_+.$$

This exposes the sign that a source estimate must deliver. A negative output weight at a semiprime contributes to the cost $M_-$. The algebra supplies no estimate for the relative sizes of the two masses.

## Source editions

- *REAL1B Gold 4.57FM Research Note*, 22 November 2026, source contract and complete accounting.
- *REAL1B Gold 4.58 FM Complete Proofs*, 23 November 2026, exact owner normalization and unified accepted theorem.
- *REAL1B Gold 4.59 FM Joint Signed Proofs*, 23 November 2026, Part A §2 (2.1), and *REAL1B Gold 4.59 FM Joint Signed Report*, §§1–5. The [original project verifier](REAL1B_Gold4_59_FM_Joint_Signed_Verify_20261123.py) names its selector `positive_boxes()`. Its complete finite output reproduces the original registry, including the ordered-box digest and 7,272 kernel profiles. The complete proof, report and verifier matched the file hashes in the original registry. The SHA-256 of the complete proof is `828f8ce69549375b28f575ddcb964ffa0369ca28d7794fe3a62f1cdd95c55717`.
- *REAL1B Gold 4.60 Joint Closure Evolutionary Proof Report*, 23 November 2026, §§A–H. Source SHA-256 `1aa1b0700073aee6a76807db55112f3e9966855603d39f2d624f5d4c5c5fc1c6`. The 4.59 Joint Signed Report has SHA-256 `09874661e9faab3da3a123fefef3de1712e7c512cf0fe3e49229491172701579`.
