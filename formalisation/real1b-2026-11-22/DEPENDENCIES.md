# What the replay proves and what remains

The 23 November update adds the [Gold 4.60 joint signed FM dependency ledger](FM-CLOSING.md).

For H2-B, the larger member is $n$. The source assigns weight $\log(n-2)$ exactly when $X<n\le 2X$ and $n-2$ is prime. The twin mass $T$ uses the additional condition that $n$ is prime. Throughout, $N_0=\mathfrak S_2 X/\log X$. The Euler product in the code starts at $p=k+3$ and supplies a unit factor for composite $p$.

## Five inputs to the H2-B endpoint

Read the signature of [infinite_of_paper_inputs](../../RequestProject/REAL1B_20261122/SieveInputs.lean). The table covers all its theorem parameters. “Paper input” means the papers give or import supporting arguments and Lean still needs a proof of the displayed proposition. All little-o bounds in this route quantify over each fixed positive tolerance before taking sufficiently large real scales.

| Parameter | Precise obligation | Source and remaining work |
|---|---|---|
| `h₁ : H1PaperInput` | For each fixed $e>0$, produce centered sieve rows whose singleton bounds hold eventually and whose genuine squarefree source mean is at least $(c_B-e)N_0$. The center and finitely supported signed coefficients enter the divisor sum; the marker range is $X^{1/7}<p\le(2X)^{1/4}$. | Paper input. Gold 4.37-B §§3–4 and Gold 4.50-B §§7, 10. Construct and estimate the actual lower and frozen upper sieve rows, including their distribution estimates. Lean proves the resulting pointwise minorant and its transfer to $A_R$. The row family supplied as a witness may depend on the fixed tolerance. |
| `h₃ : TripleCap` | Eventually $C_3\le(10I_3/3+e)N_0$ for each $e>0$, on the specified squarefree, three-factor, strictly quarter-rough source. | Paper input. Gold 4.50-B opening contracts and §10. The ordered-simplex integral is formalized and bounded. Its evaluation alone gives no estimate for the population of triples on the shifted-prime source. |
| `hI : TypeICalibration` | $T_1-T_2+\rho_D(3)N_0=o(N_0)$ with the same fixed cutoff and the exact Dirichlet coefficients as the Type-II term. | Paper input. Gold 4.53-B part II §9, (9.1)–(9.2). The centered progression estimate, integration of the principal profile, and error uniformity still require proofs in Lean. |
| `hc : negligible collarMass` | The prime-weighted population with $X<(P^-(n))^4\le n$ in the source interval is $o(N_0)$. | Paper input. Gold 4.53-B (9.7)–(9.8) gives a two-linear-form upper sieve and a reciprocal-prime summation. Lean proves the support and absolute domination of the signed collar. |
| `hII : FinalTypeII` | For every fixed $e>0$, eventually $\mathcal T_{1/4,X}\le(1/8+e)N_0$. | **Open research estimate.** Gold 4.53-B (9.1), (9.9). Use the complete unmarked signed sum in `typeII_expanded`; it retains the shifted Möbius sign, cutoff, both output presieves and the full positive divisor companion. |

If these five propositions are discharged, the endpoint yields exactly `Set.Infinite {p : ℕ | p.Prime ∧ (p+2).Prime}`. The final row is the research frontier identified in the dossier. An unconditional Lean endpoint additionally requires the first four proofs.

## Checked chain and source correspondence

| Checked result | What it connects |
|---|---|
| `rough_iff`, `fourth_root_iff`, `rough_rank`, `parity_masks`, `source_parity`, `h2_identity` | The strict fourth-root cutoff, factor classification and Möbius signs give $2T=A_R-2C_3-M_R$ on the exact finite prime-only source. Lean volume pp. 2–3 and Gold 4.50-B §10 (19)–(20), pp. 191–192. |
| `historical_conversion` | At $x=2X$, undo the old $\log x$ normalization, subtract its proper-prime-power contribution, account for $\log(p+2)-\log p$, and retain both window differences. This is an exact equality for $2X>1$. |
| `vaughan_identity`, `cV_divisors`, `cV_zero_below`, `typeII_expanded` | Split $\Lambda$ by Dirichlet convolution. The output factor $r$ carries $c_V(r)=\sum_{\ell\mid r,\ell>V}\Lambda(\ell)$, which vanishes for $r\le V$. The chosen allowed fixed exponents give $U=V=X^{1/5}$, with $Z=\exp((\log X)^{0.24})$. Gold 4.53-B (9.1), Lean volume p. 23. |
| `native_vaughan`, `gamma_split`, `gamma_approx`, `gamma_of_typeII` | The exact decomposition retains Type I, Type II, the low output coefficient, the difference between the genuine prime weight and presieved $\Lambda$, and the signed cutoff collar. Once the indicated errors are small, the one-sided Type-II bound transfers to $\Gamma_q$. Gold 4.53-B (9.6)–(9.9), pp. 24–25. |
| `lowOutput_zero`, `correction_bound`, `correction_negligible` | The low output coefficient vanishes for $X\ge4$. When $X\ge4$ and $\log X\ge4$, the absolute prime-weight correction is at most $2\sqrt{2X}\log(2X)$. Mathlib's Chebyshev bound, injectivity of $n\mapsto n-2$ on the window, and logarithmic growth give $o(N_0)$. |
| `euler_converges`, `series_pos`, `scale_pos` | The Euler product defining $\mathfrak S_2$ converges to a positive real. Its logarithms are summable by comparison with the inverse-square series. Consequently $N_0(X)>0$ for $X>1$. |
| `triple_integrability`, `triple_integral_upper`, `margin_floor` | Both simplex integrations exist. On $x=4t_1-1$, $y=4t_2-1$, $z=4t_3-1$, the integrand is at most $32-13(xy+yz+xz)$. Integrating this quadratic proves $I_3\le115/768$. Together with $2^{84}<3^{53}$ and Mathlib's upper bound for $\log2$, this gives $c_B-20I_3/3+\rho_D(3)-1/8>1/4000$, with $c_B=(7/2)\log3-4\log2$ and $\rho_D(3)=1-\log3+I_3$. This rational certificate suffices for positivity. |
| `eventual_mass_lower`, `pair_of_mass_pos`, `infinite_of_paper_inputs` | From the unsigned lower bound, triple cap and signed bound, Lean obtains $T(X)>N_0(X)/16000$ eventually. A positive mass supplies a genuine pair at that scale. Unbounded scales imply infinitude. |

## Independent Ford–Maynard route

[FMSource.lean](../../RequestProject/REAL1B_20261122/FMSource.lean) uses $x=2X$, the source $a_n$, comparator $b_n$, and weight $a_n-b_n$. It implements the multiplicity-sensitive small/large divisor split in $H_\epsilon$, the fundamental-vector subsum restriction and coagulation predicate, the marked divisor row $K$ with occurrence weight $m_X(d)/64^3$, and its three prime-label bands and cofactor band. The signed residual uses squarefree off-coagulation inputs of ranks $3$ and $5$ through $255$ and retains the full favorable companion $P_-$. These are finite definitions. The code proves companion nonnegativity and domination of the presieved twin mass by the H2 prime-only mass.

The terminal theorem has three inputs: `Lower` is the inherited signed-comparison lower estimate, `ResidualBound` is the full source-direction upper estimate, and `hS` requires eventual positivity of the concrete $S_b$. The historical and current numerical thresholds stay distinct. The aggregate centered fourth-moment bound in the manuscript has a narrower coefficient class; the replay does not use it to discharge any of these three inputs. Gold 4.53-FM §1, Lean volume p. 47; inherited divisor-kernel and marked-row definitions in Gold 4.48-FM Appendix H.

## Research coverage

The dependency list is exhaustive for the two earlier endpoints displayed on this page. The Chen H2-A minor-arc route, JCORE, Gate 1A, $H_*$, and the remaining historical Type-I/II arguments have distinct scope in the research archive. The package makes no compilation claim for these manuscript chapters. See the [repository research ledger](../../RESEARCH_FRONTIERS/CURRENT_FRONTIERS.md) for the historical branches.

The two supplied volumes are identified by SHA-256 so a reviewer can match the page references.

| File | SHA-256 |
|---|---|
| `REAL1B_Sol_Lean_Formalization_and_Proofs_20261122.pdf` | `fb4fcda1d4807269ae8eda20ab7cc9cae242104f1929a4575b506644e1cd684e` |
| `REAL1B_Sol_Mathematics_Provenance_20261122.pdf` | `89a91edcfdf58edc94e6c2d5bb43d73a273ca609ca5e21584bc58df405765531` |
