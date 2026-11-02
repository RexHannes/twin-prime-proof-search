# Real 1B — Route A & Route B Research Notes (2–3 November 2026)

This directory archives two companion research notes on the Real 1B rough shifted-prime source ($\rho = 8/31$, $z = X^\rho$). Neither note claims a positive terminal twin-prime reserve, G3+/G5 acceptance, or an unconditional proof of the Twin Prime Conjecture.

## Included PDFs

1. **[`Real1B_RouteB_Signed_Rosser_Error_2026-11-03.pdf`](Real1B_RouteB_Signed_Rosser_Error_2026-11-03.pdf)** (9 pages, 3 November 2026 — Route B)
   - **Title:** *Real 1B: a global signed Rosser-error estimate — Complete parity-dependent error control at fixed inner level*
   - **SHA-256:** `74978ea4603bc552ab615fb7f839b04d2c00de5727bf4cc523afd9d795250435`
   - **Summary:**
     - Proves a complete parity-dependent signed-error upper bound at fixed inner level $D = X^\theta$ ($3\rho < \theta < 1$):
       $$\limsup_{X\to\infty} \frac{\mathcal{R}_\theta}{\mathcal{N}_\psi} \le \frac{5}{3}(B_\theta + \kappa_\mu).$$
     - At the unchanged inner level $\theta = 199/200$, reduces the safe signed-error upper debit from $0.21970750\,\mathcal{N}_\psi$ to $0.00479332\,\mathcal{N}_\psi$ (a reduction of $0.21491418\,\mathcal{N}_\psi$), giving $\mathcal{C}_\mu \le \mathcal{S}_{199/200} + (0.00479332 + o(1))\mathcal{N}_\psi$.
     - Retains every recursion depth via the exact guarded first-prime identity $H_D(n;y) = \sum_{p\mid n,\,p\le y} \mathbf{1}_{(p,n/p)=1} H_{D/p}(n/p; p^-)$, pays all support and roughness boundaries, coprimality diagonals, and tiny first-prime tails, and evaluates the integer comparison via uniform weighted coprime Mertens cancellation.
     - Leaves the original-source signed midpoint / surviving Vaughan tail $\mathcal{S}_{199/200}$ open (terminal reserve: $0$).

2. **[`Real1B_RouteA_Stronger_Lower_Sieve_2026-11-02.pdf`](Real1B_RouteA_Stronger_Lower_Sieve_2026-11-02.pdf)** (14 pages, 2 November 2026 — Route A)
   - **Title:** *REAL 1B – GOLD INFINITY / ROUTE A: A certified stronger lower sieve on the original rough shifted-prime source*
   - **SHA-256:** `0f63e4eb9799d09df3bbc185731639e069c6fe4057508983845551a4c56f28a0`
   - **Summary:**
     - Proves a stronger lower bound for the squarefree $X^{8/31}$-rough shifted-prime source $A(X) = \sum_n \psi(n/X)\Lambda(n+2)\mu^2(n)\mathbf{1}_{P^-(n)>X^\rho}$:
       $$\liminf_{X\to\infty} \frac{A(X)}{\mathcal{N}_\psi(X)} \ge a_* := \frac{7}{2}\log 3 - 4\log 2 - 2\log\frac{12}{11} + \frac{61}{500} = 1.020531534119\dots,$$
       improving the baseline lower coefficient $a_0 \approx 0.898531534119$ by the certified rational increment $61/500 = 0.122$ (outward-rounded finite certificate over $91\,577$ active rectangles exceeding $0.1220144061$).
     - Combines a finite adaptive Buchstab decomposition with Pascadi's three-largest-factor distribution function $\Theta(a,b,c)$, Iwaniec's boxed factorable-remainder construction, and a source-preserving switched upper bound with kernel $(10/3)\omega((1-a-b-c)/c)/(abc^2)$.
     - Reduces the conditional composite-discrepancy gap in the matched consumer from $0.276610077055\dots$ to $0.154610077055\dots$, while leaving the $1.1$ target, the zero-discrepancy threshold $c_* = 1.175141611174\dots$, and twin-prime infinitude open.

## Verification & Scope Firewall

| Item | Status |
|---|---|
| Route A adaptive Buchstab + switched upper sieve bound $a_* = a_0 + 61/500$ | **PROVED** (from BFI, Iwaniec factorable remainder, Pascadi Propositions 4.4, 5.2, 5.5, and outward-rounded certificate) |
| Route B parity-dependent error majorant $H_D$ & guarded recursion | **PROVED** |
| Route B global signed Rosser-error bound $\limsup \mathcal{R}_{199/200}/\mathcal{N}_\psi < 0.00479332$ | **PROVED** (from standard upper sieve, Pascadi, Fouvry–Radziwiłł, and weighted coprime Mertens cancellation) |
| Route A target $1.1$ / zero-composite-discrepancy threshold $c_* \approx 1.17514$ | **OPEN / UNMET** |
| Route B signed midpoint / surviving Vaughan tail $\mathcal{S}_{199/200}$ | **OPEN / UNMET** |
| Positive terminal twin-prime reserve / Twin Prime Conjecture | **OPEN** |
