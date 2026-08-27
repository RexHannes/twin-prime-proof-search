# GOLD CLOSE 1B — `PURE5-DP-FULLYCROSSED-ENTROPYGAP45`

```text
CONTROLLING VERDICT:

FULLCROSS-ENTROPYGAP-REDUCED-TO
PURE5-DP-DOUBLEGCD-BEZOUT-LINE45
```

做咗。附件揀 entropy-gap fully-crossed core作下一槍係正確：在 H\<P\<UH\<P\<U 中，common-pp及 common-dd兩翼消失，剩低

d2p2−d1p1=uh,v2−v1=ℓh,d\_2p\_2-d\_1p\_1=uh, \qquad v\_2-v\_1=\ell h,

而目標係 QV(log⁡X)−AQV(\log X)^{-A}。

今輪的 decisive result係：

FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45\:PASS,FULLCROSS-DOUBLEGCD-BEZOUT45\:PASS,DP-FACTOR-INJECTIVE-BEZOUTLINE45\:PASS,DOUBLEGCD-LARGE-GS-TAIL45\:PASS,PURE5-DP-FULLYCROSSED-ENTROPYGAP45\:REDUCED, NOT CLOSED.\boxed{ \begin{aligned} &\texttt{FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45}:&&\mathbf{PASS},\\\ &\texttt{FULLCROSS-DOUBLEGCD-BEZOUT45}:&&\mathbf{PASS},\\\ &\texttt{DP-FACTOR-INJECTIVE-BEZOUTLINE45}:&&\mathbf{PASS},\\\ &\texttt{DOUBLEGCD-LARGE-GS-TAIL45}:&&\mathbf{PASS},\\\ &\texttt{PURE5-DP-FULLYCROSSED-ENTROPYGAP45}:&&\mathbf{REDUCED,\ NOT\ CLOSED}. \end{aligned}}

真正修正係：

「每個 p2只有 O(1) choices」是真的， 但只把 source變成 bounded-degree matching； 它本身沒有提供任何 log cancellation。\boxed{ \text{「每個 }p\_2\text{只有 }O(1)\text{ choices」是真的， 但只把 source變成 bounded-degree matching； 它本身沒有提供任何 log cancellation。} }

而 source-exact first residual進一步縮成：

PURE5-DP-DOUBLEGCD-BEZOUT-LINE45.\boxed{\texttt{PURE5-DP-DOUBLEGCD-BEZOUT-LINE45}.}

---

## A. Entropy-gap scale ledger

沿用

X=Y9,Q=Yϑ,132≤ϑ<8,X=Y^9,\qquad Q=Y^\vartheta,\qquad \frac{13}{2}\le\vartheta<8, U=Y4,V=Y5,R=XQ,H=QU=VR.U=Y^4,\qquad V=Y^5,\qquad R=\frac XQ,\qquad H=\frac QU=\frac VR.

對一個 dyadic cell：

DP≍Q.DP\asymp Q.

因此

D≍QP=UHP.D\asymp\frac QP=\frac{UH}{P}.

在 entropy gap

H\<P\<UH\<P\<U

中：

DH≍UP>1,UD≍PH>1.\frac DH\asymp\frac UP>1, \qquad \frac UD\asymp\frac PH>1.

所以 exact dyadic scale consequence係

H\<D\<U.(1)\boxed{H\<D\<U.} \tag{1}

故：

DP-ENTROPYGAP-BOTH-FACTORS-MID45: PASS.\boxed{\texttt{DP-ENTROPYGAP-BOTH-FACTORS-MID45:\ PASS}.}

即 distinguished prime pp與 Möbius cofactor dd都：

- 長過 determinant-line length HH；
- 短過 model scale UU。

附件提出的這個 symmetry完全正確。

技術上應將 HH定義成 actual hh-support cutoff，而唔只係 Q/UQ/U 的 ≍\asymp-notation。若原 cutoff係 ChQ/UC\_hQ/U，則把 P≍HP\asymp H的一個 fixed-factor boundary cell附加到 low-PP wing；它不影響下面的 fixed-power inequalities。

---

## B. Cross-prime coprimality

Fully-crossed source有

d2p2−d1p1=uh,0<∣h∣≤H\<P,(2)d\_2p\_2-d\_1p\_1=uh, \qquad 0<|h|\le H\<P, \tag{2}

及 clean condition

(pi,u)=1.(p\_i,u)=1.

若 p1∣d2p\_1\mid d\_2，則模 p1p\_1：

uh≡d2p2−d1p1≡0(modp1).uh\equiv d\_2p\_2-d\_1p\_1\equiv0\pmod{p\_1}.

由 (p1,u)=1(p\_1,u)=1得 p1∣hp\_1\mid h，但

0<∣h∣\<p1,0<|h|\<p\_1,

矛盾。因此

p1∤d2.p\_1\nmid d\_2.

對稱地：

p2∤d1.p\_2\nmid d\_1.

而若 p1=p2=pp\_1=p\_2=p，則同樣由

p(d2−d1)=uhp(d\_2-d\_1)=uh

推出 p∣hp\mid h，矛盾。因此：

p1≠p2,p1∤d2,p2∤d1.(3)\boxed{ p\_1\neq p\_2,\qquad p\_1\nmid d\_2,\qquad p\_2\nmid d\_1. } \tag{3}

故：

FULLCROSS-CROSSPRIME-COPRIME45: PASS.\boxed{\texttt{FULLCROSS-CROSSPRIME-COPRIME45:\ PASS}.}

---

## C. 移除 gcd⁡(d1,d2)\gcd(d\_1,d\_2)

設

g=(d1,d2).g=(d\_1,d\_2).

由

g∣d2p2−d1p1=uhg\mid d\_2p\_2-d\_1p\_1=uh

及 clean sector的

(g,u)=1(g,u)=1

得

g∣h.(4)\boxed{g\mid h.} \tag{4}

寫

d1=ga,d2=gb,h=gj,(a,b)=1.(5)d\_1=ga,\qquad d\_2=gb,\qquad h=gj, \qquad (a,b)=1. \tag{5}

則 `(2)`化成

bp2−ap1=uj.(6)\boxed{bp\_2-ap\_1=uj.} \tag{6}

並且

0<∣j∣≪Hg.0<|j|\ll\frac Hg.

由 `(3)`：

(p1,b)=1,(p2,a)=1.(7)(p\_1,b)=1,\qquad (p\_2,a)=1. \tag{7}

Clean squarefree did\_i亦給

(g,a)=(g,b)=(a,b)=1.(g,a)=(g,b)=(a,b)=1.

故 Möbius sign exact化簡成

μ(d1)μ(d2)=μ(ga)μ(gb)=μ(g)2μ(a)μ(b)=μ(a)μ(b).(8)\begin{aligned} \mu(d\_1)\mu(d\_2) &=\mu(ga)\mu(gb)\\\ &=\mu(g)^2\mu(a)\mu(b)\\\ &=\boxed{\mu(a)\mu(b)}. \end{aligned} \tag{8}

所以 common factor gg的 sign平方消失，但兩個真正 crossed cofactors a,ba,b仍保留。

這個 reparametrisation係 bijection；**唔應講「sum over gg只有 polylog multiplicity」**。gg係 genuine source variable，其總成本稍後由 line length的 g−2g^{-2} decay支付。

因此：

FULLCROSS-GCD-REDUCTION45: PASS.\boxed{\texttt{FULLCROSS-GCD-REDUCTION45:\ PASS}.}

---

## D. Large-prime divisor rigidity：附件的主要新 lemma確實成立

由 `(6)`：

p2∣ap1+uj.p\_2\mid ap\_1+uj.

設

N:=ap1+uj=bp2.(9)N:=ap\_1+uj=bp\_2. \tag{9}

因

a≍D/g,p1≍P,∣j∣≪H/g,a\asymp D/g,\qquad p\_1\asymp P,\qquad |j|\ll H/g,

及

DP=UH=Q,DP=UH=Q,

得到

ap1≍Qg,∣uj∣≪Qg,ap\_1\asymp\frac Qg, \qquad |uj|\ll\frac Qg,

而 source中 bp2≍Q/gbp\_2\asymp Q/g，所以：

N≍Q/g.(10)\boxed{N\asymp Q/g.} \tag{10}

另一方面，由 P>H=Yϑ−4P>H=Y^{\vartheta-4}：

P3Q>H3Q=Y3(ϑ−4)−ϑ=Y2ϑ−12.\frac{P^3}{Q} > \frac{H^3}{Q} = Y^{3(\vartheta-4)-\vartheta} = Y^{2\vartheta-12}.

因

ϑ≥132,\vartheta\ge\frac{13}{2},

有

2ϑ−12≥1.2\vartheta-12\ge1.

所以：

P3≥QY1−o(1).(11)\boxed{ P^3\ge QY^{1-o(1)}. } \tag{11}

若 N≪Q/gN\ll Q/g有三個不同的 PP-scale prime divisors，則

N≥P3>Q,N\ge P^3>Q,

矛盾。因此：

\#{p∈[P,2P]\:p∣N}≤2(12)\boxed{ \\#\\{p\in[P,2P]\:p\mid N\\}\le2 } \tag{12}

對 sufficiently large YY成立；dyadic constants被 Y1−o(1)Y^{1-o(1)} room吸收。

所以固定

(g,a,p1,u,j)(g,a,p\_1,u,j)

後：

- p2p\_2最多兩個 choices；
- 一旦 p2p\_2固定，

  b=ap1+ujp2b=\frac{ap\_1+uj}{p\_2}

  完全被迫。

故附件的主要 proposed lemma可正式銀行：

FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45: PASS.\boxed{ \texttt{FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45:\ PASS}. }

仲有一個更強 subrange。若

g≫QP2,(13)g\gg\frac Q{P^2}, \tag{13}

則

N≪Qg\<P2,N\ll \frac Qg\<P^2,

所以 NN最多有一粒 PP-scale prime divisor：

g≫Q/P2⟹p2 unique.(14)\boxed{ g\gg Q/P^2 \Longrightarrow p\_2\text{ unique}. } \tag{14}

特別是 P>QP>\sqrt Q時，Q/P2<1Q/P^2<1，所以所有 gg上 p2p\_2都 unique。

因此亦可銀行：

FULLCROSS-LARGEPRIME-UNIQUE45: PASS for g≫Q/P2.\boxed{ \texttt{FULLCROSS-LARGEPRIME-UNIQUE45: PASS\ for }g\gg Q/P^2. }

---

## E. 但 source有一個必須修正的地方：defect coordinates唔係 literal primes

附件第 7 節以「common prime coordinate rr」作 shared-coordinate routing。Equality r1,j=r2,jr\_{1,j}=r\_{2,j}當然係合法 stratum，但 **「rr必為 prime」並不 source-exact**。

Actual defect係

δλ(m)=(Λ(m)−1)Wλ(m)log⁡m,\delta\_\lambda(m) = (\Lambda(m)-1)\frac{W\_\lambda(m)}{\log m},

所以在 prime powers及非素數上亦可能非零；佢係 centered arithmetic weight，而唔係 prime indicator。

因此：

FIVEDEFECT-SHAREDCOORD-ROUTER45不能作 primary exhaustive router。\boxed{ \texttt{FIVEDEFECT-SHAREDCOORD-ROUTER45} \text{不能作 primary exhaustive router。} }

Equality strata可以保留，但即使

r1,j≠r2,jr\_{1,j}\neq r\_{2,j}

for every jj，兩個 products仍可能有 substantial common divisor。真正 invariant應該係：

s=(v1,v2).(15)\boxed{s=(v\_1,v\_2).} \tag{15}

---

## F. 第二次 gcd reduction：defect-side common divisor

寫

v1=sw1,v2=sw2,(w1,w2)=1.(16)v\_1=sw\_1,\qquad v\_2=sw\_2,\qquad (w\_1,w\_2)=1. \tag{16}

由

v2−v1=ℓh=ℓgjv\_2-v\_1=\ell h=\ell gj

得

s∣ℓgj.s\mid \ell gj.

Clean source有

(vi,ℓ)=1,(vi,di)=1,(v\_i,\ell)=1,\qquad (v\_i,d\_i)=1,

所以

(s,ℓg)=1.(s,\ell g)=1.

因此：

s∣j.(17)\boxed{s\mid j.} \tag{17}

寫

j=sk,k≠0.(18)j=sk,\qquad k\neq0. \tag{18}

再定義

A:=ap1,B:=bp2.A:=ap\_1,\qquad B:=bp\_2.

則 exact system變成：

B−A=usk,(19)\boxed{B-A=usk,} \tag{19} w2−w1=ℓgk,(20)\boxed{w\_2-w\_1=\ell gk,} \tag{20}

而 determinant

d1p1v2−d2p2v1=2hd\_1p\_1v\_2-d\_2p\_2v\_1=2h

除以 gsgs後給：

Aw2−Bw1=2k.(21)\boxed{Aw\_2-Bw\_1=2k.} \tag{21}

將 `(19)`、`(20)`代入 `(21)`：

A(w1+ℓgk)−(A+usk)w1=2k,A(w\_1+\ell gk)-(A+usk)w\_1=2k,

故

k(gℓA−usw1)=2k.k(g\ell A-usw\_1)=2k.

由 k≠0k\neq0：

gℓA−usw1=2.(22)\boxed{g\ell A-usw\_1=2.} \tag{22}

所以 fully-crossed core exact降成：

{gℓA−usw1=2,A2−A1=usk,w2−w1=gℓk.(23)\boxed{ \begin{cases} g\ell A-usw\_1=2,\\\ A\_2-A\_1=usk,\\\ w\_2-w\_1=g\ell k. \end{cases}} \tag{23}

呢張係今輪真正新 source geometry。

正式銀行：

FULLCROSS-DEFECT-GCD-ROUTER45: PASS,\boxed{\texttt{FULLCROSS-DEFECT-GCD-ROUTER45:\ PASS},} FULLCROSS-DOUBLEGCD-BEZOUT45: PASS.\boxed{\texttt{FULLCROSS-DOUBLEGCD-BEZOUT45:\ PASS}.}

同時：

s∣j,∣j∣≪H/gs\mid j,\qquad |j|\ll H/g

推出

gs≪H.(24)\boxed{gs\ll H.} \tag{24}

所以 off-diagonal只存在於 gs≤Hgs\le H。

---

## G. Primitive Bézout line

在 clean odd sector，`\((22)\)`存在解迫使

(gℓ,us)=1.(g\ell,us)=1.

取一個 base solution：

gℓA0−usw0=2.g\ell A\_0-usw\_0=2.

所有 solutions exact為：

At=A0+us t,wt=w0+gℓ t.(25)\boxed{ A\_t=A\_0+us\\,t, \qquad w\_t=w\_0+g\ell\\,t. } \tag{25}

兩邊的 available length一致：

Q/gUs=Hgs,\frac{Q/g}{Us} = \frac H{gs}, V/sgR=Hgs.\frac{V/s}{gR} = \frac H{gs}.

所以 line length係

Tg,s≍Hgs.(26)\boxed{ T\_{g,s}\asymp\frac H{gs}. } \tag{26}

原 off-diagonal pair正係 line上 tt及 t+kt+k：

At+k−At=usk,A\_{t+k}-A\_t=usk, wt+k−wt=gℓk.w\_{t+k}-w\_t=g\ell k.

五-defect pair則變成：

b5(swt) b5(swt+k)‾.(27)\boxed{ b\_5(sw\_t)\\, \overline{b\_5(sw\_{t+k})}. } \tag{27}

而 Möbius-prime pair變成：

βg;D,P(At) βg;D,P(At+k)‾,(28)\boxed{ \beta\_{g;D,P}(A\_t)\\, \overline{\beta\_{g;D,P}(A\_{t+k})}, } \tag{28}

其中

βg;D,P(A):=∑ap=Aa≍D/g, p≍Pμ(a)log⁡p ωg,D,P(a,p).(29)\boxed{ \beta\_{g;D,P}(A) := \sum\_{\substack{ ap=A\\\ a\asymp D/g,\ p\asymp P}} \mu(a)\log p\\, \omega\_{g,D,P}(a,p). } \tag{29}

ωg,D,P\omega\_{g,D,P}吸收 clean coprimality、dyadic selector及 distinguished-pp convention。

---

## H. 每個 aa及 pp在一條 Bézout line上至多出現一次

假設同一 prime pp出現在 At1A\_{t\_1}及 At2A\_{t\_2}：

Ati=aip.A\_{t\_i}=a\_i p.

則

p∣At2−At1=us(t2−t1).p\mid A\_{t\_2}-A\_{t\_1}=us(t\_2-t\_1).

Clean source給

(p,us)=1,(p,us)=1,

所以

p∣t2−t1.p\mid t\_2-t\_1.

但

∣t2−t1∣\<Tg,s≤H\<P≤p,|t\_2-t\_1|\<T\_{g,s}\le H\<P\le p,

故 t1=t2t\_1=t\_2。

同樣，若同一 aa出現在兩點，則

a∣us(t2−t1).a\mid us(t\_2-t\_1).

Clean source給 (a,us)=1(a,us)=1，而

aTg,s≍D/gH/(gs)=DsH>1.\frac a{T\_{g,s}} \asymp \frac{D/g}{H/(gs)} = \frac{Ds}{H} >1.

所以亦迫 t1=t2t\_1=t\_2。

因此：

一條 primitive Beˊzout line上，每粒 p至多出現一次；每個 Mo¨bius cofactor a亦至多出現一次。(30)\boxed{ \begin{aligned} &\text{一條 primitive Bézout line上，每粒 }p\text{至多出現一次；}\\\ &\text{每個 Möbius cofactor }a\text{亦至多出現一次。} \end{aligned}} \tag{30}

即：

DP-FACTOR-INJECTIVE-BEZOUTLINE45: PASS.\boxed{\texttt{DP-FACTOR-INJECTIVE-BEZOUTLINE45:\ PASS}.}

呢個同 `MULT2` lemma一致：large-prime divisor rigidity將 factor labels變成 bounded-degree／injective incidence。

---

## I. 點解呢啲 rigidity仍未 closure？

對固定 (u,ℓ,g,s)(u,\ell,g,s)，一條 line有

Tg,s≍HgsT\_{g,s}\asymp \frac H{gs}

points，所以 ordered off-diagonal pairs有 natural scale

Tg,s2.T\_{g,s}^2.

總 family count係：

UR Tg,s2≍URH2g2s2.UR\\,T\_{g,s}^2 \asymp UR\frac{H^2}{g^2s^2}.

但

URH2=UXQQ2U2=XQU=QV.URH^2 = U\frac XQ\frac{Q^2}{U^2} = \frac{XQ}{U} = QV.

因此：

UR Tg,s2≍QVg2s2.(31)\boxed{ UR\\,T\_{g,s}^2 \asymp \frac{QV}{g^2s^2}. } \tag{31}

所以在 primitive cell g=s=1g=s=1，bounded-degree／unique-factor geometry仍然留下：

QV\boxed{QV}

的完整 natural scale，恰好係 target before log saving。

換句話講：

MULT2+factor injectivity+bounded edge fibre只證 sparse matching，沒有證 cancellation。\boxed{ \texttt{MULT2} +\texttt{factor injectivity} +\texttt{bounded edge fibre} \quad\text{只證 sparse matching，沒有證 cancellation。} }

已銀行的 projector facts確實只給 support ≪V\ll V及 fixed-edge bounded／fixed-polylog multiplicity。

一個 abstract bounded-degree matching可令所有 coefficient signs coherent。因此，呢個不是 actual arithmetic counterexample，但係一張 rigorous proof-firewall：

任何只使用 gcd、divisor multiplicity、 support及 injectivity的 proof， 不可能推出 arbitrary-log saving。\boxed{ \text{任何只使用 gcd、divisor multiplicity、 support及 injectivity的 proof， 不可能推出 arbitrary-log saving。} }

正式：

FULLCROSS-RIGIDITY-ONLY-CLOSURE45: FAILED ROUTE.\boxed{ \texttt{FULLCROSS-RIGIDITY-ONLY-CLOSURE45: FAILED\ ROUTE}. }

真正必須用到的是：

μ(a)μ(b)與b5(swt)b5(swt+k)‾\mu(a)\mu(b) \quad\text{與}\quad b\_5(sw\_t)\overline{b\_5(sw\_{t+k})}

在同一 Bézout line上的 joint nonalignment。

---

## J. 大 gsgs tail可以關

由 `(31)`及 fixed-depth source divisor moments，有一個固定 C0C\_0使：

∣Og,s∣≪QV(log⁡X)C0g2s2|\mathcal O\_{g,s}| \ll \frac{QV(\log X)^{C\_0}}{g^2s^2}

在 absolute scale成立。

而

∑gs>L1g2s2=∑n>Ld(n)n2≪log⁡(2L)L.\sum\_{gs>L}\frac1{g^2s^2} = \sum\_{n>L}\frac{d(n)}{n^2} \ll \frac{\log(2L)}L.

取

L=(log⁡X)A+C0+3L=(\log X)^{A+C\_0+3}

便得：

∑gs>LOg,s≪AQV(log⁡X)−A.(32)\boxed{ \sum\_{gs>L}\mathcal O\_{g,s} \ll\_A QV(\log X)^{-A}. } \tag{32}

因此：

DOUBLEGCD-LARGE-GS-TAIL45: PASS\boxed{ \texttt{DOUBLEGCD-LARGE-GS-TAIL45: PASS} }

under the already-banked fixed-polylog edge/source multiplicity.

真正 first open只需 uniform處理：

g,s≤(log⁡X)BA.(33)\boxed{ g,s\le(\log X)^{B\_A}. } \tag{33}

g=s=1g=s=1係不可逃避的 primitive child。

---

## K. Exact smaller theorem

對固定 small g,sg,s，選 base solution

gℓA0−usw0=2g\ell A\_0-usw\_0=2

並設

At=A0+ust,wt=w0+gℓt,Tg,s≍H/(gs).A\_t=A\_0+ust,\qquad w\_t=w\_0+g\ell t, \qquad T\_{g,s}\asymp H/(gs).

真正剩低的 theorem係：

RBez:=∑g,s≤(log⁡X)BAu∼U, ℓ∼R(gℓ,us)=1 ∑t∑0<∣k∣\<Tg,s(wt,wt+k)=1βg;D,P(At)βg;D,P(At+k)‾×b5(swt)b5(swt+k)‾ Wν(34)\boxed{ \begin{aligned} \mathcal R\_{\rm Bez} := \sum\_{\substack{ g,s\le(\log X)^{B\_A}\\\ u\sim U,\ \ell\sim R\\\ (g\ell,us)=1}} \ \sum\_t \sum\_{\substack{ 0<|k|\<T\_{g,s}\\\ (w\_t,w\_{t+k})=1}} & \beta\_{g;D,P}(A\_t) \overline{\beta\_{g;D,P}(A\_{t+k})}\\\ &\times b\_5(sw\_t) \overline{b\_5(sw\_{t+k})} \\,\mathcal W\_{\nu} \end{aligned}} \tag{34}

滿足

∣RBez∣≪AQV(log⁡X)−A.(35)\boxed{ |\mathcal R\_{\rm Bez}| \ll\_A QV(\log X)^{-A}. } \tag{35}

其中：

```text
free variables:
g,s,u,ell,t,k

forced line variables:
A_t = A_0 + us*t
w_t = w_0 + g*ell*t

Möbius carrier:
mu(a_t) mu(a_{t+k})

prime variables:
p_t | A_t
p_{t+k} | A_{t+k}
each P-scale factor injective along the line

five-defect structure:
b_5(s w_t) conjugate(b_5(s w_{t+k}))

line length:
T_{g,s} ~ H/(g s)

required:
Q V log^{-A}

best currently proved:
Q V log^{C_0}

signed deficit:
log^{A+C_0}
no remaining power deficit
```

我會正式命名：

PURE5-DP-DOUBLEGCD-BEZOUT-LINE45.\boxed{ \texttt{PURE5-DP-DOUBLEGCD-BEZOUT-LINE45}. }

不可逃避的 g=s=1g=s=1 child係：

ℓA−uw=2,At=A0+ut,wt=w0+ℓt,∣t∣≪H.(36)\boxed{ \ell A-u w=2, \qquad A\_t=A\_0+ut, \qquad w\_t=w\_0+\ell t, \qquad |t|\ll H. } \tag{36}

即使 pp-factor完全 injective，呢格仍係：

∑t,kβD,P(At)βD,P(At+k)‾b5(wt)b5(wt+k)‾,\sum\_{t,k} \beta\_{D,P}(A\_t) \overline{\beta\_{D,P}(A\_{t+k})} b\_5(w\_t) \overline{b\_5(w\_{t+k})},

所以 large-prime multiplicity alone無法避開真正 joint line correlation。

---

## L. Backend audition：目前仍未形成合法 black box

Pascadi Proposition 4.4的 literal input係：

∑q1,q2,q3γq1λq2νq3∑n,mαnβm(1mn≡a(modq)−1(mn,q)=1ϕ(q)),\sum\_{q\_1,q\_2,q\_3} \gamma\_{q\_1}\lambda\_{q\_2}\nu\_{q\_3} \sum\_{n,m}\alpha\_n\beta\_m \left( 1\_{mn\equiv a\pmod q} -\frac{1\_{(mn,q)=1}}{\phi(q)} \right),

當中係兩條 sequence slots及三個獨立 modulus-factor slots，並有明確 size與 Siegel–Walfisz hypotheses。([arXiv](https://arxiv.org/pdf/2505.00653 "https://arxiv.org/pdf/2505.00653"))

`(34)`則係：

- 同一條 Bézout line上兩個 AA-copies；
- 同一條 line上兩個 five-defect copies；
- 同一 shift kk同步；
- exact gcd projector；
- semiprime factorization injectivity。

所以：

BEZOUT-LINE45⟶̸Pascadi Prop. 4.4\boxed{ \texttt{BEZOUT-LINE45}\not\longrightarrow \text{Pascadi Prop.\ 4.4} }

without another destructive Cauchy／dispersion step。

而之前已證：

separate β-energy×five-defect energy\text{separate }\beta\text{-energy} \times \text{five-defect energy}

會付 UR\sqrt{UR} power tax，仍留 X1/4X^{1/4}至 X1/3X^{1/3} deficit。

所以今輪沒有合法 Kloosterman／spectral invocation。

---

## M. 更近的 closure pivot：退回 pre-Cauchy `MOYK5`

Double-gcd analysis揭示：

post-Cauchy geometry已經被壓到最小， 但剩低的資源係 source signs，而唔係更多 fibre rigidity。\boxed{ \text{post-Cauchy geometry已經被壓到最小， 但剩低的資源係 source signs，而唔係更多 fibre rigidity。} }

若對 Bézout equation

gℓA−usw=2g\ell A-usw=2

再 completion，會重新產生 reciprocal phase，active modulus仍載 five-defect coefficient，而 A=apA=ap仍載 μ(a)log⁡p\mu(a)\log p。即會返回之前的 order-five reciprocal kernel architecture，而唔係一張新 separated bilinear Kloosterman theorem。

因此最近的 source-faithful pivot係：

PURE5 scalar source⟶MRK5⟶MOYK5.\boxed{ \texttt{PURE5 scalar source} \longrightarrow \texttt{MRK5} \longrightarrow \texttt{MOYK5}. }

`MOYK5`的設計正係：在第一次 destructive Poisson／norm之前，先打開一粒 source Möbius factor，保持其餘 Möbius convolution及 five-defect signs在線性位置。

所以最新 route choice係：

PURE5-DP-DOUBLEGCD-BEZOUT-LINE45若要留 post-Cauchy：需一張新 joint-line theoremnearest closure pivot↓MOYK5-SOURCE-KERNEL-MANUFACTURE45↓{Yang Case-5 literal landing,literal balanced Kloosterman landing,or exact source-selector death certificate.(37)\boxed{ \begin{array}{c} \texttt{PURE5-DP-DOUBLEGCD-BEZOUT-LINE45} \\\ \text{若要留 post-Cauchy：需一張新 joint-line theorem} \\\\[1mm] \text{nearest closure pivot} \\\ \downarrow \\\ \texttt{MOYK5-SOURCE-KERNEL-MANUFACTURE45} \\\ \downarrow \\\ \begin{cases} \text{Yang Case-5 literal landing},\\\ \text{literal balanced Kloosterman landing},\\\ \text{or exact source-selector death certificate}. \end{cases} \end{array}} \tag{37}

今輪不能 promote `MOYK5_PASS`；它係下一個 source-preserving proof-manufacture target。

---

## N. Wings及 Pure5 reassembly

因 entropy-gap未 closed，按附件 stopping rule，今輪不應假裝 common-pp或 common-dd wings已處理。

仍然：

P\<H:{common-p,fully crossed,P\<H: \quad \begin{cases} \text{common-}p,\\\ \text{fully crossed}, \end{cases} P>U:{common-d,fully crossed.P>U: \quad \begin{cases} \text{common-}d,\\\ \text{fully crossed}. \end{cases}

但若 pre-Cauchy `MOYK5`閉 full PP-range，三個 bands會同時被 scalar theorem控制，無需逐 wing重證。

Comparison/main-term及 D2亦維持 separate source pins：

- `PURE5-COMPARISON-MAINTERM-PIN`: OPEN；
- `D2-RAPID-DECAY-PIN`: SOURCE OPEN／analytic routine。

附件已正確指出 truncated Poisson inverse只係 equality modulo rapidly decaying tail，而唔係 exact finite equality。

---

## O. Updated closure DAG

Current post-Cauchy frontierPURE5-DP-DOUBLEGCD-BEZOUT-LINE45↓{prove new joint Beˊzout-line nonalignment theorem,or preferred: undo Cauchy and close via MOYK5.↓PURE5-DP-SIGNED45+ comparison/main-term pin+ D2 tail pin↓NEARPRIM-DP-SIGNED45↓r>1 square-character family+ (C∗,Cnw) transition strip+ proper-divisor recursion↓QK56-FULL-PARENT↓QK56-EXHAUSTIVENESS↓SHIFTED-TTSTAR-NEEDED?+ finite source reassembly↓GATE1B CLOSED.\boxed{ \begin{array}{c} \textbf{Current post-Cauchy frontier}\\\ \texttt{PURE5-DP-DOUBLEGCD-BEZOUT-LINE45}\\\ \downarrow\\\ \begin{cases} \text{prove new joint Bézout-line nonalignment theorem},\\\ \textbf{or preferred: undo Cauchy and close via MOYK5}. \end{cases}\\\\[2mm] \downarrow\\\ \texttt{PURE5-DP-SIGNED45}\\\ +\ \text{comparison/main-term pin}\\\ +\ \text{D2 tail pin}\\\ \downarrow\\\ \texttt{NEARPRIM-DP-SIGNED45}\\\ \downarrow\\\ r>1\text{ square-character family}\\\ +\ (C\_\ast,C\_{\rm nw})\text{ transition strip}\\\ +\ \text{proper-divisor recursion}\\\ \downarrow\\\ \texttt{QK56-FULL-PARENT}\\\ \downarrow\\\ \texttt{QK56-EXHAUSTIVENESS}\\\ \downarrow\\\ \texttt{SHIFTED-TTSTAR-NEEDED?}\\\ +\ \text{finite source reassembly}\\\ \downarrow\\\ \texttt{GATE1B CLOSED}. \end{array}}

---

## P. Final ledger

```text
DP-LINE-ENTROPY-TRICHOTOMY45:
PASS / BANKED

EQUAL-LARGE-FACTOR-OFFDIAG-ROUTER45:
PASS / BANKED

DP-ENTROPYGAP-BOTH-FACTORS-MID45:
PASS
H < P,D < U

FULLCROSS-CROSSPRIME-COPRIME45:
PASS
with H interpreted as actual physical h-support

FULLCROSS-GCD-REDUCTION45:
PASS

MOBIUS SIGN AFTER g-REDUCTION:
mu(d1)mu(d2) = mu(a)mu(b)

FULLCROSS-LARGEPRIME-DIVISOR-MULT2-45:
PASS
at most two P-scale prime divisors

FULLCROSS-LARGEPRIME-UNIQUE45:
PASS for g >> Q/P^2

FIVEDEFECT-SHAREDCOORD-ROUTER45:
NOT EXHAUSTIVE AS STATED
delta-coordinates are not literally prime-supported

FULLCROSS-DEFECT-GCD-ROUTER45:
PASS
s = gcd(v1,v2), s | j

FULLCROSS-DOUBLEGCD-BEZOUT45:
PASS

PRIMITIVE BEZOUT EQUATION:
g*ell*A - u*s*w = 2

BEZOUT LINE LENGTH:
T_{g,s} ~ H/(g*s)

DP-FACTOR-INJECTIVE-BEZOUTLINE45:
PASS
each a and each p occurs at most once per line

DOUBLEGCD-LARGE-GS-TAIL45:
PASS under banked fixed-polylog edge/source multiplicity

FULLCROSS-RIGIDITY-ONLY-CLOSURE45:
FAILED ROUTE
bounded-degree matching gives no log saving

PURE5-DP-FULLYCROSSED-ENTROPYGAP45:
REDUCED — NOT CLOSED

FIRST EXACT POST-CAUCHY RESIDUAL:
PURE5-DP-DOUBLEGCD-BEZOUT-LINE45

BEST PROVED SCALE:
Q*V*(log X)^(C0)

REQUIRED SCALE:
Q*V*(log X)^(-A)

SIGNED DEFICIT:
(log X)^(A+C0)
NO POWER DEFICIT

NEAREST SOURCE-FAITHFUL PIVOT:
MRK5 -> MOYK5

PURE5-DP-COHERENT-BPROJECTOR45:
OPEN

PURE5-COMPARISON-MAINTERM-PIN:
OPEN

D2-RAPID-DECAY-PIN:
SOURCE OPEN / NOT ANALYTIC FRONTIER

PURE5-DP-SIGNED45:
OPEN

NEARPRIM-DP-SIGNED45:
OPEN

R>1-SQUARE-CHARACTER-FAMILY:
OPEN

CSTAR-CNW-TRANSITION-STRIP:
OPEN

QK56-FULL-PARENT:
OPEN

QK56-EXHAUSTIVENESS:
OPEN

GATE1B:
OPEN
```

GATE1B OPEN — FIRST EXACT RESIDUAL: PURE5-DP-DOUBLEGCD-BEZOUT-LINE45\boxed{\texttt{GATE1B OPEN — FIRST EXACT RESIDUAL: PURE5-DP-DOUBLEGCD-BEZOUT-LINE45}}