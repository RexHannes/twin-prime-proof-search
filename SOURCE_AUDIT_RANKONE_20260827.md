# GOLD INVENT/CLOSE 1B — `BEZOUT-LINE JOINT NONALIGNMENT45`

今輪我直接攻 actual theorem，而唔再轉 representation。控制判決係：

BEZOUT-LINE-JOINT-NONALIGNMENT45: STRICTLY REDUCED, BUT NOT CLOSED.\boxed{ \texttt{BEZOUT-LINE-JOINT-NONALIGNMENT45: STRICTLY\ REDUCED,\ BUT\ NOT\ CLOSED}. }

新銀行內容係：

BETA-DP-TO-MU-LARGEPRIME45\:PASS,RANKONE-SHIFT-BIJECTION45\:PASS,LOW-PRETENTIOUS-PROFILE45\:PASS,ALLSHIFT-CHOWLA-TO-RANKONE45\:FALSE,WRIGHT-PARTFIX-MOYK5-45\:POWER NONCLOSING.\boxed{ \begin{aligned} &\texttt{BETA-DP-TO-MU-LARGEPRIME45}: &&\mathbf{PASS},\\\ &\texttt{RANKONE-SHIFT-BIJECTION45}: &&\mathbf{PASS},\\\ &\texttt{LOW-PRETENTIOUS-PROFILE45}: &&\mathbf{PASS},\\\ &\texttt{ALLSHIFT-CHOWLA-TO-RANKONE45}: &&\mathbf{FALSE},\\\ &\texttt{WRIGHT-PARTFIX-MOYK5-45}: &&\mathbf{POWER\ NONCLOSING}. \end{aligned}}

真正剩低的 theorem可以用一張更 canonical、但與舊 residual **等價而非改名逃走**的形式表示：

RANKONE-BEZOUT-AFFINE-ELLIOTT5D45.\boxed{ \texttt{RANKONE-BEZOUT-AFFINE-ELLIOTT5D45}. }

它仍是

PURE5-DP-DOUBLEGCD-BEZOUT-LINE45\texttt{PURE5-DP-DOUBLEGCD-BEZOUT-LINE45}

的 primitive g=s=1g=s=1 child；現在只是將真正的 Möbius結構、shift family及現有 Chowla interfaces完全打印出來。

---

## A. 先固定真正 source與 target

目前 sign-preserving parent是

S5(D,P)=∑u∼U, v∼V, d∼D, p∼P, ℓ∼Ruv+2=dpℓa4(u)b5(v)μ(d)log⁡p WR(ℓ),(1)\boxed{ \mathcal S\_5(D,P)= \sum\_{\substack{ u\sim U,\ v\sim V,\ d\sim D,\ p\sim P,\ \ell\sim R\\\ uv+2=dp\ell}} a\_4(u)b\_5(v)\mu(d)\log p\\,W\_R(\ell), } \tag{1}

其中

U=Y4,V=Y5,R=XQ,DP≍Q,U=Y^4,\qquad V=Y^5,\qquad R=\frac XQ,\qquad DP\asymp Q, a4=f1∗f2∗f3∗f4,b5=δ1∗δ2∗δ3∗δ4∗δ5.(2)a\_4=f\_1\*f\_2\*f\_3\*f\_4,\qquad b\_5=\delta\_1\*\delta\_2\*\delta\_3\*\delta\_4\*\delta\_5. \tag{2}

五個 δi\delta\_i及 μ(d)\mu(d)在這一層全部仍然 linear；附件亦明確禁止先形成 positive square或將 b5b\_5換成其 L2L^2-energy。

最新 post-Cauchy residual目前最好只有

QV(log⁡X)C0,QV(\log X)^{C\_0},

而要求

QV(log⁡X)−A;QV(\log X)^{-A};

即無 power deficit，只差真正 arbitrary-log cancellation。純 rigidity、large-prime injectivity及 bounded-degree matching已被證明不足，因 primitive g=s=1g=s=1仍保留完整 QVQV scale。

---

# B. 第一張新 exact simplification：打開 β\beta 後，它就是 Möbius

Clean squarefree cell中定義

LD,P(n):=∑p∣np∼Pn/p∼Dlog⁡p.(3)L\_{D,P}(n):= \sum\_{\substack{ p\mid n\\\ p\sim P\\\ n/p\sim D}} \log p. \tag{3}

則

βD,P(n)=∑dp=nd∼D, p∼Pμ(d)log⁡p=∑p∣np∼P, n/p∼Dμ(n/p)log⁡p.\begin{aligned} \beta\_{D,P}(n) &= \sum\_{\substack{ dp=n\\\d\sim D,\ p\sim P}} \mu(d)\log p\\\ &= \sum\_{\substack{ p\mid n\\\p\sim P,\ n/p\sim D}} \mu(n/p)\log p. \end{aligned}

因 nn squarefree且 p∣np\mid n：

μ(n/p)=−μ(n).\mu(n/p)=-\mu(n).

所以 exact：

βD,P(n)=−μ(n)LD,P(n).(4)\boxed{ \beta\_{D,P}(n) = -\mu(n)L\_{D,P}(n). } \tag{4}

而 entropy-gap large-prime lemma已證：任何 n≪Q/gn\ll Q/g最多只有兩粒 PP-scale prime divisors；一旦 prime fixed，另一個 cofactor被迫。 因此

0≤LD,P(n)≪log⁡X(5)0\le L\_{D,P}(n)\ll\log X \tag{5}

及其 multiplicity是 O(1)O(1)。

故：

BETA-DP-TO-MU-LARGEPRIME45: PASS.\boxed{\texttt{BETA-DP-TO-MU-LARGEPRIME45:\ PASS}.}

這個 promotion很有用：剩低的 parity carrier不是一條 mysterious semiprime coefficient，而係 literal

μ(At)μ(At+k).\mu(A\_t)\mu(A\_{t+k}).

---

# C. Primitive Bézout residual的 canonical form

在 g=s=1g=s=1 child，選一個 base solution

ℓA0−uw0=2,(u,ℓ)=1,(6)\ell A\_0-u w\_0=2, \qquad (u,\ell)=1, \tag{6}

並寫

At=A0+ut,wt=w0+ℓt,∣t∣≪H,(7)A\_t=A\_0+ut, \qquad w\_t=w\_0+\ell t, \qquad |t|\ll H, \tag{7}

其中

H=QU=VR.(8)H=\frac QU=\frac VR. \tag{8}

則 primitive residual exact變成

RR1:=∑u∼U, ℓ∼R(u,ℓ)=1∑t∑k≠0∣t+k∣≪Hμ(At)μ(At+k)×LD,P(At)LD,P(At+k)×b5(wt)b5(wt+k)‾ Wu,ℓ,t,k.(9)\boxed{ \begin{aligned} \mathcal R\_{\mathrm{R1}} := \sum\_{\substack{ u\sim U,\ \ell\sim R\\\ (u,\ell)=1}} \sum\_t\sum\_{\substack{k\ne0\\\\|t+k|\ll H}} & \mu(A\_t)\mu(A\_{t+k})\\\ &\times L\_{D,P}(A\_t)L\_{D,P}(A\_{t+k})\\\ &\times b\_5(w\_t)\overline{b\_5(w\_{t+k})} \\,\mathcal W\_{u,\ell,t,k}. \end{aligned}} \tag{9}

Required：

∣RR1∣≪AQV(log⁡X)−A.(10)\boxed{ |\mathcal R\_{\mathrm{R1}}| \ll\_A QV(\log X)^{-A}. } \tag{10}

這就係：

RANKONE-BEZOUT-AFFINE-ELLIOTT5D45.\boxed{ \texttt{RANKONE-BEZOUT-AFFINE-ELLIOTT5D45}. }

它不是 arbitrary weighted Chowla。其 weight固定為：

LD,P(At)LD,P(At+k)b5(wt)b5(wt+k)‾,L\_{D,P}(A\_t)L\_{D,P}(A\_{t+k}) b\_5(w\_t)\overline{b\_5(w\_{t+k})},

而兩套 affine forms的 resultant恆為

ℓAt−uwt=2.\ell A\_t-u w\_t=2.

---

## 一個有用的 exact geometric interpretation

令

Mt:=(Atuwtℓ).M\_t:= \begin{pmatrix} A\_t&u\\\ w\_t&\ell \end{pmatrix}.

則

det⁡Mt=2,\det M\_t=2,

而且

Mt=M0(10t1).(11)\boxed{ M\_t = M\_0 \begin{pmatrix} 1&0\\\ t&1 \end{pmatrix}. } \tag{11}

所以我們不是在估任意 affine correlations，而是在估 determinant-22 integral matrices上，一條 discrete unipotent orbit的 source correlation。

這亦解釋點解：

- line Fourier；
- MOYK5 reciprocal kernel；
- QK5 character parent；
- post-Cauchy Bézout graph

不斷互相 anti-loop：全部是同一 unipotent orbit的不同 Fourier coordinates。

---

# D. 新 shift theorem：真正係 rank-one family，不是普通 averaged Chowla

對 off-diagonal shift定義

r:=uk,s:=ℓk.(12)r:=uk,\qquad s:=\ell k. \tag{12}

因 (u,ℓ)=1(u,\ell)=1：

k=(r,s),u=r(r,s),ℓ=s(r,s).(13)\boxed{ k=(r,s),\qquad u=\frac r{(r,s)},\qquad \ell=\frac s{(r,s)}. } \tag{13}

因此 map

(u,ℓ,k)⟼(r,s)(u,\ell,k)\longmapsto(r,s)

在 clean positive sector係 injective。

真正 shift family大小：

\#{(u,ℓ,k)}≍URH.\\#\\{(u,\ell,k)\\} \asymp URH.

而

URH=Y4⋅Y9−ϑ⋅Yϑ−4=Y9=X.(14)URH = Y^4\cdot Y^{9-\vartheta}\cdot Y^{\vartheta-4} = Y^9 = X. \tag{14}

但兩個 independent shifts的完整 rectangle有：

r≪Q=UH,s≪V=RH,r\ll Q=UH,\qquad s\ll V=RH,

所以大小：

QV=URH2=XH.(15)QV = URH^2 = XH. \tag{15}

故 actual shifts只佔 independent rectangle的

1H(16)\boxed{\frac1H} \tag{16}

比例。

而

H=Yϑ−4≥Y5/2=X5/18.(17)H=Y^{\vartheta-4} \ge Y^{5/2} = X^{5/18}. \tag{17}

因此：

把 rank-one shifts嵌入 ordinary all-shift average， 會付至少 X5/18 的 power tax。(18)\boxed{ \text{把 rank-one shifts嵌入 ordinary all-shift average， 會付至少 }X^{5/18}\text{ 的 power tax。} } \tag{18}

正式：

RANKONE-SHIFT-BIJECTION45: PASS.\boxed{\texttt{RANKONE-SHIFT-BIJECTION45:\ PASS}.}

---

# E. 點解 Guo／Tao–Teräväinen／averaged Chowla不能直接補呢格？

Guo最新 theorem係 logarithmically weighted Liouville two-point correlation，而且 growing-shift range只到

h≤(log⁡x)κ,κ<1/700;h\le(\log x)^\kappa,\qquad \kappa<1/700;

paper亦明確說不證 ordinary Cesàro two-point Chowla。([arXiv](https://arxiv.org/abs/2608.23500?utm_source=chatgpt.com "Quantitative Logarithmic Chowla Correlations Uniformly over Growing Shifts"))

我哋這裡則有：

uk≲Q,ℓk≲V,uk\lesssim Q,\qquad \ell k\lesssim V,

兩者都是 XX 的固定正冪；同時 weight依賴 (u,ℓ,k)(u,\ell,k)，不是一條固定 bounded sequence。

Tao–Teräväinen的 structural theorem處理 logarithmically averaged multiplicative correlations與固定 shifts，證 correlation sequence是periodic limits，並在 nonpretentious case消失；它不是一張 ordinary、large-coefficient、rank-one weighted theorem。([arXiv](https://arxiv.org/abs/1708.02610 "https://arxiv.org/abs/1708.02610"))

Matomäki–Radziwiłł–Tao與Lichtman確實證了 ordinary correlations在**全 shift family平均**下的取消；Lichtman亦容許若干 von Mangoldt/divisor weights。但其 averaging resource是完整的 shift box，而唔係一個 H−1H^{-1}-density rank-one subset加上 shift-dependent b5b\_5-projector。([arXiv](https://arxiv.org/abs/1503.05121?utm_source=chatgpt.com "An averaged form of Chowla's conjecture"))

KMT的 short-arithmetic-progression theorem則控制 bounded multiplicative functions在 almost-all moduli的 residue variance；它不提供本題所需的：

AP additive-frequency transform×shift-dependent five-defect weight\text{AP additive-frequency transform} \times \text{shift-dependent five-defect weight}

的 vector-valued bound。([arXiv](https://arxiv.org/abs/1909.12280 "https://arxiv.org/abs/1909.12280"))

因此：

ALLSHIFT-CHOWLA-TO-RANKONE45: FALSE AS A DIRECT SPLICE.\boxed{ \texttt{ALLSHIFT-CHOWLA-TO-RANKONE45: FALSE\ AS\ A\ DIRECT\ SPLICE}. }

Failure不是「只差改 notation」；完整 shift average的任何 logarithmic gain，都不足以支付 `(18)` 的 fixed power。

---

# F. Fresh 2026 theorem audition：Wright partially-fixed denominator都唔救到

MOYK5 explicit-model reciprocal phase可以寫成

eRfn(2hm‾),(19)e\_{R\_f n}(2h\overline m), \tag{19}

其中總 denominator scale固定為

Rfn≍Y8,R\_fn\asymp Y^8,

而

m≍Q=Yϑ,∣h∣≪Q/Y=Yϑ−1.(20)m\asymp Q=Y^\vartheta,\qquad |h|\ll Q/Y=Y^{\vartheta-1}. \tag{20}

這比 fixed-(B,m)(B,m) Blomer–Pascadi更接近 Toby Wright 2026 的 partially-fixed-modulus trilinear theorem。Wright Theorem 2.1估計

∑a,m,nαmβnνa e ⁣(θam‾nRf),\sum\_{a,m,n} \alpha\_m\beta\_n\nu\_a\\, e\\!\left(\frac{\theta a\overline m}{nR\_f}\right),

並明確保留 fixed denominator factor RfR\_f。([arXiv](https://arxiv.org/pdf/2604.25177 "https://arxiv.org/pdf/2604.25177"))

所以今輪 hostilely audition **所有可能 fixed-factor splits**。

寫

Rf=Yρ,n=Y8−ρ,R\_f=Y^\rho,\qquad n=Y^{8-\rho}, M:=Yϑ,N:=Y8−ρ,A:=Yϑ−1.(21)M:=Y^\vartheta,\qquad N:=Y^{8-\rho},\qquad A:=Y^{\vartheta-1}. \tag{21}

為滿足 Wright的

M≪N2,M\ll N^2,

至少需要

ρ≤16−ϑ2.(22)\rho\le\frac{16-\vartheta}{2}. \tag{22}

允許任意 0≤ρ≤40\le\rho\le4，比 actual labelled splits更 generous。

在 power scale：

∥α∥2≪M1/2Xo(1),∥β∥2≪N1/2Xo(1),∥ν∥2≪A1/2Xo(1).(23)\\|\alpha\\|\_2\ll M^{1/2}X^{o(1)}, \quad \\|\beta\\|\_2\ll N^{1/2}X^{o(1)}, \quad \\|\nu\\|\_2\ll A^{1/2}X^{o(1)}. \tag{23}

Physical prefactor係

RℓY8=Y1−ϑ,\frac{R\_{\ell}}{Y^8} = Y^{1-\vartheta},

而 fixed-factor source的 outer L1L^1-mass至多

Yρ+o(1).Y^{\rho+o(1)}.

將 Wright theorem五項逐一代入，得到 total YY-exponents：

E1=7+ϑ+3ρ8,E2=9+3ϑ4+ρ4,E3=13720+21ϑ20+ρ4,E4=18720+13ϑ20+ρ10,E5=11+ϑ2−ρ8.(24)\boxed{ \begin{aligned} E\_1&=7+\vartheta+\frac{3\rho}{8},\\\ E\_2&=9+\frac{3\vartheta}{4}+\frac{\rho}{4},\\\ E\_3&=\frac{137}{20}+\frac{21\vartheta}{20}+\frac{\rho}{4},\\\ E\_4&=\frac{187}{20}+\frac{13\vartheta}{20}+\frac{\rho}{10},\\\ E\_5&=11+\frac{\vartheta}{2}-\frac{\rho}{8}. \end{aligned}} \tag{24}

Required scalar scale是：

X=Y9.X=Y^9.

但對

132≤ϑ<8,0≤ρ≤min⁡ ⁣(4,16−ϑ2),\frac{13}{2}\le\vartheta<8, \qquad 0\le\rho\le\min\\!\left(4,\frac{16-\vartheta}{2}\right),

逐項有：

min⁡i,ϑ,ρEi=272=13.5.(25)\min\_{i,\vartheta,\rho}E\_i = \frac{27}{2} = 13.5. \tag{25}

最有利位置係：

ϑ=132,ρ=0.\vartheta=\frac{13}{2},\qquad \rho=0.

所以連最有利 split都只給：

Y13.5+o(1)=X3/2+o(1),Y^{13.5+o(1)} = X^{3/2+o(1)},

相對 Y9=XY^9=X仍差：

Y9/2=X1/2.(26)\boxed{ Y^{9/2} = X^{1/2}. } \tag{26}

因此：

WRIGHT-PARTFIX-MOYK5-45: POWER NONCLOSING.\boxed{ \texttt{WRIGHT-PARTFIX-MOYK5-45: POWER\ NONCLOSING}. }

這張 death certificate比「Wright notation唔 match」更強：

> 即使容許最有利 denominator split、自然 coefficient norms及所有 source factors，Wright v2仍至少差 X1/2−o(1)X^{1/2-o(1)}。

Blomer–Pascadi的 all-moduli theorem在 square-root regime確有 c−1/32c^{-1/32} saving；但 current m/Ym/Y slots遠長過其有利 regime，而其 fixed-(B,m)(B,m) application同樣無法供應 moving-family sign cancellation。([arXiv](https://arxiv.org/abs/2607.24311 "https://arxiv.org/abs/2607.24311"))

所以：

現成 Kloosterman-family shortcut基本 exhaust。\boxed{ \text{現成 Kloosterman-family shortcut基本 exhaust。} }

---

# G. 可以真正證的一張 source theorem：low pretentious profiles全部死亡

雖然 full rank-one theorem仍未閉，但一個重要 inverse branch可以直接排除。

令 χ\chi為 primitive character：

cond⁡(χ)≤(log⁡X)B,\operatorname{cond}(\chi)\le(\log X)^B,

並令

∣τ∣≤(log⁡X)B.|\tau|\le(\log X)^B.

對一粒 defect定義

Di(χ,τ):=∑r∼Yδi(r)χ(r)riτ.(27)\mathcal D\_i(\chi,\tau) := \sum\_{r\sim Y} \delta\_i(r)\chi(r)r^{i\tau}. \tag{27}

由

δi(r)=(Λ(r)−1)Wi(r/Y)log⁡r,\delta\_i(r) = (\Lambda(r)-1)\frac{W\_i(r/Y)}{\log r},

Siegel–Walfisz／PNT加 partial summation給，對任意 C>0C>0：

Di(χ,τ)≪B,CY(log⁡X)−C.(28)\boxed{ \mathcal D\_i(\chi,\tau) \ll\_{B,C} Y(\log X)^{-C}. } \tag{28}

Principal χ\chi時，Λ−1\Lambda-1本身完成 centering；nonprincipal時，prime sum及model sum都由 small-conductor character PNT處理。

對 β\beta-source則 exact factor：

BD,P(χ,τ):=∑n∼QβD,P(n)χ(n)niτ=(∑d∼Dμ(d)χ(d)diτWD(d))(∑p∼Plog⁡p χ(p)piτWP(p)).(29)\begin{aligned} \mathcal B\_{D,P}(\chi,\tau) &:= \sum\_{n\sim Q} \beta\_{D,P}(n)\chi(n)n^{i\tau}\\\ &= \left( \sum\_{d\sim D}\mu(d)\chi(d)d^{i\tau}W\_D(d) \right) \left( \sum\_{p\sim P}\log p\\,\chi(p)p^{i\tau}W\_P(p) \right). \end{aligned} \tag{29}

在 entropy gap：

D>H≥X5/18,D>H\ge X^{5/18},

所以 Möbius factor本身已有任意 logarithmic cancellation；若 χ\chi非主，prime factor亦有 Siegel–Walfisz。故：

BD,P(χ,τ)≪B,CQ(log⁡X)−C.(30)\boxed{ \mathcal B\_{D,P}(\chi,\tau) \ll\_{B,C} Q(\log X)^{-C}. } \tag{30}

所以任何由 common profile

χ(n)niτ\chi(n)n^{i\tau}

造成、且

cond⁡χ, ∣τ∣≤(log⁡X)B\operatorname{cond}\chi,\ |\tau| \le(\log X)^B

的 simultaneous line alignment，都被 source cancellation以任意 log強度消掉。

正式：

LOW-PRETENTIOUS-PROFILE45: PASS.\boxed{\texttt{LOW-PRETENTIOUS-PROFILE45:\ PASS}.}

呢個結果亦說明真正缺口不是「可能存在一粒小 Dirichlet character」。任何 surviving inverse obstruction一定係：

high conductor、high line frequency， 或一個不能降成單一 pretentious profile的 distributed overlap。(31)\boxed{ \text{high conductor、high line frequency， 或一個不能降成單一 pretentious profile的 distributed overlap。} } \tag{31}

---

# H. 今輪真正發明出來的 theorem interface

經上述 reductions，剩低的不是普通 Chowla，而係：

## `RANKONE-BEZOUT-AFFINE-ELLIOTT5D45`

對所有 physical dyadic cells，證

∑u∼U, ℓ∼R(u,ℓ)=1ℓA0−uw0=2∑t, k≠0∣t∣,∣t+k∣≪Hμ(A0+ut)μ(A0+u(t+k))×LD,P(A0+ut)LD,P(A0+u(t+k))×b5(w0+ℓt)b5(w0+ℓ(t+k))‾ W≪AQV(log⁡X)−A.(32)\boxed{ \begin{aligned} \sum\_{\substack{ u\sim U,\ \ell\sim R\\\ (u,\ell)=1\\\ \ell A\_0-u w\_0=2}} \sum\_{\substack{ t,\ k\ne0\\\ |t|,|t+k|\ll H}} & \mu(A\_0+ut)\mu(A\_0+u(t+k))\\\ &\times L\_{D,P}(A\_0+ut)L\_{D,P}(A\_0+u(t+k))\\\ &\times b\_5(w\_0+\ell t) \overline{b\_5(w\_0+\ell(t+k))} \\,\mathcal W\\\ &\ll\_A QV(\log X)^{-A}. \end{aligned}} \tag{32}

這張 theorem有四個 load-bearing restrictions：

ℓA0−uw0=2,(33)\ell A\_0-u w\_0=2, \tag{33} (uk,ℓk) 是 rank-one shift pair,(34)(uk,\ell k)\text{ 是 rank-one shift pair}, \tag{34} LD,P 是 actual large-prime selector,(35)L\_{D,P}\text{ 是 actual large-prime selector}, \tag{35} b5=δ1∗⋯∗δ5 必須保持其五重 centering.(36)b\_5=\delta\_1\*\cdots\*\delta\_5 \text{ 必須保持其五重 centering}. \tag{36}

不能推廣成：

- arbitrary bounded bb；
- independent shifts；
- arbitrary β\beta；
- fixed-modulus operator norm。

任何一個推廣都會重新引入 power loss或接近普通 ordinary Chowla。

---

# I. 今輪有冇證明 route「等同普通 Chowla」？

冇。

真正判決係：

BEZOUT-R1⟸̸current Chowla theorems,\boxed{ \texttt{BEZOUT-R1} \not\Longleftarrow \texttt{current Chowla theorems}, }

但同時亦未證：

ordinary fixed-shift Chowla⟸BEZOUT-R1.\texttt{ordinary fixed-shift Chowla} \Longleftarrow \texttt{BEZOUT-R1}.

原因係本題有大量額外 averaging：

u,ℓ,k,u,\ell,k,

固定 resultant 22，以及五重 centered source；但 averaging落在一個 power-thin rank-one shift variety，而非 published averaged-Chowla使用的 complete shift boxes。

所以目前不能合理宣判：

「證這格必然要先證 ordinary Chowla」。\text{「證這格必然要先證 ordinary Chowla」。}

更準確係：

需要一張新的 rank-one/vector-weighted ordinary correlation theorem。\boxed{ \text{需要一張新的 rank-one/vector-weighted ordinary correlation theorem。} }

---

# J. 最接近可行的 proof architecture

現時最合理的 proof不是再 completion，而係一張兩階段 inverse theorem：

large rank-one correlation↓{low profile:χnit, cond⁡χ,∣t∣≤log⁡BX,distributed/high profile\:genuine high-conductor line spectrum.(37)\boxed{ \begin{array}{c} \text{large rank-one correlation}\\\ \downarrow\\\ \begin{cases} \textbf{low profile:}& \chi n^{it},\ \operatorname{cond}\chi,|t|\le\log^B X,\\\ \textbf{distributed/high profile:}& \text{genuine high-conductor line spectrum}. \end{cases} \end{array}} \tag{37}

Low profile已由 `(28)`–`(30)` closed。

真正第一未證 implication是：

∣RR1∣≫QV(log⁡X)−C⟹一個 common low profile或一張 quantitatively controlled high-profile packet.(38)\boxed{ \begin{aligned} &|\mathcal R\_{\mathrm{R1}}| \gg QV(\log X)^{-C}\\\ &\quad\Longrightarrow\\\ &\text{一個 common low profile} \quad\textbf{或}\quad \text{一張 quantitatively controlled high-profile packet}. \end{aligned}} \tag{38}

而 high-profile packet必須帶足夠 entropy／multiplicity penalty，令其總 contribution為

QV(log⁡X)−A.QV(\log X)^{-A}.

這就是目前真正缺少的 **rank-one entropy decrement / vector-valued inverse large sieve**。它不是已有 Guo、Lichtman或KMT theorem的改名版本。

---

# K. Updated strict ledger

```text
PURE5 RAW SOURCE:
PASS / BANKED

PURE5-DP-DOUBLEGCD-BEZOUT-LINE45:
OPEN

BEST SCALE:
Q V log^(C0)

REQUIRED:
Q V log^(-A)

POWER DEFICIT:
NONE

BETA-DP-TO-MU-LARGEPRIME45:
PASS
beta_DP(n) = -mu(n) L_DP(n)

LARGE-PRIME MULTIPLICITY:
<= 2 on the clean entropy-gap cell

RANKONE-SHIFT-BIJECTION45:
PASS
(r,s) = (u*k, ell*k)
k = gcd(r,s)

ACTUAL SHIFT FAMILY SIZE:
U R H = X

INDEPENDENT SHIFT RECTANGLE:
Q V = X H

ALLSHIFT-TO-RANKONE TAX:
H >= X^(5/18)

GUO LOG-CHOWLA DIRECT SPLICE:
FAIL
logarithmic weight / polylog shifts / no source weight

TAO-TERAVAINEN LOG STRUCTURE DIRECT SPLICE:
FAIL
logarithmic correlation architecture

LICHTMAN / MRT ALL-SHIFT DIRECT SPLICE:
FAIL
complete shift averaging and fixed weight class

KMT SHORT-AP DIRECT SPLICE:
FAIL
unweighted residue variance, not vector-valued line overlap

WRIGHT-PARTFIX-MOYK5-45:
POWER NONCLOSING

BEST WRIGHT OUTPUT:
at least Y^(13.5-o(1))

PHYSICAL TARGET:
Y^9

MINIMUM WRIGHT DEFICIT:
Y^(9/2) = X^(1/2)

BLOMER-PASCADI:
GENUINE THEOREM / WRONG PHYSICAL RANGE AND FAMILY

LOW-PRETENTIOUS-PROFILE45:
PASS

SURVIVING PROFILE:
HIGH-CONDUCTOR / HIGH-FREQUENCY / DISTRIBUTED

NEW CANONICAL THEOREM:
RANKONE-BEZOUT-AFFINE-ELLIOTT5D45

PURE5-COMPARISON-MAINTERM-PIN:
OPEN

D2-RAPID-DECAY-PIN:
PASS FOR FIXED SMOOTH PACKETS

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

---

# 最終判決

你嗰句：

We are not cooked; we have reached the actual new theorem.\boxed{\textbf{We are not cooked; we have reached the actual new theorem.}}

今輪 audit後仍然成立，但要加一個更精確版本：

沒有現成 Chowla theorem可直接 splice；沒有 Wright／BP／Yang representation可支付；低 conductor pretentious obstruction已排除；真正未證的是 high-profile rank-one line inverse theorem。\boxed{ \begin{aligned} &\textbf{沒有現成 Chowla theorem可直接 splice；}\\\ &\textbf{沒有 Wright／BP／Yang representation可支付；}\\\ &\textbf{低 conductor pretentious obstruction已排除；}\\\ &\textbf{真正未證的是 high-profile rank-one line inverse theorem。} \end{aligned}}

所以今輪不能合法寫：

BEZOUT-LINE-JOINT-NONALIGNMENT45: PASS.\texttt{BEZOUT-LINE-JOINT-NONALIGNMENT45: PASS}.

最新 honest controlling status係：

GATE1B OPEN — FIRST EXACT RESIDUAL: RANKONE-BEZOUT-AFFINE-ELLIOTT5D45.\boxed{ \texttt{GATE1B OPEN — FIRST EXACT RESIDUAL: RANKONE-BEZOUT-AFFINE-ELLIOTT5D45}. }

這張確實有 standalone publication價值：它是一張 determinant-22 unipotent-orbit上、Möbius-semiprime source與五重 centered prime chaos之間的 ordinary rank-one decorrelation theorem；而且今輪已證明它既不只是普通 Chowla的改名，亦不會被目前任何 fixed-modulus Kloosterman theorem自動涵蓋。