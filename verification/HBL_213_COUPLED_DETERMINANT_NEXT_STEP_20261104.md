# HBL 2.13：完整冻结兼容矩阵的下一步定量估计

日期：2026-11-04。

**同日后续更新：** [CI 41819072942](https://github.com/penghongzhong/HBL/actions/runs/41819072942) 已严格通过采用 `L^4` 粗响应矩界和无对数尾界的完整冻结矩阵非退化及唯一实速度消去，代码提交为 `18849520cffb37db398aa59c93bc020b5c710b52`。精确范围与证据见 [后续验收记录](HBL_213_COUPLED_NONDEGENERACY_20261104.md)。下文本身仍是较精细候选推导；其 `L^(13/4)`、对数误差和实际动力学应用不能因此自动算作全部已形式化。正式计数不变。

**状态：本文是候选分析推导和下一直接目标账本，尚未完成 Lean 验收。它不宣告完整兼容矩阵已经非退化，也不宣告实际 Hartree 残差获得相对阶提升。正式论文环境仍为 11/13（84.62%）。**

本推导使用真实的两个矩锁定速度源、同一个固定 Fredholm 逆给出的两个内区响应，以及这些响应的实际值和导数。目标是把当前已经组装的完整冻结列，归约到一个有显式误差的参考矩阵。所有内区迹项都保留；“源投影矩阵非退化”不代替完整矩阵非退化。

文中的“冻结”指固定瞬时的 Kummer 基、空间缩放、内区 cutoff 和接口。沿实际轨道改变这些量所产生的导数，以及完整 PDE 拼接余项，不属于下述行列式计算已经解决的内容。

## 1. 物理源、加性校正与符号

记物理泡尺度下的径向变量为 \(\rho>0\)，自相似变量为 \(z>0\)。令

\[
W(\rho)=(1+\rho^2)^{-1/2},\qquad
V_c=\texttt{actualMomentLockedCore}\ c,
\]

\[
Q_c=\Lambda V_c-c\,\partial_cV_c,
\qquad P_b=iQ_c,\qquad P_\omega=V_c.
\]

这里的 \(\partial_cV_c\) 是代码中包含真实移动 cutoff 导数的
`actualMomentLockedAmplitudeTangent`，并非新的可调幅度方向。
`actual_Hartree_core_residual_moment_locked_speed_split` 已证明，在真实幅度律
\(c_s=-bc+m\) 下，原残差中的速度项是

\[
\mathcal R(V_c)=S_c+bP_b+\omega P_\omega.
\tag{1.1}
\]

因此本文的 \(P_b,P_\omega\) 是**正残差源**。

固定内区算子使用

\[
H_-q=-q''-3W^4q,
\qquad
H_+q=-q''-9W^4q-\mathcal Nq.
\tag{1.2}
\]

`monopoleRadial_linearization_eq_hPlus` 已对实际单极内区剖面证明

\[
\Delta_{\mathrm{rad}}(q/\rho)+DN_W(q/\rho)
=-\frac{H_+q}{\rho}.
\tag{1.3}
\]

`monopoleRadialStaticResidual_exact` 更直接把正静态源 \(+cW^3\) 和加性内区校正写为

\[
-\frac{c}{\rho}\bigl(H_+q-\rho W^3\bigr)
+\text{实际非线性余项}.
\tag{1.4}
\]

这确认了内区加性校正消去正源 \(P\) 时，应求解
\(Hq=+\rho P\)。将 (1.3) 推广到本轮的两个规范化响应，还需使用同一径向共轭和真实 Hartree 一阶展开接口；不能把已证的特定剖面结论冒充所有响应的现成定理。

另一方面，冻结 Kummer 算子是

\[
\mathcal L_K u=u''+\left(\frac2z+\frac{iz}{2}\right)u'
+\left(\theta+i\left(\frac14-\mu\right)\right)u.
\tag{1.5}
\]

`actual_Hartree_Kummer_frozen_operator_physical_conjugacy` 已证明，若 \(\rho=az\)、\(a=\sqrt q>0\)，则

\[
\mathcal L_K[f(a\,\cdot)](z)
=a^2\Delta_{\mathrm{rad}}f(az)
+\frac{i az}{2}f'(az)
+\left(\theta+i\left(\frac14-\mu\right)\right)f(az).
\tag{1.6}
\]

它含正 Laplacian。因此，当外区 RHS 表示消去正残差源的**加性校正方程**时，其主源是 \(-a^2P(az)\)。漂移、真实 Hartree 一阶项、时间变化等差额必须保留。例如，从 (1.6) 得到的精确代数接口是

\[
\begin{aligned}
\mathcal L_K[f(a\,\cdot)](z)+a^2P(az)
={}&a^2\bigl(\Delta_{\mathrm{rad}}f+DN_Wf+P\bigr)(az)\\
&+\frac{i az}{2}f'(az)
+\left(\theta+i\left(\frac14-\mu\right)\right)f(az)
-a^2DN_Wf(az).
\end{aligned}
\tag{1.7}
\]

(1.7) 不把最后一行当成零，也不提供它的相对阶估计。

**旧的 \(+F\) Green 传递定理仍然正确。** 它证明的是所指定的方程
\(\mathcal L_Ku=F\) 的传递关系。这里需要做的是在“消去正残差”的物理应用中代入 \(F=-a^2P(a\,\cdot)\)，而不是否定原来给定 RHS 的 ODE 定理。

## 2. 真正的接口与完整源区间

令内区 cutoff 半径为 \(L>2\)，并设

\[
\eta_L(\rho)=1-\operatorname{cutoff}(\rho/L),
\qquad r_0=\frac{L}{a},\qquad 0<r_0<B.
\tag{2.1}
\]

在正半轴上，\(\eta_L=1\) 于 \([0,L]\)，\(\eta_L=0\) 于 \([2L,\infty)\)，且 \(0\le\eta_L\le1\)。内区两个真实半直线源是

\[
F_b(\rho)=\rho\eta_L(\rho)Q_c(\rho),
\qquad F_\omega(\rho)=\rho\eta_L(\rho)V_c(\rho).
\tag{2.2}
\]

外区速度源则使用未乘内区补 cutoff 的实际方向：

\[
\widehat P_b(z)=a^2P_b(az),
\qquad \widehat P_\omega(z)=a^2P_\omega(az),
\qquad z\in[r_0,B].
\tag{2.3}
\]

选择左端点 \(r_0=L/a\) 的作用是让整个传递区间从真实内接口开始。若内区 cutoff 已在 \(2L\) 结束，而仍只对固定 \([R,2R]\) 积分且 \(2L<aR\)，则 \((2L,aR)\) 中的实际源没有被处理。以 \(c=0\) 为例，\(P_\omega=W>0\)，该区间的源不会自动消失。

把区间改为 \([L/a,B]\) 消除了这个几何遗漏。它本身不证明完整 Hartree 拼接：用外区剖面替换内区响应的全局尾部，会改变非局部 Hartree 项；若采用 cutoff 拼接，还会出现真实交换子。这些必须进入后续的 PDE 余项估计。

## 3. 原点规范基及全部常数

### 3.1 基函数与 Wronskian

固定实际参数 \((\mu,\theta)\)，取代码中的原点规范基
\(K=\texttt{OriginKummerPair}\)。写

\[
x(z)=K.x(z),\qquad x'(z)=K.dx(z),
\qquad x(0)=0,\quad x'(0)=1.
\]

它满足

\[
x''+\frac{iz}{2}x'
+\left(\theta-i\left(\mu+\frac14\right)\right)x=0.
\tag{3.1}
\]

定义物理正则解

\[
k(z)=\frac{x(z)}z,
\qquad k'(z)=\frac{x'(z)}z-\frac{x(z)}{z^2}.
\tag{3.2}
\]

另一个原点解记为 \(y\)，满足 \(y(0)=1,y'(0)=0\)。为避免与泡 \(W\) 混淆，把物理基 Wronskian 记作

\[
\mathcal W_K(z)=\frac{y(z)}z\,k'(z)
-\left(\frac{y(z)}z\right)'k(z).
\]

已有 `originGreenWronskian_exact` 给出

\[
\mathcal W_K(z)=z^{-2}e^{-iz^2/4},
\qquad
\mathcal W_K(z)^{-1}=z^2e^{iz^2/4}.
\tag{3.3}
\]

于是实际源投影和出射迹为

\[
\Pi_K[F;r_0,B]
=\int_{r_0}^{B}k(z)z^2e^{iz^2/4}F(z)\,dz,
\tag{3.4}
\]

\[
\mathcal T_{K,r_0}(U,DU)
=r_0^2e^{ir_0^2/4}\bigl(Uk'(r_0)-DUk(r_0)\bigr).
\tag{3.5}
\]

这里 \(DU\) 是对 \(z\) 的导数。`actual_origin_outgoing_flux_hasDerivAt` 的符号是

\[
\frac{d}{dz}\mathcal T_{K,z}(u,u')
=-\frac{k(z)\mathcal L_Ku(z)}{\mathcal W_K(z)}.
\tag{3.6}
\]

所以 RHS 为 \(-\widehat P\) 时，兼容列是“内迹加正源投影”。

### 3.2 \(D,G,H,C_0\) 必须来自同一原点 IVP

先固定一个正的原点基区间上界 \(\bar B\)，以及预期实际参数所在的紧集
\(\mathcal P\subset\mathbb R^2\)。在 \([0,\bar B]\) 上选取一个固定 \(D\ge0\)，使

\[
\left|\frac{iz}{2}\right|
+\left|\theta-i\left(\mu+\frac14\right)\right|\le D
\quad ((\mu,\theta)\in\mathcal P).
\]

例如可取
\(D=\bar B/2+\sup_{\mathcal P}|\theta-i(\mu+1/4)|\)。然后令

\[
G=e^{(D+1)\bar B},\qquad H=(D+1)G.
\tag{3.7}
\]

`origin_kummer_pair_bound` 由真实 ODE 的 Grönwall 估计给出四个分量的 \(G\) 界。
`origin_kummer_asymptotic_bound` 的证明内已经导出

\[
|x(z)-z|\le Hz^3,\qquad |x'(z)-1|\le Hz^2.
\tag{3.8}
\]

其中导数估计当前是该证明中的局部步骤，尚需提取为本次组合可调用的结论；不能只引用其最终的值估计就声称已有导数估计接口。

对 \(0<z\le B\le\bar B\)，定义

\[
C_0=1+HB^2.
\tag{3.9}
\]

(3.8) 随即给出

\[
|k(z)|\le C_0,
\qquad |k'(z)|\le 2Hz,
\qquad |x(z)|\le C_0z.
\tag{3.10}
\]

这套常数在 \(r_0\downarrow0\) 时保持固定。不能直接使用同时控制奇异基 \(y/z\) 的一般正环带常数代替 \(C_0,H\)：该常数会随左端点趋零而变坏。

`exists_compact_origin_kummer_basis` 已使用同一个原点 IVP、同一紧参数集和上述形式的常数构造基。实际轨道留在该紧集仍须由动力学证明，不能从基存在性推出。

## 4. 参考积分 \(A\) 的实际非零估计

定义

\[
A=A_K(B):=\int_0^B x(z)e^{iz^2/4}\,dz.
\tag{4.1}
\]

选择固定的 \(B>0\)，满足

\[
B\le\min(\bar B,1),
\qquad (H+\tfrac14)B^2\le1.
\tag{4.2}
\]

因为 \(|e^{it}-1|\le |t|\) 且 \(|e^{it}|=1\)，(3.8) 给出

\[
\begin{aligned}
|x(z)e^{iz^2/4}-z|
&\le |x(z)-z|+z|e^{iz^2/4}-1|\\
&\le (H+\tfrac14)z^3.
\end{aligned}
\]

积分后得到

\[
\left|A-\frac{B^2}{2}\right|
\le\frac{H+1/4}{4}B^4
\le\frac{B^2}{4},
\qquad |A|\ge\frac{B^2}{4}>0.
\tag{4.3}
\]

这是从实际原点规范化和 ODE 导出的非零界，没有引入“任意 \(K,R\) 的投影都非零”的假设。该论证允许在紧参数集上预先选取同一个小 \(B\)。若主链的外端点由别的匹配约束固定，就必须证明允许选用这样的 \(B\)，或另行控制继续传播至真正外端点的源贡献；不能用小 \(B\) 的矩阵替换一个不同的物理矩阵。

一个可直接核对的附加恒等式是

\[
\left(x'(z)e^{iz^2/4}\right)'
=-\left(\theta-i\left(\mu+\frac14\right)\right)
 x(z)e^{iz^2/4}.
\]

因此

\[
\left(\theta-i\left(\mu+\frac14\right)\right)A
=1-x'(B)e^{iB^2/4}.
\tag{4.4}
\]

(4.4) 是具体 ODE 的精确积分归约，不需要特殊函数表。正性证明使用的是 (4.3)，并未把 (4.4) 的右侧非零作为前提。

## 5. 真实内区响应、荷与矩

对 (2.2) 的两个源，使用本轮选定的同一个固定 Fredholm 逆及其核补规范化：

\[
q_b=\texttt{normalizedMinusOutput}(F_b),
\qquad q_\omega=\texttt{normalizedPlusOutput}(F_\omega).
\]

物理实响应为

\[
u_b(\rho)=q_b(\rho)/\rho,
\qquad u_\omega(\rho)=q_\omega(\rho)/\rho.
\tag{5.1}
\]

实际复方向是 \(iu_b\) 和 \(u_\omega\)，不是任意给定的边界 jets。其唯一强制的仿射荷为

\[
\alpha_b=\texttt{actualMinusCharge}(F_b),
\qquad \alpha_\omega=\texttt{actualPlusCharge}(F_\omega).
\tag{5.2}
\]

为定义实际矩常数，写 \(x_-\)、\(x_+\) 为相应规范化的 Hilbert 核补解，并令

\[
\begin{aligned}
F_b^{\rm corr}&=F_b-\alpha_b H_-\mathrm{model},&g_b&=3x_-,\\
F_\omega^{\rm corr}&=F_\omega-\alpha_\omega H_+\mathrm{model},&
g_\omega&=\texttt{weightedPotentialOperator}(x_+).
\end{aligned}
\]

定义

\[
M_b=\texttt{innerGreenBound}(g_b,F_b^{\rm corr}),
\qquad M_\omega=\texttt{innerGreenBound}(g_\omega,F_\omega^{\rm corr}),
\tag{5.3}
\]

\[
M_*:=\max(M_b,M_\omega),
\qquad \alpha_*:=\max(|\alpha_b|,|\alpha_\omega|).
\tag{5.4}
\]

这里 \(M_j\) 包含重构源的势作用部分和经过仿射荷修正的源，不是仅对外部 \(F_j\) 积分所得的替代常数。

已有 `innerGreenRepresentative_affine_physical_trace_bounds` 对 \(L>2\) 给出

\[
|u_j(L)-\alpha_j|\le\frac{M_j}{L},
\qquad |u_j'(L)|\le\frac{M_j}{L^2},
\quad j\in\{b,\omega\}.
\tag{5.5}
\]

需要把该定理明确实例化到本轮规范化输出和 (5.3)，才能在 Lean 中使用下述完整列估计。

内接口处的复 jets 为

\[
J_b=(iu_b(L),\,ia u_b'(L)),
\qquad J_\omega=(u_\omega(L),\,a u_\omega'(L)).
\tag{5.6}
\]

第二分量中的 \(a\) 来自真实链式法则，不能省略。

正确消去符号下的两列是

\[
C_b=\mathcal T_{K,r_0}(J_b)+\Pi_K[\widehat P_b;r_0,B],
\qquad
C_\omega=\mathcal T_{K,r_0}(J_\omega)+\Pi_K[\widehat P_\omega;r_0,B].
\tag{5.7}
\]

这是 `actualMomentLockedCoupledColumns` 所表示的完整冻结矩阵。

## 6. 误差第一部分：未扰动泡的源投影

在 \(c=0\) 时，已有源识别给出

\[
P_\omega=W,\qquad P_b=i\Lambda W,
\qquad \Lambda W=-\frac12W+W^3.
\tag{6.1}
\]

对 \(t>0\)，可直接计算

\[
0\le1-tW(t)\le\frac1{2t^2},
\tag{6.2}
\]

\[
\left|t\Lambda W(t)+\frac12\right|
\le\frac1{4t^2}+\frac1{t^2}
=\frac5{4t^2}.
\tag{6.3}
\]

例如 (6.2) 来自
\(1-t/\sqrt{1+t^2}=1/[\sqrt{1+t^2}(\sqrt{1+t^2}+t)]\)。

利用 (3.4)，归一化的相位源投影为

\[
\frac1a\Pi_K[a^2W(a\,\cdot);r_0,B]
=\int_{r_0}^B x(z)e^{iz^2/4}\,[azW(az)]\,dz.
\]

它与 \(A\) 的差分成两个真实项：

1. 丢掉的参考小区间 \([0,r_0]\) 的积分；
2. \([r_0,B]\) 上泡尾与 \(1/\rho\) 的差。

由 (3.10)、(6.2)，分别得到

\[
\left|\int_0^{r_0}x(z)e^{iz^2/4}\,dz\right|
\le\frac{C_0r_0^2}{2},
\]

\[
\int_{r_0}^B C_0z\frac1{2a^2z^2}\,dz
=\frac{C_0}{2a^2}\log\frac{B}{r_0}.
\]

所以

\[
\left|\frac1a\Pi_K[\widehat P_\omega|_{c=0};r_0,B]-A\right|
\le\frac{C_0L^2}{2a^2}
+\frac{C_0}{2a^2}\log\frac{aB}{L}.
\tag{6.4}
\]

同理，尺度列使用 (6.3)，参考值为 \(-iA/2\)，并满足

\[
\left|\frac1a\Pi_K[\widehat P_b|_{c=0};r_0,B]+\frac{iA}{2}\right|
\le\frac{C_0L^2}{4a^2}
+\frac{5C_0}{4a^2}\log\frac{aB}{L}.
\tag{6.5}
\]

由于 \(aB/L>1\)，对数非负。两列可以统一用

\[
E_{\rm bubble}
:=\frac{C_0L^2}{2a^2}
+\frac{5C_0}{4a^2}\log\frac{aB}{L}
\tag{6.6}
\]

控制。这里确实使用了 \([L/a,B]\) 的全区间，而非固定环带估计的形式替换。

## 7. 误差第二部分：真实矩锁定源的 \(c\) 扰动

令 \(M_{\rm src}>0\) 是已有
`actual_Hartree_moment_locked_speed_profiles_uniform_close`
在选择 \(c,\rho\) 之前给出的固定常数，使

\[
|Q_c(\rho)-\Lambda W(\rho)|\le M_{\rm src}|c|,
\qquad |V_c(\rho)-W(\rho)|\le M_{\rm src}|c|.
\tag{7.1}
\]

它在整个正半轴成立，包括移动 cutoff 的过渡区。对每一列，除以 \(a\) 后的源差不超过 \(aM_{\rm src}|c|\)。因此

\[
\begin{aligned}
\frac1a\left|\Pi_K[\widehat P_j(c)-\widehat P_j(0);r_0,B]\right|
&\le C_0aM_{\rm src}|c|\int_{r_0}^Bz^2\,dz\\
&\le\frac{C_0M_{\rm src}B^3}{3}\,a|c|.
\end{aligned}
\tag{7.2}
\]

记右端为 \(E_c\)。这里实际需要的小量是 \(a|c|\)，不是仅有 \(|c|\to0\)。

## 8. 误差第三部分：真实内区迹

对两列，乘上 \(i\) 不改变模。由 (3.5)、(3.10)、(5.5)、(5.6)，有

\[
\begin{aligned}
\frac1a\left|\mathcal T_{K,r_0}(J_j)\right|
&\le\frac{r_0^2}{a}
\left[2Hr_0\left(|\alpha_j|+\frac{M_j}{L}\right)
+aC_0\frac{M_j}{L^2}\right]\\
&=2H\frac{L^3|\alpha_j|+L^2M_j}{a^4}
+\frac{C_0M_j}{a^2}.
\end{aligned}
\tag{8.1}
\]

故统一迹误差为

\[
E_{\rm trace}
:=\frac{C_0M_*}{a^2}
+2H\frac{L^3\alpha_*+L^2M_*}{a^4}.
\tag{8.2}
\]

这一步是源投影矩阵和完整兼容矩阵之间不可省略的区别。\(M_*\) 和 \(\alpha_*\) 均由实际响应决定，没有允许自由选择内区 jets 或仿射荷。

## 9. 全部误差及行列式下界

定义

\[
\boxed{
\begin{aligned}
E={}&\frac{C_0L^2}{2a^2}
+\frac{5C_0}{4a^2}\log\frac{aB}{L}
+\frac{C_0M_{\rm src}B^3}{3}\,a|c|\\
&+\frac{C_0M_*}{a^2}
+2H\frac{L^3\alpha_*+L^2M_*}{a^4}.
\end{aligned}}
\tag{9.1}
\]

(6.4)—(8.2) 给出的候选完整列结论是

\[
\left|\frac{C_b}{a}+\frac{iA}{2}\right|\le E,
\qquad
\left|\frac{C_\omega}{a}-A\right|\le E.
\tag{9.2}
\]

对复数列定义真实二维行列式

\[
\det_{\mathbb R}(v,w)
=\Re v\,\Im w-\Re w\,\Im v
=\Im(\overline v w).
\tag{9.3}
\]

参考两列的行列式为

\[
\det_{\mathbb R}(-iA/2,A)=\frac{|A|^2}{2}.
\tag{9.4}
\]

令 \(e_b=C_b/a+iA/2\)、\(e_\omega=C_\omega/a-A\)。双线性和
\(|\det_{\mathbb R}(v,w)|\le|v||w|\) 给出

\[
\frac1{a^2}\det_{\mathbb R}(C_b,C_\omega)
\ge\frac{|A|^2}{2}-\frac32|A|E-E^2.
\tag{9.5}
\]

因此，下面是一条具体、可核对的充分条件：

\[
E\le\frac{B^2}{16}.
\tag{9.6}
\]

结合 (4.3)，它意味着 \(E\le|A|/4\)，从而

\[
\boxed{
\det_{\mathbb R}(C_b,C_\omega)
\ge\frac{a^2|A|^2}{16}
\ge\frac{a^2B^4}{256}>0.}
\tag{9.7}
\]

这里的 \(1/16\) 来自
\(1/2-(3/2)(1/4)-(1/4)^2=1/16\)。列的顺序是尺度列、相位列；交换列会改变行列式符号。

**(9.6) 不是可以直接加入主定理的“已解非退化”假设。** 下一任务是从实际响应和实际物理区间证明 (9.1) 的各项具有所需小量，再将这些估计形式化。固定 \(L>2,c=0\) 时，实际响应和 \(M_*,\alpha_*\) 固定，\(a\to\infty\) 确实使 \(E\to0\)；这是一条有数学内容的基准命题，但它不能代替主链的移动 \(L\) 估计。

## 10. 所需响应矩增长可以怎样从固定逆取得

本节给出不依赖额外精细 \(1/\rho\) 尾估计的粗界。它们的成分已有，以下针对当前源的组合尚未 Lean 验收。

固定 \(c_0\ge0\)，在 \(|c|\le c_0\) 上令

\[
M_0=1+M_{\rm src}c_0.
\]

由 \(|W|\le1\)、\(|\Lambda W|\le1/2\) 和 (7.1)，两实剖面均满足 \(|Q_c|,|V_c|\le M_0\)。于是对 \(j=b,\omega\)，

\[
|F_j(\rho)|\le M_0\rho\,\mathbf 1_{[0,2L]}(\rho)
\quad(\rho>0).
\tag{10.1}
\]

设 \(\sigma=7/4\)，采用仓库已有的半直线权范数

\[
\|F\|_{L^{2,7/4}}^2
=\int_0^\infty(1+\rho^2)^{7/4}|F(\rho)|^2\,d\rho.
\]

对 \(L\ge1\)，有

\[
\begin{aligned}
\|F_j\|_{L^{2,7/4}}^2
&\le M_0^2(1+4L^2)^{7/4}\int_0^{2L}\rho^2\,d\rho\\
&\le M_0^2\frac83\,5^{7/4}L^{13/2}.
\end{aligned}
\]

所以

\[
\|F_j\|_{L^{2,7/4}}
\le C_NM_0L^{13/4},\qquad
C_N=\sqrt{8/3}\,5^{7/8}.
\tag{10.2}
\]

真实荷公式为

\[
\alpha_j=-\frac{\int_0^\infty\psi_j(\rho)F_j(\rho)\,d\rho}
{\psi_j(\infty)},
\quad \psi_-(\infty)=1,\quad\psi_+(\infty)=-\frac12.
\]

仅使用已有统一界 `channelResonance_abs_le_one`，安全地得到

\[
|\alpha_b|\le2M_0L^2,\qquad
|\alpha_\omega|\le4M_0L^2,
\qquad \alpha_*\le4M_0L^2.
\tag{10.3}
\]

此处不为改进常数另开辅助链。

令

\[
N_{\rm aff}=\max\bigl(
\|H_+\mathrm{model}\|_{L^{2,7/4}},
\|H_-\mathrm{model}\|_{L^{2,7/4}}\bigr).
\]

这两个固定仿射源属于现有权空间。由 (10.2)、(10.3) 及 \(L^2\le L^{13/4}\)，

\[
\|F_j^{\rm corr}\|_{L^{2,7/4}}
\le M_0(C_N+4N_{\rm aff})L^{13/4}.
\tag{10.4}
\]

已有 `actual_inner_fixed_Fredholm_moment_constants` 从两个实际固定 Fredholm 算子导出 \(D_+,D_-\ge0\)，而非把逆范数作为新前提。令 \(D_*:=\max(D_+,D_-)\)，将它实例化到经过荷修正的源即可得到候选组合界

\[
M_*\le C_ML^{13/4},
\qquad C_M=D_*M_0(C_N+4N_{\rm aff}).
\tag{10.5}
\]

需要完成的是本轮实际源的 (10.2)、荷的 (10.3)、修正源的 (10.4) 及固定逆估计的正确实例化。仅有“源属于权空间”尚不足以得到这些关于移动 \(L\) 的定量界。

## 11. 真实物理尺度的小量，不预设极限速率

主链已指定

\[
\ell=\lambda^{-1}>0,\qquad \tau=T-t>0,
\qquad q=\frac{\tau}{\ell^2},\qquad a=\frac{\sqrt\tau}{\ell},
\qquad L=L_{\rm slow}=\ell^{-1/16}.
\tag{11.1}
\]

真实 Kummer 左端点因此是

\[
r_0=\frac La=\frac{\ell^{15/16}}{\sqrt\tau}.
\tag{11.2}
\]

它通常趋于零，不能无证据地等同于一个预先固定的正环带半径。

把 (10.3)、(10.5) 代入 (9.1) 后，控制迹误差的主要物理量为

\[
\boxed{\delta:=\frac{L^{13/4}}{a^2}
=\frac{\ell^{115/64}}{\tau}.}
\tag{11.3}
\]

对 \(L\ge1\)，有精确代数关系

\[
\frac{L^2}{a^2}=\delta L^{-5/4},
\qquad
\frac{L^5}{a^4}=\delta^2L^{-3/2},
\qquad
\frac{L^{21/4}}{a^4}=\delta^2L^{-5/4}.
\tag{11.4}
\]

因此 \(\delta\to0\) 会使内迹各项及缺少小参考区间的项趋零，并且推出 \(L/a\to0\) 与 \(a\to\infty\)。当最终 \(L/a<B\le1\)、\(L\ge1\) 时，对数项满足

\[
0\le\frac1{a^2}\log\frac{aB}{L}
\le\frac{\log a}{a^2}\longrightarrow0.
\tag{11.5}
\]

真实单极幅度来自物理辐射矩：

\[
c=\kappa_H\ell\,m_{\rm phys},\qquad \kappa_H=3/\pi^2>0.
\]

从而

\[
\boxed{a|c|=\kappa_H|m_{\rm phys}|\sqrt\tau.}
\tag{11.6}
\]

若实际辐射矩保持有界且 \(\tau\downarrow0\)，(11.6) 给出 (7.2) 所需的小量。这是物理关系，未指定 \(\ell\) 的极限幂律。

### 11.1 怎样从真实动力学窗口证明 \(\delta\to0\)

已有物理变量的精确运动学关系是

\[
q_s=4\mu,\qquad
\frac{d\log\ell}{d\log\tau}=bq=\frac12+2\mu.
\tag{11.7}
\]

如果后续实际 PDE 的 bootstrap 证明
\(\mu(s)\ge\mu_{\min}>9/16\)，记
\(\nu_{\min}=1/2+2\mu_{\min}>13/8\)，则

\[
\frac d{ds}\bigl(\log\ell-\nu_{\min}\log\tau\bigr)
=-\frac{bq-\nu_{\min}}q\le0.
\]

所以从初始 \(\ell_0,\tau_0\) 得到

\[
\ell\le\ell_0(\tau/\tau_0)^{\nu_{\min}},
\]

\[
\delta\le
\ell_0^{115/64}\tau_0^{-115\nu_{\min}/64}
\tau^{115\nu_{\min}/64-1}\longrightarrow0.
\tag{11.8}
\]

这里 \(115\nu_{\min}/64-1>0\)。使用的是一个应由实际调制动力学保持的窗口，并非预先指定 \(\mu_\infty\) 或最终爆破速率。**当前并未证明该实际 trapping，不能把 (11.8) 当成已验收结果。**

相应地，\(\theta=q\omega\) 所在的紧参数窗口也必须实际建立，才能沿轨道统一使用第 3 节的基常数。

## 12. 与完整 PDE 主链之间仍须保留的边界

1. **冻结完整矩阵与移动配置 Jacobian。** 本文矩阵同时包括真实内迹和外区源投影，但在求其速度响应时冻结 \(K,a,L,r_0,B,c\)。实际参数满足 \(\mu=(2bq-1)/4\)、\(\theta=q\omega\)。固定 \(q\) 下，\(\partial_b\mu=q/2\)、\(\partial_\omega\theta=q\)。若求真实参数映射的 Jacobian，就必须加入基、迹泛函及端点等变化项。它们不会由 (9.7) 自动变小；若采用逐步冻结求解，也需把配置变化产生的项纳入下一残差并证明相对增益。

2. **外端点与继续传播。** (4.2) 是本文非零估计的具体可验证条件。要在主链使用，必须确认外端点可以这样选择。若实际外匹配在 \(B_{\rm out}>B\)，则应处理 \([B,B_{\rm out}]\) 的真实源及其传递贡献，不能把它丢掉。

3. **完整 Hartree 残差。** (1.7) 保留的差额、拼接后的非局部尾、局部 cutoff 交换子、移动内源及时间导数，都还需要用实际范数证明。行列式正性只解决有限维可解性的一部分；它不意味着这些项已具有更高相对阶。

4. **有限递推。** 只有在每次校正的真实残差估计闭合以后，才能实例化现有有限递推框架。不能通过改写 order 标签或添加“残差已提升”的输入完成此步。

因此，这份推导不增加正式论文环境计数。

## 13. 下一直接形式化目标及已有证据

| 直接目标 | 已有基础 | 尚待完成的具体组合 |
|---|---|---|
| 正则 Kummer 值与导数的统一小原点界 | `origin_kummer_pair_bound`；`origin_kummer_asymptotic_bound`；`exists_compact_origin_kummer_basis` | 提取 (3.8) 的导数步骤，推出 (3.10)，保留参数紧集和固定基区间 |
| 实际参考积分非零 | 原点初值、真实 ODE、精确 Wronskian | 证明 (4.3)，不能用抽象 `A ≠ 0` 输入代替 |
| 两真实源投影的完整区间估计 | 实际矩锁定源识别、全局 \(O(|c|)\) 界、区间可积性 | 证明 (6.4)、(6.5)、(7.2)，包括移动左端点 |
| 真实响应的移动半径矩界 | 固定规范化逆、强制荷、实际 Green 一阶矩界 | 实例化 (5.5)，证明 (10.2)—(10.5)，推出 (8.2) |
| 完整冻结矩阵非退化 | 本轮完整列和精确 affine response | 由上面实际估计推出 (9.2)，再完成 (9.5)—(9.7)；证明 (9.6) 在允许的物理区间成立 |
| 主链实际可用性 | 精确运动学和真实矩锁定关系 | 建立参数窗口、\(\delta\) 小量、允许的外端点及全部残差相对阶估计 |

关键仓库依据如下；这些定位指向实际已存在的定义/定理，不表示本文的新组合已通过检查。

- [ActualHartreeMomentLockedSpeed.lean](../HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedSpeed.lean)：真实残差拆分、cutoff 导数抵消、两方向全局接近泡、\(c=0\) 识别。
- [ActualHartreeMomentLockedInnerResponse.lean](../HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedInnerResponse.lean)、[ActualHartreeMomentLockedCoupledCompatibility.lean](../HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedCoupledCompatibility.lean)：本轮实际源的固定逆响应、真实物理 jets 与完整冻结兼容列。
- [MonopoleRadialLinearization.lean](../HBL/MonopoleRadialLinearization.lean)：`radialLaplacian_div_radius` 与真实单极剖面的负 \(H_+\) 共轭。
- [MonopoleStaticRadialBound.lean](../HBL/MonopoleStaticRadialBound.lean)：`monopoleRadialStaticResidual_exact` 的真实消去符号。
- [ActualHartreeKummerOperatorConjugacy.lean](../HBL/TypeIIDynamicSelection/ActualHartreeKummerOperatorConjugacy.lean)：冻结 Kummer 算子的精确物理拉回，不包含完整时间依赖 PDE 的等同声明。
- [KummerOriginBasis/UniformBound.lean](../HBL/KummerOriginBasis/UniformBound.lean)、[AsymptoticBound.lean](../HBL/KummerOriginBasis/AsymptoticBound.lean)、[CompactBasis.lean](../HBL/KummerOriginBasis/CompactBasis.lean)：实际原点 IVP 的统一界及局部渐近。
- [KummerOriginGreen/GreenBridge.lean](../HBL/KummerOriginGreen/GreenBridge.lean)、[ActualKummerTransmissionProjection.lean](../HBL/TypeIIDynamicSelection/ActualKummerTransmissionProjection.lean)：真实 Wronskian、投影与出射通量恒等式。
- [RepresentativeFirstMomentTrace.lean](../HBL/InnerReconstruction/RepresentativeFirstMomentTrace.lean)、[UniformMomentOperatorBound.lean](../HBL/InnerReconstruction/UniformMomentOperatorBound.lean)：实际重构源的迹界与固定 Fredholm 矩常数。
- [ActualInnerAffinelyCorrected.lean](../HBL/ActualInnerAffinelyCorrected.lean)、[AffineTailLemmaClosed.lean](../HBL/AffineTailLemmaClosed.lean)：强制荷、修正源、真实阈值常数及统一共振界。
- [ActualHartreeConjugatedLocalizedInner.lean](../HBL/TypeIIDynamicSelection/ActualHartreeConjugatedLocalizedInner.lean)：实际内区 cutoff 与 \(L_{\rm slow}=\ell^{-1/16}\)。
- [ActualRadiationScaling.lean](../HBL/TypeIIDynamicSelection/ActualRadiationScaling.lean)、[ActualRadiationMomentDynamics.lean](../HBL/TypeIIDynamicSelection/ActualRadiationMomentDynamics.lean)：真实辐射中心的缩放、\(c=\kappa_H\ell m_{\rm phys}\) 及其时间导数。
- [typeii-minimal-revised-main-20261029.md](typeii-minimal-revised-main-20261029.md)：运动学变量、应由实际 PDE 导出的调制窗口和动态速率目标。

**验收边界：当前为 11/13。本文把下一承重估计具体化为实际常数、真实响应矩和物理尺度比值；完成本文的形式化与实际动力学/残差接口之前，不更新论文环境计数。**
