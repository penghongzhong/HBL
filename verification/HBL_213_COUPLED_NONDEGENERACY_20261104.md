# HBL 2.13：完整冻结兼容矩阵的定量非退化

日期：2026-11-04。正式论文环境仍为 **11/13（84.62%）**。

## 当前验收状态

本记录承接 `83711a2964cfb7d335d7c22b2d1e33369361c3d8` 已验收的实际响应、物理迹和完整冻结兼容矩阵。**本轮完整冻结矩阵的定量非退化、真实基构造与唯一实速度消去已严格通过**：代码提交 `18849520cffb37db398aa59c93bc020b5c710b52`，CI `41819072942` 为 `success`。

通过的是下述明确参数区域内的冻结兼容结论，仍未完成真实 PDE 轨道保持、移动配置 Jacobian、残差相对增阶或第 2.13 的有限剖面目标。

## 同一个实际矩阵

仍使用矩锁定的两个真实速度方向

\[
P_b=i(\Lambda V_c-c\partial_cV_c),\qquad P_\omega=V_c,
\]

以及固定规范化 Fredholm 逆对 `rho*eta_L*P` 的响应。强制仿射荷与值、导数迹没有变成新的自由量。接口为 `r0=L/a`，完整列保持

\[
C_b=T_{L/a}(J_b)+\Pi_{[L/a,B]}(a^2P_b(a\cdot)),\qquad
C_\omega=T_{L/a}(J_\omega)+\Pi_{[L/a,B]}(a^2P_\omega(a\cdot)).
\]

正号来自加性校正外区主源 `-a^2 P(a·)`；没有修改既有指定 RHS 的 Green 恒等式。

## 省去不必要的精细渐近

上一分析稿提出 `L^(13/4)` 矩增长及对数尾误差。本轮采用足以服务非退化的较粗估计，以缩短实际组合链。

对 `L>=1, |c|<=1`，由真实两源的紧支撑、全局剖面界和已验半线支撑范数估计，导出同一固定常数 `Cg>=0`，使原源范数、强制荷、修正源范数和完整 Green 一阶矩均不超过

\[
C_g L^4.
\]

这里的一阶矩仍包括势作用于同一 Hilbert 解的部分。证明只用原固定 Fredholm 逆；没有对修正源另选一套解，也没有假定矩已经足够小。

设 `H=(D+1)G`，`C0=1+H B^2`。实际原点规范解满足

\[
|x(r)-r|\le Hr^3,\quad |x'(r)-1|\le Hr^2,
\quad |x(r)/r|\le C_0,\quad |(x/r)'(r)|\le2Hr.
\]

参考积分是实际函数的积分

\[
A=\int_0^B x(r)e^{ir^2/4}\,dr.
\]

由真实 ODE 界证明

\[
|A-B^2/2|\le(H+1/4)B^4/4.
\]

因此在 `(H+1/4)B^2<=1` 时，`|A|>=B^2/4`。该非零性不作为任意参考投影的输入。

## 完整误差与明确区域

令 `M=M_b+M_omega`，`Q=|alpha_b|+|alpha_omega|`，并令 `Msrc` 为已证明的真实源全局接近常数。两列归一化误差都由下式控制：

\[
\begin{aligned}
E={}&\frac{C_0L^2}{a^2}+\frac{2C_0B^2}{L^2}
+C_0M_{\rm src}B^3a|c|\\
&+\frac{C_0M}{a^2}
+\frac{2H(L^3Q+L^2M)}{a^4}.
\end{aligned}
\]

其中第一行来自整个 `[L/a,B]` 上的实际源投影，第二行来自真实内区迹。具体结论是

\[
|C_b/a+iA/2|\le E,\qquad |C_\omega/a-A|\le E.
\]

用 `M,Q<=2 Cg L^4` 和 `a>=L^3`，得到

\[
E\le K_0/L^2+C_0M_{\rm src}B^3a|c|,
\quad K_0=C_0(1+2B^2+2C_g)+8HC_g.
\]

明确选择

\[
L_0=3+32K_0/B^2+1/B,\qquad
\varepsilon=\frac{B^2}{32(C_0M_{\rm src}B^3+1)}.
\]

于是在 `L>=L0, a>=L^3, |c|<=1, a|c|<=epsilon` 时，接口位于 `(0,B]`，且 `E<=B^2/16`。实二维行列式的双线性估计给出

\[
\det_{\mathbb R}(C_b,C_\omega)
\ge a^2|A|^2/16\ge a^2B^4/256>0.
\]

最终区域定理内部取得实际 `Msrc` 和 `Cg`，不保留小总误差、小响应矩、非零参考积分、非零行列式或逆雅可比前提。

对任意冻结的实参数 `mu,theta`，构造终端还直接通过实际原点 IVP 产生 `K : OriginKummerPair mu theta 1`，取

\[
D=1/2+|\mathrm{originZeroCoeff}(\mu,\theta)|,\quad
G=e^{D+1},\quad H=(D+1)G,\quad B=1/[4(H+1)].
\]

原 Gronwall 定理给出真实基界，且该 `B` 满足 `0<B<1` 和所需小区间条件。因此这层终端也不要求用户提供基存在性、系数界或解界。

## 唯一的实速度消去

对同一区域内的实际列，令 `d=det_R(C_b,C_omega)>0`。对每个复兼容残差 `Z`，明确构造

\[
\delta b=\frac{\Re C_\omega\Im Z-\Im C_\omega\Re Z}{d},\qquad
\delta\omega=\frac{\Im C_b\Re Z-\Re C_b\Im Z}{d}.
\]

由实、虚两条方程证明这是唯一满足

\[
Z+\delta b\,C_b+\delta\omega\,C_\omega=0
\]

的实数对。与上一轮精确仿射兼容恒等式合用，取 `Z` 为零速度增量处的实际兼容残差，即给出该冻结映射的唯一消去。构造版终端先生成真实 Kummer 基和参数区域，再完成这个 Cramer 求解；不把非零行列式或校正速度存在作为输入。

## 实际物理区域及尚未关闭的义务

在真实换元 `L=ell^(-1/16), a=sqrt(tau)/ell` 中，`a>=L^3` 对应 `tau>=ell^(13/8)`。真实矩锁定关系给出 `a|c|=kappa_H |m_phys| sqrt(tau)`。本轮的单极小量条件与 `L` 分开，不要求额外的 `a|c|L^2<=1`，也没有为此预设一个极限爆破幂指数。

本轮结论依然是**冻结配置的实际矩阵估计**。以下内容仍未闭合：

1. 实际 PDE 轨道进入并保持上述尺度、辐射矩及参数区域，连同参数变化时所需的统一性。
2. 小外端点 `B` 与主链真正远区匹配的对应；若继续传播到别的端点，必须保留那一段真实源贡献。
3. 基底随 `mu,theta`、尺度和界面变化后的完整参数 Jacobian，或能正确吸收这些变化的迭代机制。
4. 新响应的经典二阶物理方程接口、替换全局内区尾部引起的非局部项、时间项、截断交换子和完整非线性余项。
5. 一个真实非平凡校正步骤相对于旧残差的严格正增阶，然后才可接入有限递推及完整 2.13。

因此，本轮严格验收后仍保持 11/13；最终 II 型轨道及动力学选速仍待构造。

## 严格复验证据

- 代码提交：[18849520cffb37db398aa59c93bc020b5c710b52](https://github.com/penghongzhong/HBL/commit/18849520cffb37db398aa59c93bc020b5c710b52)。
- 严格 CI：[41819072942](https://github.com/penghongzhong/HBL/actions/runs/41819072942)，状态 `completed / success`；job `126537316391`。
- 证据归档：[artifact 13315368952](https://github.com/penghongzhong/HBL/actions/runs/41819072942/artifacts/13315368952)，ZIP SHA-256 `c7decdcc3032d5dcd06bc38654848ca6e779cb47c213cc0025934a69ff734ba3`。
- 工具链沿用 Lean `4.35.0-rc3`，compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`；Mathlib 固定为 `a98628e16c11f5167f16124105ddce53efa9bfe5`。
- 累计 44 条本链公开声明与原 5 条物理源基线声明均完成类型及公理审计。公理只在 `propext`、`Classical.choice`、`Quot.sound` 范围内；没有 `sorryAx`、新增公理或新声明的截断输出。
- 17 份实际证明源码逐一以 `--trust=0 -DwarningAsError=true` 严格重放，17 份日志均为 0 字节；两份 Audit 同样严格执行。
- 成功归档已下载并独立复核：20 份唯一源码的 SHA-256、Git blob、上述不可变代码提交及本地字节全部一致。哈希清单中有一条重复路径，其内容一致，按 20 份唯一源码计。
- 目标及其依赖共完成 4184 个构建任务。该数字不计入论文环境；依赖构建日志仍含历史警告，本轮 17 份目标源码的严格重放全部无警告。

此前失败 run 不作为验收证据。后续说明文档提交不改变上述已验代码，也不冒充新的 Lean 构建。正式论文环境仍为 **11/13（84.62%）**。

核心入口：

- `ActualHartreeMomentLockedResponseMomentGrowth.lean`：真实固定逆的源、荷、修正源和完整矩增长。
- `KummerOriginBasis/ReferenceIntegralLowerBound.lean`：实际原点参考积分下界。
- `ActualHartreeMomentLockedCoupledDeterminantBound.lean`：完整两列误差与实际行列式下界。
- `ActualHartreeMomentLockedNondegenerateRegion.lean`：内部消去误差小与响应矩小前提。
- `ActualHartreeMomentLockedConstructedNondegeneracy.lean`：直接构造实际基、端点和非退化区域。
- `ActualHartreeMomentLockedCoupledCancellation.lean`：实际两列的 Cramer 构造与唯一实速度消去。
