# HBL 2.13：同一实际校正的经典方程与残差接口

日期：2026-11-04。正式论文环境仍为 **11/13（84.62%）**。

## 目标与验收边界

本轮针对用户要求“复用累积 Lean，提高论文定理数”重新核对两项剩余目标。剩余为真实有限剖面 `thm:finite-profile-stage3` 与动力学选速的 II 型主定理。现有 `FiniteProfile.lean` 仍接收 `hstep`，不能仅把已经验收的冻结矩阵消去放入它就验收 2.13。

本轮新实现直接接入同一真实 PDE 校正：固定 Fredholm 输出的经典方程、原源范数控制的非局部截断误差、任意复背景的实际 Hartree 二次余项，以及带时间项和速度交叉项的完整残差恒等式。**上述本轮范围已通过严格 CI 41834168271，证明提交为 `24c01447123be92f3bf9213b7e77c6cee7f0eaf1`；下载归档已独立复核。**

## 同一响应的经典物理方程

记已验收的两个输出为 `q_b,q_omega`，物理响应为 `h_b=q_b/r,h_omega=q_omega/r`。源的连续性由真实剖面的显式公式导出；乘上 `r` 后，原点的商被消去。直接复用 `normalizedMinusOutput_classical` 和 `normalizedPlusOutput_classical`，没有另选一套解。

对 `r>0`，

\[
\begin{aligned}
\Delta_rh_b+3W^4h_b&=-\eta_R Q_c,\\
\Delta_rh_\omega+9W^4h_\omega+4W^3\mathcal I(W^3h_\omega)&=-\eta_R V_c.
\end{aligned}
\]

两阶商函数导数均有证明，实通道中的原 Riesz 行绝对可积。这些是固定泡 Hessian 的实际方程；移动背景的算子差仍须另估计。

## 原源范数控制的真实截断误差

对任意连续 `F` 属于原 `L^{2,7/4}` Fredholm 域，令 `q_+,q_-` 是同一固定规范化逆的输出，`eta_R=1-cutoff(r/R)`。在 `R>=2, 0<r<=R/2` 上，

\[
\begin{aligned}
H_-(\eta_Rq_-)&=F,\\
H_+(\eta_Rq_+)-F&=T((1-\eta_R)q_+),\\
\left|\frac{H_+(\eta_Rq_+)-F}{r}\right|
&\le \frac{C}{R^2}\|F\|_{L^{2,7/4}}W(r)^3.
\end{aligned}
\]

常数 `C` 仅由既有固定 Fredholm 范数常数和真实共振配对决定，独立于 `F,R`。这是实际非局部尾积分导出的相对因子；没有预设响应范数小或给生成项赋予更高阶。

进一步在**同一共轭源空间**令

\[
E_R=\mathbf1_{(0,R/2]}\bigl(H_+(\eta_Rq_+)-F\bigr).
\]

实际证明其加权可积性，并得到

\[
\|E_R\|_{L^{2,7/4}}\le\frac D R\|F\|_{L^{2,7/4}},\qquad
D=C\|W^3\|_{L^{2,7/4}}.
\]

这里 `D` 与源、半径无关。用的是 `<r>^(7/4) W^3=<r>^(-5/4)` 的真实半线 L2 可积性；没有把除以 `r` 的物理误差和共轭源混用。

取原慢半径 `R=ell^(-1/16)`，该界给出真实核心算子的 `ell^(1/16)` 相对因子，旧源范数保留在右端。

该结论控制分离核心。截断环带的空间交换子、时间导数以及 Kummer/远区匹配仍应保留在完整残差中。强制常数物理尾被裸截断时，壳层 Laplacian 误差的共轭加权范数可能产生 `R^(5/4)` 损失；必须使用真实匹配结构，不能将核心 `D/R` 界直接当成全局递推的 `hstep`。

## 任意复背景的原 Hartree 二次余项

设 `P` 为原径向 Hartree 势算子，`C(u)=|u|^2u`，并定义

\[
\begin{aligned}
d(U,h)&=\Re(\overline U h),\\
D\mathcal N(U)h
&=P(|U|^4)\bigl(|U|^2h+2d(U,h)U\bigr)
 +P(4|U|^2d(U,h))|U|^2U,\\
\mathcal R_H(U,h)&=\mathcal N(U+h)-\mathcal N(U)-D\mathcal N(U)h.
\end{aligned}
\]

这里 `D N` 指明确展示的实际一阶展开项。由 quartic 密度与 cubic 乘子的精确多项式展开，以及实际泡势恒等式 `P(W^4)=3W^2`，在

\[
|U(\rho)|\le M W(\rho),\qquad |h(\rho)|\le eW(\rho),\qquad M,e\ge0
\]

下导出所有实际 Riesz 行收敛，并证明

\[
|\mathcal R_H(U,h)(r)|\le63(M+e)^5e^2W(r)^5.
\]

背景允许为复值，扰动不必属于未加权 `L^2`。但未截断的内区物理响应通常带强制常数尾，不能直接套此包络；真实截断或拼接后的 `e` 以及包含全辐射时的 `M` 必须实际估计，不能隐藏其尺度损失。

## 原 PDE 的完整新旧残差关系

令 `R` 为原复径向重整化 Hartree 残差。对于具备实际时间、空间可微性的复背景 `U` 和校正 `H`，精确证明

\[
\begin{aligned}
R(U+H;b+\delta b,\omega+\delta\omega)-R(U;b,\omega)
={}&iH_s+\Delta_rH+D\mathcal N(U)H+i b\Lambda H+\omega H\\
&+i\delta b\Lambda U+\delta\omega U
+i\delta b\Lambda H+\delta\omega H+\mathcal R_H(U,H).
\end{aligned}
\]

时间项、两阶空间导数、真实非局部一阶项和速度交叉项全部保留。上述 bubble 包络进一步给出这条真实残差之差减去明确九项后的二次界。它尚未证明那九项与旧残差整体抵消。

## 仍决定论文计数的义务

1. 同一全局校正的核心、环带和远区源对应，包含被替换内区尾部对原非局部算子的影响。
2. 用真实源范数控制完整线性误差、时间项、背景 Hessian 差和上述二次余项，证明一个实际非平凡步骤在论文共同范数中的相对增阶。
3. 固定合法辐射与一个足够阶数的剖面是可研究的最短修订；其阶数须由实际后向传播估计和参数差分要求确定。现有 `ell^(1/16)` 绝对小量不足以直接达到该门槛。
4. 完成所需有限递推、实际参数控制、Hessian 和远区对应后，才能验收 2.13；随后仍须构造真实轨道并从 PDE 导出速率。

禁止把本轮新公开声明数、构建任务数或未证明的目标降阶计入 12/13。

## 严格证据

- 精确证明提交：[24c01447123be92f3bf9213b7e77c6cee7f0eaf1](https://github.com/penghongzhong/HBL/commit/24c01447123be92f3bf9213b7e77c6cee7f0eaf1)。
- 严格 CI：[41834168271](https://github.com/penghongzhong/HBL/actions/runs/41834168271)，`completed / success`；job `126588693181` 全步骤成功。
- 归档：[13323988046](https://github.com/penghongzhong/HBL/actions/runs/41834168271/artifacts/13323988046)；ZIP SHA-256 `20c4b75f82682c2f99a9cb6a60f164fc3cf9db918fd8268dc235105cda8fbf5b`。
- 工具链 Lean `4.35.0-rc3`，compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`；Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`。
- 本轮新增 13 条公开声明；整链 57 条扩展声明与 5 条基线声明，共 62 条完整类型及公理报告全部通过。62 条均恰依赖 `propext`、`Classical.choice`、`Quot.sound`；无截断或 `sorryAx`。
- 22 份目标证明源码逐一以 `--trust=0 -DwarningAsError=true` 重放，22 份严格日志均为 0 字节；两份 Audit 同样严格执行。
- 下载归档经独立脚本复核及主任务另行核对：25 份唯一源码的 SHA-256、Git blob、精确提交、本地字节全部一致；清单 26 行含既有同内容重复路径，未重复计数。
- 目标与依赖共完成 4216 个构建任务；依赖构建保留 126 条历史警告，目标严格重放无警告。构建数量不计入论文分子。

前两次失败运行 `41832881278`、`41833742971` 不作为验收证据。后续说明文档提交不修改已验 Lean 源码。正式论文环境仍为 **11/13（84.62%）**。
