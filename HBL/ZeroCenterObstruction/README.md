# 零模—中心分裂：撤回环境恢复审查

2026-10-29，源码基准 `f911703888f397f7904570dcf5b2528a7d2c0240`。

本轮找回八个撤回环境的历史原陈述，严格核验一个诊断反例。新增原文环境验收为 **0**，当前严格账本仍为 **9/21**（八项重新验收、一项此前新闭合、四项待证、八项撤回待修复）。本反例不否定具体 Hartree 谱分裂，也不否定主 PDE 定理。

## 已核验的数学结论

令 $x=(h,z,c)\in\mathbb R^2\times\mathbb R^2\times\mathbb R^2$，使用普通欧氏配对。定义

$$
J(h,z,c)=((h_2,-h_1),c,-z),\qquad
L(h,z,c)=((-h_1,h_2),0,c),
$$
$$
A=JL,\qquad A(h,z,c)=((h_2,h_1),c,0).
$$

Lean 已证明 $J^*=-J$、$J^2=-I$、$L^*=L$，以及

$$
\langle Lx,x\rangle=-h_1^2+h_2^2+c_1^2+c_2^2,
\quad A((1,\pm1),0,0)=\pm((1,\pm1),0,0),
\quad \ker A=\{(0,z,0)\}.
$$

参考中心 $C_{\rm ref}=\{(0,0,c)\}$ 上二次型为 $c_1^2+c_2^2$，且大于等于 Lean 中乘积范数的平方。然而，对于任意线性映射 $\ell:\mathbb R^2\to\mathbb R^2$，图 $\{(0,\ell c,c)\}$ 均不被 $A$ 保持：其像为 $(0,c,0)$，若仍在图上，最后一个坐标迫使图参数为零，从而 $c=0$，与任取非零 $c$ 矛盾。

更强地，不存在值域落在 $\ker A$、在 $\ker A$ 上为恒等且与 $A$ 交换的连续线性映射 $P$。取 $u=(0,0,(1,0))$，则 $Au=(0,(1,0),0)\ne0$；一方面 $PAu=Au$，另一方面 $APu=0$，矛盾。

因此，“有一个双曲对、两个零模、参考中心二次型强制性”不足以推出精确不变的零模—中心分裂。上述终端直接核验明确的特征向量与二次型公式，没有另行宣称完成抽象 Morse 指数或完整谱分类定理。

## 历史原文与恢复条件

原文见 `HBL_v32_WeightedFredholmCompact_20261017.tex` 的历史版本 35，修改时间为 `2026-10-20T01:06:59.116229Z`。这是历史陈述见证，不是当前修复稿。完整八项陈述、行号及引用保存在 `verification/withdrawn-environment-recovery-20261029.json`。

| 原环境 | 历史行号 | 恢复验收仍需的具体工作 |
|---|---:|---|
| old-3.1 `thm:form-splitting-stage5` | 3655–3685 | 实际 Hamilton 定义域、双曲坐标，以及两个物理空间上有界的左图；或证明并明确登记有效的保留耦合替代陈述 |
| old-3.2 `thm:slow-Feshbach-stage3` | 4069–4096 | 对实际慢变算子的有效坐标构造及参数导数估计；不能从静态强制性直接推出零模—中心 Sylvester 逆 |
| old-3.3 `lem:Esl-pointwise-v2` | 4193–4202 | 将真实有限背景、有效标架及两条路径的估计代入连接公式 |
| old-3.4 `thm:full-slow-modulation-v2` | 4278–4307 | 实际调制坐标、反馈项辨识及右端时间衰减估计 |
| old-4.1 `prop:single-green-stage4` | 4430–4440 | 实际受约束演化、源与定义域控制、后向求解及稳定齐次传播 |
| old-4.2 `prop:lossy-green-stage4` | 5176–5198 | 两个真实背景间的传播比较、状态/源纤维运输及导数损失 |
| old-5.2 `thm:joint-contraction-stage4` | 5681–5705 | 真实联合非线性映射的自映与压缩，包括保留的阈值反馈 |
| old-5.3 `prop:center-stable-C1-v52` | 5801–5827 | 实际固定点族、物理初值图、射击映射和端点映射的 $C^1$ 性 |

旧 3.1 的证明在 3939–3973 行另行声称左图存在。它把

$$
A|_{E_0\oplus C_{\rm ref}}=
\begin{pmatrix}0&B_0\\0&D_c\end{pmatrix},\qquad
D_c^*\lambda_\pm=b_\pm
$$

归约为半直线零能方程，并用非零仿射荷分母宣称解在两个物理空间上有界。本轮反例并不排除这项特定分析结论；缺口是实际归约、适用源类、定义域及两个空间的范数估计尚未完整建立。已有仿射荷公式本身不能填补这些缺口。

旧 3.2 在 4117–4137 行则从参考中心二次型上的 Lax–Milgram 估计直接转到零模—中心 Sylvester 逆的一致界。这需要独立论证：可逆的压缩二次型不等于可逆的压缩 Hamilton 生成元。反例中压缩二次型是恒等，而 $D_c=0$、$B_0=I$，图方程 $\ell D_c=B_0$ 无解。

## 下一项实际义务

优先核验 old-3.1 的左图方程。必须明确实际 $D_c$ 的定义域、投影对定义域的保持、$b_\pm$ 的源类，以及半直线变换后的精确方程；随后证明解泛函在 $\mathcal X_1$ 与 $\mathcal X_{\rm f}$ 上同时有界。若这些条件不能成立，则保留 $B_0$ 的三角耦合，重新建立下游演化与反馈估计。即使固定左图最终成立，旧 3.2 的慢变 Sylvester 逆仍需另证。

已有 `TriangularThresholdCoupling.lean`、`DomainTriangularDynamics.lean` 和 `SlowFrameConnection.lean` 提供部分实际相位耦合或条件性结构公式，尚未构造这一整套实际物理演化。它们以及本反例均不增加原文验收分子。

## 核验

运行 `python verification/zero_center_obstruction_validation.py`，使用仓库固定的 Lean 4.35.0-rc3 与 mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`。

两个源码模块在新临时目录逐个以 `--trust=0 -DwarningAsError=true` 编译；审计输出全部模型定义体、终端完整类型及传递公理依赖。公理仅为 `propext`、`Classical.choice`、`Quot.sound`，没有 sorry/admit、新公理、unsafe、native_decide 或关闭 linter。状态、源码与产物哈希以及完整压缩审计分别记录在 `verification/zero-center-obstruction-status.json` 和 `verification/zero-center-obstruction-types-and-axioms.txt.gz`。这次检查范围是本诊断模块，不声称重新构建整个 HBL 仓库。
