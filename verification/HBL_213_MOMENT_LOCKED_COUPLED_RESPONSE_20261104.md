# HBL 2.13：实际内区响应与完整区间兼容关系（2026-11-04）

## 验收范围

本轮承接 `6b5144973abc49fd826bbb7be6beaf1ca466b8a5` 的目标驱动整改。正式修订版账本保持 **11/13（84.62%）**。本轮已完成两个真实内区响应、C1 物理迹与完整冻结兼容矩阵的实现及严格复验；尚未完成真实耦合校正的全部可解性义务，不能据此验收 2.13。

目标是推进整改清单第 1 项：从固定 Fredholm 逆导出两个实际速度响应和迹，组装同一对象的兼容矩阵。本轮没有预设逆雅可比、非零行列式、相对阶提升或 II 型速率。

## 实际构造

保持真实矩约束 `c_s=-bc+m`，方向为

\[
Q_c=\Lambda V_c-c\partial_cV_c,\qquad P_b=iQ_c,\qquad P_\omega=V_c.
\]

令 `eta_L(r)=1-cutoff(r/L)`。输入固定半线逆的源是

\[
G_b(r)=r\eta_L(r)Q_c(r),\qquad
G_\omega(r)=r\eta_L(r)V_c(r).
\]

新增源码证明两源属于原 `L^{2,7/4}` 空间；成员性由真实剖面、有界紧区间及截断支持推得，不是定理前提。随后直接使用原 `normalizedMinusInner/Output` 和 `normalizedPlusInner/Output`，导出原 Fredholm 方程、共振配对强制的 affine charges 和完整 C1 代表。

实际径向响应为 `u_b=i q_b/r`、`u_omega=q_omega/r`。界面导数保留

\[
\partial_z\left(\frac{q(az)}{az}\right)
=\frac{a\{azq'(az)-q(az)\}}{(az)^2}.
\]

`OutputLinearity.lean` 从加权数据、真实共振配对、固定正规化解唯一性及 Green 积分证明整个 affine-restored 输出线性。因此耦合映射中的响应迹由同一固定逆产生，没有自由边界列。

## 区间覆盖与符号

固定较小的内区半径 L 再只投影固定环带 `[R,2R]`，会在 `2L<aR` 时留下尚未处理的物理速度源。新实现取

\[
L=\ell^{-1/16},\qquad z_0=L/a,
\]

并保留 **整个 `[z_0,z_1]`** 上的原速度源积分。原点到 L 的输入与外部补项通过精确分割恒等式保留；没有把内区截断支持之外的源置零。新声明只证明这一区间映射的精确仿射关系，不证明移动界面的统一估计或全部 PDE 拼接误差。

必须区分原源投影与残差消去方程的符号。仓库 `AffineTailOperators.lean` 的 `H_±` 具有负 Laplacian；`ActualHartreeKummerOperatorConjugacy.lean` 的 Kummer 算子具有正 Laplacian。对加性校正，内区 `Hq=rP` 对应外区首部右端 `-a²P`。本实现显式保留此负号，并将算子差、时间项与非线性余项留给下一残差证明。

记 `T` 为原 outgoing Wronskian trace，`Pi` 为原 Green source coefficient，则本轮矩阵两列定义为

\[
C_b=T_{z_0}(J_b)+\Pi_{[z_0,z_1]}(a^2P_b(a\cdot)),\qquad
C_\omega=T_{z_0}(J_\omega)+\Pi_{[z_0,z_1]}(a^2P_\omega(a\cdot)).
\]

等价地，每列都是 `T(J)-Pi(outer correction RHS)`。这与正源输入时 `T(J)-Pi(P)` 的纯代数公式不矛盾；不能在解释为 PDE 残差消去时混用两种右端符号。既有 source-only 正号定理保持不变。

新终端从物理辐射幅度、Strauss 界和参数范围推导输入成员性与外区可积性，证明在冻结配置下

\[
\mathcal C(\delta b,\delta\omega)
=\mathcal C(0,0)+\delta b\,C_b+\delta\omega\,C_\omega.
\]

这仍不是沿真实轨道变化的完整 Jacobian：基底、界面、尺度及剖面的参数变化必须另行控制。

这里的物理特化是对合法瞬时参数的家族恒等式，并未构造一条满足矩锁定动力学的真实辐射轨道。内区终端目前提供原加权 Fredholm 方程及 C1 物理迹；新响应的逐点经典二阶物理方程还需接入径向共轭与正则性接口，不能由 C1 自动宣称。

## 仍未闭合

1. 上述真实两列的非退化性及所需定量逆界，特别是 `z_0=L/a` 趋向原点时的精确 Wronskian 权与迹估计。
2. 与完整原 PDE 校正的算子差、时间项、截断交换子、所有非局部项及远区项的对应。
3. 一步真实残差相对于旧残差的严格正增阶，随后才能接入有限递推。
4. 原 2.13 所需 Hessian、参数差分、局部 Lipschitz 与最终 PDE 轨道/选速。

没有通过增加辅助编号、假设可逆性、预设爆破速率或把绝对小量重复当作相对增阶改变 11/13。

下一承重估计已在 [完整冻结矩阵的定量候选推导](HBL_213_COUPLED_DETERMINANT_NEXT_STEP_20261104.md) 中具体展开。它保留真实内区迹、强制荷和 Green 一阶矩，给出归一化两列的误差表达式，并指出移动半径下需要控制 `L^(13/4)/a^2` 与 `a*|c|`。该分析稿尚未 Lean 验收，不计为已证非退化；它也明确保留实际外端点选择、参数窗口、经典物理方程和完整非局部拼接残差的缺口。

## 源码和检验入口

- `HBL/InnerEstimates/OutputLinearity.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedInnerResponse.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedProjection.lean`：只追加完整指定区间接口，旧声明保留。
- `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedCoupledCompatibility.lean`
- `HBL/TypeIIDynamicSelection/ActualHartreeMomentLockedCoupledCompatibilityAudit.lean`
- 沿用 `.github/workflows/hbl-213-moment-locked-projection.yml`，保留 Lean 4.35.0-rc3、Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5` 及原缓存、原五条审计。

## 实际严格复验

- 通过验收的代码提交：[83711a2964cfb7d335d7c22b2d1e33369361c3d8](https://github.com/penghongzhong/HBL/commit/83711a2964cfb7d335d7c22b2d1e33369361c3d8)。本记录后续仅作说明文档更新，不将文档提交混同于新的 Lean 验收。
- [CI 41809180683](https://github.com/penghongzhong/HBL/actions/runs/41809180683) 完成且结论为 `success`；job 为 `126503870555`。
- [证据 artifact 13311716206](https://github.com/penghongzhong/HBL/actions/runs/41809180683/artifacts/13311716206)，ZIP SHA-256 为 `95f2ea42385a026cb2aa97d769ffd7f70d555ed322e907742b44abf9f5356620`。
- Lean 固定为 `4.35.0-rc3`，compiler commit 为 `470d5ce1400764999581fd26d5d72b00d990b0f4`；Mathlib 固定为 `a98628e16c11f5167f16124105ddce53efa9bfe5`，未迁移工具链。
- 五份实际证明源逐一执行 `lake env lean --trust=0 -DwarningAsError=true`，严格重放日志均为空；两份 Audit 也以相同严格选项重放。
- 新的 20 条公开声明全部打印完整类型并逐条检查公理；原 5 条物理源审计同时保留。公理依赖均只有 `propext`、`Classical.choice`、`Quot.sound`，没有 `sorryAx` 或新增公理。
- 新类型输出开启 `pp.all`，没有省略号截断；打印公理时仅局部恢复标准显示，以保持公理名称与既有白名单一致，未放宽白名单。
- 已下载归档并独立核对 ZIP 摘要、内部 `commit.txt`、八份归档源码 SHA-256、精确提交的 Git blob 与本地源码字节，全部一致。这是对 CI 实际证据的复核，不声称在本地重新运行 Lean。
- 本轮 Lake 的目标及依赖构建完成 `4167 jobs`。这是目标及依赖的构建规模，不是论文证明数量或全仓库零警告声明；历史依赖 linter 警告仍在既有证明池中。

此前修复过程中的失败 run 均不作为验收证据。正式论文分子没有增加；这次通过只关闭响应、迹和冻结兼容关系的具体子步骤。
