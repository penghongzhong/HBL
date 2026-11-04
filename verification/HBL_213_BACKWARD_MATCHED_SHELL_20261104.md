# HBL 2.13：同一真实校正的后向匹配与壳层相对增益

日期：2026-11-04。正式论文环境仍为 **11/13（84.62%）**。

## 本轮关闭的承重环节

本轮复用已验收的固定 Fredholm 逆、完整兼容矩阵与真实速度源，把它们合成为一个实际的后向匹配校正。终端声明是 `actual_Hartree_moment_locked_constructed_backward_shell`，而不是接受 `hstep` 的结构性递推。

**验收状态：已通过严格 CI 与下载归档的独立复核。**

证明提交：[8eb8daada29a861d025dd5b38a177d7b2a72c957](https://github.com/penghongzhong/HBL/commit/8eb8daada29a861d025dd5b38a177d7b2a72c957)。
严格 CI：[41844544308](https://github.com/penghongzhong/HBL/actions/runs/41844544308)。

固定 `mu,theta` 后，终端内部构造原点 Kummer 基 `K`、`0<B<1`、`L0>=6`、`epsilon>0` 与常数 `C>0`。对原物理径向辐射切片 `z`，取

\[
L=\ell^{-1/16},\qquad R=L/2,
\qquad L\ge L_0,\quad a\ge L^3,\quad |c|\le1,\quad a|c|\le\varepsilon.
\]

源数据条件为 `0<ell<=1`、辐射的实际可测性、正半轴一致界和大半径 Strauss 界；真实共轭内源的连续性、完整外源在正 Kummer 区间上的点连续性仍是显式正则性输入。并未从可测性推出连续性。两个共轭内源仍要求全局连续；完整外源 `Fo` 只要求正 Kummer 区间的 `ContinuousAt`，未要求 `Fo` 的 totalized 公式在零点或负轴连续。

终端内部导出原两通道源的 weighted membership 和完整外源可积性，选择**同一完整兼容矩阵确定的唯一两个实增量** `(db,dw)`，用同一固定逆重建调整后的内场，并用同一真实 Cauchy jet 构造明确的 Kummer 外场。它返回匹配证书、证书意义下的速度唯一性、实际壳层源的加权可积性、相对范数界，以及同一外场用真实导数计算的有限 `B` 端 trace 为零。

## 两侧的源与接口为什么现在确实相同

原来的内源截断 `eta_L` 在 `[L,2L]` 变化。若在这一区间直接把内场方程和保留完整物理源的外场方程相减，还会出现

\[
(1-\eta_L)S_{\rm full}.
\]

该项没有凭“匹配”自动变小，不能从估计中删除。本轮将拼接环带取为 `[L/2,L]`，保留原兼容矩阵的匹配位置 `L/a`，把**同一个**外场从物理半径 `L` 向内延续。整个新环带满足 `eta_L=1`。

实际源恒等式为

\[
\frac{F_+(r)+iF_-(r)}r
=S_{\rm Hartree}(\ell,c,z;r)
 +\delta b\,P_b(c;r)+\delta\omega\,P_\omega(c;r),\qquad 0<r\le L,
\]

其中

\[
F_+=F_{+,0}+\delta\omega G_\omega,
\qquad F_-=F_{-,0}+\delta bG_b,
\]

以及 `P_b=i(Lambda V_c-c partial_c V_c)`、`P_omega=V_c` 均为原来的真实物理方向。缩放后的完整外源严格满足

\[
a^{-2}F_o(r/a)=-\frac{F_+(r)+iF_-(r)}r.
\]

原 Riesz 项保留在 `S_Hartree` 中。原 `[L/a,B]` 的积分端点、外源以及两项齐次系数均未改动；向左延续只是同一 Green 公式中的积分自然改变方向。没有界面修复源，没有另选内区迹，也没有新自由单极幅度。

## 同一实际外场及其真实端点导数

显式外场为原 Green 特解加两项 Cramer 齐次项。两项系数均由同一个真实内区 jet 和同一外源唯一确定，奇异系数恰等于完整兼容缺陷。另证正则系数只取决于输入 jet，源项在右端仍以原积分出现。

新的 FTC 证明在较大的正环带上展开，而固定的 Green 积分端点始终是 `L/a,B`。因此原式在整个正基底域都有真实一阶和二阶导数，尤其包括积分端点和原匹配点左侧。物理拉回

\[
v(r)=w(r/a)
\]

严格满足原缩放 Kummer 方程，并在 `r=L` 满足

\[
v(L)=u(L),\qquad v'(L)=u'(L),
\]

这里 `u=q_+(F_+)/r+i q_-(F_-)/r`，两个 `q` 来自既有固定规范化逆。斜率不再只是命名的迹变量，而被证明等于实际 `deriv`。

## 相对增益来自实际方程差

记

\[
D_a=\Delta_r+a^{-2}\left(\frac{ir}{2}\partial_r+k_{\mu,\theta}\right),
\qquad N=\|F_+\|_{L^{2,7/4}}+\|F_-\|_{L^{2,7/4}}.
\]

对同一规范化内区输出，真实泡 Hessian 方程及核行估计给出

\[
\left\|D_a u+\frac{F_++iF_-}r\right\|
\le N\left(\frac{C_{\rm eq}}{R^4}+\frac{C_K}{a^2}\right),\qquad r\in[R,2R].
\]

非局部项的逐点估计来自真实 Hartree 核行与原 weighted output norm；不是把仅 a.e. 的代表任意换成逐点结论。

令 `d=u-v`。同源恒等式和右端真实匹配给出 `d(L)=d'(L)=0`。通过 `r^2 d'` 的导数恒等式与两次均值估计，并吸收完整 Kummer 一阶、零阶项，导出 `d,d'` 的小界。只需显式预算

\[
16R^2\frac{1+|k_{\mu,\theta}|}{a^2}\le1,
\]

它已从原区域 `a>=L^3` 和提高固定 `L0` 推出，没有作为最终构造的新假设保留。证明允许零 jet 点在环带任一位置，因此原常数也适用于右端 `L=2R`。

完整拼接交换子是

\[
E_{\rm sh}=D_a(\chi_Rd)-\chi_RD_ad
=[\Delta_r,\chi_R]d+a^{-2}\frac{ir}{2}\chi_R'd.
\]

第二个真实输运项保留并估计；零阶项通过代数精确抵消。通过实际导数的可测性还导出了 `E_sh` 的可测性，没有额外假设任意全局外场可测。

原 Fredholm 源是 `r E_sh`，半线测度是 `dr`。定义

\[
\mathcal E_R(r)=\mathbf1_{(R,2R)}(r)\,r\,|E_{\rm sh}(r)|.
\]

实际证明

\[
\|\mathcal E_R\|_{L^{2,7/4}}
\le 20 C\left(C_{\rm eq}R^{-3/4}
       +C_K\frac{R^{13/4}}{a^2}\right)N
\le C_\ast(C_{\rm eq}+C_K)R^{-3/4}N.
\]

其中 `R^(13/4)` 完整包含径向共轭、`7/4` 权重和平方根环带体积。代入 `R=ell^(-1/16)/2` 后，负半径因子相当于固定常数乘 `ell^(3/64)`。这是同一实际壳层误差相对其调整后源范数的增益，不是给生成项贴阶数标签，也不是重复使用某个固定绝对小量。

## 真实速度逆界与矩锁定时间项

本轮还证明完整列的定量逆界。在实际统一物理区域内，完整列各自满足 `norm(column)<=a B^2`，结合已证明的行列式下界 `a^2 B^4/256`，对真正满足完整兼容方程的增量得到

\[
|\delta b|+|\delta\omega|
\le \frac{1024}{aB^2}|Z_{\rm actual}|.
\]

`Z_actual` 是同一基线内区解的真实 jet 与完整外源构成的 `IntervalObstruction`；该式没有把它未经证明地替换成原内源范数。逆界的 region 版本仍显式接收实际基底的 `D,G,B` 估计与 small-B 数据，内部导出列界和行列式界；本轮尚未把这条逆界进一步并入构造终端的同一存在性见证。

原 PDE 残差也已补齐矩锁定的时间变化。固定瞬时尺度值，显式构造

\[
\ell_{\delta b}(\sigma)=\ell(\sigma)e^{-\delta b(\sigma-s)},
\]

保留同一物理时钟和同一真实三维辐射矩，由链式法则得到 `delta c_s=-delta b*c`。所以原残差中的 `delta b` 列精确为 `i(Lambda V_c-c partial_c V_c)`。校正的 `iH_s`、速度与校正的交叉项以及真实 Hartree Taylor 余项全部保留。该辅助路径仅用于瞬时时间 jet 恒等式，未宣称其已解出整个动力系统。

## 验收范围与论文计数

本轮关闭：**同一固定逆输出、完整兼容消去、同一真实外场、实际接口导数、无源错位的后向拼接，以及完整 Kummer 壳交换子的原源范数相对增益。**

以下尚未由本轮终端导出，故 `thm:finite-profile-stage3` 仍未整体验收：

1. 当前 `N` 明确是调整后的两通道源范数。仍须把实际兼容逆界与速度源范数、完整外源控制合成，得到所需原残差输入的统一算子界。
2. 换入这一个全局校正后的非局部尾反馈、实际时间项、移动参数/Hessian 差及非线性余项，尚须在同一论文范数中一起获得相对增阶。
3. 有限小端点 `B` 的原点基 trace 不能等同无穷远辐射条件；远区匹配及其实际误差仍须接入。
4. 以上完整单步完成后，才能合法调用有限递推，并验证实际参数 Jacobian、Hessian 与下游稳定性所需全部结论。

因此本轮不把新 Lean 声明数或构建任务数计入论文分子，正式论文环境保持 **11/13（84.62%）**。

## 严格证据

- 精确证明提交：`8eb8daada29a861d025dd5b38a177d7b2a72c957`；本轮为 15 份新增证明源码、38 条新增公开声明。
- 严格运行：[41844544308](https://github.com/penghongzhong/HBL/actions/runs/41844544308)，`completed / success`；job `126624516281` 全步骤成功。
- 归档：[13331040987](https://github.com/penghongzhong/HBL/actions/runs/41844544308/artifacts/13331040987)；ZIP SHA-256 `e88f2bccaa7ab9519d7d45ca725675e58a8bd0b95d7175117af2c7fb12aa43da`。
- Lean `4.35.0-rc3`，compiler commit `470d5ce1400764999581fd26d5d72b00d990b0f4`；编译器压缩包 SHA-256 `1526de16c0496f16b46a168f26c990af4e3796505273c3342fec17d72d763997`；Mathlib `a98628e16c11f5167f16124105ddce53efa9bfe5`。
- 37 份目标证明源码逐一 `--trust=0 -DwarningAsError=true` 重放，37 份日志均为 0 字节；两份 Audit 同样严格执行。
- 累计 95 条扩展声明及 5 条既有基线，共 100 条完整类型和公理报告，均恰依赖 `propext`、`Classical.choice`、`Quot.sound`，无 `sorryAx`、无类型截断。终端结论的实际 `Prop` 定义也额外完整展开，未把误差界隐藏为输入字段。
- 40 份唯一归档源码的 SHA-256、Git blob、精确提交字节及本地源码字节全部一致；清单 41 行中的既有 `ProjectionAsymptotics` 重复路径内容一致，未重复计数。本轮相对上一已验提交 `24c0144…` 的所有 15 份变化证明源码均包含在严格重放中。
- 目标和依赖共 4243 个构建任务；保留 126 条历史依赖警告，目标源码严格重放零警告。构建任务数不计入论文分子。
- 机器复核报告：[HBL_213_BACKWARD_SHELL_INDEPENDENT_CHECK_20261104.json](HBL_213_BACKWARD_SHELL_INDEPENDENT_CHECK_20261104.json)。报告由下载 ZIP 对照精确提交复核产生。

前期失败运行 `41837865623`、`41839806602`、`41841267958`、`41842204856`、`41843039040`、`41843618331` 仅用于修复证明实现，不作为验收证据。后续记录提交不修改已验 Lean 源码。
