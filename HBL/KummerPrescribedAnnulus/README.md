# 规定正环带上的实际 Kummer 逆

目标仍为原命题 `prop:one-layer-stage3`。本批去掉实际 Kummer 基本解与逆构造中的“小环带”限制，原文环境验收仍为 **9/21**。

对任意输入的实参数 `mu, theta` 和 `0 < d < z`，终端
`exists_actual_kummer_prescribed_annulus_inverse` 构造

\[
I=[z-d,z+d],\qquad
T:C(I;\mathbb C)\longrightarrow C(I;\mathbb C^2),
\]

其中 `T F = (u,u')`，实际方程为

\[
u''+\left(\frac2r+\frac{ir}{2}\right)u'
+\left(\theta+i\left(\frac14-\mu\right)\right)u=F.
\]

环带中心和宽度均为输入，没有缩小它们。输出在整个闭环带、包括两端点，具有真正的一、二阶径向导数。

构造得到在中心归一化的基本解 `phi, psi`，其初值分别为 `(1,0)`、`(0,1)`。Wronskian 在整个环带不为零。端点规范为

\[
u(z+d)\psi'(d)-u'(z+d)\psi(d)=0,\qquad
\phi(-d)u'(z-d)-\phi'(-d)u(z-d)=0.
\]

这里基本解的自变量是相对中心的坐标。终端还证明该规范下的唯一性、算子范数及稳定性。存在有限的 `C>0`，令 `B=4dC^3`，则

\[
\|T\|\le B,\qquad \|TF-TG\|\le B\|F-G\|.
\]

任意满足同一端点规范的经典近似解 `U`，若其实际方程源是 `H`，则

\[
\|U-TF\|\le B\|H-F\|.
\]

## 延拓方法

在四个实坐标中截断状态变量，获得全局有界、Lipschitz 的向量场，从而直接在预先规定的有限区间上应用 Picard–Lindelöf。对缩小后的初值使用 Grönwall 估计，证明解始终位于截断恒等区域；利用线性齐次性缩放回来，得到未截断方程的解。

实际 Kummer 系数逐项转换为四维实线性算子。Abel 微分恒等式与逆向初值唯一性证明 Wronskian 不消失。先在稍大区间求解，再在输入中心重新归一化，以保证规定闭环带的端点也有双侧导数。最后直接复用已经验证的变参数积分、唯一性与误差估计。

六个新定理各占一个文件。没有把基本解、延拓、Wronskian 非零或右逆作为假设。

## 核验与未完成部分

`verification/kummer_prescribed_annulus_validation.py` 在全新目录中严格编译七个新源文件，并审计完整类型、定义体与传递公理。固定 Lean 4.35.0-rc3 和 mathlib a98628e16；使用 `--trust=0 -DwarningAsError=true`。既有 71 个严格编译文件只在源码与编译产物哈希全部一致时复用，否则重建其证书。历史依赖的普通构建不冒充全文严格重验。

上面六个定理完成固定参数构造。后续四个定理已补上规定环带上的紧参数统一界：给定任意紧集 `A` 以及输入 `0<d<z`，存在同一 `eps,C,B`，使

\[
d<\varepsilon<z,\qquad C>0,\quad B=4dC^3>0,
\]

对每个 `p=(mu,theta) in A`，实际中心归一化基本解都满足 `LocalKummerBound K C`，相应实际逆满足

\[
\|T_p\|\le B,\qquad
\|T_pF-T_pG\|\le B\|F-G\|,\qquad
\|U-T_pF\|\le B\|H-F\|.
\]

最后一个估计中 `U` 解实际方程 `L_p U=H`，并满足该参数的中心基底端点规范。`C,B` 对参数和源一致；环带没有缩小。

证明不对每个参数分别选取常数。先用紧性统一控制实际系数，记

\[
\sup_{p\in A,\ |t|\le\varepsilon}
\left(\left|\frac2{z+t}+\frac{i(z+t)}2\right|
+\left|\theta+i\left(\frac14-\mu\right)\right|\right)\le D.
\]

由中心初值及双向 Grönwall，四个基本解分量均被 `exp((D+1)eps)` 控制。Abel 恒等式还给出

\[
W'=-aW,\qquad (W^{-1})'=aW^{-1},\qquad W(0)=1,
\]

故同一常数也控制逆 Wronskian。终端为 `exists_compact_prescribed_kummer_inverse`。

`verification/kummer_compact_prescribed_validation.py` 在新目录严格编译这四个定理，复用经过源码和产物哈希核对的既有 78 个严格编译文件，审计完整类型、实际系数、解的定义、基本解结构构造子的全部字段及传递公理。恢复依赖时的普通构建不计作全文严格复验。

这仍不是原文 2.12 的闭合：

- 紧参数统一的零阶算子界已证明；规定环带上的实际参数导数及其统一高阶界仍待证明。
- 本批使用中心初值归一化基底，尚未识别成稿件指定的奇异/正则出射基底及匹配规范。
- 带权重叠、三个区域的实际 Hartree 源、残差展开及增阶分类仍未接通。

下一步应连接这些原文义务，不增加与该目标无关的辅助接口，也不把本批登记成新的原文环境。
