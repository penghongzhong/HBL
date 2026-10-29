# HBL：按完整原文环境推进

用户于2026-10-29要求参照 OpenAI 数学发布加速。已阅读 openai/math 的 README、Lean README、ComparatorChallenges README、Lean family 371 范围说明及 DefocusingNLS 挑战陈述；本地固定 Lean 4.35.0-rc3 也已确认提供 lake comparator / lake check。未运行 Comparator，不登记其成功。

参考链接：
- https://github.com/openai/math
- https://github.com/openai/math/blob/main/lean/README.md
- https://github.com/openai/math/blob/main/lean/ComparatorChallenges/DefocusingNLS.lean
- https://github.com/openai/math/blob/main/lean/docs/371.md

公开发布所说三小时是每项成果平均使用的 Pro 思考算力；其说明不承诺每篇论文从构思到全部 Lean 形式化的完整用时。该库各结果的验证阶段不同。

本项目当前9/21。近期观测、图单值性等辅助构造均保留，但不增加分子。主要效率问题是连续扩展辅助模块而未闭合完整原文目标。

下一轮优先目标固定为 old-2.12 / prop:one-layer-stage3，先利用已通过的实际 Kummer 紧参数逆、唯一性与切向估计，解决规定匹配环带、带权重叠及真实源/残差对应。必须核对整个原陈述的量词、函数空间、参数一致性和全部结论。局部环带存在性不能替代规定匹配环带；抽象右逆包不能替代实际物理算子实例。

旧3.1及其下游八项继续列为撤回待修复。Hamilton光滑图的四个辅助定理已严格核验，应保存后停止继续堆叠同类辅助结论，直至能说明它们如何闭合一个完整目标。

执行方式：复用固定依赖和源码哈希一致的编译缓存；调试仅编译变化模块及必要依赖；完整目标闭合后集中输出类型、公理和原文范围审计。辅助模块不单独作为完成环境报告。不为追赶数字把传播子、真实余项或目标结论改成假设。

禁止将本文件或新的目标选择登记为数学验收成功。本文不声称Comparator通过、原文环境增加或主PDE定理闭合。

## 规定环带进展

2026-10-29 后续批次已构造任意输入 `0<d<z` 上的实际 Kummer 逆，环带不再由证明缩小；包括双侧端点导数、Wronskian 非零、指定中心基底端点规范下的唯一性及源/残差界。详见 `HBL/KummerPrescribedAnnulus/README.md` 和 `verification/kummer-prescribed-annulus-status.json`。

仍待证明规定环带上的紧参数一致性/参数导数，并把中心初值基底与稿件出射基底及带权重叠匹配对应；实际非线性源、残差符号和增阶分类仍须从 PDE 推导。当前不增加原文验收数。
