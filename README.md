# Siegel-φπ Public Lean Validation

本仓是公开、最小化的数学形式化验证轨，只包含可公开的 Lean 源、依赖锁与验证工作流；不包含私域协作文件、运行状态或凭证。

## 验证对象

`lean_proofs/Proofs.lean` 当前包含 31 个 theorem，覆盖有限 KL／Gibbs、Kuramoto 积分、Kleene 第二递归定理、π 无理性与超越性、CHSH／Tsirelson 的有序星环、C⋆-代数及矩阵 L2 范数形式。

## 公共 CI 闸口

1. 固定 Lean `v4.36.0-rc2` 与 mathlib 提交 `4ecbbfd4570fa1dde086dffd72bc5dec5a728042`。
2. 真实 `lake build` 与 `lean4checker --fresh Proofs`。
3. 31/31 theorem 的 `#print axioms` 审计，拒绝任何 `sorryAx`、未知公理和覆盖缺失。
4. `lean4export` 导出后由独立 Rust `nanoda` 检查全部传递依赖。
5. 已知坏答案 `False := by sorry` 必须被 nanoda 拒绝，否则整个工作流失败。

公开仓库的标准 GitHub-hosted runner 用于避免私域 CI 额度消耗。公共 CI 的运行成功不代表命题自然语言语义已经外部数学评审；语义边界仍须阅读源文件。
