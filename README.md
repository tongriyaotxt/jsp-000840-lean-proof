# Justin Sun Prize — JSP-000840 Lean 4 形式化证明（Rademacher 定理，t = 1 分量）

## 题目

**JSP-000840**: How many triangles must a graph have once its edge count exceeds the
maximum bipartite edge count?
（边数刚刚超过二部图最大边数 ⌊n²/4⌋ 时，图中至少有多少个三角形？）

来源：<https://github.com/TheJustinSunPrize/awards> · `problems/catalog-0801-0900.md#JSP-000840`
对应 Erdős 问题 <https://www.erdosproblems.com/1010>（Erdős–Rademacher 问题；
一般形式 `⌊n²/4⌋ + t` 条边 ⟹ 至少 `t⌊n/2⌋` 个三角形，t < ⌊n/2⌋，由
Lovász–Simonovits 与 Nikiforov–Khadzhiivanov 独立解决）。

## 本仓库证明的内容（scoped component：t = 1，即 Rademacher 定理）

**每个 n 顶点简单图，若边数 ≥ ⌊n²/4⌋ + 1，则三角形数 ≥ ⌊n/2⌋。**

这是 Erdős 问题的 t = 1 情形（Rademacher 1941；Erdős 1955 给出的归纳证明），
也是该问题记录在案的奠基性情形。t ≥ 2 的一般 Lovász–Simonovits 定理不在本提交范围内。

形式化陈述（`Jsp000840.lean`，纯 **Lean 4 core**，零依赖，不需要 Mathlib）：

```lean
theorem jsp_000840 (n : Nat) (G : Gph n)
    (h : n * n / 4 + 1 ≤ ecountIn G.adj (List.finRange n)) :
    n / 2 ≤ tcountIn G.adj (List.finRange n)
```

- 图：`Gph n` = `Fin n → Fin n → Bool` 邻接矩阵 + 对称性 + 无自环。
- 边数 `ecountIn`：无序点对 i < j 的计数（Nat 除法即向下取整，`n*n/4 = ⌊n²/4⌋`）。
- 三角形数 `tcountIn`：无序三元组 i < j < k 两两相邻的计数。

## 证明思路（Erdős 1955 归纳法）

对 n 强归纳。先用"删边"（`shrink`，删一条边只减三角形数）把边数缩到恰好 ⌊n²/4⌋+1。

- **n = 2q+1（奇）**：度数总和 = 2e = 2(q²+q+1) < (2q+1)(q+1)，故存在顶点 v 度 ≤ q；
  删 v 后剩 ⌊(n−1)²/4⌋+1 条边，直接套归纳假设。
- **n = 2q+2（偶）**，子情形 1：存在顶点 w 度 ≤ q。删 w 后边数 ≥ ⌊(n−1)²/4⌋+2；
  由 Mantel 定理（本文件内证明：两顶点删除归纳）取一个三角形，删去它的一条边，
  再套归纳假设——被毁的三角形贡献 +1。
- **n = 2q+2（偶）**，子情形 2：所有顶点度 ≥ q+1。度数总和恰为 2q²+4q+4，故至多两个顶点
  度 > q+1；Mantel 给出的三角形 (a,b,c) 上必有一点 y 度恰为 q+1。删 y：边数恰降至
  归纳阈值，而 y 本身在一个三角形上（顶点删除恒等式 +1 补回）。

全部推理为内核可核查的构造性/经典逻辑：列表加权和（`ssum`）、filter 计数恒等式、
握手引理、鸽笼（公共邻居）、Mantel、逐点 Bool 单调性。

## 构建与验证

安装 Lean 4（本证明在 v4.34.0 上验证通过；见 `lean-toolchain`）后：

```bash
lean Jsp000840.lean
```

公理审计（文件末尾 `#print axioms jsp_000840`）：仅 `propext`、`Classical.choice`、
`Quot.sound`。**无 `sorryAx`，未使用 `native_decide`**（全部推理为内核可核查的证明项，
无可信计算成分）。

## 数学出处（原问题的解答，非本仓库贡献）

- H. Rademacher (1941, 未发表)；P. Erdős, *Some remarks on the theory of graphs* 相关注释 /
  P. Erdős, *On a theorem of Rademacher–Turán*, Illinois J. Math. 6 (1962), 122–127.
- 完整问题（任意 t）: L. Lovász and M. Simonovits (1976); V. Nikiforov and
  N. Khadzhiivanov, C. R. Acad. Bulgare Sci. (1981), 969–970.

本仓库贡献：上述 t = 1 定理的机器可验证形式化（Lean 4 core）。数学结果本身属于上述文献。
