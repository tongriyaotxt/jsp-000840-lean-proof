# JSP-000840 — Statement correspondence audit

Catalog entry (TheJustinSunPrize/awards, `problems/catalog-0801-0900.md#JSP-000840`):

> How many triangles must a graph have once its edge count exceeds the maximum bipartite
> edge count?

Scoped component formalized here: the **t = 1 case** (Rademacher's theorem), i.e. the
first step past the bipartite/Turán threshold. Upstream reference:
<https://www.erdosproblems.com/1010> ("every graph on n vertices with ⌊n²/4⌋ + t edges
contains at least t⌊n/2⌋ triangles", t < ⌊n/2⌋; the record there explicitly states
"Rademacher proved that every graph on n vertices with ⌊n²/4⌋+1 edges contains at least
⌊n/2⌋ triangles").

## Mapping table

| Informal concept | Lean formalization |
| --- | --- |
| simple graph on n vertices | `Gph n`: `adj : Fin n → Fin n → Bool` with `sym : ∀ i j, adj i j = adj j i`, `irr : ∀ i, adj i i = false` |
| edge (unordered pair) | counted once at the pair `i < j` (on `Fin.val`) |
| number of edges | `ecountIn G.adj (List.finRange n) = Σ_{i<j} (adj i j).toNat` |
| ⌊n²/4⌋ | `n * n / 4` (Nat division is floor) |
| triangle | unordered triple `i < j < k` with `adj i j ∧ adj j k ∧ adj i k` |
| number of triangles | `tcountIn G.adj (List.finRange n) = Σ_{i<j<k} (adj i j && adj j k && adj i k).toNat` |
| ⌊n/2⌋ | `n / 2` |
| "at least ⌊n/2⌋ triangles once edges exceed ⌊n²/4⌋" | `n*n/4 + 1 ≤ ecountIn … → n/2 ≤ tcountIn …` |

## Notes

- All quantifiers are first-order over `Nat`/`Fin n`; no extra premises, no classical
  axioms beyond the Lean default (`propext`, `Classical.choice`, `Quot.sound`).
- The full Erdős problem (all `t < ⌊n/2⌋`, Lovász–Simonovits / Nikiforov–Khadzhiivanov)
  is NOT claimed; this submission is explicitly the `t = 1` component.
- Vertex-deletion and edge-deletion counting identities are proved from first principles
  (`ecountIn_eq_filter_add_deg`, `ecountIn_deleteEdge`, `tcountIn_ge_delVertex_add_one`,
  `tcountIn_deleteEdge_add_one_le`); Mantel's theorem is included (`mantel`).
- No `sorry`, no `native_decide`; nothing trusted beyond the Lean 4 kernel (v4.34.0).
