### Related problem or entry

JSP-000840 — "How many triangles must a graph have once its edge count exceeds the maximum bipartite edge count?" (`problems/catalog-0801-0900.md#JSP-000840`; current record: Solved, Lean proof: No). Corresponds to Erdős problem #1010 (Erdős–Rademacher problem; solved in full by Lovász–Simonovits and independently Nikiforov–Khadzhiivanov).

Relation to issue #118: that issue records only the finite `n = 4` specialization as a placeholder observation (`resolved: null`, no verification attestation). This submission is the complete `t = 1` theorem for all `n` (Rademacher's theorem), with a full kernel-checked Lean 4 proof.

### Recipient placeholder or confirmed public ID

RECIPIENT-JSP-000840-A (identity unconfirmed; submitter public ID: github.com/tongriyaotxt)

### Contributions and evidence

**Contribution type: formalization only (scoped component t = 1).** The mathematical result is due to the published literature, not to this contribution:

- H. Rademacher (1941, unpublished; reported by Erdős);
- P. Erdős, *On a theorem of Rademacher–Turán*, Illinois J. Math. 6 (1962), 122–127;
- the inductive proof formalized here is Erdős's 1955 proof (delete a vertex of minimal degree);
- full problem (all `t`): L. Lovász and M. Simonovits (1976); V. Nikiforov and N. Khadzhiivanov, C. R. Acad. Bulgare Sci. (1981), 969–970.

**New contribution (2026-09-17):** a complete machine-checked Lean 4 formalization of the `t = 1` case recorded for this problem: *every simple graph on n vertices with at least ⌊n²/4⌋ + 1 edges contains at least ⌊n/2⌋ triangles*. The development includes from-scratch proofs of Mantel's theorem, the handshake lemma, vertex/edge-deletion counting identities, and Erdős's induction (including the even-`n` sub-case analysis via the degree-sum excess bound).

Formal statement (top-level theorem):

```lean
theorem jsp_000840 (n : Nat) (G : Gph n)
    (h : n * n / 4 + 1 ≤ ecountIn G.adj (List.finRange n)) :
    n / 2 ≤ tcountIn G.adj (List.finRange n)
```

Statement correspondence notes: a simple graph on `n` vertices is a symmetric irreflexive Boolean adjacency on `Fin n` (`Gph n`); edges are unordered pairs counted once (`i < j`); triangles are unordered triples counted once (`i < j < k`); `n*n/4 = ⌊n²/4⌋` and `n/2 = ⌊n/2⌋` (Nat division). No extra premises; all quantifiers first-order. See `STATEMENT-CORRESPONDENCE.md` in the repository for the full mapping table.

**Pinned proof source:**

- Repository: https://github.com/tongriyaotxt/jsp-000840-lean-proof
- Pinned commit: `TO_BE_FILLED_ON_PUSH`
- File: `Jsp000840.lean` (self-contained, **Lean 4 core only, no Mathlib dependency**, ~1500 lines)
- Toolchain: Lean v4.34.0 (pinned in `lean-toolchain`)

**Verification records:**

- Local kernel check (Lean v4.34.0, Windows, `lean Jsp000840.lean`): pass, no errors, no warnings (2026-09-17).
- Axiom audit (`#print axioms jsp_000840`): `propext`, `Classical.choice`, `Quot.sound` only. **No `sorryAx`; no `native_decide`/`Lean.ofReduceBool`** — the entire development is kernel-checked reasoning with no trusted computation.
- CI kernel check (GitHub Actions, ubuntu-latest, fresh elan + Lean v4.34.0, `lean Jsp000840.lean` plus automated sorryAx scan): TO_BE_FILLED_ON_PUSH.

If the record for JSP-000840 is updated to `Lean proof: Yes` (t = 1 component) following review, its claim-status screening flags would change accordingly; this issue supplies the evidence for that review. The submission covers only the `t = 1` case; the general Lovász–Simonovits theorem (`t < ⌊n/2⌋`) is not part of this submission.

### Confirmation status

Pending. No written confirmation exists yet; the recipient identity is intentionally left as the placeholder above. The submitting GitHub account is the public point of contact.

### Attribution questions and conflicts

None. No conflicts to disclose. Mathematical priority belongs to the literature cited above; this contribution claims formalization authorship only.
