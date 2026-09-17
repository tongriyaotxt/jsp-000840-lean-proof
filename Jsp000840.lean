/-!
# JSP-000840 (scoped component, t = 1) — Rademacher's theorem

Every simple graph on `n` vertices with `⌊n²/4⌋ + 1` edges contains at least
`⌊n/2⌋` triangles.

This is the `t = 1` case of Erdős's problem (JSP-000840 / Erdős problem #1010:
"graphs with `⌊n²/4⌋ + t` edges contain at least `t⌊n/2⌋` triangles"), proved in
full by Lovász–Simonovits and independently Nikiforov–Khadzhiivanov. The `t = 1`
case is Rademacher's classical theorem (1941, unpublished); the proof formalized
here is Erdős's 1955 induction (remove a vertex of minimal degree).

Mathematical references (the result is classical, not new here):
- H. Rademacher (1941), unpublished; P. Erdős, *On a theorem of Rademacher–Turán*,
  Illinois J. Math. 6 (1962), 122–127; P. Erdős (1955, Hebrew journal, English
  appendix) for the inductive proof used below.
- L. Lovász and M. Simonovits (1976); V. Nikiforov and N. Khadzhiivanov (1981)
  for the full theorem.

Self-contained formalization in **Lean 4 core** (no Mathlib, no imports).
-/

namespace Jsp000840

/-! ## Weighted sums over lists -/

/-- Sum of `f` over a list. -/
def ssum (l : List α) (f : α → Nat) : Nat := (l.map f).sum

theorem ssum_nil (f : α → Nat) : ssum [] f = 0 := rfl

theorem ssum_cons (a : α) (l : List α) (f : α → Nat) :
    ssum (a :: l) f = f a + ssum l f := by simp [ssum]

theorem ssum_congr {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x = g x) :
    ssum l f = ssum l g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, ssum_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem ssum_add (l : List α) (f g : α → Nat) :
    ssum l (fun x => f x + g x) = ssum l f + ssum l g := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [ssum_cons, ssum_cons, ssum_cons, ih]; omega

theorem ssum_const (l : List α) (c : Nat) :
    ssum l (fun _ => c) = c * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, ih, List.length_cons, Nat.mul_succ]; omega

theorem ssum_le {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≤ g x) :
    ssum l f ≤ ssum l g := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [ssum_cons, ssum_cons]
    exact Nat.add_le_add (h a (List.mem_cons_self ..))
      (ih (fun x hx => h x (List.mem_cons_of_mem _ hx)))

theorem ssum_ge {l : List α} {f g : α → Nat} (h : ∀ x ∈ l, f x ≥ g x) :
    ssum l f ≥ ssum l g := ssum_le h

theorem ssum_swap (A : List α) (B : List β) (f : α → β → Nat) :
    ssum A (fun i => ssum B (f i)) = ssum B (fun j => ssum A (fun i => f i j)) := by
  induction A with
  | nil =>
    have hz : ssum B (fun j => ssum [] (fun i => f i j)) = 0 := by
      calc ssum B (fun j => ssum [] (fun i => f i j))
          = ssum B (fun _ => 0) := ssum_congr (fun j _ => rfl)
        _ = 0 * B.length := ssum_const B 0
        _ = 0 := Nat.zero_mul _
    rw [ssum_nil]; exact hz.symm
  | cons a A ih =>
    rw [ssum_cons]
    have step : ∀ j ∈ B, ssum (a :: A) (fun i => f i j) =
        f a j + ssum A (fun i => f i j) := fun j _ => ssum_cons a A _
    calc ssum B (f a) + ssum A (fun i => ssum B (f i))
        = ssum B (f a) + ssum B (fun j => ssum A (fun i => f i j)) := by rw [ih]
      _ = ssum B (fun j => f a j + ssum A (fun i => f i j)) := (ssum_add B (f a) _).symm
      _ = ssum B (fun j => ssum (a :: A) (fun i => f i j)) := (ssum_congr step).symm

theorem ssum_eq_zero {l : List α} {f : α → Nat} (h : ∀ x ∈ l, f x = 0) :
    ssum l f = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons, h a (List.mem_cons_self ..),
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)), Nat.add_zero]

/-- If `f ≤ g` pointwise on `l` and the gap at `y ∈ l` is at least 1,
the total gap is at least 1. -/
theorem ssum_add_one_le {l : List α} {f g : α → Nat}
    (h : ∀ x ∈ l, f x ≤ g x) (y : α) (hy : y ∈ l) (hy1 : f y + 1 ≤ g y) :
    ssum l f + 1 ≤ ssum l g := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rw [List.mem_cons] at hy
    cases hy with
    | inl hya =>
      subst hya
      have h1 : ssum l f ≤ ssum l g :=
        ssum_le (fun x hx => h x (List.mem_cons_of_mem _ hx))
      have h2 := Nat.add_le_add hy1 h1
      rw [ssum_cons, ssum_cons]
      omega
    | inr hyl =>
      have h2 : ssum l f + 1 ≤ ssum l g :=
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx)) hyl
      have h3 : f a ≤ g a := h a (List.mem_cons_self ..)
      rw [ssum_cons, ssum_cons]
      omega

/-- A positive total has a positive term. -/
theorem ssum_pos_of_pos {l : List α} {f : α → Nat} (h : 1 ≤ ssum l f) :
    ∃ x ∈ l, 1 ≤ f x := by
  induction l with
  | nil => rw [ssum_nil] at h; omega
  | cons a l ih =>
    rw [ssum_cons] at h
    by_cases ha : 1 ≤ f a
    · exact ⟨a, List.mem_cons_self .., ha⟩
    · have h0 : f a = 0 := by omega
      have h1 : 1 ≤ ssum l f := by omega
      cases ih h1 with
      | intro x hx => exact ⟨x, List.mem_cons_of_mem _ hx.1, hx.2⟩

/-- If every term vanishes off the `p`-filter, the sum equals the filtered sum. -/
theorem ssum_filter_of_vanish (p : α → Bool) (l : List α) (f : α → Nat)
    (h : ∀ x ∈ l, p x = false → f x = 0) :
    ssum l f = ssum (l.filter p) f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons]
    cases hp : p a with
    | true =>
      have hrw : (a :: l).filter p = a :: l.filter p := by simp [List.filter, hp]
      rw [hrw, ssum_cons, ih (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)]
    | false =>
      have hrw : (a :: l).filter p = l.filter p := by simp [List.filter, hp]
      rw [hrw, h a (List.mem_cons_self ..) hp, Nat.zero_add]
      exact ih (fun x hx hpx => h x (List.mem_cons_of_mem _ hx) hpx)

/-- Sums split along a Boolean predicate. -/
theorem ssum_filter_add (p : α → Bool) (l : List α) (f : α → Nat) :
    ssum l f = ssum (l.filter p) f + ssum (l.filter (fun x => !p x)) f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [ssum_cons]
    cases hp : p a with
    | true =>
      have hrw1 : (a :: l).filter p = a :: l.filter p := by simp [List.filter, hp]
      have hrw2 : (a :: l).filter (fun x => !p x) = l.filter (fun x => !p x) := by
        simp [List.filter, hp]
      rw [hrw1, hrw2, ssum_cons, ih]; omega
    | false =>
      have hrw1 : (a :: l).filter p = l.filter p := by simp [List.filter, hp]
      have hrw2 : (a :: l).filter (fun x => !p x) = a :: l.filter (fun x => !p x) := by
        simp [List.filter, hp]
      rw [hrw1, hrw2, ssum_cons, ih]; omega

/-- In a duplicate-free list, "sum of `g` at the position of `y`" is `g y`. -/
theorem ssum_eq_single [DecidableEq α] {l : List α} (nd : l.Nodup) {y : α}
    (hy : y ∈ l) (g : α → Nat) :
    ssum l (fun i => if i = y then g i else 0) = g y := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rw [List.nodup_cons] at nd
    rw [List.mem_cons] at hy
    rw [ssum_cons]
    cases hy with
    | inl hay =>
      -- hay : y = a
      have h0 : ssum l (fun i => if i = y then g i else 0) = 0 := by
        apply ssum_eq_zero
        intro x hx
        have hne : x ≠ y := by
          intro hxy
          exact nd.1 (hay ▸ hxy ▸ hx)
        simp [hne]
      have h1 : (if a = y then g a else 0) = g y := by rw [hay]; simp
      rw [h1, h0, Nat.add_zero]
    | inr hyl =>
      have hne : ¬ a = y := fun hay => nd.1 (hay ▸ hyl)
      simp [hne]
      exact ih nd.2 hyl

/-- Length of a filter as a weighted sum. -/
theorem filter_length_eq (p : α → Bool) (l : List α) :
    (l.filter p).length = ssum l (fun x => (p x).toNat) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> simp [List.filter, hp, ssum_cons] <;> omega

/-- Filter lengths of a predicate and its negation add up to the list length. -/
theorem filter_length_add (p : α → Bool) (l : List α) :
    (l.filter p).length + (l.filter (fun x => !p x)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases hp : p a <;> simp [List.filter, hp, List.length_cons] <;> omega

/-- In a duplicate-free list containing `y`, exactly one element equals `y`. -/
theorem filter_eq_single_length [DecidableEq α] {l : List α} (nd : l.Nodup)
    {y : α} (hy : y ∈ l) :
    (l.filter (fun x => x == y)).length = 1 := by
  rw [filter_length_eq]
  have hc : (fun i => ((i == y) : Bool).toNat) = (fun i => if i = y then (1 : Nat) else 0) := by
    funext i
    by_cases hiy : i = y <;> simp [hiy]
  rw [hc]
  exact ssum_eq_single nd hy _

/-- Removing one element of a duplicate-free list drops the length by one. -/
theorem length_filter_neq_of_mem [DecidableEq α] {l : List α} (nd : l.Nodup)
    {y : α} (hy : y ∈ l) :
    (l.filter (fun x => !(x == y))).length = l.length - 1 := by
  have h1 := filter_length_add (fun x => x == y) l
  have h2 := filter_eq_single_length nd hy
  have h3 : 1 ≤ l.length := by
    cases l with
    | nil => simp at hy
    | cons a l => simp
  omega

/-! ## More list-sum tools -/

theorem ssum_filter_le (p : α → Bool) (l : List α) (f : α → Nat) :
    ssum (l.filter p) f ≤ ssum l f := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    rw [ssum_cons]
    cases hp : p a with
    | true =>
      have hrw : (a :: l).filter p = a :: l.filter p := by simp [List.filter, hp]
      rw [hrw, ssum_cons]
      exact Nat.add_le_add (Nat.le_refl _) ih
    | false =>
      have hrw : (a :: l).filter p = l.filter p := by simp [List.filter, hp]
      rw [hrw]
      exact Nat.le_add_left_of_le ih

theorem one_le_ssum_of_mem {l : List α} {f : α → Nat} {x : α} (hx : x ∈ l)
    (h : 1 ≤ f x) : 1 ≤ ssum l f := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    rw [List.mem_cons] at hx
    rw [ssum_cons]
    cases hx with
    | inl hxa => rw [← hxa]; omega
    | inr hxl => have := ih hxl; omega

/-- Sum over the `== y` filter picks out `f y` (duplicate-free list). -/
theorem ssum_filter_eq_single [DecidableEq α] {l : List α} (nd : l.Nodup)
    {y : α} (hy : y ∈ l) (f : α → Nat) :
    ssum (l.filter (fun x => x == y)) f = f y := by
  induction l with
  | nil => simp at hy
  | cons a l ih =>
    rw [List.nodup_cons] at nd
    rw [List.mem_cons] at hy
    cases hy with
    | inl hay =>
      -- hay : y = a
      have h1 : (a == y) = true := by rw [← hay]; simp
      have h2 : l.filter (fun x => x == y) = [] := by
        rw [List.filter_eq_nil_iff]
        intro x hx
        have hne : x ≠ y := fun hxy => nd.1 (hay ▸ hxy ▸ hx)
        have h3 : (x == y) = false := by simp [hne]
        simp [h3]
      have hfilter : (a :: l).filter (fun x => x == y) = [a] := by
        simp [List.filter, h1, h2]
      rw [hfilter, ssum_cons, ssum_nil, Nat.add_zero, hay]
    | inr hyl =>
      have hne : (a == y) = false := by
        simp
        intro hay
        exact nd.1 (hay ▸ hyl)
      have hfilter : (a :: l).filter (fun x => x == y) = l.filter (fun x => x == y) := by
        simp [List.filter, hne]
      rw [hfilter]
      exact ih nd.2 hyl

theorem Bool.toNat_le_one : ∀ b : Bool, b.toNat ≤ 1 := fun b => by cases b <;> decide

/-! ## Graphs on `Fin n`, counts relative to a vertex list -/

/-- A simple graph on `Fin n` as a Boolean adjacency matrix. -/
structure Gph (n : Nat) where
  adj : Fin n → Fin n → Bool
  sym : ∀ i j, adj i j = adj j i
  irr : ∀ i, adj i i = false

/-- Degree of `v` within the vertex list `l`. -/
def degIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) (v : Fin n) : Nat :=
  ssum l fun j => (A v j).toNat

/-- Number of edges with both endpoints in `l` (each unordered pair counted once). -/
def ecountIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) : Nat :=
  ssum l fun i => ssum l fun j => if (i : Nat) < (j : Nat) then (A i j).toNat else 0

/-- Indicator term for an ordered triple forming a triangle. -/
def triTerm (A : Fin n → Fin n → Bool) (i j k : Fin n) : Nat :=
  if (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat) then (A i j && A j k && A i k).toNat else 0

/-- Number of triangles inside `l` (each unordered triple counted once). -/
def tcountIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) : Nat :=
  ssum l fun i => ssum l fun j => ssum l fun k => triTerm A i j k

/-- Common-neighbor count of `x` and `y` within `l`. -/
def commonIn (A : Fin n → Fin n → Bool) (l : List (Fin n)) (x y : Fin n) : Nat :=
  ssum l fun j => (A x j && A y j).toNat

/-- Handshake lemma: the degrees in `l` sum to twice the edge count. -/
theorem handshake (G : Gph n) (l : List (Fin n)) :
    ssum l (fun v => degIn G.adj l v) = 2 * ecountIn G.adj l := by
  have pw : ∀ v ∈ l, ∀ j ∈ l, (G.adj v j).toNat =
      (if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0) +
      (if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0) := by
    intro v _ j _
    by_cases h1 : (v : Nat) < (j : Nat)
    · have h2 : ¬ (j : Nat) < (v : Nat) := by omega
      simp [h1, h2]
    · by_cases h2 : (j : Nat) < (v : Nat)
      · simp [h1, h2]
      · have h3 : v = j := Fin.ext (by omega)
        rw [h3]
        simp [G.irr]
  calc ssum l (fun v => degIn G.adj l v)
      = ssum l (fun v => ssum l (fun j =>
          (if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0) +
          (if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0))) :=
        ssum_congr fun v hv => ssum_congr fun j hj => pw v hv j hj
    _ = ssum l (fun v => ssum l (fun j => if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0) +
            ssum l (fun j => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) :=
        ssum_congr fun v _ => ssum_add _ _ _
    _ = ssum l (fun v => ssum l (fun j => if (v : Nat) < (j : Nat) then (G.adj v j).toNat else 0)) +
        ssum l (fun v => ssum l (fun j => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) :=
        ssum_add _ _ _
    _ = ecountIn G.adj l +
        ssum l (fun j => ssum l (fun v => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) := by
        have hs := ssum_swap l l (fun v j => if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)
        show ecountIn G.adj l + ssum l (fun v => ssum l (fun j =>
              if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0)) = _
        rw [hs]
    _ = 2 * ecountIn G.adj l := by
        have h : ∀ j ∈ l, ∀ v ∈ l,
            (if (j : Nat) < (v : Nat) then (G.adj v j).toNat else 0) =
            (if (j : Nat) < (v : Nat) then (G.adj j v).toNat else 0) :=
          fun j _ v _ => by rw [G.sym j v]
        rw [ssum_congr fun j hj => ssum_congr fun v hv => h j hj v hv]
        show ecountIn G.adj l + ecountIn G.adj l = 2 * ecountIn G.adj l
        omega

/-- Pigeonhole: `deg x + deg y ≤ |l| + |common neighbors|`. -/
theorem deg_add_le (G : Gph n) (l : List (Fin n)) (x y : Fin n) :
    degIn G.adj l x + degIn G.adj l y ≤ l.length + commonIn G.adj l x y := by
  have pw : ∀ j ∈ l, (G.adj x j).toNat + (G.adj y j).toNat ≤
      1 + (G.adj x j && G.adj y j).toNat := by
    intro j _
    generalize G.adj x j = b1
    generalize G.adj y j = b2
    cases b1 <;> cases b2 <;> decide
  calc degIn G.adj l x + degIn G.adj l y
      = ssum l (fun j => (G.adj x j).toNat + (G.adj y j).toNat) := (ssum_add _ _ _).symm
    _ ≤ ssum l (fun j => 1 + (G.adj x j && G.adj y j).toNat) := ssum_le pw
    _ = ssum l (fun _ => 1) + commonIn G.adj l x y := ssum_add _ _ _
    _ = l.length + commonIn G.adj l x y := by rw [ssum_const, Nat.one_mul]

/-! ## Boolean helpers -/

theorem bool_true_of_toNat_pos {a : Bool} (h : 1 ≤ a.toNat) : a = true := by
  cases a <;> simp at h ⊢

theorem bool_and_true_of_toNat_pos {a b : Bool} (h : 1 ≤ (a && b).toNat) :
    a = true ∧ b = true := by
  cases a <;> cases b <;> simp at h ⊢

/-! ## Vertex removal and degree/edge counts -/

/-- Degrees split off a vertex `y`. -/
theorem degIn_filter_add (G : Gph n) {l : List (Fin n)} (nd : l.Nodup) {y : Fin n}
    (hy : y ∈ l) (x : Fin n) :
    degIn G.adj l x = (G.adj x y).toNat + degIn G.adj (l.filter fun v => !(v == y)) x := by
  have h := ssum_filter_add (fun v => v == y) l (fun j => (G.adj x j).toNat)
  rw [ssum_filter_eq_single nd hy] at h
  exact h

/-- The vertex list with `y` removed. -/
def delVertex (l : List (Fin n)) (y : Fin n) : List (Fin n) := l.filter fun v => !(v == y)

/-- Edge count splits off a vertex `y` (nodup list, `y ∈ l`). -/
theorem ecountIn_eq_filter_add_deg (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    {y : Fin n} (hy : y ∈ l) :
    ecountIn G.adj l =
      degIn G.adj l y + ecountIn G.adj (delVertex l y) := by
  have memL' : ∀ x ∈ delVertex l y, x ≠ y := by
    intro x hx
    have h := (List.mem_filter.mp hx).2
    intro hxy
    rw [hxy] at h
    simp at h
  -- Per-vertex inner sum splits at `j = y`.
  have hInner : ∀ i ∈ l, ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) =
      (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0) +
      ssum (delVertex l y) (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) := by
    intro i _
    have h := ssum_filter_add (fun v => v == y) l
      (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)
    rw [ssum_filter_eq_single nd hy] at h
    exact h
  -- Sum over `i`: split at `i = y`.
  have hOuter : ecountIn G.adj l =
      ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) +
      ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by
    have h := ssum_filter_add (fun v => !(v == y)) l
      (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0))
    have hs : ssum (l.filter fun v => !(!(v == y)))
        (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
        ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by
      have hsingle := ssum_filter_eq_single nd hy
        (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0))
      have hcongr : ssum (l.filter fun v => !(!(v == y)))
          (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
          ssum (l.filter fun v => v == y)
          (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) := by
        have hfilter : (l.filter fun v => !(!(v == y))) = l.filter fun v => v == y := by
          induction l with
          | nil => rfl
          | cons a l ih =>
            cases hpa : (a == y) <;> simp [List.filter, hpa] <;> exact ih
        rw [hfilter]
      rw [hcongr]
      exact hsingle
    rw [hs] at h
    exact h
  -- Combine: inner sums over `i ∈ delVertex l y`.
  have hMid : ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
      ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0)) +
      ecountIn G.adj (delVertex l y) := by
    have h1 : ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) =
        ssum (delVertex l y) (fun i => ((if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0) +
          ssum (delVertex l y) (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0))) :=
      ssum_congr fun i hi => hInner i ((List.mem_filter.mp hi).1)
    rw [h1, ssum_add]
    rfl
  have hRow : ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) =
      ssum (delVertex l y) (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by
    have h := ssum_filter_add (fun v => !(v == y)) l
      (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0)
    have hz : ssum (l.filter fun v => !(!(v == y)))
        (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) = 0 := by
      apply ssum_eq_zero
      intro x hx
      have hx2 := (List.mem_filter.mp hx).2
      have hxy : x = y := by
        simp only [Bool.not_not] at hx2
        exact beq_iff_eq.mp hx2
      rw [hxy]
      simp
    rw [hz, Nat.add_zero] at h
    exact h
  have h2 : ∀ j ∈ delVertex l y, (G.adj y j).toNat =
      (if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
      (if (j : Nat) < (y : Nat) then (G.adj y j).toNat else 0) := by
    intro j hj
    have hjy : j ≠ y := memL' j hj
    by_cases h1 : (y : Nat) < (j : Nat)
    · have h2 : ¬ (j : Nat) < (y : Nat) := by omega
      simp [h1, h2]
    · have h2 : (j : Nat) < (y : Nat) := by
        have hne : (j : Nat) ≠ (y : Nat) := fun heq => hjy (Fin.ext heq)
        omega
      simp [h1, h2]
  have hDeg : ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
        ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0)) =
      degIn G.adj l y := by
    calc ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
          ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0))
        = ssum (delVertex l y) (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
          ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0)) := by
          rw [hRow]
      _ = ssum (delVertex l y) (fun j => (if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) +
            (if (j : Nat) < (y : Nat) then (G.adj y j).toNat else 0)) := (ssum_add _ _ _).symm
      _ = ssum (delVertex l y) (fun j => (G.adj y j).toNat) :=
          ssum_congr fun j hj => (h2 j hj).symm
      _ = degIn G.adj l y := by
          have h4 : degIn G.adj l y = (G.adj y y).toNat + degIn G.adj (delVertex l y) y :=
            degIn_filter_add G nd hy y
          rw [G.irr y] at h4
          simp at h4
          exact h4.symm
  -- Assemble.
  calc ecountIn G.adj l
      = ssum (delVertex l y) (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0)) +
        ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := hOuter
    _ = (ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0)) +
          ecountIn G.adj (delVertex l y)) +
        ssum l (fun j => if (y : Nat) < (j : Nat) then (G.adj y j).toNat else 0) := by rw [hMid]
    _ = degIn G.adj l y + ecountIn G.adj (delVertex l y) := by
        have h5 : ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj i y).toNat else 0)) =
            ssum (delVertex l y) (fun i => (if (i : Nat) < (y : Nat) then (G.adj y i).toNat else 0)) :=
          ssum_congr fun i _ => by rw [G.sym i y]
        rw [h5]
        omega

/-- The second triangle of infrastructure: edge existence from a positive count. -/
theorem exists_edge_of_pos (G : Gph n) {l : List (Fin n)} (h : 1 ≤ ecountIn G.adj l) :
    ∃ i ∈ l, ∃ j ∈ l, (i : Nat) < (j : Nat) ∧ G.adj i j = true := by
  obtain ⟨i, hi, hpi⟩ := ssum_pos_of_pos h
  obtain ⟨j, hj, hpj⟩ := ssum_pos_of_pos hpi
  have hij : (i : Nat) < (j : Nat) := by
    by_cases hc : (i : Nat) < (j : Nat)
    · exact hc
    · simp [hc] at hpj
  have hA : G.adj i j = true := by
    have h1 : (if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) = (G.adj i j).toNat := by
      simp [hij]
    rw [h1] at hpj
    exact bool_true_of_toNat_pos hpj
  exact ⟨i, hi, j, hj, hij, hA⟩

/-- Edge count is tiny on lists of length at most 2. -/
theorem ecountIn_le_of_length_le_two (A : Fin n → Fin n → Bool) {l : List (Fin n)}
    (h : l.length ≤ 2) : ecountIn A l ≤ l.length - 1 := by
  cases l with
  | nil => simp [ecountIn, ssum]
  | cons a l =>
    cases l with
    | nil =>
      have hz : ecountIn A [a] = 0 := by
        simp [ecountIn, ssum_cons, ssum_nil]
      simp [hz]
    | cons b l =>
      cases l with
      | nil =>
        have hexp : ecountIn A [a, b] =
            (if (a : Nat) < (b : Nat) then (A a b).toNat else 0) +
            (if (b : Nat) < (a : Nat) then (A b a).toNat else 0) := by
          simp [ecountIn, ssum_cons, ssum_nil]
        rw [hexp]
        by_cases h1 : (a : Nat) < (b : Nat)
        · have h2 : ¬ (b : Nat) < (a : Nat) := by omega
          simp [h1, h2]
          exact Bool.toNat_le_one _
        · by_cases h2 : (b : Nat) < (a : Nat)
          · simp [h1, h2]
            exact Bool.toNat_le_one _
          · simp [h1, h2]
      | cons c l => simp at h

/-! ## Mantel's theorem -/

/-- Mantel's theorem (list form): more than `⌊m²/4⌋` edges force a triangle. -/
theorem mantel (G : Gph n) : ∀ m : Nat, ∀ l : List (Fin n), l.Nodup → l.length = m →
    m * m / 4 + 1 ≤ ecountIn G.adj l →
    ∃ x ∈ l, ∃ y ∈ l, ∃ z ∈ l, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧
      G.adj x y = true ∧ G.adj x z = true ∧ G.adj y z = true := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro l nd hm he
    by_cases hm2 : m ≤ 2
    · have hb : ecountIn G.adj l ≤ l.length - 1 := ecountIn_le_of_length_le_two G.adj (by omega)
      rw [hm] at hb
      have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      obtain h0 | h1 | h2 := h2
      · subst h0; omega
      · subst h1; omega
      · subst h2; omega
    · have hm3 : 3 ≤ m := by omega
      have hpos : 1 ≤ ecountIn G.adj l := by omega
      obtain ⟨x, hx, y, hy, hxy, hAxy⟩ := exists_edge_of_pos G hpos
      have hxy' : x ≠ y := by intro h; rw [h] at hxy; omega
      by_cases hdeg : degIn G.adj l x + degIn G.adj l y ≤ m
      · -- Delete both endpoints; the rest still has enough edges.
        have nd₁ : (l.filter fun v => !(v == y)).Nodup := nd.filter _
        have hx₁ : x ∈ l.filter (fun v => !(v == y)) := by
          have h : (!(x == y)) = true := by simp [hxy']
          exact List.mem_filter.mpr ⟨hx, h⟩
        have hE1 := ecountIn_eq_filter_add_deg G nd hy
        have hE2 := ecountIn_eq_filter_add_deg G nd₁ hx₁
        simp only [delVertex] at hE1 hE2
        have hd : degIn G.adj (l.filter fun v => !(v == y)) x + 1 = degIn G.adj l x := by
          have h := degIn_filter_add G nd hy x
          rw [hAxy] at h
          simp at h
          omega
        have nd₂ : ((l.filter fun v => !(v == y)).filter fun v => !(v == x)).Nodup := nd₁.filter _
        have hlen2 : ((l.filter fun v => !(v == y)).filter fun v => !(v == x)).length = m - 2 := by
          have h1 : (l.filter fun v => !(v == y)).length = m - 1 := by
            have h := length_filter_neq_of_mem nd hy
            rwa [hm] at h
          have h2 := length_filter_neq_of_mem nd₁ hx₁
          rw [h1] at h2
          exact h2
        have hE : (m - 2) * (m - 2) / 4 + 1 ≤
            ecountIn G.adj ((l.filter fun v => !(v == y)).filter fun v => !(v == x)) := by
          obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
          have hk2 : m - 2 = k := by omega
          have hexp : (k + 2) * (k + 2) = k * k + 4 * k + 4 := by
            rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega
          rw [hk] at he hdeg
          rw [hexp] at he
          rw [hk2]
          omega
        obtain ⟨x', hx', y', hy', z', hz', h1', h2', h3', h4', h5', h6'⟩ :=
          ih (m - 2) (by omega) _ nd₂ hlen2 hE
        exact ⟨x', (List.mem_filter.mp (List.mem_filter.mp hx').1).1,
               y', (List.mem_filter.mp (List.mem_filter.mp hy').1).1,
               z', (List.mem_filter.mp (List.mem_filter.mp hz').1).1,
               h1', h2', h3', h4', h5', h6'⟩
      · -- High degree sum: a common neighbor exists.
        have hcom := deg_add_le G l x y
        rw [hm] at hcom
        have hcm : 1 ≤ commonIn G.adj l x y := by omega
        obtain ⟨z, hz, hz1⟩ := ssum_pos_of_pos hcm
        obtain ⟨hxz, hyz⟩ := bool_and_true_of_toNat_pos hz1
        have hzx : z ≠ x := by
          intro h; rw [h, G.irr] at hxz; simp at hxz
        have hzy : z ≠ y := by
          intro h; rw [h, G.irr] at hyz; simp at hyz
        exact ⟨x, hx, y, hy, z, hz, hxy', hzx.symm, hzy.symm, hAxy, hxz, hyz⟩

/-! ## Edge deletion -/

/-- The graph with edge `{u,v}` removed. -/
def deleteEdge (G : Gph n) (u v : Fin n) : Gph n where
  adj := fun i j => if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then false else G.adj i j
  sym := by
    intro i j
    have hswap : ∀ a b : Fin n, ((a = u ∧ b = v) ∨ (a = v ∧ b = u)) →
        ((b = u ∧ a = v) ∨ (b = v ∧ a = u)) := by
      intro a b h
      cases h with
      | inl h1 => exact Or.inr ⟨h1.2, h1.1⟩
      | inr h1 => exact Or.inl ⟨h1.2, h1.1⟩
    show (if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then false else G.adj i j) =
         (if (j = u ∧ i = v) ∨ (j = v ∧ i = u) then false else G.adj j i)
    by_cases h : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
    · have h' := hswap i j h
      simp [h, h']
    · by_cases h' : (j = u ∧ i = v) ∨ (j = v ∧ i = u)
      · exact absurd (hswap j i h') h
      · simp [h, h', G.sym i j]
  irr := by
    intro i
    show (if (i = u ∧ i = v) ∨ (i = v ∧ i = u) then false else G.adj i i) = false
    by_cases h : (i = u ∧ i = v) ∨ (i = v ∧ i = u)
    · simp [h]
    · simp [h, G.irr i]

theorem deleteEdge_adj_eq (G : Gph n) (u v i j : Fin n) :
    (deleteEdge G u v).adj i j =
      (if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then false else G.adj i j) := rfl

theorem deleteEdge_adj_true {G : Gph n} {u v a b : Fin n}
    (h : (deleteEdge G u v).adj a b = true) : G.adj a b = true := by
  rw [deleteEdge_adj_eq] at h
  by_cases hc : (a = u ∧ b = v) ∨ (a = v ∧ b = u)
  · simp [hc] at h
  · simp [hc] at h
    exact h

/-- Triangle count is monotone under edge deletion. -/
theorem tcountIn_deleteEdge_le (G : Gph n) (u v : Fin n) (l : List (Fin n)) :
    tcountIn (deleteEdge G u v).adj l ≤ tcountIn G.adj l := by
  apply ssum_le; intro i _
  apply ssum_le; intro j _
  apply ssum_le; intro k _
  simp only [triTerm]
  by_cases hc : (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat)
  · simp [hc]
    by_cases h1 : (deleteEdge G u v).adj i j = true
    · have h1' : G.adj i j = true := deleteEdge_adj_true h1
      by_cases h2 : (deleteEdge G u v).adj j k = true
      · have h2' : G.adj j k = true := deleteEdge_adj_true h2
        by_cases h3 : (deleteEdge G u v).adj i k = true
        · have h3' : G.adj i k = true := deleteEdge_adj_true h3
          simp [h1, h1', h2, h2', h3, h3']
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [hc]

/-- Deleting an existing edge drops the edge count by exactly one. -/
theorem ecountIn_deleteEdge (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    {u v : Fin n} (hu : u ∈ l) (hv : v ∈ l) (huv : u ≠ v) (hA : G.adj u v = true) :
    ecountIn (deleteEdge G u v).adj l + 1 = ecountIn G.adj l := by
  have hAvu : G.adj v u = true := by
    rw [G.sym v u]; exact hA
  have pw : ∀ i ∈ l, ∀ j ∈ l,
      (if (i : Nat) < (j : Nat) then (G.adj i j).toNat else 0) =
      (if (i : Nat) < (j : Nat) then ((deleteEdge G u v).adj i j).toNat else 0) +
      (if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then 1 else 0) := by
    intro i _ j _
    by_cases hp : (i = u ∧ j = v) ∨ (i = v ∧ j = u)
    · have hAij : G.adj i j = true := by
        cases hp with
        | inl h1 => rw [h1.1, h1.2]; exact hA
        | inr h1 => rw [h1.1, h1.2]; exact hAvu
      have hD : (deleteEdge G u v).adj i j = false := by
        rw [deleteEdge_adj_eq]; simp [hp]
      by_cases hij : (i : Nat) < (j : Nat)
      · simp [hij, hAij, hD, hp]
      · simp [hij, hp]
    · have hD : (deleteEdge G u v).adj i j = G.adj i j := by
        rw [deleteEdge_adj_eq]; simp [hp]
      by_cases hij : (i : Nat) < (j : Nat)
      · simp [hij, hD, hp]
      · simp [hij, hp]
  -- The correction term totals exactly 1.
  have hΔ : ssum l (fun i => ssum l (fun j =>
        if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) = 1 := by
    have hsplit : ∀ i ∈ l, ∀ j ∈ l,
        (if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0) =
        (if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then 1 else 0) +
        (if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then 1 else 0) := by
      intro i _ j _
      by_cases h1 : i = u ∧ j = v
      · by_cases h2 : i = v ∧ j = u
        · obtain ⟨hi1, -⟩ := h1
          obtain ⟨hi2, -⟩ := h2
          exact absurd (hi1.symm.trans hi2) huv
        · by_cases h3 : (i : Nat) < (j : Nat)
          · simp [h1, huv]
          · simp [h1, huv]
      · by_cases h2 : i = v ∧ j = u
        · by_cases h3 : (i : Nat) < (j : Nat)
          · simp [h2, huv]
          · simp [h2, huv]
        · by_cases h3 : (i : Nat) < (j : Nat) <;> simp [h1, h2, h3]
    have hΔ1 : ssum l (fun i => ssum l (fun j =>
        if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) =
        (if (u : Nat) < (v : Nat) then 1 else 0) := by
      have hcomp2 : ∀ i ∈ l, ssum l (fun j => if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if i = u then ssum l (fun j => if j = v ∧ (i : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro i _
        by_cases h : i = u
        · simp [h]
        · have hz : ssum l (fun j => if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) = 0 :=
            ssum_eq_zero fun j _ => by simp [h]
          rw [hz]; simp [h]
      rw [ssum_congr fun i hi => hcomp2 i hi, ssum_eq_single nd hu]
      have hcomp3 : ∀ j ∈ l, (if j = v ∧ (u : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if j = v then (if (u : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro j _; by_cases h : j = v <;> simp [h]
      rw [ssum_congr hcomp3, ssum_eq_single nd hv]
    have hΔ2 : ssum l (fun i => ssum l (fun j =>
        if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) =
        (if (v : Nat) < (u : Nat) then 1 else 0) := by
      have hcomp2 : ∀ i ∈ l, ssum l (fun j => if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if i = v then ssum l (fun j => if j = u ∧ (i : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro i _
        by_cases h : i = v
        · simp [h]
        · have hz : ssum l (fun j => if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0) = 0 :=
            ssum_eq_zero fun j _ => by simp [h]
          rw [hz]; simp [h]
      rw [ssum_congr fun i hi => hcomp2 i hi, ssum_eq_single nd hv]
      have hcomp3 : ∀ j ∈ l, (if j = u ∧ (v : Nat) < (j : Nat) then (1 : Nat) else 0) =
          if j = u then (if (v : Nat) < (j : Nat) then 1 else 0) else 0 := by
        intro j _; by_cases h : j = u <;> simp [h]
      rw [ssum_congr hcomp3, ssum_eq_single nd hu]
    calc ssum l (fun i => ssum l (fun j =>
            if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0))
        = ssum l (fun i => ssum l (fun j =>
            (if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then 1 else 0) +
            (if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then 1 else 0))) :=
          ssum_congr fun i hi => ssum_congr fun j hj => hsplit i hi j hj
      _ = ssum l (fun i => ssum l (fun j => if i = u ∧ j = v ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) +
          ssum l (fun i => ssum l (fun j => if i = v ∧ j = u ∧ (i : Nat) < (j : Nat) then (1 : Nat) else 0)) := by
          rw [ssum_congr fun i _ => ssum_add _ _ _, ssum_add]
      _ = (if (u : Nat) < (v : Nat) then 1 else 0) + (if (v : Nat) < (u : Nat) then 1 else 0) := by
          rw [hΔ1, hΔ2]
      _ = 1 := by
          have huv2 : (u : Nat) ≠ (v : Nat) := fun h => huv (Fin.ext h)
          by_cases h1 : (u : Nat) < (v : Nat) <;> by_cases h2 : (v : Nat) < (u : Nat) <;>
            simp [h1, h2] <;> omega
  -- Assemble.
  have hsum : ecountIn G.adj l =
      ecountIn (deleteEdge G u v).adj l +
      ssum l (fun i => ssum l (fun j =>
        if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) := by
    calc ecountIn G.adj l
        = ssum l (fun i => ssum l (fun j =>
            (if (i : Nat) < (j : Nat) then ((deleteEdge G u v).adj i j).toNat else 0) +
            (if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then 1 else 0))) :=
          ssum_congr fun i hi => ssum_congr fun j hj => pw i hi j hj
      _ = ssum l (fun i => ssum l (fun j => if (i : Nat) < (j : Nat) then ((deleteEdge G u v).adj i j).toNat else 0)) +
          ssum l (fun i => ssum l (fun j =>
            if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) := by
          rw [ssum_congr fun i _ => ssum_add _ _ _, ssum_add]
      _ = ecountIn (deleteEdge G u v).adj l +
          ssum l (fun i => ssum l (fun j =>
            if (i : Nat) < (j : Nat) ∧ ((i = u ∧ j = v) ∨ (i = v ∧ j = u)) then (1 : Nat) else 0)) := by
          rfl
  omega

/-! ## Triangles through a vertex -/

/-- Removing vertex `y` destroys at least one triangle when `y` lies on one. -/
theorem tcountIn_ge_delVertex_add_one (G : Gph n) {l : List (Fin n)} (nd : l.Nodup)
    {y u w : Fin n} (hy : y ∈ l) (hu : u ∈ l) (hw : w ∈ l)
    (hyu : y ≠ u) (hyw : y ≠ w) (huw : u ≠ w)
    (h1 : G.adj y u = true) (h2 : G.adj y w = true) (h3 : G.adj u w = true) :
    tcountIn G.adj (delVertex l y) + 1 ≤ tcountIn G.adj l := by
  -- symmetry variants
  have h1' : G.adj u y = true := by rw [G.sym u y]; exact h1
  have h2' : G.adj w y = true := by rw [G.sym w y]; exact h2
  have h3' : G.adj w u = true := by rw [G.sym w u]; exact h3
  -- value-level distinctness
  have vy'u : (y : Nat) ≠ (u : Nat) := fun h => hyu (Fin.ext h)
  have vy'w : (y : Nat) ≠ (w : Nat) := fun h => hyw (Fin.ext h)
  have vu'w : (u : Nat) ≠ (w : Nat) := fun h => huw (Fin.ext h)
  -- the `== y` filter is the complement of `delVertex`
  have hfeq : (l.filter fun v => !(!(v == y))) = l.filter fun v => v == y := by
    induction l with
    | nil => rfl
    | cons a l ih =>
      cases hpa : (a == y) <;> simp [List.filter, hpa] <;> exact ih
  -- monotonicity of inner sums under filtering
  have hmono : ∀ i ∈ delVertex l y,
      ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj i j k)) ≤
      ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)) := by
    intro i _
    exact Nat.le_trans (ssum_le fun j _ => ssum_filter_le _ _ _) (ssum_filter_le _ _ _)
  have hle : tcountIn G.adj (delVertex l y) ≤
      ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
    ssum_le hmono
  have hle' : ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) ≤
      tcountIn G.adj l := ssum_filter_le _ _ _
  have hsplit := ssum_filter_add (fun v => !(v == y)) l
    (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)))
  rw [hfeq, ssum_filter_eq_single nd hy] at hsplit
  -- hsplit : tcountIn l = ssum l' F + F y  (up to the delVertex/filter defeq)
  -- case split on the rank of y among {u, w}
  by_cases hA : (y : Nat) < (u : Nat) ∧ (y : Nat) < (w : Nat)
  · -- y is the smallest: the triangle shows up at `i = y`.
    obtain ⟨u', hu'mem, hu'eq, w', hw'mem, hw'eq, hord⟩ :
        ∃ u' ∈ l, (u' = u ∨ u' = w) ∧ ∃ w' ∈ l, (w' = u ∨ w' = w) ∧ (u' : Nat) < (w' : Nat) := by
      by_cases huw2 : (u : Nat) < (w : Nat)
      · exact ⟨u, hu, Or.inl rfl, w, hw, Or.inr rfl, huw2⟩
      · exact ⟨w, hw, Or.inr rfl, u, hu, Or.inl rfl, by omega⟩
    have hyu' : (y : Nat) < (u' : Nat) := by
      cases hu'eq with
      | inl h => rw [h]; omega
      | inr h => rw [h]; omega
    have hterm : triTerm G.adj y u' w' = 1 := by
      have e1 : G.adj y u' = true := by cases hu'eq with | inl h => rw [h]; exact h1 | inr h => rw [h]; exact h2
      have e3 : G.adj u' w' = true := by
        cases hu'eq with
        | inl ha => cases hw'eq with
          | inl hb => rw [ha, hb] at hord; omega
          | inr hb => rw [ha, hb]; exact h3
        | inr ha => cases hw'eq with
          | inl hb => rw [ha, hb]; exact h3'
          | inr hb => rw [ha, hb] at hord; omega
      have e2 : G.adj y w' = true := by cases hw'eq with | inl h => rw [h]; exact h1 | inr h => rw [h]; exact h2
      simp [triTerm, hyu', hord, e1, e3, e2]
    have hFy : 1 ≤ ssum l (fun j => ssum l (fun k => triTerm G.adj y j k)) :=
      one_le_ssum_of_mem hu'mem (one_le_ssum_of_mem hw'mem (by simp [hterm]))
    -- tcountIn l = ssum l' F + F y ≥ tcountIn l' + 1
    have hsplit2 : tcountIn G.adj l =
        ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) +
        ssum l (fun j => ssum l (fun k => triTerm G.adj y j k)) := hsplit
    omega
  · -- y is not smallest
    by_cases hB : (u : Nat) < (y : Nat) ∧ (y : Nat) < (w : Nat)
    · -- middle: u < y < w, strict at `j = y` inside `F u`
      have hGy : 1 ≤ ssum l (fun k => triTerm G.adj u y k) :=
        one_le_ssum_of_mem hw (by
          have ht : triTerm G.adj u y w = 1 := by
            simp [triTerm, hB.1, hB.2, h1', h2, h3]
          simp [ht])
      have huL' : u ∈ delVertex l y := by
        have hb : (!(u == y)) = true := by simp [hyu.symm]
        exact List.mem_filter.mpr ⟨hu, hb⟩
      have hrow : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) + 1 ≤
          ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) := by
        have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) ≤
            ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) :=
          ssum_le fun j _ => ssum_filter_le _ _ _
        have h2 : ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) + 1 ≤
            ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) := by
          have hsp := ssum_filter_add (fun v => v == y) l (fun j => ssum l (fun k => triTerm G.adj u j k))
          rw [ssum_filter_eq_single nd hy] at hsp
          have hsp2 : ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) =
              ssum l (fun k => triTerm G.adj u y k) +
              ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) := hsp
          omega
        omega
      have htot : tcountIn G.adj (delVertex l y) + 1 ≤
          ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) := by
        have hpoint : ∀ i ∈ delVertex l y,
            ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj i j k)) ≤
            ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)) := hmono
        exact ssum_add_one_le hpoint u huL' hrow
      omega
    · -- largest: both u, w < y (or w < y < u handled symmetrically via roles)
      by_cases hC : (w : Nat) < (y : Nat) ∧ (y : Nat) < (u : Nat)
      · -- middle with roles of u, w swapped: w < y < u
        have hGy : 1 ≤ ssum l (fun k => triTerm G.adj w y k) :=
          one_le_ssum_of_mem hu (by
            have ht : triTerm G.adj w y u = 1 := by
              simp [triTerm, hC.1, hC.2, h2', h1, h3']
            simp [ht])
        have hwL' : w ∈ delVertex l y := by
          have hb : (!(w == y)) = true := by simp [hyw.symm]
          exact List.mem_filter.mpr ⟨hw, hb⟩
        have hrow : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) + 1 ≤
            ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) := by
          have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) ≤
              ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) :=
            ssum_le fun j _ => ssum_filter_le _ _ _
          have h2 : ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) + 1 ≤
              ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) := by
            have hsp := ssum_filter_add (fun v => v == y) l (fun j => ssum l (fun k => triTerm G.adj w j k))
            rw [ssum_filter_eq_single nd hy] at hsp
            have hsp2 : ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) =
                ssum l (fun k => triTerm G.adj w y k) +
                ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) := hsp
            omega
          omega
        have htot : tcountIn G.adj (delVertex l y) + 1 ≤
            ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
          ssum_add_one_le hmono w hwL' hrow
        omega
      · -- largest: u < y and w < y. Let a = min u w, b = max u w: strict at k = y inside row b.
        have huy : (u : Nat) < (y : Nat) := by omega
        have hwy : (w : Nat) < (y : Nat) := by omega
        by_cases huw2 : (u : Nat) < (w : Nat)
        · -- a = u, b = w: strict at j = w (row u), k = y
          have hterm : triTerm G.adj u w y = 1 := by
            simp [triTerm, huw2, hwy, h3, h2', h1']
          have hHw : 1 ≤ ssum l (fun k => triTerm G.adj u w k) :=
            one_le_ssum_of_mem hy (by simp [hterm])
          have hroww : ssum (delVertex l y) (fun k => triTerm G.adj u w k) + 1 ≤
              ssum l (fun k => triTerm G.adj u w k) := by
            have hsp := ssum_filter_add (fun v => v == y) l (fun k => triTerm G.adj u w k)
            rw [ssum_filter_eq_single nd hy] at hsp
            have hsp2 : ssum l (fun k => triTerm G.adj u w k) =
                triTerm G.adj u w y + ssum (delVertex l y) (fun k => triTerm G.adj u w k) := hsp
            omega
          have hwL' : w ∈ delVertex l y := by
            have hb : (!(w == y)) = true := by simp [hyw.symm]
            exact List.mem_filter.mpr ⟨hw, hb⟩
          have hrowu : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) + 1 ≤
              ssum l (fun j => ssum l (fun k => triTerm G.adj u j k)) := by
            have hpoint : ∀ j ∈ delVertex l y, ssum (delVertex l y) (fun k => triTerm G.adj u j k) ≤
                ssum l (fun k => triTerm G.adj u j k) := fun j _ => ssum_filter_le _ _ _
            have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj u j k)) + 1 ≤
                ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj u j k)) :=
              ssum_add_one_le hpoint w hwL' hroww
            exact Nat.le_trans h1 (ssum_filter_le _ _ _)
          have huL' : u ∈ delVertex l y := by
            have hb : (!(u == y)) = true := by simp [hyu.symm]
            exact List.mem_filter.mpr ⟨hu, hb⟩
          have htot : tcountIn G.adj (delVertex l y) + 1 ≤
              ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
            ssum_add_one_le hmono u huL' hrowu
          omega
        · -- a = w, b = u
          have hterm : triTerm G.adj w u y = 1 := by
            have hwu : (w : Nat) < (u : Nat) := by omega
            simp [triTerm, hwu, huy, h3', h1', h2']
          have hHu : 1 ≤ ssum l (fun k => triTerm G.adj w u k) :=
            one_le_ssum_of_mem hy (by simp [hterm])
          have hrowu2 : ssum (delVertex l y) (fun k => triTerm G.adj w u k) + 1 ≤
              ssum l (fun k => triTerm G.adj w u k) := by
            have hsp := ssum_filter_add (fun v => v == y) l (fun k => triTerm G.adj w u k)
            rw [ssum_filter_eq_single nd hy] at hsp
            have hsp2 : ssum l (fun k => triTerm G.adj w u k) =
                triTerm G.adj w u y + ssum (delVertex l y) (fun k => triTerm G.adj w u k) := hsp
            omega
          have huL' : u ∈ delVertex l y := by
            have hb : (!(u == y)) = true := by simp [hyu.symm]
            exact List.mem_filter.mpr ⟨hu, hb⟩
          have hroww2 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) + 1 ≤
              ssum l (fun j => ssum l (fun k => triTerm G.adj w j k)) := by
            have hpoint : ∀ j ∈ delVertex l y, ssum (delVertex l y) (fun k => triTerm G.adj w j k) ≤
                ssum l (fun k => triTerm G.adj w j k) := fun j _ => ssum_filter_le _ _ _
            have h1 : ssum (delVertex l y) (fun j => ssum (delVertex l y) (fun k => triTerm G.adj w j k)) + 1 ≤
                ssum (delVertex l y) (fun j => ssum l (fun k => triTerm G.adj w j k)) :=
              ssum_add_one_le hpoint u huL' hrowu2
            exact Nat.le_trans h1 (ssum_filter_le _ _ _)
          have hwL' : w ∈ delVertex l y := by
            have hb : (!(w == y)) = true := by simp [hyw.symm]
            exact List.mem_filter.mpr ⟨hw, hb⟩
          have htot : tcountIn G.adj (delVertex l y) + 1 ≤
              ssum (delVertex l y) (fun i => ssum l (fun j => ssum l (fun k => triTerm G.adj i j k))) :=
            ssum_add_one_le hmono w hwL' hroww2
          omega

/-- Pointwise triangle-term monotonicity under edge deletion. -/
theorem triTerm_deleteEdge_le (G : Gph n) (u v i j k : Fin n) :
    triTerm (deleteEdge G u v).adj i j k ≤ triTerm G.adj i j k := by
  simp only [triTerm]
  by_cases hc : (i : Nat) < (j : Nat) ∧ (j : Nat) < (k : Nat)
  · simp [hc]
    by_cases h1 : (deleteEdge G u v).adj i j = true
    · have h1' : G.adj i j = true := deleteEdge_adj_true h1
      by_cases h2 : (deleteEdge G u v).adj j k = true
      · have h2' : G.adj j k = true := deleteEdge_adj_true h2
        by_cases h3 : (deleteEdge G u v).adj i k = true
        · have h3' : G.adj i k = true := deleteEdge_adj_true h3
          simp [h1, h1', h2, h2', h3, h3']
        · simp [h3]
      · simp [h2]
    · simp [h1]
  · simp [hc]

/-- Deleting an edge that lies on a triangle destroys at least one triangle. -/
theorem tcountIn_deleteEdge_add_one_le (G : Gph n) {l : List (Fin n)}
    {u v w : Fin n} (hu : u ∈ l) (hv : v ∈ l) (hw : w ∈ l)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (h1 : G.adj u v = true) (h2 : G.adj u w = true) (h3 : G.adj v w = true) :
    tcountIn (deleteEdge G u v).adj l + 1 ≤ tcountIn G.adj l := by
  have h1' : G.adj v u = true := by rw [G.sym v u]; exact h1
  have h2' : G.adj w u = true := by rw [G.sym w u]; exact h2
  have h3' : G.adj w v = true := by rw [G.sym w v]; exact h3
  have huv2 : (u : Nat) ≠ (v : Nat) := fun h => huv (Fin.ext h)
  have huw2 : (u : Nat) ≠ (w : Nat) := fun h => huw (Fin.ext h)
  have hvw2 : (v : Nat) ≠ (w : Nat) := fun h => hvw (Fin.ext h)
  -- generic finisher: strict gap at the sorted triple (s1, s2, s3)
  have finish : ∀ (s1 s2 s3 : Fin n), s1 ∈ l → s2 ∈ l → s3 ∈ l →
      triTerm (deleteEdge G u v).adj s1 s2 s3 + 1 ≤ triTerm G.adj s1 s2 s3 →
      tcountIn (deleteEdge G u v).adj l + 1 ≤ tcountIn G.adj l := by
    intro s1 s2 s3 h1m h2m h3m hst
    have hstrict2 : ssum l (fun k => triTerm (deleteEdge G u v).adj s1 s2 k) + 1 ≤
        ssum l (fun k => triTerm G.adj s1 s2 k) :=
      ssum_add_one_le (fun k _ => triTerm_deleteEdge_le G u v s1 s2 k) s3 h3m hst
    have hstrict1 : ssum l (fun j => ssum l (fun k => triTerm (deleteEdge G u v).adj s1 j k)) + 1 ≤
        ssum l (fun j => ssum l (fun k => triTerm G.adj s1 j k)) :=
      ssum_add_one_le (fun j _ => ssum_le (fun k _ => triTerm_deleteEdge_le G u v s1 j k)) s2 h2m hstrict2
    have hmono : ∀ i ∈ l, ssum l (fun j => ssum l (fun k => triTerm (deleteEdge G u v).adj i j k)) ≤
        ssum l (fun j => ssum l (fun k => triTerm G.adj i j k)) :=
      fun i _ => ssum_le (fun j _ => ssum_le (fun k _ => triTerm_deleteEdge_le G u v i j k))
    exact ssum_add_one_le hmono s1 h1m hstrict1
  have hduv : (deleteEdge G u v).adj u v = false := by rw [deleteEdge_adj_eq]; simp
  have hdvu : (deleteEdge G u v).adj v u = false := by rw [deleteEdge_adj_eq]; simp
  by_cases c1 : (u : Nat) < (v : Nat)
  · by_cases c2 : (v : Nat) < (w : Nat)
    · -- u < v < w
      refine finish u v w hu hv hw ?_
      have o2 : (v : Nat) < (w : Nat) := c2
      simp only [triTerm]
      simp [c1, o2, hduv, h1, h2, h3]
    · by_cases c3 : (u : Nat) < (w : Nat)
      · -- u < w < v
        refine finish u w v hu hw hv ?_
        have o2 : (w : Nat) < (v : Nat) := by omega
        simp only [triTerm]
        simp [c3, o2, hduv, h2, h3', h1]
      · -- w < u < v
        refine finish w u v hw hu hv ?_
        have o1 : (w : Nat) < (u : Nat) := by omega
        simp only [triTerm]
        simp [o1, c1, hduv, h2', h3', h1]
  · by_cases c2 : (u : Nat) < (w : Nat)
    · -- v < u < w
      refine finish v u w hv hu hw ?_
      have o1 : (v : Nat) < (u : Nat) := by omega
      simp only [triTerm]
      simp [o1, c2, hdvu, h1', h3, h2]
    · by_cases c3 : (w : Nat) < (v : Nat)
      · -- w < v < u
        refine finish w v u hw hv hu ?_
        have o2 : (v : Nat) < (u : Nat) := by omega
        simp only [triTerm]
        simp [c3, o2, hdvu, h3', h2', h1']
      · -- v < w < u
        refine finish v w u hv hw hu ?_
        have o1 : (v : Nat) < (w : Nat) := by omega
        have o2 : (w : Nat) < (u : Nat) := by omega
        simp only [triTerm]
        simp [o1, o2, hdvu, h3, h2', h1']

/-! ## Shrinking to exactly the threshold -/

/-- If `l` has more than `X` edges, delete edges one at a time until exactly `X`;
triangle count only drops. -/
theorem shrink {n : Nat} {l : List (Fin n)} (nd : l.Nodup) :
    ∀ (G : Gph n) (X : Nat), X ≤ ecountIn G.adj l →
      ∃ G' : Gph n, ecountIn G'.adj l = X ∧ tcountIn G'.adj l ≤ tcountIn G.adj l := by
  intro G X hX
  by_cases hEq : ecountIn G.adj l = X
  · exact ⟨G, hEq, Nat.le_refl _⟩
  · have hgt : X + 1 ≤ ecountIn G.adj l := by omega
    have hpos : 1 ≤ ecountIn G.adj l := by omega
    obtain ⟨i, hi, j, hj, hij, hAij⟩ := exists_edge_of_pos G hpos
    have hij' : i ≠ j := by intro h; rw [h] at hij; omega
    have hcount := ecountIn_deleteEdge G nd hi hj hij' hAij
    have hmono := tcountIn_deleteEdge_le G i j l
    obtain ⟨G', h1', h2'⟩ := shrink nd (deleteEdge G i j) X (by omega)
    exact ⟨G', h1', Nat.le_trans h2' hmono⟩
termination_by G X => ecountIn G.adj l - X

/-! ## Arithmetic helpers -/

theorem sq_two_mul (a : Nat) : (2 * a) * (2 * a) = 4 * (a * a) := by
  calc (2 * a) * (2 * a) = 2 * (a * (2 * a)) := Nat.mul_assoc ..
    _ = 2 * ((2 * a) * a) := by rw [Nat.mul_comm a (2 * a)]
    _ = 2 * (2 * (a * a)) := by rw [Nat.mul_assoc]
    _ = 4 * (a * a) := by rw [← Nat.mul_assoc]

theorem sq_add_one (a : Nat) : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

theorem sq_add_two (a : Nat) : (a + 2) * (a + 2) = a * a + 4 * a + 4 := by
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]; omega

theorem bool_eq_false_of_ne_true {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- Triangle count is monotone under vertex removal. -/
theorem tcountIn_delVertex_le (G : Gph n) (l : List (Fin n)) (y : Fin n) :
    tcountIn G.adj (delVertex l y) ≤ tcountIn G.adj l :=
  Nat.le_trans
    (Nat.le_trans
      (ssum_le fun _ _ => ssum_le fun _ _ => ssum_filter_le _ _ _)
      (ssum_le fun _ _ => ssum_filter_le _ _ _))
    (ssum_filter_le _ _ _)

/-- Base case: a 3-vertex list whose three pairs are all edges has a triangle. -/
theorem base_three (G : Gph n) {a b c : Fin n}
    (h1 : G.adj a b = true) (h2 : G.adj a c = true) (h3 : G.adj b c = true) :
    1 ≤ tcountIn G.adj [a, b, c] := by
  have h1' : G.adj b a = true := by rw [G.sym b a]; exact h1
  have h2' : G.adj c a = true := by rw [G.sym c a]; exact h2
  have h3' : G.adj c b = true := by rw [G.sym c b]; exact h3
  have habv : (a : Nat) ≠ (b : Nat) := by
    intro h
    rw [Fin.ext h, G.irr b] at h1
    exact Bool.noConfusion h1
  have hacv : (a : Nat) ≠ (c : Nat) := by
    intro h
    rw [Fin.ext h, G.irr c] at h2
    exact Bool.noConfusion h2
  have hbcv : (b : Nat) ≠ (c : Nat) := by
    intro h
    rw [Fin.ext h, G.irr c] at h3
    exact Bool.noConfusion h3
  by_cases o1 : (a : Nat) < (b : Nat)
  · by_cases o2 : (b : Nat) < (c : Nat)
    · -- a < b < c
      apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
      apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
      apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
      simp [triTerm, o1, o2, h1, h2, h3]
    · by_cases o3 : (a : Nat) < (c : Nat)
      · by_cases o4 : (c : Nat) < (b : Nat)
        · -- a < c < b
          apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
          simp [triTerm, o3, o4, h2, h3', h1]
        · -- c = b, contradicting h3
          have hce : c = b := Fin.ext (by omega)
          rw [hce, G.irr b] at h3
          exact Bool.noConfusion h3
      · by_cases o4 : (c : Nat) < (a : Nat)
        · -- c < a < b
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self : c ∈ c :: [])))
          apply one_le_ssum_of_mem (List.mem_cons_self : a ∈ a :: b :: c :: [])
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_self : b ∈ b :: c :: []))
          simp [triTerm, o4, o1, h2', h3', h1]
        · -- c = a, contradicting h2
          have hce : c = a := Fin.ext (by omega)
          rw [hce, G.irr a] at h2
          exact Bool.noConfusion h2
  · by_cases o2 : (a : Nat) < (c : Nat)
    · by_cases o3 : (b : Nat) < (a : Nat)
      · -- b < a < c
        apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
        apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
        apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
        simp [triTerm, o3, o2, h1', h2, h3]
      · -- b = a, contradicting h1
        have hbe : b = a := Fin.ext (by omega)
        rw [hbe, G.irr a] at h1
        exact Bool.noConfusion h1
    · by_cases o3 : (b : Nat) < (c : Nat)
      · by_cases o4 : (c : Nat) < (a : Nat)
        · -- b < c < a
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a ((List.mem_cons_self : b ∈ b :: c :: [])))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b ((List.mem_cons_self : c ∈ c :: []))))
          apply one_le_ssum_of_mem ((List.mem_cons_self : a ∈ a :: b :: c :: []))
          simp [triTerm, o3, o4, h3, h2', h1']
        · -- c = a, contradicting h2
          have hce : c = a := Fin.ext (by omega)
          rw [hce, G.irr a] at h2
          exact Bool.noConfusion h2
      · by_cases o5 : (c : Nat) < (b : Nat)
        · -- c < b < a
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_of_mem b (List.mem_cons_self : c ∈ c :: [])))
          apply one_le_ssum_of_mem (List.mem_cons_of_mem a (List.mem_cons_self : b ∈ b :: c :: []))
          apply one_le_ssum_of_mem (List.mem_cons_self : a ∈ a :: b :: c :: [])
          have o6 : (b : Nat) < (a : Nat) := by omega
          simp [triTerm, o5, o6, h2', h3', h1']
        · -- c = b, contradicting h3
          have hce : c = b := Fin.ext (by omega)
          rw [hce, G.irr b] at h3
          exact Bool.noConfusion h3

/-! ## Rademacher's theorem -/

/-- **Rademacher's theorem** (list form): a simple graph with more than
`⌊m²/4⌋` edges among `m` vertices contains at least `⌊m/2⌋` triangles.

Proof: Erdős's 1955 induction (remove a vertex of minimal degree). -/
theorem rademacher_list : ∀ (m : Nat) (n : Nat) (G : Gph n) (l : List (Fin n)), l.Nodup →
    l.length = m → m * m / 4 + 1 ≤ ecountIn G.adj l → m / 2 ≤ tcountIn G.adj l := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro n G l nd hm he
    -- WLOG exactly `⌊m²/4⌋ + 1` edges (deleting edges only lowers the triangle count).
    obtain ⟨G₁, hE1, hmono₁⟩ := shrink nd G (m * m / 4 + 1) he
    refine Nat.le_trans ?_ hmono₁
    by_cases hm2 : m ≤ 2
    · -- Vacuous: too few edges exist.
      have hb : ecountIn G₁.adj l ≤ l.length - 1 := ecountIn_le_of_length_le_two G₁.adj (by omega)
      rw [hm, hE1] at hb
      have h2 : m = 0 ∨ m = 1 ∨ m = 2 := by omega
      obtain h0 | h1 | h2 := h2
      · subst h0; omega
      · subst h1; omega
      · subst h2; omega
    · by_cases hm3 : m = 3
      · -- Base: three vertices, three edges.
        subst hm3
        have h3l : ∃ a b c : Fin n, l = [a, b, c] := by
          cases l with
          | nil => simp at hm
          | cons a l =>
            cases l with
            | nil => simp at hm
            | cons b l =>
              cases l with
              | nil => simp at hm
              | cons c l =>
                cases l with
                | nil => exact ⟨a, b, c, rfl⟩
                | cons d l =>
                  simp only [List.length_cons] at hm
                  omega
        obtain ⟨a, b, c, rfl⟩ := h3l
        have hE : ecountIn G₁.adj [a, b, c] = 3 := by
          have h := hE1
          simp at h
          exact h
        have hexp : ecountIn G₁.adj [a, b, c] ≤
            (G₁.adj a b).toNat + ((G₁.adj a c).toNat + (G₁.adj b c).toNat) := by
          have pairle : ∀ x y : Fin n, (if (x : Nat) < (y : Nat) then (G₁.adj x y).toNat else 0) +
              (if (y : Nat) < (x : Nat) then (G₁.adj y x).toNat else 0) ≤ (G₁.adj x y).toNat := by
            intro x y
            by_cases h : (x : Nat) < (y : Nat)
            · have h2 : ¬ (y : Nat) < (x : Nat) := by omega
              simp [h, h2]
            · by_cases h2 : (y : Nat) < (x : Nat)
              · simp [h, h2, G₁.sym y x]
              · simp [h, h2]
          simp [ecountIn, ssum_cons, ssum_nil]
          rw [G₁.sym b a, G₁.sym c a, G₁.sym c b]
          have p1 := pairle a b
          have p2 := pairle a c
          have p3 := pairle b c
          rw [G₁.sym b a] at p1
          rw [G₁.sym c a] at p2
          rw [G₁.sym c b] at p3
          omega
        have h1 : G₁.adj a b = true := by
          have hb1 := Bool.toNat_le_one (G₁.adj a c)
          have hb2 := Bool.toNat_le_one (G₁.adj b c)
          by_cases h : G₁.adj a b = true
          · exact h
          · have h0 : (G₁.adj a b).toNat = 0 := by simp [bool_eq_false_of_ne_true h]
            omega
        have h2 : G₁.adj a c = true := by
          have hb1 := Bool.toNat_le_one (G₁.adj a b)
          have hb2 := Bool.toNat_le_one (G₁.adj b c)
          by_cases h : G₁.adj a c = true
          · exact h
          · have h0 : (G₁.adj a c).toNat = 0 := by simp [bool_eq_false_of_ne_true h]
            omega
        have h3 : G₁.adj b c = true := by
          have hb1 := Bool.toNat_le_one (G₁.adj a b)
          have hb2 := Bool.toNat_le_one (G₁.adj a c)
          by_cases h : G₁.adj b c = true
          · exact h
          · have h0 : (G₁.adj b c).toNat = 0 := by simp [bool_eq_false_of_ne_true h]
            omega
        have ht := base_three G₁ h1 h2 h3
        exact ht
      · -- Inductive step, m ≥ 4.
        have hm4 : 4 ≤ m := by omega
        obtain ⟨q, hq⟩ : ∃ q, m = 2 * q + 1 ∨ m = 2 * q + 2 := by
          by_cases hodd : m % 2 = 1
          · exact ⟨m / 2, Or.inl (by omega)⟩
          · exact ⟨m / 2 - 1, Or.inr (by omega)⟩
        have hshake : ssum l (fun v => degIn G₁.adj l v) = 2 * ecountIn G₁.adj l := handshake G₁ l
        cases hq with
        | inl hodd =>
          -- m = 2q + 1 odd, q ≥ 2: some vertex has degree ≤ q; delete it.
          have hq2 : 2 ≤ q := by omega
          have hsq1 : m * m = 4 * (q * q) + 4 * q + 1 := by
            rw [hodd, sq_add_one, sq_two_mul]; omega
          rw [hsq1] at hE1
          have hmin : ∃ y ∈ l, degIn G₁.adj l y ≤ q := by
            by_cases hc : ∃ y ∈ l, degIn G₁.adj l y ≤ q
            · exact hc
            · have hall : ∀ v ∈ l, q + 1 ≤ degIn G₁.adj l v := by
                intro v hv
                by_cases hcv : degIn G₁.adj l v ≤ q
                · exact absurd ⟨v, hv, hcv⟩ hc
                · omega
              have hge : ssum l (fun v => degIn G₁.adj l v) ≥ ssum l (fun _ => q + 1) :=
                ssum_ge hall
              rw [ssum_const, hm] at hge
              have hexp4 : (q + 1) * (2 * q + 1) = 2 * (q * q) + 3 * q + 1 := by
                have h1 : q * (2 * q) = 2 * (q * q) := by
                  rw [Nat.mul_comm q (2 * q), Nat.mul_assoc]
                rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                omega
              rw [hodd] at hge
              rw [hexp4] at hge
              omega
          obtain ⟨y, hy, hydeg⟩ := hmin
          have hE' := ecountIn_eq_filter_add_deg G₁ nd hy
          have hlen' : (delVertex l y).length = m - 1 := by
            have h := length_filter_neq_of_mem nd hy
            rwa [hm] at h
          have hnd' : (delVertex l y).Nodup := nd.filter _
          have hE'' : (m - 1) * (m - 1) / 4 + 1 ≤ ecountIn G₁.adj (delVertex l y) := by
            have hsub : (m - 1) * (m - 1) = 4 * (q * q) := by
              rw [hodd]
              have h1 : 2 * q + 1 - 1 = 2 * q := by omega
              rw [h1]
              exact sq_two_mul q
            rw [hsub]
            omega
          have hIH := ih (m - 1) (by omega) n G₁ (delVertex l y) hnd' hlen' hE''
          have hmono2 := tcountIn_delVertex_le G₁ l y
          omega
        | inr heven =>
          -- m = 2q + 2 even, q ≥ 1.
          have hq1 : 1 ≤ q := by omega
          have hsq2 : m * m = 4 * (q * q) + 8 * q + 4 := by
            rw [heven, sq_add_two, sq_two_mul]; omega
          rw [hsq2] at hE1
          by_cases hmin : ∃ w ∈ l, degIn G₁.adj l w ≤ q
          · -- Sub-case 1: delete a low-degree vertex, destroy one triangle, induct.
            obtain ⟨w, hw, hwdeg⟩ := hmin
            have hE' := ecountIn_eq_filter_add_deg G₁ nd hw
            have hlen' : (delVertex l w).length = m - 1 := by
              have h := length_filter_neq_of_mem nd hw
              rwa [hm] at h
            have hnd' : (delVertex l w).Nodup := nd.filter _
            have hmantel : (m - 1) * (m - 1) / 4 + 1 ≤ ecountIn G₁.adj (delVertex l w) := by
              have hsub : (m - 1) * (m - 1) = 4 * (q * q) + 4 * q + 1 := by
                rw [heven]
                have h1 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
                rw [h1, sq_add_one, sq_two_mul]
                omega
              rw [hsub]
              omega
            obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hAab, hAac, hAbc⟩ :=
              mantel G₁ (m - 1) (delVertex l w) hnd' hlen' hmantel
            have hcount := ecountIn_deleteEdge G₁ hnd' ha hb hab hAab
            have hE'' : (m - 1) * (m - 1) / 4 + 1 ≤
                ecountIn (deleteEdge G₁ a b).adj (delVertex l w) := by
              have hsub : (m - 1) * (m - 1) = 4 * (q * q) + 4 * q + 1 := by
                rw [heven]
                have h1 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
                rw [h1, sq_add_one, sq_two_mul]
                omega
              rw [hsub]
              omega
            have hIH := ih (m - 1) (by omega) n (deleteEdge G₁ a b) (delVertex l w) hnd' hlen' hE''
            have hdrop := tcountIn_deleteEdge_add_one_le G₁ ha hb hc hab hac hbc hAab hAac hAbc
            have hmono2 := tcountIn_delVertex_le G₁ l w
            omega
          · -- Sub-case 2: all degrees are q + 1 or more; at most two vertices exceed q + 1.
            have hall : ∀ v ∈ l, q + 1 ≤ degIn G₁.adj l v := by
              intro v hv
              by_cases hcv : degIn G₁.adj l v ≤ q
              · exact absurd ⟨v, hv, hcv⟩ hmin
              · omega
            have hmantel : m * m / 4 + 1 ≤ ecountIn G₁.adj l := by omega
            obtain ⟨a, ha, b, hb, c, hc, hab, hac, hbc, hAab, hAac, hAbc⟩ :=
              mantel G₁ m l nd hm hmantel
            -- Some vertex of the triangle has degree exactly q + 1.
            have hex : ∃ y ∈ l, (y = a ∨ y = b ∨ y = c) ∧ degIn G₁.adj l y ≤ q + 1 := by
              by_cases hcase : ∃ y ∈ l, (y = a ∨ y = b ∨ y = c) ∧ degIn G₁.adj l y ≤ q + 1
              · exact hcase
              · have h3hi : ∀ y ∈ l, y = a ∨ y = b ∨ y = c → q + 2 ≤ degIn G₁.adj l y := by
                  intro y hy hyor
                  by_cases hcy : degIn G₁.adj l y ≤ q + 1
                  · exact absurd ⟨y, hy, hyor, hcy⟩ hcase
                  · omega
                have hpoint : ∀ v ∈ l,
                    q + 1 + (if v = a ∨ v = b ∨ v = c then 1 else 0) ≤ degIn G₁.adj l v := by
                  intro v hv
                  by_cases hv3 : v = a ∨ v = b ∨ v = c
                  · simp [hv3]
                    exact h3hi v hv hv3
                  · simp [hv3]
                    exact hall v hv
                have hsum := ssum_ge hpoint
                rw [ssum_add, ssum_const, hm] at hsum
                have hind : ssum l (fun v => if v = a ∨ v = b ∨ v = c then 1 else 0) = 3 := by
                  have hp : ∀ v ∈ l, (if v = a ∨ v = b ∨ v = c then (1 : Nat) else 0) =
                      (if v = a then 1 else 0) + ((if v = b then 1 else 0) +
                        (if v = c then 1 else 0)) := by
                    intro v _
                    by_cases h1 : v = a
                    · subst h1
                      simp [hab, hac]
                    · by_cases h2 : v = b
                      · subst h2
                        simp [hab.symm, hbc]
                      · by_cases h3 : v = c
                        · subst h3
                          simp [hac.symm, hbc.symm]
                        · simp [h1, h2, h3]
                  rw [ssum_congr hp, ssum_add, ssum_add]
                  rw [ssum_eq_single nd ha, ssum_eq_single nd hb, ssum_eq_single nd hc]
                rw [hind] at hsum
                have hexp3 : (q + 1) * (2 * q + 2) = 2 * (q * q) + 4 * q + 2 := by
                  have h1 : q * (2 * q) = 2 * (q * q) := by
                    rw [Nat.mul_comm q (2 * q), Nat.mul_assoc]
                  rw [Nat.add_mul, Nat.mul_add, Nat.mul_add]
                  omega
                rw [heven] at hsum
                rw [hexp3] at hsum
                have hshake2 : ssum l (degIn G₁.adj l) = 2 * ecountIn G₁.adj l := hshake
                have hcontra : (0 : Nat) < 0 := by omega
                exact (Nat.lt_irrefl 0 hcontra).elim
            obtain ⟨y, hy, hyor, hydeg⟩ := hex
            have hydeg2 : degIn G₁.adj l y = q + 1 := by
              have h := hall y hy
              omega
            have hE' := ecountIn_eq_filter_add_deg G₁ nd hy
            have hlen' : (delVertex l y).length = m - 1 := by
              have h := length_filter_neq_of_mem nd hy
              rwa [hm] at h
            have hnd' : (delVertex l y).Nodup := nd.filter _
            have hE'' : (m - 1) * (m - 1) / 4 + 1 ≤ ecountIn G₁.adj (delVertex l y) := by
              have hsub : (m - 1) * (m - 1) = 4 * (q * q) + 4 * q + 1 := by
                rw [heven]
                have h1 : 2 * q + 2 - 1 = 2 * q + 1 := by omega
                rw [h1, sq_add_one, sq_two_mul]
                omega
              rw [hsub]
              omega
            have hIH := ih (m - 1) (by omega) n G₁ (delVertex l y) hnd' hlen' hE''
            -- y lies on the triangle, so deletion destroys at least one triangle.
            have htri : tcountIn G₁.adj (delVertex l y) + 1 ≤ tcountIn G₁.adj l := by
              cases hyor with
              | inl hya =>
                rw [hya]
                exact tcountIn_ge_delVertex_add_one G₁ nd ha hb hc hab hac hbc hAab hAac hAbc
              | inr hrest =>
                cases hrest with
                | inl hyb =>
                  rw [hyb]
                  have hAba : G₁.adj b a = true := by rw [G₁.sym b a]; exact hAab
                  exact tcountIn_ge_delVertex_add_one G₁ nd hb ha hc hab.symm hbc hac hAba hAbc hAac
                | inr hyc =>
                  rw [hyc]
                  have hAca : G₁.adj c a = true := by rw [G₁.sym c a]; exact hAac
                  have hAcb : G₁.adj c b = true := by rw [G₁.sym c b]; exact hAbc
                  exact tcountIn_ge_delVertex_add_one G₁ nd hc ha hb hac.symm hbc.symm hab hAca hAcb hAab
            omega

/-- **JSP-000840 (scoped component, t = 1): Rademacher's theorem.**
Every simple graph on `n` vertices with at least `⌊n²/4⌋ + 1` edges contains
at least `⌊n/2⌋` triangles. -/
theorem jsp_000840 (n : Nat) (G : Gph n)
    (h : n * n / 4 + 1 ≤ ecountIn G.adj (List.finRange n)) :
    n / 2 ≤ tcountIn G.adj (List.finRange n) :=
  rademacher_list n n G (List.finRange n) (List.nodup_finRange n) List.length_finRange h

#print axioms jsp_000840

end Jsp000840
