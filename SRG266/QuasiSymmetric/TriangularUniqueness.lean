/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.BlockGraph

/-!
# Local structure of the derived block graph

The block graph of a `Derived45` is strongly regular with parameters
`(55, 18, 9, 4)`. Finite counting shows that it has no `11`-clique, is
claw-free, and that every local graph splits into two `9`-cliques joined by a
perfect matching.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

namespace Derived45

variable {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P)

/-! ### Neighbourhoods as `Finset`s

`BlockGraph.lean` phrases strong regularity through
`SimpleGraph.commonNeighbors`; the counting below is easier with
`neighborFinset`, so the three parameters are restated in that form. -/

/-- The block graph is `18`-regular, in `Finset` form. -/
theorem card_neighborFinset (p : P) : (E.blockGraph.neighborFinset p).card = 18 :=
  E.blockGraph_degree p

/-- Common neighbours as an intersection of `neighborFinset`s. -/
theorem neighborFinset_inter (p q : P) :
    E.blockGraph.neighborFinset p ∩ E.blockGraph.neighborFinset q =
      Finset.univ.filter fun r => E.blockGraph.Adj p r ∧ E.blockGraph.Adj q r := by
  ext r
  simp [SimpleGraph.mem_neighborFinset]

/-- `λ = 9`, in `Finset` form. -/
theorem card_neighborFinset_inter_of_adj {p q : P} (h : E.blockGraph.Adj p q) :
    (E.blockGraph.neighborFinset p ∩ E.blockGraph.neighborFinset q).card = 9 := by
  rw [E.neighborFinset_inter p q, ← E.card_commonNeighbors_eq p q,
    E.card_commonNeighbors_of_adj h]

/-- `μ = 4`, in `Finset` form. -/
theorem card_neighborFinset_inter_of_not_adj {p q : P} (hne : p ≠ q)
    (h : ¬ E.blockGraph.Adj p q) :
    (E.blockGraph.neighborFinset p ∩ E.blockGraph.neighborFinset q).card = 4 := by
  rw [E.neighborFinset_inter p q, ← E.card_commonNeighbors_eq p q,
    E.card_commonNeighbors_of_not_adj hne h]

/-! ### No eleven-clique -/

/-- Inside an `11`-clique `C`, two adjacent points `x, y` already have `9`
common neighbours *inside* `C`, namely `C \ {x, y}`; since `λ = 9` there are no
others.  Hence a point off `C` has at most one neighbour in `C`. -/
theorem card_filter_adj_le_one_of_isNClique {C : Finset P}
    (hC : E.blockGraph.IsNClique 11 C) {z : P} (hz : z ∉ C) :
    (C.filter fun x => E.blockGraph.Adj x z).card ≤ 1 := by
  by_contra hlt
  rw [Nat.not_le] at hlt
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hlt
  rw [Finset.mem_filter] at hx hy
  obtain ⟨hxC, hxz⟩ := hx
  obtain ⟨hyC, hyz⟩ := hy
  -- `C \ {x, y}` consists of common neighbours of `x` and `y` …
  have hsub : (C.erase x).erase y ⊆
      E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y := by
    intro w hw
    have hwy : w ≠ y := (Finset.mem_erase.mp hw).1
    have hw' := Finset.mem_of_mem_erase hw
    have hwx : w ≠ x := (Finset.mem_erase.mp hw').1
    have hwC : w ∈ C := Finset.mem_of_mem_erase hw'
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hC.isClique (Finset.mem_coe.mpr hxC) (Finset.mem_coe.mpr hwC) (Ne.symm hwx),
      hC.isClique (Finset.mem_coe.mpr hyC) (Finset.mem_coe.mpr hwC) (Ne.symm hwy)⟩
  -- … and there are exactly `9` of each.
  have hycard : y ∈ C.erase x := Finset.mem_erase.mpr ⟨Ne.symm hxy, hyC⟩
  have hcard : ((C.erase x).erase y).card = 9 := by
    rw [Finset.card_erase_of_mem hycard, Finset.card_erase_of_mem hxC, hC.card_eq]
  have hadj : E.blockGraph.Adj x y :=
    hC.isClique (Finset.mem_coe.mpr hxC) (Finset.mem_coe.mpr hyC) hxy
  have heq : (C.erase x).erase y =
      E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y :=
    Finset.eq_of_subset_of_card_le hsub
      (by rw [E.card_neighborFinset_inter_of_adj hadj, hcard])
  -- so `z`, a common neighbour of `x` and `y`, would lie in `C`.
  have hzmem : z ∈ (C.erase x).erase y := by
    rw [heq]
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hxz, hyz⟩
  exact hz (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hzmem))

/-- The block graph of a `Derived45` has no `11`-clique.

The `88` edges leaving an `11`-clique cannot be distributed over the `44`
outside points at one apiece. -/
theorem no_clique_eleven : E.blockGraph.CliqueFree 11 := by
  intro C hC
  classical
  -- the complement of `C`
  have hDcard : ((Finset.univ : Finset P) \ C).card = 44 := by
    have h := Finset.card_sdiff_add_card_inter (Finset.univ : Finset P) C
    rw [Finset.univ_inter, Finset.card_univ, E.point_card, hC.card_eq] at h
    omega
  -- inside a clique, the neighbours of `x` in `C` are all of `C \ {x}`
  have hin : ∀ x ∈ C, E.blockGraph.neighborFinset x ∩ C = C.erase x := by
    intro x hx
    ext w
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset, Finset.mem_erase]
    exact ⟨fun h => ⟨h.1.ne', h.2⟩, fun h =>
      ⟨hC.isClique (Finset.mem_coe.mpr hx) (Finset.mem_coe.mpr h.2) (Ne.symm h.1), h.2⟩⟩
  -- hence `18 − 10 = 8` neighbours outside
  have houter : ∀ x ∈ C,
      (((Finset.univ : Finset P) \ C).filter fun z => E.blockGraph.Adj x z).card = 8 := by
    intro x hx
    have hset : (((Finset.univ : Finset P) \ C).filter fun z => E.blockGraph.Adj x z) =
        E.blockGraph.neighborFinset x \ C := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_sdiff, Finset.mem_univ, true_and,
        SimpleGraph.mem_neighborFinset]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    have h1 := Finset.card_sdiff_add_card_inter (E.blockGraph.neighborFinset x) C
    rw [hin x hx, Finset.card_erase_of_mem hx, hC.card_eq, E.card_neighborFinset x] at h1
    rw [hset]
    omega
  -- the double count of the `C`-to-outside edges
  have hswap : (∑ x ∈ C,
        (((Finset.univ : Finset P) \ C).filter fun z => E.blockGraph.Adj x z).card) =
      ∑ z ∈ (Finset.univ : Finset P) \ C,
        (C.filter fun x => E.blockGraph.Adj x z).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have hleft : (∑ x ∈ C,
      (((Finset.univ : Finset P) \ C).filter fun z => E.blockGraph.Adj x z).card) = 88 := by
    rw [Finset.sum_congr rfl houter, Finset.sum_const, hC.card_eq, smul_eq_mul]
  have hright : (∑ z ∈ (Finset.univ : Finset P) \ C,
      (C.filter fun x => E.blockGraph.Adj x z).card) ≤ 44 := by
    calc (∑ z ∈ (Finset.univ : Finset P) \ C,
            (C.filter fun x => E.blockGraph.Adj x z).card)
        ≤ ∑ _z ∈ (Finset.univ : Finset P) \ C, 1 :=
          Finset.sum_le_sum fun z hz => E.card_filter_adj_le_one_of_isNClique hC
            (Finset.mem_sdiff.mp hz).2
      _ = 44 := by rw [Finset.sum_const, hDcard, smul_eq_mul, mul_one]
  omega

/-! ### Claw-freeness -/

/-- Two non-adjacent neighbours `u, v` of `x` share at most `3` neighbours with
`x`: their `μ = 4` common neighbours include `x` itself, which is not one of its
own neighbours. -/
theorem card_local_inter_le_three {x u v : P} (hu : E.blockGraph.Adj x u)
    (hv : E.blockGraph.Adj x v) (huv : u ≠ v) (hnadj : ¬ E.blockGraph.Adj u v) :
    ((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset u) ∩
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset v)).card ≤ 3 := by
  have hxmem : x ∈ E.blockGraph.neighborFinset u ∩ E.blockGraph.neighborFinset v := by
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
    exact ⟨hu.symm, hv.symm⟩
  have hsub : ((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset u) ∩
      (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset v)) ⊆
        (E.blockGraph.neighborFinset u ∩ E.blockGraph.neighborFinset v).erase x := by
    intro w hw
    simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · rintro rfl
      exact hw.1.1.ne rfl
    · simp only [Finset.mem_inter, SimpleGraph.mem_neighborFinset]
      exact ⟨hw.1.2, hw.2.2⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hxmem,
    E.card_neighborFinset_inter_of_not_adj huv hnadj] at hle
  omega

/-- The block graph of a `Derived45` is claw-free: a point `x` has no
three pairwise distinct, pairwise non-adjacent neighbours.

Equivalently, every local graph `Γ(x)` has independence number at most `2`. -/
theorem blockGraph_clawFree {x y₁ y₂ y₃ : P}
    (h₁ : E.blockGraph.Adj x y₁) (h₂ : E.blockGraph.Adj x y₂) (h₃ : E.blockGraph.Adj x y₃)
    (n₁₂ : y₁ ≠ y₂) (n₁₃ : y₁ ≠ y₃) (n₂₃ : y₂ ≠ y₃)
    (a₁₂ : ¬ E.blockGraph.Adj y₁ y₂) (a₁₃ : ¬ E.blockGraph.Adj y₁ y₃)
    (a₂₃ : ¬ E.blockGraph.Adj y₂ y₃) : False := by
  classical
  -- the three local neighbourhoods, of size `λ = 9`
  have c₁ := E.card_neighborFinset_inter_of_adj h₁
  have c₂ := E.card_neighborFinset_inter_of_adj h₂
  have c₃ := E.card_neighborFinset_inter_of_adj h₃
  -- pairwise, they meet in at most `μ − 1 = 3` points
  have b₁₂ := E.card_local_inter_le_three h₁ h₂ n₁₂ a₁₂
  have b₁₃ := E.card_local_inter_le_three h₁ h₃ n₁₃ a₁₃
  have b₂₃ := E.card_local_inter_le_three h₂ h₃ n₂₃ a₂₃
  -- their union avoids `y₁, y₂, y₃`, so it has at most `18 − 3 = 15` points
  have hsub : ((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₁) ∪
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₂)) ∪
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₃) ⊆
      (((E.blockGraph.neighborFinset x).erase y₁).erase y₂).erase y₃ := by
    intro w hw
    simp only [Finset.mem_union, Finset.mem_inter, SimpleGraph.mem_neighborFinset] at hw
    have hwx : E.blockGraph.Adj x w := by rcases hw with (h | h) | h <;> exact h.1
    have key : w ≠ y₁ ∧ w ≠ y₂ ∧ w ≠ y₃ := by
      refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hw with (h | h) | h
      · exact h.2.ne rfl
      · exact a₁₂ h.2.symm
      · exact a₁₃ h.2.symm
      · exact a₁₂ h.2
      · exact h.2.ne rfl
      · exact a₂₃ h.2.symm
      · exact a₁₃ h.2
      · exact a₂₃ h.2
      · exact h.2.ne rfl
    simp only [Finset.mem_erase, SimpleGraph.mem_neighborFinset]
    exact ⟨key.2.2, key.2.1, key.1, hwx⟩
  have h₁mem : y₁ ∈ E.blockGraph.neighborFinset x :=
    SimpleGraph.mem_neighborFinset _ _ _ |>.mpr h₁
  have h₂mem : y₂ ∈ (E.blockGraph.neighborFinset x).erase y₁ :=
    Finset.mem_erase.mpr ⟨Ne.symm n₁₂, SimpleGraph.mem_neighborFinset _ _ _ |>.mpr h₂⟩
  have h₃mem : y₃ ∈ ((E.blockGraph.neighborFinset x).erase y₁).erase y₂ :=
    Finset.mem_erase.mpr ⟨Ne.symm n₂₃, Finset.mem_erase.mpr
      ⟨Ne.symm n₁₃, SimpleGraph.mem_neighborFinset _ _ _ |>.mpr h₃⟩⟩
  have hbig : ((((E.blockGraph.neighborFinset x).erase y₁).erase y₂).erase y₃).card = 15 := by
    rw [Finset.card_erase_of_mem h₃mem, Finset.card_erase_of_mem h₂mem,
      Finset.card_erase_of_mem h₁mem, E.card_neighborFinset x]
  have hunion := Finset.card_le_card hsub
  rw [hbig] at hunion
  -- Bonferroni: `|A₁ ∪ A₂ ∪ A₃| ≥ 3·9 − 3·3 = 18 > 15`
  have e₁₂ := Finset.card_union_add_card_inter
    (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₁)
    (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₂)
  have e₃ := Finset.card_union_add_card_inter
    ((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₁) ∪
      (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₂))
    (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₃)
  have hdist : (((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₁) ∪
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₂)) ∩
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₃)).card ≤
      ((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₁) ∩
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₃)).card +
      ((E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₂) ∩
        (E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset y₃)).card := by
    rw [Finset.union_inter_distrib_right]
    exact Finset.card_union_le _ _
  omega

/-! ### The local graph splits into two nine-cliques

Write `Δ = Γ(x)` for the local graph at a point `x`: `18` vertices, `9`-regular
because `λ = 9`. Its complement `Δ̄` is `8`-regular and triangle-free. It is
`K₉,₉` minus a perfect matching, i.e.
`Δ` as the rook's graph `K₉ □ K₂`; equivalently `Γ(x)` is the disjoint union of
two `9`-cliques, each point of one being adjacent to exactly one point of the
other.

The two neighbourhoods inside `Δ` are named `Derived45.localNbr` (the
`Δ`-neighbours of `u` in `Γ(x)`) and `Derived45.localNonNbr` (the
`Δ̄`-neighbours), and all of the counting below happens inside them. -/

/-- The neighbours of `u` inside the local graph `Γ(x)`. -/
def localNbr (x u : P) : Finset P :=
  E.blockGraph.neighborFinset x ∩ E.blockGraph.neighborFinset u

/-- The non-neighbours of `u` inside the local graph `Γ(x)`: the neighbourhood
of `u` in the complement `Δ̄` of `Δ = Γ(x)`. -/
def localNonNbr (x u : P) : Finset P :=
  (E.blockGraph.neighborFinset x).filter fun q => q ≠ u ∧ ¬ E.blockGraph.Adj u q

variable {x u : P}

theorem mem_localNbr {q : P} :
    q ∈ E.localNbr x u ↔ E.blockGraph.Adj x q ∧ E.blockGraph.Adj u q := by
  simp only [localNbr, Finset.mem_inter, SimpleGraph.mem_neighborFinset]

theorem mem_localNonNbr {q : P} :
    q ∈ E.localNonNbr x u ↔
      E.blockGraph.Adj x q ∧ q ≠ u ∧ ¬ E.blockGraph.Adj u q := by
  simp only [localNonNbr, Finset.mem_filter, SimpleGraph.mem_neighborFinset]

/-- `Δ` is `9`-regular: `|Γ(x) ∩ Γ(u)| = λ = 9`. -/
theorem card_localNbr (h : E.blockGraph.Adj x u) : (E.localNbr x u).card = 9 :=
  E.card_neighborFinset_inter_of_adj h

/-- `Γ(x)` minus `u` is the disjoint union of the `Δ`- and the
`Δ̄`-neighbourhood of `u`. -/
theorem localNbr_union_localNonNbr :
    E.localNbr x u ∪ E.localNonNbr x u = (E.blockGraph.neighborFinset x).erase u := by
  ext q
  simp only [Finset.mem_union, Finset.mem_erase, E.mem_localNbr, E.mem_localNonNbr,
    SimpleGraph.mem_neighborFinset]
  constructor
  · rintro (⟨hxq, huq⟩ | ⟨hxq, hqu, -⟩)
    · exact ⟨huq.ne', hxq⟩
    · exact ⟨hqu, hxq⟩
  · rintro ⟨hqu, hxq⟩
    by_cases huq : E.blockGraph.Adj u q
    · exact Or.inl ⟨hxq, huq⟩
    · exact Or.inr ⟨hxq, hqu, huq⟩

theorem disjoint_localNbr_localNonNbr :
    Disjoint (E.localNbr x u) (E.localNonNbr x u) := by
  rw [Finset.disjoint_left]
  intro q hq hq'
  exact (E.mem_localNonNbr.1 hq').2.2 (E.mem_localNbr.1 hq).2

/-- `Δ̄` is `8`-regular: `18 − 1 − 9 = 8`. -/
theorem card_localNonNbr (h : E.blockGraph.Adj x u) : (E.localNonNbr x u).card = 8 := by
  have hmem : u ∈ E.blockGraph.neighborFinset x := (SimpleGraph.mem_neighborFinset _ _ _).2 h
  have hcard := Finset.card_union_of_disjoint (E.disjoint_localNbr_localNonNbr (x := x) (u := u))
  rw [E.localNbr_union_localNonNbr, Finset.card_erase_of_mem hmem, E.card_neighborFinset x,
    E.card_localNbr h] at hcard
  omega

/-- `Δ̄`-adjacency is symmetric. -/
theorem localNonNbr_symm {q : P} (h : E.blockGraph.Adj x u)
    (hq : q ∈ E.localNonNbr x u) : u ∈ E.localNonNbr x q := by
  obtain ⟨-, hqu, hnadj⟩ := E.mem_localNonNbr.1 hq
  exact E.mem_localNonNbr.2 ⟨h, Ne.symm hqu, fun hadj => hnadj hadj.symm⟩

/-- `Δ̄` is triangle-free: `u`, `p` and `q` cannot be
pairwise `Δ̄`-adjacent inside `Γ(x)`. -/
theorem localNonNbr_triangle {p q : P} (h : E.blockGraph.Adj x u)
    (hp : p ∈ E.localNonNbr x u) (hq : q ∈ E.localNonNbr x u)
    (hpq : q ∈ E.localNonNbr x p) : False := by
  obtain ⟨hxp, hpu, hup⟩ := E.mem_localNonNbr.1 hp
  obtain ⟨hxq, hqu, huq⟩ := E.mem_localNonNbr.1 hq
  obtain ⟨-, hqp, hpq'⟩ := E.mem_localNonNbr.1 hpq
  exact E.blockGraph_clawFree h hxp hxq (Ne.symm hpu) (Ne.symm hqu) (Ne.symm hqp) hup huq hpq'

/-- The `Δ̄`-neighbourhood of `u` is a clique of `Γ`: two `Δ̄`-neighbours of `u`
that were themselves `Δ̄`-adjacent would complete a triangle of `Δ̄`. -/
theorem localNonNbr_isClique (h : E.blockGraph.Adj x u) :
    E.blockGraph.IsClique (E.localNonNbr x u : Set P) := by
  intro a ha b hb hab
  by_contra hnadj
  exact E.localNonNbr_triangle h (Finset.mem_coe.1 ha) (Finset.mem_coe.1 hb)
    (E.mem_localNonNbr.2 ⟨(E.mem_localNonNbr.1 (Finset.mem_coe.1 hb)).1, Ne.symm hab, hnadj⟩)

/-- **`e(A, B)`, one row.**  A `Δ̄`-neighbour `a` of `u` has `u` and seven
`Δ`-neighbours of `u` as its own `Δ̄`-neighbours: none of the other
`Δ̄`-neighbours of `u` qualifies, since they are all `Δ`-adjacent to `a`. -/
theorem card_localNonNbr_inter_localNbr {a : P} (h : E.blockGraph.Adj x u)
    (ha : a ∈ E.localNonNbr x u) :
    (E.localNonNbr x a ∩ E.localNbr x u).card = 7 := by
  obtain ⟨hxa, hau, hua⟩ := E.mem_localNonNbr.1 ha
  have humem : u ∈ E.localNonNbr x a := E.localNonNbr_symm h ha
  have hnot : u ∉ E.localNonNbr x a ∩ E.localNbr x u := fun hmem =>
    (E.mem_localNbr.1 (Finset.mem_inter.1 hmem).2).2.ne rfl
  have hins : insert u (E.localNonNbr x a ∩ E.localNbr x u) = E.localNonNbr x a := by
    refine Finset.Subset.antisymm ?_ ?_
    · intro q hq
      rcases Finset.mem_insert.1 hq with rfl | hq
      · exact humem
      · exact (Finset.mem_inter.1 hq).1
    · intro q hq
      by_cases hqu : q = u
      · exact hqu ▸ Finset.mem_insert_self _ _
      refine Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hq, ?_⟩)
      obtain ⟨hxq, hqa, haq⟩ := E.mem_localNonNbr.1 hq
      refine E.mem_localNbr.2 ⟨hxq, ?_⟩
      by_contra huq
      exact haq (E.localNonNbr_isClique h (Finset.mem_coe.2 ha)
        (Finset.mem_coe.2 (E.mem_localNonNbr.2 ⟨hxq, hqu, huq⟩)) fun hea => hqa hea.symm)
  have hcard := Finset.card_insert_of_notMem hnot
  rw [hins, E.card_localNonNbr hxa] at hcard
  omega

/-- **The row sum at a `Δ`-neighbour.**  A `Δ`-neighbour `b` of `u` is not
`Δ̄`-adjacent to `u`, so its eight `Δ̄`-neighbours split between the
`Δ̄`- and the `Δ`-neighbourhood of `u`. -/
theorem card_localNonNbr_inter_add {b : P} (h : E.blockGraph.Adj x u)
    (hb : b ∈ E.localNbr x u) :
    (E.localNonNbr x b ∩ E.localNonNbr x u).card
      + (E.localNonNbr x b ∩ E.localNbr x u).card = 8 := by
  obtain ⟨hxb, hub⟩ := E.mem_localNbr.1 hb
  have hdisj : Disjoint (E.localNonNbr x b ∩ E.localNonNbr x u)
      (E.localNonNbr x b ∩ E.localNbr x u) := by
    rw [Finset.disjoint_left]
    intro q hq hq'
    exact (E.mem_localNonNbr.1 (Finset.mem_inter.1 hq).2).2.2
      (E.mem_localNbr.1 (Finset.mem_inter.1 hq').2).2
  have hsub : E.localNonNbr x b ⊆ E.localNonNbr x u ∪ E.localNbr x u := by
    intro q hq
    obtain ⟨hxq, hqb, hbq⟩ := E.mem_localNonNbr.1 hq
    by_cases huq : E.blockGraph.Adj u q
    · exact Finset.mem_union_right _ (E.mem_localNbr.2 ⟨hxq, huq⟩)
    · refine Finset.mem_union_left _ (E.mem_localNonNbr.2 ⟨hxq, ?_, huq⟩)
      rintro rfl
      exact hbq hub.symm
  have hunion : E.localNonNbr x b ∩ E.localNonNbr x u
      ∪ E.localNonNbr x b ∩ E.localNbr x u = E.localNonNbr x b := by
    rw [← Finset.inter_union_distrib_left, Finset.inter_eq_left.2 hsub]
  rw [← Finset.card_union_of_disjoint hdisj, hunion, E.card_localNonNbr hxb]

/-- **The `Δ̄`-degree sum inside the `Δ`-neighbourhood of `u` is `16`.**
Double counting the `Δ̄`-edges between the two neighbourhoods gives
`8 · 7 = 56` from the `Δ̄`-side, so the `9` points of the `Δ`-side carry
`9 · 8 − 56 = 16` further `Δ̄`-ends among themselves. -/
theorem sum_localNonNbr_inter_localNbr (h : E.blockGraph.Adj x u) :
    ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNbr x u).card = 16 := by
  classical
  have hrow : ∀ a ∈ E.localNonNbr x u, (E.localNonNbr x a ∩ E.localNbr x u).card = 7 :=
    fun a ha => E.card_localNonNbr_inter_localNbr h ha
  have hA : ∑ a ∈ E.localNonNbr x u, (E.localNonNbr x a ∩ E.localNbr x u).card = 56 := by
    rw [Finset.sum_congr rfl hrow]
    simp [E.card_localNonNbr h]
  have hcard : ∀ (s : Finset P) (a : P), (E.localNonNbr x a ∩ s).card
      = ∑ b ∈ s, if b ∈ E.localNonNbr x a then 1 else 0 := by
    intro s a
    rw [← Finset.card_filter]
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_inter]
    exact ⟨fun hb => ⟨hb.2, hb.1⟩, fun hb => ⟨hb.2, hb.1⟩⟩
  have hswap : ∑ a ∈ E.localNonNbr x u, (E.localNonNbr x a ∩ E.localNbr x u).card
      = ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNonNbr x u).card := by
    rw [Finset.sum_congr rfl fun a _ => hcard (E.localNbr x u) a,
      Finset.sum_congr rfl fun b _ => hcard (E.localNonNbr x u) b, Finset.sum_comm]
    refine Finset.sum_congr rfl fun b hb => Finset.sum_congr rfl fun a ha => ?_
    have hxa : E.blockGraph.Adj x a := (E.mem_localNonNbr.1 ha).1
    have hxb : E.blockGraph.Adj x b := (E.mem_localNbr.1 hb).1
    by_cases hmem : b ∈ E.localNonNbr x a
    · rw [if_pos hmem, if_pos (E.localNonNbr_symm hxa hmem)]
    · rw [if_neg hmem, if_neg fun hmem' => hmem (E.localNonNbr_symm hxb hmem')]
  have hrow' : ∀ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNonNbr x u).card
      + (E.localNonNbr x b ∩ E.localNbr x u).card = 8 :=
    fun b hb => E.card_localNonNbr_inter_add h hb
  have hB : ∑ b ∈ E.localNbr x u, ((E.localNonNbr x b ∩ E.localNonNbr x u).card
      + (E.localNonNbr x b ∩ E.localNbr x u).card) = 72 := by
    rw [Finset.sum_congr rfl hrow']
    simp [E.card_localNbr h]
  rw [Finset.sum_add_distrib] at hB
  omega

/-- Two `Δ̄`-adjacent points of the `Δ`-neighbourhood of `u` have disjoint
`Δ̄`-neighbourhoods on the `Δ̄`-side, so together they keep at least `8` of
their `16` `Δ̄`-ends inside the `Δ`-side. -/
theorem le_card_add_card_of_edge {b₁ b₂ : P} (h : E.blockGraph.Adj x u)
    (h₁ : b₁ ∈ E.localNbr x u) (h₂ : b₂ ∈ E.localNbr x u)
    (he : b₂ ∈ E.localNonNbr x b₁) :
    8 ≤ (E.localNonNbr x b₁ ∩ E.localNbr x u).card
      + (E.localNonNbr x b₂ ∩ E.localNbr x u).card := by
  have hs₁ := E.card_localNonNbr_inter_add h h₁
  have hs₂ := E.card_localNonNbr_inter_add h h₂
  have hdisj : Disjoint (E.localNonNbr x b₁ ∩ E.localNonNbr x u)
      (E.localNonNbr x b₂ ∩ E.localNonNbr x u) := by
    rw [Finset.disjoint_left]
    intro a ha ha'
    exact E.localNonNbr_triangle (E.mem_localNbr.1 h₁).1 (Finset.mem_inter.1 ha).1 he
      (E.localNonNbr_symm (E.mem_localNbr.1 h₂).1 (Finset.mem_inter.1 ha').1)
  have hsub : E.localNonNbr x b₁ ∩ E.localNonNbr x u
      ∪ E.localNonNbr x b₂ ∩ E.localNonNbr x u ⊆ E.localNonNbr x u := by
    intro q hq
    rcases Finset.mem_union.1 hq with hq' | hq' <;> exact (Finset.mem_inter.1 hq').2
  have hle := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, E.card_localNonNbr h] at hle
  omega

/-- **No two disjoint `Δ̄`-edges inside the `Δ`-neighbourhood of `u`.**  Two
such edges would already account for all `16` `Δ̄`-ends, isolating every other
point; but then each of the four endpoints keeps its `Δ̄`-neighbours inside the
four-element set, for a total of at most `12`. -/
theorem no_two_disjoint_edges {b₁ b₂ b₃ b₄ : P} (h : E.blockGraph.Adj x u)
    (h₁ : b₁ ∈ E.localNbr x u) (h₂ : b₂ ∈ E.localNbr x u)
    (h₃ : b₃ ∈ E.localNbr x u) (h₄ : b₄ ∈ E.localNbr x u)
    (e₁ : b₂ ∈ E.localNonNbr x b₁) (e₂ : b₄ ∈ E.localNonNbr x b₃)
    (n₁₃ : b₁ ≠ b₃) (n₁₄ : b₁ ≠ b₄) (n₂₃ : b₂ ≠ b₃) (n₂₄ : b₂ ≠ b₄) : False := by
  classical
  have n₁₂ : b₁ ≠ b₂ := fun heq => (E.mem_localNonNbr.1 e₁).2.1 heq.symm
  have n₃₄ : b₃ ≠ b₄ := fun heq => (E.mem_localNonNbr.1 e₂).2.1 heq.symm
  set T : Finset P := {b₁, b₂, b₃, b₄} with hT
  have hm₁ : b₁ ∉ ({b₂, b₃, b₄} : Finset P) := by simp [n₁₂, n₁₃, n₁₄]
  have hm₂ : b₂ ∉ ({b₃, b₄} : Finset P) := by simp [n₂₃, n₂₄]
  have hm₃ : b₃ ∉ ({b₄} : Finset P) := by simp [n₃₄]
  have hTB : T ⊆ E.localNbr x u := by
    intro q hq
    simp only [hT, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl | rfl | rfl
    exacts [h₁, h₂, h₃, h₄]
  have hTcard : T.card = 4 := by
    rw [hT, Finset.card_insert_of_notMem hm₁, Finset.card_insert_of_notMem hm₂,
      Finset.card_insert_of_notMem hm₃]
    simp
  have hTsum : ∑ b ∈ T, (E.localNonNbr x b ∩ E.localNbr x u).card
      = (E.localNonNbr x b₁ ∩ E.localNbr x u).card
        + (E.localNonNbr x b₂ ∩ E.localNbr x u).card
        + (E.localNonNbr x b₃ ∩ E.localNbr x u).card
        + (E.localNonNbr x b₄ ∩ E.localNbr x u).card := by
    rw [hT, Finset.sum_insert hm₁, Finset.sum_insert hm₂, Finset.sum_insert hm₃,
      Finset.sum_singleton]
    ring
  have hsum : ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNbr x u).card = 16 :=
    E.sum_localNonNbr_inter_localNbr h
  have hsplit : (∑ b ∈ E.localNbr x u \ T, (E.localNonNbr x b ∩ E.localNbr x u).card)
      + ∑ b ∈ T, (E.localNonNbr x b ∩ E.localNbr x u).card
      = ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNbr x u).card :=
    Finset.sum_sdiff hTB
  have hlow₁ := E.le_card_add_card_of_edge h h₁ h₂ e₁
  have hlow₂ := E.le_card_add_card_of_edge h h₃ h₄ e₂
  have hzero : ∀ b ∈ E.localNbr x u \ T,
      (E.localNonNbr x b ∩ E.localNbr x u).card = 0 := by
    intro b hb
    by_contra hne
    have hle : (E.localNonNbr x b ∩ E.localNbr x u).card
        ≤ ∑ b ∈ E.localNbr x u \ T, (E.localNonNbr x b ∩ E.localNbr x u).card :=
      Finset.single_le_sum (f := fun b => (E.localNonNbr x b ∩ E.localNbr x u).card)
        (fun i _ => Nat.zero_le _) hb
    omega
  have hsubT : ∀ b ∈ T, E.localNonNbr x b ∩ E.localNbr x u ⊆ T.erase b := by
    intro b hbT q hq
    obtain ⟨hq₁, hq₂⟩ := Finset.mem_inter.1 hq
    refine Finset.mem_erase.mpr ⟨(E.mem_localNonNbr.1 hq₁).2.1, ?_⟩
    by_contra hqT
    have hbq : b ∈ E.localNonNbr x q :=
      E.localNonNbr_symm (E.mem_localNbr.1 (hTB hbT)).1 hq₁
    have hzq := hzero q (Finset.mem_sdiff.mpr ⟨hq₂, hqT⟩)
    rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem] at hzq
    exact hzq b (Finset.mem_inter.2 ⟨hbq, hTB hbT⟩)
  have hbound : ∀ b ∈ T, (E.localNonNbr x b ∩ E.localNbr x u).card ≤ 3 := by
    intro b hbT
    have hle := Finset.card_le_card (hsubT b hbT)
    rw [Finset.card_erase_of_mem hbT, hTcard] at hle
    omega
  have hb₁ := hbound b₁ (by simp [hT])
  have hb₂ := hbound b₂ (by simp [hT])
  have hb₃ := hbound b₃ (by simp [hT])
  have hb₄ := hbound b₄ (by simp [hT])
  have hout : ∑ b ∈ E.localNbr x u \ T, (E.localNonNbr x b ∩ E.localNbr x u).card = 0 :=
    Finset.sum_eq_zero hzero
  omega

/-- **The `Δ̄`-edges inside the `Δ`-neighbourhood of `u` form a star.**  There
is a point `c` on every one of them: the `Δ̄`-edges are pairwise intersecting
(`no_two_disjoint_edges`) and `Δ̄` is triangle-free, so they cannot split into
two pencils. -/
theorem exists_star_centre (h : E.blockGraph.Adj x u) :
    ∃ c ∈ E.localNbr x u, ∀ b ∈ E.localNbr x u, ∀ b' ∈ E.localNbr x u,
      b' ∈ E.localNonNbr x b → b = c ∨ b' = c := by
  classical
  obtain ⟨b₁, hb₁, hpos⟩ : ∃ b ∈ E.localNbr x u,
      0 < (E.localNonNbr x b ∩ E.localNbr x u).card := by
    by_contra hcon
    push Not at hcon
    have hz : ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNbr x u).card = 0 :=
      Finset.sum_eq_zero fun b hb => Nat.le_zero.1 (hcon b hb)
    rw [E.sum_localNonNbr_inter_localNbr h] at hz
    exact absurd hz (by norm_num)
  obtain ⟨b₂, hb₂⟩ := Finset.card_pos.1 hpos
  obtain ⟨he₁, hb₂B⟩ := Finset.mem_inter.1 hb₂
  by_cases hall : ∀ b ∈ E.localNbr x u, ∀ b' ∈ E.localNbr x u,
      b' ∈ E.localNonNbr x b → b = b₁ ∨ b' = b₁
  · exact ⟨b₁, hb₁, hall⟩
  push Not at hall
  obtain ⟨p, hp, q, hq, hpq, hpb₁, hqb₁⟩ := hall
  have hmeet : b₂ = p ∨ b₂ = q := by
    by_contra hcon
    push Not at hcon
    exact E.no_two_disjoint_edges h hb₁ hb₂B hp hq he₁ hpq
      (Ne.symm hpb₁) (Ne.symm hqb₁) hcon.1 hcon.2
  obtain ⟨r, hrB, hr, hrb₁, hrb₂⟩ : ∃ r ∈ E.localNbr x u,
      r ∈ E.localNonNbr x b₂ ∧ r ≠ b₁ ∧ r ≠ b₂ := by
    rcases hmeet with heq | heq
    · refine ⟨q, hq, ?_, hqb₁, ?_⟩
      · rw [heq]; exact hpq
      · rw [heq]; exact (E.mem_localNonNbr.1 hpq).2.1
    · refine ⟨p, hp, ?_, hpb₁, ?_⟩
      · rw [heq]; exact E.localNonNbr_symm (E.mem_localNbr.1 hp).1 hpq
      · rw [heq]; exact fun heq' => (E.mem_localNonNbr.1 hpq).2.1 heq'.symm
  have hb₁c : b₁ ∈ E.localNonNbr x b₂ :=
    E.localNonNbr_symm (E.mem_localNbr.1 hb₁).1 he₁
  have hxb₂ : E.blockGraph.Adj x b₂ := (E.mem_localNbr.1 hb₂B).1
  refine ⟨b₂, hb₂B, ?_⟩
  intro b hbB b' hb'B hedge
  by_contra hcon
  push Not at hcon
  obtain ⟨hbne, hb'ne⟩ := hcon
  have hone : b = b₁ ∨ b' = b₁ := by
    by_contra hc
    push Not at hc
    exact E.no_two_disjoint_edges h hb₁ hb₂B hbB hb'B he₁ hedge
      (Ne.symm hc.1) (Ne.symm hc.2) (Ne.symm hbne) (Ne.symm hb'ne)
  have htwo : b = r ∨ b' = r := by
    by_contra hc
    push Not at hc
    exact E.no_two_disjoint_edges h hb₂B hrB hbB hb'B hr hedge
      (Ne.symm hbne) (Ne.symm hb'ne) (Ne.symm hc.1) (Ne.symm hc.2)
  rcases hone with hone | hone <;> rcases htwo with htwo | htwo
  · exact hrb₁ (by rw [← htwo]; exact hone)
  · exact E.localNonNbr_triangle hxb₂ hb₁c hr (by rw [← htwo, ← hone]; exact hedge)
  · refine E.localNonNbr_triangle hxb₂ hb₁c hr ?_
    exact E.localNonNbr_symm (E.mem_localNbr.1 hrB).1 (by rw [← htwo, ← hone]; exact hedge)
  · exact hrb₁ (by rw [← htwo]; exact hone)

/-- The local graph `Γ(x)` of the block graph of a `Derived45` is the
disjoint union of two `9`-cliques.

Equivalently the complement of `Γ(x)` inside itself is bipartite, with the two
sides `X` and `Y`; `card_cross_eq_one` adds that it is `K₉,₉` minus a perfect
matching. -/
theorem local_split (x : P) :
    ∃ X Y : Finset P, X ∪ Y = E.blockGraph.neighborFinset x ∧ Disjoint X Y ∧
      X.card = 9 ∧ Y.card = 9 ∧
      E.blockGraph.IsClique (X : Set P) ∧ E.blockGraph.IsClique (Y : Set P) := by
  classical
  obtain ⟨u, hu⟩ : ∃ u, E.blockGraph.Adj x u := by
    have hpos : 0 < (E.blockGraph.neighborFinset x).card := by
      rw [E.card_neighborFinset x]; norm_num
    obtain ⟨u, hmem⟩ := Finset.card_pos.1 hpos
    exact ⟨u, (SimpleGraph.mem_neighborFinset _ _ _).1 hmem⟩
  obtain ⟨c, hc, hstar⟩ := E.exists_star_centre hu
  obtain ⟨hxc, huc⟩ := E.mem_localNbr.1 hc
  have hunotB : u ∉ E.localNbr x u := fun hmem => (E.mem_localNbr.1 hmem).2.ne rfl
  have hunotA : u ∉ E.localNonNbr x u := fun hmem => (E.mem_localNonNbr.1 hmem).2.1 rfl
  have hcnotA : c ∉ E.localNonNbr x u := fun hmem => (E.mem_localNonNbr.1 hmem).2.2 huc
  have hucne : u ≠ c := fun heq => hunotB (heq ▸ hc)
  -- every point of `B` other than `c` is `Δ̄`-adjacent to `c` or to nothing in `B`
  have hleaf : ∀ b ∈ (E.localNbr x u).erase c,
      (E.localNonNbr x b ∩ E.localNbr x u).card
        = if b ∈ E.localNonNbr x c then 1 else 0 := by
    intro b hb
    obtain ⟨hbc, hbB⟩ := Finset.mem_erase.1 hb
    have hxb : E.blockGraph.Adj x b := (E.mem_localNbr.1 hbB).1
    have hsub : E.localNonNbr x b ∩ E.localNbr x u ⊆ {c} := by
      intro q hq
      obtain ⟨hq₁, hq₂⟩ := Finset.mem_inter.1 hq
      rcases hstar b hbB q hq₂ hq₁ with heq | heq
      · exact absurd heq hbc
      · exact Finset.mem_singleton.2 heq
    by_cases hbc' : b ∈ E.localNonNbr x c
    · rw [if_pos hbc']
      have heq : E.localNonNbr x b ∩ E.localNbr x u = {c} := by
        refine Finset.Subset.antisymm hsub ?_
        intro q hq
        rw [Finset.mem_singleton] at hq
        subst hq
        exact Finset.mem_inter.2 ⟨E.localNonNbr_symm hxc hbc', hc⟩
      rw [heq, Finset.card_singleton]
    · rw [if_neg hbc']
      have heq : E.localNonNbr x b ∩ E.localNbr x u = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro q hq
        have hqc : q = c := Finset.mem_singleton.1 (hsub hq)
        subst hqc
        exact hbc' (E.localNonNbr_symm hxb (Finset.mem_inter.1 hq).1)
      rw [heq, Finset.card_empty]
  have hsum : ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNbr x u).card = 16 :=
    E.sum_localNonNbr_inter_localNbr hu
  have hsplit : (∑ b ∈ (E.localNbr x u).erase c, (E.localNonNbr x b ∩ E.localNbr x u).card)
      + (E.localNonNbr x c ∩ E.localNbr x u).card
      = ∑ b ∈ E.localNbr x u, (E.localNonNbr x b ∩ E.localNbr x u).card :=
    Finset.sum_erase_add _ _ hc
  have hfilter : ((E.localNbr x u).erase c).filter (fun b => b ∈ E.localNonNbr x c)
      = E.localNonNbr x c ∩ E.localNbr x u := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_inter]
    exact ⟨fun hb => ⟨hb.2, hb.1.2⟩,
      fun hb => ⟨⟨(E.mem_localNonNbr.1 hb.1).2.1, hb.2⟩, hb.1⟩⟩
  have herase : ∑ b ∈ (E.localNbr x u).erase c,
      (E.localNonNbr x b ∩ E.localNbr x u).card
        = (E.localNonNbr x c ∩ E.localNbr x u).card := by
    rw [Finset.sum_congr rfl hleaf, ← Finset.card_filter, hfilter]
  have hdc : (E.localNonNbr x c ∩ E.localNbr x u).card = 8 := by omega
  have hcA : E.localNonNbr x c ∩ E.localNonNbr x u = ∅ := by
    have hadd := E.card_localNonNbr_inter_add hu hc
    rw [hdc] at hadd
    exact Finset.card_eq_zero.1 (by omega)
  refine ⟨insert u ((E.localNbr x u).erase c), insert c (E.localNonNbr x u), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext q
    simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase,
      SimpleGraph.mem_neighborFinset]
    constructor
    · rintro ((rfl | ⟨-, hq⟩) | (rfl | hq))
      · exact hu
      · exact (E.mem_localNbr.1 hq).1
      · exact hxc
      · exact (E.mem_localNonNbr.1 hq).1
    · intro hq
      by_cases hqu : q = u
      · exact Or.inl (Or.inl hqu)
      by_cases huq : E.blockGraph.Adj u q
      · by_cases hqc : q = c
        · exact Or.inr (Or.inl hqc)
        · exact Or.inl (Or.inr ⟨hqc, E.mem_localNbr.2 ⟨hq, huq⟩⟩)
      · exact Or.inr (Or.inr (E.mem_localNonNbr.2 ⟨hq, hqu, huq⟩))
  · rw [Finset.disjoint_left]
    intro q hq hq'
    rcases Finset.mem_insert.1 hq with rfl | hq₁
    · rcases Finset.mem_insert.1 hq' with heq | hmem
      · exact hucne heq
      · exact hunotA hmem
    · obtain ⟨hqc, hqB⟩ := Finset.mem_erase.1 hq₁
      rcases Finset.mem_insert.1 hq' with heq | hmem
      · exact hqc heq
      · exact (E.mem_localNonNbr.1 hmem).2.2 (E.mem_localNbr.1 hqB).2
  · have herasecard : ((E.localNbr x u).erase c).card = 8 := by
      have hcard := Finset.card_erase_of_mem hc
      rw [E.card_localNbr hu] at hcard
      omega
    rw [Finset.card_insert_of_notMem fun hmem => hunotB (Finset.mem_of_mem_erase hmem),
      herasecard]
  · rw [Finset.card_insert_of_notMem hcnotA, E.card_localNonNbr hu]
  · intro p hp q hq hpq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe, Finset.mem_erase] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · exact absurd rfl hpq
    · exact (E.mem_localNbr.1 hq.2).2
    · exact ((E.mem_localNbr.1 hp.2).2).symm
    · by_contra hnadj
      have hqp : q ∈ E.localNonNbr x p :=
        E.mem_localNonNbr.2 ⟨(E.mem_localNbr.1 hq.2).1, Ne.symm hpq, hnadj⟩
      rcases hstar p hp.2 q hq.2 hqp with heq | heq
      · exact hp.1 heq
      · exact hq.1 heq
  · intro p hp q hq hpq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hp hq
    rcases hp with rfl | hp <;> rcases hq with rfl | hq
    · exact absurd rfl hpq
    · by_contra hnadj
      refine (Finset.eq_empty_iff_forall_notMem.1 hcA) q (Finset.mem_inter.2 ⟨?_, hq⟩)
      exact E.mem_localNonNbr.2 ⟨(E.mem_localNonNbr.1 hq).1, Ne.symm hpq, hnadj⟩
    · by_contra hnadj
      refine (Finset.eq_empty_iff_forall_notMem.1 hcA) p (Finset.mem_inter.2 ⟨?_, hp⟩)
      exact E.mem_localNonNbr.2
        ⟨(E.mem_localNonNbr.1 hp).1, hpq, fun hadj => hnadj hadj.symm⟩
    · exact E.localNonNbr_isClique hu (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq) hpq

/-- **The matching.**  In any splitting of `Γ(x)` into two `9`-cliques each
point of one side has exactly one neighbour on the other: its `9` neighbours
inside `Γ(x)` already contain the `8` other points of its own side. -/
theorem card_cross_eq_one {p : P} {X Y : Finset P}
    (hXY : X ∪ Y = E.blockGraph.neighborFinset x) (hdisj : Disjoint X Y)
    (hX : X.card = 9) (hXc : E.blockGraph.IsClique (X : Set P)) (hp : p ∈ X) :
    (Y.filter fun q => E.blockGraph.Adj p q).card = 1 := by
  classical
  have hxp : E.blockGraph.Adj x p := by
    have hmem : p ∈ E.blockGraph.neighborFinset x := hXY ▸ Finset.mem_union_left _ hp
    exact (SimpleGraph.mem_neighborFinset _ _ _).1 hmem
  have hXp : (X.filter fun q => E.blockGraph.Adj p q) = X.erase p := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_erase]
    exact ⟨fun hq => ⟨hq.2.ne', hq.1⟩, fun hq =>
      ⟨hq.2, hXc (Finset.mem_coe.2 hp) (Finset.mem_coe.2 hq.2) (Ne.symm hq.1)⟩⟩
  have hlocal : ((X ∪ Y).filter fun q => E.blockGraph.Adj p q) = E.localNbr x p := by
    rw [hXY]
    ext q
    simp only [Finset.mem_filter, SimpleGraph.mem_neighborFinset, E.mem_localNbr]
  have hfd : Disjoint (X.filter fun q => E.blockGraph.Adj p q)
      (Y.filter fun q => E.blockGraph.Adj p q) := Finset.disjoint_filter_filter hdisj
  have hcard := Finset.card_union_of_disjoint hfd
  rw [← Finset.filter_union, hlocal, E.card_localNbr hxp, hXp,
    Finset.card_erase_of_mem hp, hX] at hcard
  omega

/-- `Γ(x)` splits into two `9`-cliques, and every point of
either side has exactly one neighbour on the other; i.e. the complement of the
local graph at `x` is `K₉,₉` minus a perfect matching, so the local graph is
`K₉ □ K₂`. -/
theorem local_split_matching (x : P) :
    ∃ X Y : Finset P, X ∪ Y = E.blockGraph.neighborFinset x ∧ Disjoint X Y ∧
      X.card = 9 ∧ Y.card = 9 ∧
      E.blockGraph.IsClique (X : Set P) ∧ E.blockGraph.IsClique (Y : Set P) ∧
      (∀ p ∈ X, (Y.filter fun q => E.blockGraph.Adj p q).card = 1) ∧
      (∀ q ∈ Y, (X.filter fun p => E.blockGraph.Adj q p).card = 1) := by
  obtain ⟨X, Y, hXY, hdisj, hX, hY, hXc, hYc⟩ := E.local_split x
  have hYX : Y ∪ X = E.blockGraph.neighborFinset x := by rw [Finset.union_comm]; exact hXY
  exact ⟨X, Y, hXY, hdisj, hX, hY, hXc, hYc,
    fun p hp => E.card_cross_eq_one hXY hdisj hX hXc hp,
    fun q hq => E.card_cross_eq_one hYX hdisj.symm hY hYc hq⟩

end Derived45

end SRG266.QuasiSymmetric
