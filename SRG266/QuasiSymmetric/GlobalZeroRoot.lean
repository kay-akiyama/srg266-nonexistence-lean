/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.GlobalZeroGraph

/-!
# A rooted finite obstruction for the global zero graph

Fix a vertex `T` of a hypothetical `GlobalZeroGraph`.  Its twenty-four
neighbours form an independent family of triples on the eight points outside
`T`.  The other `140` triples meet that family in columns of prescribed
weights, and every pair of rows has a prescribed scalar product.

This file packages that first-neighbourhood extension as a smaller finite
object.  It is intended as the input of a chunked, exact certificate checker:
the checker need only enumerate the possible twenty-four-row neighbourhoods
and refute their `24 × 140` extensions.  The reduction below is mathematical;
it contains no enumeration and trusts no generated conclusion.
-/

namespace SRG266.QuasiSymmetric

/-- The triples outside a root and outside its chosen first neighbourhood. -/
def zeroSecond (root : Finset (Fin 11))
    (near : Finset (Finset (Fin 11))) : Finset (Finset (Fin 11)) :=
  (triples.erase root) \ near

@[simp] theorem mem_zeroSecond {root U : Finset (Fin 11)}
    {near : Finset (Finset (Fin 11))} :
    U ∈ zeroSecond root near ↔ U ∈ triples ∧ U ≠ root ∧ U ∉ near := by
  simp [zeroSecond, mem_triples, and_left_comm, and_assoc]

/-- The exact first-neighbourhood extension forced at one root. -/
structure GlobalZeroRoot where
  /-- The distinguished triple. -/
  root : Finset (Fin 11)
  /-- The twenty-four neighbours of the root. -/
  near : Finset (Finset (Fin 11))
  /-- For each remaining triple, its neighbours among `near`. -/
  cross : Finset (Fin 11) → Finset (Finset (Fin 11))
  root_triple : root ∈ triples
  near_closed : ∀ {U}, U ∈ near → U ∈ triples
  near_card : near.card = 24
  near_supported : ∀ {U}, U ∈ near → (root ∩ U).card = 0
  /-- A point off the root occurs in nine rows; a point of the root in none. -/
  near_vertex_balance : ∀ v,
    (near ∩ triplesAt v).card = if v ∈ root then 0 else 9
  /-- Every off-root point pair occurs in two or three rows. -/
  near_pair_balance : ∀ {v w : Fin 11}, v ≠ w → v ∉ root → w ∉ root →
    (near ∩ triplesThrough v w).card = 2 ∨
      (near ∩ triplesThrough v w).card = 3
  cross_closed : ∀ {V}, V ∈ zeroSecond root near → ∀ {U}, U ∈ cross V → U ∈ near
  /-- A remaining triple has `3 + #(root ∩ V)` neighbours in the first
  neighbourhood. -/
  cross_card : ∀ {V}, V ∈ zeroSecond root near →
    (cross V).card = (root ∩ V).card + 3
  /-- Cross edges still lie in the Kneser graph. -/
  cross_supported : ∀ {V}, V ∈ zeroSecond root near →
    ∀ {U}, U ∈ cross V → (U ∩ V).card = 0
  /-- Every first-neighbourhood row has its other twenty-three graph
  neighbours among the remaining triples. -/
  cross_row_card : ∀ {U}, U ∈ near →
    ((zeroSecond root near).filter fun X => U ∈ cross X).card = 23
  /-- In a fixed row, a root point occurs in eight cross columns, a point of
  the row occurs in none, and each of the other five points occurs in nine. -/
  cross_vertex_balance : ∀ {U}, U ∈ near → ∀ v,
    ((zeroSecond root near).filter fun X => U ∈ cross X ∧ v ∈ X).card =
      if v ∈ U then 0 else if v ∈ root then 8 else 9
  /-- The row-wise pair balance, with the common root column removed. -/
  cross_pair_balance : ∀ {U}, U ∈ near → ∀ {v w : Fin 11},
    v ≠ w → v ∉ U → w ∉ U →
    let count := ((zeroSecond root near).filter fun X =>
      U ∈ cross X ∧ X ∈ triplesThrough v w).card
    count + (if v ∈ root ∧ w ∈ root then 1 else 0) = 2 ∨
      count + (if v ∈ root ∧ w ∈ root then 1 else 0) = 3
  /-- Two distinct first-neighbourhood rows have scalar product
  `2 + #(U ∩ V)` after the common root is deleted. -/
  cross_pair : ∀ {U V}, U ∈ near → V ∈ near → U ≠ V →
    ((zeroSecond root near).filter fun X => U ∈ cross X ∧ V ∈ cross X).card =
      (U ∩ V).card + 2

namespace GlobalZeroGraph

variable (G : GlobalZeroGraph)

/-- Two neighbours of a vertex are not adjacent: the zero graph is
triangle-free. -/
theorem not_mem_neighbours_of_mem_neighbours {T U V : Finset (Fin 11)}
    (hT : T ∈ triples) (hU : U ∈ G.neighbours T)
    (hV : V ∈ G.neighbours T) : V ∉ G.neighbours U := by
  have hUt : U ∈ triples := G.closed hT hU
  have hTU : T ≠ U := by
    intro h
    subst U
    exact G.loopless hT hU
  have hzero := G.common hT hUt hTU
  rw [if_pos hU, Finset.card_eq_zero] at hzero
  intro hVU
  have hmem : V ∈ G.neighbours T ∩ G.neighbours U :=
    Finset.mem_inter.mpr ⟨hV, hVU⟩
  rw [hzero] at hmem
  simp at hmem

/-- At a chosen root, a global zero graph gives the exact `24 × 140`
first-neighbourhood extension. -/
def toGlobalZeroRoot (T : Finset (Fin 11)) (hT : T ∈ triples) : GlobalZeroRoot where
  root := T
  near := G.neighbours T
  cross := fun V => G.neighbours T ∩ G.neighbours V
  root_triple := hT
  near_closed := fun hU => G.closed hT hU
  near_card := G.degree hT
  near_supported := fun hU => G.supported hT hU
  near_vertex_balance := fun v => G.vertex_balance hT v
  near_pair_balance := fun hvw hvT hwT => G.pair_balance hT hvw hvT hwT
  cross_closed := by
    intro V hV U hU
    exact (Finset.mem_inter.mp hU).1
  cross_card := by
    intro V hV
    obtain ⟨hVt, hVT, hVnear⟩ := mem_zeroSecond.mp hV
    rw [G.common hT hVt (Ne.symm hVT), if_neg hVnear]
  cross_supported := by
    intro V hV U hU
    obtain ⟨hVt, -, -⟩ := mem_zeroSecond.mp hV
    have hUV := (Finset.mem_inter.mp hU).2
    simpa [Finset.inter_comm] using G.supported hVt hUV
  cross_row_card := by
    intro U hU
    have hUt : U ∈ triples := G.closed hT hU
    have hrootU : T ∈ G.neighbours U := (G.symmetric hT hUt).mp hU
    have hset :
        ((zeroSecond T (G.neighbours T)).filter fun X =>
          U ∈ G.neighbours T ∩ G.neighbours X) =
          (G.neighbours U).erase T := by
      ext X
      simp only [Finset.mem_filter, mem_zeroSecond, Finset.mem_inter,
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨hXt, hXT, -⟩, ⟨-, hUX⟩⟩
        exact ⟨hXT, (G.symmetric hUt hXt).mpr hUX⟩
      · rintro ⟨hXT, hXU⟩
        have hXt : X ∈ triples := G.closed hUt hXU
        have hXnotNear : X ∉ G.neighbours T := by
          intro hXnear
          exact (G.not_mem_neighbours_of_mem_neighbours hT hU hXnear) hXU
        exact ⟨⟨hXt, hXT, hXnotNear⟩,
          ⟨hU, (G.symmetric hUt hXt).mp hXU⟩⟩
    rw [hset, Finset.card_erase_of_mem hrootU, G.degree hUt]
  cross_vertex_balance := by
    intro U hU v
    have hUt : U ∈ triples := G.closed hT hU
    have hrootU : T ∈ G.neighbours U := (G.symmetric hT hUt).mp hU
    have hset :
        ((zeroSecond T (G.neighbours T)).filter fun X =>
          U ∈ G.neighbours T ∩ G.neighbours X ∧ v ∈ X) =
          (G.neighbours U ∩ triplesAt v).erase T := by
      ext X
      simp only [Finset.mem_filter, mem_zeroSecond, Finset.mem_inter,
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨hXt, hXT, -⟩, ⟨⟨-, hUX⟩, hvX⟩⟩
        exact ⟨hXT, (G.symmetric hUt hXt).mpr hUX,
          mem_triplesAt.mpr ⟨hXt, hvX⟩⟩
      · rintro ⟨hXT, hXU, hXat⟩
        obtain ⟨hXt, hvX⟩ := mem_triplesAt.mp hXat
        have hXnotNear : X ∉ G.neighbours T := by
          intro hXnear
          exact (G.not_mem_neighbours_of_mem_neighbours hT hU hXnear) hXU
        exact ⟨⟨hXt, hXT, hXnotNear⟩,
          ⟨⟨hU, (G.symmetric hUt hXt).mp hXU⟩, hvX⟩⟩
    by_cases hvU : v ∈ U
    · have hzero := G.vertex_balance hUt v
      rw [if_pos hvU, Finset.card_eq_zero] at hzero
      rw [hset, hzero]
      simp [hvU]
    · have hnine := G.vertex_balance hUt v
      rw [if_neg hvU] at hnine
      by_cases hvT : v ∈ T
      · have hrootAt : T ∈ G.neighbours U ∩ triplesAt v :=
          Finset.mem_inter.mpr ⟨hrootU, mem_triplesAt.mpr ⟨hT, hvT⟩⟩
        rw [hset, Finset.card_erase_of_mem hrootAt, hnine]
        simp [hvU, hvT]
      · have hrootNotAt : T ∉ G.neighbours U ∩ triplesAt v := by
          intro h
          exact hvT (mem_triplesAt.mp (Finset.mem_inter.mp h).2).2
        rw [hset, Finset.erase_eq_of_notMem hrootNotAt, hnine]
        simp [hvU, hvT]
  cross_pair_balance := by
    intro U hU v w hvw hvU hwU
    dsimp only
    have hUt : U ∈ triples := G.closed hT hU
    have hrootU : T ∈ G.neighbours U := (G.symmetric hT hUt).mp hU
    have hset :
        ((zeroSecond T (G.neighbours T)).filter fun X =>
          U ∈ G.neighbours T ∩ G.neighbours X ∧ X ∈ triplesThrough v w) =
          (G.neighbours U ∩ triplesThrough v w).erase T := by
      ext X
      simp only [Finset.mem_filter, mem_zeroSecond, Finset.mem_inter,
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨hXt, hXT, -⟩, ⟨⟨-, hUX⟩, hXpair⟩⟩
        exact ⟨hXT, (G.symmetric hUt hXt).mpr hUX, hXpair⟩
      · rintro ⟨hXT, hXU, hXpair⟩
        have hXt : X ∈ triples := (mem_triplesThrough.mp hXpair).1
        have hXnotNear : X ∉ G.neighbours T := by
          intro hXnear
          exact (G.not_mem_neighbours_of_mem_neighbours hT hU hXnear) hXU
        exact ⟨⟨hXt, hXT, hXnotNear⟩,
          ⟨⟨hU, (G.symmetric hUt hXt).mp hXU⟩, hXpair⟩⟩
    have hfull := G.pair_balance hUt hvw hvU hwU
    by_cases hboth : v ∈ T ∧ w ∈ T
    · have hrootPair : T ∈ G.neighbours U ∩ triplesThrough v w :=
        Finset.mem_inter.mpr ⟨hrootU,
          mem_triplesThrough.mpr ⟨hT, hboth.1, hboth.2⟩⟩
      rw [hset, Finset.card_erase_of_mem hrootPair]
      rcases hfull with hfull | hfull <;> rw [hfull] <;> simp [hboth]
    · have hrootNotPair : T ∉ G.neighbours U ∩ triplesThrough v w := by
        intro h
        have hp := mem_triplesThrough.mp (Finset.mem_inter.mp h).2
        exact hboth ⟨hp.2.1, hp.2.2⟩
      rw [hset, Finset.erase_eq_of_notMem hrootNotPair]
      rcases hfull with hfull | hfull <;> rw [hfull] <;> simp [hboth]
  cross_pair := by
    intro U V hU hV hUV
    have hUt : U ∈ triples := G.closed hT hU
    have hVt : V ∈ triples := G.closed hT hV
    have hVnotU : V ∉ G.neighbours U :=
      G.not_mem_neighbours_of_mem_neighbours hT hU hV
    have hrootCommon : T ∈ G.neighbours U ∩ G.neighbours V := by
      exact Finset.mem_inter.mpr ⟨(G.symmetric hT hUt).mp hU,
        (G.symmetric hT hVt).mp hV⟩
    have hcommonCard : (G.neighbours U ∩ G.neighbours V).card =
        (U ∩ V).card + 3 := by
      rw [G.common hUt hVt hUV, if_neg hVnotU]
    have hset :
        ((zeroSecond T (G.neighbours T)).filter fun X =>
          U ∈ G.neighbours T ∩ G.neighbours X ∧
            V ∈ G.neighbours T ∩ G.neighbours X) =
          (G.neighbours U ∩ G.neighbours V).erase T := by
      ext X
      simp only [Finset.mem_filter, mem_zeroSecond, Finset.mem_inter,
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨hXt, hXT, -⟩, ⟨⟨-, hUX⟩, ⟨-, hVX⟩⟩⟩
        exact ⟨hXT, (G.symmetric hUt hXt).mpr hUX,
          (G.symmetric hVt hXt).mpr hVX⟩
      · rintro ⟨hXT, hXU, hXV⟩
        have hXt : X ∈ triples := G.closed hUt hXU
        have hXnotNear : X ∉ G.neighbours T := by
          intro hXnear
          exact (G.not_mem_neighbours_of_mem_neighbours hT hU hXnear) hXU
        exact ⟨⟨hXt, hXT, hXnotNear⟩,
          ⟨⟨hU, (G.symmetric hUt hXt).mp hXU⟩,
            ⟨hV, (G.symmetric hVt hXt).mp hXV⟩⟩⟩
    rw [hset, Finset.card_erase_of_mem hrootCommon, hcommonCard]
    omega

end GlobalZeroGraph

/-- The finite proposition whose checked refutation would eliminate every
global zero graph. -/
abbrev NoGlobalZeroRoot : Prop := IsEmpty GlobalZeroRoot

/-- Refuting all rooted first-neighbourhood extensions refutes the global zero
graph. -/
theorem noGlobalZeroGraph_of_noGlobalZeroRoot
    (h : NoGlobalZeroRoot) : NoGlobalZeroGraph := by
  refine ⟨fun G => ?_⟩
  let T : Finset (Fin 11) := {0, 1, 2}
  have hT : T ∈ triples := by
    rw [mem_triples]
    change ({0, 1, 2} : Finset (Fin 11)).card = 3
    have h01 : (0 : Fin 11) ≠ 1 := by
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
    have h02 : (0 : Fin 11) ≠ 2 := by
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
    have h12 : (1 : Fin 11) ≠ 2 := by
      intro heq
      have hval := congrArg Fin.val heq
      norm_num at hval
    rw [Finset.card_insert_of_notMem (by simp [h01, h02]),
      Finset.card_insert_of_notMem (by simp [h12]), Finset.card_singleton]
  exact h.elim (G.toGlobalZeroRoot T hT)

/-- The rooted finite refutation discharges the cherry-cover boundary. -/
theorem noResidualCherryCover_of_noGlobalZeroRoot
    (h : NoGlobalZeroRoot) : NoResidualCherryCover :=
  noResidualCherryCover_of_noGlobalZeroGraph
    (noGlobalZeroGraph_of_noGlobalZeroRoot h)

/-- The same rooted refutation eliminates the quasi-symmetric design. -/
theorem noQuasiSymmetricDesign56_of_noGlobalZeroRoot
    (h : NoGlobalZeroRoot) : NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noGlobalZeroRoot h)

end SRG266.QuasiSymmetric
