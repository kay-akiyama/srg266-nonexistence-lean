/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalZeroRoot

/-!
# A rooted block-and-zero-graph obstruction

The rooted zero graph of `GlobalZeroRoot.lean` remembers the complete first
neighbourhood of a triple, but forgets the twelve-edge blocks which produced
that graph.  This file stores the root block and its twenty-four disjoint
neighbour blocks.  The resulting object records, simultaneously:

* the exact `24 × 140` zero-graph extension;
* twenty-five cubic graphs on eight vertices;
* disjointness from the root block;
* intersection number three between every two neighbour blocks;
* reconstruction of the root block from pair multiplicities; and
* the exact number of neighbour blocks through every edge of `K₁₁`.

Thus `GlobalDesignRoot` is a strictly stronger finite search target than
`GlobalZeroRoot`.  Every field below is derived from the axioms of a
`GlobalDesign`; no enumeration or certificate is trusted here.
-/

namespace SRG266.QuasiSymmetric

/-- The exact first-neighbourhood data of a global design, retaining both its
zero graph and the root and neighbour blocks. -/
structure GlobalDesignRoot extends GlobalZeroRoot where
  /-- The twelve-edge block indexed by a triple.  Only the root and its first
  neighbourhood are constrained by this structure. -/
  block : Finset (Fin 11) → Finset Edge11
  root_block_card : (block root).card = 12
  root_block_isolates : ∀ {x}, x ∈ root → arcDegree (block root) x = 0
  root_block_cubic : ∀ x, x ∉ root → arcDegree (block root) x = 3
  near_block_card : ∀ {U}, U ∈ near → (block U).card = 12
  near_block_isolates : ∀ {U}, U ∈ near → ∀ {x}, x ∈ U →
    arcDegree (block U) x = 0
  near_block_cubic : ∀ {U}, U ∈ near → ∀ x, x ∉ U →
    arcDegree (block U) x = 3
  /-- A first-neighbour block is disjoint from the root block. -/
  root_near_disjoint : ∀ {U}, U ∈ near →
    ((block root) ∩ (block U)).card = 0
  /-- Triangle-freeness of the zero graph forces every two distinct
  first-neighbour blocks to meet in three edges. -/
  near_block_meet : ∀ {U V}, U ∈ near → V ∈ near → U ≠ V →
    ((block U) ∩ (block V)).card = 3
  /-- The local pair law reconstructs membership in the root block. -/
  near_pair_reconstruction : ∀ {v w : Fin 11}, (hvw : v ≠ w) → v ∉ root → w ∉ root →
    (near ∩ triplesThrough v w).card +
      (if Edge11.mk' hvw ∈ block root then 1 else 0) = 3
  /-- The root neighbourhood misses the root block and covers every other edge
  with multiplicity `6 + #(e ∩ root)`. -/
  near_edge_balance : ∀ e : Edge11,
    (near.filter fun U => e ∈ block U).card =
      if e ∈ block root then 0 else 6 + (e.vertices ∩ root).card
  /-- The exact row-pair law satisfied by the block data.  The disjunctive law
  in `GlobalZeroRoot` is its block-free shadow. -/
  cross_pair_reconstruction : ∀ {U}, U ∈ near → ∀ {v w : Fin 11},
    (hvw : v ≠ w) → v ∉ U → w ∉ U →
    let count := ((zeroSecond root near).filter fun X =>
      U ∈ cross X ∧ X ∈ triplesThrough v w).card
    count + (if v ∈ root ∧ w ∈ root then 1 else 0) +
      (if Edge11.mk' hvw ∈ block U then 1 else 0) = 3

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Membership in the root block is reconstructed by the low pair
multiplicity in its first neighbourhood.  Thus the root block need not be
supplied independently by a finite certificate. -/
theorem mem_rootBlock_iff_near_pair_eq_two {v w : Fin 11} (hvw : v ≠ w)
    (hv : v ∉ R.root) (hw : w ∉ R.root) :
    Edge11.mk' hvw ∈ R.block R.root ↔
      (R.near ∩ triplesThrough v w).card = 2 := by
  have h := R.near_pair_reconstruction hvw hv hw
  constructor
  · intro hmem
    rw [if_pos hmem] at h
    omega
  · intro htwo
    by_contra hmem
    rw [if_neg hmem] at h
    omega

/-- Dually, the high pair multiplicity is exactly non-membership in the root
block. -/
theorem not_mem_rootBlock_iff_near_pair_eq_three {v w : Fin 11} (hvw : v ≠ w)
    (hv : v ∉ R.root) (hw : w ∉ R.root) :
    Edge11.mk' hvw ∉ R.block R.root ↔
      (R.near ∩ triplesThrough v w).card = 3 := by
  have h := R.near_pair_reconstruction hvw hv hw
  constructor
  · intro hmem
    rw [if_neg hmem] at h
    exact h
  · intro hthree hmem
    rw [if_pos hmem] at h
    omega

/-- An edge belongs to the root block exactly when none of the twenty-four
neighbour blocks contains it. -/
theorem mem_rootBlock_iff_near_coverage_zero (e : Edge11) :
    e ∈ R.block R.root ↔
      (R.near.filter fun U => e ∈ R.block U).card = 0 := by
  constructor
  · intro he
    rw [R.near_edge_balance e, if_pos he]
  · intro hzero
    by_contra he
    have h := R.near_edge_balance e
    rw [if_neg he, hzero] at h
    omega

/-- The root block is definitionally dispensable: it is the set of edges not
covered by any first-neighbour block. -/
theorem rootBlock_eq_uncovered :
    R.block R.root =
      (Finset.univ.filter fun e : Edge11 =>
        (R.near.filter fun U => e ∈ R.block U).card = 0) := by
  ext e
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    R.mem_rootBlock_iff_near_coverage_zero e

end GlobalDesignRoot

namespace GlobalDesign

variable (G : GlobalDesign)

/-- A global design supplies the full rooted block-and-zero-graph obstruction
at every one of its `165` triples. -/
def toGlobalDesignRoot (T : Finset (Fin 11)) (hT : T ∈ triples) :
    GlobalDesignRoot where
  toGlobalZeroRoot := G.toGlobalZeroGraph.toGlobalZeroRoot T hT
  block := G.block
  root_block_card := G.block_card T hT
  root_block_isolates := fun hx => G.block_isolates T hT _ hx
  root_block_cubic := fun x hx => G.block_cubic T hT x hx
  near_block_card := by
    intro U hU
    exact G.block_card U (G.mem_disjointFrom.mp hU).1
  near_block_isolates := by
    intro U hU x hx
    exact G.block_isolates U (G.mem_disjointFrom.mp hU).1 x hx
  near_block_cubic := by
    intro U hU x hx
    exact G.block_cubic U (G.mem_disjointFrom.mp hU).1 x hx
  root_near_disjoint := by
    intro U hU
    exact (G.mem_disjointFrom.mp hU).2
  near_block_meet := by
    intro U V hU hV hUV
    have hUt : U ∈ triples := (G.mem_disjointFrom.mp hU).1
    have hVt : V ∈ triples := (G.mem_disjointFrom.mp hV).1
    have hnot : V ∉ G.disjointFrom U :=
      G.toGlobalZeroGraph.not_mem_neighbours_of_mem_neighbours hT hU hV
    rcases G.block_meet U hUt V hVt hUV with hzero | hthree
    · exact absurd (G.mem_disjointFrom.mpr ⟨hVt, hzero⟩) hnot
    · exact hthree
  near_pair_reconstruction := by
    intro v w hvw hvT hwT
    exact G.card_disjointFrom_inter_triplesThrough hT hvw hvT hwT
  near_edge_balance := by
    intro e
    change ((G.disjointFrom T).filter fun U => e ∈ G.block U).card =
      if e ∈ G.block T then 0 else 6 + (e.vertices ∩ T).card
    by_cases he : e ∈ G.block T
    · rw [if_pos he, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro U hU heU
      have hzero := (G.mem_disjointFrom.mp hU).2
      have hempty : G.block T ∩ G.block U = ∅ := Finset.card_eq_zero.mp hzero
      have heBoth : e ∈ G.block T ∩ G.block U := Finset.mem_inter.mpr ⟨he, heU⟩
      rw [hempty] at heBoth
      simp at heBoth
    · rw [if_neg he]
      exact G.card_disjointFrom_filter_mem_block hT he
  cross_pair_reconstruction := by
    intro U hU v w hvw hvU hwU
    dsimp only
    change (((zeroSecond T (G.disjointFrom T)).filter fun X =>
      U ∈ G.disjointFrom T ∩ G.disjointFrom X ∧
        X ∈ triplesThrough v w).card +
      (if v ∈ T ∧ w ∈ T then 1 else 0)) +
      (if Edge11.mk' hvw ∈ G.block U then 1 else 0) = 3
    have hUt : U ∈ triples := (G.mem_disjointFrom.mp hU).1
    have hrootU : T ∈ G.disjointFrom U :=
      (G.mem_disjointFrom_comm hT hUt).mp hU
    have hfull := G.card_disjointFrom_inter_triplesThrough hUt hvw hvU hwU
    have hset :
        ((zeroSecond T (G.disjointFrom T)).filter fun X =>
          U ∈ G.disjointFrom T ∩ G.disjointFrom X ∧ X ∈ triplesThrough v w) =
          (G.disjointFrom U ∩ triplesThrough v w).erase T := by
      ext X
      simp only [Finset.mem_filter, mem_zeroSecond, Finset.mem_inter,
        Finset.mem_erase]
      constructor
      · rintro ⟨⟨hXt, hXT, -⟩, ⟨⟨-, hUX⟩, hXpair⟩⟩
        exact ⟨hXT, (G.mem_disjointFrom_comm hUt hXt).mpr hUX, hXpair⟩
      · rintro ⟨hXT, hXU, hXpair⟩
        have hXt : X ∈ triples := (mem_triplesThrough.mp hXpair).1
        have hXnotNear : X ∉ G.disjointFrom T := by
          intro hXnear
          exact (G.toGlobalZeroGraph.not_mem_neighbours_of_mem_neighbours hT hU hXnear) hXU
        exact ⟨⟨hXt, hXT, hXnotNear⟩,
          ⟨⟨hU, (G.mem_disjointFrom_comm hUt hXt).mp hXU⟩, hXpair⟩⟩
    by_cases hboth : v ∈ T ∧ w ∈ T
    · have hrootPair : T ∈ G.disjointFrom U ∩ triplesThrough v w :=
        Finset.mem_inter.mpr ⟨hrootU,
          mem_triplesThrough.mpr ⟨hT, hboth.1, hboth.2⟩⟩
      rw [hset, Finset.card_erase_of_mem hrootPair]
      rw [if_pos hboth]
      have hcardPos : 0 < (G.disjointFrom U ∩ triplesThrough v w).card :=
        Finset.card_pos.mpr ⟨T, hrootPair⟩
      omega
    · have hrootNotPair : T ∉ G.disjointFrom U ∩ triplesThrough v w := by
        intro h
        have hp := mem_triplesThrough.mp (Finset.mem_inter.mp h).2
        exact hboth ⟨hp.2.1, hp.2.2⟩
      rw [hset, Finset.erase_eq_of_notMem hrootNotPair]
      rw [if_neg hboth]
      exact hfull

end GlobalDesign

/-- The pure finite statement that the rooted block-and-zero-graph obstruction
does not exist. -/
abbrev NoGlobalDesignRoot : Prop := IsEmpty GlobalDesignRoot

/-- Refuting the rooted object refutes every global residual design. -/
theorem isEmpty_globalDesign_of_noGlobalDesignRoot
    (h : NoGlobalDesignRoot) : IsEmpty GlobalDesign := by
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
  exact h.elim (G.toGlobalDesignRoot T hT)

/-- A checked refutation of the rooted object discharges the cherry-cover
boundary. -/
theorem noResidualCherryCover_of_noGlobalDesignRoot
    (h : NoGlobalDesignRoot) : NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign
    (isEmpty_globalDesign_of_noGlobalDesignRoot h)

/-- The same rooted refutation eliminates the quasi-symmetric design. -/
theorem noQuasiSymmetricDesign56_of_noGlobalDesignRoot
    (h : NoGlobalDesignRoot) : NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noGlobalDesignRoot h)

end SRG266.QuasiSymmetric
