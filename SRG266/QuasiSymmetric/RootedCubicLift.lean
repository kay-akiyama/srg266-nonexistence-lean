/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalDesignRoot

/-!
# The intrinsic rooted cubic lift

This file extracts the small integral object at the heart of the residual
cherry-cover obstruction.  A root triple isolates a cubic graph on the other
eight vertices.  Its twenty-four disjoint neighbours are indexed by triples
on those eight vertices and carry cubic graphs which are disjoint from the
root graph and meet one another in three edges.

Unlike `GlobalDesignRoot`, the structure below does not retain the 140-column
second-neighbourhood extension.  It records exactly the data used by the
rooted-cubic argument:

* the root and the twenty-four isolated triples;
* the twenty-five cubic twelve-edge graphs;
* the exact point and pair multiplicities of the isolated triples;
* root-neighbour disjointness and neighbour-neighbour intersection three; and
* the four-valued edge-total law for the twenty-four neighbour graphs.

All fields are projected from `GlobalDesignRoot`, hence ultimately from an
arbitrary residual structure over an arbitrary cherry cover.  No
classification or finite search is used in the extraction.
-/

namespace SRG266.QuasiSymmetric

/-- The root row and its twenty-four-row cubic lift. -/
structure RootedCubicLift where
  /-- The three vertices isolated by the root cubic graph. -/
  root : Finset (Fin 11)
  /-- The twenty-four isolated triples naming the neighbouring rows. -/
  near : Finset (Finset (Fin 11))
  /-- The root and neighbour cubic edge sets. -/
  block : Finset (Fin 11) → Finset Edge11
  root_triple : root ∈ triples
  near_closed : ∀ {U}, U ∈ near → U ∈ triples
  near_card : near.card = 24
  near_supported : ∀ {U}, U ∈ near → (root ∩ U).card = 0
  /-- Every off-root point occurs in nine of the isolated triples. -/
  near_vertex_balance : ∀ v,
    (near ∩ triplesAt v).card = if v ∈ root then 0 else 9
  /-- Off the root, a pair occurs twice precisely when it is a root edge, and
  three times otherwise. -/
  near_pair_count : ∀ {v w : Fin 11}, (hvw : v ≠ w) → v ∉ root → w ∉ root →
    (near ∩ triplesThrough v w).card =
      if Edge11.mk' hvw ∈ block root then 2 else 3
  root_block_card : (block root).card = 12
  root_block_isolates : ∀ {x}, x ∈ root → arcDegree (block root) x = 0
  root_block_cubic : ∀ x, x ∉ root → arcDegree (block root) x = 3
  near_block_card : ∀ {U}, U ∈ near → (block U).card = 12
  near_block_isolates : ∀ {U}, U ∈ near → ∀ {x}, x ∈ U →
    arcDegree (block U) x = 0
  near_block_cubic : ∀ {U}, U ∈ near → ∀ x, x ∉ U →
    arcDegree (block U) x = 3
  root_near_disjoint : ∀ {U}, U ∈ near →
    ((block root) ∩ (block U)).card = 0
  near_block_meet : ∀ {U V}, U ∈ near → V ∈ near → U ≠ V →
    ((block U) ∩ (block V)).card = 3
  /-- The neighbour rows use a root-block edge zero times and every other
  edge `6 + #(e ∩ root)` times.  These are exactly the totals `0, 6, 7, 8`
  in the rooted-cubic formulation. -/
  near_edge_total : ∀ e : Edge11,
    (near.filter fun U => e ∈ block U).card =
      if e ∈ block root then 0 else 6 + (e.vertices ∩ root).card

/-- Existence of the intrinsic rooted-cubic object. -/
abbrev IsRootedCubicLift : Prop := Nonempty RootedCubicLift

/-- The intrinsic rooted-cubic obstruction. -/
abbrev NoRootedCubicLift : Prop := IsEmpty RootedCubicLift

namespace GlobalDesignRoot

variable (R : GlobalDesignRoot)

/-- Forget the second-neighbourhood columns of a rooted global design and
retain only its intrinsic twenty-four-row cubic lift. -/
def toRootedCubicLift : RootedCubicLift where
  root := R.root
  near := R.near
  block := R.block
  root_triple := R.root_triple
  near_closed := R.near_closed
  near_card := R.near_card
  near_supported := R.near_supported
  near_vertex_balance := R.near_vertex_balance
  near_pair_count := by
    intro v w hvw hv hw
    have h := R.near_pair_reconstruction hvw hv hw
    by_cases he : Edge11.mk' hvw ∈ R.block R.root
    · rw [if_pos he] at h ⊢
      omega
    · rw [if_neg he] at h ⊢
      exact h
  root_block_card := R.root_block_card
  root_block_isolates := R.root_block_isolates
  root_block_cubic := R.root_block_cubic
  near_block_card := R.near_block_card
  near_block_isolates := R.near_block_isolates
  near_block_cubic := R.near_block_cubic
  root_near_disjoint := R.root_near_disjoint
  near_block_meet := R.near_block_meet
  near_edge_total := R.near_edge_balance

end GlobalDesignRoot

namespace GlobalDesign

variable (G : GlobalDesign)

/-- Root an arbitrary global design at any one of its triples and discard the
unused second-neighbourhood data. -/
def toRootedCubicLift (T : Finset (Fin 11)) (hT : T ∈ triples) :
    RootedCubicLift :=
  (G.toGlobalDesignRoot T hT).toRootedCubicLift

end GlobalDesign

/-- Non-existence of the intrinsic rooted lift refutes every global residual
design. -/
theorem isEmpty_globalDesign_of_noRootedCubicLift
    (h : NoRootedCubicLift) : IsEmpty GlobalDesign := by
  refine ⟨fun G => ?_⟩
  let T : Finset (Fin 11) := {0, 1, 2}
  have hT : T ∈ triples := by
    decide +kernel
  exact h.elim (G.toRootedCubicLift T hT)

/-- The rooted-cubic obstruction discharges the residual cherry-cover
boundary, without a classification of derived designs. -/
theorem noResidualCherryCover_of_noRootedCubicLift
    (h : NoRootedCubicLift) : NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign
    (isEmpty_globalDesign_of_noRootedCubicLift h)

/-- The same intrinsic rooted obstruction eliminates the quasi-symmetric
design. -/
theorem noQuasiSymmetricDesign56_of_noRootedCubicLift
    (h : NoRootedCubicLift) : NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noRootedCubicLift h)

end SRG266.QuasiSymmetric
