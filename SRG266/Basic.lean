/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

/-!
# The hypothetical strongly regular graph `srg(266, 45, 0, 9)`

This file fixes the graph-theoretic interface used throughout the project.  It
introduces the first and second subconstituents at a root vertex and proves
their cardinalities directly from `SimpleGraph.IsSRGWith`.

No classification theorem or computer-generated certificate is used here.
-/

open scoped BigOperators

namespace SRG266

variable {V : Type*} [Fintype V]

/-- The project-local name for the hypothetical SRG assumption. -/
abbrev IsHypothetical (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.IsSRGWith 266 45 0 9

section Rooted

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The first subconstituent at `x`, represented as a subtype. -/
abbrev FirstSubconstituent (x : V) := G.neighborSet x

/-- The second subconstituent at `x`, represented as a subtype. -/
abbrev SecondSubconstituent (x : V) := Gᶜ.neighborSet x

/-- A common neighbor of `x` and `y` is, in particular, in the first
subconstituent at `x`. -/
def commonNeighborEmbedding (x y : V) :
    G.commonNeighbors x y ↪ FirstSubconstituent G x where
  toFun z := ⟨z, z.property.1⟩
  inj' _ _ h :=
    Subtype.ext (congrArg (fun z : FirstSubconstituent G x => (z : V)) h)

/-- A local block is the set of neighbors in the first subconstituent. -/
def localBlock (x : V) (y : SecondSubconstituent G x) :
    Finset (FirstSubconstituent G x) :=
  Finset.univ.map (commonNeighborEmbedding G x y)

@[simp]
theorem mem_localBlock (x : V) (y : SecondSubconstituent G x)
    (z : FirstSubconstituent G x) :
    z ∈ localBlock G x y ↔ G.Adj (z : V) (y : V) := by
  constructor
  · rw [localBlock, Finset.mem_map]
    rintro ⟨a, _, rfl⟩
    exact a.property.2.symm
  · intro h
    rw [localBlock, Finset.mem_map]
    exact ⟨⟨z, z.property, h.symm⟩, Finset.mem_univ _, rfl⟩

theorem firstSubconstituent_card
    (hG : IsHypothetical G) (x : V) :
    Fintype.card (FirstSubconstituent G x) = 45 := by
  rw [G.card_neighborSet_eq_degree]
  exact hG.regular x

theorem secondSubconstituent_card
    [DecidableEq V] (hG : IsHypothetical G) (x : V) :
    Fintype.card (SecondSubconstituent G x) = 220 := by
  rw [Gᶜ.card_neighborSet_eq_degree]
  simpa using hG.compl_is_regular x

theorem localBlock_card
    (hG : IsHypothetical G) (x : V) (y : SecondSubconstituent G x) :
    (localBlock G x y).card = 9 := by
  rw [localBlock, Finset.card_map, Finset.card_univ]
  have hy : Gᶜ.Adj x (y : V) := y.property
  exact hG.of_not_adj ((G.compl_adj x y).mp hy).1 ((G.compl_adj x y).mp hy).2

end Rooted

end SRG266
