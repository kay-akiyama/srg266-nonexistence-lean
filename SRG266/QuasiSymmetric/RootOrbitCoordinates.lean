/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootNearCompression
import SRG266.Search.ExactCountCNF

/-!
# Consecutive coordinates for rooted orbit certificates

The orbit-cover certificate has two small Boolean layers:

* 28 variables for a cubic graph on the eight vertices outside the root;
* 56 variables for the triples on those eight vertices.

This module defines both dictionaries, their exact-count CNFs, and the packed
permutation action used by certificate witnesses.  Every table is generated
from `List.range`; the six cubic representatives are the only literal data.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- The 28 two-subset characteristic masks of `Fin 8`, in lexicographic
combination order. -/
def edge8Codes : List ℕ :=
  (List.range 8).flatMap fun a =>
    ((List.range 8).drop (a + 1)).map fun b => 2 ^ a ||| 2 ^ b

/-- The 56 three-subset characteristic masks of `Fin 8`, in the same order as
the compact rooted-neighbourhood coordinates. -/
def triple8Codes : List ℕ :=
  (List.range 8).flatMap fun a =>
    ((List.range 8).drop (a + 1)).flatMap fun b =>
      ((List.range 8).drop (b + 1)).map fun c =>
        2 ^ a ||| 2 ^ b ||| 2 ^ c

theorem length_edge8Codes : edge8Codes.length = 28 := by
  decide +kernel

theorem nodup_edge8Codes : edge8Codes.Nodup := by
  decide +kernel

theorem length_triple8Codes : triple8Codes.length = 56 := by
  decide +kernel

theorem nodup_triple8Codes : triple8Codes.Nodup := by
  decide +kernel

theorem rootNearCompressedCodes_eq :
    rootNearCompressedCodes = triple8Codes.map fun code => 8 * code := by
  rfl

/-- Variables for the seven edges incident with vertex `v`. -/
def edge8StarVariables (v : ℕ) : List ℕ :=
  (edge8Codes.zipIdx.filter fun codeAndIndex =>
    codeAndIndex.1.testBit v).map Prod.snd

/-- Variables for the six triples containing the edge with characteristic
mask `edgeCode`. -/
def triple8PairVariables (edgeCode : ℕ) : List ℕ :=
  (triple8Codes.zipIdx.filter fun codeAndIndex =>
    (codeAndIndex.1 &&& edgeCode) == edgeCode).map Prod.snd

/-- Eight degree-three constraints for a labelled cubic graph. -/
def cubic8Constraints : List (List ℕ × ℕ) :=
  (List.range 8).map fun v => (edge8StarVariables v, 3)

/-- The 28 pair demands of a rooted first neighbourhood. -/
def near8Constraints (rootGraph : ℕ) : List (List ℕ × ℕ) :=
  edge8Codes.zipIdx.map fun codeAndIndex =>
    (triple8PairVariables codeAndIndex.1,
      if rootGraph.testBit codeAndIndex.2 then 2 else 3)

/-- A 28-bit mask is cubic in the exact-count certificate semantics. -/
abbrev IsCubic8 (rootGraph : ℕ) : Prop :=
  ∀ constraint ∈ cubic8Constraints,
    popcount (localAssignmentMask constraint.1 rootGraph) = constraint.2

/-- A 56-bit near mask has the pair demands prescribed by `rootGraph`. -/
abbrev IsNear8For (rootGraph nearMask : ℕ) : Prop :=
  ∀ constraint ∈ near8Constraints rootGraph,
    popcount (localAssignmentMask constraint.1 nearMask) = constraint.2

/-- The six labelled cubic representatives used by the generator. -/
def rootGraphRepresentatives : List ℕ :=
  [264249735, 260587911, 253002375, 129008263, 219760135, 187254279]

theorem rootGraphRepresentatives_length :
    rootGraphRepresentatives.length = 6 := by
  decide +kernel

theorem rootGraphRepresentatives_cubic :
    ∀ rootGraph ∈ rootGraphRepresentatives, IsCubic8 rootGraph := by
  decide +kernel

theorem rootGraphRepresentative_lt {rootGraph : ℕ}
    (hmem : rootGraph ∈ rootGraphRepresentatives) : rootGraph < 2 ^ 28 := by
  simp only [rootGraphRepresentatives, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Image of a vertex under a permutation packed in eight three-bit fields. -/
def packedVertexImage (permutationCode vertex : ℕ) : ℕ :=
  slice permutationCode 3 vertex

/-- A packed code describes a permutation precisely when its eight images are
in range and pairwise distinct. -/
def PackedPerm8OK (permutationCode : ℕ) : Prop :=
  ((List.range 8).all fun vertex =>
    decide (packedVertexImage permutationCode vertex < 8)) = true ∧
    ((List.range 8).map (packedVertexImage permutationCode)).Nodup

instance (permutationCode : ℕ) : Decidable (PackedPerm8OK permutationCode) :=
  by unfold PackedPerm8OK; infer_instance

/-- The eight images stored in a packed permutation code. -/
def packedVertexImages (permutationCode : ℕ) : List ℕ :=
  (List.range 8).map (packedVertexImage permutationCode)

/-- The checked forward function on compact vertices. -/
def packedFin8Image (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (vertex : Fin 8) : Fin 8 :=
  ⟨packedVertexImage permutationCode vertex.val, by
    have h := (List.all_eq_true.mp hperm.1) vertex.val
      (List.mem_range.mpr vertex.isLt)
    simpa [decide_eq_true_eq] using h⟩

theorem packedFin8Image_injective (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    Function.Injective (packedFin8Image permutationCode hperm) := by
  intro x y hxy
  apply Fin.ext
  have hx : x.val < (packedVertexImages permutationCode).length := by
    simp [packedVertexImages]
  have hy : y.val < (packedVertexImages permutationCode).length := by
    simp [packedVertexImages]
  have hitems :
      (packedVertexImages permutationCode)[x.val]'hx =
        (packedVertexImages permutationCode)[y.val]'hy := by
    simpa [packedVertexImages, packedFin8Image] using congrArg Fin.val hxy
  exact (List.Nodup.getElem_inj_iff hperm.2).mp hitems

theorem mem_packedVertexImages (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (vertex : Fin 8) :
    vertex.val ∈ packedVertexImages permutationCode := by
  have hbijective : Function.Bijective
      (packedFin8Image permutationCode hperm) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨packedFin8Image_injective permutationCode hperm, rfl⟩
  obtain ⟨preimage, hpreimage⟩ := hbijective.2 vertex
  rw [packedVertexImages, List.mem_map]
  exact ⟨preimage.val, List.mem_range.mpr preimage.isLt,
    congrArg Fin.val hpreimage⟩

/-- A checked packed permutation code acts as a computable permutation of
`Fin 8`.  Its inverse is obtained by lookup in the checked noduplicate image
list, so concrete certificate equalities can be reduced by the kernel. -/
def packedPerm8Equiv (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) : Equiv.Perm (Fin 8) where
  toFun := packedFin8Image permutationCode hperm
  invFun := fun vertex =>
    ⟨(packedVertexImages permutationCode).idxOf vertex.val,
      (List.idxOf_lt_length_iff.mpr
        (mem_packedVertexImages permutationCode hperm vertex))⟩
  left_inv := by
    intro vertex
    apply Fin.ext
    have hi : vertex.val < (packedVertexImages permutationCode).length := by
      simp [packedVertexImages]
    simpa [packedVertexImages, packedFin8Image] using
      List.get_idxOf hperm.2 ⟨vertex.val, hi⟩
  right_inv := by
    intro vertex
    apply Fin.ext
    have hi : (packedVertexImages permutationCode).idxOf vertex.val <
        (packedVertexImages permutationCode).length :=
      List.idxOf_lt_length_iff.mpr
        (mem_packedVertexImages permutationCode hperm vertex)
    let j := (packedVertexImages permutationCode).idxOf vertex.val
    have hj : j < (packedVertexImages permutationCode).length := hi
    have hget : (packedVertexImages permutationCode)[j] = vertex.val :=
      List.getElem_idxOf hj
    change ((List.range 8).map (packedVertexImage permutationCode))[j] =
      vertex.val at hget
    rw [List.getElem_map, List.getElem_range] at hget
    simpa [j, packedFin8Image] using hget

@[simp] theorem packedPerm8Equiv_apply (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (vertex : Fin 8) :
    (packedPerm8Equiv permutationCode hperm vertex).val =
      packedVertexImage permutationCode vertex.val := by
  rfl

/-- Relabel an eight-vertex characteristic mask by a packed permutation. -/
def relabelVertexCode8 (permutationCode vertexCode : ℕ) : ℕ :=
  itemPositionsMask <|
    ((List.range 8).filter fun vertex => vertexCode.testBit vertex).map fun vertex =>
      packedVertexImage permutationCode vertex

/-- Relabel a consecutive family mask whose item dictionary consists of
eight-vertex characteristic masks. -/
def relabelIndexedMask8 (itemCodes : List ℕ) (permutationCode familyMask : ℕ) : ℕ :=
  itemPositionsMask <|
    ((itemCodes.zipIdx.filter fun codeAndIndex =>
      familyMask.testBit codeAndIndex.2).map fun codeAndIndex =>
        itemCodes.idxOf (relabelVertexCode8 permutationCode codeAndIndex.1))

def relabelEdgeMask8 (permutationCode edgeMask : ℕ) : ℕ :=
  relabelIndexedMask8 edge8Codes permutationCode edgeMask

def relabelTripleMask8 (permutationCode tripleMask : ℕ) : ℕ :=
  relabelIndexedMask8 triple8Codes permutationCode tripleMask

/-- Cubic-cover counterexample CNF: a cubic graph not present in the supplied
orbit list. -/
def cubic8CoverFmla (orbitMasks : List ℕ) : Sat.Fmla :=
  exactCountCoverFmla 28 cubic8Constraints orbitMasks

/-- Fixed-root near-cover counterexample CNF. -/
def near8CoverFmla (rootGraph : ℕ) (orbitMasks : List ℕ) : Sat.Fmla :=
  exactCountCoverFmla 56 (near8Constraints rootGraph) orbitMasks

def cubic8CoverChunkFmla (prefixMask : ℕ) (orbitMasks : List ℕ) : Sat.Fmla :=
  exactCountCoverChunkFmla 28 4 prefixMask cubic8Constraints orbitMasks

def near8CoverChunkFmla (rootGraph prefixBits prefixMask : ℕ)
    (orbitMasks : List ℕ) : Sat.Fmla :=
  exactCountCoverChunkFmla 56 prefixBits prefixMask
    (near8Constraints rootGraph) orbitMasks

end SRG266.QuasiSymmetric
