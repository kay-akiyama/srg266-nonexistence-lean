/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.ArcSearch

/-!
# Fixed packed coordinates for the rooted search

The rooted certificates use the lexicographic order

`01, 02, ..., 0A, 12, ..., 9A`

on the fifty-five edges of `K₁₁`.  This module supplies both directions of
that dictionary and proves that they are inverse.  The large searches can
therefore use 55-bit natural numbers, while their logical consumers can move
back to `Finset Edge11` through `EdgeCoding.edgesOfMask`.

Only the small finite table identities are evaluated with `decide +kernel`.
No native evaluator or bit-vector decision procedure is used.
-/

namespace SRG266.QuasiSymmetric.RootCoordinates

/-- Six-bit key-to-position table for lexicographic edge order. -/
def edgeTable : ℕ :=
  4036555462272590509014231179511948754600926240115452891845127336004463717266421249867039894124351032296628813832894758960819493973353776812914611371675630568212768903168180458796214860621757301657600

/-- Seven-bit position-to-key table for lexicographic edge order. -/
def edgeInverseTable : ℕ :=
  67581574371031068333602731149178551470779869858207487422963755974072406746687763043846033940204938429054575611789569

/-- Fifty-five-bit vertex-star masks, one field per vertex. -/
def starTable : ℕ :=
  108991677901128512174663029445058769569436046478795662557799293465216992154148682745813825266778440282484449285430912777790327234590540167247519059745033923890221929106167768700421119

theorem edgeTable_lt : ∀ a < 11, ∀ b < 11, a < b →
    slice edgeTable 6 (11 * a + b) < 55 := by
  decide +kernel

theorem edgeTable_inv : ∀ a < 11, ∀ b < 11, a < b →
    slice edgeInverseTable 7 (slice edgeTable 6 (11 * a + b)) =
      11 * a + b := by
  decide +kernel

/-- The fixed lexicographic edge coding. -/
def edgeCoding : EdgeCoding :=
  codingOfTable edgeTable edgeInverseTable edgeTable_lt edgeTable_inv

/-- The packed star of a vertex. -/
def starMask (v : ℕ) : ℕ := slice starTable 55 v

theorem starTable_spec : ∀ v < 11, ∀ a < 11, ∀ b < 11, a < b →
    (starMask v).testBit (slice edgeTable 6 (11 * a + b)) =
      decide (v = a ∨ v = b) := by
  decide +kernel

/-- Packed star membership agrees with endpoint membership. -/
theorem starMask_spec (v : Fin 11) (e : Edge11) :
    (starMask v.val).testBit (edgeCoding.idx e) = decide (v ∈ e.vertices) :=
  star_spec_of_keys (slice starTable 55) starTable_spec v e

theorem starMask_lt (v : Fin 11) : starMask v.val < 2 ^ 55 :=
  slice_lt _ _ v.val

/-- Decoding a packed star gives the ordinary edge star. -/
theorem edgesOfMask_starMask (v : Fin 11) :
    edgeCoding.edgesOfMask (starMask v.val) = Edge11.star v := by
  ext e
  simp [EdgeCoding.mem_edgesOfMask, starMask_spec, Edge11.mem_star]

/-- Four-bit table of lower endpoints, indexed by edge position. -/
def edgeLoTable : ℕ :=
  1003949748801945808873498625453003612742896985211069042099696435200

/-- Four-bit table of upper endpoints, indexed by edge position. -/
def edgeHiTable : ℕ :=
  1122917926740683552240427753845279642627165539472198912449655948065

theorem edgeLo_lt : ∀ i < 55, slice edgeLoTable 4 i < 11 := by
  decide +kernel

theorem edgeHi_lt : ∀ i < 55, slice edgeHiTable 4 i < 11 := by
  decide +kernel

theorem edgeLo_ne_hi : ∀ i < 55,
    slice edgeLoTable 4 i ≠ slice edgeHiTable 4 i := by
  decide +kernel

theorem edgeLo_lt_hi : ∀ i < 55,
    slice edgeLoTable 4 i < slice edgeHiTable 4 i := by
  decide +kernel

theorem edgePosition_spec : ∀ i < 55,
    slice edgeTable 6
      (11 * slice edgeLoTable 4 i + slice edgeHiTable 4 i) = i := by
  decide +kernel

/-- The lower endpoint of a numbered edge. -/
def edgeLo (i : Fin 55) : Fin 11 :=
  ⟨slice edgeLoTable 4 i.val, edgeLo_lt i.val i.isLt⟩

/-- The upper endpoint of a numbered edge. -/
def edgeHi (i : Fin 55) : Fin 11 :=
  ⟨slice edgeHiTable 4 i.val, edgeHi_lt i.val i.isLt⟩

/-- The 11-bit endpoint mask at a numeric edge position. -/
def edgeVertexMask (i : ℕ) : ℕ :=
  2 ^ slice edgeLoTable 4 i ||| 2 ^ slice edgeHiTable 4 i

/-- The edge at a lexicographic position. -/
def edgeAt (i : Fin 55) : Edge11 :=
  Edge11.ofLt (a := edgeLo i) (b := edgeHi i) (by
    change (edgeLo i).val < (edgeHi i).val
    exact edgeLo_lt_hi i.val i.isLt)

/-- Looking up the edge at a position and coding it returns that position. -/
theorem idx_edgeAt : ∀ i : Fin 55, edgeCoding.idx (edgeAt i) = i.val := by
  intro i
  rw [edgeAt, edgeCoding, idx_ofLt]
  exact edgePosition_spec i.val i.isLt

/-- Decoding the coordinate assigned to an edge recovers that edge. -/
@[simp] theorem edgeAt_idx (e : Edge11) :
    edgeAt ⟨edgeCoding.idx e, edgeCoding.idx_lt e⟩ = e := by
  apply edgeCoding.idx_injective
  rw [idx_edgeAt]

/-- The executable list of all fifty-five edges, in packed-coordinate order. -/
def edges : List Edge11 := List.ofFn edgeAt

@[simp] theorem length_edges : edges.length = 55 := by
  simp [edges]

/-- Every edge occurs in the executable coordinate list. -/
theorem mem_edges (e : Edge11) : e ∈ edges := by
  rw [edges, List.mem_ofFn]
  let i : Fin 55 := ⟨edgeCoding.idx e, edgeCoding.idx_lt e⟩
  refine ⟨i, edgeCoding.idx_injective ?_⟩
  rw [idx_edgeAt]

/-- The coordinate list has no repeated edge. -/
theorem nodup_edges : edges.Nodup := by
  rw [edges, List.nodup_ofFn]
  intro i j h
  apply Fin.ext
  have := congrArg edgeCoding.idx h
  simpa [idx_edgeAt] using this

end SRG266.QuasiSymmetric.RootCoordinates
