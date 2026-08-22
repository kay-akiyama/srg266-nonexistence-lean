/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.ResidualRigidity
import SRG266.QuasiSymmetric.CherryRecut

/-!
# The local design at a vertex, as a cover-free finite object

`SRG266/QuasiSymmetric/ResidualRigidity.lean` proves that a hypothetical
residual structure over a cherry cover of `K₁₁` is completely rigid: its `165`
blocks are indexed by the `165` triples of vertices they isolate, and for every
vertex `v` the `45` blocks isolating `v` form a symmetric `2-(45, 12, 3)` design
on the `45` edges of `K₁₁ − v`.

This file turns that local design into a **self-contained finite object** — the
structure `SRG266.QuasiSymmetric.LocalDesign` — and proves the reduction

> `IsEmpty (LocalDesign v)` for a single vertex `v`
> ⟹ `SRG266.QuasiSymmetric.NoResidualCherryCover`
> ⟹ `SRG266.NoQuasiSymmetricDesign56`.

A `LocalDesign v` mentions neither a cherry cover, nor a `Derived45`, nor a
`Residual165`, nor the `120` blocks in which `v` is not isolated: it is a family
of `45` sets of edges of `K₁₁ − v`, indexed by the `45` edges of `K₁₁ − v`
themselves, together with nine axioms.  Refuting it is therefore a
*cover-free* finite search.

## The object

Write `p` for an edge of `K₁₁ − v` used as an *index* and `e` for one used as a
*point*.  A `LocalDesign v` consists of blocks `block p ⊆ Edge11.off v` with

| field | statement |
|---|---|
| `block_subset` | `block p` misses `v` |
| `block_card` | `#(block p) = 12` |
| `block_isolates` | `block p` isolates both endpoints of `p` |
| `block_cubic` | `block p` has degree `3` at each of the other eight vertices |
| `block_meet` | distinct blocks meet in exactly `3` edges |
| `point_rep` | every point lies on exactly `12` blocks |
| `point_pair` | every two distinct points lie on exactly `3` blocks |
| `point_star` | the `12` blocks through a point `e` are indexed by a cubic graph on the eight vertices off `e` |

The last three are *derivable* from the first five (`point_rep` and `point_pair`
are the design identity `N Nᵀ = 9 I + 3 J ⟹ Nᵀ N = 9 I + 3 J`, and `point_star`
is the zero-variance count of
`SRG266.QuasiSymmetric.Residual165.localCount_two`), but they are recorded as
axioms because a residual structure supplies them for free and because they are
exactly the propagators a search wants.  With them the object is **self dual**:
`SRG266.QuasiSymmetric.LocalDesign.dual` sends a local design to the family
`e ↦ {p | e ∈ block p}`, which satisfies the same nine axioms — the exchange
pairs `block_card` with `point_rep`, `block_meet` with `point_pair` and
`block_cubic` with `point_star`, and fixes `block_isolates`.

## What is *not* claimed

Nothing here asserts that a `LocalDesign` fails to exist — that is the remaining
finite problem.  The content of the file is only that its non-existence at *one*
vertex is enough to discharge `SRG266.QuasiSymmetric.NoResidualCherryCover`.

There is no `decide`, no design datum and no case analysis anywhere in the file.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### An edge is determined by its endpoints -/

namespace Edge11

/-- An edge of `K₁₁` is determined by its two endpoints. -/
theorem vertices_injective :
    Function.Injective (vertices : Edge11 → Finset (Fin 11)) := by
  intro e f hef
  obtain ⟨a, b, hab, hverts⟩ := Finset.card_eq_two.mp (card_vertices e)
  have ha : a ∈ e.vertices := by rw [hverts]; simp
  have hb : b ∈ e.vertices := by rw [hverts]; simp
  have ha' : a ∈ f.vertices := hef ▸ ha
  have hb' : b ∈ f.vertices := hef ▸ hb
  rw [eq_of_mem_mem hab ha hb, eq_of_mem_mem hab ha' hb']

/-- Adjoining to an edge a vertex off it gives a triple. -/
theorem card_insert_vertices {v : Fin 11} {p : Edge11} (hp : v ∉ p.vertices) :
    (insert v p.vertices).card = 3 := by
  rw [Finset.card_insert_of_notMem hp, card_vertices]

end Edge11

/-! ### The local design -/

/-- **The local symmetric `2-(45, 12, 3)` design at a vertex `v` of `K₁₁`.**

The points and the blocks are both the `45` edges of `K₁₁ − v`; the block named
by the edge `p` is a cubic graph on the eight vertices other than `v` and the
two endpoints of `p`; any two distinct blocks meet in three edges, any two
distinct points lie on three blocks, and the blocks through a point `e` are
themselves named by a cubic graph on the eight vertices off `e`.

This is precisely the shape that
`SRG266.QuasiSymmetric.Residual165.localDesign` extracts from a hypothetical
residual structure, with every reference to the cherry cover removed.  The
function `block` is total on `Edge11` for convenience; it is constrained only on
`SRG266.QuasiSymmetric.Edge11.off v`. -/
structure LocalDesign (v : Fin 11) where
  /-- The block named by an edge of `K₁₁ − v`. -/
  block : Edge11 → Finset Edge11
  /-- Every block lives on the edges of `K₁₁ − v`. -/
  block_subset : ∀ p ∈ Edge11.off v, block p ⊆ Edge11.off v
  /-- Every block has `12` edges. -/
  block_card : ∀ p ∈ Edge11.off v, (block p).card = 12
  /-- The block named by `p` isolates the two endpoints of `p`. -/
  block_isolates : ∀ p ∈ Edge11.off v, ∀ x ∈ p.vertices, arcDegree (block p) x = 0
  /-- The block named by `p` is cubic at the eight vertices off `v` and `p`. -/
  block_cubic : ∀ p ∈ Edge11.off v, ∀ x : Fin 11, x ≠ v → x ∉ p.vertices →
    arcDegree (block p) x = 3
  /-- Two distinct blocks meet in exactly `3` edges. -/
  block_meet : ∀ p ∈ Edge11.off v, ∀ q ∈ Edge11.off v, p ≠ q →
    ((block p) ∩ (block q)).card = 3
  /-- Every point lies on exactly `12` blocks. -/
  point_rep : ∀ e ∈ Edge11.off v,
    ((Edge11.off v).filter fun p => e ∈ block p).card = 12
  /-- Two distinct points lie on exactly `3` common blocks. -/
  point_pair : ∀ e ∈ Edge11.off v, ∀ f ∈ Edge11.off v, e ≠ f →
    ((Edge11.off v).filter fun p => e ∈ block p ∧ f ∈ block p).card = 3
  /-- The `12` blocks through a point `e` are named by a cubic graph on the
  eight vertices off `v` and `e`. -/
  point_star : ∀ e ∈ Edge11.off v, ∀ u : Fin 11, u ≠ v → u ∉ e.vertices →
    ((Edge11.off v).filter fun p => u ∈ p.vertices ∧ e ∈ block p).card = 3

namespace LocalDesign

variable {v : Fin 11} (L : LocalDesign v)

/-- Every block isolates the centre `v` as well, so it is a cubic graph on
exactly eight of the eleven vertices. -/
theorem block_isolates_center {p : Edge11} (hp : p ∈ Edge11.off v) :
    arcDegree (L.block p) v = 0 := by
  rw [arcDegree, Finset.card_eq_zero]
  refine Finset.filter_eq_empty_iff.mpr fun {e} he hv => ?_
  exact (Edge11.mem_off.mp (L.block_subset p hp he)) hv

/-- Distinct indices name distinct blocks. -/
theorem block_injOn {p q : Edge11} (hp : p ∈ Edge11.off v) (hq : q ∈ Edge11.off v)
    (h : L.block p = L.block q) : p = q := by
  by_contra hpq
  have hmeet := L.block_meet p hp q hq hpq
  rw [h, Finset.inter_self, L.block_card q hq] at hmeet
  omega

/-- A point of a block misses both endpoints of the index of that block. -/
theorem notMem_vertices_of_mem_block {p e : Edge11} (hp : p ∈ Edge11.off v)
    (he : e ∈ L.block p) {x : Fin 11} (hx : x ∈ p.vertices) : x ∉ e.vertices := by
  have h0 : arcDegree (L.block p) x = 0 := L.block_isolates p hp x hx
  rw [arcDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  exact h0 he

/-! ### Self-duality -/

/-- The dual family of a local design: `dualBlock e` collects the indices whose
block contains `e`. -/
def dualBlock (e : Edge11) : Finset Edge11 :=
  (Edge11.off v).filter fun p => e ∈ L.block p

@[simp] theorem mem_dualBlock {e p : Edge11} :
    p ∈ L.dualBlock e ↔ p ∈ Edge11.off v ∧ e ∈ L.block p := Finset.mem_filter

/-- The degree of a dual block, as a count over the indices. -/
theorem arcDegree_dualBlock (e : Edge11) (x : Fin 11) :
    arcDegree (L.dualBlock e) x =
      ((Edge11.off v).filter fun p => x ∈ p.vertices ∧ e ∈ L.block p).card := by
  rw [arcDegree, dualBlock, Finset.filter_filter]
  exact congrArg Finset.card (Finset.filter_congr fun _ _ => and_comm)

/-- **The local design is self dual.**  Exchanging the roles of the points and
the indices of a `LocalDesign` gives a `LocalDesign`: the nine axioms are
permuted among themselves, `block_card ↔ point_rep`, `block_meet ↔ point_pair`
and `block_cubic ↔ point_star`, with `block_isolates` self-paired.

A refutation of `LocalDesign v` may therefore assume any property that is stable
under this exchange, which halves the symmetry-breaking work of a search. -/
def dual : LocalDesign v where
  block := L.dualBlock
  block_subset := fun _ _ => Finset.filter_subset _ _
  block_card := fun e he => L.point_rep e he
  block_isolates := by
    intro e he x hx
    rw [L.arcDegree_dualBlock, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp hcon
    exact L.notMem_vertices_of_mem_block hp hcon.2 hcon.1 hx
  block_cubic := fun e he x hxv hxe => by
    rw [L.arcDegree_dualBlock]
    exact L.point_star e he x hxv hxe
  block_meet := by
    intro e he f hf hef
    have hset : (L.dualBlock e) ∩ (L.dualBlock f) =
        (Edge11.off v).filter fun p => e ∈ L.block p ∧ f ∈ L.block p := by
      ext p
      simp only [Finset.mem_inter, mem_dualBlock, Finset.mem_filter]
      tauto
    rw [hset]
    exact L.point_pair e he f hf hef
  point_rep := by
    intro e he
    have hset : ((Edge11.off v).filter fun p => e ∈ L.dualBlock p) = L.block e := by
      ext p
      simp only [Finset.mem_filter, mem_dualBlock]
      constructor
      · rintro ⟨-, -, hb⟩
        exact hb
      · intro hb
        exact ⟨L.block_subset e he hb, he, hb⟩
    rw [hset]
    exact L.block_card e he
  point_pair := by
    intro e he f hf hef
    have hset : ((Edge11.off v).filter fun p => e ∈ L.dualBlock p ∧ f ∈ L.dualBlock p) =
        (L.block e) ∩ (L.block f) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_inter, mem_dualBlock]
      constructor
      · rintro ⟨-, ⟨-, h1⟩, -, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨L.block_subset e he h1, ⟨he, h1⟩, hf, h2⟩
    rw [hset]
    exact L.block_meet e he f hf hef
  point_star := by
    intro e he u huv hue
    have hset : ((Edge11.off v).filter fun p => u ∈ p.vertices ∧ e ∈ L.dualBlock p) =
        (L.block e).filter fun p => u ∈ p.vertices := by
      ext p
      simp only [Finset.mem_filter, mem_dualBlock]
      constructor
      · rintro ⟨-, hu, -, hb⟩
        exact ⟨hb, hu⟩
      · rintro ⟨hb, hu⟩
        exact ⟨L.block_subset e he hb, hu, he, hb⟩
    rw [hset]
    exact L.block_cubic e he u huv hue

@[simp] theorem dual_block (e : Edge11) : L.dual.block e = L.dualBlock e := rfl

end LocalDesign

/-! ### A residual structure produces a local design -/

namespace Residual165

variable {C : CherryCover} (R : Residual165 C.toDerived45)

/-- The index of the residual block isolating `v` and the two endpoints of an
edge `p` off `v`.  (The value at an edge through `v` is junk.) -/
noncomputable def localIndex (v : Fin 11) (p : Edge11) : Fin 165 :=
  if h : (insert v p.vertices).card = 3 then R.blockOf h else 0

/-- The block named by `p` isolates exactly `v` and the endpoints of `p`. -/
theorem isolatedTriple_localIndex {v : Fin 11} {p : Edge11} (hp : v ∉ p.vertices) :
    R.isolatedTriple (R.localIndex v p) = insert v p.vertices := by
  rw [localIndex, dif_pos (Edge11.card_insert_vertices hp)]
  exact R.isolatedTriple_blockOf _

/-- The block named by an edge off `v` does isolate `v`. -/
theorem localIndex_mem_isolating {v : Fin 11} {p : Edge11} (hp : v ∉ p.vertices) :
    R.localIndex v p ∈ R.isolating v := by
  rw [mem_isolating_iff, R.isolatedTriple_localIndex hp]
  exact Finset.mem_insert_self v p.vertices

/-- Distinct edges off `v` name distinct blocks. -/
theorem localIndex_injOn {v : Fin 11} {p q : Edge11} (hp : v ∉ p.vertices)
    (hq : v ∉ q.vertices) (h : R.localIndex v p = R.localIndex v q) : p = q := by
  have htriple := congrArg R.isolatedTriple h
  rw [R.isolatedTriple_localIndex hp, R.isolatedTriple_localIndex hq] at htriple
  have herase : (insert v p.vertices).erase v = (insert v q.vertices).erase v :=
    congrArg (fun s => Finset.erase s v) htriple
  rw [Finset.erase_insert hp, Finset.erase_insert hq] at herase
  exact Edge11.vertices_injective herase

/-- Every block isolating `v` is named by an edge off `v`. -/
theorem exists_localIndex {v : Fin 11} {n : Fin 165} (hn : n ∈ R.isolating v) :
    ∃ p : Edge11, v ∉ p.vertices ∧ R.localIndex v p = n := by
  have hv : v ∈ R.isolatedTriple n := R.mem_isolating_iff.mp hn
  have hcard : ((R.isolatedTriple n).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem hv, R.card_isolatedTriple n]
  obtain ⟨p, hp⟩ := Edge11.exists_vertices_eq hcard
  have hvp : v ∉ p.vertices := by
    rw [hp]
    exact Finset.notMem_erase v _
  refine ⟨p, hvp, R.isolatedTriple_injective ?_⟩
  rw [R.isolatedTriple_localIndex hvp, hp, Finset.insert_erase hv]

/-- **The naming bijection.**  Counting the blocks isolating `v` that have a
property is the same as counting the edges off `v` that name them. -/
theorem card_filter_localIndex {v : Fin 11} (Q : Fin 165 → Prop) [DecidablePred Q] :
    ((Edge11.off v).filter fun p => Q (R.localIndex v p)).card =
      ((R.isolating v).filter Q).card := by
  refine Finset.card_bij (fun p _ => R.localIndex v p) ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    exact ⟨R.localIndex_mem_isolating (Edge11.mem_off.mp hp.1), hp.2⟩
  · intro p hp q hq hEq
    rw [Finset.mem_filter] at hp hq
    exact R.localIndex_injOn (Edge11.mem_off.mp hp.1) (Edge11.mem_off.mp hq.1) hEq
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨p, hvp, hpn⟩ := R.exists_localIndex hn.1
    refine ⟨p, Finset.mem_filter.mpr ⟨Edge11.mem_off.mpr hvp, ?_⟩, hpn⟩
    rw [hpn]
    exact hn.2

/-- **The local design of a residual structure.**

Every hypothetical residual structure over a cherry cover of `K₁₁` produces, at
every vertex `v`, a `SRG266.QuasiSymmetric.LocalDesign v`.  All nine axioms are
theorems of `SRG266/QuasiSymmetric/ResidualRigidity.lean`, transported along the
naming bijection `card_filter_localIndex` between the edges off `v` and the
blocks isolating `v`. -/
noncomputable def toLocalDesign (v : Fin 11) : LocalDesign v where
  block := fun p => R.res (R.localIndex v p)
  block_subset := fun p hp =>
    R.res_subset_off (R.localIndex_mem_isolating (Edge11.mem_off.mp hp))
  block_card := fun _ _ => R.res_card _
  block_isolates := by
    intro p hp x hx
    show R.deg (R.localIndex v p) x = 0
    rw [← mem_isolatedTriple, R.isolatedTriple_localIndex (Edge11.mem_off.mp hp)]
    exact Finset.mem_insert_of_mem hx
  block_cubic := by
    intro p hp x hxv hxp
    have hnot : x ∉ R.isolatedTriple (R.localIndex v p) := by
      rw [R.isolatedTriple_localIndex (Edge11.mem_off.mp hp), Finset.mem_insert]
      rintro (rfl | hmem)
      · exact hxv rfl
      · exact hxp hmem
    rw [mem_isolatedTriple] at hnot
    show R.deg (R.localIndex v p) x = 3
    rcases R.deg_cases (R.localIndex v p) x with h | h
    · exact absurd h hnot
    · exact h
  block_meet := by
    intro p hp q hq hpq
    exact R.meet_of_isolating (R.localIndex_mem_isolating (Edge11.mem_off.mp hp))
      (R.localIndex_mem_isolating (Edge11.mem_off.mp hq))
      fun hEq => hpq (R.localIndex_injOn (Edge11.mem_off.mp hp)
        (Edge11.mem_off.mp hq) hEq)
  point_rep := by
    intro e he
    have h := R.card_filter_localIndex (v := v) fun n => e ∈ R.res n
    rw [R.card_isolating_through (Edge11.mem_off.mp he)] at h
    exact h
  point_pair := by
    intro e he f hf hef
    have h := R.card_filter_localIndex (v := v) fun n => e ∈ R.res n ∧ f ∈ R.res n
    rw [R.localDesign_pairMult (Edge11.mem_off.mp he) (Edge11.mem_off.mp hf) hef] at h
    exact h
  point_star := by
    intro e he u huv hue
    have h := R.card_filter_localIndex (v := v)
      fun n => u ∈ R.isolatedTriple n ∧ e ∈ R.res n
    have hL : ((Edge11.off v).filter fun p =>
          u ∈ p.vertices ∧ e ∈ R.res (R.localIndex v p)) =
        ((Edge11.off v).filter fun p =>
          u ∈ R.isolatedTriple (R.localIndex v p) ∧ e ∈ R.res (R.localIndex v p)) := by
      refine Finset.filter_congr fun p hp => ?_
      rw [R.isolatedTriple_localIndex (Edge11.mem_off.mp hp), Finset.mem_insert]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨Or.inr h1, h2⟩
      · rintro ⟨h1 | h1, h2⟩
        · exact absurd h1 huv
        · exact ⟨h1, h2⟩
    have hR : ((R.isolating v).filter fun n => u ∈ R.isolatedTriple n ∧ e ∈ R.res n) =
        (((R.isolating u) ∩ (R.isolating v)).filter fun n => e ∈ R.res n) := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_inter, mem_isolating, mem_isolatedTriple]
      tauto
    rw [hL, h, hR]
    exact R.localCount_two huv (Edge11.mem_off₂.mpr ⟨hue, Edge11.mem_off.mp he⟩)

@[simp] theorem block_toLocalDesign (v : Fin 11) (p : Edge11) :
    (R.toLocalDesign v).block p = R.res (R.localIndex v p) := rfl

end Residual165

/-! ### The reduction -/

universe u

/-- **The cover-free boundary.**  If the local design at a single vertex of
`K₁₁` does not exist, then no cherry cover carries a residual structure.

The result reduces the residual cherry-cover obstruction to one explicit finite
object with `45` unknowns. -/
theorem noResidualCherryCover_of_isEmpty_localDesign {v : Fin 11}
    (h : IsEmpty (LocalDesign v)) : NoResidualCherryCover :=
  fun _ => ⟨fun R => h.elim (R.toLocalDesign v)⟩

/-- **The local design input.**  The cover-free finite statement that would
close `SRG266.NoQuasiSymmetricDesign56`. -/
abbrev NoLocalDesign : Prop := IsEmpty (LocalDesign 0)

/-- `NoLocalDesign` implies the residual cherry-cover obstruction. -/
theorem noResidualCherryCover_of_noLocalDesign (h : NoLocalDesign) :
    NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_localDesign h

/-- `NoLocalDesign` implies the headline non-existence theorem. -/
theorem noQuasiSymmetricDesign56_of_noLocalDesign (h : NoLocalDesign) :
    NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noLocalDesign h)

end SRG266.QuasiSymmetric
