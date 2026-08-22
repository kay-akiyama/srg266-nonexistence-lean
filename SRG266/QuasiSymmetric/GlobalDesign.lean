/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.ResidualRigidity
import SRG266.QuasiSymmetric.CherryRecut

/-!
# The global residual design on the `165` triples, as a cover-free finite object

`SRG266/QuasiSymmetric/ResidualRigidity.lean` proves that a hypothetical
residual structure over a cherry cover of `K₁₁` is completely rigid: sending a
block to the three vertices it isolates is a *bijection* onto the
`165 = C(11, 3)` triples of vertices
(`SRG266.QuasiSymmetric.Residual165.isolatedTriple_bijOn`).

`SRG266/QuasiSymmetric/LocalDesign.lean` already extracts a cover-free object
from that rigidity, but only the *local* one: the `45` blocks isolating one
fixed vertex.  Doing so throws away the other `120` blocks, and with them every
constraint that relates blocks isolating disjoint triples.

This file keeps all `165`.  The structure `SRG266.QuasiSymmetric.GlobalDesign`
is a family of `165` sets of edges of `K₁₁`, indexed by the triples of vertices
they isolate, with the seven axioms a residual structure supplies for free, and
the reduction proved here is

> `IsEmpty GlobalDesign`
> ⟹ `SRG266.QuasiSymmetric.NoResidualCherryCover`
> ⟹ `SRG266.NoQuasiSymmetricDesign56`.

## The object

Writing `B T` for the block named by the triple `T`:

| field | statement |
|---|---|
| `block_card` | `#(B T) = 12` |
| `block_isolates` | `B T` has degree `0` at each vertex of `T` |
| `block_cubic` | `B T` has degree `3` at each of the eight vertices off `T` |
| `block_meet` | distinct blocks meet in `0` or `3` edges |
| `meet_of_shared` | distinct blocks whose triples share a vertex meet in `3` edges |
| `edge_rep` | every edge of `K₁₁` lies on exactly `36` blocks |
| `pair_mult` | two distinct edges lie on `7 + #(common endpoints)` blocks |

The fourth and fifth axioms are the whole difference from the local object.  A
`LocalDesign v` sees only `meet_of_shared`, and only for the `45` triples
through `v`, where it is unconditional; here the two branches are separated,
and the sharper `block_meet` applies to the `24 · 165 / 2` pairs of *disjoint*
triples that the local object cannot even name.  Each of the eleven vertices `v`
carries its own copy of the local object inside a `GlobalDesign` — the `45`
triples containing `v` — and every block lies in exactly three of those copies,
so the global object is strictly more constrained than any one of them.

## What is *not* claimed

Nothing here asserts that a `GlobalDesign` fails to exist; that is the remaining
finite problem.  The content of this file is only that its non-existence
discharges `SRG266.QuasiSymmetric.NoResidualCherryCover`, and that a residual
structure over a cherry cover produces one.

There is no `decide`, no design datum and no case analysis anywhere in the file.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

/-! ### The `165` triples of vertices -/

/-- The `165` triples of vertices of `K₁₁`, used as the index set of the global
residual design. -/
def triples : Finset (Finset (Fin 11)) := Finset.univ.filter fun s => s.card = 3

@[simp] theorem mem_triples {s : Finset (Fin 11)} : s ∈ triples ↔ s.card = 3 := by
  simp [triples]

/-- There are `165 = C(11, 3)` triples. -/
theorem card_triples : triples.card = 165 := by
  have hset : triples = Finset.powersetCard 3 (Finset.univ : Finset (Fin 11)) := by
    ext s
    simp only [mem_triples, Finset.mem_powersetCard, Finset.subset_univ, true_and]
  rw [hset, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  rfl

/-! ### The global design -/

/-- **The global residual design of `K₁₁`.**

A family of `165` sets of edges of `K₁₁`, one for each triple `T` of vertices,
such that the block named by `T` is a cubic graph on the eight vertices off `T`;
two blocks named by triples sharing a vertex meet in exactly three edges, two
blocks named by disjoint triples meet in `0` or `3`; every edge lies on `36`
blocks and every pair of distinct edges on `8` or `7` according as the edges
meet or not.

This is precisely the shape that `SRG266.QuasiSymmetric.Residual165` acquires
once `SRG266.QuasiSymmetric.Residual165.isolatedTriple_bijOn` has renamed its
blocks by the triples they isolate, with every reference to the cherry cover
removed.  The function `block` is total on `Finset (Fin 11)` for convenience; it
is constrained only on `SRG266.QuasiSymmetric.triples`. -/
structure GlobalDesign where
  /-- The block named by a triple of vertices. -/
  block : Finset (Fin 11) → Finset Edge11
  /-- Every block has `12` edges. -/
  block_card : ∀ T ∈ triples, (block T).card = 12
  /-- The block named by `T` isolates the three vertices of `T`. -/
  block_isolates : ∀ T ∈ triples, ∀ x ∈ T, arcDegree (block T) x = 0
  /-- The block named by `T` is cubic at the eight vertices off `T`. -/
  block_cubic : ∀ T ∈ triples, ∀ x : Fin 11, x ∉ T → arcDegree (block T) x = 3
  /-- Two distinct blocks meet in `0` or `3` edges. -/
  block_meet : ∀ T ∈ triples, ∀ U ∈ triples, T ≠ U →
    ((block T) ∩ (block U)).card = 0 ∨ ((block T) ∩ (block U)).card = 3
  /-- Two blocks whose triples share a vertex meet in exactly `3` edges. -/
  meet_of_shared : ∀ T ∈ triples, ∀ U ∈ triples, T ≠ U → (T ∩ U).Nonempty →
    ((block T) ∩ (block U)).card = 3
  /-- Every edge of `K₁₁` lies on exactly `36` blocks. -/
  edge_rep : ∀ e : Edge11, (triples.filter fun T => e ∈ block T).card = 36
  /-- Two distinct edges lie on `8` common blocks if they share an endpoint and
  on `7` if they do not. -/
  pair_mult : ∀ e f : Edge11, e ≠ f →
    (triples.filter fun T => e ∈ block T ∧ f ∈ block T).card = 7 + Edge11.vmeet e f

namespace GlobalDesign

variable (G : GlobalDesign)

/-- No edge of the block named by `T` meets `T`. -/
theorem notMem_vertices_of_mem_block {T : Finset (Fin 11)} (hT : T ∈ triples)
    {e : Edge11} (he : e ∈ G.block T) {x : Fin 11} (hx : x ∈ T) : x ∉ e.vertices := by
  have h0 : arcDegree (G.block T) x = 0 := G.block_isolates T hT x hx
  rw [arcDegree, Finset.card_eq_zero, Finset.filter_eq_empty_iff] at h0
  exact h0 he

/-- Every block avoids the star of each vertex of its triple: it is a graph on
the eight vertices off that triple. -/
theorem block_subset_off {T : Finset (Fin 11)} (hT : T ∈ triples) {v : Fin 11}
    (hv : v ∈ T) : G.block T ⊆ Edge11.off v := fun _ he =>
  Edge11.mem_off.mpr (G.notMem_vertices_of_mem_block hT he hv)

/-- Distinct triples name distinct blocks. -/
theorem block_injOn {T U : Finset (Fin 11)} (hT : T ∈ triples) (hU : U ∈ triples)
    (h : G.block T = G.block U) : T = U := by
  by_contra hTU
  have hmeet := G.block_meet T hT U hU hTU
  rw [h, Finset.inter_self, G.block_card U hU] at hmeet
  omega

/-- The pair multiplicity of two distinct edges is `8` or `7`. -/
theorem pair_mult_cases (G : GlobalDesign) {e f : Edge11} (hef : e ≠ f) :
    (triples.filter fun T => e ∈ G.block T ∧ f ∈ G.block T).card = 8 ∨
      (triples.filter fun T => e ∈ G.block T ∧ f ∈ G.block T).card = 7 := by
  have h := G.pair_mult e f hef
  have hle := Edge11.vmeet_le_one hef
  omega

end GlobalDesign

/-! ### A residual structure produces a global design -/

namespace Residual165

variable {C : CherryCover} (R : Residual165 C.toDerived45)

/-- The index of the unique residual block isolating a given triple of vertices.
(The value at a set that is not a triple is junk.) -/
noncomputable def globalIndex (T : Finset (Fin 11)) : Fin 165 :=
  if h : T.card = 3 then R.blockOf h else 0

/-- The block named by a triple isolates exactly that triple. -/
theorem isolatedTriple_globalIndex {T : Finset (Fin 11)} (hT : T ∈ triples) :
    R.isolatedTriple (R.globalIndex T) = T := by
  rw [globalIndex, dif_pos (mem_triples.mp hT)]
  exact R.isolatedTriple_blockOf _

/-- Distinct triples name distinct residual blocks. -/
theorem globalIndex_injOn {T U : Finset (Fin 11)} (hT : T ∈ triples) (hU : U ∈ triples)
    (h : R.globalIndex T = R.globalIndex U) : T = U := by
  have htriple := congrArg R.isolatedTriple h
  rwa [R.isolatedTriple_globalIndex hT, R.isolatedTriple_globalIndex hU] at htriple

/-- Every residual block is named by a triple. -/
theorem exists_globalIndex (n : Fin 165) : ∃ T ∈ triples, R.globalIndex T = n := by
  have hT : R.isolatedTriple n ∈ triples := mem_triples.mpr (R.card_isolatedTriple n)
  exact ⟨R.isolatedTriple n, hT,
    R.isolatedTriple_injective (R.isolatedTriple_globalIndex hT)⟩

/-- **The naming bijection.**  Counting the residual blocks with a property is
the same as counting the triples that name them. -/
theorem card_filter_globalIndex (Q : Fin 165 → Prop) [DecidablePred Q] :
    (triples.filter fun T => Q (R.globalIndex T)).card =
      (Finset.univ.filter Q).card := by
  refine Finset.card_bij (fun T _ => R.globalIndex T) ?_ ?_ ?_
  · intro T hT
    rw [Finset.mem_filter] at hT ⊢
    exact ⟨Finset.mem_univ _, hT.2⟩
  · intro T hT U hU hEq
    rw [Finset.mem_filter] at hT hU
    exact R.globalIndex_injOn hT.1 hU.1 hEq
  · intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨T, hT, hTn⟩ := R.exists_globalIndex n
    refine ⟨T, Finset.mem_filter.mpr ⟨hT, ?_⟩, hTn⟩
    rw [hTn]
    exact hn.2

/-- The residual pair multiplicity of two distinct edges is `7` plus the number
of endpoints they share: `8` on a cherry, `7` on a disjoint pair.

This is `SRG266.QuasiSymmetric.residual_pairMult` read through the cherry cover
identity `SRG266.QuasiSymmetric.CherryCover.pairCount_add_vmeet`. -/
theorem pairMult_eq_add_vmeet {e f : Edge11} (hef : e ≠ f) :
    R.pairMult e f = 7 + Edge11.vmeet e f := by
  have hadd := residual_pairMult_add R hef
  rw [C.toDerived45_pairMult] at hadd
  have hcover := C.pairCount_add_vmeet e f
  rw [if_neg hef] at hcover
  omega

/-- **The global design of a residual structure.**

Every hypothetical residual structure over a cherry cover of `K₁₁` produces a
`SRG266.QuasiSymmetric.GlobalDesign`.  All seven axioms are theorems of
`SRG266/QuasiSymmetric/ResidualRigidity.lean` and
`SRG266/QuasiSymmetric/PairMultiplicity.lean`, transported along the naming
bijection `card_filter_globalIndex` between the `165` triples and the `165`
blocks. -/
noncomputable def toGlobalDesign : GlobalDesign where
  block := fun T => R.res (R.globalIndex T)
  block_card := fun _ _ => R.res_card _
  block_isolates := by
    intro T hT x hx
    show R.deg (R.globalIndex T) x = 0
    rw [← mem_isolatedTriple, R.isolatedTriple_globalIndex hT]
    exact hx
  block_cubic := by
    intro T hT x hx
    have hnot : x ∉ R.isolatedTriple (R.globalIndex T) := by
      rw [R.isolatedTriple_globalIndex hT]
      exact hx
    rw [mem_isolatedTriple] at hnot
    show R.deg (R.globalIndex T) x = 3
    rcases R.deg_cases (R.globalIndex T) x with h | h
    · exact absurd h hnot
    · exact h
  block_meet := fun T hT U hU hTU =>
    R.res_meet _ _ fun hEq => hTU (R.globalIndex_injOn hT hU hEq)
  meet_of_shared := by
    intro T hT U hU hTU hshare
    obtain ⟨v, hv⟩ := hshare
    rw [Finset.mem_inter] at hv
    have hmT : R.globalIndex T ∈ R.isolating v := by
      rw [mem_isolating_iff, R.isolatedTriple_globalIndex hT]
      exact hv.1
    have hmU : R.globalIndex U ∈ R.isolating v := by
      rw [mem_isolating_iff, R.isolatedTriple_globalIndex hU]
      exact hv.2
    exact R.meet_of_isolating hmT hmU fun hEq => hTU (R.globalIndex_injOn hT hU hEq)
  edge_rep := by
    intro e
    rw [R.card_filter_globalIndex fun n => e ∈ R.res n]
    exact R.res_rep e
  pair_mult := by
    intro e f hef
    rw [R.card_filter_globalIndex fun n => e ∈ R.res n ∧ f ∈ R.res n]
    exact R.pairMult_eq_add_vmeet hef

@[simp] theorem block_toGlobalDesign (T : Finset (Fin 11)) :
    R.toGlobalDesign.block T = R.res (R.globalIndex T) := rfl

end Residual165

/-! ### The reduction -/

universe u

/-- If the global residual design
does not exist, then no cherry cover of `K₁₁` carries a residual structure.

Compared with `SRG266.QuasiSymmetric.noResidualCherryCover_of_isEmpty_localDesign`
this keeps the `120` blocks that the local reduction discards, hence is a weaker
hypothesis: `IsEmpty (LocalDesign v)` refutes an object that a `GlobalDesign`
contains eleven copies of. -/
theorem noResidualCherryCover_of_isEmpty_globalDesign (h : IsEmpty GlobalDesign) :
    NoResidualCherryCover :=
  fun _ => ⟨fun R => h.elim R.toGlobalDesign⟩

/-- **The global design input.**  The cover-free finite statement that would
close `SRG266.NoQuasiSymmetricDesign56`. -/
abbrev NoGlobalDesign : Prop := IsEmpty GlobalDesign

/-- `NoGlobalDesign` implies the residual cherry-cover obstruction. -/
theorem noResidualCherryCover_of_noGlobalDesign (h : NoGlobalDesign) :
    NoResidualCherryCover :=
  noResidualCherryCover_of_isEmpty_globalDesign h

/-- `NoGlobalDesign` implies the headline non-existence theorem. -/
theorem noQuasiSymmetricDesign56_of_noGlobalDesign (h : NoGlobalDesign) :
    NoQuasiSymmetricDesign56.{u} :=
  noQuasiSymmetricDesign56_of_noResidualCherryCover
    (noResidualCherryCover_of_noGlobalDesign h)

end SRG266.QuasiSymmetric
