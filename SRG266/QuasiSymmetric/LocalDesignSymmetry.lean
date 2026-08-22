/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.LocalDesign

/-!
# The symmetry group of the local design

`SRG266/QuasiSymmetric/LocalDesign.lean` reduced the design-side boundary input
`SRG266.QuasiSymmetric.NoResidualCherryCover` to the non-existence of one
cover-free finite object, the symmetric `2-(45, 12, 3)` design
`SRG266.QuasiSymmetric.LocalDesign v` on the `45` edges of `K₁₁ − v`.

This file equips that object with its symmetry group.  Relabelling the eleven
vertices carries a local design at `v` to a local design at `σ v`
(`SRG266.QuasiSymmetric.LocalDesign.relabel`), so the stabiliser of the centre —
a copy of `S₁₀` — acts on `LocalDesign v` itself.

Two things follow.

* **The centre is irrelevant.**  `LocalDesign v` is empty for one vertex exactly
  when it is empty for every vertex
  (`SRG266.QuasiSymmetric.LocalDesign.isEmpty_congr`), so the abbreviation
  `SRG266.QuasiSymmetric.NoLocalDesign`, which fixes the centre `0`, loses
  nothing.

* **Symmetry breaking.**  A search may normalise one block.  Fix an index `p₀`.
  If a property `S` of blocks meets the orbit of `L.block p₀` under the
  subgroup fixing both `v` and `p₀`, for every local design `L`, then it is
  enough to refute the local designs whose block at `p₀` satisfies `S`
  (`SRG266.QuasiSymmetric.LocalDesign.isEmpty_of_normalized`).

The subgroup fixing `v` and `p₀` contains a copy of `S₈` permuting the eight
vertices on which `block p₀` is a cubic graph.  Thus `S` may be a set of
representatives for the six isomorphism types of cubic graphs on eight vertices.

Nothing here asserts that a `LocalDesign` fails to exist.  There is no `decide`,
no design datum and no case analysis in the file.
-/

namespace SRG266.QuasiSymmetric

/-! ### Relabelling the edges off a vertex -/

namespace Edge11

/-- Relabelling by a permutation and by its inverse are mutually inverse. -/
@[simp] theorem map_symm_map (σ : Equiv.Perm (Fin 11)) (e : Edge11) :
    map σ.symm (map σ e) = e := by
  apply Subtype.ext
  simp [Sym2.map_map]

/-- Relabelling by the inverse of a permutation and by the permutation are
mutually inverse. -/
@[simp] theorem map_map_symm (σ : Equiv.Perm (Fin 11)) (e : Edge11) :
    map σ (map σ.symm e) = e := by
  apply Subtype.ext
  simp [Sym2.map_map]

/-- A vertex lies on an edge exactly when its image under `σ.symm` lies on the
edge relabelled by `σ.symm`. -/
theorem mem_vertices_map_symm {σ : Equiv.Perm (Fin 11)} {u : Fin 11} {p : Edge11} :
    σ.symm u ∈ (map σ.symm p).vertices ↔ u ∈ p.vertices := by
  rw [mem_vertices_map]
  simp

/-- Relabelling carries the edges off `v` to the edges off `σ v`. -/
theorem map_mem_off {σ : Equiv.Perm (Fin 11)} {v : Fin 11} {e : Edge11}
    (he : e ∈ off v) : map σ e ∈ off (σ v) := by
  rw [mem_off] at he ⊢
  intro hcon
  exact he (by simpa using mem_vertices_map.mp hcon)

/-- Relabelling by the inverse carries the edges off `σ v` to the edges off
`v`. -/
theorem mem_off_map_symm {σ : Equiv.Perm (Fin 11)} {v : Fin 11} {p : Edge11}
    (hp : p ∈ off (σ v)) : map σ.symm p ∈ off v := by
  rw [mem_off] at hp ⊢
  intro hcon
  have hmem := mem_vertices_map.mp hcon
  rw [Equiv.symm_symm] at hmem
  exact hp hmem

/-- The `45` edges off `σ v` are the relabellings of the `45` edges off `v`. -/
theorem image_off (σ : Equiv.Perm (Fin 11)) (v : Fin 11) :
    (off v).image (map σ) = off (σ v) := by
  ext p
  constructor
  · intro hp
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hp
    exact map_mem_off hf
  · intro hp
    exact Finset.mem_image.mpr ⟨map σ.symm p, mem_off_map_symm hp, map_map_symm σ p⟩

/-- Counting edges off `σ v` by a relabelled predicate is counting edges off `v`
by the predicate. -/
theorem card_filter_off_map (σ : Equiv.Perm (Fin 11)) (v : Fin 11)
    (P : Edge11 → Prop) [DecidablePred P] :
    ((off (σ v)).filter fun p => P (map σ.symm p)).card = ((off v).filter P).card := by
  classical
  rw [← image_off σ v, Finset.filter_image,
    Finset.card_image_of_injective _ (map_injective σ)]
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by simp)

end Edge11

/-! ### The action on local designs -/

namespace LocalDesign

variable {v : Fin 11} (L : LocalDesign v)

/-- The blocks of a relabelled local design: the block named by `p` is the
relabelling of the block named by the preimage of `p`. -/
def relabelBlock (σ : Equiv.Perm (Fin 11)) (p : Edge11) : Finset Edge11 :=
  (L.block (Edge11.map σ.symm p)).image (Edge11.map σ)

variable {L}

@[simp] theorem mem_relabelBlock {σ : Equiv.Perm (Fin 11)} {p e : Edge11} :
    e ∈ L.relabelBlock σ p ↔ Edge11.map σ.symm e ∈ L.block (Edge11.map σ.symm p) := by
  rw [relabelBlock]
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa using hf
  · intro he
    exact Finset.mem_image.mpr ⟨_, he, Edge11.map_map_symm σ e⟩

variable (L)

/-- **The symmetry group of the local design.**  Relabelling the eleven vertices
of `K₁₁` by `σ` carries a local design centred at `v` to a local design centred
at `σ v`.

All nine axioms transport, because `SRG266.QuasiSymmetric.Edge11.map σ` is a
bijection of the edges carrying `Edge11.off v` onto `Edge11.off (σ v)` and
`SRG266.QuasiSymmetric.arcDegree_image` transports degrees. -/
def relabel (σ : Equiv.Perm (Fin 11)) : LocalDesign (σ v) where
  block := L.relabelBlock σ
  block_subset := by
    intro p hp e he
    rw [mem_relabelBlock] at he
    have := L.block_subset _ (Edge11.mem_off_map_symm hp) he
    simpa using Edge11.map_mem_off (σ := σ) this
  block_card := by
    intro p hp
    rw [relabelBlock, Finset.card_image_of_injective _ (Edge11.map_injective σ)]
    exact L.block_card _ (Edge11.mem_off_map_symm hp)
  block_isolates := by
    intro p hp x hx
    rw [relabelBlock, arcDegree_image]
    exact L.block_isolates _ (Edge11.mem_off_map_symm hp) _
      (Edge11.mem_vertices_map_symm.mpr hx)
  block_cubic := by
    intro p hp x hxv hxp
    rw [relabelBlock, arcDegree_image]
    refine L.block_cubic _ (Edge11.mem_off_map_symm hp) _ ?_ ?_
    · intro hcon
      exact hxv (by rw [← hcon, Equiv.apply_symm_apply])
    · exact fun hcon => hxp (Edge11.mem_vertices_map_symm.mp hcon)
  block_meet := by
    intro p hp q hq hpq
    rw [relabelBlock, relabelBlock,
      ← Finset.image_inter _ _ (Edge11.map_injective σ),
      Finset.card_image_of_injective _ (Edge11.map_injective σ)]
    exact L.block_meet _ (Edge11.mem_off_map_symm hp) _ (Edge11.mem_off_map_symm hq)
      fun hcon => hpq (by
        have := congrArg (Edge11.map σ) hcon
        simpa using this)
  point_rep := by
    classical
    intro e he
    have hfil : ((Edge11.off (σ v)).filter fun p => e ∈ L.relabelBlock σ p)
        = (Edge11.off (σ v)).filter
            fun p => Edge11.map σ.symm e ∈ L.block (Edge11.map σ.symm p) :=
      Finset.filter_congr fun _ _ => mem_relabelBlock
    rw [hfil, Edge11.card_filter_off_map σ v fun q => Edge11.map σ.symm e ∈ L.block q]
    exact L.point_rep _ (Edge11.mem_off_map_symm he)
  point_pair := by
    classical
    intro e he f hf hef
    have hfil : ((Edge11.off (σ v)).filter
          fun p => e ∈ L.relabelBlock σ p ∧ f ∈ L.relabelBlock σ p)
        = (Edge11.off (σ v)).filter
            fun p => Edge11.map σ.symm e ∈ L.block (Edge11.map σ.symm p) ∧
              Edge11.map σ.symm f ∈ L.block (Edge11.map σ.symm p) :=
      Finset.filter_congr fun _ _ => and_congr mem_relabelBlock mem_relabelBlock
    rw [hfil, Edge11.card_filter_off_map σ v
      fun q => Edge11.map σ.symm e ∈ L.block q ∧ Edge11.map σ.symm f ∈ L.block q]
    refine L.point_pair _ (Edge11.mem_off_map_symm he) _ (Edge11.mem_off_map_symm hf) ?_
    intro hcon
    exact hef (by simpa using congrArg (Edge11.map σ) hcon)
  point_star := by
    classical
    intro e he u huv hue
    have hfil : ((Edge11.off (σ v)).filter
          fun p => u ∈ p.vertices ∧ e ∈ L.relabelBlock σ p)
        = (Edge11.off (σ v)).filter
            fun p => σ.symm u ∈ (Edge11.map σ.symm p).vertices ∧
              Edge11.map σ.symm e ∈ L.block (Edge11.map σ.symm p) :=
      Finset.filter_congr fun _ _ =>
        and_congr Edge11.mem_vertices_map_symm.symm mem_relabelBlock
    rw [hfil, Edge11.card_filter_off_map σ v
      fun q => σ.symm u ∈ q.vertices ∧ Edge11.map σ.symm e ∈ L.block q]
    refine L.point_star _ (Edge11.mem_off_map_symm he) _ ?_ ?_
    · intro hcon
      exact huv (by rw [← hcon, Equiv.apply_symm_apply])
    · exact fun hcon => hue (Edge11.mem_vertices_map_symm.mp hcon)

@[simp] theorem block_relabel (σ : Equiv.Perm (Fin 11)) (p : Edge11) :
    (L.relabel σ).block p = (L.block (Edge11.map σ.symm p)).image (Edge11.map σ) := rfl

/-- Relabelling into a named centre. -/
def relabelOf (σ : Equiv.Perm (Fin 11)) {w : Fin 11} (hw : σ v = w) : LocalDesign w :=
  hw ▸ L.relabel σ

@[simp] theorem block_relabelOf (σ : Equiv.Perm (Fin 11)) {w : Fin 11} (hw : σ v = w)
    (p : Edge11) :
    (L.relabelOf σ hw).block p = (L.block (Edge11.map σ.symm p)).image (Edge11.map σ) := by
  subst hw; rfl

end LocalDesign

/-! ### The centre is irrelevant -/

/-- **The local design does not depend on its centre.**  If the local design at
one vertex of `K₁₁` is empty, then it is empty at every vertex. -/
theorem LocalDesign.isEmpty_congr {v w : Fin 11} (h : IsEmpty (LocalDesign v)) :
    IsEmpty (LocalDesign w) :=
  ⟨fun L => h.elim (L.relabelOf (Equiv.swap w v) (Equiv.swap_apply_left w v))⟩

/-- `SRG266.QuasiSymmetric.NoLocalDesign` fixes the centre `0` without loss:
it is equivalent to the statement at every vertex. -/
theorem noLocalDesign_iff_forall : NoLocalDesign ↔ ∀ v : Fin 11, IsEmpty (LocalDesign v) :=
  ⟨fun h _ => LocalDesign.isEmpty_congr h, fun h => h 0⟩

/-- The local design at any single vertex discharges the design-side input. -/
theorem noLocalDesign_of_isEmpty {v : Fin 11} (h : IsEmpty (LocalDesign v)) :
    NoLocalDesign :=
  LocalDesign.isEmpty_congr h

/-! ### Symmetry breaking -/

namespace LocalDesign

/-- **Symmetry breaking for a search.**  Fix an index `p₀`.  Suppose a property
`S` of sets of edges is *reached* by every local design: for each `L` there is a
permutation `σ` fixing the centre `v` and the index `p₀` with
`S ((L.block p₀).image (Edge11.map σ))`.  Then it is enough to refute the local
designs whose block at `p₀` satisfies `S`.

The permutations fixing `v` and `p₀` are exactly those permuting the eight
vertices on which `block p₀` is a cubic graph, together with the transposition of
the two endpoints of `p₀`; so `S` may be taken to be a set of representatives
for the isomorphism types of cubic graphs on eight vertices, of which there are
six. -/
theorem isEmpty_of_normalized {v : Fin 11} (p₀ : Edge11) (S : Finset Edge11 → Prop)
    (hnorm : ∀ L : LocalDesign v, ∃ σ : Equiv.Perm (Fin 11),
      σ v = v ∧ Edge11.map σ p₀ = p₀ ∧ S ((L.block p₀).image (Edge11.map σ)))
    (hrefute : ∀ L : LocalDesign v, ¬ S (L.block p₀)) :
    IsEmpty (LocalDesign v) := by
  refine ⟨fun L => ?_⟩
  obtain ⟨σ, hσ, hp, hS⟩ := hnorm L
  refine hrefute (L.relabelOf σ hσ) ?_
  have hsymm : Edge11.map σ.symm p₀ = p₀ := by
    conv_lhs => rw [← hp]
    exact Edge11.map_symm_map σ p₀
  rw [block_relabelOf, hsymm]
  exact hS

/-! ### The tightest pairwise constraint -/

/-- **Nine of twenty-one.**  A block has `12` points, of which three meet any
vertex other than the centre and the two endpoints of its index; so `9` of them
avoid that vertex.

This is the arithmetic behind the tightest constraint a refutation of the local
design has: if the indices `p ≠ q` share an endpoint, say `q = {x, y}` with
`x ∈ p`, then `block p` and `block q` both live on the `21` edges spanned by the
seven vertices other than the centre and `p ∪ q`, each with exactly `9` points
there, and `block_meet` forces them to share exactly `3`.  Two indices with
*disjoint* endpoints are a weaker condition, not a stronger one: there the two
blocks have `6` or `7` points on the `15` edges they can share. -/
theorem card_block_avoiding {v : Fin 11} (L : LocalDesign v) {p : Edge11}
    (hp : p ∈ Edge11.off v) {x : Fin 11} (hxv : x ≠ v) (hxp : x ∉ p.vertices) :
    ((L.block p).filter fun e => x ∉ e.vertices).card = 9 := by
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := L.block p) (p := fun e : Edge11 => x ∈ e.vertices)
  have hdeg := L.block_cubic p hp x hxv hxp
  rw [arcDegree] at hdeg
  rw [hdeg, L.block_card p hp] at hsplit
  omega

end LocalDesign

end SRG266.QuasiSymmetric
