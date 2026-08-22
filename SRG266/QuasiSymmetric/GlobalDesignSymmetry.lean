/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.GlobalDesignLaws
import SRG266.QuasiSymmetric.LocalDesignSymmetry

/-!
# The symmetry group of the global residual design

`SRG266/QuasiSymmetric/GlobalDesign.lean` reduces the design-side boundary input
`SRG266.QuasiSymmetric.NoResidualCherryCover` to the non-existence of one
cover-free finite object: the family of `165` twelve-edge blocks `B T` of `K₁₁`,
indexed by the triples `T` of vertices they isolate.
`SRG266/QuasiSymmetric/GlobalDesignLaws.lean` pins down the disjointness graph of
that object.  This file equips it with its symmetry group.

Relabelling the eleven vertices by a permutation `σ` carries a global design to a
global design (`SRG266.QuasiSymmetric.GlobalDesign.relabel`): the block named by
`T` becomes the `σ`-image of the block named by `σ⁻¹ T`.  So `S₁₁` acts on
`GlobalDesign`, and — unlike the local object, which carries a distinguished
centre — it acts on the whole object, with no parameter to transport.  The
disjointness graph is equivariant for that action
(`SRG266.QuasiSymmetric.GlobalDesign.disjointFrom_relabel`).

Two theorems package the two levels of canonical symmetry breaking.

* **Level one** (`SRG266.QuasiSymmetric.GlobalDesign.isEmpty_of_normalized`).
  Fix a triple `T₀`.  If a property `S₀` of edge sets is *reached* from every
  global design by some permutation stabilising `T₀` — that is,
  `S₀ ((B T₀).image σ)` holds for some such `σ` — then it is enough to refute the
  global designs whose block at `T₀` satisfies `S₀`.  The stabiliser of `T₀`
  contains a copy of `S₈` permuting the eight vertices off `T₀`
  (`SRG266.QuasiSymmetric.extendOff`), and `B T₀` is a cubic graph on exactly
  those eight vertices, so `S₀` may be taken to be a set of representatives for
  the isomorphism types of cubic graphs on eight vertices, of which there are
  six.

* **Level two** (`SRG266.QuasiSymmetric.GlobalDesign.isEmpty_of_normalized_two`).
  Once the first block is normalised, the permutations still available are those
  stabilising `T₀` *and fixing the normalised block* — the automorphism group of
  that cubic graph, together with the six permutations of `T₀` itself.  Fix a
  second triple `T₁` stabilised by the ones used; the theorem then lets a search
  normalise `B T₁` in the orbits of that residual group, with the second normal
  form allowed to depend on the first
  (`S₁ : Finset Edge11 → Finset Edge11 → Prop`).

* **Level two, second triple per case**
  (`SRG266.QuasiSymmetric.GlobalDesign.isEmpty_of_normalized_two_choice`).  The
  This variant takes
  `T₁ : Finset Edge11 → Finset (Fin 11)`, a triple chosen from the normalised
  first block, and level two above is its constant case.  The reduction survives
  because the second relabelling fixes the first block, so it does not move the
  triple it is normalising.

Both levels quantify over permutations that *stabilise the naming triples*, so
the two supporting facts a certificate needs are proved here:
`SRG266.QuasiSymmetric.extendOff`, which extends a permutation of the eight
vertices off a triple to one of all eleven fixing that triple pointwise, and
`SRG266.QuasiSymmetric.image_eq_self_of_mapsTo`, which recognises a stabilising
permutation from its values.  For completeness the action is also shown to be
transitive on the `165` triples
(`SRG266.QuasiSymmetric.exists_perm_image_eq`), so no generality is lost in
naming one of them `T₀`.

Nothing here asserts that a `GlobalDesign` fails to exist, and nothing here
generates or consumes a certificate.  There is no `decide`, no design datum and
no case analysis in the file.
-/

namespace SRG266.QuasiSymmetric

/-! ### Relabelling the triples of vertices -/

/-- Relabelling a set of vertices and relabelling it back. -/
@[simp] theorem image_perm_image_symm (σ : Equiv.Perm (Fin 11)) (T : Finset (Fin 11)) :
    (T.image σ).image σ.symm = T := by
  simp [Finset.image_image]

/-- Relabelling a set of vertices backwards and then forwards. -/
@[simp] theorem image_symm_image_perm (σ : Equiv.Perm (Fin 11)) (T : Finset (Fin 11)) :
    (T.image σ.symm).image σ = T := by
  simp [Finset.image_image]

/-- A vertex lies in a set exactly when its image lies in the relabelled set. -/
theorem mem_image_perm {σ : Equiv.Perm (Fin 11)} {x : Fin 11} {T : Finset (Fin 11)} :
    σ x ∈ T.image σ ↔ x ∈ T := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp h
    rwa [σ.injective hxy] at hy
  · exact fun h => Finset.mem_image_of_mem _ h

/-- Relabelling carries triples to triples. -/
theorem mem_triples_image {σ : Equiv.Perm (Fin 11)} {T : Finset (Fin 11)} (hT : T ∈ triples) :
    T.image σ ∈ triples := by
  rw [mem_triples] at hT ⊢
  rw [Finset.card_image_of_injective _ σ.injective]
  exact hT

/-- Relabelling permutes the `165` triples. -/
theorem image_triples (σ : Equiv.Perm (Fin 11)) :
    triples.image (fun T => T.image σ) = triples := by
  ext T
  constructor
  · intro hT
    obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hT
    exact mem_triples_image hU
  · intro hT
    exact Finset.mem_image.mpr
      ⟨T.image σ.symm, mem_triples_image hT, image_symm_image_perm σ T⟩

/-- Counting triples by a relabelled property is counting them by the property:
the analogue for the `165` triples of
`SRG266.QuasiSymmetric.Edge11.card_filter_off_map`. -/
theorem card_filter_triples_map (σ : Equiv.Perm (Fin 11))
    (P : Finset (Fin 11) → Prop) [DecidablePred P] :
    (triples.filter fun T => P (T.image σ.symm)).card = (triples.filter P).card := by
  classical
  conv_lhs => rw [← image_triples σ]
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (Finset.image_injective σ.injective)]
  exact congrArg Finset.card (Finset.filter_congr fun a _ => by simp)

/-! ### Permutations stabilising a set of vertices -/

/-- A permutation mapping a set into itself stabilises it. -/
theorem image_eq_self_of_mapsTo {σ : Equiv.Perm (Fin 11)} {T : Finset (Fin 11)}
    (h : ∀ x ∈ T, σ x ∈ T) : T.image σ = T := by
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact h x hx
  · exact le_of_eq (Finset.card_image_of_injective _ σ.injective).symm

/-- A permutation stabilises a set exactly when its inverse does. -/
theorem image_symm_eq_self {σ : Equiv.Perm (Fin 11)} {T : Finset (Fin 11)}
    (h : T.image σ = T) : T.image σ.symm = T := by
  have h' := congrArg (fun s : Finset (Fin 11) => s.image σ.symm) h
  simp only [image_perm_image_symm] at h'
  exact h'.symm

/-- **Extending a permutation of the eight vertices off a triple.**  A
permutation of the vertices outside a set extends to a permutation of all eleven
that fixes the set pointwise.

This is the concrete source of the symmetry a search uses: the block named by `T`
is a cubic graph on the eight vertices off `T`, and every isomorphism of such
graphs is realised by a permutation of `Fin 11` stabilising `T`. -/
def extendOff (T : Finset (Fin 11)) (π : Equiv.Perm {x : Fin 11 // x ∉ T}) :
    Equiv.Perm (Fin 11) :=
  Equiv.Perm.subtypeCongr (Equiv.refl {x : Fin 11 // x ∈ T}) π

/-- The extension fixes the set pointwise. -/
@[simp] theorem extendOff_apply_of_mem {T : Finset (Fin 11)}
    (π : Equiv.Perm {x : Fin 11 // x ∉ T}) {x : Fin 11} (hx : x ∈ T) :
    extendOff T π x = x :=
  Equiv.Perm.subtypeCongr.left_apply _ _ hx

/-- The extension acts by the given permutation outside the set. -/
theorem extendOff_apply_of_notMem {T : Finset (Fin 11)}
    (π : Equiv.Perm {x : Fin 11 // x ∉ T}) {x : Fin 11} (hx : x ∉ T) :
    extendOff T π x = π ⟨x, hx⟩ :=
  Equiv.Perm.subtypeCongr.right_apply _ _ hx

/-- The extension stabilises the set. -/
@[simp] theorem image_extendOff (T : Finset (Fin 11))
    (π : Equiv.Perm {x : Fin 11 // x ∉ T}) : T.image (extendOff T π) = T :=
  image_eq_self_of_mapsTo fun x hx => by
    rw [extendOff_apply_of_mem π hx]
    exact hx

/-- **Transitivity on the triples.**  Any set of vertices is carried to any other
of the same size by a relabelling; in particular `S₁₁` is transitive on the `165`
triples, so nothing is lost by naming one of them and normalising its block. -/
theorem exists_perm_image_eq {T U : Finset (Fin 11)} (h : T.card = U.card) :
    ∃ σ : Equiv.Perm (Fin 11), T.image σ = U := by
  classical
  have hcard : Fintype.card {x : Fin 11 // x ∈ T} = Fintype.card {x : Fin 11 // x ∈ U} := by
    rw [Fintype.card_coe, Fintype.card_coe]
    exact h
  refine ⟨(Fintype.equivOfCardEq hcard).extendSubtype, ?_⟩
  refine Finset.eq_of_subset_of_card_le ?_ ?_
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact (Fintype.equivOfCardEq hcard).extendSubtype_mem x hx
  · exact le_of_eq
      (h.symm.trans (Finset.card_image_of_injective _ (Equiv.injective _)).symm)

/-! ### The action of `S₁₁` on global designs -/

namespace GlobalDesign

variable (G : GlobalDesign)

/-- The blocks of a relabelled global design: the block named by `T` is the
relabelling of the block named by the preimage of `T`. -/
def relabelBlock (σ : Equiv.Perm (Fin 11)) (T : Finset (Fin 11)) : Finset Edge11 :=
  (G.block (T.image σ.symm)).image (Edge11.map σ)

variable {G}

@[simp] theorem mem_relabelBlock {σ : Equiv.Perm (Fin 11)} {T : Finset (Fin 11)}
    {e : Edge11} :
    e ∈ G.relabelBlock σ T ↔ Edge11.map σ.symm e ∈ G.block (T.image σ.symm) := by
  rw [relabelBlock]
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    simpa using hf
  · intro he
    exact Finset.mem_image.mpr ⟨_, he, Edge11.map_map_symm σ e⟩

variable (G)

/-- **The symmetry group of the global design.**  Relabelling the eleven vertices
of `K₁₁` by `σ` carries a global design to a global design, the block named by a
triple `T` becoming the `σ`-image of the block named by `σ⁻¹ T`.

All seven axioms transport, because `SRG266.QuasiSymmetric.Edge11.map σ` is a
bijection of the `55` edges preserving `SRG266.QuasiSymmetric.Edge11.vmeet`,
`SRG266.QuasiSymmetric.arcDegree_image` transports degrees, and
`SRG266.QuasiSymmetric.card_filter_triples_map` transports counts over the `165`
triples. -/
def relabel (σ : Equiv.Perm (Fin 11)) : GlobalDesign where
  block := G.relabelBlock σ
  block_card := by
    intro T hT
    rw [relabelBlock, Finset.card_image_of_injective _ (Edge11.map_injective σ)]
    exact G.block_card _ (mem_triples_image hT)
  block_isolates := by
    intro T hT x hx
    rw [relabelBlock, arcDegree_image]
    exact G.block_isolates _ (mem_triples_image hT) _ (Finset.mem_image_of_mem _ hx)
  block_cubic := by
    intro T hT x hx
    rw [relabelBlock, arcDegree_image]
    refine G.block_cubic _ (mem_triples_image hT) _ ?_
    intro hcon
    exact hx (mem_image_perm.mp hcon)
  block_meet := by
    intro T hT U hU hTU
    rw [relabelBlock, relabelBlock, ← Finset.image_inter _ _ (Edge11.map_injective σ),
      Finset.card_image_of_injective _ (Edge11.map_injective σ)]
    refine G.block_meet _ (mem_triples_image hT) _ (mem_triples_image hU) ?_
    intro hcon
    exact hTU (by simpa using congrArg (fun s : Finset (Fin 11) => s.image σ) hcon)
  meet_of_shared := by
    intro T hT U hU hTU hshare
    rw [relabelBlock, relabelBlock, ← Finset.image_inter _ _ (Edge11.map_injective σ),
      Finset.card_image_of_injective _ (Edge11.map_injective σ)]
    refine G.meet_of_shared _ (mem_triples_image hT) _ (mem_triples_image hU) ?_ ?_
    · intro hcon
      exact hTU (by simpa using congrArg (fun s : Finset (Fin 11) => s.image σ) hcon)
    · obtain ⟨v, hv⟩ := hshare
      rw [Finset.mem_inter] at hv
      exact ⟨σ.symm v, Finset.mem_inter.mpr
        ⟨Finset.mem_image_of_mem _ hv.1, Finset.mem_image_of_mem _ hv.2⟩⟩
  edge_rep := by
    classical
    intro e
    have hfil : (triples.filter fun T => e ∈ G.relabelBlock σ T) =
        triples.filter fun T => Edge11.map σ.symm e ∈ G.block (T.image σ.symm) :=
      Finset.filter_congr fun _ _ => mem_relabelBlock
    rw [hfil, card_filter_triples_map σ fun U => Edge11.map σ.symm e ∈ G.block U]
    exact G.edge_rep _
  pair_mult := by
    classical
    intro e f hef
    have hne : Edge11.map σ.symm e ≠ Edge11.map σ.symm f := fun hcon =>
      hef (Edge11.map_injective σ.symm hcon)
    have hfil : (triples.filter fun T =>
          e ∈ G.relabelBlock σ T ∧ f ∈ G.relabelBlock σ T) =
        triples.filter fun T => Edge11.map σ.symm e ∈ G.block (T.image σ.symm) ∧
          Edge11.map σ.symm f ∈ G.block (T.image σ.symm) :=
      Finset.filter_congr fun _ _ => and_congr mem_relabelBlock mem_relabelBlock
    rw [hfil, card_filter_triples_map σ
      fun U => Edge11.map σ.symm e ∈ G.block U ∧ Edge11.map σ.symm f ∈ G.block U,
      G.pair_mult _ _ hne, Edge11.vmeet_map]

@[simp] theorem block_relabel (σ : Equiv.Perm (Fin 11)) (T : Finset (Fin 11)) :
    (G.relabel σ).block T = (G.block (T.image σ.symm)).image (Edge11.map σ) := rfl

/-- At a fixed triple, relabelling the design relabels its block. -/
theorem block_relabel_of_image_eq {σ : Equiv.Perm (Fin 11)} {T : Finset (Fin 11)}
    (h : T.image σ = T) :
    (G.relabel σ).block T = (G.block T).image (Edge11.map σ) := by
  rw [block_relabel, image_symm_eq_self h]

/-- Two blocks of a relabelled design meet exactly as their preimages do. -/
theorem card_block_relabel_inter (σ : Equiv.Perm (Fin 11)) (T U : Finset (Fin 11)) :
    ((G.relabel σ).block T ∩ (G.relabel σ).block U).card =
      (G.block (T.image σ.symm) ∩ G.block (U.image σ.symm)).card := by
  rw [block_relabel, block_relabel, ← Finset.image_inter _ _ (Edge11.map_injective σ),
    Finset.card_image_of_injective _ (Edge11.map_injective σ)]

/-- **The disjointness graph is equivariant.**  Relabelling the vertices carries
the `24`-regular graph `Z` of `SRG266/QuasiSymmetric/GlobalDesignLaws.lean` to
itself, so the six laws proved there are `S₁₁`-invariant statements and a search
may normalise before using them. -/
theorem disjointFrom_relabel (σ : Equiv.Perm (Fin 11)) (T : Finset (Fin 11)) :
    (G.relabel σ).disjointFrom T =
      (G.disjointFrom (T.image σ.symm)).image fun U => U.image σ := by
  ext U
  simp only [mem_disjointFrom, Finset.mem_image]
  constructor
  · rintro ⟨hU, h0⟩
    refine ⟨U.image σ.symm, ⟨mem_triples_image hU, ?_⟩, image_symm_image_perm σ U⟩
    rwa [G.card_block_relabel_inter σ T U] at h0
  · rintro ⟨V, ⟨hV, h0⟩, rfl⟩
    refine ⟨mem_triples_image hV, ?_⟩
    rw [G.card_block_relabel_inter σ T (V.image σ), image_perm_image_symm]
    exact h0

/-! ### Symmetry breaking -/

/-- **Level one: normalising the first block.**  Fix a triple `T₀`.  Suppose a
property `S` of sets of edges is *reached* by every global design: for each `G`
there is a permutation `σ` stabilising `T₀` with `S ((G.block T₀).image σ)`.
Then it is enough to refute the global designs whose block at `T₀` satisfies `S`.

The permutations stabilising `T₀` include the copy of `S₈` permuting the eight
vertices off `T₀` (`SRG266.QuasiSymmetric.extendOff`), and `G.block T₀` is a
cubic graph on exactly those eight vertices, so `S` may be taken to be a set of
representatives for the isomorphism types of cubic graphs on eight vertices, of
which there are six. -/
theorem isEmpty_of_normalized (T₀ : Finset (Fin 11)) (S : Finset Edge11 → Prop)
    (hnorm : ∀ G : GlobalDesign, ∃ σ : Equiv.Perm (Fin 11),
      T₀.image σ = T₀ ∧ S ((G.block T₀).image (Edge11.map σ)))
    (hrefute : ∀ G : GlobalDesign, ¬ S (G.block T₀)) :
    IsEmpty GlobalDesign := by
  refine ⟨fun G => ?_⟩
  obtain ⟨σ, hσ, hS⟩ := hnorm G
  refine hrefute (G.relabel σ) ?_
  rw [G.block_relabel_of_image_eq hσ]
  exact hS

/-- **Level two: normalising a second block inside the residual group.**  Fix two
triples `T₀` and `T₁`.  Suppose

* every global design can be relabelled, by a permutation stabilising `T₀`, so
  that its block at `T₀` satisfies `S₀`; and
* every global design whose block at `T₀` satisfies `S₀` can be relabelled again,
  by a permutation stabilising both `T₀` and `T₁` *and fixing the block at `T₀`*,
  so that its block at `T₁` satisfies `S₁` — where the second normal form may
  depend on the first.

Then it is enough to refute the global designs normalised at both triples.

The second hypothesis is the residual-group statement: after the first block is
normalised the permutations still available are the automorphisms of that cubic
graph together with the permutations of `T₀`, and `S₁` is a set of orbit
representatives for their action on the admissible blocks at `T₁`.  Because `S₁`
takes the first block as an argument, the *representatives* may be chosen per
first-level case.  The second triple `T₁` may not: it is a parameter of this
statement, fixed once for all six cases.  Choosing it per case needs
`SRG266.QuasiSymmetric.GlobalDesign.isEmpty_of_normalized_two_choice`, of which
this theorem is the constant case. -/
theorem isEmpty_of_normalized_two (T₀ T₁ : Finset (Fin 11))
    (S₀ : Finset Edge11 → Prop) (S₁ : Finset Edge11 → Finset Edge11 → Prop)
    (hnorm₀ : ∀ G : GlobalDesign, ∃ σ : Equiv.Perm (Fin 11),
      T₀.image σ = T₀ ∧ S₀ ((G.block T₀).image (Edge11.map σ)))
    (hnorm₁ : ∀ G : GlobalDesign, S₀ (G.block T₀) → ∃ τ : Equiv.Perm (Fin 11),
      T₀.image τ = T₀ ∧ T₁.image τ = T₁ ∧
        (G.block T₀).image (Edge11.map τ) = G.block T₀ ∧
        S₁ (G.block T₀) ((G.block T₁).image (Edge11.map τ)))
    (hrefute : ∀ G : GlobalDesign, S₀ (G.block T₀) → ¬ S₁ (G.block T₀) (G.block T₁)) :
    IsEmpty GlobalDesign := by
  refine ⟨fun G => ?_⟩
  obtain ⟨σ, hσ, hS₀⟩ := hnorm₀ G
  have hfirst : (G.relabel σ).block T₀ = (G.block T₀).image (Edge11.map σ) :=
    G.block_relabel_of_image_eq hσ
  have h₀ : S₀ ((G.relabel σ).block T₀) := by rw [hfirst]; exact hS₀
  obtain ⟨τ, hτ₀, hτ₁, hfix, hS₁⟩ := hnorm₁ (G.relabel σ) h₀
  have hsecond₀ : ((G.relabel σ).relabel τ).block T₀ = (G.relabel σ).block T₀ := by
    rw [(G.relabel σ).block_relabel_of_image_eq hτ₀, hfix]
  have hsecond₁ : ((G.relabel σ).relabel τ).block T₁ =
      ((G.relabel σ).block T₁).image (Edge11.map τ) :=
    (G.relabel σ).block_relabel_of_image_eq hτ₁
  refine hrefute ((G.relabel σ).relabel τ) ?_ ?_
  · rw [hsecond₀]; exact h₀
  · rw [hsecond₀, hsecond₁]; exact hS₁

/-- **Level two with the second triple chosen per first-level case.**  Fix a
triple `T₀`.  Suppose

* every global design can be relabelled, by a permutation stabilising `T₀`, so
  that its block at `T₀` satisfies `S₀`; and
* every global design whose block at `T₀` satisfies `S₀` can be relabelled again,
  by a permutation stabilising `T₀` and the triple `T₁ (B T₀)` *and fixing the
  block at `T₀`*, so that its block at `T₁ (B T₀)` satisfies `S₁ (B T₀)`.

Then it is enough to refute the global designs normalised at both triples.

`SRG266.QuasiSymmetric.GlobalDesign.isEmpty_of_normalized_two` is the special
case of a constant `T₁`.  The generality is not cosmetic: there the second triple
is a parameter of the statement, fixed once for all first-level cases, so the
per-case choice of `T₁` cannot be expressed at all.  Here `T₁` is a function of
the normalised first block, and the reduction still goes through because the
relabelling `τ` supplied by the second hypothesis fixes that block, hence leaves
the value of `T₁` — and therefore the triple being normalised — unchanged.

This permits a different second triple for each first-block isomorphism type. -/
theorem isEmpty_of_normalized_two_choice (T₀ : Finset (Fin 11))
    (S₀ : Finset Edge11 → Prop) (T₁ : Finset Edge11 → Finset (Fin 11))
    (S₁ : Finset Edge11 → Finset Edge11 → Prop)
    (hnorm₀ : ∀ G : GlobalDesign, ∃ σ : Equiv.Perm (Fin 11),
      T₀.image σ = T₀ ∧ S₀ ((G.block T₀).image (Edge11.map σ)))
    (hnorm₁ : ∀ G : GlobalDesign, S₀ (G.block T₀) → ∃ τ : Equiv.Perm (Fin 11),
      T₀.image τ = T₀ ∧ (T₁ (G.block T₀)).image τ = T₁ (G.block T₀) ∧
        (G.block T₀).image (Edge11.map τ) = G.block T₀ ∧
        S₁ (G.block T₀) ((G.block (T₁ (G.block T₀))).image (Edge11.map τ)))
    (hrefute : ∀ G : GlobalDesign, S₀ (G.block T₀) →
      ¬ S₁ (G.block T₀) (G.block (T₁ (G.block T₀)))) :
    IsEmpty GlobalDesign := by
  refine ⟨fun G => ?_⟩
  obtain ⟨σ, hσ, hS₀⟩ := hnorm₀ G
  have hfirst : (G.relabel σ).block T₀ = (G.block T₀).image (Edge11.map σ) :=
    G.block_relabel_of_image_eq hσ
  have h₀ : S₀ ((G.relabel σ).block T₀) := by rw [hfirst]; exact hS₀
  obtain ⟨τ, hτ₀, hτ₁, hfix, hS₁⟩ := hnorm₁ (G.relabel σ) h₀
  have hsecond₀ : ((G.relabel σ).relabel τ).block T₀ = (G.relabel σ).block T₀ := by
    rw [(G.relabel σ).block_relabel_of_image_eq hτ₀, hfix]
  have hsecond₁ : ((G.relabel σ).relabel τ).block (T₁ ((G.relabel σ).block T₀)) =
      ((G.relabel σ).block (T₁ ((G.relabel σ).block T₀))).image (Edge11.map τ) :=
    (G.relabel σ).block_relabel_of_image_eq hτ₁
  refine hrefute ((G.relabel σ).relabel τ) ?_ ?_
  · rw [hsecond₀]; exact h₀
  · rw [hsecond₀, hsecond₁]; exact hS₁

end GlobalDesign

end SRG266.QuasiSymmetric
