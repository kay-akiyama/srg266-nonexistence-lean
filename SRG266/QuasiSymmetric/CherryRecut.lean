/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.TriangularIso
import SRG266.QuasiSymmetric.Transport

/-!
# The `K₁₁` recoordinatisation of an arbitrary derived design

`SRG266.QuasiSymmetric.Derived45.blockGraph_iso_T11` identifies the block
graph of a `SRG266.QuasiSymmetric.Derived45` with the triangular graph `T(11)`.
An arbitrary `Derived45` is transported along that labelling to a
`SRG266.QuasiSymmetric.CherryCover` of `K₁₁`, and the design input of the
development is stated in terms of cherry covers.

Together with `SRG266.QuasiSymmetric.CherryCover.toDerived45`, this shows that
the `K₁₁` presentation is equivalent to `Derived45`.

## The construction

Fix `φ : P ≃ Edge11` from `Derived45.exists_equiv_edge11`, which carries the
pair-multiplicity identity

`t p q + vmeet (φ p) (φ q) = 2 + 9 · [p = q]`.

The members of the cover are the blocks read through `φ`
(`Derived45.coverMember`).  Two of the three cherry-cover axioms are the two
off-diagonal cases of that identity, read at `p = φ⁻¹ e`, `q = φ⁻¹ f`:

* `cherry_exact` is the case `vmeet = 1`, giving `t = 1`;
* `disjoint_twice` is the case `vmeet = 0`, giving `t = 2`.

The third, `two_regular`, is a zero-variance count over the `11` vertices
(`Derived45.two_regular_coverMember`).  Writing `d v` for the number of edges of
a fixed member through the vertex `v`,

* `∑ d v = ∑_{e ∈ member} |e.vertices| = 11 · 2 = 22` (`Edge11.sum_star_card`);
* `∑ (d v)² = ∑_{e, f ∈ member} vmeet e f` (`Edge11.sum_vmeet`), and this double
  sum is `44` (`Derived45.sum_vmeet_coverMember`), because the identity above
  turns it into `2 · 11² + 9 · 11 − ∑_j |Bᵢ ∩ Bⱼ|²` and the last sum is
  `11² + 44 · 2² = 297` by `Derived45.pair_meet`;

and `4x ≤ x² + 4` with `∑ 4 d v = 88 = ∑ ((d v)² + 4)` forces `d v = 2`
pointwise.

## The design boundary

`SRG266.QuasiSymmetric.NoResidualCherryCover` — *no cherry cover of `K₁₁` carries
a residual structure* — is a finite statement about subsets of the `55` edges
of `K₁₁`, with no classification list or isomorphism relation.

## Main results

* `SRG266.QuasiSymmetric.Derived45.toCherryCover` — the recoordinatisation;
* `SRG266.QuasiSymmetric.Derived45.isoToCherryCover` — it is an isomorphism of
  derived designs;
* `SRG266.QuasiSymmetric.NoResidualCherryCover` — the finite design input;
* `SRG266.QuasiSymmetric.noQuasiSymmetricDesign56_of_noResidualCherryCover` —
  this input suffices for the design theorem.

Nothing here uses `decide`, a certificate, or an external datum, and the module
is inside the default `lake build`.
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

namespace Derived45

variable {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P)

/-! ### The chosen `T(11)` labelling -/

/-- A choice of the `T(11)` labelling supplied by
`Derived45.exists_equiv_edge11`. -/
noncomputable def edgeEquiv : P ≃ Edge11 := E.exists_equiv_edge11.choose

/-- Two points are adjacent in the block graph exactly when their edges meet. -/
theorem adj_iff_vmeet_edgeEquiv (p q : P) :
    E.blockGraph.Adj p q ↔ Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q) = 1 :=
  E.exists_equiv_edge11.choose_spec.1 p q

/-- **The identity that drives the whole file.**  Two points lie on `9` common
blocks when equal, on `1` when their edges meet and on `2` when they do not. -/
theorem pairMult_add_vmeet_edgeEquiv (p q : P) :
    E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q)
      = 2 + if p = q then 9 else 0 :=
  E.exists_equiv_edge11.choose_spec.2 p q

/-! ### The members of the cover -/

/-- **The blocks of a `Derived45`, in `K₁₁` coordinates.** -/
noncomputable def coverMember (i : Fin 45) : Finset Edge11 :=
  (E.block i).image E.edgeEquiv

theorem mem_coverMember {i : Fin 45} {e : Edge11} :
    e ∈ E.coverMember i ↔ E.edgeEquiv.symm e ∈ E.block i := by
  rw [coverMember]
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simpa using hp
  · intro h
    exact Finset.mem_image.mpr ⟨E.edgeEquiv.symm e, h, by simp⟩

/-- A member of the cover has `11` edges. -/
theorem card_coverMember (i : Fin 45) : (E.coverMember i).card = 11 := by
  rw [coverMember, Finset.card_image_of_injective _ E.edgeEquiv.injective, E.block_card i]

/-- Pair counts are read through the labelling. -/
theorem pairCount_coverMember (e f : Edge11) :
    pairCount E.coverMember e f = E.pairMult (E.edgeEquiv.symm e) (E.edgeEquiv.symm f) := by
  have hset : (Finset.univ.filter fun i => e ∈ E.coverMember i ∧ f ∈ E.coverMember i)
      = Finset.univ.filter fun i =>
          E.edgeEquiv.symm e ∈ E.block i ∧ E.edgeEquiv.symm f ∈ E.block i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, E.mem_coverMember]
  exact congrArg Finset.card hset

/-- Summing a function over a member of the cover is summing it over the block,
read through the labelling. -/
theorem sum_coverMember {M : Type*} [AddCommMonoid M] (i : Fin 45) (F : Edge11 → M) :
    (∑ e ∈ E.coverMember i, F e) = ∑ p ∈ E.block i, F (E.edgeEquiv p) := by
  rw [coverMember, Finset.sum_image]
  exact fun x _ y _ h => E.edgeEquiv.injective h

/-! ### The variance count -/

/-- The sum of the squared traces of the family of blocks on one block:
`11² + 44 · 2² = 297`. -/
theorem sum_inter_block_sq (i : Fin 45) :
    (∑ j, ((E.block i) ∩ (E.block j)).card ^ 2) = 297 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hoff : ∀ j ∈ (Finset.univ : Finset (Fin 45)).erase i,
      ((E.block i) ∩ (E.block j)).card ^ 2 = 4 := by
    intro j hj
    rw [E.pair_meet i j (Ne.symm (Finset.mem_erase.mp hj).1)]
    norm_num
  rw [Finset.sum_congr rfl hoff, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Finset.inter_self, E.block_card i]
  norm_num [nsmul_eq_mul]

/-- The double sum of the pair multiplicity over one block: `297`. -/
theorem sum_pairMult_block (i : Fin 45) :
    (∑ p ∈ E.block i, ∑ q ∈ E.block i, E.pairMult p q) = 297 := by
  have h : (∑ p ∈ E.block i, ∑ q ∈ E.block i, E.pairMult p q)
      = ∑ j, ((E.block i) ∩ (E.block j)).card ^ 2 :=
    (sum_inter_card_sq E.block (E.block i)).symm
  rw [h, E.sum_inter_block_sq i]

/-- **The `44` of §5.2.**  Over a member of the cover, the edges meet each other
in `44` vertex incidences: the double sum of `pairMult + vmeet` is
`2 · 11² + 9 · 11 = 341`, and its `pairMult` half is `297`. -/
theorem sum_vmeet_coverMember (i : Fin 45) :
    (∑ e ∈ E.coverMember i, ∑ f ∈ E.coverMember i, Edge11.vmeet e f) = 44 := by
  have hdouble : (∑ e ∈ E.coverMember i, ∑ f ∈ E.coverMember i, Edge11.vmeet e f)
      = ∑ p ∈ E.block i, ∑ q ∈ E.block i,
          Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q) := by
    rw [E.sum_coverMember i fun e => ∑ f ∈ E.coverMember i, Edge11.vmeet e f]
    exact Finset.sum_congr rfl fun p _ => E.sum_coverMember i _
  have htot : (∑ p ∈ E.block i, ∑ q ∈ E.block i,
      (E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q))) = 341 := by
    have hcell : ∀ p ∈ E.block i, (∑ q ∈ E.block i,
        (E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q))) = 31 := by
      intro p hp
      rw [Finset.sum_congr rfl fun q _ => E.pairMult_add_vmeet_edgeEquiv p q,
        Finset.sum_add_distrib, Finset.sum_const, E.block_card i,
        Finset.sum_ite_eq (E.block i) p (fun _ => 9), if_pos hp]
      norm_num [nsmul_eq_mul]
    rw [Finset.sum_congr rfl hcell, Finset.sum_const, E.block_card i]
    norm_num [nsmul_eq_mul]
  have hsplit : (∑ p ∈ E.block i, ∑ q ∈ E.block i,
      (E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q)))
      = (∑ p ∈ E.block i, ∑ q ∈ E.block i, E.pairMult p q)
        + ∑ p ∈ E.block i, ∑ q ∈ E.block i,
            Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib
  rw [hsplit, E.sum_pairMult_block i] at htot
  rw [hdouble]
  omega

/-! ### The three cherry-cover axioms -/

/-- **Two-regularity.**  Each of the `11` vertices of `K₁₁` lies on exactly two
edges of each member of the cover.

`∑_v d v = 22` and `∑_v (d v)² = 44` over `11` vertices is zero variance about
the mean `2`. -/
theorem two_regular_coverMember (i : Fin 45) (v : Fin 11) :
    ((E.coverMember i).filter fun e => v ∈ e.vertices).card = 2 := by
  have hsum : (∑ w : Fin 11,
      ((E.coverMember i).filter fun e => w ∈ e.vertices).card) = 22 := by
    have h := Edge11.sum_star_card (E.coverMember i)
    rw [Finset.sum_congr rfl fun e _ => Edge11.card_vertices e, Finset.sum_const,
      E.card_coverMember i] at h
    simpa using h
  have hsq : (∑ w : Fin 11,
      ((E.coverMember i).filter fun e => w ∈ e.vertices).card ^ 2) = 44 := by
    rw [← Edge11.sum_vmeet (E.coverMember i), E.sum_vmeet_coverMember i]
  have hle : ∀ w ∈ (Finset.univ : Finset (Fin 11)),
      4 * ((E.coverMember i).filter fun e => w ∈ e.vertices).card
        ≤ ((E.coverMember i).filter fun e => w ∈ e.vertices).card ^ 2 + 4 :=
    fun w _ => four_mul_le_sq_add_four _
  have heq : (∑ w : Fin 11,
      4 * ((E.coverMember i).filter fun e => w ∈ e.vertices).card)
      = ∑ w : Fin 11,
          (((E.coverMember i).filter fun e => w ∈ e.vertices).card ^ 2 + 4) := by
    rw [← Finset.mul_sum, hsum, Finset.sum_add_distrib, hsq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    norm_num [nsmul_eq_mul]
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp heq v (Finset.mem_univ v)
  have hz : ((((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ) - 2) ^ 2 = 0 := by
    have hcast : (4 : ℤ) *
        ((((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ))
        = (((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ) ^ 2 + 4 := by
      exact_mod_cast hpt
    linear_combination -hcast
  have htwo : ((((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ)) = 2 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    linarith
  exact_mod_cast htwo

/-- **Cherries are covered once.**  Two edges through a common vertex lie in
exactly one common member. -/
theorem cherry_exact_coverMember (e f : Edge11) (hef : e ≠ f)
    (hvm : Edge11.vmeet e f = 1) : pairCount E.coverMember e f = 1 := by
  have hne : E.edgeEquiv.symm e ≠ E.edgeEquiv.symm f := fun hcon =>
    hef (E.edgeEquiv.symm.injective hcon)
  have h := E.pairMult_add_vmeet_edgeEquiv (E.edgeEquiv.symm e) (E.edgeEquiv.symm f)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hvm, if_neg hne] at h
  rw [E.pairCount_coverMember]
  omega

/-- **Disjoint pairs are covered twice.**  Two edges with no common vertex lie
in exactly two common members. -/
theorem disjoint_twice_coverMember (e f : Edge11) (hvm : Edge11.vmeet e f = 0) :
    pairCount E.coverMember e f = 2 := by
  have hef : e ≠ f := by
    rintro rfl
    rw [Edge11.vmeet_self] at hvm
    exact absurd hvm (by norm_num)
  have hne : E.edgeEquiv.symm e ≠ E.edgeEquiv.symm f := fun hcon =>
    hef (E.edgeEquiv.symm.injective hcon)
  have h := E.pairMult_add_vmeet_edgeEquiv (E.edgeEquiv.symm e) (E.edgeEquiv.symm f)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hvm, if_neg hne] at h
  rw [E.pairCount_coverMember]
  omega

/-! ### The recoordinatisation -/

/-- Every `SRG266.QuasiSymmetric.Derived45`, on any `55`-element point type, is a
cherry cover of `K₁₁` once its points are named by
`SRG266.QuasiSymmetric.Derived45.blockGraph_iso_T11`. -/
noncomputable def toCherryCover : CherryCover where
  g := E.coverMember
  two_regular := E.two_regular_coverMember
  cherry_exact := E.cherry_exact_coverMember
  disjoint_twice := E.disjoint_twice_coverMember

/-- The blocks of the recoordinatisation, unfolded: the definitional `simp` API
of `Derived45.toCherryCover`. -/
@[simp] theorem toCherryCover_g (i : Fin 45) :
    E.toCherryCover.g i = (E.block i).image E.edgeEquiv := rfl

/-- **The recoordinatisation is an isomorphism of derived designs.**  Its point
map is the `T(11)` labelling and its index map is the identity. -/
noncomputable def isoToCherryCover : Derived45Iso E E.toCherryCover.toDerived45 where
  point := E.edgeEquiv
  index := Equiv.refl (Fin 45)
  map_block _ := rfl

/-- **The contradiction moves to `K₁₁`.**  A derived design carries a residual
structure only if its cherry cover does. -/
theorem isEmpty_residual165_of_toCherryCover
    (h : IsEmpty (Residual165 E.toCherryCover.toDerived45)) : IsEmpty (Residual165 E) :=
  isEmpty_residual165_of_iso E.isoToCherryCover h

end Derived45

/-! ### The design input -/

universe u

/-! No cherry cover of `K₁₁` carries a residual structure. -/
abbrev NoResidualCherryCover : Prop :=
  ∀ C : CherryCover, IsEmpty (Residual165 C.toDerived45)

/-- Delete a point of a hypothetical
quasi-symmetric `2-(56, 12, 9)` design with intersection numbers `0` and `3`,
recoordinatise the derived design into `K₁₁`
with `SRG266.QuasiSymmetric.Derived45.toCherryCover`, and read off the
contradiction. -/
theorem noQuasiSymmetricDesign56_of_noResidualCherryCover
    (h : NoResidualCherryCover) : NoQuasiSymmetricDesign56.{u} := by
  refine noQuasiSymmetricDesign56_of_concrete ⟨fun Q => ?_⟩
  exact ((Q.derived45 0).isEmpty_residual165_of_toCherryCover
    (h (Q.derived45 0).toCherryCover)).elim (Q.residual165 0)

end SRG266.QuasiSymmetric
