/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.Concrete

/-!
# The derived and residual structures at a point

Fix a point `z` of
a hypothetical quasi-symmetric `2-(56, 12, 9)` design with intersection numbers
`0` and `3`.  Deleting `z` splits the `210` blocks into

* the `45` blocks through `z`, which trace out `11`-element subsets of the `55`
  remaining points meeting pairwise in exactly `2` points — the *derived*
  structure, packaged as `SRG266.QuasiSymmetric.Derived45`;
* the `165` blocks missing `z`, which are `12`-element subsets meeting each
  other and each derived block in `0` or `3` points — the *residual*
  structure, packaged as `SRG266.QuasiSymmetric.Residual165`.

`Derived45` is exactly the dual of a `2-(45, 9, 2)` design.  These two
structures are the interface used below; nothing downstream mentions the
`56 × 210` matrix again.

The file ends with the interface theorem
`SRG266.QuasiSymmetric.exists_derived_residual`.

## Implementation notes

The `55` surviving points are the coercion `↥(Finset.univ.erase z)` of a
`Finset (Fin 56)`, which carries the required `Fintype` and `DecidableEq`
instances for free.  The `45` and `165` block indices are transported to
`Fin 45` and `Fin 165` by `Finset.equivFinOfCardEq`; the two reindexing
lemmas `card_filter_of_enum` and `card_filter_subtype` below are what make
those transports painless.
-/

open scoped BigOperators Matrix

namespace SRG266.QuasiSymmetric

/-! ### Generic counting helpers -/

section Counting

variable {α : Type*}

/-- The sum of a `0/1`-valued integer function counts the fibre over `1`. -/
theorem sum_eq_card_filter [Fintype α] (a : α → ℤ) (ha : ∀ x, a x = 0 ∨ a x = 1) :
    (∑ x, a x) = ((Finset.univ.filter fun x => a x = 1).card : ℤ) := by
  have hpoint : ∀ x, a x = if a x = 1 then (1 : ℤ) else 0 := by
    intro x
    rcases ha x with h | h <;> simp [h]
  rw [Finset.sum_congr rfl fun x _ => hpoint x]
  simp

/-- The inner product of two `0/1`-valued integer functions counts the points
where both are `1`. -/
theorem sum_mul_eq_card_filter [Fintype α] (a b : α → ℤ)
    (ha : ∀ x, a x = 0 ∨ a x = 1) (hb : ∀ x, b x = 0 ∨ b x = 1) :
    (∑ x, a x * b x) =
      ((Finset.univ.filter fun x => a x = 1 ∧ b x = 1).card : ℤ) := by
  have hpoint : ∀ x, a x * b x = if a x = 1 ∧ b x = 1 then (1 : ℤ) else 0 := by
    intro x
    rcases ha x with h | h <;> rcases hb x with h' | h' <;> simp [h, h']
  rw [Finset.sum_congr rfl fun x _ => hpoint x]
  simp

/-- Filtering over the coercion of a `Finset` to a type is filtering over the
`Finset`. -/
theorem card_filter_subtype [DecidableEq α] (s : Finset α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun x : ↥s => p x.val).card = (s.filter p).card := by
  rw [← Finset.card_image_of_injective _ (Subtype.val_injective (p := (· ∈ s)))]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hpx⟩
    exact ⟨⟨x, hx⟩, hpx, rfl⟩

/-- Counting over an enumeration `b : Fin n → α` of a `Finset` is counting over
the `Finset`. -/
theorem card_filter_of_enum [DecidableEq α] {n : ℕ} (b : Fin n → α) (s : Finset α)
    (hinj : Function.Injective b) (hrange : ∀ x, x ∈ s ↔ ∃ i, b i = x)
    (p : α → Prop) [DecidablePred p] :
    (Finset.univ.filter fun i => p (b i)).card = (s.filter p).card := by
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext x
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨(hrange _).mpr ⟨i, rfl⟩, hi⟩
  · rintro ⟨hx, hpx⟩
    obtain ⟨i, rfl⟩ := (hrange x).mp hx
    exact ⟨i, hpx, rfl⟩

end Counting

/-! ### Point and block incidence sets of a concrete design -/

namespace ConcreteQSD56

variable (Q : ConcreteQSD56)

/-- The points on a block. -/
def pointsOn (B : Fin 210) : Finset (Fin 56) :=
  Finset.univ.filter fun p => Q.matrix p B = 1

/-- The points on two blocks at once. -/
def pointsOnPair (B D : Fin 210) : Finset (Fin 56) :=
  Finset.univ.filter fun p => Q.matrix p B = 1 ∧ Q.matrix p D = 1

/-- The blocks through a point. -/
def blocksThrough (p : Fin 56) : Finset (Fin 210) :=
  Finset.univ.filter fun B => Q.matrix p B = 1

/-- The blocks through two points at once. -/
def blocksThroughPair (p q : Fin 56) : Finset (Fin 210) :=
  Finset.univ.filter fun B => Q.matrix p B = 1 ∧ Q.matrix q B = 1

/-- Membership in the point set of a block. -/
@[simp] theorem mem_pointsOn {B : Fin 210} {p : Fin 56} :
    p ∈ Q.pointsOn B ↔ Q.matrix p B = 1 := by
  simp [pointsOn]

/-- Membership in the block set through a point. -/
@[simp] theorem mem_blocksThrough {p : Fin 56} {B : Fin 210} :
    B ∈ Q.blocksThrough p ↔ Q.matrix p B = 1 := by
  simp [blocksThrough]

/-- Every block carries exactly `12` points. -/
theorem card_pointsOn (B : Fin 210) : (Q.pointsOn B).card = 12 := by
  have hcol := Q.block_size B
  rw [incidenceColumnSum,
    sum_eq_card_filter (fun p => Q.matrix p B) fun p => Q.entry_cases p B] at hcol
  exact_mod_cast hcol

/-- Every point lies on exactly `45` blocks. -/
theorem card_blocksThrough (p : Fin 56) : (Q.blocksThrough p).card = 45 := by
  have hrow := Q.row_sum p
  rw [sum_eq_card_filter (fun B => Q.matrix p B) fun B => Q.entry_cases p B] at hrow
  exact_mod_cast hrow

/-- Two distinct points lie on exactly `9` common blocks. -/
theorem card_blocksThroughPair {p q : Fin 56} (h : p ≠ q) :
    (Q.blocksThroughPair p q).card = 9 := by
  have hgram := Q.point_gram p q
  rw [Matrix.mul_apply] at hgram
  simp only [Matrix.transpose_apply] at hgram
  rw [sum_mul_eq_card_filter (fun B => Q.matrix p B) (fun B => Q.matrix q B)
    (fun B => Q.entry_cases p B) fun B => Q.entry_cases q B, if_neg h] at hgram
  exact_mod_cast hgram

/-- Two distinct blocks meet in `0` or `3` points. -/
theorem card_pointsOnPair {B D : Fin 210} (h : B ≠ D) :
    (Q.pointsOnPair B D).card = 0 ∨ (Q.pointsOnPair B D).card = 3 := by
  have hinter := Q.block_intersections h
  rw [Matrix.mul_apply] at hinter
  simp only [Matrix.transpose_apply] at hinter
  rw [sum_mul_eq_card_filter (fun p => Q.matrix p B) (fun p => Q.matrix p D)
    (fun p => Q.entry_cases p B) fun p => Q.entry_cases p D] at hinter
  rcases hinter with h' | h'
  · exact Or.inl (by exact_mod_cast h')
  · exact Or.inr (by exact_mod_cast h')

end ConcreteQSD56

/-! ### Derived and residual interfaces -/

/-- The derived structure of a quasi-symmetric `2-(56, 12, 9)` design at a
point: `45` blocks of size `11` on `55` points, pairwise meeting in `2` points,
each point on `9` of them.  Equivalently, the dual of a `2-(45, 9, 2)`
design. -/
structure Derived45 (P : Type*) [Fintype P] [DecidableEq P] where
  /-- The `45` derived blocks. -/
  block : Fin 45 → Finset P
  /-- There are `55` points. -/
  point_card : Fintype.card P = 55
  /-- Every derived block has `11` points. -/
  block_card : ∀ i, (block i).card = 11
  /-- Distinct derived blocks meet in exactly `2` points. -/
  pair_meet : ∀ i j, i ≠ j → ((block i) ∩ (block j)).card = 2
  /-- Every point lies on exactly `9` derived blocks. -/
  replication : ∀ p, (Finset.univ.filter fun i => p ∈ block i).card = 9

/-- The residual structure accompanying a `Derived45`: the `165` blocks missing
the deleted point, as `12`-element subsets of the same `55` points. -/
structure Residual165 {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P) where
  /-- The `165` residual blocks. -/
  res : Fin 165 → Finset P
  /-- Every residual block has `12` points. -/
  res_card : ∀ n, (res n).card = 12
  /-- Distinct residual blocks meet in `0` or `3` points. -/
  res_meet : ∀ m n, m ≠ n →
    ((res m) ∩ (res n)).card = 0 ∨ ((res m) ∩ (res n)).card = 3
  /-- A derived block and a residual block meet in `0` or `3` points. -/
  cross_meet : ∀ i n,
    ((E.block i) ∩ (res n)).card = 0 ∨ ((E.block i) ∩ (res n)).card = 3
  /-- Every point lies on exactly `36` residual blocks. -/
  res_rep : ∀ p, (Finset.univ.filter fun n => p ∈ res n).card = 36
  /-- Distinct residual block indices carry distinct point sets. -/
  res_inj : Function.Injective res

/-! ### Construction from a concrete design -/

/-- The `55` points other than `z`. -/
abbrev Punctured (z : Fin 56) : Type := ↥((Finset.univ : Finset (Fin 56)).erase z)

/-- There are `55` points other than `z`. -/
theorem card_punctured (z : Fin 56) : Fintype.card (Punctured z) = 55 := by
  rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ z)]
  simp

namespace ConcreteQSD56

variable (Q : ConcreteQSD56) (z : Fin 56)

/-- The blocks through `z`. -/
def derivedIndex : Finset (Fin 210) := Q.blocksThrough z

/-- The blocks missing `z`. -/
def residualIndex : Finset (Fin 210) :=
  Finset.univ.filter fun B => Q.matrix z B = 0

/-- The trace of a block on the `55` points other than `z`. -/
def restrictedBlock (B : Fin 210) : Finset (Punctured z) :=
  Finset.univ.filter fun p => Q.matrix p.val B = 1

variable {Q z}

/-- Membership in the derived block index. -/
@[simp] theorem mem_derivedIndex {B : Fin 210} :
    B ∈ Q.derivedIndex z ↔ Q.matrix z B = 1 := by
  simp [derivedIndex]

/-- Membership in the residual block index. -/
@[simp] theorem mem_residualIndex {B : Fin 210} :
    B ∈ Q.residualIndex z ↔ Q.matrix z B = 0 := by
  simp [residualIndex]

/-- Membership in the trace of a block on the punctured point set. -/
@[simp] theorem mem_restrictedBlock {B : Fin 210} {p : Punctured z} :
    p ∈ Q.restrictedBlock z B ↔ Q.matrix p.val B = 1 := by
  simp [restrictedBlock]

variable (Q z)

/-- There are `45` blocks through `z`. -/
theorem card_derivedIndex : (Q.derivedIndex z).card = 45 :=
  Q.card_blocksThrough z

/-- There are `165` blocks missing `z`. -/
theorem card_residualIndex : (Q.residualIndex z).card = 165 := by
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin 210)))
      (p := fun B => Q.matrix z B = 1)
  have hneg : (Finset.univ.filter fun B => ¬ Q.matrix z B = 1) = Q.residualIndex z := by
    ext B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_residualIndex]
    rcases Q.entry_cases z B with h | h <;> simp [h]
  have hpos : (Finset.univ.filter fun B => Q.matrix z B = 1) = Q.derivedIndex z := rfl
  rw [hpos, hneg, card_derivedIndex] at hsplit
  simp only [Finset.card_univ, Fintype.card_fin] at hsplit
  omega

/-- The trace of a block on the punctured point set is the block's point set
with `z` removed. -/
theorem restrictedBlock_card (B : Fin 210) :
    (Q.restrictedBlock z B).card = ((Q.pointsOn B).erase z).card := by
  rw [restrictedBlock,
    card_filter_subtype (Finset.univ.erase z) fun p => Q.matrix p B = 1,
    Finset.filter_erase]
  rfl

/-- The trace of two blocks on the punctured point set. -/
theorem restrictedBlock_inter_card (B D : Fin 210) :
    (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card =
      ((Q.pointsOnPair B D).erase z).card := by
  have hand :
      Q.restrictedBlock z B ∩ Q.restrictedBlock z D =
        Finset.univ.filter fun p : Punctured z =>
          Q.matrix p.val B = 1 ∧ Q.matrix p.val D = 1 := by
    ext p
    simp [restrictedBlock]
  rw [hand,
    card_filter_subtype (Finset.univ.erase z)
      fun p => Q.matrix p B = 1 ∧ Q.matrix p D = 1,
    Finset.filter_erase]
  rfl

variable {Q z}

/-- A block through `z` traces out `11` points. -/
theorem card_restrictedBlock_of_through {B : Fin 210} (h : Q.matrix z B = 1) :
    (Q.restrictedBlock z B).card = 11 := by
  have hmem : z ∈ Q.pointsOn B := Q.mem_pointsOn.mpr h
  rw [restrictedBlock_card, Finset.card_erase_of_mem hmem, Q.card_pointsOn B]

/-- A block missing `z` traces out all `12` of its points. -/
theorem card_restrictedBlock_of_missing {B : Fin 210} (h : Q.matrix z B = 0) :
    (Q.restrictedBlock z B).card = 12 := by
  have hmem : z ∉ Q.pointsOn B := by
    simp only [ConcreteQSD56.mem_pointsOn, h]
    norm_num
  rw [restrictedBlock_card, Finset.erase_eq_of_notMem hmem, Q.card_pointsOn B]

/-- Two distinct blocks through `z` trace out sets meeting in
exactly `2` points: their full intersection has `3` points, one of which is
`z`. -/
theorem card_restrictedBlock_inter_of_through {B D : Fin 210}
    (hB : Q.matrix z B = 1) (hD : Q.matrix z D = 1) (hBD : B ≠ D) :
    (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card = 2 := by
  have hmem : z ∈ Q.pointsOnPair B D := by
    simp only [pointsOnPair, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hB, hD⟩
  have hpos : (Q.pointsOnPair B D).card ≠ 0 := by
    intro hzero
    rw [Finset.card_eq_zero] at hzero
    exact absurd hmem (by simp [hzero])
  have hthree : (Q.pointsOnPair B D).card = 3 :=
    (Q.card_pointsOnPair hBD).resolve_left hpos
  rw [restrictedBlock_inter_card, Finset.card_erase_of_mem hmem, hthree]

/-- A block through `z` and a block missing `z` trace out sets
meeting in `0` or `3` points. -/
theorem card_restrictedBlock_inter_of_missing {B D : Fin 210}
    (hD : Q.matrix z D = 0) (hBD : B ≠ D) :
    (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card = 0 ∨
      (Q.restrictedBlock z B ∩ Q.restrictedBlock z D).card = 3 := by
  have hmem : z ∉ Q.pointsOnPair B D := by
    simp only [pointsOnPair, Finset.mem_filter, Finset.mem_univ, true_and, hD,
      not_and]
    intro _
    norm_num
  rw [restrictedBlock_inter_card, Finset.erase_eq_of_notMem hmem]
  exact Q.card_pointsOnPair hBD

/-- A point other than `z` lies on `9` blocks through `z`. -/
theorem card_derivedIndex_filter {p : Fin 56} (hp : p ≠ z) :
    ((Q.derivedIndex z).filter fun B => Q.matrix p B = 1).card = 9 := by
  have hfilter :
      (Q.derivedIndex z).filter (fun B => Q.matrix p B = 1) =
        Q.blocksThroughPair z p := by
    ext B
    simp only [Finset.mem_filter, mem_derivedIndex, blocksThroughPair,
      Finset.mem_univ, true_and]
  rw [hfilter]
  exact Q.card_blocksThroughPair (Ne.symm hp)

/-- A point other than `z` lies on `36` blocks missing `z`. -/
theorem card_residualIndex_filter {p : Fin 56} (hp : p ≠ z) :
    ((Q.residualIndex z).filter fun B => Q.matrix p B = 1).card = 36 := by
  have hsplit :=
    Finset.card_filter_add_card_filter_not (s := Q.blocksThrough p)
      (p := fun B => Q.matrix z B = 1)
  have hpos :
      ((Q.blocksThrough p).filter fun B => Q.matrix z B = 1) =
        (Q.derivedIndex z).filter fun B => Q.matrix p B = 1 := by
    ext B
    simp only [Finset.mem_filter, mem_blocksThrough, mem_derivedIndex]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hneg :
      ((Q.blocksThrough p).filter fun B => ¬ Q.matrix z B = 1) =
        (Q.residualIndex z).filter fun B => Q.matrix p B = 1 := by
    ext B
    simp only [Finset.mem_filter, mem_blocksThrough, mem_residualIndex]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Q.entry_cases z B).resolve_right h2, h1⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [h1]
      norm_num
  rw [hpos, hneg, card_derivedIndex_filter hp, Q.card_blocksThrough p] at hsplit
  omega

end ConcreteQSD56

/-! ### The derived and residual structures as data

The construction is packaged as two `def`s rather than as a bare existence
statement, so that the finite contradiction can be
stated as "no concrete design has *this* derived design at *that* point".
-/

namespace ConcreteQSD56

variable (Q : ConcreteQSD56) (z : Fin 56)

/-- An enumeration of the `45` blocks through `z`. -/
noncomputable def derivedEnum (i : Fin 45) : Fin 210 :=
  ((Finset.equivFinOfCardEq (card_derivedIndex Q z)).symm i : Fin 210)

/-- An enumeration of the `165` blocks missing `z`. -/
noncomputable def residualEnum (n : Fin 165) : Fin 210 :=
  ((Finset.equivFinOfCardEq (card_residualIndex Q z)).symm n : Fin 210)

variable {Q z}

/-- Every enumerated derived index is a block through `z`. -/
theorem derivedEnum_mem (i : Fin 45) : Q.derivedEnum z i ∈ Q.derivedIndex z :=
  ((Finset.equivFinOfCardEq (card_derivedIndex Q z)).symm i).2

/-- Every enumerated residual index is a block missing `z`. -/
theorem residualEnum_mem (n : Fin 165) : Q.residualEnum z n ∈ Q.residualIndex z :=
  ((Finset.equivFinOfCardEq (card_residualIndex Q z)).symm n).2

/-- The enumerated derived blocks contain `z`. -/
theorem derivedEnum_one (i : Fin 45) : Q.matrix z (Q.derivedEnum z i) = 1 :=
  mem_derivedIndex.mp (derivedEnum_mem i)

/-- The enumerated residual blocks miss `z`. -/
theorem residualEnum_zero (n : Fin 165) : Q.matrix z (Q.residualEnum z n) = 0 :=
  mem_residualIndex.mp (residualEnum_mem n)

/-- The enumeration of the derived blocks is injective. -/
theorem derivedEnum_injective : Function.Injective (Q.derivedEnum z) := fun _ _ hij =>
  (Finset.equivFinOfCardEq (card_derivedIndex Q z)).symm.injective (Subtype.ext hij)

/-- The enumeration of the residual blocks is injective. -/
theorem residualEnum_injective : Function.Injective (Q.residualEnum z) := fun _ _ hmn =>
  (Finset.equivFinOfCardEq (card_residualIndex Q z)).symm.injective (Subtype.ext hmn)

/-- The enumeration of the derived blocks is onto the blocks through `z`. -/
theorem derivedEnum_range (B : Fin 210) :
    B ∈ Q.derivedIndex z ↔ ∃ i, Q.derivedEnum z i = B := by
  constructor
  · intro hB
    exact ⟨Finset.equivFinOfCardEq (card_derivedIndex Q z) ⟨B, hB⟩, by simp [derivedEnum]⟩
  · rintro ⟨i, rfl⟩
    exact derivedEnum_mem i

/-- The enumeration of the residual blocks is onto the blocks missing `z`. -/
theorem residualEnum_range (B : Fin 210) :
    B ∈ Q.residualIndex z ↔ ∃ n, Q.residualEnum z n = B := by
  constructor
  · intro hB
    exact ⟨Finset.equivFinOfCardEq (card_residualIndex Q z) ⟨B, hB⟩, by simp [residualEnum]⟩
  · rintro ⟨n, rfl⟩
    exact residualEnum_mem n

/-- A block through `z` is never a block missing `z`. -/
theorem derivedEnum_ne_residualEnum (i : Fin 45) (n : Fin 165) :
    Q.derivedEnum z i ≠ Q.residualEnum z n := by
  intro h
  have h1 := derivedEnum_one (Q := Q) (z := z) i
  rw [h, residualEnum_zero (Q := Q) (z := z) n] at h1
  norm_num at h1

variable (Q z)

/-- The derived structure of a concrete quasi-symmetric
`2-(56, 12, 9)` design at a point: the `45` blocks through `z`, traced on the
`55` remaining points. -/
noncomputable def derived45 : Derived45 (Punctured z) where
  block i := Q.restrictedBlock z (Q.derivedEnum z i)
  point_card := card_punctured z
  block_card i := card_restrictedBlock_of_through (derivedEnum_one i)
  pair_meet i j hij :=
    card_restrictedBlock_inter_of_through (derivedEnum_one i) (derivedEnum_one j)
      fun h => hij (derivedEnum_injective h)
  replication := by
    classical
    intro p
    have hp : p.val ≠ z := (Finset.mem_erase.mp p.2).1
    rw [show (Finset.univ.filter fun i => p ∈ Q.restrictedBlock z (Q.derivedEnum z i)) =
        Finset.univ.filter fun i => Q.matrix p.val (Q.derivedEnum z i) = 1 by
      ext i; simp]
    rw [card_filter_of_enum (Q.derivedEnum z) (Q.derivedIndex z) derivedEnum_injective
      derivedEnum_range fun B => Q.matrix p.val B = 1]
    exact card_derivedIndex_filter hp

/-- The residual structure accompanying `derived45`: the
`165` blocks missing `z`. -/
noncomputable def residual165 : Residual165 (Q.derived45 z) where
  res n := Q.restrictedBlock z (Q.residualEnum z n)
  res_card n := card_restrictedBlock_of_missing (residualEnum_zero n)
  res_meet m n hmn :=
    card_restrictedBlock_inter_of_missing (residualEnum_zero n)
      fun h => hmn (residualEnum_injective h)
  cross_meet i n :=
    card_restrictedBlock_inter_of_missing (residualEnum_zero n)
      (derivedEnum_ne_residualEnum i n)
  res_rep := by
    classical
    intro p
    have hp : p.val ≠ z := (Finset.mem_erase.mp p.2).1
    rw [show (Finset.univ.filter fun n => p ∈ Q.restrictedBlock z (Q.residualEnum z n)) =
        Finset.univ.filter fun n => Q.matrix p.val (Q.residualEnum z n) = 1 by
      ext n; simp]
    rw [card_filter_of_enum (Q.residualEnum z) (Q.residualIndex z) residualEnum_injective
      residualEnum_range fun B => Q.matrix p.val B = 1]
    exact card_residualIndex_filter hp
  res_inj := by
    intro m n hmn
    by_contra hne
    have hmeet :=
      card_restrictedBlock_inter_of_missing (Q := Q) (z := z) (residualEnum_zero n)
        (fun h => hne (residualEnum_injective h))
    rw [show Q.restrictedBlock z (Q.residualEnum z m) =
        Q.restrictedBlock z (Q.residualEnum z n) from hmn, Finset.inter_self,
      card_restrictedBlock_of_missing (residualEnum_zero n)] at hmeet
    omega

end ConcreteQSD56

/-! ### Interface theorem -/

/-- Deleting any point `z` of a concrete
quasi-symmetric `2-(56, 12, 9)` design with intersection numbers `0` and `3`
produces a derived structure `Derived45` on the remaining `55` points together
with its residual structure `Residual165`. -/
theorem exists_derived_residual_at (Q : ConcreteQSD56) (z : Fin 56) :
    ∃ (P : Type) (instF : Fintype P) (instD : DecidableEq P)
      (E : @Derived45 P instF instD), Nonempty (@Residual165 P instF instD E) :=
  ⟨Punctured z, inferInstance, inferInstance, Q.derived45 z, ⟨Q.residual165 z⟩⟩

/-- Every concrete quasi-symmetric `2-(56, 12, 9)` design
with intersection numbers `0` and `3` carries a derived structure `Derived45`
together with its residual structure `Residual165`.

This is the only statement about the `56 × 210` incidence matrix that the
subsequent arguments consume. -/
theorem exists_derived_residual (Q : ConcreteQSD56) :
    ∃ (P : Type) (instF : Fintype P) (instD : DecidableEq P)
      (E : @Derived45 P instF instD), Nonempty (@Residual165 P instF instD E) :=
  exists_derived_residual_at Q 0

end SRG266.QuasiSymmetric
