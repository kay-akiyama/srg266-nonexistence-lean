/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.ArcDegree
import SRG266.Search.SubsetDFS

/-!
# Bitmask coordinates for the edges of `K₁₁`

Kernel reduction on `Finset (Sym2 (Fin 11))` is too expensive for the finite
searches, so they run on natural-number bitmasks.  This file
is the single bridge between the two worlds.

An `SRG266.QuasiSymmetric.EdgeCoding` is an injective numbering
`Edge11 → {0, …, 54}` of the `55` edges of `K₁₁`.  Injectivity plus the bound is
already enough for it to be a bijection, and that is what makes the dictionary
work:

* `EdgeCoding.maskOf` sends a `Finset Edge11` to a natural number `< 2 ^ 55`,
  `EdgeCoding.edgesOfMask` sends it back, and the two are mutually inverse;
* intersection becomes `Nat.land` (`EdgeCoding.maskOf_and`) and cardinality
  becomes `SRG266.Search.popcount` (`EdgeCoding.popcount_maskOf`).

The numbering is *not* fixed once and for all: each listed design carries its
own, chosen so that the members of its cherry cover close as early as possible
in the depth-first arc search.  That choice halves the number of pruning tests
the kernel performs, and nothing in this file depends on which numbering is
used.

The file ends with `cherryCoverOfData`, which turns six packed tables together
with a handful of `decide`-checkable numerical facts into a genuine
`SRG266.QuasiSymmetric.CherryCover`.

## Main results

* `SRG266.QuasiSymmetric.Edge11.key_injective`
* `SRG266.QuasiSymmetric.EdgeCoding.card_edgesOfMask`,
  `SRG266.QuasiSymmetric.EdgeCoding.popcount_maskOf`
* `SRG266.QuasiSymmetric.codingOfTable`, `SRG266.QuasiSymmetric.cherryCoverOfData`
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-! ### The two endpoints of an edge, ordered -/

namespace Edge11

/-- The smaller endpoint of an edge. -/
def lo (e : Edge11) : Fin 11 :=
  e.vertices.min' (Finset.card_pos.mp (by rw [card_vertices]; norm_num))

/-- The larger endpoint of an edge. -/
def hi (e : Edge11) : Fin 11 :=
  e.vertices.max' (Finset.card_pos.mp (by rw [card_vertices]; norm_num))

theorem lo_mem (e : Edge11) : e.lo ∈ e.vertices := Finset.min'_mem _ _

theorem hi_mem (e : Edge11) : e.hi ∈ e.vertices := Finset.max'_mem _ _

theorem lo_lt_hi (e : Edge11) : e.lo < e.hi :=
  Finset.min'_lt_max'_of_card _ (by rw [card_vertices]; norm_num)

/-- An edge is the pair of its two ordered endpoints. -/
theorem vertices_eq (e : Edge11) : e.vertices = {e.lo, e.hi} := by
  classical
  refine (Finset.eq_of_subset_of_card_le ?_ ?_).symm
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact lo_mem e
    · exact hi_mem e
  · rw [card_vertices, Finset.card_insert_of_notMem (by simpa using (lo_lt_hi e).ne),
      Finset.card_singleton]

/-- Membership in an edge, in terms of its ordered endpoints. -/
theorem mem_vertices_iff {v : Fin 11} {e : Edge11} :
    v ∈ e.vertices ↔ v = e.lo ∨ v = e.hi := by
  rw [vertices_eq]; simp

/-- The *key* of an edge: `11` times the smaller endpoint plus the larger one.
It is `< 121` and determines the edge. -/
def key (e : Edge11) : ℕ := 11 * (e.lo : ℕ) + (e.hi : ℕ)

theorem key_lt (e : Edge11) : e.key < 121 := by
  have h1 : (e.lo : ℕ) < 11 := e.lo.isLt
  have h2 : (e.hi : ℕ) < 11 := e.hi.isLt
  rw [key]; omega

/-- The key determines the edge. -/
theorem key_injective : Function.Injective key := by
  intro e f h
  have h1 : (e.hi : ℕ) < 11 := e.hi.isLt
  have h2 : (f.hi : ℕ) < 11 := f.hi.isLt
  rw [key, key] at h
  have hlo : e.lo = f.lo := Fin.ext (by omega)
  have hhi : e.hi = f.hi := Fin.ext (by omega)
  have hne : e.lo ≠ e.hi := (lo_lt_hi e).ne
  rw [eq_of_mem_mem hne (lo_mem e) (hi_mem e),
    eq_of_mem_mem (hlo ▸ hhi ▸ hne : f.lo ≠ f.hi) (lo_mem f) (hi_mem f)]
  simp [hlo, hhi]

/-- Every key of an ordered pair of distinct vertices is realised. -/
theorem exists_key {a b : Fin 11} (hab : a < b) : ∃ e : Edge11, e.key = 11 * (a : ℕ) + b := by
  refine ⟨mk' hab.ne, ?_⟩
  have hv : (mk' hab.ne).vertices = {a, b} := vertices_mk' hab.ne
  have hlo : (mk' hab.ne).lo = a := by
    refine le_antisymm (Finset.min'_le _ _ (by rw [hv]; simp)) ?_
    refine Finset.le_min' _ _ _ fun y hy => ?_
    rw [hv] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact le_rfl
    · exact hab.le
  have hhi : (mk' hab.ne).hi = b := by
    refine le_antisymm (Finset.max'_le _ _ _ fun y hy => ?_) (Finset.le_max' _ _ (by rw [hv]; simp))
    rw [hv] at hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact hab.le
    · exact le_rfl
  rw [key, hlo, hhi]

end Edge11

/-! ### Numbering the edges -/

/-- A numbering of the `55` edges of `K₁₁` by the naturals below `55`.  The two
fields are all a bitmask dictionary needs: being injective into a set of its own
size, such a numbering is automatically a bijection. -/
structure EdgeCoding where
  /-- The position an edge occupies in a bitmask. -/
  idx : Edge11 → ℕ
  /-- Positions are below `55`. -/
  idx_lt : ∀ e, idx e < 55
  /-- Distinct edges occupy distinct positions. -/
  idx_injective : Function.Injective idx

namespace EdgeCoding

variable (c : EdgeCoding)

/-- An edge numbering hits every position below `55`. -/
theorem exists_idx {k : ℕ} (hk : k < 55) : ∃ e : Edge11, c.idx e = k := by
  classical
  have hsub : (Finset.univ.image c.idx) ⊆ Finset.range 55 := by
    intro k hk
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (c.idx_lt e)
  have hcard : (Finset.univ.image c.idx).card = 55 := by
    rw [Finset.card_image_of_injective _ c.idx_injective, Finset.card_univ, Edge11.card_edge11]
  have heq : Finset.univ.image c.idx = Finset.range 55 :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard, Finset.card_range])
  have : k ∈ Finset.univ.image c.idx := by rw [heq]; exact Finset.mem_range.mpr hk
  obtain ⟨e, -, he⟩ := Finset.mem_image.mp this
  exact ⟨e, he⟩

/-- The set of edges a bitmask describes. -/
def edgesOfMask (m : ℕ) : Finset Edge11 :=
  Finset.univ.filter fun e => m.testBit (c.idx e) = true

@[simp] theorem mem_edgesOfMask {m : ℕ} {e : Edge11} :
    e ∈ c.edgesOfMask m ↔ m.testBit (c.idx e) = true := by
  simp [edgesOfMask]

/-- The bitmask describing a set of edges. -/
def maskOf (s : Finset Edge11) : ℕ := s.fold (· ||| ·) 0 fun e => 2 ^ c.idx e

theorem maskOf_empty : c.maskOf (∅ : Finset Edge11) = 0 := rfl

theorem maskOf_insert {a : Edge11} {s : Finset Edge11} (ha : a ∉ s) :
    c.maskOf (insert a s) = 2 ^ c.idx a ||| c.maskOf s := by
  classical
  rw [maskOf, maskOf, Finset.fold_insert ha]

theorem testBit_maskOf (s : Finset Edge11) (k : ℕ) :
    (c.maskOf s).testBit k = true ↔ ∃ e ∈ s, c.idx e = k := by
  classical
  induction s using Finset.induction with
  | empty => simp [c.maskOf_empty]
  | insert a s ha ih =>
      rw [c.maskOf_insert ha, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, ih]
      constructor
      · rintro (h | ⟨e, he, rfl⟩)
        · exact ⟨a, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨e, Finset.mem_insert_of_mem he, rfl⟩
      · rintro ⟨e, he, rfl⟩
        rcases Finset.mem_insert.mp he with rfl | he'
        · exact Or.inl (by simp)
        · exact Or.inr ⟨e, he', rfl⟩

theorem maskOf_lt (s : Finset Edge11) : c.maskOf s < 2 ^ 55 := by
  classical
  induction s using Finset.induction with
  | empty => simp [c.maskOf_empty]
  | insert a s ha ih =>
      rw [c.maskOf_insert ha]
      exact Nat.or_lt_two_pow (Nat.pow_lt_pow_right (by norm_num) (c.idx_lt a)) ih

@[simp] theorem edgesOfMask_maskOf (s : Finset Edge11) : c.edgesOfMask (c.maskOf s) = s := by
  ext e
  rw [mem_edgesOfMask, c.testBit_maskOf]
  constructor
  · rintro ⟨e', he', h⟩
    exact c.idx_injective h ▸ he'
  · intro he
    exact ⟨e, he, rfl⟩

theorem maskOf_injective : Function.Injective c.maskOf := fun s t h => by
  rw [← c.edgesOfMask_maskOf s, ← c.edgesOfMask_maskOf t, h]

theorem maskOf_edgesOfMask {m : ℕ} (hm : m < 2 ^ 55) : c.maskOf (c.edgesOfMask m) = m := by
  refine Nat.eq_of_testBit_eq fun k => Bool.eq_iff_iff.mpr ?_
  rw [c.testBit_maskOf]
  constructor
  · rintro ⟨e, he, rfl⟩
    exact c.mem_edgesOfMask.mp he
  · intro hbit
    have hk : k < 55 := by
      by_contra hcon
      have hzero : m.testBit k = false :=
        Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hm (Nat.pow_le_pow_right (by norm_num) (by omega)))
      rw [hzero] at hbit
      exact Bool.noConfusion hbit
    obtain ⟨e, rfl⟩ := c.exists_idx hk
    exact ⟨e, c.mem_edgesOfMask.mpr hbit, rfl⟩

theorem edgesOfMask_and (m m' : ℕ) :
    c.edgesOfMask (m &&& m') = c.edgesOfMask m ∩ c.edgesOfMask m' := by
  ext e
  simp [mem_edgesOfMask, Nat.testBit_and]

theorem maskOf_and (s t : Finset Edge11) : c.maskOf (s ∩ t) = c.maskOf s &&& c.maskOf t := by
  have h : c.edgesOfMask (c.maskOf s &&& c.maskOf t) = s ∩ t := by
    rw [c.edgesOfMask_and, c.edgesOfMask_maskOf, c.edgesOfMask_maskOf]
  rw [← h, c.maskOf_edgesOfMask (Nat.and_lt_two_pow _ (c.maskOf_lt t))]

end EdgeCoding

/-! ### Counting the bits of a mask -/

/-- Cardinality of a filter by bit membership, along an injective numbering that
exhausts the window.  Both bitmask dictionaries of the development — the `55`
edges of `K₁₁` and the `45` members of a cherry cover — are instances. -/
theorem card_filter_testBit {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℕ) (N : ℕ)
    (hlt : ∀ i, f i < N) (hinj : Function.Injective f) (hcard : Fintype.card ι = N)
    {m : ℕ} (hm : m < 2 ^ N) :
    (Finset.univ.filter fun i => m.testBit (f i) = true).card = popcount m := by
  classical
  have hsurj : ∀ k < N, ∃ i, f i = k := by
    intro k hk
    have hsub : (Finset.univ.image f) ⊆ Finset.range N := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_range.mpr (hlt i)
    have hcimg : (Finset.univ.image f).card = N := by
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcard]
    have heq : Finset.univ.image f = Finset.range N :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcimg, Finset.card_range])
    have : k ∈ Finset.univ.image f := by rw [heq]; exact Finset.mem_range.mpr hk
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp this
    exact ⟨i, hi⟩
  rw [popcount_correct m N hm]
  refine Finset.card_bij (fun i _ => f i) ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_filter] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (hlt i), hi.2⟩
  · intro i _ j _ h
    exact hinj h
  · intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨i, rfl⟩ := hsurj k hk.1
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hk.2⟩, rfl⟩

namespace EdgeCoding

variable (c : EdgeCoding)

/-- The size of the edge set a mask describes is the mask's population count. -/
theorem card_edgesOfMask {m : ℕ} (hm : m < 2 ^ 55) :
    (c.edgesOfMask m).card = popcount m :=
  card_filter_testBit c.idx 55 c.idx_lt c.idx_injective Edge11.card_edge11 hm

/-- The population count of the mask of a set of edges is the size of the set. -/
theorem popcount_maskOf (s : Finset Edge11) : popcount (c.maskOf s) = s.card := by
  rw [← c.card_edgesOfMask (c.maskOf_lt s), c.edgesOfMask_maskOf]

/-- Intersecting sets of edges is `Nat.land` on their masks. -/
theorem popcount_and_maskOf (s t : Finset Edge11) :
    popcount (c.maskOf s &&& c.maskOf t) = (s ∩ t).card := by
  rw [← c.card_edgesOfMask (Nat.and_lt_two_pow _ (c.maskOf_lt t)), c.edgesOfMask_and,
    c.edgesOfMask_maskOf, c.edgesOfMask_maskOf]

end EdgeCoding

/-! ### Packed tables

All certificate data is stored as a single natural number per table, sliced by
shift-and-mask.  The module header of `SRG266/Search/SubsetDFS.lean` records the
measurement that forces this: an `Array` lookup in the kernel is a list
traversal and costs about seventy times more.
-/

/-- The `k`-th `w`-bit field of a packed table. -/
def slice (t w k : ℕ) : ℕ := (t >>> (w * k)) &&& (2 ^ w - 1)

theorem slice_lt (t w k : ℕ) : slice t w k < 2 ^ w :=
  Nat.and_lt_two_pow _ (Nat.sub_lt (Nat.two_pow_pos w) Nat.one_pos)

/-- An edge numbering read off a packed table of six-bit fields, indexed by
`SRG266.QuasiSymmetric.Edge11.key`.  The second hypothesis exhibits a left
inverse, which is what makes the numbering injective; both hypotheses are
`decide`-checkable over the `121` keys. -/
def codingOfTable (tbl inv : ℕ)
    (hlt : ∀ a < 11, ∀ b < 11, a < b → slice tbl 6 (11 * a + b) < 55)
    (hinv : ∀ a < 11, ∀ b < 11, a < b →
      slice inv 7 (slice tbl 6 (11 * a + b)) = 11 * a + b) :
    EdgeCoding where
  idx e := slice tbl 6 e.key
  idx_lt e := hlt _ e.lo.isLt _ e.hi.isLt (Fin.lt_def.mp e.lo_lt_hi)
  idx_injective := by
    intro e f h
    have he := hinv _ e.lo.isLt _ e.hi.isLt (Fin.lt_def.mp e.lo_lt_hi)
    have hf := hinv _ f.lo.isLt _ f.hi.isLt (Fin.lt_def.mp f.lo_lt_hi)
    rw [show 11 * (e.lo : ℕ) + (e.hi : ℕ) = e.key from rfl] at he
    rw [show 11 * (f.lo : ℕ) + (f.hi : ℕ) = f.key from rfl] at hf
    refine Edge11.key_injective ?_
    rw [← he, ← hf]
    exact congrArg (slice inv 7) h

@[simp] theorem codingOfTable_idx {tbl inv : ℕ} {hlt hinv} (e : Edge11) :
    (codingOfTable tbl inv hlt hinv).idx e = slice tbl 6 e.key := rfl

/-- The vertex-star masks of a tabulated numbering, checked over the `121`
keys, describe edge membership. -/
theorem star_spec_of_keys {tbl inv : ℕ} {hlt hinv} (star : ℕ → ℕ)
    (h : ∀ v < 11, ∀ a < 11, ∀ b < 11, a < b →
      (star v).testBit (slice tbl 6 (11 * a + b)) = decide (v = a ∨ v = b)) :
    ∀ (v : Fin 11) (e : Edge11),
      (star v.val).testBit ((codingOfTable tbl inv hlt hinv).idx e) =
        decide (v ∈ e.vertices) := by
  intro v e
  have hkey := h v.val v.isLt _ e.lo.isLt _ e.hi.isLt (Fin.lt_def.mp e.lo_lt_hi)
  simp only [codingOfTable_idx, Edge11.key]
  rw [hkey]
  refine decide_eq_decide.mpr ?_
  rw [Edge11.mem_vertices_iff, Fin.ext_iff, Fin.ext_iff]

/-! ### A cherry cover from tabulated masks -/

section Data

variable (c : EdgeCoding) (star memb col vmask : ℕ → ℕ)

/-- The number of common endpoints of two edges, read off the endpoint masks. -/
theorem vmeet_eq_popcount
    (hvm : ∀ (v : Fin 11) (e : Edge11),
      (vmask (c.idx e)).testBit v.val = decide (v ∈ e.vertices))
    (hlt : ∀ e : Edge11, vmask (c.idx e) < 2 ^ 11) (e f : Edge11) :
    Edge11.vmeet e f = popcount (vmask (c.idx e) &&& vmask (c.idx f)) := by
  classical
  rw [← card_filter_testBit (fun v : Fin 11 => v.val) 11 (fun v => v.isLt) Fin.val_injective
    (by simp) (Nat.and_lt_two_pow _ (hlt f))]
  refine congrArg Finset.card ?_
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter, Nat.testBit_and,
    Bool.and_eq_true, hvm, decide_eq_true_eq]

/-- The number of members of the listed cover containing two given edges, read
off the transposed member table. -/
theorem pairCount_eq_popcount
    (hcollt : ∀ k < 55, col k < 2 ^ 45)
    (hcol : ∀ k < 55, ∀ i < 45, (col k).testBit i = (memb i).testBit k) (e f : Edge11) :
    pairCount (fun i : Fin 45 => c.edgesOfMask (memb i.val)) e f =
      popcount (col (c.idx e) &&& col (c.idx f)) := by
  classical
  rw [← card_filter_testBit (fun i : Fin 45 => i.val) 45 (fun i => i.isLt) Fin.val_injective
    (by simp) (Nat.and_lt_two_pow _ (hcollt _ (c.idx_lt f)))]
  refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
  simp only [EdgeCoding.mem_edgesOfMask, Nat.testBit_and, Bool.and_eq_true,
    hcol _ (c.idx_lt e) _ i.isLt, hcol _ (c.idx_lt f) _ i.isLt]

/-- **The listed-data constructor.**  Forty-five member masks together with the
vertex-star masks, their transpose and the endpoint masks assemble into a
`SRG266.QuasiSymmetric.CherryCover` as soon as the two numerical identities
`h2reg` and `hpair` hold; both are `decide`-checkable. -/
def cherryCoverOfData
    (hstar : ∀ (v : Fin 11) (e : Edge11), (star v.val).testBit (c.idx e) = decide (v ∈ e.vertices))
    (hstarlt : ∀ v < 11, star v < 2 ^ 55)
    (hcollt : ∀ k < 55, col k < 2 ^ 45)
    (hvmasklt : ∀ k < 55, vmask k < 2 ^ 11)
    (hcol : ∀ k < 55, ∀ i < 45, (col k).testBit i = (memb i).testBit k)
    (hvmask : ∀ k < 55, ∀ v < 11, (vmask k).testBit v = (star v).testBit k)
    (h2reg : ∀ i < 45, ∀ v < 11, popcount (memb i &&& star v) = 2)
    (hpair : ∀ k < 55, ∀ l < 55,
      popcount (col k &&& col l) + popcount (vmask k &&& vmask l) =
        2 + if k = l then 9 else 0) :
    CherryCover where
  g i := c.edgesOfMask (memb i.val)
  two_regular := by
    classical
    intro i v
    have hset : ((c.edgesOfMask (memb i.val)).filter fun e => v ∈ e.vertices) =
        c.edgesOfMask (memb i.val &&& star v.val) := by
      ext e
      simp only [Finset.mem_filter, EdgeCoding.mem_edgesOfMask, Nat.testBit_and, Bool.and_eq_true,
        hstar v e, decide_eq_true_eq]
    rw [hset, c.card_edgesOfMask (Nat.and_lt_two_pow _ (hstarlt _ v.isLt)),
      h2reg _ i.isLt _ v.isLt]
  cherry_exact := by
    intro e f hef hvm
    have hvv : ∀ (v : Fin 11) (e : Edge11),
        (vmask (c.idx e)).testBit v.val = decide (v ∈ e.vertices) := by
      intro v e
      rw [hvmask _ (c.idx_lt e) _ v.isLt, hstar v e]
    have hmeet := vmeet_eq_popcount c vmask hvv (fun e => hvmasklt _ (c.idx_lt e)) e f
    have hp := hpair _ (c.idx_lt e) _ (c.idx_lt f)
    rw [if_neg (fun hcon => hef (c.idx_injective hcon))] at hp
    rw [pairCount_eq_popcount c memb col hcollt hcol e f]
    omega
  disjoint_twice := by
    intro e f hvm
    have hne : e ≠ f := by
      rintro rfl
      rw [Edge11.vmeet_self] at hvm
      exact absurd hvm (by norm_num)
    have hvv : ∀ (v : Fin 11) (e : Edge11),
        (vmask (c.idx e)).testBit v.val = decide (v ∈ e.vertices) := by
      intro v e
      rw [hvmask _ (c.idx_lt e) _ v.isLt, hstar v e]
    have hmeet := vmeet_eq_popcount c vmask hvv (fun e => hvmasklt _ (c.idx_lt e)) e f
    have hp := hpair _ (c.idx_lt e) _ (c.idx_lt f)
    rw [if_neg (fun hcon => hne (c.idx_injective hcon))] at hp
    rw [pairCount_eq_popcount c memb col hcollt hcol e f]
    omega

/-- The members of a cherry cover built from listed data are the edge sets of
its member masks. -/
@[simp] theorem cherryCoverOfData_g
    {hstar hstarlt hcollt hvmasklt hcol hvmask h2reg hpair} (i : Fin 45) :
    (cherryCoverOfData c star memb col vmask hstar hstarlt hcollt hvmasklt hcol hvmask
      h2reg hpair).g i = c.edgesOfMask (memb i.val) := rfl

end Data

end SRG266.QuasiSymmetric
