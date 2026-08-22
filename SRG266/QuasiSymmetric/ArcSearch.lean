/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.QuasiSymmetric.EdgeMask

/-!
# The cherry-local arc search and its clique refutation

This file proves the finite contradiction that kills a listed
`2-(45, 9, 2)` design.  The mathematics behind
it is already in place —

* `SRG266.QuasiSymmetric.residual_pairMult`: two distinct points lie on
  exactly `9 − t` common residual blocks, so a *cherry* (a pair of points on a
  single common derived block) carries exactly `8`;
* `SRG266.QuasiSymmetric.IsArc.arc_is_cubic_on_eight`: every
  residual block is a `{12; 3}`-arc of the cherry cover, hence a cubic graph on
  eight of the eleven vertices of `K₁₁`.

So it suffices, for **one** cherry `(e, f)` of each listed design, to enumerate
the arcs containing both `e` and `f` and to refute an `8`-clique in the graph
that joins two arcs meeting in exactly three edges.  Two residual blocks through
`e` and `f` already share those two edges, so their intersection cannot be
empty, hence has exactly three edges: the eight residual blocks *are* an
`8`-clique.

Both halves are kernel searches over natural-number bitmasks.  The enumeration
is `SRG266.Search.rowDFS`, the refutation is `SRG266.Search.cliqueDFS`, and this
file supplies the bridge:

* `SRG266.QuasiSymmetric.arcGuard` / `SRG266.QuasiSymmetric.arcAccept` — the
  pruning and acceptance predicates, built only from `SRG266.Search.atMost` and
  `SRG266.Search.zeroOrThree` so that no kernel step ever computes a population
  count;
* `SRG266.QuasiSymmetric.arcRowsOK` — a `decide`-checkable well-formedness test
  on the per-position row data, and
  `SRG266.QuasiSymmetric.arcMask_mem_rowDFS`, which turns it into search
  completeness;
* `SRG266.QuasiSymmetric.isEmpty_residual165_of_arcSearch` — the per-design
  contradiction, consuming exactly four generated facts: the row data is
  well-formed, the search returns a listed table of arcs, the adjacency table is
  the meet-three relation of those arcs, and the clique search fails.

The eight residual blocks are carried into the enumerated table by choice, each
to its own entry, so no index list and no injectivity certificate for the packed
arc table is needed.

`SRG266.QuasiSymmetric.Edge11.ofLt` and `SRG266.QuasiSymmetric.idx_ofLt` are the
small naming layer the generated certificates use to address the two edges of
the chosen cherry by their endpoints and to read off their positions.

## Main results

* `SRG266.QuasiSymmetric.arcMask_mem_rowDFS`
* `SRG266.QuasiSymmetric.arc_designMasks_meet`
* `SRG266.QuasiSymmetric.isEmpty_residual165_of_arcSearch`
-/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-! ### Bitmask helpers

The three facts the completeness argument needs about the window `t % 2 ^ n`:
it is a submask of `t`, a mask that fits inside the window is a submask of it as
soon as it is a submask of `t`, and intersecting with such a mask does not see
the truncation at all.
-/

/-- A submask is absorbed by conjunction. -/
theorem and_eq_self_of_submask {a b : ℕ} (h : Submask a b) : a &&& b = a := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and]
  rcases Bool.eq_false_or_eq_true (a.testBit i) with hi | hi
  · simp [hi, h i hi]
  · simp [hi]

/-- Conversely, absorption exhibits a submask. -/
theorem submask_of_and_eq_self {a b : ℕ} (h : a &&& b = a) : Submask a b := by
  intro i hi
  have := congrArg (fun x => Nat.testBit x i) h
  simp only [Nat.testBit_and, hi, Bool.true_and] at this
  exact this

/-- A set bit of a mask below `2 ^ n` sits inside the window. -/
theorem lt_of_testBit {a n i : ℕ} (h : a < 2 ^ n) (hi : a.testBit i = true) : i < n := by
  by_contra hcon
  have hlt : a < 2 ^ i :=
    lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
  rw [Nat.testBit_lt_two_pow hlt] at hi
  exact Bool.noConfusion hi

/-- Truncating to a window deletes bits. -/
theorem submask_mod_two_pow (t n : ℕ) : Submask (t % 2 ^ n) t := by
  intro i hi
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true] at hi
  exact hi.2

/-- A submask that fits inside the window survives truncation. -/
theorem submask_mod_two_pow_of_lt {a t n : ℕ} (ha : a < 2 ^ n) (h : Submask a t) :
    Submask a (t % 2 ^ n) := by
  intro i hi
  rw [Nat.testBit_mod_two_pow, Bool.and_eq_true]
  exact ⟨by simpa using lt_of_testBit ha hi, h i hi⟩

/-- Intersecting with a mask that fits inside the window ignores the
truncation. -/
theorem and_mod_two_pow {a t n : ℕ} (ha : a < 2 ^ n) : (t % 2 ^ n) &&& a = t &&& a := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and, Nat.testBit_and, Nat.testBit_mod_two_pow]
  rcases Bool.eq_false_or_eq_true (a.testBit i) with hi | hi
  · simp [hi, lt_of_testBit ha hi]
  · simp [hi]

/-! ### The pruning predicate -/

/-- Per-position data of the arc search: the seed bits that must already be
present at this position, the masks through this position that are still open,
and the masks whose last position this is.

A "mask" here is a member of the cherry cover or a vertex star of `K₁₁`; an arc
meets each of them in `0` or `3` edges. -/
abbrev ArcRow : Type := ℕ × List ℕ × List ℕ

/-- The pruning predicate of the arc search: the seed bits are present, at most
twelve edges have been chosen, every still-open mask carries at most three of
them, and every mask that closes here carries exactly `0` or `3`.

No branch computes a population count; `SRG266.Search.atMost` and
`SRG266.Search.zeroOrThree` compare against a bound directly. -/
def arcGuard (row : ArcRow) (m : ℕ) : Bool :=
  (row.1 &&& m == row.1) && atMost 12 m &&
    row.2.1.all (fun a => atMost 3 (m &&& a)) &&
    row.2.2.all (fun a => zeroOrThree (m &&& a))

/-- The acceptance predicate of the arc search: exactly twelve edges. -/
def arcAccept (m : ℕ) : Bool := atMost 12 m && !atMost 11 m

/-- **Well-formedness of the row data**, checked by `decide` in each generated
certificate.  At position `k` the seed bits recorded in the row are seed bits of
`s` lying inside the window `[0, k]`, every open mask is one of the listed
masks, and every closing mask is a listed mask that fits inside the window.

Nothing else about the rows matters: pruning power is a matter of speed, not of
soundness. -/
def arcRowsOK (s : ℕ) (masks : List ℕ) : ℕ → List ArcRow → Bool
  | _, [] => true
  | k, row :: rows =>
      (row.1 &&& s == row.1) && decide (row.1 < 2 ^ (k + 1)) &&
        row.2.1.all (fun a => masks.contains a) &&
        row.2.2.all (fun a => masks.contains a && decide (a < 2 ^ (k + 1))) &&
        arcRowsOK s masks (k + 1) rows

/-- Every prefix of an arc mask passes the test of the row that decides its last
position.  This is the hypothesis of `SRG266.Search.rowDFS_mem`. -/
theorem rowGuardChain_of_arcRowsOK {s t : ℕ} {masks : List ℕ}
    (hs : Submask s t) (hcap : popcount t ≤ 12)
    (hmasks : ∀ a ∈ masks, popcount (t &&& a) = 0 ∨ popcount (t &&& a) = 3) :
    ∀ (rows : List ArcRow) (k : ℕ), arcRowsOK s masks k rows = true →
      RowGuardChain arcGuard rows k t := by
  intro rows
  induction rows with
  | nil => intro _ _; trivial
  | cons row rows ih =>
      intro k hok
      rw [arcRowsOK] at hok
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true] at hok
      obtain ⟨⟨⟨⟨hseed, hwin⟩, hopen⟩, hclose⟩, hrest⟩ := hok
      refine ⟨?_, ih (k + 1) hrest⟩
      have hpt : Submask (t % 2 ^ (k + 1)) t := submask_mod_two_pow t (k + 1)
      have hrow : Submask row.1 (t % 2 ^ (k + 1)) :=
        submask_mod_two_pow_of_lt hwin ((submask_of_and_eq_self hseed).trans hs)
      have hforced : (row.1 &&& (t % 2 ^ (k + 1)) == row.1) = true := by
        rw [beq_iff_eq]
        exact and_eq_self_of_submask hrow
      have hcapp : atMost 12 (t % 2 ^ (k + 1)) = true :=
        atMost_eq_true_iff.2 (le_trans (popcount_mono hpt) hcap)
      have hopen' : (row.2.1.all fun a => atMost 3 (t % 2 ^ (k + 1) &&& a)) = true := by
        rw [List.all_eq_true]
        intro a ha
        have hmem : a ∈ masks := List.mem_of_elem_eq_true (by simpa using hopen a ha)
        have hsub : Submask (t % 2 ^ (k + 1) &&& a) (t &&& a) :=
          Submask.and hpt (Submask.refl a)
        have hle := popcount_mono hsub
        have := hmasks a hmem
        exact atMost_eq_true_iff.2 (by omega)
      have hclose' : (row.2.2.all fun a => zeroOrThree (t % 2 ^ (k + 1) &&& a)) = true := by
        rw [List.all_eq_true]
        intro a ha
        obtain ⟨hcontains, halt⟩ := by simpa [Bool.and_eq_true] using hclose a ha
        have hmem : a ∈ masks := List.mem_of_elem_eq_true (by simpa using hcontains)
        rw [and_mod_two_pow halt]
        exact zeroOrThree_of_card (hmasks a hmem)
      rw [arcGuard]
      simp only [Bool.and_eq_true]
      exact ⟨⟨⟨hforced, hcapp⟩, hopen'⟩, hclose'⟩

/-- **Completeness of the cherry-local arc search.**  A twelve-bit mask that
contains the seed and meets every listed mask in `0` or `3` bits is returned by
the search.  Combined with one `decide +kernel` evaluation of `rowDFS` this says
that the generated table of arcs is complete. -/
theorem arcMask_mem_rowDFS {s t : ℕ} {masks : List ℕ} {rows : List ArcRow}
    (hlen : rows.length = 55) (hok : arcRowsOK s masks 0 rows = true)
    (hs : Submask s t) (hlt : t < 2 ^ 55) (hcard : popcount t = 12)
    (hmasks : ∀ a ∈ masks, popcount (t &&& a) = 0 ∨ popcount (t &&& a) = 3) :
    t ∈ rowDFS arcGuard arcAccept rows 0 0 := by
  have hacc : arcAccept t = true := by
    rw [arcAccept, Bool.and_eq_true]
    refine ⟨atMost_eq_true_iff.2 (by omega), ?_⟩
    rcases Bool.eq_false_or_eq_true (atMost 11 t) with h | h
    · have := atMost_eq_true_iff.1 h
      omega
    · simp [h]
  have h := rowDFS_mem arcGuard arcAccept hacc rows 0
    (by rw [Nat.zero_add, hlen]; exact hlt)
    (rowGuardChain_of_arcRowsOK hs (le_of_eq hcard) hmasks rows 0 hok)
  simpa [Nat.mod_one] using h

/-! ### The listed masks of a design

An arc meets every member of the cherry cover, and every vertex star of `K₁₁`,
in `0` or `3` edges — the first by definition, the second by
`SRG266.QuasiSymmetric.IsArc.arc_degree_cases`.  Those `45 + 11` masks are the
only ones the pruning predicate is allowed to mention.
-/

/-- The `56` masks a listed design offers the search: its `45` members and the
`11` vertex stars of `K₁₁`. -/
def designMasks (memb star : ℕ → ℕ) : List ℕ :=
  (List.range 45).map memb ++ (List.range 11).map star

/-- **Every listed mask meets an arc in `0` or `3` edges.** -/
theorem arc_designMasks_meet {C : CherryCover} {c : EdgeCoding} {memb star : ℕ → ℕ}
    (hg : ∀ i : Fin 45, C.g i = c.edgesOfMask (memb i.val))
    (hmemblt : ∀ i < 45, memb i < 2 ^ 55)
    (hstar : ∀ (v : Fin 11) (e : Edge11),
      (star v.val).testBit (c.idx e) = decide (v ∈ e.vertices))
    (hstarlt : ∀ v < 11, star v < 2 ^ 55)
    {T : Finset Edge11} (hT : IsArc C T) :
    ∀ a ∈ designMasks memb star,
      popcount (c.maskOf T &&& a) = 0 ∨ popcount (c.maskOf T &&& a) = 3 := by
  classical
  intro a ha
  rcases List.mem_append.mp ha with h | h
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
    have hi' : i < 45 := List.mem_range.mp hi
    have hmask : c.maskOf (C.g ⟨i, hi'⟩) = memb i := by
      rw [hg ⟨i, hi'⟩]
      exact c.maskOf_edgesOfMask (hmemblt i hi')
    rw [← hmask, c.popcount_and_maskOf]
    exact hT.meet ⟨i, hi'⟩
  · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp h
    have hv' : v < 11 := List.mem_range.mp hv
    have hset : c.edgesOfMask (star v) = Edge11.star ⟨v, hv'⟩ := by
      ext x
      rw [EdgeCoding.mem_edgesOfMask, Edge11.mem_star, hstar ⟨v, hv'⟩ x]
      simp
    have hmask : c.maskOf (Edge11.star ⟨v, hv'⟩) = star v := by
      rw [← hset]
      exact c.maskOf_edgesOfMask (hstarlt v hv')
    have hfilter : T ∩ Edge11.star ⟨v, hv'⟩ =
        T.filter fun x => (⟨v, hv'⟩ : Fin 11) ∈ x.vertices := by
      ext x
      simp only [Finset.mem_inter, Finset.mem_filter, Edge11.mem_star]
    rw [← hmask, c.popcount_and_maskOf, hfilter]
    exact hT.arc_degree_cases ⟨v, hv'⟩

/-! ### Naming an edge by its endpoints

The generated certificates address the two edges of the chosen cherry by their
endpoints, and need their positions in the design's numbering as numerals.
-/

namespace Edge11

/-- The smaller endpoint of `mk' h` is the smaller of the two vertices. -/
theorem lo_mk' {a b : Fin 11} (hab : a < b) : (mk' hab.ne).lo = a := by
  have hv : (mk' hab.ne).vertices = {a, b} := vertices_mk' hab.ne
  refine le_antisymm (Finset.min'_le _ _ (by rw [hv]; simp)) ?_
  refine Finset.le_min' _ _ _ fun y hy => ?_
  rw [hv] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact le_rfl
  · exact hab.le

/-- The larger endpoint of `mk' h` is the larger of the two vertices. -/
theorem hi_mk' {a b : Fin 11} (hab : a < b) : (mk' hab.ne).hi = b := by
  have hv : (mk' hab.ne).vertices = {a, b} := vertices_mk' hab.ne
  refine le_antisymm (Finset.max'_le _ _ _ fun y hy => ?_)
    (Finset.le_max' _ _ (by rw [hv]; simp))
  rw [hv] at hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · exact hab.le
  · exact le_rfl

/-- The key of an edge named by its two ordered endpoints. -/
theorem key_mk' {a b : Fin 11} (hab : a < b) :
    (mk' hab.ne).key = 11 * (a : ℕ) + (b : ℕ) := by
  rw [key, lo_mk' hab, hi_mk' hab]

/-- The edge of `K₁₁` named by an ordered pair of distinct vertices. -/
def ofLt {a b : Fin 11} (hab : a < b) : Edge11 := mk' hab.ne

/-- The endpoints of an edge named by an ordered pair. -/
theorem vertices_ofLt {a b : Fin 11} (hab : a < b) : (ofLt hab).vertices = {a, b} :=
  vertices_mk' hab.ne

/-- The smaller named endpoint lies on the edge. -/
theorem lo_mem_ofLt {a b : Fin 11} (hab : a < b) : a ∈ (ofLt hab).vertices := by
  rw [vertices_ofLt]; simp

/-- The larger named endpoint lies on the edge. -/
theorem hi_mem_ofLt {a b : Fin 11} (hab : a < b) : b ∈ (ofLt hab).vertices := by
  rw [vertices_ofLt]; simp

/-- The key of an edge named by an ordered pair. -/
theorem key_ofLt {a b : Fin 11} (hab : a < b) :
    (ofLt hab).key = 11 * (a : ℕ) + (b : ℕ) := key_mk' hab

/-- Two edges with different keys are different. -/
theorem ofLt_ne {a b a' b' : Fin 11} (hab : a < b) (hab' : a' < b')
    (hkey : 11 * (a : ℕ) + (b : ℕ) ≠ 11 * (a' : ℕ) + (b' : ℕ)) : ofLt hab ≠ ofLt hab' := by
  intro heq
  exact hkey (by rw [← key_ofLt hab, ← key_ofLt hab', heq])

end Edge11

/-- The position of an edge named by an ordered pair of endpoints, in a
tabulated numbering.  This is what turns the chosen cherry of a listed design
into the two numerals the generated row data is seeded with. -/
theorem idx_ofLt {tbl inv : ℕ} {hlt hinv} {a b : Fin 11} (hab : a < b) :
    (codingOfTable tbl inv hlt hinv).idx (Edge11.ofLt hab) =
      slice tbl 6 (11 * (a : ℕ) + (b : ℕ)) := by
  rw [codingOfTable_idx, Edge11.key_ofLt]

/-! ### The per-design contradiction -/

/-- A listed cherry cover with a cherry whose arcs carry no
`8`-clique has no residual structure, so no quasi-symmetric `2-(56, 12, 9)`
design has it as a point-derived design.

The five hypotheses beyond the design data are exactly the generated
certificates: `hok` says the row data mentions only the design's own masks and
respects the windows, `hdfs` is the kernel arc enumeration, `hadj` is the
adjacency table of the enumerated arcs, and `hclique` is the failed `8`-clique
search. -/
theorem isEmpty_residual165_of_arcSearch
    {C : CherryCover} {c : EdgeCoding} {memb star : ℕ → ℕ}
    (hg : ∀ i : Fin 45, C.g i = c.edgesOfMask (memb i.val))
    (hmemblt : ∀ i < 45, memb i < 2 ^ 55)
    (hstar : ∀ (v : Fin 11) (e : Edge11),
      (star v.val).testBit (c.idx e) = decide (v ∈ e.vertices))
    (hstarlt : ∀ v < 11, star v < 2 ^ 55)
    {e f : Edge11} (hef : e ≠ f) (hvm : Edge11.vmeet e f = 1)
    {rows : List ArcRow} (hlen : rows.length = 55)
    (hok : arcRowsOK (2 ^ c.idx e ||| 2 ^ c.idx f) (designMasks memb star) 0 rows = true)
    {N arcT adjT : ℕ}
    (hdfs : rowDFS arcGuard arcAccept rows 0 0 = (List.range N).map (slice arcT 55))
    (hadj : ∀ k < N, ∀ l < N,
      (slice adjT N k).testBit l =
        decide (popcount (slice arcT 55 k &&& slice arcT 55 l) = 3))
    (hclique : cliqueDFS (slice adjT N) N 8 = false) :
    IsEmpty (Residual165 C.toDerived45) := by
  classical
  refine ⟨fun R => ?_⟩
  -- the eight residual blocks through the cherry
  have hE : C.toDerived45.pairMult e f = 1 := C.cherry_exact e f hef hvm
  have hR : R.pairMult e f = 8 := by
    rw [residual_pairMult R hef, hE]
  set S : Finset (Fin 165) :=
    Finset.univ.filter (fun n => e ∈ R.res n ∧ f ∈ R.res n) with hSdef
  have hScard : S.card = 8 := hR
  have hmemS : ∀ n ∈ S, e ∈ R.res n ∧ f ∈ R.res n := by
    intro n hn
    simpa [hSdef] using hn
  -- every residual block is an arc of the cover
  have harc : ∀ n : Fin 165, IsArc C (R.res n) := by
    intro n
    refine ⟨R.res_card n, fun i => ?_⟩
    have h := R.cross_meet i n
    rwa [Finset.inter_comm] at h
  -- each of them is listed in the enumerated table
  have hkey : ∀ n : Fin 165, ∃ k,
      n ∈ S → k < N ∧ slice arcT 55 k = c.maskOf (R.res n) := by
    intro n
    by_cases hn : n ∈ S
    · obtain ⟨he, hf⟩ := hmemS n hn
      have hs : Submask (2 ^ c.idx e ||| 2 ^ c.idx f) (c.maskOf (R.res n)) := by
        intro i hi
        rw [Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, Nat.testBit_two_pow,
          decide_eq_true_eq, decide_eq_true_eq] at hi
        rw [c.testBit_maskOf]
        rcases hi with h | h
        · exact ⟨e, he, h⟩
        · exact ⟨f, hf, h⟩
      have hmem := arcMask_mem_rowDFS hlen hok hs (c.maskOf_lt _)
        (by rw [c.popcount_maskOf, R.res_card n])
        (arc_designMasks_meet hg hmemblt hstar hstarlt (harc n))
      rw [hdfs] at hmem
      obtain ⟨k, hk, hkeq⟩ := List.mem_map.mp hmem
      exact ⟨k, fun _ => ⟨List.mem_range.mp hk, hkeq⟩⟩
    · exact ⟨0, fun h => absurd h hn⟩
  choose φ hφ using hkey
  -- the images of the eight residual blocks form an eight-clique
  have hinjOn : Set.InjOn φ S := by
    intro m hm n hn hmn
    have h1 := (hφ m hm).2
    have h2 := (hφ n hn).2
    rw [hmn, h2] at h1
    exact R.res_inj (c.maskOf_injective h1.symm)
  refine cliqueDFS_sound hclique (S := S.image φ) ?_ ?_ ?_
  · rw [Finset.card_image_of_injOn hinjOn, hScard]
  · intro x hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hx
    exact (hφ n hn).1
  · intro x hx y hy hxy
    obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hy
    have hmn : m ≠ n := fun h => hxy (by rw [h])
    have hmeet : (R.res m ∩ R.res n).card = 3 := by
      obtain ⟨hem, hfm⟩ := hmemS m hm
      obtain ⟨hen, hfn⟩ := hmemS n hn
      have hsub : ({e, f} : Finset Edge11) ⊆ R.res m ∩ R.res n := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact Finset.mem_inter.mpr ⟨hem, hen⟩
        · exact Finset.mem_inter.mpr ⟨hfm, hfn⟩
      have hpair : ({e, f} : Finset Edge11).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hef), Finset.card_singleton]
      have hge : 2 ≤ (R.res m ∩ R.res n).card := by
        rw [← hpair]
        exact Finset.card_le_card hsub
      rcases R.res_meet m n hmn with h | h <;> omega
    have hpc : popcount (slice arcT 55 (φ m) &&& slice arcT 55 (φ n)) = 3 := by
      rw [(hφ m hm).2, (hφ n hn).2, c.popcount_and_maskOf, hmeet]
    rw [hadj _ (hφ m hm).1 _ (hφ n hn).1, hpc]
    simp

end SRG266.QuasiSymmetric
