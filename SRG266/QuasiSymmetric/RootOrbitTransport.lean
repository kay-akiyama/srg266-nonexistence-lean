/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.QuasiSymmetric.RootedSearchNormalization
import SRG266.QuasiSymmetric.RootOrbitCoordinates

/-!
# Transport from compact rooted orbit coordinates

The SAT certificates act on the eight vertices outside the fixed root, while
the mathematical normalization theorem acts on `Fin 11`.  This module builds
the actual permutation fixing `{0,1,2}` and proves the coordinate bridge.
-/

namespace SRG266.QuasiSymmetric

/-- Add the three fixed root vertices to a compact vertex coordinate. -/
def shiftRootVertex (v : Fin 8) : Fin 11 :=
  ⟨v.val + 3, by omega⟩

@[simp] theorem shiftRootVertex_val (v : Fin 8) :
    (shiftRootVertex v).val = v.val + 3 := rfl

theorem shiftRootVertex_not_mem_fixedRoot012 (v : Fin 8) :
    shiftRootVertex v ∉ fixedRoot012 := by
  rw [fixedRoot012]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> intro h
  all_goals have hval := congrArg Fin.val h
  all_goals simp [shiftRootVertex] at hval

/-- The eight vertices outside the fixed root, in consecutive coordinates. -/
def fixedRootComplementEquiv8 :
    {v : Fin 11 // v ∉ fixedRoot012} ≃ Fin 8 where
  toFun v := ⟨v.1.val - 3, by
    have hge : 3 ≤ v.1.val := by
      by_contra hnot
      have hlt : v.1.val < 3 := Nat.lt_of_not_ge hnot
      have hv := v.2
      interval_cases hvalue : v.1.val <;>
        simp [fixedRoot012, Fin.ext_iff, hvalue] at hv
    omega⟩
  invFun v := ⟨shiftRootVertex v, shiftRootVertex_not_mem_fixedRoot012 v⟩
  left_inv v := by
    apply Subtype.ext
    apply Fin.ext
    dsimp [shiftRootVertex]
    have hge : 3 ≤ v.1.val := by
      by_contra hnot
      have hlt : v.1.val < 3 := Nat.lt_of_not_ge hnot
      have hv := v.2
      interval_cases hvalue : v.1.val <;>
        simp [fixedRoot012, Fin.ext_iff, hvalue] at hv
    omega
  right_inv v := by
    apply Fin.ext
    simp [shiftRootVertex]

/-- Extend a checked packed permutation by the identity on the fixed root. -/
def packedPerm11Equiv (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) : Equiv.Perm (Fin 11) :=
  extendOff fixedRoot012 <|
    fixedRootComplementEquiv8.trans <|
      (packedPerm8Equiv permutationCode hperm).trans
      fixedRootComplementEquiv8.symm

/-- A total, computable interpretation of a packed code.  Invalid codes use
the identity; checked witnesses always enter the valid branch. -/
def packedPerm11OfCode (permutationCode : ℕ) : Equiv.Perm (Fin 11) :=
  if hperm : PackedPerm8OK permutationCode then
    packedPerm11Equiv permutationCode hperm
  else Equiv.refl _

theorem packedPerm11OfCode_eq (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    packedPerm11OfCode permutationCode =
      packedPerm11Equiv permutationCode hperm := by
  simp [packedPerm11OfCode, hperm]

@[simp] theorem packedPerm11Equiv_fixes_root (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    fixedRoot012.image (packedPerm11Equiv permutationCode hperm) =
      fixedRoot012 := by
  exact image_extendOff _ _

theorem packedPerm11Equiv_apply_shift (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (v : Fin 8) :
    packedPerm11Equiv permutationCode hperm (shiftRootVertex v) =
      shiftRootVertex (packedPerm8Equiv permutationCode hperm v) := by
  rw [packedPerm11Equiv, extendOff_apply_of_notMem _
    (shiftRootVertex_not_mem_fixedRoot012 v)]
  rfl

/-! ## Packing inverse permutations -/

/-- Pack a genuine permutation into the eight base-eight fields used by the
certificate format. -/
def packPerm8 (π : Equiv.Perm (Fin 8)) : ℕ :=
  Nat.ofDigits 8 (List.ofFn fun v : Fin 8 => (π v).val)

theorem slice_packPerm8 (π : Equiv.Perm (Fin 8)) (i : Fin 8) :
    slice (packPerm8 π) 3 i.val = (π i).val := by
  rw [slice, packPerm8, Nat.shiftRight_eq_div_pow,
    show 2 ^ (3 * i.val) = 8 ^ i.val by norm_num [Nat.pow_mul],
    Nat.ofDigits_div_pow_eq_ofDigits_drop i.val (by norm_num)]
  · rw [Nat.and_two_pow_sub_one_eq_mod, show 2 ^ 3 = 8 by norm_num,
      Nat.ofDigits_mod_eq_head!, List.head!_eq_head?_getD,
      List.head?_drop,
      List.getElem?_eq_getElem (l := List.ofFn fun v : Fin 8 => (π v).val)
        (i := i.val) (by simp), List.getElem_ofFn]
    simp
  · intro digit hdigit
    rw [List.mem_ofFn] at hdigit
    obtain ⟨j, rfl⟩ := hdigit
    exact (π j).isLt

theorem packedPerm8OK_packPerm8 (π : Equiv.Perm (Fin 8)) :
    PackedPerm8OK (packPerm8 π) := by
  constructor
  · rw [List.all_eq_true]
    intro i hi
    rw [decide_eq_true_eq]
    let v : Fin 8 := ⟨i, List.mem_range.mp hi⟩
    change slice (packPerm8 π) 3 v.val < 8
    rw [slice_packPerm8]
    exact (π v).isLt
  · apply List.Nodup.map_on _ List.nodup_range
    intro i hi j hj hij
    let vi : Fin 8 := ⟨i, List.mem_range.mp hi⟩
    let vj : Fin 8 := ⟨j, List.mem_range.mp hj⟩
    have hp : π vi = π vj := by
      apply Fin.ext
      change slice (packPerm8 π) 3 vi.val =
        slice (packPerm8 π) 3 vj.val at hij
      rw [slice_packPerm8 π vi, slice_packPerm8 π vj] at hij
      exact hij
    exact congrArg Fin.val (π.injective hp)

theorem packedPerm8Equiv_packPerm8 (π : Equiv.Perm (Fin 8)) :
    packedPerm8Equiv (packPerm8 π) (packedPerm8OK_packPerm8 π) = π := by
  ext i
  exact slice_packPerm8 π i

/-- Packed code of the inverse of a checked certificate permutation. -/
def inversePackedPerm8Code (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) : ℕ :=
  packPerm8 (packedPerm8Equiv permutationCode hperm).symm

theorem inversePackedPerm8Code_OK (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    PackedPerm8OK (inversePackedPerm8Code permutationCode hperm) :=
  packedPerm8OK_packPerm8 _

theorem packedPerm8Equiv_inverseCode (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    packedPerm8Equiv (inversePackedPerm8Code permutationCode hperm)
        (inversePackedPerm8Code_OK permutationCode hperm) =
      (packedPerm8Equiv permutationCode hperm).symm :=
  packedPerm8Equiv_packPerm8 _

theorem packedPerm11Equiv_inverseCode (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    packedPerm11Equiv (inversePackedPerm8Code permutationCode hperm)
        (inversePackedPerm8Code_OK permutationCode hperm) =
      (packedPerm11Equiv permutationCode hperm).symm := by
  apply Equiv.ext
  intro x
  by_cases hx : x ∈ fixedRoot012
  · apply (packedPerm11Equiv permutationCode hperm).injective
    simp [packedPerm11Equiv, extendOff_apply_of_mem, hx]
  · let πinv : Equiv.Perm {v : Fin 11 // v ∉ fixedRoot012} :=
      fixedRootComplementEquiv8.trans <|
        (packedPerm8Equiv
          (inversePackedPerm8Code permutationCode hperm)
          (inversePackedPerm8Code_OK permutationCode hperm)).trans
            fixedRootComplementEquiv8.symm
    have htau :
        packedPerm11Equiv (inversePackedPerm8Code permutationCode hperm)
            (inversePackedPerm8Code_OK permutationCode hperm) x =
          πinv ⟨x, hx⟩ := by
      exact extendOff_apply_of_notMem πinv hx
    rw [htau]
    apply (packedPerm11Equiv permutationCode hperm).injective
    rw [(packedPerm11Equiv permutationCode hperm).apply_symm_apply]
    rw [packedPerm11Equiv,
      extendOff_apply_of_notMem _ (πinv ⟨x, hx⟩).property]
    change fixedRootComplementEquiv8.symm
        (packedPerm8Equiv permutationCode hperm
          (packedPerm8Equiv
            (inversePackedPerm8Code permutationCode hperm)
            (inversePackedPerm8Code_OK permutationCode hperm)
            (fixedRootComplementEquiv8 ⟨x, hx⟩))) = x
    rw [packedPerm8Equiv_inverseCode]
    simp

/-! ## Characteristic masks on the eight compact vertices -/

/-- Decode the low eight bits as compact vertices. -/
def vertices8OfMask (mask : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter fun v => mask.testBit v.val

@[simp] theorem mem_vertices8OfMask (mask : ℕ) (v : Fin 8) :
    v ∈ vertices8OfMask mask ↔ mask.testBit v.val = true := by
  simp [vertices8OfMask]

/-- Encode compact vertices by their characteristic bits. -/
def vertexMask8 (S : Finset (Fin 8)) : ℕ :=
  S.fold (· ||| ·) 0 fun v => 2 ^ v.val

theorem vertexMask8_insert {v : Fin 8} {S : Finset (Fin 8)} (hv : v ∉ S) :
    vertexMask8 (insert v S) = 2 ^ v.val ||| vertexMask8 S := by
  classical
  rw [vertexMask8, vertexMask8, Finset.fold_insert hv]

theorem testBit_vertexMask8 (S : Finset (Fin 8)) (k : ℕ) :
    (vertexMask8 S).testBit k = true ↔ ∃ v ∈ S, v.val = k := by
  classical
  induction S using Finset.induction with
  | empty => simp [vertexMask8]
  | @insert v S hv ih =>
      rw [vertexMask8_insert hv,
        Nat.testBit_or, Bool.or_eq_true, Nat.testBit_two_pow, ih]
      constructor
      · rintro (h | ⟨w, hw, rfl⟩)
        · exact ⟨v, Finset.mem_insert_self _ _, by simpa using h⟩
        · exact ⟨w, Finset.mem_insert_of_mem hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact Or.inl (by simp)
        · exact Or.inr ⟨w, hw, rfl⟩

theorem vertexMask8_lt (S : Finset (Fin 8)) : vertexMask8 S < 2 ^ 8 := by
  classical
  induction S using Finset.induction with
  | empty => simp [vertexMask8]
  | @insert v S hv ih =>
      rw [vertexMask8_insert hv]
      exact Nat.or_lt_two_pow
        (Nat.pow_lt_pow_right (by omega) v.isLt) ih

@[simp] theorem vertices8OfMask_vertexMask8 (S : Finset (Fin 8)) :
    vertices8OfMask (vertexMask8 S) = S := by
  ext v
  rw [mem_vertices8OfMask, testBit_vertexMask8]
  constructor
  · rintro ⟨w, hw, hval⟩
    exact Fin.val_injective hval ▸ hw
  · intro hv
    exact ⟨v, hv, rfl⟩

theorem vertexMask8_vertices8OfMask {mask : ℕ} (hlt : mask < 2 ^ 8) :
    vertexMask8 (vertices8OfMask mask) = mask := by
  apply Nat.eq_of_testBit_eq
  intro k
  apply Bool.eq_iff_iff.mpr
  rw [testBit_vertexMask8]
  constructor
  · rintro ⟨v, hv, rfl⟩
    simpa using hv
  · intro hbit
    have hk : k < 8 := by
      by_contra hnot
      have hpow : 2 ^ 8 ≤ 2 ^ k :=
        Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hnot)
      have := Nat.testBit_lt_two_pow (lt_of_lt_of_le hlt hpow)
      rw [this] at hbit
      exact Bool.noConfusion hbit
    exact ⟨⟨k, hk⟩, by simpa, rfl⟩

theorem testBit_relabelVertexCode8_iff {permutationCode vertexCode output : ℕ} :
    (relabelVertexCode8 permutationCode vertexCode).testBit output = true ↔
      ∃ input < 8, vertexCode.testBit input = true ∧
        packedVertexImage permutationCode input = output := by
  rw [relabelVertexCode8, SRG266.Search.testBit_itemPositionsMask_iff,
    List.mem_map]
  constructor
  · rintro ⟨input, hinput, rfl⟩
    rw [List.mem_filter] at hinput
    exact ⟨input, List.mem_range.mp hinput.1, hinput.2, rfl⟩
  · rintro ⟨input, hlt, hbit, rfl⟩
    exact ⟨input, List.mem_filter.mpr
      ⟨List.mem_range.mpr hlt, hbit⟩, rfl⟩

theorem relabelVertexCode8_eq_vertexMask8_image
    (permutationCode vertexCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    relabelVertexCode8 permutationCode vertexCode =
      vertexMask8 ((vertices8OfMask vertexCode).image
        (packedPerm8Equiv permutationCode hperm)) := by
  apply Nat.eq_of_testBit_eq
  intro output
  apply Bool.eq_iff_iff.mpr
  rw [testBit_relabelVertexCode8_iff, testBit_vertexMask8]
  constructor
  · rintro ⟨input, hinput, hbit, himage⟩
    let v : Fin 8 := ⟨input, hinput⟩
    refine ⟨packedPerm8Equiv permutationCode hperm v, ?_, ?_⟩
    · rw [Finset.mem_image]
      exact ⟨v, by simpa [v] using hbit, rfl⟩
    · simpa [v] using himage
  · rintro ⟨v, hv, hval⟩
    rw [Finset.mem_image] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    refine ⟨u.val, u.isLt, by simpa using hu, ?_⟩
    simpa using hval

theorem triple8Code_lt : ∀ i : Fin 56, triple8Codes[i.val] < 2 ^ 8 := by
  decide +kernel

theorem edge8Code_lt : ∀ i : Fin 28, edge8Codes[i.val] < 2 ^ 8 := by
  decide +kernel

theorem vertices8Of_triple8Code_card (i : Fin 56) :
    (vertices8OfMask triple8Codes[i.val]).card = 3 := by
  decide +kernel +revert

theorem triple8Codes_complete (S : Finset (Fin 8)) (hcard : S.card = 3) :
    vertexMask8 S ∈ triple8Codes := by
  revert S
  decide +kernel

theorem vertices8Of_edge8Code_card (i : Fin 28) :
    (vertices8OfMask edge8Codes[i.val]).card = 2 := by
  decide +kernel +revert

theorem edge8Codes_complete (S : Finset (Fin 8)) (hcard : S.card = 2) :
    vertexMask8 S ∈ edge8Codes := by
  revert S
  decide +kernel

theorem relabelVertexCode8_triple_mem (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 56) :
    relabelVertexCode8 permutationCode triple8Codes[i.val] ∈ triple8Codes := by
  rw [relabelVertexCode8_eq_vertexMask8_image permutationCode _ hperm]
  apply triple8Codes_complete
  rw [Finset.card_image_of_injective _
    (packedPerm8Equiv permutationCode hperm).injective]
  exact vertices8Of_triple8Code_card i

theorem relabelVertexCode8_edge_mem (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 28) :
    relabelVertexCode8 permutationCode edge8Codes[i.val] ∈ edge8Codes := by
  rw [relabelVertexCode8_eq_vertexMask8_image permutationCode _ hperm]
  apply edge8Codes_complete
  rw [Finset.card_image_of_injective _
    (packedPerm8Equiv permutationCode hperm).injective]
  exact vertices8Of_edge8Code_card i

/-- Reindex a compact triple after applying a checked permutation. -/
def relabelTripleIndex8 (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 56) : Fin 56 :=
  ⟨triple8Codes.idxOf
      (relabelVertexCode8 permutationCode triple8Codes[i.val]),
    by
      have hlt : triple8Codes.idxOf
          (relabelVertexCode8 permutationCode triple8Codes[i.val]) <
          triple8Codes.length := List.idxOf_lt_length_iff.mpr
            (relabelVertexCode8_triple_mem permutationCode hperm i)
      simpa [length_triple8Codes] using hlt⟩

theorem triple8Code_relabelTripleIndex8 (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 56) :
    triple8Codes[(relabelTripleIndex8 permutationCode hperm i).val] =
      relabelVertexCode8 permutationCode triple8Codes[i.val] := by
  exact List.getElem_idxOf
    (relabelTripleIndex8 permutationCode hperm i).isLt

theorem testBit_relabelTripleMask8_iff (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) (j : Fin 56) :
    (relabelTripleMask8 permutationCode mask).testBit j.val = true ↔
      ∃ i : Fin 56, mask.testBit i.val = true ∧
        relabelTripleIndex8 permutationCode hperm i = j := by
  rw [relabelTripleMask8, relabelIndexedMask8,
    SRG266.Search.testBit_itemPositionsMask_iff]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨entry, ⟨hentry, hbit⟩, hindex⟩
    have hzip := List.mem_zipIdx hentry
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hzip
    have hi : entry.2 < 56 := by
      simpa [length_triple8Codes] using hzip.1
    let i : Fin 56 := ⟨entry.2, hi⟩
    refine ⟨i, by simpa [i] using hbit, ?_⟩
    apply Fin.ext
    change triple8Codes.idxOf
        (relabelVertexCode8 permutationCode triple8Codes[i.val]) = j.val
    have hcode : entry.1 = triple8Codes[i.val] := by
      convert hzip.2
    simpa [hcode] using hindex
  · rintro ⟨i, hbit, hindex⟩
    let entry : ℕ × ℕ := (triple8Codes[i.val], i.val)
    have hentry : entry ∈ triple8Codes.zipIdx := by
      rw [List.mem_iff_getElem]
      refine ⟨i.val, ?_, ?_⟩
      · simp [length_triple8Codes]
      simp [entry, List.getElem_zipIdx]
    refine ⟨entry, ⟨hentry, by simpa [entry]⟩, ?_⟩
    change triple8Codes.idxOf
      (relabelVertexCode8 permutationCode triple8Codes[i.val]) = j.val
    exact congrArg Fin.val hindex

/-! ## The compact triple dictionary as a mathematical family -/

/-- The mathematical off-root triple at compact position `i`. -/
def rootTripleAt (i : Fin 56) : Finset (Fin 11) :=
  verticesOfMask (8 * triple8Codes[i.val])

theorem rootTripleCode_lt : ∀ i : Fin 56,
    8 * triple8Codes[i.val] < 2 ^ 11 := by
  decide +kernel

theorem rootNearCompressedCode_at (i : Fin 56) :
    rootNearCompressedCodes[i.val] = 8 * triple8Codes[i.val] := by
  decide +kernel +revert

@[simp] theorem vertexMask_rootTripleAt (i : Fin 56) :
    vertexMask (rootTripleAt i) = 8 * triple8Codes[i.val] := by
  exact vertexMask_verticesOfMask (rootTripleCode_lt i)

theorem rootTripleAt_mem_triples (i : Fin 56) : rootTripleAt i ∈ triples := by
  decide +kernel +revert

theorem rootTripleAt_injective : Function.Injective rootTripleAt := by
  intro i j hij
  apply Fin.ext
  have hcodes : triple8Codes[i.val] = triple8Codes[j.val] := by
    have hmasks := congrArg vertexMask hij
    simp only [vertexMask_rootTripleAt] at hmasks
    omega
  have hi : i.val < triple8Codes.length := by
    rw [length_triple8Codes]
    exact i.isLt
  have hj : j.val < triple8Codes.length := by
    rw [length_triple8Codes]
    exact j.isLt
  exact (List.Nodup.getElem_inj_iff nodup_triple8Codes).mp hcodes

theorem rootTripleAt_eq_image_shift (i : Fin 56) :
    rootTripleAt i =
      (vertices8OfMask triple8Codes[i.val]).image shiftRootVertex := by
  decide +kernel +revert

theorem rootTripleAt_image_packed (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 56) :
    (rootTripleAt i).image (packedPerm11Equiv permutationCode hperm) =
      rootTripleAt (relabelTripleIndex8 permutationCode hperm i) := by
  rw [rootTripleAt_eq_image_shift, rootTripleAt_eq_image_shift]
  have hvertices :
      vertices8OfMask
          triple8Codes[(relabelTripleIndex8 permutationCode hperm i).val] =
        (vertices8OfMask triple8Codes[i.val]).image
          (packedPerm8Equiv permutationCode hperm) := by
    rw [triple8Code_relabelTripleIndex8]
    rw [relabelVertexCode8_eq_vertexMask8_image permutationCode _ hperm]
    exact vertices8OfMask_vertexMask8 _
  rw [hvertices, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  simp only [Function.comp_apply]
  exact packedPerm11Equiv_apply_shift permutationCode hperm v

/-- Decode the selected compact triple indices as an ordinary family on
`Fin 11`. -/
def rootTripleFamily8 (mask : ℕ) : Finset (Finset (Fin 11)) :=
  (Finset.univ.filter fun i : Fin 56 => mask.testBit i.val).image rootTripleAt

theorem rootTripleFamily8_closed (mask : ℕ) :
    ∀ U ∈ rootTripleFamily8 mask, U ∈ triples := by
  intro U hU
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hU
  exact rootTripleAt_mem_triples i

theorem rootTripleFamily8_relabel (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    rootTripleFamily8 (relabelTripleMask8 permutationCode mask) =
      (rootTripleFamily8 mask).image fun U =>
        U.image (packedPerm11Equiv permutationCode hperm) := by
  ext U
  constructor
  · intro hU
    obtain ⟨j, hj, hUj⟩ := Finset.mem_image.mp hU
    have hjbit : (relabelTripleMask8 permutationCode mask).testBit j.val =
        true := by simpa [rootTripleFamily8] using hj
    obtain ⟨i, hibit, hij⟩ :=
      (testBit_relabelTripleMask8_iff permutationCode mask hperm j).mp hjbit
    rw [Finset.mem_image]
    refine ⟨rootTripleAt i, ?_, ?_⟩
    · rw [rootTripleFamily8, Finset.mem_image]
      exact ⟨i, by simp [hibit], rfl⟩
    · calc
        (rootTripleAt i).image (packedPerm11Equiv permutationCode hperm) =
            rootTripleAt (relabelTripleIndex8 permutationCode hperm i) :=
          rootTripleAt_image_packed permutationCode hperm i
        _ = rootTripleAt j := congrArg rootTripleAt hij
        _ = U := hUj
  · intro hU
    obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hU
    obtain ⟨i, hi, hVi⟩ := Finset.mem_image.mp hV
    have hibit : mask.testBit i.val = true := by
      simpa [rootTripleFamily8] using hi
    subst V
    let j := relabelTripleIndex8 permutationCode hperm i
    rw [← hVU, rootTripleAt_image_packed]
    rw [rootTripleFamily8, Finset.mem_image]
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (testBit_relabelTripleMask8_iff permutationCode mask hperm j).mpr
      ⟨i, hibit, rfl⟩

/-- Expanding the 56 consecutive bits is exactly encoding the corresponding
mathematical triple family. -/
theorem expandRootNearMask_eq_vertexFamilyMask_rootTripleFamily8
    (mask : ℕ) :
    expandRootNearMask mask = vertexFamilyMask (rootTripleFamily8 mask) := by
  apply Nat.eq_of_testBit_eq
  intro code
  apply Bool.eq_iff_iff.mpr
  rw [expandRootNearMask, testBit_expandPositionMask,
    testBit_vertexFamilyMask]
  constructor
  · rintro ⟨index, hentry, hbit⟩
    have hzip := List.mem_zipIdx hentry
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hzip
    have hindex : index < 56 := by
      simpa [length_rootNearCompressedCodes] using hzip.1
    let i : Fin 56 := ⟨index, hindex⟩
    refine ⟨rootTripleAt i, ?_, ?_⟩
    · rw [rootTripleFamily8, Finset.mem_image]
      exact ⟨i, by simp [hbit, i], rfl⟩
    · rw [vertexMask_rootTripleAt]
      have hcodeEntry := hzip.2
      calc
        8 * triple8Codes[i.val] = rootNearCompressedCodes[i.val] := by
          exact (rootNearCompressedCode_at i).symm
        _ = code := by
          convert hcodeEntry.symm
  · rintro ⟨U, hU, hcode⟩
    rw [rootTripleFamily8, Finset.mem_image] at hU
    obtain ⟨i, hi, rfl⟩ := hU
    have hbit : mask.testBit i.val = true := by simpa using hi
    have hentry : (8 * triple8Codes[i.val], i.val) ∈
        rootNearCompressedCodes.zipIdx := by
      rw [rootNearCompressedCodes_eq]
      rw [List.mem_iff_getElem]
      refine ⟨i.val, ?_, ?_⟩
      · simp [length_triple8Codes]
      simp [List.getElem_zipIdx]
    refine ⟨i.val, ?_, hbit⟩
    rw [vertexMask_rootTripleAt] at hcode
    simpa [hcode] using hentry

theorem tripleFamilyOfMask_expandRootNearMask {mask : ℕ}
    :
    tripleFamilyOfMask (expandRootNearMask mask) = rootTripleFamily8 mask := by
  rw [expandRootNearMask_eq_vertexFamilyMask_rootTripleFamily8]
  exact tripleFamilyOfMask_vertexFamilyMask (rootTripleFamily8_closed mask)

/-- The compact certificate action is exactly mathematical relabelling of the
expanded triple family. -/
theorem relabelTripleFamilyMask_expandRootNearMask (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    relabelTripleFamilyMask (packedPerm11Equiv permutationCode hperm)
        (expandRootNearMask mask) =
      expandRootNearMask (relabelTripleMask8 permutationCode mask) := by
  rw [relabelTripleFamilyMask, tripleFamilyOfMask_expandRootNearMask,
    ← rootTripleFamily8_relabel]
  exact (expandRootNearMask_eq_vertexFamilyMask_rootTripleFamily8 _).symm

theorem relabelTripleFamilyMask_trans (σ τ : Equiv.Perm (Fin 11))
    (familyMask : ℕ) :
    relabelTripleFamilyMask (σ.trans τ) familyMask =
      relabelTripleFamilyMask τ
        (relabelTripleFamilyMask σ familyMask) := by
  unfold relabelTripleFamilyMask
  rw [tripleFamilyOfMask_vertexFamilyMask]
  · rw [Finset.image_image]
    apply congrArg vertexFamilyMask
    apply Finset.image_congr
    intro U hU
    change U.image (σ.trans τ) = (U.image σ).image τ
    rw [Finset.image_image]
    rfl
  · intro U hU
    obtain ⟨V, hV, rfl⟩ := Finset.mem_image.mp hU
    exact mem_triples_image (σ := σ)
      (Finset.mem_filter.mp hV).1

/-! ## The compact pair dictionary -/

/-- The mathematical off-root pair at compact position `i`. -/
def rootPairAt (i : Fin 28) : Finset (Fin 11) :=
  verticesOfMask (8 * edge8Codes[i.val])

theorem rootPairCode_lt : ∀ i : Fin 28,
    8 * edge8Codes[i.val] < 2 ^ 11 := by
  decide +kernel

@[simp] theorem vertexMask_rootPairAt (i : Fin 28) :
    vertexMask (rootPairAt i) = 8 * edge8Codes[i.val] := by
  exact vertexMask_verticesOfMask (rootPairCode_lt i)

theorem rootPairAt_card (i : Fin 28) : (rootPairAt i).card = 2 := by
  decide +kernel +revert

theorem rootPairAt_injective : Function.Injective rootPairAt := by
  intro i j hij
  apply Fin.ext
  have hcodes : edge8Codes[i.val] = edge8Codes[j.val] := by
    have hmasks := congrArg vertexMask hij
    simp only [vertexMask_rootPairAt] at hmasks
    omega
  have hi : i.val < edge8Codes.length := by
    rw [length_edge8Codes]
    exact i.isLt
  have hj : j.val < edge8Codes.length := by
    rw [length_edge8Codes]
    exact j.isLt
  exact (List.Nodup.getElem_inj_iff nodup_edge8Codes).mp hcodes

/-- Decode selected compact graph edges as unordered pairs on `Fin 11`. -/
def rootPairFamily8 (mask : ℕ) : Finset (Finset (Fin 11)) :=
  (Finset.univ.filter fun i : Fin 28 => mask.testBit i.val).image rootPairAt

/-- The 28 packed `K₁₁` edge positions disjoint from the fixed root. -/
def rootEdgePositions11 : List ℕ :=
  (List.range 55).filter fun k => (RootCoordinates.edgeVertexMask k &&& 7) == 0

theorem length_rootEdgePositions11 : rootEdgePositions11.length = 28 := by
  decide +kernel

theorem nodup_rootEdgePositions11 : rootEdgePositions11.Nodup := by
  decide +kernel

theorem rootEdgePosition11_lt (i : Fin 28) :
    rootEdgePositions11[i.val] < 55 := by
  decide +kernel +revert

/-- The actual `K₁₁` edge at compact pair position `i`. -/
def rootEdgeAt8 (i : Fin 28) : Edge11 :=
  RootCoordinates.edgeAt
    ⟨rootEdgePositions11[i.val], rootEdgePosition11_lt i⟩

theorem rootEdgeAt8_vertices (i : Fin 28) :
    (rootEdgeAt8 i).vertices = rootPairAt i := by
  decide +kernel +revert

theorem rootEdgeAt8_injective : Function.Injective rootEdgeAt8 := by
  intro i j hij
  apply rootPairAt_injective
  rw [← rootEdgeAt8_vertices, ← rootEdgeAt8_vertices, hij]

/-- Decode a compact graph as actual edges of `K₁₁`. -/
def rootEdgeFamily8 (mask : ℕ) : Finset Edge11 :=
  (Finset.univ.filter fun i : Fin 28 => mask.testBit i.val).image rootEdgeAt8

/-- Reindex a compact pair after applying a checked permutation. -/
def relabelEdgeIndex8 (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 28) : Fin 28 :=
  ⟨edge8Codes.idxOf
      (relabelVertexCode8 permutationCode edge8Codes[i.val]),
    by
      have hlt : edge8Codes.idxOf
          (relabelVertexCode8 permutationCode edge8Codes[i.val]) <
          edge8Codes.length := List.idxOf_lt_length_iff.mpr
            (relabelVertexCode8_edge_mem permutationCode hperm i)
      simpa [length_edge8Codes] using hlt⟩

theorem edge8Code_relabelEdgeIndex8 (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 28) :
    edge8Codes[(relabelEdgeIndex8 permutationCode hperm i).val] =
      relabelVertexCode8 permutationCode edge8Codes[i.val] := by
  exact List.getElem_idxOf (relabelEdgeIndex8 permutationCode hperm i).isLt

theorem testBit_relabelEdgeMask8_iff (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) (j : Fin 28) :
    (relabelEdgeMask8 permutationCode mask).testBit j.val = true ↔
      ∃ i : Fin 28, mask.testBit i.val = true ∧
        relabelEdgeIndex8 permutationCode hperm i = j := by
  rw [relabelEdgeMask8, relabelIndexedMask8,
    SRG266.Search.testBit_itemPositionsMask_iff]
  simp only [List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨entry, ⟨hentry, hbit⟩, hindex⟩
    have hzip := List.mem_zipIdx hentry
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hzip
    have hi : entry.2 < 28 := by
      simpa [length_edge8Codes] using hzip.1
    let i : Fin 28 := ⟨entry.2, hi⟩
    refine ⟨i, by simpa [i] using hbit, ?_⟩
    apply Fin.ext
    change edge8Codes.idxOf
        (relabelVertexCode8 permutationCode edge8Codes[i.val]) = j.val
    have hcode : entry.1 = edge8Codes[i.val] := by
      convert hzip.2
    simpa [hcode] using hindex
  · rintro ⟨i, hbit, hindex⟩
    let entry : ℕ × ℕ := (edge8Codes[i.val], i.val)
    have hentry : entry ∈ edge8Codes.zipIdx := by
      rw [List.mem_iff_getElem]
      refine ⟨i.val, ?_, ?_⟩
      · simp [length_edge8Codes]
      simp [entry, List.getElem_zipIdx]
    refine ⟨entry, ⟨hentry, by simpa [entry]⟩, ?_⟩
    change edge8Codes.idxOf
      (relabelVertexCode8 permutationCode edge8Codes[i.val]) = j.val
    exact congrArg Fin.val hindex

theorem rootPairAt_eq_image_shift (i : Fin 28) :
    rootPairAt i =
      (vertices8OfMask edge8Codes[i.val]).image shiftRootVertex := by
  decide +kernel +revert

theorem rootPairAt_image_packed (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 28) :
    (rootPairAt i).image (packedPerm11Equiv permutationCode hperm) =
      rootPairAt (relabelEdgeIndex8 permutationCode hperm i) := by
  rw [rootPairAt_eq_image_shift, rootPairAt_eq_image_shift]
  have hvertices :
      vertices8OfMask
          edge8Codes[(relabelEdgeIndex8 permutationCode hperm i).val] =
        (vertices8OfMask edge8Codes[i.val]).image
          (packedPerm8Equiv permutationCode hperm) := by
    rw [edge8Code_relabelEdgeIndex8]
    rw [relabelVertexCode8_eq_vertexMask8_image permutationCode _ hperm]
    exact vertices8OfMask_vertexMask8 _
  rw [hvertices, Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro v hv
  simp only [Function.comp_apply]
  exact packedPerm11Equiv_apply_shift permutationCode hperm v

theorem rootPairFamily8_relabel (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    rootPairFamily8 (relabelEdgeMask8 permutationCode mask) =
      (rootPairFamily8 mask).image fun U =>
        U.image (packedPerm11Equiv permutationCode hperm) := by
  ext U
  constructor
  · intro hU
    obtain ⟨j, hj, hUj⟩ := Finset.mem_image.mp hU
    have hjbit : (relabelEdgeMask8 permutationCode mask).testBit j.val =
        true := by simpa [rootPairFamily8] using hj
    obtain ⟨i, hibit, hij⟩ :=
      (testBit_relabelEdgeMask8_iff permutationCode mask hperm j).mp hjbit
    rw [Finset.mem_image]
    refine ⟨rootPairAt i, ?_, ?_⟩
    · rw [rootPairFamily8, Finset.mem_image]
      exact ⟨i, by simp [hibit], rfl⟩
    · calc
        (rootPairAt i).image (packedPerm11Equiv permutationCode hperm) =
            rootPairAt (relabelEdgeIndex8 permutationCode hperm i) :=
          rootPairAt_image_packed permutationCode hperm i
        _ = rootPairAt j := congrArg rootPairAt hij
        _ = U := hUj
  · intro hU
    obtain ⟨V, hV, hVU⟩ := Finset.mem_image.mp hU
    obtain ⟨i, hi, hVi⟩ := Finset.mem_image.mp hV
    have hibit : mask.testBit i.val = true := by
      simpa [rootPairFamily8] using hi
    subst V
    let j := relabelEdgeIndex8 permutationCode hperm i
    rw [← hVU, rootPairAt_image_packed]
    rw [rootPairFamily8, Finset.mem_image]
    refine ⟨j, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (testBit_relabelEdgeMask8_iff permutationCode mask hperm j).mpr
      ⟨i, hibit, rfl⟩

theorem relabelEdgeIndex8_injective (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    Function.Injective (relabelEdgeIndex8 permutationCode hperm) := by
  intro i j hij
  apply rootPairAt_injective
  apply (Finset.image_injective
    (packedPerm11Equiv permutationCode hperm).injective)
  rw [rootPairAt_image_packed, rootPairAt_image_packed, hij]

theorem relabelEdgeIndex8_bijective (permutationCode : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    Function.Bijective (relabelEdgeIndex8 permutationCode hperm) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨relabelEdgeIndex8_injective permutationCode hperm, rfl⟩

theorem testBit_relabelEdgeMask8_at (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) (i : Fin 28) :
    (relabelEdgeMask8 permutationCode mask).testBit
        (relabelEdgeIndex8 permutationCode hperm i).val =
      mask.testBit i.val := by
  apply Bool.eq_iff_iff.mpr
  rw [testBit_relabelEdgeMask8_iff permutationCode mask hperm]
  constructor
  · rintro ⟨j, hbit, hji⟩
    have : j = i := relabelEdgeIndex8_injective permutationCode hperm hji
    simpa [this] using hbit
  · intro hbit
    exact ⟨i, hbit, rfl⟩

/-- Filtering a family by containment of a pair is invariant under a vertex
permutation. -/
theorem card_filter_pair_image (σ : Equiv.Perm (Fin 11))
    (family : Finset (Finset (Fin 11))) (pair : Finset (Fin 11)) :
    (((family.image fun U => U.image σ).filter fun U =>
        pair.image σ ⊆ U).card) =
      (family.filter fun U => pair ⊆ U).card := by
  rw [Finset.filter_image,
    Finset.card_image_of_injective _ (Finset.image_injective σ.injective)]
  apply congrArg Finset.card
  ext U
  simp only [Finset.mem_filter]
  rw [Finset.image_subset_image_iff σ.injective]

/-! ## Pair counts in compact and mathematical coordinates -/

/-- Selected compact triples containing a fixed compact pair. -/
def compactTriplesThrough (mask : ℕ) (i : Fin 28) : Finset (Fin 56) :=
  Finset.univ.filter fun j =>
    mask.testBit j.val && decide (rootPairAt i ⊆ rootTripleAt j)

theorem triple8PairVariables_eq (i : Fin 28) :
    triple8PairVariables edge8Codes[i.val] =
      ((List.finRange 56).filter fun j =>
        decide (rootPairAt i ⊆ rootTripleAt j)).map Fin.val := by
  decide +kernel +revert

theorem compactPairCount_eq_card (mask : ℕ) (i : Fin 28) :
    SRG266.Search.popcount
        (SRG266.Search.localAssignmentMask
          (triple8PairVariables edge8Codes[i.val]) mask) =
      (compactTriplesThrough mask i).card := by
  rw [SRG266.Search.popcount_localAssignmentMask,
    triple8PairVariables_eq, List.filter_map]
  simp only [List.length_map]
  rw [List.filter_filter]
  change (List.filter (fun j : Fin 56 =>
    mask.testBit j.val && decide (rootPairAt i ⊆ rootTripleAt j))
      (List.finRange 56)).length = _
  have hnodup := (List.nodup_finRange 56).filter
    (fun j => mask.testBit j.val && decide (rootPairAt i ⊆ rootTripleAt j))
  rw [← List.toFinset_card_of_nodup hnodup,
    List.toFinset_filter, List.toFinset_finRange]
  apply congrArg Finset.card
  ext j
  simp [compactTriplesThrough, Bool.and_eq_true]

theorem compactPairCount_eq_familyCard (mask : ℕ) (i : Fin 28) :
    SRG266.Search.popcount
        (SRG266.Search.localAssignmentMask
          (triple8PairVariables edge8Codes[i.val]) mask) =
      ((rootTripleFamily8 mask).filter fun U => rootPairAt i ⊆ U).card := by
  rw [compactPairCount_eq_card, rootTripleFamily8, Finset.filter_image,
    Finset.card_image_of_injective _ rootTripleAt_injective]
  apply congrArg Finset.card
  ext j
  simp [compactTriplesThrough, Bool.and_eq_true]

theorem expandedPairCount_eq_compactPairCount (mask : ℕ) (i : Fin 28) :
    SRG266.Search.popcount
        (expandRootNearMask mask &&& triplePairMask (rootEdgeAt8 i)) =
      SRG266.Search.popcount
        (SRG266.Search.localAssignmentMask
          (triple8PairVariables edge8Codes[i.val]) mask) := by
  rw [expandRootNearMask_eq_vertexFamilyMask_rootTripleFamily8,
    triplePairMask, popcount_and_vertexFamilyMask,
    compactPairCount_eq_familyCard]
  apply congrArg Finset.card
  ext U
  simp only [Finset.mem_inter, Finset.mem_filter]
  constructor
  · rintro ⟨hU, hpair⟩
    refine ⟨hU, ?_⟩
    rw [← rootEdgeAt8_vertices]
    intro v hv
    have hv' := Edge11.mem_vertices_iff.mp hv
    rcases hv' with rfl | rfl
    · exact (mem_triplesThrough.mp hpair).2.1
    · exact (mem_triplesThrough.mp hpair).2.2
  · rintro ⟨hU, hsubset⟩
    refine ⟨hU, mem_triplesThrough.mpr
      ⟨rootTripleFamily8_closed mask U hU, ?_, ?_⟩⟩
    · exact hsubset (rootEdgeAt8_vertices i ▸ (rootEdgeAt8 i).lo_mem)
    · exact hsubset (rootEdgeAt8_vertices i ▸ (rootEdgeAt8 i).hi_mem)

/-- The compact graph consisting of precisely the pairs occurring twice. -/
def reconstructedRootGraph8 (mask : ℕ) : ℕ :=
  SRG266.Search.itemPositionsMask <|
    ((List.finRange 28).filter fun i =>
      SRG266.Search.popcount
        (SRG266.Search.localAssignmentMask
          (triple8PairVariables edge8Codes[i.val]) mask) == 2).map Fin.val

theorem reconstructedRootGraph8_lt (mask : ℕ) :
    reconstructedRootGraph8 mask < 2 ^ 28 := by
  apply SRG266.Search.itemPositionsMask_lt
  intro k hk
  rw [List.mem_map] at hk
  obtain ⟨i, hi, rfl⟩ := hk
  exact i.isLt

theorem testBit_reconstructedRootGraph8 (mask : ℕ) (i : Fin 28) :
    (reconstructedRootGraph8 mask).testBit i.val = true ↔
      SRG266.Search.popcount
          (SRG266.Search.localAssignmentMask
            (triple8PairVariables edge8Codes[i.val]) mask) = 2 := by
  rw [reconstructedRootGraph8,
    SRG266.Search.testBit_itemPositionsMask_iff, List.mem_map]
  constructor
  · rintro ⟨j, hj, hval⟩
    have hji : j = i := Fin.ext hval
    subst j
    simpa only [List.mem_filter, List.mem_finRange, beq_iff_eq,
      true_and] using hj
  · intro hcount
    exact ⟨i, by simp [hcount], rfl⟩

theorem isNear8For_iff (rootGraph mask : ℕ) :
    IsNear8For rootGraph mask ↔
      ∀ i : Fin 28,
        SRG266.Search.popcount
            (SRG266.Search.localAssignmentMask
              (triple8PairVariables edge8Codes[i.val]) mask) =
          if rootGraph.testBit i.val then 2 else 3 := by
  constructor
  · intro hnear i
    let entry : ℕ × ℕ := (edge8Codes[i.val], i.val)
    have hentry : entry ∈ edge8Codes.zipIdx := by
      rw [List.mem_iff_getElem]
      refine ⟨i.val, ?_, ?_⟩
      · simp [length_edge8Codes]
      simp [entry, List.getElem_zipIdx]
    have hconstraint :
        (triple8PairVariables edge8Codes[i.val],
          if rootGraph.testBit i.val then 2 else 3) ∈
            near8Constraints rootGraph := by
      rw [near8Constraints, List.mem_map]
      exact ⟨entry, hentry, rfl⟩
    exact hnear _ hconstraint
  · intro hpoint constraint hconstraint
    rw [near8Constraints, List.mem_map] at hconstraint
    obtain ⟨entry, hentry, rfl⟩ := hconstraint
    have hzip := List.mem_zipIdx hentry
    simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hzip
    have hi : entry.2 < 28 := by
      simpa [length_edge8Codes] using hzip.1
    let i : Fin 28 := ⟨entry.2, hi⟩
    have h := hpoint i
    simpa [i, hzip.2] using h

/-- The compact pair-demand system is equivariant under every checked packed
permutation. -/
theorem IsNear8For.relabel {rootGraph mask permutationCode : ℕ}
    (hnear : IsNear8For rootGraph mask)
    (hperm : PackedPerm8OK permutationCode) :
    IsNear8For (relabelEdgeMask8 permutationCode rootGraph)
      (relabelTripleMask8 permutationCode mask) := by
  rw [isNear8For_iff] at hnear ⊢
  intro j
  obtain ⟨i, hij⟩ :=
    (relabelEdgeIndex8_bijective permutationCode hperm).2 j
  subst j
  rw [compactPairCount_eq_familyCard,
    rootTripleFamily8_relabel permutationCode mask hperm,
    ← rootPairAt_image_packed permutationCode hperm i,
    card_filter_pair_image,
    ← compactPairCount_eq_familyCard,
    testBit_relabelEdgeMask8_at permutationCode rootGraph hperm i]
  exact hnear i

theorem rootEdgeAt8_disjoint_fixedRoot (i : Fin 28) :
    7 &&& vertexMask (rootEdgeAt8 i).vertices = 0 := by
  decide +kernel +revert

/-- The exact `2/3` leaf equations become the compact pair-demand system. -/
theorem isNear8For_reconstructedRootGraph8_of_accept {mask : ℕ}
    (haccept : rootNearFreeAccept 7 (expandRootNearMask mask) = true) :
    IsNear8For (reconstructedRootGraph8 mask) mask := by
  rw [isNear8For_iff]
  intro i
  rw [rootNearFreeAccept, Bool.and_eq_true, Bool.and_eq_true] at haccept
  have hpair := (List.all_eq_true.mp haccept.1.2) (rootEdgeAt8 i)
    (RootCoordinates.mem_edges (rootEdgeAt8 i))
  rw [rootNearFreePairAccept,
    if_pos (by simp [rootEdgeAt8_disjoint_fixedRoot])] at hpair
  rw [Bool.or_eq_true, beq_iff_eq, beq_iff_eq] at hpair
  have hcount := expandedPairCount_eq_compactPairCount mask i
  rw [hcount] at hpair
  by_cases hbit : (reconstructedRootGraph8 mask).testBit i.val = true
  · rw [if_pos hbit]
    exact (testBit_reconstructedRootGraph8 mask i).mp hbit
  · rw [if_neg hbit]
    rcases hpair with htwo | hthree
    · exact False.elim (hbit
        ((testBit_reconstructedRootGraph8 mask i).mpr htwo))
    · exact hthree

/-! ## Cubicity in compact coordinates -/

theorem isCubic8_iff (graph : ℕ) :
    IsCubic8 graph ↔
      ∀ v : Fin 8,
        SRG266.Search.popcount
            (SRG266.Search.localAssignmentMask
              (edge8StarVariables v.val) graph) = 3 := by
  constructor
  · intro hcubic v
    have hmem : (edge8StarVariables v.val, 3) ∈ cubic8Constraints := by
      rw [cubic8Constraints, List.mem_map]
      exact ⟨v.val, List.mem_range.mpr v.isLt, rfl⟩
    exact hcubic _ hmem
  · intro hpoint constraint hconstraint
    rw [cubic8Constraints, List.mem_map] at hconstraint
    obtain ⟨v, hv, rfl⟩ := hconstraint
    exact hpoint ⟨v, List.mem_range.mp hv⟩

theorem edge8StarVariables_eq (v : Fin 8) :
    edge8StarVariables v.val =
      ((List.finRange 28).filter fun i =>
        shiftRootVertex v ∈ (rootEdgeAt8 i).vertices).map Fin.val := by
  decide +kernel +revert

theorem compactDegree_eq_arcDegree (graph : ℕ) (v : Fin 8) :
    SRG266.Search.popcount
        (SRG266.Search.localAssignmentMask
          (edge8StarVariables v.val) graph) =
      arcDegree (rootEdgeFamily8 graph) (shiftRootVertex v) := by
  rw [SRG266.Search.popcount_localAssignmentMask, edge8StarVariables_eq,
    List.filter_map]
  simp only [List.length_map]
  rw [List.filter_filter]
  change (List.filter (fun i : Fin 28 =>
    graph.testBit i.val &&
      decide (shiftRootVertex v ∈ (rootEdgeAt8 i).vertices))
      (List.finRange 28)).length = _
  have hnodup := (List.nodup_finRange 28).filter (fun i =>
    graph.testBit i.val &&
      decide (shiftRootVertex v ∈ (rootEdgeAt8 i).vertices))
  rw [← List.toFinset_card_of_nodup hnodup, List.toFinset_filter,
    List.toFinset_finRange]
  rw [arcDegree, rootEdgeFamily8, Finset.filter_image,
    Finset.card_image_of_injective _ rootEdgeAt8_injective]
  apply congrArg Finset.card
  ext i
  simp [Bool.and_eq_true]

theorem rootEdgeAt8_surjective_offroot (e : Edge11)
    (hoff : 7 &&& vertexMask e.vertices = 0) :
    ∃ i : Fin 28, rootEdgeAt8 i = e := by
  revert e
  decide +kernel

theorem reconstructedRootBlock_eq_rootEdgeFamily8 (mask : ℕ) :
    reconstructedRootBlock 7 (expandRootNearMask mask) =
      rootEdgeFamily8 (reconstructedRootGraph8 mask) := by
  ext e
  constructor
  · intro he
    rw [reconstructedRootBlock, Finset.mem_filter] at he
    obtain ⟨i, hie⟩ := rootEdgeAt8_surjective_offroot e he.2.1
    subst e
    rw [rootEdgeFamily8, Finset.mem_image]
    refine ⟨i, ?_, rfl⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [testBit_reconstructedRootGraph8]
    rw [← expandedPairCount_eq_compactPairCount]
    exact he.2.2
  · intro he
    rw [rootEdgeFamily8, Finset.mem_image] at he
    obtain ⟨i, hi, rfl⟩ := he
    have hbit : (reconstructedRootGraph8 mask).testBit i.val = true := by
      simpa using hi
    rw [reconstructedRootBlock, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, rootEdgeAt8_disjoint_fixedRoot i, ?_⟩
    rw [expandedPairCount_eq_compactPairCount]
    exact (testBit_reconstructedRootGraph8 mask i).mp hbit

theorem packedDegree_maskOf (T : Finset Edge11) (v : Fin 11) :
    packedDegree (RootCoordinates.edgeCoding.maskOf T) v.val = arcDegree T v := by
  have hstar : RootCoordinates.edgeCoding.maskOf (Edge11.star v) =
      RootCoordinates.starMask v.val := by
    rw [← RootCoordinates.edgesOfMask_starMask v]
    exact RootCoordinates.edgeCoding.maskOf_edgesOfMask
      (RootCoordinates.starMask_lt v)
  rw [packedDegree, ← hstar,
    RootCoordinates.edgeCoding.popcount_and_maskOf, card_inter_star]

/-- The cubic leaf check becomes the eight compact degree-three equations. -/
theorem isCubic8_reconstructedRootGraph8_of_accept {mask : ℕ}
    (haccept : rootNearFreeAccept 7 (expandRootNearMask mask) = true) :
    IsCubic8 (reconstructedRootGraph8 mask) := by
  rw [isCubic8_iff]
  intro v
  rw [compactDegree_eq_arcDegree]
  rw [rootNearFreeAccept, Bool.and_eq_true, Bool.and_eq_true] at haccept
  have hcubic := haccept.2
  rw [cubicMaskAccept, Bool.and_eq_true] at hcubic
  have hdegree := (List.all_eq_true.mp hcubic.2) (shiftRootVertex v).val
    (List.mem_range.mpr (shiftRootVertex v).isLt)
  have hrootBit : (7 : ℕ).testBit (shiftRootVertex v).val = false := by
    change (7 : ℕ).testBit (v.val + 3) = false
    apply Nat.testBit_lt_two_pow
    exact lt_of_lt_of_le (by norm_num : 7 < 2 ^ 3)
      (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ v.val + 3))
  rw [if_neg (by simpa using hrootBit), beq_iff_eq] at hdegree
  rw [reconstructedRootBlockMask, reconstructedRootBlock_eq_rootEdgeFamily8,
    packedDegree_maskOf] at hdegree
  exact hdegree

/-! ## Inverse action laws on bounded family masks -/

theorem rootTripleAt_mem_rootTripleFamily8 (mask : ℕ) (i : Fin 56) :
    rootTripleAt i ∈ rootTripleFamily8 mask ↔ mask.testBit i.val = true := by
  rw [rootTripleFamily8, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have : j = i := rootTripleAt_injective hji
    simpa [this] using hj
  · intro hbit
    exact ⟨i, by simp [hbit], rfl⟩

theorem rootPairAt_mem_rootPairFamily8 (mask : ℕ) (i : Fin 28) :
    rootPairAt i ∈ rootPairFamily8 mask ↔ mask.testBit i.val = true := by
  rw [rootPairFamily8, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    have : j = i := rootPairAt_injective hji
    simpa [this] using hj
  · intro hbit
    exact ⟨i, by simp [hbit], rfl⟩

theorem rootTripleFamily8_injective_of_lt {a b : ℕ}
    (ha : a < 2 ^ 56) (hb : b < 2 ^ 56)
    (hfamily : rootTripleFamily8 a = rootTripleFamily8 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 56
  · let i : Fin 56 := ⟨k, hk⟩
    have hmem := congrArg (fun family => rootTripleAt i ∈ family) hfamily
    simpa [rootTripleAt_mem_rootTripleFamily8, i] using hmem
  · have hpow : 2 ^ 56 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hk)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

theorem rootPairFamily8_injective_of_lt {a b : ℕ}
    (ha : a < 2 ^ 28) (hb : b < 2 ^ 28)
    (hfamily : rootPairFamily8 a = rootPairFamily8 b) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro k
  by_cases hk : k < 28
  · let i : Fin 28 := ⟨k, hk⟩
    have hmem := congrArg (fun family => rootPairAt i ∈ family) hfamily
    simpa [rootPairAt_mem_rootPairFamily8, i] using hmem
  · have hpow : 2 ^ 28 ≤ 2 ^ k :=
      Nat.pow_le_pow_right (by omega) (Nat.le_of_not_gt hk)
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hpow),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hpow)]

theorem relabelTripleMask8_lt (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    relabelTripleMask8 permutationCode mask < 2 ^ 56 := by
  apply SRG266.Search.itemPositionsMask_lt
  intro output houtput
  rw [List.mem_map] at houtput
  obtain ⟨entry, hentry, rfl⟩ := houtput
  have hzip := List.mem_zipIdx (List.mem_of_mem_filter hentry)
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hzip
  have hi : entry.2 < 56 := by
    simpa [length_triple8Codes] using hzip.1
  let i : Fin 56 := ⟨entry.2, hi⟩
  have hmem : relabelVertexCode8 permutationCode entry.1 ∈ triple8Codes := by
    have hcode : entry.1 = triple8Codes[i.val] := by convert hzip.2
    rw [hcode]
    exact relabelVertexCode8_triple_mem permutationCode hperm i
  have := List.idxOf_lt_length_iff.mpr hmem
  simpa [length_triple8Codes] using this

theorem relabelEdgeMask8_lt (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) :
    relabelEdgeMask8 permutationCode mask < 2 ^ 28 := by
  apply SRG266.Search.itemPositionsMask_lt
  intro output houtput
  rw [List.mem_map] at houtput
  obtain ⟨entry, hentry, rfl⟩ := houtput
  have hzip := List.mem_zipIdx (List.mem_of_mem_filter hentry)
  simp only [Nat.zero_le, zero_add, Nat.sub_zero, true_and] at hzip
  have hi : entry.2 < 28 := by
    simpa [length_edge8Codes] using hzip.1
  let i : Fin 28 := ⟨entry.2, hi⟩
  have hmem : relabelVertexCode8 permutationCode entry.1 ∈ edge8Codes := by
    have hcode : entry.1 = edge8Codes[i.val] := by convert hzip.2
    rw [hcode]
    exact relabelVertexCode8_edge_mem permutationCode hperm i
  have := List.idxOf_lt_length_iff.mpr hmem
  simpa [length_edge8Codes] using this

theorem relabelTripleMask8_inverse (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) (hlt : mask < 2 ^ 56) :
    relabelTripleMask8 (inversePackedPerm8Code permutationCode hperm)
        (relabelTripleMask8 permutationCode mask) = mask := by
  apply rootTripleFamily8_injective_of_lt
    (relabelTripleMask8_lt _ _ (inversePackedPerm8Code_OK _ _)) hlt
  rw [rootTripleFamily8_relabel
      (inversePackedPerm8Code permutationCode hperm)
      (relabelTripleMask8 permutationCode mask)
      (inversePackedPerm8Code_OK permutationCode hperm),
    rootTripleFamily8_relabel permutationCode mask hperm,
    packedPerm11Equiv_inverseCode, Finset.image_image]
  have hmap :
      ((fun U : Finset (Fin 11) =>
          U.image (packedPerm11Equiv permutationCode hperm).symm) ∘
        fun U => U.image (packedPerm11Equiv permutationCode hperm)) = id := by
    funext U
    exact image_perm_image_symm _ _
  rw [hmap, Finset.image_id]

theorem relabelEdgeMask8_inverse (permutationCode mask : ℕ)
    (hperm : PackedPerm8OK permutationCode) (hlt : mask < 2 ^ 28) :
    relabelEdgeMask8 (inversePackedPerm8Code permutationCode hperm)
        (relabelEdgeMask8 permutationCode mask) = mask := by
  apply rootPairFamily8_injective_of_lt
    (relabelEdgeMask8_lt _ _ (inversePackedPerm8Code_OK _ _)) hlt
  rw [rootPairFamily8_relabel
      (inversePackedPerm8Code permutationCode hperm)
      (relabelEdgeMask8 permutationCode mask)
      (inversePackedPerm8Code_OK permutationCode hperm),
    rootPairFamily8_relabel permutationCode mask hperm,
    packedPerm11Equiv_inverseCode, Finset.image_image]
  have hmap :
      ((fun U : Finset (Fin 11) =>
          U.image (packedPerm11Equiv permutationCode hperm).symm) ∘
        fun U => U.image (packedPerm11Equiv permutationCode hperm)) = id := by
    funext U
    exact image_perm_image_symm _ _
  rw [hmap, Finset.image_id]

end SRG266.QuasiSymmetric
