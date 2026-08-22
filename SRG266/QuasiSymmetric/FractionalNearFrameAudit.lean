/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Certificates.NonnegativeFarkas
import SRG266.QuasiSymmetric.FractionalNearFrameShell

/-!
# Executable audit for fractional near-frame certificates

This module is the small executable core used by generated certificate files.
A rooted near normal form is a 56-bit mask.  Its semantic columns are 56-bit
masks satisfying the regular degree condition; the suffix-pruned subset search
is only a complete enumerator for computation.  An empty-shell claim is first
tested against a theorem-mined Hall cut and otherwise rediscovered by that
enumerator.  A nonempty certificate is a 168-entry integer pair-weight array;
normalization coefficients and column inequalities are reconstructed from
shell minima.

All arithmetic checked here is integer arithmetic.  The external LP solver is
used only by the untrusted generator to suggest vectors; it is not imported or
invoked by Lean.
-/

namespace SRG266.QuasiSymmetric

open SRG266.Search

/-- Whether two selected compact near rows meet in exactly one active point. -/
def compactRowsMeetOne (left right : ℕ) : Bool :=
  popcount (compactTripleCodeAt left &&& compactTripleCodeAt right) == 1

/-- All unordered pairs from a list, preserving the list order. -/
def compactListPairs {α : Type*} : List α → List (α × α)
  | [] => []
  | item :: items => items.map (item, ·) ++ compactListPairs items

theorem compactListPairs_filter {α : Type*} (selected : α → Bool) :
    ∀ items : List α,
      compactListPairs (items.filter selected) =
        (compactListPairs items).filter fun pair =>
          selected pair.1 && selected pair.2 := by
  intro items
  induction items with
  | nil => rfl
  | cons item items ih =>
      cases hitem : selected item
      · simp [compactListPairs, hitem, ih, List.filter_append]
      · simp only [List.filter_cons, hitem, ↓reduceIte,
          compactListPairs, List.filter_append, ih]
        congr 1
        rw [List.filter_map]
        simp [Function.comp_def, hitem]

/-- The 168 intersection-one row pairs, in lexicographic row order. -/
def compactIntersectionOnePairs (nearMask : ℕ) : List (ℕ × ℕ) :=
  (compactListPairs (compactNearRows nearMask)).filter fun pair =>
    compactRowsMeetOne pair.1 pair.2

/-- Endpoint coefficient in the averaged concurrence equation. -/
def compactEndpointCoefficient (endpointMask : ℕ) : ℤ :=
  if popcount endpointMask < 2 then 3 else 1

/-- Typed endpoint indices for one normal form. -/
abbrev CompactEndpointIndex (nearMask : ℕ) :=
  Fin (compactEndpointMasks nearMask).length

/-- Typed intersection-one pair indices for one normal form. -/
abbrev CompactPairIndex (nearMask : ℕ) :=
  Fin (compactIntersectionOnePairs nearMask).length

/-- Endpoint mask at a typed index. -/
def compactEndpointMaskAt (nearMask : ℕ)
    (endpoint : CompactEndpointIndex nearMask) : ℕ :=
  (compactEndpointMasks nearMask)[endpoint.val]

/-! ## A mined Hall cut for regular endpoint shells -/

/-- Vertices carrying coefficient `+1` in a shell Hall cut. -/
def compactHallPositiveVertices (positiveMask : ℕ) : Finset (Fin 8) :=
  Finset.univ.filter fun vertex => positiveMask.testBit vertex.val

/-- Positive incidences contributed by one available triple. -/
def compactHallRowPositiveCount (positiveMask code : ℕ) : ℕ :=
  ((compactHallPositiveVertices positiveMask).filter fun vertex =>
    (compactTripleCodeAt code).testBit vertex.val).card

/-- The single negative incidence contributed by one available triple. -/
def compactHallRowNegativeCount (negativeVertex : Fin 8) (code : ℕ) : ℕ :=
  if (compactTripleCodeAt code).testBit negativeVertex.val then 1 else 0

/-- Nonnegative row capacity after paying for the negative incidence. -/
def compactHallRowCapacity
    (positiveMask : ℕ) (negativeVertex : Fin 8) (code : ℕ) : ℕ :=
  compactHallRowPositiveCount positiveMask code -
    compactHallRowNegativeCount negativeVertex code

/-- Required positive incidence in a regular endpoint shell. -/
def compactHallPositiveDemand (endpointMask positiveMask : ℕ) : ℕ :=
  ∑ vertex ∈ compactHallPositiveVertices positiveMask,
    compactColumnVertexTarget endpointMask vertex.val

/-- Total available row capacity for one Hall cut. -/
def compactHallAvailableCapacity (nearMask endpointMask positiveMask : ℕ)
    (negativeVertex : Fin 8) : ℕ :=
  ∑ code ∈ (compactNearColumnItems nearMask endpointMask).toFinset,
    compactHallRowCapacity positiveMask negativeVertex code

/-- A positive-positive-positive-negative vertex cut whose required incidence
exceeds the negative demand plus every available row's residual capacity. -/
def compactHallDeficient (nearMask endpointMask positiveMask : ℕ)
    (negativeVertex : Fin 8) : Bool :=
  decide (
    compactColumnVertexTarget endpointMask negativeVertex.val +
      compactHallAvailableCapacity nearMask endpointMask positiveMask
        negativeVertex <
    compactHallPositiveDemand endpointMask positiveMask)

/-- The Hall inequality is a semantic obstruction to a regular compact
column.  It depends only on the near rows and endpoint, not on the DFS used to
enumerate columns. -/
theorem not_isCompactNearColumn_of_compactHallDeficient
    (nearMask endpointMask positiveMask columnMask : ℕ)
    (negativeVertex : Fin 8)
    (hcut : compactHallDeficient nearMask endpointMask positiveMask
      negativeVertex = true) :
    ¬ IsCompactNearColumn nearMask endpointMask columnMask := by
  intro hcolumn
  rw [compactHallDeficient, decide_eq_true_eq] at hcut
  let items := (compactNearColumnItems nearMask endpointMask).toFinset
  let selected := items.filter fun code => columnMask.testBit code
  have hpositive : compactHallPositiveDemand endpointMask positiveMask =
      ∑ code ∈ selected, compactHallRowPositiveCount positiveMask code := by
    rw [compactHallPositiveDemand]
    calc
      (∑ vertex ∈ compactHallPositiveVertices positiveMask,
          compactColumnVertexTarget endpointMask vertex.val) =
          ∑ vertex ∈ compactHallPositiveVertices positiveMask,
            ((compactNearColumnItems nearMask endpointMask).toFinset.filter
              fun code => columnMask.testBit code = true ∧
                (compactTripleCodeAt code).testBit vertex.val = true).card := by
            apply Finset.sum_congr rfl
            intro vertex _
            exact (hcolumn.2 vertex).symm
      _ = ∑ code ∈ selected,
          compactHallRowPositiveCount positiveMask code := by
            calc
              (∑ vertex ∈ compactHallPositiveVertices positiveMask,
                  ((compactNearColumnItems nearMask endpointMask).toFinset.filter
                    fun code => columnMask.testBit code = true ∧
                      (compactTripleCodeAt code).testBit vertex.val = true).card) =
                  ∑ vertex ∈ compactHallPositiveVertices positiveMask,
                    ∑ code ∈ selected,
                      if (compactTripleCodeAt code).testBit vertex.val
                        then 1 else 0 := by
                    apply Finset.sum_congr rfl
                    intro vertex _
                    rw [Finset.sum_boole]
                    congr 1
                    ext code
                    simp [selected, items, and_assoc]
              _ = ∑ code ∈ selected,
                    ∑ vertex ∈ compactHallPositiveVertices positiveMask,
                      if (compactTripleCodeAt code).testBit vertex.val
                        then 1 else 0 := by
                    rw [Finset.sum_comm]
              _ = ∑ code ∈ selected,
                  compactHallRowPositiveCount positiveMask code := by
                    apply Finset.sum_congr rfl
                    intro code _
                    rw [compactHallRowPositiveCount, Finset.sum_boole]
                    norm_cast
  have hnegative : compactColumnVertexTarget endpointMask negativeVertex.val =
      ∑ code ∈ selected,
        compactHallRowNegativeCount negativeVertex code := by
    calc
      compactColumnVertexTarget endpointMask negativeVertex.val =
          ((compactNearColumnItems nearMask endpointMask).toFinset.filter
            fun code => columnMask.testBit code = true ∧
              (compactTripleCodeAt code).testBit negativeVertex.val = true).card :=
        (hcolumn.2 negativeVertex).symm
      _ = ∑ code ∈ selected,
          compactHallRowNegativeCount negativeVertex code := by
            simp only [compactHallRowNegativeCount]
            rw [Finset.sum_boole]
            congr 1
            ext code
            simp [selected, items, and_assoc]
  have hrow : ∀ code, compactHallRowPositiveCount positiveMask code ≤
      compactHallRowNegativeCount negativeVertex code +
        compactHallRowCapacity positiveMask negativeVertex code := by
    intro code
    rw [compactHallRowCapacity]
    omega
  have hselected :
      (∑ code ∈ selected, compactHallRowPositiveCount positiveMask code) ≤
        (∑ code ∈ selected,
          compactHallRowNegativeCount negativeVertex code) +
        ∑ code ∈ selected,
          compactHallRowCapacity positiveMask negativeVertex code := by
    calc
      (∑ code ∈ selected, compactHallRowPositiveCount positiveMask code) ≤
          ∑ code ∈ selected,
            (compactHallRowNegativeCount negativeVertex code +
              compactHallRowCapacity positiveMask negativeVertex code) := by
            exact Finset.sum_le_sum fun code _ => hrow code
      _ = _ := by simp [Finset.sum_add_distrib]
  have hsubset : selected ⊆ items := Finset.filter_subset _ _
  have hcapacity :
      (∑ code ∈ selected,
        compactHallRowCapacity positiveMask negativeVertex code) ≤
      compactHallAvailableCapacity nearMask endpointMask positiveMask
        negativeVertex := by
    rw [compactHallAvailableCapacity]
    exact Finset.sum_le_sum_of_subset hsubset
  rw [← hpositive, ← hnegative] at hselected
  omega

/-- Weighted row value for a general vertex Hall functional. -/
def compactWeightedHallRowValue (vertexWeight : Fin 8 → ℤ) (code : ℕ) : ℤ :=
  ∑ vertex : Fin 8,
    if (compactTripleCodeAt code).testBit vertex.val then
      vertexWeight vertex
    else 0

/-- Weighted degree demand of one endpoint shell. -/
def compactWeightedHallDemand (endpointMask : ℕ)
    (vertexWeight : Fin 8 → ℤ) : ℤ :=
  ∑ vertex : Fin 8,
    (compactColumnVertexTarget endpointMask vertex.val : ℤ) *
      vertexWeight vertex

/-- The sum of all positive row values available to a weighted Hall cut. -/
def compactWeightedHallAvailableCapacity (nearMask endpointMask : ℕ)
    (vertexWeight : Fin 8 → ℤ) : ℤ :=
  ∑ code ∈ (compactNearColumnItems nearMask endpointMask).toFinset,
    max 0 (compactWeightedHallRowValue vertexWeight code)

/-- A general weighted Hall functional whose demand exceeds all available
positive row contributions. -/
def compactWeightedHallDeficient (nearMask endpointMask : ℕ)
    (vertexWeight : Fin 8 → ℤ) : Bool :=
  decide (compactWeightedHallAvailableCapacity nearMask endpointMask
      vertexWeight < compactWeightedHallDemand endpointMask vertexWeight)

/-- Any weighted Hall deficiency rules out a semantic regular compact
column.  This is the general theorem-mined rule behind the exceptional
`(-2,-2,0,0,1,1,1,4)` cut orbit. -/
theorem not_isCompactNearColumn_of_compactWeightedHallDeficient
    (nearMask endpointMask columnMask : ℕ) (vertexWeight : Fin 8 → ℤ)
    (hcut : compactWeightedHallDeficient nearMask endpointMask vertexWeight = true) :
    ¬ IsCompactNearColumn nearMask endpointMask columnMask := by
  intro hcolumn
  rw [compactWeightedHallDeficient, decide_eq_true_eq] at hcut
  let items := (compactNearColumnItems nearMask endpointMask).toFinset
  let selected := items.filter fun code => columnMask.testBit code
  have hdemand : compactWeightedHallDemand endpointMask vertexWeight =
      ∑ code ∈ selected, compactWeightedHallRowValue vertexWeight code := by
    rw [compactWeightedHallDemand]
    calc
      (∑ vertex : Fin 8,
          (compactColumnVertexTarget endpointMask vertex.val : ℤ) *
            vertexWeight vertex) =
          ∑ vertex : Fin 8,
            (((compactNearColumnItems nearMask endpointMask).toFinset.filter
              fun code => columnMask.testBit code = true ∧
                (compactTripleCodeAt code).testBit vertex.val = true).card : ℤ) *
              vertexWeight vertex := by
            apply Finset.sum_congr rfl
            intro vertex _
            rw [hcolumn.2 vertex]
      _ = ∑ vertex : Fin 8, ∑ code ∈ selected,
            if (compactTripleCodeAt code).testBit vertex.val then
              vertexWeight vertex
            else 0 := by
            apply Finset.sum_congr rfl
            intro vertex _
            calc
              (((compactNearColumnItems nearMask endpointMask).toFinset.filter
                    fun code => columnMask.testBit code = true ∧
                      (compactTripleCodeAt code).testBit vertex.val = true).card : ℤ) *
                  vertexWeight vertex =
                  (∑ code ∈ selected,
                    if (compactTripleCodeAt code).testBit vertex.val
                      then (1 : ℤ) else 0) * vertexWeight vertex := by
                    have hset :
                        (compactNearColumnItems nearMask endpointMask).toFinset.filter
                            (fun code => columnMask.testBit code = true ∧
                              (compactTripleCodeAt code).testBit vertex.val = true) =
                          selected.filter fun code =>
                            (compactTripleCodeAt code).testBit vertex.val := by
                      ext code
                      simp [selected, items, and_assoc]
                    rw [Finset.sum_boole, hset]
              _ = ∑ code ∈ selected,
                    if (compactTripleCodeAt code).testBit vertex.val then
                      vertexWeight vertex
                    else 0 := by
                    rw [Finset.sum_mul]
                    apply Finset.sum_congr rfl
                    intro code _
                    split <;> simp_all
      _ = ∑ code ∈ selected, compactWeightedHallRowValue vertexWeight code := by
            rw [Finset.sum_comm]
            rfl
  have hselected :
      (∑ code ∈ selected, compactWeightedHallRowValue vertexWeight code) ≤
      ∑ code ∈ selected, max 0 (compactWeightedHallRowValue vertexWeight code) := by
    exact Finset.sum_le_sum fun code _ => le_max_right _ _
  have hsubset : selected ⊆ items := Finset.filter_subset _ _
  have hcapacity :
      (∑ code ∈ selected,
        max 0 (compactWeightedHallRowValue vertexWeight code)) ≤
      compactWeightedHallAvailableCapacity nearMask endpointMask vertexWeight := by
    rw [compactWeightedHallAvailableCapacity]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun code _ _ =>
      le_max_left _ _
  rw [← hdemand] at hselected
  exact (not_lt_of_ge (le_trans hselected hcapacity)) hcut

/-- Intersection-one pair at a typed index. -/
def compactIntersectionOnePairAt (nearMask : ℕ)
    (pair : CompactPairIndex nearMask) : ℕ × ℕ :=
  (compactIntersectionOnePairs nearMask).getD pair.val (0, 0)

/-- Typed columns in one regular endpoint shell.  The semantic column type is
bounded directly by its 56-bit mask; the executable shell is only an
enumerator and is not part of the feasibility problem's definition. -/
abbrev CompactShellColumn (nearMask : ℕ)
    (endpoint : CompactEndpointIndex nearMask) :=
  {columnMask : Fin (2 ^ 56) // IsCompactNearColumn nearMask
    (compactEndpointMaskAt nearMask endpoint) columnMask.val}

noncomputable instance compactShellColumnFintype (nearMask : ℕ)
    (endpoint : CompactEndpointIndex nearMask) :
    Fintype (CompactShellColumn nearMask endpoint) := by
  classical
  exact Fintype.ofFinite _

/-- All columns, tagged by their endpoint shell. -/
abbrev CompactFractionalColumn (nearMask : ℕ) :=
  Σ endpoint : CompactEndpointIndex nearMask,
    CompactShellColumn nearMask endpoint

/-- Normalization rows followed by intersection-one concurrence rows. -/
abbrev CompactFractionalRow (nearMask : ℕ) :=
  CompactEndpointIndex nearMask ⊕ CompactPairIndex nearMask

/-- Safe lookup of one integer witness entry. -/
def compactWitnessAt (witness : Array ℤ) (index : ℕ) : ℤ :=
  witness.getD index 0

/-- One pair contribution, with a natural index for fast list evaluation. -/
def compactFarkasPairTerm (nearMask : ℕ) (witness : Array ℤ)
    (columnMask pairIndex : ℕ) : ℤ :=
  let vertices := (compactIntersectionOnePairs nearMask).toArray.getD pairIndex (0, 0)
  if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
    compactWitnessAt witness
      ((compactEndpointMasks nearMask).length + pairIndex)
  else 0

/-- Exact `AᵀY` value of one shell column. -/
def compactFarkasColumnSlack (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) : ℤ :=
  compactWitnessAt witness endpoint.val +
    compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      ∑ pair : CompactPairIndex nearMask,
        compactFarkasPairTerm nearMask witness columnMask pair.val

/-- Exact `b·Y` value. -/
def compactFarkasRhsDot (nearMask : ℕ) (witness : Array ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactWitnessAt witness endpoint.val) +
    3 * ∑ pair : CompactPairIndex nearMask,
      compactWitnessAt witness
        ((compactEndpointMasks nearMask).length + pair.val)

/-- List evaluation of a mapped range agrees with the corresponding finite
sum.  Generated checks use the list side because it reduces substantially
faster in the kernel. -/
theorem list_sum_map_range {α : Type*} [AddCommMonoid α] (f : ℕ → α) :
    ∀ n : ℕ, ((List.range n).map f).sum = ∑ k ∈ Finset.range n, f k := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, ih,
        Finset.sum_range_succ]
      simp

theorem list_sum_map_range_eq_sum_fin {α : Type*} [AddCommMonoid α]
    (f : ℕ → α) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  rw [list_sum_map_range, Finset.sum_fin_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.mem_range.mp hi]

private theorem foldl_int_add_eq_sum_map {α : Type*}
    (items : List α) (value : α → ℤ) (base : ℤ) :
    items.foldl (fun total item => total + value item) base =
      base + (items.map value).sum := by
  induction items generalizing base with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- Sparse list form of one column slack. -/
def compactSparseFarkasColumnSlack (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) : ℤ :=
  compactWitnessAt witness endpoint.val +
    compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      ((List.range (compactIntersectionOnePairs nearMask).length).map fun pairIndex =>
        compactFarkasPairTerm nearMask witness columnMask pairIndex).sum

/-- Sparse list form of the right-hand-side dot product. -/
def compactSparseFarkasRhsDot (nearMask : ℕ) (witness : Array ℤ) : ℤ :=
  ((List.range (compactEndpointMasks nearMask).length).map fun endpointIndex =>
      compactWitnessAt witness endpointIndex).sum +
    3 * ((List.range (compactIntersectionOnePairs nearMask).length).map fun pairIndex =>
      compactWitnessAt witness
        ((compactEndpointMasks nearMask).length + pairIndex)).sum

/-- Hot-loop column slack with all shared lists and lengths passed explicitly.
This avoids reconstructing the 168 pair rows for every summand. -/
def compactFastFarkasColumnSlack
    (endpointCount endpointIndex endpointMask columnMask : ℕ)
    (pairs : Array (ℕ × ℕ)) (witness : Array ℤ) : ℤ :=
  compactWitnessAt witness endpointIndex +
    compactEndpointCoefficient endpointMask *
      ((List.range pairs.size).map fun pairIndex =>
        let vertices := pairs.getD pairIndex (0, 0)
        if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
          compactWitnessAt witness (endpointCount + pairIndex)
        else 0).sum

/-- Kernel-oriented column slack. Filtering the active pair indices before
summing avoids retaining 168 integer zero terms in a reduction proof. -/
def compactKernelFarkasColumnSlack
    (endpointCount endpointIndex endpointMask columnMask : ℕ)
    (pairs : Array (ℕ × ℕ)) (witness : Array ℤ) : ℤ :=
  compactWitnessAt witness endpointIndex +
    compactEndpointCoefficient endpointMask *
      (((List.range pairs.size).filter fun pairIndex =>
        let vertices := pairs.getD pairIndex (0, 0)
        columnMask.testBit vertices.1 && columnMask.testBit vertices.2).map
          fun pairIndex => compactWitnessAt witness
            (endpointCount + pairIndex)).sum

private theorem sum_map_ite_eq_sum_filter
    {α : Type*} (items : List α) (selected : α → Bool) (value : α → ℤ) :
    (items.map fun item => if selected item then value item else 0).sum =
      ((items.filter selected).map value).sum := by
  induction items with
  | nil => rfl
  | cons item items ih =>
      cases hselected : selected item <;> simp [hselected, ih]

theorem compactKernelFarkasColumnSlack_eq_fast
    (endpointCount endpointIndex endpointMask columnMask : ℕ)
    (pairs : Array (ℕ × ℕ)) (witness : Array ℤ) :
    compactKernelFarkasColumnSlack endpointCount endpointIndex endpointMask
        columnMask pairs witness =
      compactFastFarkasColumnSlack endpointCount endpointIndex endpointMask
        columnMask pairs witness := by
  rw [compactKernelFarkasColumnSlack, compactFastFarkasColumnSlack]
  apply congrArg₂ (· + ·) rfl
  apply congrArg₂ (· * ·) rfl
  exact (sum_map_ite_eq_sum_filter _ _ _).symm

/-- Hot-loop right-hand-side dot product. -/
def compactFastFarkasRhsDot
    (endpointCount pairCount : ℕ) (witness : Array ℤ) : ℤ :=
  ((List.range endpointCount).map fun endpointIndex =>
      compactWitnessAt witness endpointIndex).sum +
    3 * ((List.range pairCount).map fun pairIndex =>
      compactWitnessAt witness (endpointCount + pairIndex)).sum

theorem compactSparseFarkasColumnSlack_eq
    (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) :
    compactSparseFarkasColumnSlack nearMask witness endpoint columnMask =
      compactFarkasColumnSlack nearMask witness endpoint columnMask := by
  rw [compactSparseFarkasColumnSlack, compactFarkasColumnSlack,
    list_sum_map_range_eq_sum_fin]

theorem compactSparseFarkasRhsDot_eq (nearMask : ℕ) (witness : Array ℤ) :
    compactSparseFarkasRhsDot nearMask witness =
      compactFarkasRhsDot nearMask witness := by
  rw [compactSparseFarkasRhsDot, compactFarkasRhsDot,
    list_sum_map_range_eq_sum_fin, list_sum_map_range_eq_sum_fin]

theorem compactFastFarkasColumnSlack_eq
    (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) :
    compactFastFarkasColumnSlack
        (compactEndpointMasks nearMask).length endpoint.val
        (compactEndpointMaskAt nearMask endpoint) columnMask
        (compactIntersectionOnePairs nearMask).toArray witness =
      compactFarkasColumnSlack nearMask witness endpoint columnMask := by
  rw [compactFastFarkasColumnSlack, compactFarkasColumnSlack,
    List.size_toArray, list_sum_map_range_eq_sum_fin]
  rfl

theorem compactFastFarkasRhsDot_eq (nearMask : ℕ) (witness : Array ℤ) :
    compactFastFarkasRhsDot (compactEndpointMasks nearMask).length
        (compactIntersectionOnePairs nearMask).length witness =
      compactFarkasRhsDot nearMask witness := by
  rw [compactFastFarkasRhsDot, compactFarkasRhsDot,
    list_sum_map_range_eq_sum_fin, list_sum_map_range_eq_sum_fin]

theorem sum_fin_getD_eq_sum_map {α M : Type*} [AddCommMonoid M]
    (items : List α) (fallback : α) (value : α → M) :
    (∑ index : Fin items.length, value (items.getD index.val fallback)) =
      (items.map value).sum := by
  rw [← List.sum_ofFn]
  simp

/-- Exact `AᵀY` value with pair weights supplied as a small generated
pattern-matching function. -/
def compactFunctionalFarkasColumnSlack (nearMask : ℕ)
    (endpointWeights : Array ℤ) (pairWeight : ℕ × ℕ → ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) : ℤ :=
  compactWitnessAt endpointWeights endpoint.val +
    compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      ∑ pair : CompactPairIndex nearMask,
        let vertices := compactIntersectionOnePairAt nearMask pair
        if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
          pairWeight vertices
        else 0

/-- Kernel-oriented functional slack, visiting only pairs of selected rows. -/
def compactKernelFunctionalFarkasColumnSlack (nearMask : ℕ)
    (endpointWeights : Array ℤ) (pairWeight : ℕ × ℕ → ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) : ℤ :=
  let selectedRows :=
    (compactNearRows nearMask).filter fun row => columnMask.testBit row
  compactWitnessAt endpointWeights endpoint.val +
    compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      (((compactListPairs selectedRows).filter fun pair =>
        compactRowsMeetOne pair.1 pair.2).map pairWeight).sum

/-- The pair-quadratic part of a column slack, evaluated only on selected
rows.  This is the canonical statistic used to mine normalization weights. -/
def compactKernelPairWeightSum (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) (columnMask : ℕ) : ℤ :=
  let selectedRows :=
    (compactNearRows nearMask).filter fun row => columnMask.testBit row
  (((compactListPairs selectedRows).filter fun pair =>
    compactRowsMeetOne pair.1 pair.2).map pairWeight).sum

theorem compactKernelPairWeightSum_eq (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) (columnMask : ℕ) :
    compactKernelPairWeightSum nearMask pairWeight columnMask =
      ∑ pair : CompactPairIndex nearMask,
        let vertices := compactIntersectionOnePairAt nearMask pair
        if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
          pairWeight vertices
        else 0 := by
  rw [compactKernelPairWeightSum]
  let pairValue : ℕ × ℕ → ℤ := fun vertices =>
    if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
      pairWeight vertices
    else 0
  change _ = ∑ pair : CompactPairIndex nearMask,
    pairValue ((compactIntersectionOnePairs nearMask).getD pair.val (0, 0))
  rw [sum_fin_getD_eq_sum_map]
  dsimp only [pairValue]
  rw [compactIntersectionOnePairs, sum_map_ite_eq_sum_filter,
    List.filter_comm]
  rw [← compactListPairs_filter]

/-- A fused minimum that does not allocate the mapped list during kernel
reduction.  The fallback is relevant only for an empty input. -/
def compactListMinimumBy {α : Type*} (value : α → ℤ) : List α → ℤ
  | [] => 0
  | head :: tail =>
      tail.foldl (fun current item => min current (value item)) (value head)

private theorem foldl_minimumBy_le_base {α : Type*} (value : α → ℤ)
    (items : List α) (base : ℤ) :
    items.foldl (fun current item => min current (value item)) base ≤ base := by
  induction items generalizing base with
  | nil => rfl
  | cons head tail ih =>
      rw [List.foldl_cons]
      exact le_trans (ih _) (min_le_left _ _)

private theorem foldl_minimumBy_le_of_mem {α : Type*} (value : α → ℤ)
    {target : α} (items : List α) (base : ℤ) (htarget : target ∈ items) :
    items.foldl (fun current item => min current (value item)) base ≤
      value target := by
  induction items generalizing base with
  | nil => simp at htarget
  | cons head tail ih =>
      rw [List.foldl_cons]
      rcases List.eq_or_mem_of_mem_cons htarget with rfl | htail
      · exact le_trans (foldl_minimumBy_le_base value tail _)
          (min_le_right _ _)
      · exact ih _ htail

theorem compactListMinimumBy_le_of_mem {α : Type*} (value : α → ℤ)
    {target : α} {items : List α} (htarget : target ∈ items) :
    compactListMinimumBy value items ≤ value target := by
  cases items with
  | nil => simp at htarget
  | cons head tail =>
      rw [compactListMinimumBy]
      rcases List.eq_or_mem_of_mem_cons htarget with rfl | htail
      · exact foldl_minimumBy_le_base value tail _
      · exact foldl_minimumBy_le_of_mem value tail _ htail

/-- The least pair-quadratic value on an endpoint shell, with zero as the
irrelevant fallback for an empty shell. -/
def compactEndpointPairMinimum (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  compactListMinimumBy (compactKernelPairWeightSum nearMask pairWeight)
    (compactNearColumnShell nearMask
      (compactEndpointMaskAt nearMask endpoint))

/-- Canonical normalization coefficient mined from a pair-weight function. -/
def compactCanonicalEndpointWeight (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
    compactEndpointPairMinimum nearMask pairWeight endpoint

theorem compactCanonicalEndpointWeight_nonnegativeSlack
    (nearMask : ℕ) (pairWeight : ℕ × ℕ → ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ)
    (hcolumn : columnMask ∈ compactNearColumnShell nearMask
      (compactEndpointMaskAt nearMask endpoint)) :
    0 ≤ compactCanonicalEndpointWeight nearMask pairWeight endpoint +
      compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
        compactKernelPairWeightSum nearMask pairWeight columnMask := by
  have hminimum : compactEndpointPairMinimum nearMask pairWeight endpoint ≤
      compactKernelPairWeightSum nearMask pairWeight columnMask := by
    exact compactListMinimumBy_le_of_mem
      (compactKernelPairWeightSum nearMask pairWeight) hcolumn
  have hcoefficient :
      0 ≤ compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) := by
    simp only [compactEndpointCoefficient]
    split <;> norm_num
  rw [compactCanonicalEndpointWeight]
  nlinarith [mul_le_mul_of_nonneg_left hminimum hcoefficient]

/-- Pair-quadratic column value read from an indexed pair-weight array. -/
def compactIndexedPairWeightSum (nearMask : ℕ) (witness : Array ℤ)
    (columnMask : ℕ) : ℤ :=
  ∑ pair : CompactPairIndex nearMask,
    let vertices := compactIntersectionOnePairAt nearMask pair
    if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
      compactWitnessAt witness
        pair.val
    else 0

/-- Kernel-oriented indexed pair sum, filtering zero terms before addition. -/
def compactKernelIndexedPairWeightSum (nearMask : ℕ) (witness : Array ℤ)
    (columnMask : ℕ) : ℤ :=
  let pairs := compactIntersectionOnePairs nearMask
  (((List.range pairs.length).filter fun pairIndex =>
    let vertices := pairs.getD pairIndex (0, 0)
    columnMask.testBit vertices.1 && columnMask.testBit vertices.2).map
      fun pairIndex => compactWitnessAt witness
        pairIndex).sum

theorem compactKernelIndexedPairWeightSum_eq (nearMask : ℕ)
    (witness : Array ℤ) (columnMask : ℕ) :
    compactKernelIndexedPairWeightSum nearMask witness columnMask =
      compactIndexedPairWeightSum nearMask witness columnMask := by
  rw [compactKernelIndexedPairWeightSum, compactIndexedPairWeightSum,
    ← sum_map_ite_eq_sum_filter, list_sum_map_range_eq_sum_fin]
  rfl

/-- Minimum operation for optional values. -/
def compactMinimumOption : Option ℤ → Option ℤ → Option ℤ
  | none, right => right
  | left, none => left
  | some left, some right => some (min left right)

private theorem foldl_compactMinimumOption_le_base {α : Type*}
    (value : α → Option ℤ) (items : List α) (base : ℤ) :
    ∃ result,
      items.foldl (fun current item =>
        compactMinimumOption current (value item)) (some base) = some result ∧
      result ≤ base := by
  induction items generalizing base with
  | nil => exact ⟨base, rfl, le_rfl⟩
  | cons head tail ih =>
      rw [List.foldl_cons]
      cases hvalue : value head with
      | none => simpa [compactMinimumOption, hvalue] using ih base
      | some headValue =>
          rcases ih (min base headValue) with ⟨result, hresult, hle⟩
          exact ⟨result, by simpa [compactMinimumOption, hvalue] using hresult,
            le_trans hle (min_le_left _ _)⟩

private theorem foldl_compactMinimumOption_le_of_mem {α : Type*}
    (value : α → Option ℤ) (items : List α) (accumulator : Option ℤ)
    {target : α} {targetValue : ℤ} (htarget : target ∈ items)
    (hvalue : value target = some targetValue) :
    ∃ result,
      items.foldl (fun current item =>
        compactMinimumOption current (value item)) accumulator = some result ∧
      result ≤ targetValue := by
  induction items generalizing accumulator with
  | nil => simp at htarget
  | cons head tail ih =>
      rw [List.foldl_cons]
      rcases List.eq_or_mem_of_mem_cons htarget with rfl | htail
      · cases accumulator with
        | none =>
            simpa [compactMinimumOption, hvalue] using
              foldl_compactMinimumOption_le_base value tail targetValue
        | some base =>
            rcases foldl_compactMinimumOption_le_base value tail
                (min base targetValue) with ⟨result, hresult, hle⟩
            exact ⟨result,
              by simpa [compactMinimumOption, hvalue] using hresult,
              le_trans hle (min_le_right _ _)⟩
      · exact ih (compactMinimumOption accumulator (value head)) htail

/-- Fuse exact-demand shell enumeration with minimization, avoiding a materialized
list of all completed columns. -/
def transparentCompactNearColumnMinimumAux (value : ℕ → ℤ) (items : List ℕ) :
    ℕ → TransparentCompactColumnState → Option ℤ
  | 0, _ => none
  | fuel + 1, state =>
      let validItems := items.filter fun code =>
        transparentCompactColumnCodeValid state code
      match transparentCompactColumnPivot state with
      | none => some (value state.columnMask)
      | some pivot =>
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          (candidates.sublistsLen need).foldl (fun current selected =>
            match addTransparentCompactBundle? state selected with
            | none => current
            | some next => compactMinimumOption current
                (transparentCompactNearColumnMinimumAux value items fuel next)) none

/-- Direct minimum over one exact-demand shell. -/
def compactNearColumnMinimum (nearMask endpointMask : ℕ) (value : ℕ → ℤ) : ℤ :=
  let items := compactNearColumnItems nearMask endpointMask
  (transparentCompactNearColumnMinimumAux value items 9
    ⟨0, transparentCompactColumnInitialDemand endpointMask⟩).getD 0

private theorem transparentCompactNearColumnMinimumAux_le_of_mem
    (value : ℕ → ℤ) (items : List ℕ) (fuel : ℕ)
    (state : TransparentCompactColumnState) {columnMask : ℕ}
    (hcolumn : columnMask ∈
      transparentCompactNearColumnAux items fuel state) :
    ∃ result,
      transparentCompactNearColumnMinimumAux value items fuel state = some result ∧
      result ≤ value columnMask := by
  induction fuel generalizing state with
  | zero => simp [transparentCompactNearColumnAux] at hcolumn
  | succ fuel ih =>
      simp only [transparentCompactNearColumnAux] at hcolumn
      simp only [transparentCompactNearColumnMinimumAux]
      let validItems := items.filter fun code =>
        transparentCompactColumnCodeValid state code
      cases hpivot : transparentCompactColumnPivot state with
      | none =>
          simp only [hpivot] at hcolumn ⊢
          have heq : columnMask = state.columnMask := by simpa using hcolumn
          subst columnMask
          exact ⟨value state.columnMask, rfl, le_rfl⟩
      | some pivot =>
          simp only [hpivot] at hcolumn ⊢
          let need := state.demand pivot
          let candidates := validItems.filter fun code =>
            (compactTripleCodeAt code).testBit pivot.val
          rcases List.mem_flatMap.mp hcolumn with
            ⟨selected, hselected, hbranch⟩
          cases hnext : addTransparentCompactBundle? state selected with
          | none => simp [hnext] at hbranch
          | some next =>
              have hnextColumn : columnMask ∈
                  transparentCompactNearColumnAux items fuel next := by
                simpa [hnext] using hbranch
              rcases ih next hnextColumn with ⟨branchResult, hresult, hle⟩
              let branchValue : List ℕ → Option ℤ := fun branch =>
                match addTransparentCompactBundle? state branch with
                | none => none
                | some nextState =>
                    transparentCompactNearColumnMinimumAux value items fuel nextState
              have hselectedValue : branchValue selected = some branchResult := by
                simp [branchValue, hnext, hresult]
              rcases foldl_compactMinimumOption_le_of_mem branchValue
                  (candidates.sublistsLen need) none hselected hselectedValue with
                ⟨result, hfold, hfoldLe⟩
              have hstep :
                  (fun current branch =>
                    compactMinimumOption current (branchValue branch)) =
                  (fun current branch =>
                    match addTransparentCompactBundle? state branch with
                    | none => current
                    | some nextState => compactMinimumOption current
                        (transparentCompactNearColumnMinimumAux value items fuel
                          nextState)) := by
                funext current branch
                cases hbranchNext : addTransparentCompactBundle? state branch <;>
                  cases current <;>
                  simp [branchValue, hbranchNext, compactMinimumOption]
              rw [hstep] at hfold
              exact ⟨result, by
                simpa [candidates, need, validItems, Bool.and_comm] using hfold,
                le_trans hfoldLe hle⟩

theorem compactNearColumnMinimum_le_of_mem
    (nearMask endpointMask : ℕ) (value : ℕ → ℤ) {columnMask : ℕ}
    (hcolumn : columnMask ∈ compactNearColumnShell nearMask endpointMask) :
    compactNearColumnMinimum nearMask endpointMask value ≤ value columnMask := by
  rw [compactNearColumnShell, transparentCompactNearColumnShell] at hcolumn
  rcases transparentCompactNearColumnMinimumAux_le_of_mem value
      (compactNearColumnItems nearMask endpointMask) 9
      ⟨0, transparentCompactColumnInitialDemand endpointMask⟩ hcolumn with
    ⟨result, hresult, hle⟩
  rw [compactNearColumnMinimum, hresult]
  exact hle

/-- Canonical shell minimum from an indexed pair-weight array. -/
def compactIndexedEndpointPairMinimum (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  compactNearColumnMinimum nearMask (compactEndpointMaskAt nearMask endpoint)
    (compactKernelIndexedPairWeightSum nearMask witness)

/-- Canonical endpoint coefficient reconstructed from indexed pair entries. -/
def compactIndexedCanonicalEndpointWeight (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
    compactIndexedEndpointPairMinimum nearMask witness endpoint

theorem compactIndexedCanonicalEndpointWeight_nonnegativeSlack
    (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ)
    (hcolumn : columnMask ∈ compactNearColumnShell nearMask
      (compactEndpointMaskAt nearMask endpoint)) :
    0 ≤ compactIndexedCanonicalEndpointWeight nearMask witness endpoint +
      compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
        compactKernelIndexedPairWeightSum nearMask witness columnMask := by
  have hminimum : compactIndexedEndpointPairMinimum nearMask witness endpoint ≤
      compactKernelIndexedPairWeightSum nearMask witness columnMask := by
    exact compactNearColumnMinimum_le_of_mem nearMask
      (compactEndpointMaskAt nearMask endpoint)
      (compactKernelIndexedPairWeightSum nearMask witness) hcolumn
  have hcoefficient :
      0 ≤ compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) := by
    simp only [compactEndpointCoefficient]
    split <;> norm_num
  rw [compactIndexedCanonicalEndpointWeight]
  nlinarith [mul_le_mul_of_nonneg_left hminimum hcoefficient]

/-! ## A mined local-search lower bound for the large empty endpoint shell -/

/-- The empty endpoint is always the first endpoint type. -/
def compactEmptyEndpointIndex (nearMask : ℕ) : CompactEndpointIndex nearMask :=
  ⟨0, by simp [compactEndpointMasks]⟩

@[simp] theorem compactEndpointMaskAt_empty (nearMask : ℕ) :
    compactEndpointMaskAt nearMask (compactEmptyEndpointIndex nearMask) = 0 := by
  simp [compactEndpointMaskAt, compactEmptyEndpointIndex, compactEndpointMasks]

/-- The first empty-shell column, evaluated by the short-circuit DFS compiler
rather than by materializing the complete shell. -/
def compactIndexedEmptyStart (nearMask : ℕ) : ℕ :=
  (compactNearColumnFirst? nearMask 0).getD 0

theorem compactIndexedEmptyStart_eq_shell_head (nearMask : ℕ) :
    compactIndexedEmptyStart nearMask =
      ((compactNearColumnShell nearMask 0).head?).getD 0 := by
  rw [compactIndexedEmptyStart, compactNearColumnFirst?_eq_head?]

/-- One deterministic steepest-descent step among columns differing in at
most three selected rows. Its lower-bound property is proved separately. -/
def compactIndexedEmptyDescentStep (nearMask : ℕ) (witness : Array ℤ)
    (current : ℕ) : ℕ :=
  (compactNearColumnShell nearMask 0).foldl (fun best candidate =>
    if popcount (current ^^^ candidate) ≤ 6 ∧
        compactKernelIndexedPairWeightSum nearMask witness candidate <
          compactKernelIndexedPairWeightSum nearMask witness best then
      candidate
    else best) current

private theorem compactIndexedEmptyDescentFold_le
    (nearMask : ℕ) (witness : Array ℤ) (current : ℕ) :
    ∀ (candidates : List ℕ) (best : ℕ),
      compactKernelIndexedPairWeightSum nearMask witness
          (candidates.foldl (fun previous candidate =>
            if popcount (current ^^^ candidate) ≤ 6 ∧
                compactKernelIndexedPairWeightSum nearMask witness candidate <
                  compactKernelIndexedPairWeightSum nearMask witness previous then
              candidate
            else previous) best) ≤
        compactKernelIndexedPairWeightSum nearMask witness best := by
  intro candidates
  induction candidates with
  | nil =>
      intro best
      exact le_rfl
  | cons candidate candidates ih =>
      intro best
      simp only [List.foldl_cons]
      by_cases himproves : popcount (current ^^^ candidate) ≤ 6 ∧
          compactKernelIndexedPairWeightSum nearMask witness candidate <
            compactKernelIndexedPairWeightSum nearMask witness best
      · rw [if_pos himproves]
        exact le_trans (ih candidate) (le_of_lt himproves.2)
      · rw [if_neg himproves]
        exact ih best

/-- One local-descent step never increases the indexed pair value. -/
theorem compactIndexedEmptyDescentStep_le (nearMask : ℕ)
    (witness : Array ℤ) (current : ℕ) :
    compactKernelIndexedPairWeightSum nearMask witness
        (compactIndexedEmptyDescentStep nearMask witness current) ≤
      compactKernelIndexedPairWeightSum nearMask witness current := by
  exact compactIndexedEmptyDescentFold_le nearMask witness current
    (compactNearColumnShell nearMask 0) current

/-- Iterate local descent until it stabilizes, with a fixed guard well above
the depth observed in the committed corpus. -/
def compactIndexedEmptyDescentAux (nearMask : ℕ) (witness : Array ℤ) :
    ℕ → ℕ → ℕ
  | 0, current => current
  | fuel + 1, current =>
      let next := compactIndexedEmptyDescentStep nearMask witness current
      if next = current then current
      else compactIndexedEmptyDescentAux nearMask witness fuel next

/-- Every finite descent run is nonincreasing from its initial column. -/
theorem compactIndexedEmptyDescentAux_le (nearMask : ℕ)
    (witness : Array ℤ) : ∀ (fuel current : ℕ),
    compactKernelIndexedPairWeightSum nearMask witness
        (compactIndexedEmptyDescentAux nearMask witness fuel current) ≤
      compactKernelIndexedPairWeightSum nearMask witness current := by
  intro fuel
  induction fuel with
  | zero =>
      intro current
      exact le_rfl
  | succ fuel ih =>
      intro current
      rw [compactIndexedEmptyDescentAux]
      let next := compactIndexedEmptyDescentStep nearMask witness current
      split
      · rename_i hstable
        exact le_rfl
      · exact le_trans (ih next)
          (compactIndexedEmptyDescentStep_le nearMask witness current)

/-- A data-free empty-shell candidate: start at the enumerator's first column
and descend through radius-three exchanges. -/
def compactIndexedEmptyCandidate (nearMask : ℕ) (witness : Array ℤ) : ℕ :=
  compactIndexedEmptyDescentAux nearMask witness 25
    (compactIndexedEmptyStart nearMask)

/-- The empty-shell lower-bound candidate with fixed gap four. Soundness uses
the universal lower-bound proposition below. -/
def compactIndexedEmptyCandidateLowerBound (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  compactKernelIndexedPairWeightSum nearMask witness
      (compactIndexedEmptyCandidate nearMask witness) - 4

/-- The start-column lower estimate is cheap to evaluate and bounds the final
descent estimate from above. -/
def compactIndexedEmptyStartLowerBound (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  compactKernelIndexedPairWeightSum nearMask witness
      (compactIndexedEmptyStart nearMask) - 4

theorem compactIndexedEmptyCandidateLowerBound_le_start
    (nearMask : ℕ) (witness : Array ℤ) :
    compactIndexedEmptyCandidateLowerBound nearMask witness ≤
      compactIndexedEmptyStartLowerBound nearMask witness := by
  rw [compactIndexedEmptyCandidateLowerBound,
    compactIndexedEmptyStartLowerBound, compactIndexedEmptyCandidate]
  have hle := compactIndexedEmptyDescentAux_le nearMask witness 25
    (compactIndexedEmptyStart nearMask)
  omega

/-- Semantic validity condition for the mined empty-shell lower bound. -/
def CompactIndexedEmptyCandidateBound (nearMask : ℕ)
    (witness : Array ℤ) : Prop :=
  ∀ columnMask,
    IsCompactNearColumn nearMask 0 columnMask →
      compactIndexedEmptyCandidateLowerBound nearMask witness ≤
        compactKernelIndexedPairWeightSum nearMask witness columnMask

/-- Endpoint weights using local descent only for the large empty shell and
the exact internal minimum for the other twenty-four endpoint shells. -/
def compactIndexedHybridEndpointWeight (nearMask : ℕ) (witness : Array ℤ)
    (endpoint : CompactEndpointIndex nearMask) : ℤ :=
  if endpoint = compactEmptyEndpointIndex nearMask then
    -compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
      compactIndexedEmptyCandidateLowerBound nearMask witness
  else compactIndexedCanonicalEndpointWeight nearMask witness endpoint

theorem compactIndexedHybridEndpointWeight_nonnegativeSlack
    (nearMask : ℕ) (witness : Array ℤ)
    (hbound : CompactIndexedEmptyCandidateBound nearMask witness)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ)
    (hcolumn : IsCompactNearColumn nearMask
      (compactEndpointMaskAt nearMask endpoint) columnMask) :
    0 ≤ compactIndexedHybridEndpointWeight nearMask witness endpoint +
      compactEndpointCoefficient (compactEndpointMaskAt nearMask endpoint) *
        compactKernelIndexedPairWeightSum nearMask witness columnMask := by
  by_cases hempty : endpoint = compactEmptyEndpointIndex nearMask
  · subst endpoint
    have hlower := hbound columnMask (by simpa using hcolumn)
    have hcoefficient :
        0 ≤ compactEndpointCoefficient
          (compactEndpointMaskAt nearMask (compactEmptyEndpointIndex nearMask)) := by
      simp [compactEndpointCoefficient]
    rw [compactIndexedHybridEndpointWeight, if_pos rfl]
    nlinarith [mul_le_mul_of_nonneg_left hlower hcoefficient]
  · rw [compactIndexedHybridEndpointWeight, if_neg hempty]
    exact compactIndexedCanonicalEndpointWeight_nonnegativeSlack nearMask witness
      endpoint columnMask (isCompactNearColumn_mem_shell hcolumn)

theorem compactKernelFunctionalFarkasColumnSlack_eq
    (nearMask : ℕ) (endpointWeights : Array ℤ)
    (pairWeight : ℕ × ℕ → ℤ)
    (endpoint : CompactEndpointIndex nearMask) (columnMask : ℕ) :
    compactKernelFunctionalFarkasColumnSlack nearMask endpointWeights pairWeight
        endpoint columnMask =
      compactFunctionalFarkasColumnSlack nearMask endpointWeights pairWeight
        endpoint columnMask := by
  rw [compactKernelFunctionalFarkasColumnSlack,
    compactFunctionalFarkasColumnSlack]
  apply congrArg₂ (· + ·) rfl
  apply congrArg₂ (· * ·) rfl
  let pairValue : ℕ × ℕ → ℤ := fun vertices =>
    if columnMask.testBit vertices.1 && columnMask.testBit vertices.2 then
      pairWeight vertices
    else 0
  change _ = ∑ pair : CompactPairIndex nearMask,
    pairValue ((compactIntersectionOnePairs nearMask).getD pair.val (0, 0))
  rw [sum_fin_getD_eq_sum_map]
  dsimp only [pairValue]
  rw [compactIntersectionOnePairs, sum_map_ite_eq_sum_filter,
    List.filter_comm]
  rw [← compactListPairs_filter]

/-- Sparse integer matrix of the compact fractional feasibility problem. -/
def compactFractionalMatrix (nearMask : ℕ) :
    Matrix (CompactFractionalRow nearMask)
      (CompactFractionalColumn nearMask) ℤ :=
  fun row column =>
    match row with
    | .inl endpoint => if endpoint = column.1 then 1 else 0
    | .inr pair =>
        let vertices := compactIntersectionOnePairAt nearMask pair
        if column.2.1.val.testBit vertices.1 &&
            column.2.1.val.testBit vertices.2 then
          compactEndpointCoefficient
            (compactEndpointMaskAt nearMask column.1)
        else 0

/-- Right-hand side: one for normalization and three for concurrence. -/
def compactFractionalRhs (nearMask : ℕ) : CompactFractionalRow nearMask → ℤ
  | .inl _ => 1
  | .inr _ => 3

/-- Interpret a generated list in normalization-then-concurrence row order. -/
def compactFarkasVector (nearMask : ℕ) (witness : Array ℤ) :
    CompactFractionalRow nearMask → ℤ
  | .inl endpoint => compactWitnessAt witness endpoint.val
  | .inr pair => compactWitnessAt witness
      ((compactEndpointMasks nearMask).length + pair.val)

/-- Interpret generated functional pair weights as a Farkas vector. -/
def compactFunctionalFarkasVector (nearMask : ℕ)
    (endpointWeights : Array ℤ) (pairWeight : ℕ × ℕ → ℤ) :
    CompactFractionalRow nearMask → ℤ
  | .inl endpoint => compactWitnessAt endpointWeights endpoint.val
  | .inr pair => pairWeight (compactIntersectionOnePairAt nearMask pair)

/-- Exact `b·Y` value for generated functional pair weights. -/
def compactFunctionalFarkasRhsDot (nearMask : ℕ)
    (endpointWeights : Array ℤ) (pairWeight : ℕ × ℕ → ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactWitnessAt endpointWeights endpoint.val) +
    3 * ∑ pair : CompactPairIndex nearMask,
      pairWeight (compactIntersectionOnePairAt nearMask pair)

/-- The canonical Farkas vector determined solely by its pair weights. -/
def compactCanonicalFarkasVector (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) : CompactFractionalRow nearMask → ℤ
  | .inl endpoint => compactCanonicalEndpointWeight nearMask pairWeight endpoint
  | .inr pair => pairWeight (compactIntersectionOnePairAt nearMask pair)

/-- Exact `b·Y` value of the canonical pair-weight separator. -/
def compactCanonicalFarkasRhsDot (nearMask : ℕ)
    (pairWeight : ℕ × ℕ → ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactCanonicalEndpointWeight nearMask pairWeight endpoint) +
    3 * ∑ pair : CompactPairIndex nearMask,
      pairWeight (compactIntersectionOnePairAt nearMask pair)

/-- Canonical Farkas vector reconstructed from an indexed pair-weight array. -/
def compactIndexedCanonicalFarkasVector (nearMask : ℕ) (witness : Array ℤ) :
    CompactFractionalRow nearMask → ℤ
  | .inl endpoint =>
      compactIndexedCanonicalEndpointWeight nearMask witness endpoint
  | .inr pair => compactWitnessAt witness pair.val

/-- Exact `b·Y` value after canonical reconstruction from indexed pairs. -/
def compactIndexedCanonicalFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactIndexedCanonicalEndpointWeight nearMask witness endpoint) +
    3 * ∑ pair : CompactPairIndex nearMask,
      compactWitnessAt witness pair.val

/-- The indexed Farkas vector using the mined empty-shell lower bound. -/
def compactIndexedHybridFarkasVector (nearMask : ℕ) (witness : Array ℤ) :
    CompactFractionalRow nearMask → ℤ
  | .inl endpoint => compactIndexedHybridEndpointWeight nearMask witness endpoint
  | .inr pair => compactWitnessAt witness pair.val

/-- Exact right-hand-side dot product for the hybrid indexed vector. -/
def compactIndexedHybridFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  (∑ endpoint : CompactEndpointIndex nearMask,
      compactIndexedHybridEndpointWeight nearMask witness endpoint) +
    3 * ∑ pair : CompactPairIndex nearMask,
      compactWitnessAt witness pair.val

/-- Kernel-oriented hybrid right-hand-side dot product. -/
def compactKernelIndexedHybridFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint).foldl
      (fun total endpoint => total +
        compactIndexedHybridEndpointWeight nearMask witness endpoint) 0 +
    3 * (List.range (compactIntersectionOnePairs nearMask).length).foldl
      (fun total pairIndex => total + compactWitnessAt witness pairIndex) 0

/-- Kernel-oriented canonical right-hand-side dot product. -/
def compactKernelIndexedCanonicalFarkasRhsDot (nearMask : ℕ)
    (witness : Array ℤ) : ℤ :=
  (List.ofFn fun endpoint : CompactEndpointIndex nearMask => endpoint).foldl
      (fun total endpoint => total +
        compactIndexedCanonicalEndpointWeight nearMask witness endpoint) 0 +
    3 * (List.range (compactIntersectionOnePairs nearMask).length).foldl
      (fun total pairIndex => total + compactWitnessAt witness pairIndex) 0

theorem compactKernelIndexedCanonicalFarkasRhsDot_eq (nearMask : ℕ)
    (witness : Array ℤ) :
    compactKernelIndexedCanonicalFarkasRhsDot nearMask witness =
      compactIndexedCanonicalFarkasRhsDot nearMask witness := by
  rw [compactKernelIndexedCanonicalFarkasRhsDot,
    compactIndexedCanonicalFarkasRhsDot, foldl_int_add_eq_sum_map,
    foldl_int_add_eq_sum_map, zero_add, zero_add,
    list_sum_map_range_eq_sum_fin]
  rw [List.map_ofFn, List.sum_ofFn]
  simp

theorem compactKernelIndexedHybridFarkasRhsDot_eq (nearMask : ℕ)
    (witness : Array ℤ) :
    compactKernelIndexedHybridFarkasRhsDot nearMask witness =
      compactIndexedHybridFarkasRhsDot nearMask witness := by
  rw [compactKernelIndexedHybridFarkasRhsDot,
    compactIndexedHybridFarkasRhsDot, foldl_int_add_eq_sum_map,
    foldl_int_add_eq_sum_map, zero_add, zero_add,
    list_sum_map_range_eq_sum_fin]
  rw [List.map_ofFn, List.sum_ofFn]
  simp

theorem integerDot_compactFarkasVector_matrixColumn
    (nearMask : ℕ) (witness : Array ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot (compactFarkasVector nearMask witness)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactFarkasColumnSlack nearMask witness column.1 column.2.1 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type, compactFarkasVector,
    compactFractionalMatrix, compactFarkasColumnSlack]
  rw [Finset.sum_eq_single column.1]
  · simp only [if_pos, mul_one]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro pair _
    split_ifs <;>
      (simp_all [compactFarkasPairTerm, compactIntersectionOnePairAt] <;> ring)
  · intro endpoint _ hne
    simp [hne]
  · simp

theorem integerDot_compactFarkasVector_rhs
    (nearMask : ℕ) (witness : Array ℤ) :
    SRG266.integerDot (compactFarkasVector nearMask witness)
        (compactFractionalRhs nearMask) =
      compactFarkasRhsDot nearMask witness := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type, compactFarkasVector,
    compactFractionalRhs, compactFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem integerDot_compactFunctionalFarkasVector_matrixColumn
    (nearMask : ℕ) (endpointWeights : Array ℤ)
    (pairWeight : ℕ × ℕ → ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot
        (compactFunctionalFarkasVector nearMask endpointWeights pairWeight)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactFunctionalFarkasColumnSlack nearMask endpointWeights pairWeight
        column.1 column.2.1 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactFunctionalFarkasVector, compactFractionalMatrix,
    compactFunctionalFarkasColumnSlack]
  rw [Finset.sum_eq_single column.1]
  · simp only [if_pos, mul_one]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro pair _
    split_ifs <;>
      (simp_all [compactIntersectionOnePairAt] <;> ring)
  · intro endpoint _ hne
    simp [hne]
  · simp

theorem integerDot_compactFunctionalFarkasVector_rhs
    (nearMask : ℕ) (endpointWeights : Array ℤ)
    (pairWeight : ℕ × ℕ → ℤ) :
    SRG266.integerDot
        (compactFunctionalFarkasVector nearMask endpointWeights pairWeight)
        (compactFractionalRhs nearMask) =
      compactFunctionalFarkasRhsDot nearMask endpointWeights pairWeight := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactFunctionalFarkasVector, compactFractionalRhs,
    compactFunctionalFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem integerDot_compactCanonicalFarkasVector_matrixColumn
    (nearMask : ℕ) (pairWeight : ℕ × ℕ → ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot (compactCanonicalFarkasVector nearMask pairWeight)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactCanonicalEndpointWeight nearMask pairWeight column.1 +
        compactEndpointCoefficient (compactEndpointMaskAt nearMask column.1) *
          ∑ pair : CompactPairIndex nearMask,
            let vertices := compactIntersectionOnePairAt nearMask pair
            if column.2.1.val.testBit vertices.1 &&
                column.2.1.val.testBit vertices.2 then
              pairWeight vertices
            else 0 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactCanonicalFarkasVector, compactFractionalMatrix]
  rw [Finset.sum_eq_single column.1]
  · simp only [if_pos, mul_one]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro pair _
    split_ifs <;>
      (simp_all [compactIntersectionOnePairAt] <;> ring)
  · intro endpoint _ hne
    simp [hne]
  · simp

theorem integerDot_compactCanonicalFarkasVector_rhs
    (nearMask : ℕ) (pairWeight : ℕ × ℕ → ℤ) :
    SRG266.integerDot (compactCanonicalFarkasVector nearMask pairWeight)
        (compactFractionalRhs nearMask) =
      compactCanonicalFarkasRhsDot nearMask pairWeight := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactCanonicalFarkasVector, compactFractionalRhs,
    compactCanonicalFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem integerDot_compactIndexedCanonicalFarkasVector_matrixColumn
    (nearMask : ℕ) (witness : Array ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot
        (compactIndexedCanonicalFarkasVector nearMask witness)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactIndexedCanonicalEndpointWeight nearMask witness column.1 +
        compactEndpointCoefficient (compactEndpointMaskAt nearMask column.1) *
          compactIndexedPairWeightSum nearMask witness column.2.1 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedCanonicalFarkasVector, compactFractionalMatrix,
    compactIndexedPairWeightSum]
  rw [Finset.sum_eq_single column.1]
  · simp only [if_pos, mul_one]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro pair _
    split_ifs <;>
      (simp_all [compactIntersectionOnePairAt] <;> ring)
  · intro endpoint _ hne
    simp [hne]
  · simp

theorem integerDot_compactIndexedCanonicalFarkasVector_rhs
    (nearMask : ℕ) (witness : Array ℤ) :
    SRG266.integerDot
        (compactIndexedCanonicalFarkasVector nearMask witness)
        (compactFractionalRhs nearMask) =
      compactIndexedCanonicalFarkasRhsDot nearMask witness := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedCanonicalFarkasVector, compactFractionalRhs,
    compactIndexedCanonicalFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

theorem integerDot_compactIndexedHybridFarkasVector_matrixColumn
    (nearMask : ℕ) (witness : Array ℤ)
    (column : CompactFractionalColumn nearMask) :
    SRG266.integerDot
        (compactIndexedHybridFarkasVector nearMask witness)
        (fun row => compactFractionalMatrix nearMask row column) =
      compactIndexedHybridEndpointWeight nearMask witness column.1 +
        compactEndpointCoefficient (compactEndpointMaskAt nearMask column.1) *
          compactIndexedPairWeightSum nearMask witness column.2.1 := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedHybridFarkasVector, compactFractionalMatrix,
    compactIndexedPairWeightSum]
  rw [Finset.sum_eq_single column.1]
  · simp only [if_pos, mul_one]
    rw [Finset.mul_sum]
    apply congrArg₂ (· + ·) rfl
    apply Finset.sum_congr rfl
    intro pair _
    split_ifs <;>
      (simp_all [compactIntersectionOnePairAt] <;> ring)
  · intro endpoint _ hne
    simp [hne]
  · simp

theorem integerDot_compactIndexedHybridFarkasVector_rhs
    (nearMask : ℕ) (witness : Array ℤ) :
    SRG266.integerDot
        (compactIndexedHybridFarkasVector nearMask witness)
        (compactFractionalRhs nearMask) =
      compactIndexedHybridFarkasRhsDot nearMask witness := by
  classical
  simp only [SRG266.integerDot, Fintype.sum_sum_type,
    compactIndexedHybridFarkasVector, compactFractionalRhs,
    compactIndexedHybridFarkasRhsDot, mul_one]
  rw [Finset.mul_sum]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro pair _
  ring

/-- The compact rational feasibility problem associated with a normal form. -/
abbrev CompactFractionalNearFrame (nearMask : ℕ) : Prop :=
  ∃ mass : CompactFractionalColumn nearMask → ℚ,
    (∀ column, 0 ≤ mass column) ∧
    ∀ row, ∑ column,
      (compactFractionalMatrix nearMask row column : ℚ) * mass column =
        (compactFractionalRhs nearMask row : ℚ)

/-- Absence of a compact fractional near frame. -/
abbrev NoCompactFractionalNearFrame (nearMask : ℕ) : Prop :=
  ¬CompactFractionalNearFrame nearMask

/-- A sparse separator expressed by the executable slack functions rules out
the compact rational feasibility problem. -/
theorem noCompactFractionalNearFrame_of_farkas
    (nearMask : ℕ) (witness : Array ℤ)
    (hcolumns : ∀ endpoint : CompactEndpointIndex nearMask,
      ∀ columnMask ∈ compactNearColumnShell nearMask
        (compactEndpointMaskAt nearMask endpoint),
        0 ≤ compactFarkasColumnSlack nearMask witness endpoint columnMask)
    (hrhs : compactFarkasRhsDot nearMask witness < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactFarkasVector nearMask witness)
  constructor
  · intro column
    rw [integerDot_compactFarkasVector_matrixColumn]
    exact hcolumns column.1 column.2.1
      (isCompactNearColumn_mem_shell column.2.2)
  · rw [integerDot_compactFarkasVector_rhs]
    exact hrhs

/-- A functional separator rules out the compact rational feasibility problem. -/
theorem noCompactFractionalNearFrame_of_functionalFarkas
    (nearMask : ℕ) (endpointWeights : Array ℤ)
    (pairWeight : ℕ × ℕ → ℤ)
    (hcolumns : ∀ endpoint : CompactEndpointIndex nearMask,
      ∀ columnMask ∈ compactNearColumnShell nearMask
        (compactEndpointMaskAt nearMask endpoint),
        0 ≤ compactKernelFunctionalFarkasColumnSlack nearMask endpointWeights
          pairWeight endpoint columnMask)
    (hrhs : compactFunctionalFarkasRhsDot nearMask endpointWeights pairWeight < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactFunctionalFarkasVector nearMask endpointWeights pairWeight)
  constructor
  · intro column
    rw [integerDot_compactFunctionalFarkasVector_matrixColumn,
      ← compactKernelFunctionalFarkasColumnSlack_eq]
    exact hcolumns column.1 column.2.1
      (isCompactNearColumn_mem_shell column.2.2)
  · rw [integerDot_compactFunctionalFarkasVector_rhs]
    exact hrhs

/-- Pair weights whose canonical normalization has negative right-hand side
rule out the compact rational feasibility problem.  All column inequalities
follow internally from the shell minima, so no column-slack certificate is
an external input. -/
theorem noCompactFractionalNearFrame_of_canonicalPairFarkas
    (nearMask : ℕ) (pairWeight : ℕ × ℕ → ℤ)
    (hrhs : compactCanonicalFarkasRhsDot nearMask pairWeight < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactCanonicalFarkasVector nearMask pairWeight)
  constructor
  · intro column
    rw [integerDot_compactCanonicalFarkasVector_matrixColumn,
      ← compactKernelPairWeightSum_eq]
    exact compactCanonicalEndpointWeight_nonnegativeSlack nearMask pairWeight
      column.1 column.2.1 (isCompactNearColumn_mem_shell column.2.2)
  · rw [integerDot_compactCanonicalFarkasVector_rhs]
    exact hrhs

/-- Indexed pair weights suffice: endpoint weights and all column slacks are
reconstructed internally from shell minima. -/
theorem noCompactFractionalNearFrame_of_indexedCanonicalPairFarkas
    (nearMask : ℕ) (witness : Array ℤ)
    (hrhs : compactKernelIndexedCanonicalFarkasRhsDot nearMask witness < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactIndexedCanonicalFarkasVector nearMask witness)
  constructor
  · intro column
    rw [integerDot_compactIndexedCanonicalFarkasVector_matrixColumn,
      ← compactKernelIndexedPairWeightSum_eq]
    exact compactIndexedCanonicalEndpointWeight_nonnegativeSlack nearMask witness
      column.1 column.2.1 (isCompactNearColumn_mem_shell column.2.2)
  · rw [integerDot_compactIndexedCanonicalFarkasVector_rhs,
      ← compactKernelIndexedCanonicalFarkasRhsDot_eq]
    exact hrhs

/-- The data-free local-search normalization also suffices.  Its only
noncomputational premise is the semantic empty-shell lower bound, intended for
proof by a verified bit-vector circuit; no minimum or endpoint coefficient is
supplied as certificate data. -/
theorem noCompactFractionalNearFrame_of_indexedHybridPairFarkas
    (nearMask : ℕ) (witness : Array ℤ)
    (hbound : CompactIndexedEmptyCandidateBound nearMask witness)
    (hrhs : compactKernelIndexedHybridFarkasRhsDot nearMask witness < 0) :
    NoCompactFractionalNearFrame nearMask := by
  apply SRG266.no_nonnegative_rational_solution_of_integer_farkas
    (compactFractionalMatrix nearMask) (compactFractionalRhs nearMask)
    (compactIndexedHybridFarkasVector nearMask witness)
  constructor
  · intro column
    rw [integerDot_compactIndexedHybridFarkasVector_matrixColumn,
      ← compactKernelIndexedPairWeightSum_eq]
    exact compactIndexedHybridEndpointWeight_nonnegativeSlack nearMask witness
      hbound column.1 column.2.1 column.2.2
  · rw [integerDot_compactIndexedHybridFarkasVector_rhs,
      ← compactKernelIndexedHybridFarkasRhsDot_eq]
    exact hrhs

/-- Search internally for the mined `(+1,+1,+1,-1)` Hall cut.  The positive
set ranges over the 56 triples and the negative vertex is required to lie
outside it. -/
def compactHasHallDeficientEndpointShell (nearMask : ℕ) : Bool :=
  (List.finRange (compactEndpointMasks nearMask).length).reverse.any fun endpoint =>
    (List.finRange 56).any fun positive =>
      (List.finRange 8).any fun negative =>
        (!(compactTripleCodeAt positive.val).testBit negative.val) &&
          compactHallDeficient nearMask (compactEndpointMaskAt nearMask endpoint)
            (compactTripleCodeAt positive.val) negative

/-- The exceptional weighted Hall orbit: one vertex has weight `4`, three
have weight `1`, two have weight `-2`, and the remaining two have weight
zero. -/
def compactExceptionalHallWeight (highVertex : Fin 8)
    (positiveMask negativeMask : ℕ) (vertex : Fin 8) : ℤ :=
  (if vertex = highVertex then 4 else 0) +
    (if positiveMask.testBit vertex.val then 1 else 0) -
    (if negativeMask.testBit vertex.val then 2 else 0)

/-- Kernel-oriented weighted capacity over a duplicate-free item list. -/
def compactWeightedHallListCapacity (items : List ℕ)
    (vertexWeight : Fin 8 → ℤ) : ℤ :=
  items.foldl (fun total code =>
    total + max 0 (compactWeightedHallRowValue vertexWeight code)) 0

theorem compactWeightedHallListCapacity_eq (items : List ℕ)
    (hitems : items.Nodup) (vertexWeight : Fin 8 → ℤ) :
    compactWeightedHallListCapacity items vertexWeight =
      ∑ code ∈ items.toFinset,
        max 0 (compactWeightedHallRowValue vertexWeight code) := by
  rw [compactWeightedHallListCapacity, foldl_int_add_eq_sum_map]
  simpa using (List.sum_toFinset
      (fun code => max 0 (compactWeightedHallRowValue vertexWeight code))
      hitems).symm

/-- List-oriented weighted Hall test used inside the small exceptional orbit. -/
def compactWeightedHallListDeficient (endpointMask : ℕ) (items : List ℕ)
    (vertexWeight : Fin 8 → ℤ) : Bool :=
  decide (compactWeightedHallListCapacity items vertexWeight <
    compactWeightedHallDemand endpointMask vertexWeight)

theorem compactWeightedHallDeficient_of_list
    (nearMask endpointMask : ℕ) (vertexWeight : Fin 8 → ℤ)
    (hcheck : compactWeightedHallListDeficient endpointMask
      (compactNearColumnItems nearMask endpointMask) vertexWeight = true) :
    compactWeightedHallDeficient nearMask endpointMask vertexWeight = true := by
  rw [compactWeightedHallListDeficient, decide_eq_true_eq] at hcheck
  rw [compactWeightedHallDeficient, decide_eq_true_eq,
    compactWeightedHallAvailableCapacity,
    ← compactWeightedHallListCapacity_eq
      (compactNearColumnItems nearMask endpointMask)
      (compactNearColumnItems_nodup nearMask endpointMask)]
  exact hcheck

/-- Search the second mined Hall orbit.  The two endpoint vertices receive
weight zero; the six active vertices are partitioned into weights `4`, three
weights `1`, and two weights `-2`. -/
def compactHasExceptionalHallDeficientEndpointShell (nearMask : ℕ) : Bool :=
  (List.finRange (compactEndpointMasks nearMask).length).reverse.any fun endpoint =>
    (List.finRange 8).any fun highVertex =>
      (List.finRange 56).any fun positive =>
          let endpointMask := compactEndpointMaskAt nearMask endpoint
          let items := compactNearColumnItems nearMask endpointMask
          let positiveMask := compactTripleCodeAt positive.val
          let highMask := 2 ^ highVertex.val
          let negativeMask := 255 ^^^ endpointMask ^^^ positiveMask ^^^ highMask
          decide (popcount endpointMask = 2 ∧
            positiveMask &&& endpointMask = 0 ∧
            !positiveMask.testBit highVertex.val ∧
            !endpointMask.testBit highVertex.val) &&
          compactWeightedHallListDeficient endpointMask items
            (compactExceptionalHallWeight highVertex positiveMask negativeMask)

/-- A discovered Hall-deficient endpoint shell rules out the compact
feasibility problem without running the exact-demand shell DFS. -/
theorem noCompactFractionalNearFrame_of_hasHallDeficientEndpointShell
    (nearMask : ℕ)
    (hcheck : compactHasHallDeficientEndpointShell nearMask = true) :
    NoCompactFractionalNearFrame nearMask := by
  rw [compactHasHallDeficientEndpointShell, List.any_eq_true] at hcheck
  rcases hcheck with ⟨endpoint, -, hpositive⟩
  rw [List.any_eq_true] at hpositive
  rcases hpositive with ⟨positive, -, hnegative⟩
  rw [List.any_eq_true] at hnegative
  rcases hnegative with ⟨negative, -, hcut⟩
  rw [Bool.and_eq_true] at hcut
  rintro ⟨mass, -, hequations⟩
  have heq := hequations (Sum.inl endpoint)
  have hzero : (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inl endpoint) column : ℚ) *
        mass column) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨otherEndpoint, column⟩ _
    by_cases hsame : endpoint = otherEndpoint
    · subst otherEndpoint
      exact False.elim <|
        not_isCompactNearColumn_of_compactHallDeficient nearMask
          (compactEndpointMaskAt nearMask endpoint)
          (compactTripleCodeAt positive.val) column.val.val negative hcut.2
          column.property
    · simp [compactFractionalMatrix, hsame]
  rw [hzero] at heq
  norm_num [compactFractionalRhs] at heq

/-- The exceptional weighted Hall orbit rules out the remaining empty-shell
normal forms without exact-demand enumeration. -/
theorem noCompactFractionalNearFrame_of_hasExceptionalHallDeficientEndpointShell
    (nearMask : ℕ)
    (hcheck : compactHasExceptionalHallDeficientEndpointShell nearMask = true) :
    NoCompactFractionalNearFrame nearMask := by
  rw [compactHasExceptionalHallDeficientEndpointShell, List.any_eq_true] at hcheck
  rcases hcheck with ⟨endpoint, -, hhigh⟩
  rw [List.any_eq_true] at hhigh
  rcases hhigh with ⟨highVertex, -, hpositive⟩
  rw [List.any_eq_true] at hpositive
  rcases hpositive with ⟨positive, -, hcut⟩
  rw [Bool.and_eq_true] at hcut
  rintro ⟨mass, -, hequations⟩
  have heq := hequations (Sum.inl endpoint)
  have hzero : (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inl endpoint) column : ℚ) *
        mass column) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨otherEndpoint, column⟩ _
    by_cases hsame : endpoint = otherEndpoint
    · subst otherEndpoint
      exact False.elim <|
        not_isCompactNearColumn_of_compactWeightedHallDeficient nearMask
          (compactEndpointMaskAt nearMask endpoint) column.val.val
          (compactExceptionalHallWeight highVertex
            (compactTripleCodeAt positive.val)
            (255 ^^^ compactEndpointMaskAt nearMask endpoint ^^^
              compactTripleCodeAt positive.val ^^^ 2 ^ highVertex.val))
          (compactWeightedHallDeficient_of_list nearMask
            (compactEndpointMaskAt nearMask endpoint) _ hcut.2) column.property
    · simp [compactFractionalMatrix, hsame]
  rw [hzero] at heq
  norm_num [compactFractionalRhs] at heq

/-- Whether the compact normal form has an empty endpoint shell.  Reversing
the endpoint order visits the sixteen small two-endpoint shells before the
larger singleton and empty-endpoint shells. -/
def compactHasEmptyEndpointShell (nearMask : ℕ) : Bool :=
  (List.finRange (compactEndpointMasks nearMask).length).reverse.any fun endpoint =>
    compactNearColumnShell nearMask
      (compactEndpointMaskAt nearMask endpoint) == []

/-- An internally discovered empty shell rules out the compact feasibility
problem; no generated shell index is needed. -/
theorem noCompactFractionalNearFrame_of_hasEmptyEndpointShell
    (nearMask : ℕ) (hcheck : compactHasEmptyEndpointShell nearMask = true) :
    NoCompactFractionalNearFrame nearMask := by
  rw [compactHasEmptyEndpointShell, List.any_eq_true] at hcheck
  rcases hcheck with ⟨endpoint, -, hempty⟩
  rw [beq_iff_eq] at hempty
  rintro ⟨mass, -, hequations⟩
  have heq := hequations (Sum.inl endpoint)
  have hzero : (∑ column : CompactFractionalColumn nearMask,
      (compactFractionalMatrix nearMask (Sum.inl endpoint) column : ℚ) *
        mass column) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨otherEndpoint, column⟩ _
    by_cases hsame : endpoint = otherEndpoint
    · subst otherEndpoint
      have hfalse : (column : ℕ) ∈ ([] : List ℕ) := by
        simpa [hempty] using isCompactNearColumn_mem_shell column.property
      exact False.elim (List.not_mem_nil hfalse)
    · simp [compactFractionalMatrix, hsame]
  rw [hzero] at heq
  norm_num [compactFractionalRhs] at heq

/-- Generated data for one representative. -/
inductive FractionalNearFrameCertificate where
  /-- A shell which must carry probability mass is empty.  The checker
  discovers the shell internally. -/
  | emptyShell
  /-- Indexed integer pair weights determining the canonical separator. -/
  | farkas (pairWeights : Array ℤ)
deriving Repr

/-- Boolean exact checker for one normal-form certificate. -/
def checkFractionalNearFrameCertificate
    (nearMask : ℕ) : FractionalNearFrameCertificate → Bool
  | .emptyShell =>
      compactHasHallDeficientEndpointShell nearMask ||
        (compactHasExceptionalHallDeficientEndpointShell nearMask ||
          compactHasEmptyEndpointShell nearMask)
  | .farkas witness =>
      decide (compactKernelIndexedCanonicalFarkasRhsDot nearMask witness < 0)

/-- Soundness of the executable certificate checker. -/
theorem checkFractionalNearFrameCertificate_sound
    {nearMask : ℕ} {certificate : FractionalNearFrameCertificate}
    (hcheck : checkFractionalNearFrameCertificate nearMask certificate = true) :
    NoCompactFractionalNearFrame nearMask := by
  cases certificate with
  | emptyShell =>
      rw [checkFractionalNearFrameCertificate, Bool.or_eq_true] at hcheck
      rcases hcheck with hhall | hempty
      · exact noCompactFractionalNearFrame_of_hasHallDeficientEndpointShell
          nearMask hhall
      · rw [Bool.or_eq_true] at hempty
        rcases hempty with hexceptional | hfallback
        · exact
            noCompactFractionalNearFrame_of_hasExceptionalHallDeficientEndpointShell
              nearMask hexceptional
        · exact noCompactFractionalNearFrame_of_hasEmptyEndpointShell
            nearMask hfallback
  | farkas witness =>
      apply noCompactFractionalNearFrame_of_indexedCanonicalPairFarkas
        nearMask witness
      exact of_decide_eq_true hcheck

/-- A generated `(normal form, certificate)` entry is internally keyed by the
same compact mask that the normal-form cover uses. -/
structure FractionalNearFrameCertificateEntry where
  nearMask : ℕ
  certificate : FractionalNearFrameCertificate
deriving Repr

def checkFractionalNearFrameCertificateEntry
    (entry : FractionalNearFrameCertificateEntry) : Bool :=
  checkFractionalNearFrameCertificate entry.nearMask entry.certificate

end SRG266.QuasiSymmetric
