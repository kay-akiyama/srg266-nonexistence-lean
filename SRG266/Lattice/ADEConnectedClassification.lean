/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Lattice.ADETripodStandard

/-!
# Classification of connected positive simply-laced Cartan graphs

A connected positive Cartan graph of rank at most fifteen is a path or a
single tripod.  The path is `A`; the preceding affine-obstruction argument and
the explicit coordinate maps identify the tripod as `D`, `E6`, `E7`, or `E8`.
-/

namespace SRG266
namespace Lattice

open SimpleGraph

variable {V : Type*}

/-- Coordinate-level ADE classification of one connected Cartan graph. -/
def ConnectedADECoordinates [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ t : ADEType, t.IsRegular ∧ t.rank = Fintype.card V ∧
    ∃ coord : Fin t.rank ≃ V, ∀ i j,
      graphCartanMatrix G (coord i) (coord j) = t.gram i j

theorem connectedADECoordinates_of_dTripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    {t : ℕ} (ht : 0 < t) (g : tripodGraph 1 1 t ≃g G) :
    ConnectedADECoordinates G := by
  let e : Fin (t + 3) ≃ V := (dTripodEquiv t ht).trans g.toEquiv
  refine ⟨.D (t + 3), by simp only [ADEType.IsRegular]; omega, ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramD (t + 3) i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 1 t)
          (dTripodEquiv t ht i) (dTripodEquiv t ht j) :=
        graphCartanMatrix_apply_iso g _ _
      _ = gramD (t + 3) i j := graphCartanMatrix_dTripod t ht i j

theorem connectedADECoordinates_of_e6TripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (g : tripodGraph 1 2 2 ≃g G) : ConnectedADECoordinates G := by
  let e : Fin 6 ≃ V := e6TripodEquiv.trans g.toEquiv
  refine ⟨.E6, by simp only [ADEType.IsRegular], ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramE 6 i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 2 2)
          (e6TripodEquiv i) (e6TripodEquiv j) := graphCartanMatrix_apply_iso g _ _
      _ = gramE 6 i j := graphCartanMatrix_e6Tripod i j

theorem connectedADECoordinates_of_e7TripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (g : tripodGraph 1 2 3 ≃g G) : ConnectedADECoordinates G := by
  let e : Fin 7 ≃ V := e7TripodEquiv.trans g.toEquiv
  refine ⟨.E7, by simp only [ADEType.IsRegular], ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramE 7 i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 2 3)
          (e7TripodEquiv i) (e7TripodEquiv j) := graphCartanMatrix_apply_iso g _ _
      _ = gramE 7 i j := graphCartanMatrix_e7Tripod i j

theorem connectedADECoordinates_of_e8TripodIso
    [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (g : tripodGraph 1 2 4 ≃g G) : ConnectedADECoordinates G := by
  let e : Fin 8 ≃ V := e8TripodEquiv.trans g.toEquiv
  refine ⟨.E8, by simp only [ADEType.IsRegular], ?_, e, ?_⟩
  · simpa only [ADEType.rank, Fintype.card_fin] using Fintype.card_congr e
  · intro i j
    change graphCartanMatrix G (e i) (e j) = gramE 8 i j
    calc
      _ = graphCartanMatrix (tripodGraph 1 2 4)
          (e8TripodEquiv i) (e8TripodEquiv j) := graphCartanMatrix_apply_iso g _ _
      _ = gramE 8 i j := graphCartanMatrix_e8Tripod i j

/-- Connected positive simply-laced Cartan graphs of rank at most fifteen are
ADE, with an explicit coordinate equivalence. -/
theorem positiveCartan_connected_ADE
    [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    (hpos : IsPositiveCartan G) (hconn : G.Connected)
    (hcard : Fintype.card V ≤ 15) : ConnectedADECoordinates G := by
  classical
  by_cases hbranch : ∃ z, G.degree z = 3
  · obtain ⟨z, hz⟩ := hbranch
    obtain ⟨A₀, A₁, A₂, h₀₁, h₀₂, h₁₂, hshape⟩ :=
      exists_orientedArms_D_or_E hpos hconn hcard hz
    have hcomponents := card_puncturedComponents_eq_three hpos hconn hz
    rcases hshape with hD | hE6 | hE7 | hE8
    · unfold IsDArmTriple at hD
      rcases hD with ⟨h₀, h₁⟩ | ⟨h₀, h₂⟩ | ⟨h₁, h₂⟩
      · obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents
          A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
        rw [h₀, h₁] at g
        exact connectedADECoordinates_of_dTripodIso A₂.length_pos g
      · obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents
          A₀ A₂ A₁ h₀₂ h₀₁ h₁₂.symm
        rw [h₀, h₂] at g
        exact connectedADECoordinates_of_dTripodIso A₁.length_pos g
      · obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents
          A₁ A₂ A₀ h₁₂ h₀₁.symm h₀₂.symm
        rw [h₁, h₂] at g
        exact connectedADECoordinates_of_dTripodIso A₀.length_pos g
    · unfold IsE6ArmTriple at hE6
      rcases hE6 with ⟨h₀, h₁, h₂⟩ | ⟨h₁, h₀, h₂⟩ | ⟨h₂, h₀, h₁⟩
      · obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents
          A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
        rw [h₀, h₁, h₂] at g
        exact connectedADECoordinates_of_e6TripodIso g
      · obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents
          A₁ A₀ A₂ h₀₁.symm h₁₂ h₀₂
        rw [h₁, h₀, h₂] at g
        exact connectedADECoordinates_of_e6TripodIso g
      · obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents
          A₂ A₀ A₁ h₀₂.symm h₁₂.symm h₀₁
        rw [h₂, h₀, h₁] at g
        exact connectedADECoordinates_of_e6TripodIso g
    · unfold IsE7ArmTriple at hE7
      rcases hE7 with h | h | h | h | h | h
      · rcases h with ⟨h₀, h₁, h₂⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
        rw [h₀, h₁, h₂] at g
        exact connectedADECoordinates_of_e7TripodIso g
      · rcases h with ⟨h₀, h₂, h₁⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₀ A₂ A₁ h₀₂ h₀₁ h₁₂.symm
        rw [h₀, h₂, h₁] at g
        exact connectedADECoordinates_of_e7TripodIso g
      · rcases h with ⟨h₁, h₀, h₂⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₁ A₀ A₂ h₀₁.symm h₁₂ h₀₂
        rw [h₁, h₀, h₂] at g
        exact connectedADECoordinates_of_e7TripodIso g
      · rcases h with ⟨h₁, h₂, h₀⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₁ A₂ A₀ h₁₂ h₀₁.symm h₀₂.symm
        rw [h₁, h₂, h₀] at g
        exact connectedADECoordinates_of_e7TripodIso g
      · rcases h with ⟨h₂, h₀, h₁⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₂ A₀ A₁ h₀₂.symm h₁₂.symm h₀₁
        rw [h₂, h₀, h₁] at g
        exact connectedADECoordinates_of_e7TripodIso g
      · rcases h with ⟨h₂, h₁, h₀⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₂ A₁ A₀ h₁₂.symm h₀₂.symm h₀₁.symm
        rw [h₂, h₁, h₀] at g
        exact connectedADECoordinates_of_e7TripodIso g
    · unfold IsE8ArmTriple at hE8
      rcases hE8 with h | h | h | h | h | h
      · rcases h with ⟨h₀, h₁, h₂⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₀ A₁ A₂ h₀₁ h₀₂ h₁₂
        rw [h₀, h₁, h₂] at g
        exact connectedADECoordinates_of_e8TripodIso g
      · rcases h with ⟨h₀, h₂, h₁⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₀ A₂ A₁ h₀₂ h₀₁ h₁₂.symm
        rw [h₀, h₂, h₁] at g
        exact connectedADECoordinates_of_e8TripodIso g
      · rcases h with ⟨h₁, h₀, h₂⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₁ A₀ A₂ h₀₁.symm h₁₂ h₀₂
        rw [h₁, h₀, h₂] at g
        exact connectedADECoordinates_of_e8TripodIso g
      · rcases h with ⟨h₁, h₂, h₀⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₁ A₂ A₀ h₁₂ h₀₁.symm h₀₂.symm
        rw [h₁, h₂, h₀] at g
        exact connectedADECoordinates_of_e8TripodIso g
      · rcases h with ⟨h₂, h₀, h₁⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₂ A₀ A₁ h₀₂.symm h₁₂.symm h₀₁
        rw [h₂, h₀, h₁] at g
        exact connectedADECoordinates_of_e8TripodIso g
      · rcases h with ⟨h₂, h₁, h₀⟩
        obtain ⟨g⟩ := exists_tripodGraph_iso hpos hconn hcomponents A₂ A₁ A₀ h₁₂.symm h₀₂.symm h₀₁.symm
        rw [h₂, h₁, h₀] at g
        exact connectedADECoordinates_of_e8TripodIso g
  · have hdeg : ∀ v, G.degree v ≤ 2 := by
      intro v
      have hle := hpos.degree_le_three v
      have hne : G.degree v ≠ 3 := fun h ↦ hbranch ⟨v, h⟩
      omega
    obtain ⟨e, he⟩ := exists_A_coordinates_of_degree_le_two
      hconn hpos.isAcyclic hdeg
    letI : Nonempty V := hconn.nonempty
    refine ⟨.A (Fintype.card V), ?_, rfl, e, ?_⟩
    · simp only [ADEType.IsRegular]
      exact Fintype.card_pos
    intro i j
    change graphCartanMatrix G (e i) (e j) = gramA (Fintype.card V) i j
    exact he i j

end Lattice
end SRG266
