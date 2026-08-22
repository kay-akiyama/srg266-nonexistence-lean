/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Certificates.A15ProjectorData.Profile00
import SRG266.Certificates.A15ProjectorData.Profile01
import SRG266.Certificates.A15ProjectorData.Profile08
import SRG266.Certificates.A15ProjectorData.Profile12
import SRG266.Hosts.A15ParityTransport

/-!
# Base facts for A15 final transport

The centroid identifications are proved coordinatewise.  The two generic
transport lemmas remove dependent casts before the finite orbit predicates
are checked in separate profile modules.
-/

namespace SRG266

set_option maxRecDepth 100000

theorem a15SubsetContains_transport
    {d e : Fin 16 → ℤ} (h : d = e)
    (s : A15EligibleIndex d) (i : Fin 16) :
    a15SubsetContains (h ▸ s) i ↔ a15SubsetContains s i := by
  subst e
  rfl

theorem a15SubsetContains_equivCast
    {d e : Fin 16 → ℤ} (h : d = e)
    (s : A15EligibleIndex d) (i : Fin 16) :
    a15SubsetContains
        (Equiv.cast (congrArg A15EligibleIndex h) s) i ↔
      a15SubsetContains s i := by
  subst e
  rfl

theorem a15ProjectorProfile00_centroidVector :
    a15ProjectorProfile00.profile.centroidVector =
      a15BinaryProfile0 := by
  funext i
  fin_cases i <;> rfl

theorem a15ProjectorProfile01_centroidVector :
    a15ProjectorProfile01.profile.centroidVector =
      a15ParityProfile1 := by
  funext i
  fin_cases i <;> rfl

theorem a15ProjectorProfile08_centroidVector :
    a15ProjectorProfile08.profile.centroidVector =
      a15ParityProfile8 := by
  funext i
  fin_cases i <;> rfl

theorem a15ProjectorProfile12_centroidVector :
    a15ProjectorProfile12.profile.centroidVector =
      a15BinaryProfile12 := by
  funext i
  fin_cases i <;> rfl

def a15FinalTransportIndex
    (block : Fin 14) (offset : Fin 130) : A15FourSubsetIndex :=
  ⟨block.1 * 130 + offset.1, by
    rw [a15FourSubsetData_size]
    omega⟩

def a15ProjectorProfile00OrbitProperty
    (i : A15FourSubsetIndex) : Prop :=
  a15Eligible a15ProjectorProfile00.profile.centroidVector i →
    (a15ProjectorProfile00.profile.indexMatches 0 i ↔
      ¬(0 : Fin 16) ∈ a15FourSubsetAsFinset i)

def a15ProjectorProfile01OrbitProperty
    (i : A15FourSubsetIndex) : Prop :=
  a15Eligible a15ProjectorProfile01.profile.centroidVector i →
    (a15ProjectorProfile01.profile.indexMatches 0 i ↔
      (15 : Fin 16) ∈ a15FourSubsetAsFinset i)

def a15ProjectorProfile08OrbitProperty
    (i : A15FourSubsetIndex) : Prop :=
  a15Eligible a15ProjectorProfile08.profile.centroidVector i →
    (a15ProjectorProfile08.profile.indexMatches 1 i ↔
      (0 : Fin 16) ∈ a15FourSubsetAsFinset i)

def a15ProjectorProfile12OrbitProperty
    (i : A15FourSubsetIndex) : Prop :=
  a15Eligible a15ProjectorProfile12.profile.centroidVector i →
    (a15ProjectorProfile12.profile.indexMatches 1 i ↔
      ¬(15 : Fin 16) ∈ a15FourSubsetAsFinset i)

end SRG266
