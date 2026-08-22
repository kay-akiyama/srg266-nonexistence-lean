/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SRG266 formalization contributors
-/
import SRG266.Hosts.E7MinedProfileData
import SRG266.Hosts.E7WeylTransportCore
import Mathlib.Data.Fin.VecNotation

/-!
# Checked Weyl compression of the 25 mined E7 profiles

Every reflection path has length at most three.  Lean checks the roots and
the exact endpoint, and separately checks that the sources cover precisely
the 25-profile mined search and the targets are precisely seven canonical
component representatives.
-/

namespace SRG266

structure E7MinedWeylCertificate where
  profile : Fin 8 → ℤ
  target : Fin 8 → ℤ
  reflections : List (Fin 8 → ℤ)

def e7MinedWeylCanonicalProfiles : List (List ℤ) :=
  [ [-2, 0, 0, 0, 0, 0, 0, 2],
    [-3, -1, -1, 1, 1, 1, 1, 1],
    [-4, 0, 0, 0, 0, 0, 2, 2],
    [-3, -3, 1, 1, 1, 1, 1, 1],
    [-5, -1, 1, 1, 1, 1, 1, 1],
    [-4, 0, 0, 0, 0, 0, 0, 4],
    [-5, -1, -1, 1, 1, 1, 1, 3] ]

def E7MinedWeylCertificate.Valid (c : E7MinedWeylCertificate) : Prop :=
  List.ofFn c.profile ∈ e7MinedComponentProfiles ∧
    List.ofFn c.target ∈ e7MinedWeylCanonicalProfiles ∧
    e7ApplyReflections c.profile c.reflections = some c.target ∧
    c.reflections.all e7ReflectionTransportCheck = true ∧
    ∀ w : E7WeightIndex,
      integerDot c.profile (e7Weight4 w) % 8 = 0

instance instDecidableE7MinedWeylCertificateValid
    (c : E7MinedWeylCertificate) : Decidable c.Valid := by
  unfold E7MinedWeylCertificate.Valid
  infer_instance

def E7MinedWeylCertificate.check (c : E7MinedWeylCertificate) : Bool :=
  decide c.Valid

theorem E7MinedWeylCertificate.valid_of_check
    (c : E7MinedWeylCertificate) (hcheck : c.check = true) : c.Valid :=
  of_decide_eq_true hcheck

def e7MinedWeylCertificates : List E7MinedWeylCertificate :=
[
  { profile := ![-5, -1, -1, 1, 1, 1, 1, 3]
    target := ![-5, -1, -1, 1, 1, 1, 1, 3]
    reflections := [] },
  { profile := ![-5, -1, 1, 1, 1, 1, 1, 1]
    target := ![-5, -1, 1, 1, 1, 1, 1, 1]
    reflections := [] },
  { profile := ![-4, -2, -2, 0, 2, 2, 2, 2]
    target := ![-5, -1, -1, 1, 1, 1, 1, 3]
    reflections := [![-1, 1, 1, 1, -1, -1, -1, 1]] },
  { profile := ![-4, -2, 0, 0, 0, 0, 2, 4]
    target := ![-5, -1, -1, 1, 1, 1, 1, 3]
    reflections := [![-1, 1, -1, 1, 1, 1, -1, -1]] },
  { profile := ![-4, -2, 0, 0, 0, 2, 2, 2]
    target := ![-5, -1, 1, 1, 1, 1, 1, 1]
    reflections := [![-1, 1, 1, 1, 1, -1, -1, -1]] },
  { profile := ![-4, 0, 0, 0, 0, 0, 0, 4]
    target := ![-4, 0, 0, 0, 0, 0, 0, 4]
    reflections := [] },
  { profile := ![-4, 0, 0, 0, 0, 0, 2, 2]
    target := ![-4, 0, 0, 0, 0, 0, 2, 2]
    reflections := [] },
  { profile := ![-3, -3, -1, -1, 1, 1, 3, 3]
    target := ![-5, -1, -1, 1, 1, 1, 1, 3]
    reflections := [![-1, 1, 1, 1, -1, -1, -1, 1],
      ![-1, 1, -1, 1, 1, 1, -1, -1]] },
  { profile := ![-3, -3, -1, 1, 1, 1, 1, 3]
    target := ![-5, -1, 1, 1, 1, 1, 1, 1]
    reflections := [![-1, 1, 1, 1, 1, -1, -1, -1],
      ![-1, 1, 1, -1, -1, 1, 1, -1]] },
  { profile := ![-3, -3, 1, 1, 1, 1, 1, 1]
    target := ![-3, -3, 1, 1, 1, 1, 1, 1]
    reflections := [] },
  { profile := ![-3, -1, -1, -1, -1, 1, 1, 5]
    target := ![-5, -1, -1, 1, 1, 1, 1, 3]
    reflections := [![-1, 1, -1, 1, 1, 1, -1, -1],
      ![-1, -1, 1, 1, 1, -1, 1, -1]] },
  { profile := ![-3, -1, -1, -1, -1, 1, 3, 3]
    target := ![-5, -1, 1, 1, 1, 1, 1, 1]
    reflections := [![0, -2, 0, 0, 0, 2, 0, 0],
      ![-1, -1, 1, 1, 1, 1, -1, -1]] },
  { profile := ![-3, -1, -1, -1, 1, 1, 1, 3]
    target := ![-4, 0, 0, 0, 0, 0, 2, 2]
    reflections := [![-1, 1, 1, 1, -1, -1, 1, -1]] },
  { profile := ![-3, -1, -1, 1, 1, 1, 1, 1]
    target := ![-3, -1, -1, 1, 1, 1, 1, 1]
    reflections := [] },
  { profile := ![-2, -2, -2, -2, 0, 2, 2, 4]
    target := ![-5, -1, -1, 1, 1, 1, 1, 3]
    reflections := [![-1, 1, 1, 1, -1, -1, -1, 1],
      ![-1, 1, -1, 1, 1, 1, -1, -1],
      ![-1, -1, 1, 1, 1, -1, 1, -1]] },
  { profile := ![-2, -2, -2, -2, 2, 2, 2, 2]
    target := ![-4, 0, 0, 0, 0, 0, 0, 4]
    reflections := [![-1, 1, 1, 1, -1, -1, -1, 1]] },
  { profile := ![-2, -2, -2, 0, 0, 0, 2, 4]
    target := ![-5, -1, 1, 1, 1, 1, 1, 1]
    reflections := [![0, -2, 0, 0, 0, 2, 0, 0],
      ![-1, 1, 1, -1, -1, 1, 1, -1],
      ![-1, -1, 1, 1, 1, 1, -1, -1]] },
  { profile := ![-2, -2, -2, 0, 0, 2, 2, 2]
    target := ![-4, 0, 0, 0, 0, 0, 2, 2]
    reflections := [![-1, 1, 1, 1, -1, -1, 1, -1],
      ![-1, 1, 1, -1, 1, -1, -1, 1]] },
  { profile := ![-2, -2, 0, 0, 0, 0, 0, 4]
    target := ![-4, 0, 0, 0, 0, 0, 2, 2]
    reflections := [![-1, 1, 1, 1, -1, -1, 1, -1],
      ![-1, 1, -1, -1, 1, 1, 1, -1]] },
  { profile := ![-2, -2, 0, 0, 0, 0, 2, 2]
    target := ![-3, -1, -1, 1, 1, 1, 1, 1]
    reflections := [![-1, 1, -1, 1, 1, 1, -1, -1]] },
  { profile := ![-2, 0, 0, 0, 0, 0, 0, 2]
    target := ![-2, 0, 0, 0, 0, 0, 0, 2]
    reflections := [] },
  { profile := ![-1, -1, -1, -1, -1, -1, 1, 5]
    target := ![-5, -1, 1, 1, 1, 1, 1, 1]
    reflections := [![-1, 1, 1, 1, -1, -1, 1, -1],
      ![-1, 1, -1, -1, 1, 1, 1, -1],
      ![-1, -1, 1, 1, 1, 1, -1, -1]] },
  { profile := ![-1, -1, -1, -1, -1, -1, 3, 3]
    target := ![-3, -3, 1, 1, 1, 1, 1, 1]
    reflections := [![-1, -1, 1, 1, 1, 1, -1, -1]] },
  { profile := ![-1, -1, -1, -1, -1, 1, 1, 3]
    target := ![-3, -1, -1, 1, 1, 1, 1, 1]
    reflections := [![-1, 1, -1, 1, 1, 1, -1, -1],
      ![-1, -1, 1, 1, 1, -1, 1, -1]] },
  { profile := ![-1, -1, -1, -1, 1, 1, 1, 1]
    target := ![-2, 0, 0, 0, 0, 0, 0, 2]
    reflections := [![-1, 1, 1, 1, -1, -1, -1, 1]] }
]

theorem e7MinedWeylCertificates_length :
    e7MinedWeylCertificates.length = 25 := by
  rfl

def e7MinedWeylSourceProfiles : List (List ℤ) :=
  e7MinedWeylCertificates.map fun c => List.ofFn c.profile

def e7MinedWeylTargetProfiles : List (List ℤ) :=
  e7MinedWeylCertificates.map fun c => List.ofFn c.target

end SRG266
