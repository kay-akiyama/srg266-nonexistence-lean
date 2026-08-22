/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import SRG266.Hosts.A15MinedNormSearch

/-! # Explicit norm profiles emitted by the mined A15 search -/

namespace SRG266

def a15MinedNormProfile00 : List ℤ :=
  [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 3, 5]
def a15MinedNormProfile01 : List ℤ :=
  [-1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, -1, 3, 3, 3, 3]
def a15MinedNormProfile02 : List ℤ :=
  [-2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6]
def a15MinedNormProfile03 : List ℤ :=
  [-2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 4, 4]
def a15MinedNormProfile04 : List ℤ :=
  [-2, -2, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 4]
def a15MinedNormProfile05 : List ℤ :=
  [-2, -2, -2, -2, -2, -2, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2]
def a15MinedNormProfile06 : List ℤ :=
  [-3, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 5]
def a15MinedNormProfile07 : List ℤ :=
  [-3, -1, -1, -1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 3, 3, 3]
def a15MinedNormProfile08 : List ℤ :=
  [-3, -3, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 3, 3]
def a15MinedNormProfile09 : List ℤ :=
  [-3, -3, -3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3]
def a15MinedNormProfile10 : List ℤ :=
  [-3, -3, -3, -3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def a15MinedNormProfile11 : List ℤ :=
  [-4, -2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 4]
def a15MinedNormProfile12 : List ℤ :=
  [-4, -2, -2, -2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2]
def a15MinedNormProfile13 : List ℤ :=
  [-4, -4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2]
def a15MinedNormProfile14 : List ℤ :=
  [-5, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 3]
def a15MinedNormProfile15 : List ℤ :=
  [-5, -3, -1, -1, -1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]
def a15MinedNormProfile16 : List ℤ :=
  [-6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2]

/-- Explicit normal form of the 17 small norm profiles. -/
def a15MinedNormProfiles : List (List ℤ) :=
  [a15MinedNormProfile00, a15MinedNormProfile01,
    a15MinedNormProfile02, a15MinedNormProfile03,
    a15MinedNormProfile04, a15MinedNormProfile05,
    a15MinedNormProfile06, a15MinedNormProfile07,
    a15MinedNormProfile08, a15MinedNormProfile09,
    a15MinedNormProfile10, a15MinedNormProfile11,
    a15MinedNormProfile12, a15MinedNormProfile13,
    a15MinedNormProfile14, a15MinedNormProfile15,
    a15MinedNormProfile16]

end SRG266
