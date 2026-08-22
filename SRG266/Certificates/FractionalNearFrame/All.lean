import SRG266.Certificates.FractionalNearFrame.Group1Kernel
import SRG266.Certificates.FractionalNearFrame.Group2Kernel
import SRG266.Certificates.FractionalNearFrame.Group3Kernel
import SRG266.Certificates.FractionalNearFrame.Group4Kernel
import SRG266.Certificates.FractionalNearFrame.Group5Kernel

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Complete non-`2K4` fractional near-frame audit

The five nonexceptional cubic-root groups contain 2,743 rooted near normal
forms.  Group 2 representative zero is a bounded kernel theorem, group-2
tail indices `[1, 1395)` use split Hall/Farkas audits, and the group-1,
group-3, group-4, and group-5 empty-shell strata are discharged by
theorem-mined Hall rules.  All group-1 residual separators are reconstructed
intrinsically from their masks; native certificate replay is confined to the
other groups' residual Farkas certificates.  This module dispatches to those
already checked theorems and performs no monolithic certificate evaluation.
-/

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

def rootNearRepresentativesNonTwoK4 : List ℕ :=
  rootNearRepresentativeGroup1 ++
  rootNearRepresentativeGroup2 ++
  rootNearRepresentativeGroup3 ++
  rootNearRepresentativeGroup4 ++
  rootNearRepresentativeGroup5

/-- Every listed non-`2K4` normal form has no compact fractional near frame.
Every branch is a kernel-only dispatcher: no native Farkas audit remains on this path. -/
theorem noCompactFractionalNearFrame_of_mem_nonTwoK4
    {nearMask : ℕ} (hmem : nearMask ∈ rootNearRepresentativesNonTwoK4) :
    NoCompactFractionalNearFrame nearMask := by
  change nearMask ∈ rootNearRepresentativeGroup1 ++
    rootNearRepresentativeGroup2 ++ rootNearRepresentativeGroup3 ++
    rootNearRepresentativeGroup4 ++ rootNearRepresentativeGroup5 at hmem
  rcases List.mem_append.mp hmem with hrest | hgroup5
  rcases List.mem_append.mp hrest with hrest | hgroup4
  rcases List.mem_append.mp hrest with hrest | hgroup3
  rcases List.mem_append.mp hrest with hgroup1 | hgroup2
  · exact noCompactFractionalNearFrame_of_mem_group1_kernel hgroup1
  · exact noCompactFractionalNearFrame_of_mem_group2_kernel hgroup2
  · exact noCompactFractionalNearFrame_of_mem_group3_kernel hgroup3
  · exact noCompactFractionalNearFrame_of_mem_group4_kernel hgroup4
  · exact noCompactFractionalNearFrame_of_mem_group5_kernel hgroup5

end SRG266.Certificates
