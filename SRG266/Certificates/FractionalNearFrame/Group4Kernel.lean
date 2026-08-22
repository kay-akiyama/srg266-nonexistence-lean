import SRG266.Certificates.FractionalNearFrameSubtree.G4R0000P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0001P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0002P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0003P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0004P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0005P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0006P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0007P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0008P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0009P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0010P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0011P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0012P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0013P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0014P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0015P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0016P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0017P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0018P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0019P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0020P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0021P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0022P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0023P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0024P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0025P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0026P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0027P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0028P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0029P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0030P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0031P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0032P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0033P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0034P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0035P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0036P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0037P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0038P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0039P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0040P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0041P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0042P
import SRG266.Certificates.FractionalNearFrameSubtree.G4R0043P
import SRG266.Certificates.FractionalNearFrame.Group4KernelRule
import SRG266.QuasiSymmetric.FractionalNearFrameKernelSplit

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Group 4 without a native Farkas audit

The 44 residual Farkas masks of group 4 each have a kernel-only
obstruction of their own, proved by subtree-split shell lower bounds.
This module collects them and feeds them to the semantic dispatcher, so
the group obstruction avoids reducing stored witnesses.
-/

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

/-- The 44 residual Farkas masks of group 4. -/
def group4FarkasMasks : List ℕ :=
  [520939441717315, 521900574867523, 521902451761283, 538377143156803,
  936555774413059, 944037882200131, 944046197154051, 1101189391024466,
  1382720473104451, 4737706040868995, 4738668174330117, 4739630372801029,
  4869653626994819, 4870615760455941, 4871584208249093, 4877206387771653,
  4877219205173509, 4884693992026373, 4884697187988485, 4884765903268873,
  4886627775534085, 4887100083775777, 4887108405020961, 5159856228516099,
  5160887014344969, 5354538506488835, 5363196768143633, 5363197145619473,
  5368610111261187, 5369656532978185, 5369784576973073, 5387247644789009,
  5424769746668806, 5432466315250962, 5434388141162836, 5439873267600460,
  5440781384271110, 5441246314957218, 5447569836182616, 5464043208509784,
  5471567696348434, 5471808498663778, 5471842305819426, 5714009837256963]

theorem group4FarkasMasks_obstructed :
    ∀ mask ∈ group4FarkasMasks, NoCompactFractionalNearFrame mask := by
  intro mask hmask
  simp only [group4FarkasMasks] at hmask
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0000
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0001
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0002
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0003
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0004
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0005
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0006
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0007
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0008
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0009
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0010
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0011
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0012
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0013
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0014
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0015
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0016
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0017
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0018
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0019
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0020
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0021
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0022
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0023
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0024
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0025
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0026
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0027
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0028
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0029
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0030
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0031
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0032
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0033
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0034
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0035
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0036
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0037
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0038
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0039
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0040
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0041
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0042
  rcases List.mem_cons.mp hmask with rfl | hmask
  · exact noCompactFractionalNearFrame_fractionalNearFrameSubtreeG4R0043
  simp at hmask

/-- Bridge from entries to masks: constructor and mask only, no shell. -/
theorem group4FarkasMasks_cover :
    fractionalNearFrameFarkasMasksCovered
      fractionalNearFrameCertificatesGroup4 group4FarkasMasks = true := by
  decide +kernel

theorem group4FarkasRule :
    FractionalNearFrameKernelFarkasRuleOn fractionalNearFrameCertificatesGroup4 :=
  fractionalNearFrameKernelFarkasRuleOn_of_masks fractionalNearFrameCertificatesGroup4
    group4FarkasMasks group4FarkasMasks_cover
    group4FarkasMasks_obstructed

/-- Every group-4 normal form is impossible, with no native audit
anywhere in the proof term. -/
theorem noCompactFractionalNearFrame_of_mem_group4_kernel
    {nearMask : ℕ} (hmem : nearMask ∈ rootNearRepresentativeGroup4) :
    NoCompactFractionalNearFrame nearMask := by
  rw [← fractionalNearFrameCertificatesGroup4_masks] at hmem
  obtain ⟨entry, hentry, hmask⟩ := List.mem_map.mp hmem
  subst nearMask
  exact noCompactFractionalNearFrame_of_mem_kernel_split fractionalNearFrameCertificatesGroup4
    fractionalNearFrameCertificatesGroup4_emptyRule group4FarkasRule hentry

end SRG266.Certificates
