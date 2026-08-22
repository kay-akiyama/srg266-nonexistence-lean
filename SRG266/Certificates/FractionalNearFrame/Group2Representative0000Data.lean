import SRG266.QuasiSymmetric.FractionalNearFrameAudit

/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/

/-!
# Kernel pilot data for group 2 representative 0

This module owns the first generated pair-weight array independently of the
large group list.  The group data module references this entry, so the array is
not duplicated and bounded proof shards do not unfold the other 278 entries.
-/

namespace SRG266.Certificates

open SRG266.QuasiSymmetric

def fractionalNearFrameGroup2Representative0000 :
    FractionalNearFrameCertificateEntry := {
  nearMask := 236306569216131
  certificate := .farkas #[-96, -220, -123, -218, -68, 0, 47, 43, 73, -42,
    130, 6, 92, 247, 0, 166, 146, -141, 74, 57, 76, -121, 176, 124, 42,
    -48, -66, 79, -5, -50, 18, -4, -89, 49, 54, -93, 86, 49, -45, 48,
    -68, 70, 135, -7, -232, 68, -48, -49, -19, -79, -28, 169, 3, -60,
    -43, 40, 161, -11, 64, 96, -46, -35, -4, -11, 2, 25, 115, 45, 130,
    153, 89, -25, -59, 17, -158, -76, 53, 145, 34, 33, 34, 23, -132, 67,
    125, -11, -19, -160, -7, -149, 69, 13, 53, -85, -9, -115, 11, 124,
    -10, 51, -16, -70, -119, -39, -140, -5, -87, 49, -34, 79, -6, -116,
    -203, 60, -311, 89, -68, -99, 86, 112, 44, 133, -65, 82, -51, 111,
    -16, 128, -53, 67, -73, 3, 90, 9, -53, -23, -35, 190, -5, 163, -52,
    -84, 45, -189, -80, 169, -42, -184, -46, 122, 5, -57, 212, -22, -23,
    150, 40, 153, -113, 46, -50, 49, 169, -230, 13, 31, -73, 90]
}

def fractionalNearFrameGroup2Representative0000Witness : Array ℤ :=
  match fractionalNearFrameGroup2Representative0000.certificate with
  | .farkas witness => witness
  | .emptyShell => #[]

theorem fractionalNearFrameGroup2Representative0000_nearMask :
    fractionalNearFrameGroup2Representative0000.nearMask =
      236306569216131 := by
  rfl

theorem fractionalNearFrameGroup2Representative0000_certificate :
    fractionalNearFrameGroup2Representative0000.certificate =
      .farkas fractionalNearFrameGroup2Representative0000Witness := by
  rfl

end SRG266.Certificates
