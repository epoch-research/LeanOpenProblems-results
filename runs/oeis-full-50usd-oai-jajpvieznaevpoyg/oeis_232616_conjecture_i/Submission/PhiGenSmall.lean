import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0

def psmall : Nat → Nat
| 0 => 2
| 1 => 3
| 2 => 5
| 3 => 7
| _ => 1
def phiFrom : Nat → Nat → Nat
| 0, n => n
| i+1, n => phiFrom i n - phiFrom i (n / psmall i)

opaque phi_0_100 : phiFrom 0 100 = 100 := rfl
opaque phi_0_50 : phiFrom 0 50 = 50 := rfl
opaque phi_1_100 : phiFrom 1 100 = 50 := by
  change phiFrom 0 100 - phiFrom 0 (100 / psmall 0) = 50
  norm_num [psmall]
  try rw [phi_0_100, phi_0_50]
  try norm_num
opaque phi_0_33 : phiFrom 0 33 = 33 := rfl
opaque phi_0_16 : phiFrom 0 16 = 16 := rfl
opaque phi_1_33 : phiFrom 1 33 = 17 := by
  change phiFrom 0 33 - phiFrom 0 (33 / psmall 0) = 17
  norm_num [psmall]
  try rw [phi_0_33, phi_0_16]
  try norm_num
opaque phi_2_100 : phiFrom 2 100 = 33 := by
  change phiFrom 1 100 - phiFrom 1 (100 / psmall 1) = 33
  norm_num [psmall]
  try rw [phi_1_100, phi_1_33]
  try norm_num
opaque phi_0_20 : phiFrom 0 20 = 20 := rfl
opaque phi_0_10 : phiFrom 0 10 = 10 := rfl
opaque phi_1_20 : phiFrom 1 20 = 10 := by
  change phiFrom 0 20 - phiFrom 0 (20 / psmall 0) = 10
  norm_num [psmall]
  try rw [phi_0_20, phi_0_10]
  try norm_num
opaque phi_0_6 : phiFrom 0 6 = 6 := rfl
opaque phi_0_3 : phiFrom 0 3 = 3 := rfl
opaque phi_1_6 : phiFrom 1 6 = 3 := by
  change phiFrom 0 6 - phiFrom 0 (6 / psmall 0) = 3
  norm_num [psmall]
  try rw [phi_0_6, phi_0_3]
  try norm_num
opaque phi_2_20 : phiFrom 2 20 = 7 := by
  change phiFrom 1 20 - phiFrom 1 (20 / psmall 1) = 7
  norm_num [psmall]
  try rw [phi_1_20, phi_1_6]
  try norm_num
opaque phi_3_100 : phiFrom 3 100 = 26 := by
  change phiFrom 2 100 - phiFrom 2 (100 / psmall 2) = 26
  norm_num [psmall]
  try rw [phi_2_100, phi_2_20]
  try norm_num
opaque phi_0_14 : phiFrom 0 14 = 14 := rfl
opaque phi_0_7 : phiFrom 0 7 = 7 := rfl
opaque phi_1_14 : phiFrom 1 14 = 7 := by
  change phiFrom 0 14 - phiFrom 0 (14 / psmall 0) = 7
  norm_num [psmall]
  try rw [phi_0_14, phi_0_7]
  try norm_num
opaque phi_0_4 : phiFrom 0 4 = 4 := rfl
opaque phi_0_2 : phiFrom 0 2 = 2 := rfl
opaque phi_1_4 : phiFrom 1 4 = 2 := by
  change phiFrom 0 4 - phiFrom 0 (4 / psmall 0) = 2
  norm_num [psmall]
  try rw [phi_0_4, phi_0_2]
  try norm_num
opaque phi_2_14 : phiFrom 2 14 = 5 := by
  change phiFrom 1 14 - phiFrom 1 (14 / psmall 1) = 5
  norm_num [psmall]
  try rw [phi_1_14, phi_1_4]
  try norm_num
opaque phi_0_1 : phiFrom 0 1 = 1 := rfl
opaque phi_1_2 : phiFrom 1 2 = 1 := by
  change phiFrom 0 2 - phiFrom 0 (2 / psmall 0) = 1
  norm_num [psmall]
  try rw [phi_0_2, phi_0_1]
  try norm_num
opaque phi_0_0 : phiFrom 0 0 = 0 := rfl
opaque phi_1_0 : phiFrom 1 0 = 0 := by
  change phiFrom 0 0 - phiFrom 0 (0 / psmall 0) = 0
  norm_num [psmall]
  try rw [phi_0_0, phi_0_0]
  try norm_num
opaque phi_2_2 : phiFrom 2 2 = 1 := by
  change phiFrom 1 2 - phiFrom 1 (2 / psmall 1) = 1
  norm_num [psmall]
  try rw [phi_1_2, phi_1_0]
  try norm_num
opaque phi_3_14 : phiFrom 3 14 = 4 := by
  change phiFrom 2 14 - phiFrom 2 (14 / psmall 2) = 4
  norm_num [psmall]
  try rw [phi_2_14, phi_2_2]
  try norm_num
opaque phi_4_100 : phiFrom 4 100 = 22 := by
  change phiFrom 3 100 - phiFrom 3 (100 / psmall 3) = 22
  norm_num [psmall]
  try rw [phi_3_100, phi_3_14]
  try norm_num
theorem phi_result : phiFrom 4 100 = 22 := phi_4_100
