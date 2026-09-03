import Submission.NewmanFinitePrefix

/-! A particular degree23 polynomial is excluded from all normalized Newman
polynomials using a global quotient bound and nine exact integer cuts.
This is not a classification of all degrees and does not settle Erdős 406. -/
namespace Erdos406TwentyThree
open Polynomial Erdos406Quotient Erdos406FinitePrefix Erdos406IntegerCuts
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable def qTwentyThree : ℤ[X] := 1 + (-1) * X ^ 3 + (2) * X ^ 4 + (-2) * X ^ 7 + (1) * X ^ 8 + (1) * X ^ 9 + (1) * X ^ 10 + (-1) * X ^ 11 + (-1) * X ^ 12 + (2) * X ^ 13 + (1) * X ^ 15 + (-3) * X ^ 16 + (2) * X ^ 17 + (2) * X ^ 19 + (-2) * X ^ 20 + (1) * X ^ 21 + (-1) * X ^ 22 + (1) * X ^ 23
def coefficients : Array ℤ := #[1, 0, 0, -1, 2, 0, 0, -2, 1, 1, 1, -1, -1, 2, 0, 1, -3, 2, 0, 2, -2, 1, -1, 1]
def sCertificate : List ℤ := [3423, -1162, -4555, -4190, -5181, -11165, -10928, -8234, -10541, -11868, -9621, -5380, -6325, -6049, 1207, 2898, 2066, 5202, 9972, 11239, 8036, 11585, 13941, 8819, 7612, 8530, 7416, 1163, -2338, 456, -4881, -10061, -8759, -8914, -11943, -15406, -10090, -7608, -12094, -7782, -2665, -1307, -1165, 2944, 10597, 7446, 7255, 14097, 14187, 11741, 9760, 13285, 10660, 1745, 4911, 4200, -3188, -7402, -7807, -6372, -14473, -15161, -9131, -13724, -14981, -11714, -5153, -4621, -8141, 2806, 5971, 2930, 8608, 13636, 15871, 9430, 12578, 19473, 10365, 8640, 9546, 6865, 779, -6375, 458, -5418, -16278, -12212, -12345, -14091, -18869, -13231, -6386, -16577, -9571, 323, 145, 1803, 2761, 14495, 11986, 7948, 20798, 18372, 13705, 10170, 13889, 16581, -557, 3568, 5268, -9071, -10086, -11194, -7118, -17505, -24280, -10229, -16882, -17231, -11581, -7098, -1876, -12535, 4515, 15412, 3430, 12407, 16345, 19771, 13888, 13911, 28970, 10352, 5373, 11533, 5065, 4676, -11125, -4475, -5402, -27432, -14470, -12199, -17334, -23821, -22730, -2384, -18844, -11156, 9030, -4061, 3905, 4174, 19325, 25851, 5695, 25214, 21788, 14486, 17017, 13618, 26290, -8272, -7132, 14173, -16289, -10133, -14651, -17360, -20520, -36424, -5059, -16110, -24426, -13125, -17333, 9256, -10218, 3305, 31820, -5160, 11819, 28625, 28282, 23721, 8800, 34180, 8975, 2073, 26644, -653, 3252, -19074, -23219, 9398, -32991, -24411, -10983, -34059, -28075, -27813, 12429, -15882, -34220, 25287, -14531, 12242, 29860, 7043, 43189, -5699, 24318, 47094, 15722, 31013, -11193, 36996, -7815, -28639, 54961, -42217, -30707, -11296, -35716, -772, -48597, -4357, -37672, -39459, 8076, -27471, 45776, -14536, -41277, 59717, -2659, 17737, 71030, 35523, -6414, 12102, 29560, 19635, 18880, 24925, 11452, -12067, -26213, -33444, -37109, -30563, -14118, 3392, 17143, 26303, 28607, 23125, 12935, 1840, -7858, -14312, -16240, -14050, -9331, -3666, 1587, 5311, 7015, 6908, 5521, 3450, 1285, -525, -1777, -2452, -2617, -2385, -1887, -1231, -503, 213, 828, 1264, 1463, 1398, 1090, 609, 57, -451, -818, -983, -932, -702, -361, 4, 314, 513, 579, 518, 365, 167, -28, -182, -273, -295, -258, -180, -85, 8, 81, 127, 142, 131, 99, 56, 11, -29, -58, -72, -72, -60, -39, -14, 10, 29, 40, 42, 36, 24, 10, -4, -16, -22, -24, -21, -14, -6, 2, 8, 12, 13, 11, 8, 3, -1, -4, -6, -7, -6, -4, -2, 0, 2, 3, 4, 3, 3, 1, 0, -1, -2, -2, -2, -1, -1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def eCertificate : List ℤ := [3423, -1162, -4555, -7613, 2827, -8934, -15848, -18279, -3991, -11899, -17157, -14275, -9396, -6281, -17040, -7098, -13967, -1996, -7799, 2794, -9493, 1098, -4687, 1, 2, 2, -1, -5, 2, -1, 5, -5, 3, -2, 3, -3, 0, 1, 0, 2, -3, 3, -2, 3, -3, 1, -1, 2, 0, -2, 0, 0, 1, -1, -1, 0, 0, 2, -2, 1, -3, 1, -2, 1, 0, 0, -1, -2, 2, -1, 2, -4, 0, 0, 3, -2, -2, 0, 2, 3, -3, -2, -1, 3, 1, -2, -2, 0, 3, -2, 1, -3, 2, 0, 1, -1, -1, 1, 0, 1, -3, 2, 0, 1, 0, -1, 1, -2, 2, -1, 3, -2, 2, -1, 1, -1, 1, 1, 1, 0, -2, 2, 1, 0, -3, 1, 1, 2, -2, 1, 0, 1, 0, 0, 0, 0, 0, -1, 2, -1, 0, -1, 2, 1, 0, -1, -2, 2, 1, 1, -3, 1, 1, 2, -1, -2, 0, 1, 2, -3, 0, 1, 2, -3, -1, 1, 3, -2, -2, -1, 4, 0, -2, -3, 4, 2, -2, -3, 0, 3, -1, -2, 0, 2, 0, -2, 0, 0, 2, -3, 1, 0, 2, -2, -1, 0, 2, 0, -1, 1, 1, 0, -1, -1, 1, 0, 0, 0, 1, -1, 1, 0, 0, -1, 1, 0, 0, -1, 0, 2, 0, 0, -4, 2, 0, 2, -5, 2, 0, 1, -2, -1, 2, -1, 1, -3, 2, -1, 1, -1, 1, 0, -2, 0, 0, 1, -2, -1, 1, 1, -1, -3, 1, 1, 0, -4, 0, 2, 1, -2, -3, 1, 1, 1, -4, 0, 0, 2, -2, 0, 1, 1, 0, -3, 1, -1, 2, -2, 2, -1, 2, -1, 1, 0, 1, 0, 0, -1, 0, 1, 2, 0, -1, -2, 3, 1, 1, -4, 2, 2, 3, -5, 0, 1, 4, -1, -3, 1, 2, 3, -4, 2, -2, 6, -4, 2, -2, 4, -1, 1, 0, 0, 1, -2, 3, -2, 3, -3, 3, -2, 3, -2, 1, -1, 2, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, -1, -1, 1, 2, -1, -2, 0, 2, 0, -1, -2, 1, 1, 0, -2, -1, 2, 0, 0, -2, 3, -2, 3, -5, 4, -3, 4, -3, 2, -2, 1, 1, -2, 1, -2, 4, -2, 1, -4, 2, 0, 2, -2, 0, 1, 2, -2, -1, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
lemma q_list : qTwentyThree = listPoly [1, 0, 0, -1, 2, 0, 0, -2, 1, 1, 1, -1, -1, 2, 0, 1, -3, 2, 0, 2, -2, 1, -1, 1] := by
  simp [qTwentyThree, listPoly]
  ring

lemma q_coeff (n : ℕ) : qTwentyThree.coeff n = coefficients.getD n 0 := by
  rw [q_list, listPoly_coeff_getD]
  simp [coefficients]

lemma certificate :
    listPoly sCertificate * qTwentyThree = monomial 256 262144 + listPoly eCertificate := by
  rw [q_list]
  apply listPoly_certificate
  decide +kernel

lemma quotient_bound_all (P R : ℤ[X]) (hPR : P = qTwentyThree * R)
    (hP : ∀ i, |P.coeff i| ≤ 1) : ∀ i, |R.coeff i| ≤ 54 := by
  intro i
  have hh := quotient_bound qTwentyThree P R sCertificate eCertificate 262144 256
    hPR certificate hP i
  norm_num [weight, sCertificate, eCertificate] at hh
  omega

def rhs0 : Fin 256 → ℤ := state (fun _ : Fin 64 => 54)
def rows0 (i : Fin 1) : Fin 256 :=
  ⟨(#[0] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights0 (i : Fin 1) : ℤ := (#[4294967296] : Array ℤ).getD i.val 0
def rhs1 : Fin 256 → ℤ := Function.update rhs0 128 (1)
lemma step0 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs0 r) :
    Valid (matrix coefficients) rhs1 r := by
  exact selected_cut_update (matrix coefficients) rhs0 rows0 weights0 r 128
    4294967296 (1) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows1 (i : Fin 1) : Fin 256 :=
  ⟨(#[64] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights1 (i : Fin 1) : ℤ := (#[4294967296] : Array ℤ).getD i.val 0
def rhs2 : Fin 256 → ℤ := Function.update rhs1 192 (-1)
lemma step1 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs1 r) :
    Valid (matrix coefficients) rhs2 r := by
  exact selected_cut_update (matrix coefficients) rhs1 rows1 weights1 r 192
    4294967296 (-1) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows2 (i : Fin 1) : Fin 256 :=
  ⟨(#[1] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights2 (i : Fin 1) : ℤ := (#[4294967296] : Array ℤ).getD i.val 0
def rhs3 : Fin 256 → ℤ := Function.update rhs2 129 (1)
lemma step2 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs2 r) :
    Valid (matrix coefficients) rhs3 r := by
  exact selected_cut_update (matrix coefficients) rhs2 rows2 weights2 r 129
    4294967296 (1) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows3 (i : Fin 1) : Fin 256 :=
  ⟨(#[65] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights3 (i : Fin 1) : ℤ := (#[4294967296] : Array ℤ).getD i.val 0
def rhs4 : Fin 256 → ℤ := Function.update rhs3 193 (0)
lemma step3 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs3 r) :
    Valid (matrix coefficients) rhs4 r := by
  exact selected_cut_update (matrix coefficients) rhs3 rows3 weights3 r 193
    4294967296 (0) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows4 (i : Fin 104) : Fin 256 :=
  ⟨(#[1, 4, 6, 10, 11, 12, 13, 18, 19, 20, 21, 25, 26, 27, 28, 32, 33, 34, 35, 40, 41, 42, 43, 47, 48, 49, 50, 55, 56, 57, 63, 64, 67, 72, 73, 78, 79, 80, 81, 86, 87, 88, 93, 94, 95, 100, 101, 102, 103, 108, 109, 110, 115, 116, 117, 118, 122, 123, 124, 125, 129, 131, 133, 136, 138, 140, 142, 144, 146, 148, 150, 152, 154, 158, 159, 163, 164, 167, 168, 169, 172, 173, 177, 178, 188, 189, 192, 194, 196, 198, 205, 207, 209, 215, 220, 224, 226, 230, 234, 235, 239, 243, 244, 255] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights4 (i : Fin 104) : ℤ := (#[1224884160, 6190287890, 904902883, 311896984, 192723983, 1938900199, 283076586, 540755609, 262639305, 424977747, 47775755, 15865447, 267342699, 131822031, 31796356, 11715454, 47069227, 89462569, 35220225, 21845827, 30544722, 21004943, 4455510, 563957, 16332717, 11185870, 4493291, 5038358, 6730492, 2096178, 2589690, 9547361853, 133469777, 3616532159, 323176050, 600886690, 271972454, 958961355, 152168755, 400347630, 197422068, 155889892, 41636665, 163395525, 73837834, 25910935, 41236818, 45586731, 15392000, 18851962, 17262806, 9903160, 2166623, 10095737, 4051334, 493512, 2730712, 5179380, 3365246, 2730712, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 1, 1, 5954936, 2730712, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 2, 2, 2, 1, 1, 2589690] : Array ℤ).getD i.val 0
def rhs5 : Fin 256 → ℤ := Function.update rhs4 130 (0)
lemma step4 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs4 r) :
    Valid (matrix coefficients) rhs5 r := by
  exact selected_cut_update (matrix coefficients) rhs4 rows4 weights4 r 130
    4294967296 (0) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows5 (i : Fin 1) : Fin 256 :=
  ⟨(#[66] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights5 (i : Fin 1) : ℤ := (#[4294967296] : Array ℤ).getD i.val 0
def rhs6 : Fin 256 → ℤ := Function.update rhs5 194 (0)
lemma step5 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs5 r) :
    Valid (matrix coefficients) rhs6 r := by
  exact selected_cut_update (matrix coefficients) rhs5 rows5 weights5 r 194
    4294967296 (0) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows6 (i : Fin 107) : Fin 256 :=
  ⟨(#[4, 5, 7, 10, 11, 13, 16, 18, 19, 24, 25, 26, 27, 31, 32, 33, 34, 38, 39, 40, 41, 46, 47, 48, 53, 54, 55, 60, 61, 62, 63, 64, 70, 72, 73, 78, 79, 84, 85, 86, 87, 92, 93, 94, 99, 100, 101, 106, 107, 108, 109, 113, 114, 115, 116, 120, 121, 122, 123, 129, 130, 131, 135, 138, 140, 142, 144, 146, 151, 155, 159, 163, 164, 167, 168, 169, 173, 174, 178, 179, 183, 184, 188, 192, 196, 198, 201, 203, 205, 207, 209, 212, 213, 216, 220, 221, 222, 224, 226, 230, 235, 240, 245, 249, 253, 254, 255] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights6 (i : Fin 107) : ℤ := (#[7425085348, 1302923251, 1169469523, 4998872534, 52396338, 371978156, 590934772, 1354848374, 292915529, 474005632, 174137307, 252063690, 51799641, 8001038, 196546069, 96922273, 3602727, 24614695, 33705930, 61363149, 30817134, 18587486, 19040800, 16442221, 1778926, 7720510, 7309141, 3161475, 4387932, 6132272, 5061918, 15232486825, 8437663258, 2055679491, 934197848, 2708604015, 341608556, 619731344, 154639697, 625560958, 161102125, 323801137, 141615169, 78796132, 29288351, 110778506, 54017515, 24689737, 26072332, 31536461, 10336857, 84173, 15787802, 15014650, 8912390, 190679, 5614388, 7876612, 3991564, 1, 12603018444, 3, 1, 1, 3, 4, 1, 3, 2, 3, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1900443, 4, 3, 1, 2, 4, 3, 5, 2, 2, 1, 3, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 4387932, 6132272, 5061918] : Array ℤ).getD i.val 0
def rhs7 : Fin 256 → ℤ := Function.update rhs6 131 (1)
lemma step6 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs6 r) :
    Valid (matrix coefficients) rhs7 r := by
  exact selected_cut_update (matrix coefficients) rhs6 rows6 weights6 r 131
    4294967296 (1) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows7 (i : Fin 2) : Fin 256 :=
  ⟨(#[64, 67] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights7 (i : Fin 2) : ℤ := (#[4294967296, 4294967296] : Array ℤ).getD i.val 0
def rhs8 : Fin 256 → ℤ := Function.update rhs7 195 (-1)
lemma step7 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs7 r) :
    Valid (matrix coefficients) rhs8 r := by
  exact selected_cut_update (matrix coefficients) rhs7 rows7 weights7 r 195
    4294967296 (-1) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def rows8 (i : Fin 115) : Fin 256 :=
  ⟨(#[4, 5, 10, 11, 13, 16, 18, 19, 24, 25, 26, 27, 32, 33, 34, 38, 39, 40, 41, 46, 47, 48, 49, 53, 54, 55, 56, 60, 61, 62, 63, 64, 67, 70, 72, 73, 78, 79, 84, 85, 86, 87, 92, 93, 94, 95, 99, 100, 101, 106, 107, 108, 109, 114, 115, 116, 121, 122, 123, 128, 130, 132, 136, 138, 140, 142, 144, 145, 149, 151, 153, 155, 157, 159, 161, 163, 165, 167, 171, 172, 174, 176, 178, 180, 184, 188, 193, 194, 195, 199, 201, 203, 205, 207, 210, 211, 212, 214, 216, 218, 220, 222, 224, 226, 228, 230, 232, 237, 241, 243, 245, 247, 253, 254, 255] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def weights8 (i : Fin 115) : ℤ := (#[11709543202, 3353831638, 5356508484, 916839862, 616271956, 583008329, 1476005915, 607747724, 481435785, 254619368, 308208750, 125813828, 210205744, 141181708, 23138767, 15566809, 35722754, 70693997, 47617320, 17086918, 22803290, 22623699, 3597915, 861536, 7993108, 10227021, 1791020, 2488836, 4128203, 6768693, 6545401, 28397802711, 3134604795, 9174196825, 2033661559, 1764777770, 2905143119, 889433770, 618657543, 229390097, 708086815, 322710190, 338003099, 205063105, 114728484, 19030415, 23601207, 123271251, 81904667, 21079342, 29847347, 38984862, 18132733, 15611271, 18260135, 12839571, 5767570, 9409183, 6322109, 2, 14193973248, 3, 3, 1, 3, 1, 2, 1, 5, 1, 5, 2, 2, 3, 2, 3, 2, 3, 2, 1, 1, 3, 1, 3, 1, 4056565, 1, 1, 1, 3, 1, 3, 1, 2, 2, 1, 1, 3, 4, 2, 4, 1, 3, 1, 3, 2, 3, 2, 3, 1, 1, 1, 4128203, 6768693, 6545401] : Array ℤ).getD i.val 0
def rhs9 : Fin 256 → ℤ := Function.update rhs8 132 (-1)
lemma step8 (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs8 r) :
    Valid (matrix coefficients) rhs9 r := by
  exact selected_cut_update (matrix coefficients) rhs8 rows8 weights8 r 132
    4294967296 (-1) (by decide +kernel) (by decide) (by decide +kernel)
    (by decide +kernel) h
def finalRows (i : Fin 102) : Fin 256 :=
  ⟨(#[4, 7, 10, 12, 17, 18, 19, 24, 25, 26, 27, 31, 32, 33, 34, 38, 39, 40, 41, 46, 47, 48, 49, 53, 54, 55, 56, 60, 61, 62, 63, 65, 69, 70, 72, 75, 78, 79, 84, 85, 86, 87, 92, 93, 94, 99, 100, 101, 106, 107, 108, 109, 114, 115, 116, 121, 122, 123, 129, 130, 132, 134, 135, 139, 140, 141, 145, 149, 150, 153, 154, 155, 159, 161, 163, 167, 168, 172, 174, 176, 188, 195, 196, 197, 201, 202, 206, 210, 211, 212, 216, 220, 222, 224, 226, 230, 235, 239, 243, 253, 254, 255] : Array ℕ).getD i.val 0 % 256, Nat.mod_lt _ (by decide)⟩
def finalWeights (i : Fin 102) : ℤ := (#[39120878, 85339406, 361537642, 89853724, 9947430, 120858592, 17441273, 28818437, 14268060, 29011244, 3793547, 375247, 15357110, 7980133, 3384481, 382691, 2436680, 5469219, 2859902, 1158693, 1476499, 1749346, 197406, 69450, 599576, 666878, 169586, 157142, 278582, 483870, 452012, 468673972, 58571535, 528787122, 317212811, 8011437, 218655501, 16188283, 27303878, 14822876, 62144332, 10563823, 23054334, 11364891, 11871381, 2028575, 9372164, 4712713, 1247363, 1951704, 3028503, 1082994, 1119148, 1192183, 980184, 400022, 689158, 420154, 1, 617560933, 777346914, 2, 1, 1, 1, 1, 3, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 1, 1, 294870, 247404341, 2, 1, 2, 1, 3, 2, 1, 2, 2, 2, 1, 1, 3, 1, 2, 1, 1, 278582, 483870, 452012] : Array ℤ).getD i.val 0

theorem prefix_impossible (r : Fin 64 → ℤ) (h : Valid (matrix coefficients) rhs0 r) : False := by
  have h1 := step0 r h
  have h2 := step1 r h1
  have h3 := step2 r h2
  have h4 := step3 r h3
  have h5 := step4 r h4
  have h6 := step5 r h5
  have h7 := step6 r h6
  have h8 := step7 r h7
  have h9 := step8 r h8
  exact selected_contradiction (matrix coefficients) rhs9 finalRows finalWeights r
    (by decide +kernel) (by decide +kernel) (by decide +kernel) h9

theorem not_dvd_newman (P : ℤ[X]) (h0 : P.coeff 0 = 1)
    (hP : ∀ i, P.coeff i = 0 ∨ P.coeff i = 1) : ¬ qTwentyThree ∣ P := by
  rintro ⟨R, hPR⟩
  have hb := quotient_bound_all P R hPR (fun i => by
    rcases hP i with h | h <;> rw [h] <;> norm_num)
  have hp (i : ℕ) : 0 ≤ P.coeff i ∧ P.coeff i ≤ 1 := by
    rcases hP i with h | h <;> rw [h] <;> norm_num
  exact prefix_impossible (fun j => R.coeff j.val)
    (initial_valid (by decide) coefficients (fun _ : Fin 64 => 54) qTwentyThree P R
      q_coeff hPR h0 hp (fun i => hb i.val))

lemma eval_three : qTwentyThree.eval 3 = (2 : ℤ) ^ 36 := by norm_num [qTwentyThree]
lemma degree_eq : qTwentyThree.natDegree = 23 := by
  unfold qTwentyThree
  compute_degree <;> norm_num

#print axioms quotient_bound_all
#print axioms prefix_impossible
#print axioms not_dvd_newman
#print axioms eval_three
end Erdos406TwentyThree
