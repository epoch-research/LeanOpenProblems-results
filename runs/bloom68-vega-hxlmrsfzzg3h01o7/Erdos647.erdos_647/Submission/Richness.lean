import Submission.Reductions

/-!
# Additional verified necessary conditions for Erdős problem 647

These lemmas do not settle either theorem in `Submission.Spec`.
-/

namespace Erdos647

open scoped ArithmeticFunction.sigma

/-- Complementary divisor sets are disjoint whenever the larger number does not
    divide the square of the smaller divisor; no size comparison is needed. -/
theorem two_mul_card_divisors_le_of_not_dvd_sq {d m : ℕ}
    (hm0 : m ≠ 0) (hd : d ∣ m) (hm : ¬ m ∣ d * d) :
    2 * d.divisors.card ≤ m.divisors.card := by
  have hs : d.divisors ⊆ m.divisors := Nat.divisors_subset_of_dvd hm0 hd
  have hi : Set.InjOn (fun x : ℕ => m / x) (↑d.divisors : Set ℕ) := by
    intro x hx y hy hxy
    exact (Nat.div_eq_iff_eq_of_dvd_dvd hm0
      ((Nat.dvd_of_mem_divisors hx).trans hd)
      ((Nat.dvd_of_mem_divisors hy).trans hd)).mp hxy
  have ht : d.divisors.image (fun x => m / x) ⊆ m.divisors := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact Nat.mem_divisors.mpr
      ⟨Nat.div_dvd_of_dvd ((Nat.dvd_of_mem_divisors hy).trans hd), hm0⟩
  have hdis : Disjoint d.divisors (d.divisors.image (fun x => m / x)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hxi
    obtain ⟨y, hy, hxy⟩ := Finset.mem_image.mp hxi
    have hprod : x * y = m := by
      rw [← hxy]
      exact Nat.div_mul_cancel ((Nat.dvd_of_mem_divisors hy).trans hd)
    apply hm
    rw [← hprod]
    exact Nat.mul_dvd_mul (Nat.dvd_of_mem_divisors hx) (Nat.dvd_of_mem_divisors hy)
  have hc := Finset.card_le_card (Finset.union_subset hs ht)
  rw [Finset.card_union_of_disjoint hdis, Finset.card_image_of_injOn hi] at hc
  omega

/-- The core has exactly 192 divisors. -/
theorem card_divisors_core : (360360 : ℕ).divisors.card = 192 := by
  have he : (360360 : ℕ) = 8 * (9 * (5 * (7 * (11 * 13)))) := by norm_num
  rw [he]
  rw [Nat.Coprime.card_divisors_mul
    (by decide : Nat.Coprime 8 (9 * (5 * (7 * (11 * 13)))))]
  rw [Nat.Coprime.card_divisors_mul
    (by decide : Nat.Coprime 9 (5 * (7 * (11 * 13))))]
  rw [Nat.Coprime.card_divisors_mul
    (by decide : Nat.Coprime 5 (7 * (11 * 13)))]
  rw [Nat.Coprime.card_divisors_mul (by decide : Nat.Coprime 7 (11 * 13))]
  rw [Nat.Coprime.card_divisors_mul (by decide : Nat.Coprime 11 13)]
  decide

/-- Each row contains a divisor `g` of the core, an offset `j`, and at least
`j + 3` distinct divisors of `360360 * g - j`. -/
private def coreDivisorCertificates : List (ℕ × ℕ × List ℕ) := [
  (1, 1, [1, 173, 2083, 360359]),
  (2, 1, [1, 31, 67, 347]),
  (3, 3, [1, 3, 173, 519, 2083, 6249]),
  (4, 2, [1, 2, 31, 62, 67]),
  (5, 1, [1, 29, 62131, 1801799]),
  (6, 1, [1, 1039, 2081, 2162159]),
  (7, 1, [1, 157, 16067, 2522519]),
  (8, 1, [1, 389, 7411, 2882879]),
  (9, 5, [1, 5, 37, 47, 185, 235, 373, 1739]),
  (10, 1, [1, 1069, 3371, 3603599]),
  (11, 2, [1, 2, 17, 23, 34]),
  (12, 1, [1, 449, 9631, 4324319]),
  (13, 1, [1, 829, 5651, 4684679]),
  (14, 1, [1, 17, 296767, 5045039]),
  (15, 1, [1, 41, 131839, 5405399]),
  (18, 3, [1, 3, 1039, 2081, 3117, 6243]),
  (20, 1, [1, 107, 193, 349]),
  (21, 1, [1, 419, 18061, 7567559]),
  (22, 4, [1, 2, 4, 17, 23, 34, 37]),
  (24, 1, [1, 37, 233747, 8648639]),
  (26, 1, [1, 2203, 4253, 9369359]),
  (28, 1, [1, 43, 234653, 10090079]),
  (30, 1, [1, 47, 230017, 10810799]),
  (33, 1, [1, 31, 383609, 11891879]),
  (35, 1, [1, 19, 663821, 12612599]),
  (36, 3, [1, 3, 449, 1347, 9631, 28893]),
  (39, 1, [1, 97, 144887, 14054039]),
  (40, 1, [1, 23, 626713, 14414399]),
  (42, 1, [1, 1471, 10289, 15135119]),
  (44, 3, [1, 3, 29, 59, 87, 177]),
  (45, 1, [1, 227, 71437, 16216199]),
  (52, 2, [1, 2, 2203, 4253, 4406]),
  (55, 2, [1, 2, 1619, 3238, 6121]),
  (56, 1, [1, 41, 139, 3541]),
  (60, 1, [1, 2281, 9479, 21621599]),
  (63, 1, [1, 23, 29, 101]),
  (65, 1, [1, 17, 1377847, 23423399]),
  (66, 1, [1, 409, 58151, 23783759]),
  (70, 1, [1, 2579, 9781, 25225199]),
  (72, 3, [1, 3, 37, 111, 233747, 701241]),
  (77, 1, [1, 47, 590377, 27747719]),
  (78, 1, [1, 269, 104491, 28108079]),
  (84, 2, [1, 2, 1471, 2942, 10289]),
  (88, 1, [1, 89, 356311, 31711679]),
  (90, 2, [1, 2, 227, 454, 71437]),
  (91, 1, [1, 109, 300851, 32792759]),
  (99, 1, [1, 17, 691, 3037]),
  (104, 1, [1, 479, 78241, 37477439]),
  (105, 2, [1, 2, 73, 146, 259163]),
  (110, 3, [1, 3, 17, 51, 777247, 2331741]),
  (117, 2, [1, 2, 331, 662, 63689]),
  (120, 1, [1, 271, 159569, 43243199]),
  (126, 1, [1, 31, 1464689, 45405359]),
  (130, 1, [1, 19, 2465621, 46846799]),
  (132, 1, [1, 23, 709, 2917]),
  (140, 1, [1, 71, 710569, 50450399]),
  (143, 1, [1, 3931, 13109, 51531479]),
  (154, 1, [1, 397, 139787, 55495439]),
  (156, 2, [1, 2, 269, 538, 104491]),
  (165, 2, [1, 2, 19, 38, 1564721]),
  (168, 1, [1, 19, 467, 6823]),
  (180, 3, [1, 3, 2281, 6843, 9479, 28437]),
  (182, 2, [1, 2, 109, 218, 300851]),
  (195, 1, [1, 139, 223, 2267]),
  (198, 2, [1, 2, 17, 34, 691]),
  (210, 1, [1, 4493, 16843, 75675599]),
  (220, 1, [1, 41, 61, 2501]),
  (231, 1, [1, 59, 281, 5021]),
  (234, 1, [1, 107, 788077, 84324239]),
  (252, 1, [1, 17, 877, 6091]),
  (260, 2, [1, 2, 19, 38, 2465621]),
  (264, 1, [1, 79, 113, 8927]),
  (273, 3, [1, 3, 109, 327, 300851, 902553]),
  (280, 2, [1, 2, 71, 142, 710569]),
  (286, 1, [1, 17, 43, 731]),
  (308, 1, [1, 73, 1520423, 110990879]),
  (312, 1, [1, 31, 47, 1457]),
  (315, 1, [1, 5981, 18979, 113513399]),
  (330, 1, [1, 97, 241, 5087]),
  (360, 1, [1, 1873, 69263, 129729599]),
  (364, 1, [1, 1553, 84463, 131171039]),
  (385, 1, [1, 23, 1481, 4073]),
  (390, 2, [1, 2, 139, 223, 278]),
  (396, 1, [1, 19, 179, 3401]),
  (420, 1, [1, 53, 2855683, 151351199]),
  (429, 1, [1, 3299, 46861, 154594439]),
  (440, 1, [1, 29, 419, 12151]),
  (455, 1, [1, 239, 686041, 163963799]),
  (462, 2, [1, 2, 59, 118, 281]),
  (468, 1, [1, 37, 1369, 123191]),
  (495, 1, [1, 71, 2512369, 178378199]),
  (504, 1, [1, 857, 211927, 181621439]),
  (520, 1, [1, 173, 991, 1093]),
  (546, 1, [1, 23, 8554633, 196756559]),
  (572, 1, [1, 809, 254791, 206125919]),
  (585, 1, [1, 29, 59, 1711]),
  (616, 1, [1, 37, 269, 9953]),
  (630, 1, [1, 41, 43, 131]),
  (660, 1, [1, 17, 127, 2159]),
  (693, 1, [1, 173, 1443523, 249729479]),
  (715, 1, [1, 31, 677, 12277]),
  (728, 1, [1, 17, 15431887, 262342079]),
  (770, 1, [1, 101, 719, 3821]),
  (780, 1, [1, 1103, 254833, 281080799]),
  (792, 1, [1, 157, 193, 9419]),
  (819, 1, [1, 73, 4042943, 295134839]),
  (840, 1, [1, 587, 515677, 302702399]),
  (858, 1, [1, 1009, 306431, 309188879]),
  (910, 1, [1, 263, 449, 2777]),
  (924, 1, [1, 3389, 98251, 332972639]),
  (936, 2, [1, 2, 37, 74, 1369]),
  (990, 2, [1, 2, 71, 142, 2512369]),
  (1001, 1, [1, 6277, 57467, 360720359]),
  (1092, 2, [1, 2, 23, 46, 8554633]),
  (1144, 1, [1, 23, 17923993, 412251839]),
  (1155, 2, [1, 2, 89, 178, 2338291]),
  (1170, 1, [1, 17, 137, 2329]),
  (1260, 1, [1, 827, 549037, 454053599]),
  (1287, 1, [1, 12697, 36527, 463783319]),
  (1320, 1, [1, 149, 3192451, 475675199]),
  (1365, 1, [1, 19, 25889021, 491891399]),
  (1386, 1, [1, 11621, 42979, 499458959]),
  (1430, 1, [1, 37, 2753, 5059]),
  (1540, 1, [1, 3011, 184309, 554954399]),
  (1560, 1, [1, 71, 7917769, 562161599]),
  (1638, 2, [1, 2, 73, 146, 4042943]),
  (1716, 1, [1, 29, 21323371, 618377759]),
  (1820, 2, [1, 2, 263, 449, 526]),
  (1848, 2, [1, 2, 3389, 6778, 98251]),
  (1980, 3, [1, 3, 17, 51, 127, 381]),
  (2002, 1, [1, 79, 139, 10981]),
  (2145, 1, [1, 47, 16446217, 772972199]),
  (2184, 1, [1, 101, 127, 12827]),
  (2310, 3, [1, 3, 101, 303, 719, 2157]),
  (2340, 1, [1, 23, 529, 1594031]),
  (2520, 1, [1, 409, 2220311, 908107199]),
  (2574, 1, [1, 6691, 138629, 927566639]),
  (2730, 1, [1, 31, 31734929, 983782799]),
  (2772, 1, [1, 6679, 149561, 998917919]),
  (2860, 1, [1, 233, 457, 9679]),
  (3003, 1, [1, 5669, 190891, 1082161079]),
  (3080, 2, [1, 2, 3011, 6022, 184309]),
  (3276, 4, [1, 2, 4, 73, 146, 292, 4042943]),
  (3432, 1, [1, 5119, 241601, 1236755519]),
  (3465, 1, [1, 17, 37, 629]),
  (3640, 1, [1, 43, 30504893, 1311710399]),
  (3960, 3, [1, 3, 149, 447, 3192451, 9577353]),
  (4004, 1, [1, 89, 7921, 182159]),
  (4095, 1, [1, 443, 3331093, 1475674199]),
  (4290, 1, [1, 67, 739, 31223]),
  (4620, 3, [1, 3, 3011, 9033, 184309, 552927]),
  (4680, 2, [1, 2, 23, 46, 529]),
  (5005, 2, [1, 2, 59, 118, 509]),
  (5148, 1, [1, 17, 31, 527]),
  (5460, 1, [1, 773, 2545363, 1967565599]),
  (5544, 1, [1, 29, 3169, 21739]),
  (5720, 1, [1, 53, 227, 12031]),
  (6006, 1, [1, 257, 8421487, 2164322159]),
  (6435, 1, [1, 43, 53928293, 2318916599]),
  (6552, 1, [1, 19, 367, 571]),
  (6930, 1, [1, 61, 907, 45137]),
  (8008, 1, [1, 199, 2011, 7211]),
  (8190, 2, [1, 2, 443, 886, 3331093]),
  (8580, 1, [1, 107, 197, 21079]),
  (9009, 1, [1, 151, 21499889, 3246483239]),
  (9240, 1, [1, 23, 31, 41]),
  (10010, 1, [1, 17, 19, 29]),
  (10296, 2, [1, 2, 17, 31, 34]),
  (10920, 2, [1, 2, 773, 1546, 2545363]),
  (12012, 1, [1, 37, 103, 683]),
  (12870, 2, [1, 2, 43, 86, 53928293]),
  (13860, 1, [1, 59, 727, 42893]),
  (15015, 1, [1, 7993, 676943, 5410805399]),
  (16380, 1, [1, 79, 271, 21409]),
  (17160, 1, [1, 293, 21105043, 6183777599]),
  (18018, 2, [1, 2, 151, 302, 21499889]),
  (20020, 1, [1, 71, 463, 32873]),
  (24024, 1, [1, 179, 48364741, 8657288639]),
  (25740, 3, [1, 3, 107, 197, 321, 591]),
  (27720, 1, [1, 43, 283, 701]),
  (30030, 1, [1, 83, 277, 22991]),
  (32760, 1, [1, 2029, 5818331, 11805393599]),
  (36036, 1, [1, 53, 245017603, 12985932959]),
  (40040, 1, [1, 113, 1063, 120119]),
  (45045, 1, [1, 31, 167, 5177]),
  (51480, 1, [1, 29, 639701131, 18551332799]),
  (60060, 1, [1, 317, 3461, 19727]),
  (72072, 1, [1, 661, 39291779, 25971865919]),
  (90090, 1, [1, 180179, 180181, 32464832399]),
  (120120, 1, [1, 251, 172455949, 43286443199]),
  (180180, 1, [1, 17, 73, 191]),
  (360360, 1, [1, 89, 173, 2083])
]

private abbrev coreCertificateValid (c : ℕ × ℕ × List ℕ) : Prop :=
  c.1 ∣ 360360 ∧ 0 < c.2.1 ∧ c.2.1 < 360360 * c.1 ∧
    c.2.1 + 2 < c.2.2.toFinset.card ∧
      ∀ d ∈ c.2.2.toFinset, d ∣ 360360 * c.1 - c.2.1

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem coreCertificateValid_all :
    ∀ c ∈ coreDivisorCertificates, coreCertificateValid c := by
  decide

private def coreDivisorList : Finset ℕ :=
  (coreDivisorCertificates.map Prod.fst).toFinset

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
private theorem coreDivisorList_card : coreDivisorList.card = 192 := by
  decide

private theorem coreDivisorList_eq : coreDivisorList = (360360 : ℕ).divisors := by
  apply Finset.eq_of_subset_of_card_le
  · intro g hg
    simp only [coreDivisorList, List.mem_toFinset, List.mem_map] at hg
    obtain ⟨c, hc, rfl⟩ := hg
    exact Nat.mem_divisors.mpr ⟨(coreCertificateValid_all c hc).1, by decide⟩
  · rw [card_divisors_core, coreDivisorList_card]

/-- All 192 possible `360360 * g`, with `g` a divisor of the core, fail `P`.
This uses small explicit divisor certificates, not a search over integers. -/
theorem not_P_core_mul_divisor {g : ℕ} (hg : g ∣ 360360) : ¬ P (360360 * g) := by
  have hg' : g ∈ coreDivisorList := by
    rw [coreDivisorList_eq]
    exact Nat.mem_divisors.mpr ⟨hg, by decide⟩
  simp only [coreDivisorList, List.mem_toFinset, List.mem_map] at hg'
  obtain ⟨c, hc, rfl⟩ := hg'
  exact not_P_of_divisor_certificate (coreCertificateValid_all c hc).2

/-- A full witness above 24 would have at least 384 divisors.
No unformalized finite-range exclusion is used. -/
theorem P.sigma_zero_ge_384 {n : ℕ} (h : P n) (hn : 24 < n) : 384 ≤ σ 0 n := by
  have hd := h.dvd_360360 hn
  by_contra hsmall
  have hnd : n ∣ 360360 * 360360 := by
    by_contra hnot
    have hl := two_mul_card_divisors_le_of_not_dvd_sq (by omega : n ≠ 0) hd hnot
    rw [card_divisors_core, ← ArithmeticFunction.sigma_zero_apply] at hl
    omega
  obtain ⟨g, rfl⟩ := hd
  have hg : g ∣ 360360 := Nat.dvd_of_mul_dvd_mul_left (by decide) hnd
  exact not_P_core_mul_divisor hg h

end Erdos647

#print axioms Erdos647.two_mul_card_divisors_le_of_not_dvd_sq
#print axioms Erdos647.not_P_core_mul_divisor
#print axioms Erdos647.P.sigma_zero_ge_384
