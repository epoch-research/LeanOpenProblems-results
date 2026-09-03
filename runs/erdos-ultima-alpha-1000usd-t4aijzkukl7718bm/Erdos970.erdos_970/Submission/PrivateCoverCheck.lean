import Submission.OptimalCoverCore

/-! A finite obstruction to deducing nonempty survivor sets from private-position counts alone.
This is not asserted to be a globally optimal cover, and is not a disproof of Erdős 970. -/
namespace Erdos970.OptimalCoverCore
namespace PrivateCoverExample

private def records : List (ℕ × ℕ × ℕ × ℕ) :=
  [
    (2, 1, 1, 3),
    (3, 2, 2, 8),
    (5, 4, 4, 24),
    (7, 6, 6, 48),
    (11, 10, 10, 120),
    (13, 12, 12, 168),
    (17, 16, 16, 288),
    (19, 18, 18, 360),
    (23, 22, 22, 528),
    (29, 28, 28, 840),
    (31, 30, 30, 960),
    (37, 36, 36, 1368),
    (41, 27, 150, 232),
    (43, 0, 0, 172),
    (47, 42, 42, 136),
    (53, 17, 70, 282),
    (59, 41, 100, 336),
    (61, 21, 82, 448),
    (67, 52, 52, 856),
    (71, 40, 40, 466),
    (73, 35, 108, 400),
    (79, 33, 112, 270),
    (83, 43, 126, 292),
    (89, 17, 106, 462),
    (97, 68, 262, 456),
    (103, 89, 192, 810),
    (109, 81, 190, 408),
    (131, 49, 180, 442),
    (151, 103, 556, 858),
    (127, 121, 502, 756),
    (263, 259, 522, 1048),
    (113, 54, 280, 732),
    (577, 316, 316, 1470),
    (409, 88, 88, 906),
    (173, 153, 672, 1018),
    (229, 81, 310, 768),
    (439, 352, 352, 1230),
    (313, 147, 460, 1086),
    (211, 176, 598, 1020),
    (157, 101, 886, 1200),
    (163, 90, 742, 1068),
    (389, 372, 372, 1150),
    (233, 97, 330, 796),
    (167, 75, 576, 910),
    (191, 153, 726, 1108),
    (251, 127, 378, 880),
    (419, 102, 102, 940),
    (317, 138, 138, 772),
    (359, 312, 312, 1030),
    (401, 210, 210, 1012),
    (257, 49, 306, 820),
    (569, 348, 348, 1486),
    (283, 194, 760, 1326),
    (281, 259, 540, 1102),
    (467, 31, 498, 1432),
    (271, 196, 196, 738),
    (367, 148, 148, 882),
    (137, 130, 130, 952),
    (193, 34, 420, 1192),
    (479, 228, 228, 1186),
    (181, 103, 646, 1008),
    (433, 159, 592, 1458),
    (227, 222, 222, 676),
    (241, 105, 346, 828),
    (547, 226, 226, 1320),
    (349, 178, 178, 876),
    (179, 25, 562, 1278),
    (463, 57, 520, 1446),
    (347, 265, 612, 1306),
    (587, 276, 276, 1450),
    (379, 358, 358, 1116),
    (353, 307, 660, 1366),
    (337, 60, 60, 1408),
    (277, 268, 268, 822),
    (443, 43, 486, 1372),
    (101, 63, 366, 568),
    (139, 91, 508, 786),
    (613, 256, 256, 1482),
    (331, 46, 46, 708),
    (397, 58, 58, 852),
    (197, 38, 432, 826),
    (311, 240, 240, 862),
    (641, 156, 156, 1438),
    (593, 96, 96, 1282),
    (107, 76, 718, 1360),
    (617, 66, 66, 1300),
    (521, 438, 438, 1480),
    (383, 162, 162, 928),
    (431, 199, 630, 1492),
    (373, 9, 382, 1128),
    (307, 68, 682, 1296),
    (499, 490, 490, 1488),
    (421, 250, 250, 1092),
    (239, 140, 618, 1096),
    (223, 198, 198, 1090),
    (293, 72, 72, 658),
    (457, 238, 238, 1152),
    (199, 55, 652, 1050),
    (541, 166, 166, 1248),
    (149, 20, 616, 1212),
    (449, 78, 78, 976)
  ]

private def check : Bool :=
  records.all (fun c => decide c.1.Prime) &&
  records.all (fun c => records.all (fun d => decide (c.1 = d.1 → c = d))) &&
  (List.range 1500).all (fun i => records.any (fun c => i % c.1 == c.2.1)) &&
  records.all (fun c =>
    decide (c.2.2.1 < 1500) && decide (c.2.2.2 < 1500) &&
    decide (c.2.2.1 ≠ c.2.2.2) &&
    (c.2.2.1 % c.1 == c.2.1) && (c.2.2.2 % c.1 == c.2.1) &&
    records.all (fun d => decide (d.1 ≠ c.1 →
      c.2.2.1 % d.1 ≠ d.2.1 ∧ c.2.2.2 % d.1 ≠ d.2.1)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem check_true : check = true := by decide +kernel

private theorem records_card : records.toFinset.card = 101 := by decide +kernel

private theorem verified :
    (∀ c ∈ records, c.1.Prime) ∧
    (∀ c ∈ records, ∀ d ∈ records, c.1 = d.1 → c = d) ∧
    (∀ i : Fin 1500, ∃ c ∈ records, i.val % c.1 = c.2.1) ∧
    (∀ c ∈ records,
      c.2.2.1 < 1500 ∧ c.2.2.2 < 1500 ∧ c.2.2.1 ≠ c.2.2.2 ∧
      c.2.2.1 % c.1 = c.2.1 ∧ c.2.2.2 % c.1 = c.2.1 ∧
      ∀ d ∈ records, d.1 ≠ c.1 →
        c.2.2.1 % d.1 ≠ d.2.1 ∧ c.2.2.2 % d.1 ≠ d.2.1) := by
  have h := check_true
  simp only [check, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    List.any_eq_true, beq_iff_eq, List.mem_range] at h
  refine ⟨h.1.1.1, h.1.1.2, ?_, ?_⟩
  · intro i
    exact h.1.2 i.val i.isLt
  · intro c hc
    have hh := h.2 c hc
    exact ⟨hh.1.1.1.1.1, hh.1.1.1.1.2, hh.1.1.1.2, hh.1.1.2, hh.1.2, hh.2⟩


#print axioms check_true
#print axioms records_card
#print axioms verified
end PrivateCoverExample
end Erdos970.OptimalCoverCore
