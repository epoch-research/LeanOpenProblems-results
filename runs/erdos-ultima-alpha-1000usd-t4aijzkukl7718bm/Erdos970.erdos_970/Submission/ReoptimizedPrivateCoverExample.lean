import Submission.PrivateCoverExample

/-! A verified finite reoptimization of the private-position example.
The solver is not trusted: the full residue and private-point data are checked
in the kernel. No optimality of the new cover is asserted. -/
namespace Erdos970.OptimalCoverCore.ReoptimizedPrivateCoverExample

private def records : List (ℕ × ℕ × ℕ × ℕ) :=
  [
    (2, 1, 3, 7),
    (3, 2, 8, 26),
    (5, 4, 4, 24),
    (7, 6, 6, 48),
    (11, 10, 10, 120),
    (13, 12, 12, 168),
    (17, 16, 16, 288),
    (19, 18, 18, 360),
    (23, 22, 22, 528),
    (29, 28, 840, 1188),
    (31, 30, 960, 1270),
    (37, 36, 36, 1368),
    (41, 2, 330, 576),
    (43, 9, 52, 138),
    (47, 21, 162, 256),
    (53, 1, 372, 478),
    (59, 30, 148, 502),
    (61, 11, 72, 316),
    (67, 13, 348, 616),
    (71, 30, 172, 456),
    (73, 35, 108, 400),
    (79, 42, 42, 358),
    (83, 0, 0, 498),
    (89, 28, 562, 918),
    (97, 60, 60, 448),
    (101, 66, 66, 268),
    (103, 56, 262, 880),
    (107, 58, 58, 486),
    (109, 64, 282, 718),
    (113, 82, 82, 760),
    (127, 92, 346, 600),
    (131, 49, 180, 442),
    (137, 104, 378, 652),
    (139, 104, 382, 660),
    (149, 73, 222, 520),
    (151, 40, 40, 946),
    (157, 104, 418, 732),
    (163, 117, 280, 606),
    (167, 88, 88, 756),
    (173, 21, 540, 886),
    (179, 49, 228, 586),
    (181, 69, 250, 612),
    (191, 46, 46, 810),
    (193, 47, 240, 1012),
    (197, 1, 198, 592),
    (199, 33, 232, 630),
    (211, 100, 100, 522),
    (223, 14, 460, 906),
    (227, 130, 130, 1038),
    (229, 112, 112, 570),
    (233, 43, 276, 742),
    (239, 223, 462, 940),
    (241, 95, 336, 1300),
    (251, 55, 306, 808),
    (257, 194, 708, 1222),
    (263, 150, 150, 676),
    (269, 163, 432, 970),
    (271, 237, 508, 1050),
    (277, 189, 466, 1020),
    (281, 56, 618, 1180),
    (283, 9, 292, 858),
    (293, 73, 366, 952),
    (311, 164, 786, 1408),
    (313, 226, 226, 852),
    (331, 106, 106, 768),
    (337, 309, 646, 1320),
    (347, 78, 78, 772),
    (349, 178, 178, 876),
    (353, 156, 156, 862),
    (359, 192, 192, 910),
    (367, 21, 388, 1122),
    (379, 70, 70, 828),
    (383, 210, 210, 976),
    (389, 19, 408, 1186),
    (397, 238, 238, 1032),
    (401, 126, 126, 928),
    (421, 219, 640, 1482),
    (431, 420, 420, 1282),
    (433, 430, 430, 1296),
    (439, 352, 352, 1230),
    (443, 96, 96, 982),
    (457, 99, 556, 1470),
    (463, 136, 136, 1062),
    (479, 102, 102, 1060),
    (499, 490, 490, 1488),
    (503, 312, 312, 1318),
    (509, 270, 270, 1288),
    (523, 190, 190, 1236),
    (631, 196, 196, 1458)
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

private theorem records_card : records.toFinset.card = 89 := by decide +kernel

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

/-- A completely covered interval can have two private positions for every class.
The conditions here do not include global budget optimality. -/
theorem exists_empty_survivor_core_with_two_private :
    ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ P.card = 89 ∧
      survivors 1500 P r = ∅ ∧
      ∀ p ∈ P, 2 ≤ (privatePositions 1500 P r p).card := by
  exact exists_full_cover_of_private_witnesses 1500 89 records verified records_card


/-- An actual finite Jacobsthal lower bound, not an asymptotic disproof. -/
theorem not_bound_1500 : ¬IsJacobsthalBound 89 1500 := by
  obtain ⟨P, r, hP, hcard, hs, _⟩ := exists_empty_survivor_core_with_two_private
  apply (not_isJacobsthalBound_iff_cover 89 1500).mpr
  refine ⟨P, hP, by omega, r, ?_⟩
  intro i hi
  by_contra hbad
  push_neg at hbad
  have hh := (mem_survivors 1500 P r i).mpr ⟨hi, hbad⟩
  simpa only [hs, Finset.notMem_empty] using hh

theorem jacobsthalFunction_eighty_nine_gt : 1500 < jacobsthalFunction 89 := by
  apply Nat.lt_of_not_ge
  intro h
  exact not_bound_1500 ((jacobsthalFunction_le_iff 89 1500).mp h)

/-- Hence the old 101-class full cover is not globally budget-optimal, despite
having at least two private positions for every retained class. -/
theorem exists_nonoptimal_private_core :
    ∃ P : Finset ℕ, ∃ r : ℕ → ℕ,
      (∀ p ∈ P, p.Prime) ∧ P.card = 101 ∧
      survivors 1500 P r = ∅ ∧
      (∀ p ∈ P, 2 ≤ (privatePositions 1500 P r p).card) ∧
      ¬IsOptimal 1500 P r := by
  obtain ⟨P, r, hP, hcard, hcover, hprivate⟩ :=
    PrivateCoverExample.exists_empty_survivor_core_with_two_private
  obtain ⟨Q, s, hQ, hQcard, hQcover, _⟩ :=
    exists_empty_survivor_core_with_two_private
  refine ⟨P, r, hP, hcard, hcover, hprivate, ?_⟩
  intro hopt
  have hb := hopt.2.1 Q hQ s
  simp only [budget, hcard, hcover, hQcard, hQcover, Finset.card_empty,
    Nat.add_zero] at hb
  omega

#print axioms exists_empty_survivor_core_with_two_private
#print axioms exists_nonoptimal_private_core
#print axioms jacobsthalFunction_eighty_nine_gt
end Erdos970.OptimalCoverCore.ReoptimizedPrivateCoverExample
