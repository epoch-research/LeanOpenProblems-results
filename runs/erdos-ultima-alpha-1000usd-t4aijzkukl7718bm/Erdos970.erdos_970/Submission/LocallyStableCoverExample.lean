import Submission.ReoptimizedPrivateCoverExample
import Submission.SinglePrimeExchange

/-! A nonoptimal full cover stable against every one-new-prime block exchange.
This is an obstruction to a local-to-global strategy, not a disproof of970. -/
namespace Erdos970.OptimalCoverCore.LocallyStableCoverExample

set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

def primes : Finset ℕ := records.toFinset.image Prod.fst

def residues (p : ℕ) : ℕ :=
  ((records.find? (fun c => c.1 == p)).getD (0, 0, 0, 0)).2.1

lemma prime_members : ∀ p ∈ primes, p.Prime := by decide +kernel
lemma prime_card : primes.card = 101 := by decide +kernel

private lemma residue_record : ∀ c ∈ records, residues c.1 = c.2.1 := by
  decide +kernel

private lemma cover_check : (List.range 1500).all
    (fun i => records.any (fun c => i % c.1 == c.2.1)) = true := by
  decide +kernel

lemma covers : ∀ i : Fin 1500, ∃ p ∈ primes, i.val ≡ residues p [MOD p] := by
  have hc := cover_check
  simp only [List.all_eq_true, List.any_eq_true, beq_iff_eq, List.mem_range] at hc
  intro i
  obtain ⟨c, hcR, hic⟩ := hc i.val i.isLt
  refine ⟨c.1, Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hcR, rfl⟩, ?_⟩
  change i.val % c.1 = residues c.1 % c.1
  rw [residue_record c hcR, ← hic, Nat.mod_mod]

lemma full_cover : survivors 1500 primes residues = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨him, hiP⟩ := (mem_survivors _ _ _ _).mp hi
  obtain ⟨p, hp, hip⟩ := covers ⟨i, him⟩
  exact hiP p hp hip

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

private lemma residue_reduced : ∀ c ∈ records, c.2.1 % c.1 = c.2.1 := by
  decide +kernel

private lemma private_of_record_conditions (p i : ℕ) (him : i < 1500)
    (hip : i % p = residues p % p)
    (hother : ∀ d ∈ records, d.1 ≠ p → i % d.1 ≠ d.2.1) :
    i ∈ privatePositions 1500 primes residues p := by
  apply Finset.mem_filter.mpr
  refine ⟨(mem_survivors _ _ _ _).mpr ⟨him, ?_⟩, hip⟩
  intro q hq hiq
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp (Finset.mem_of_mem_erase hq)
  have hdR := List.mem_toFinset.mp hd
  apply hother d hdR (Finset.mem_erase.mp hq).1
  change i % d.1 = residues d.1 % d.1 at hiq
  simpa only [residue_record d hdR, residue_reduced d hdR] using hiq

private lemma witness_check : ∀ c ∈ records,
    c.2.2.1 ≠ c.2.2.2 ∧
    c.2.2.1 ∈ privatePositions 1500 primes residues c.1 ∧
    c.2.2.2 ∈ privatePositions 1500 primes residues c.1 := by
  intro c hc
  obtain ⟨hi, hj, hne, hip, hjp, hother⟩ := verified.2.2.2 c hc
  refine ⟨hne, ?_, ?_⟩
  · apply private_of_record_conditions c.1 c.2.2.1 hi _ (fun d hd hne => (hother d hd hne).1)
    rw [residue_record c hc, residue_reduced c hc]
    exact hip
  · apply private_of_record_conditions c.1 c.2.2.2 hj _ (fun d hd hne => (hother d hd hne).2)
    rw [residue_record c hc, residue_reduced c hc]
    exact hjp

lemma two_private : ∀ p ∈ primes, 2 ≤ (privatePositions 1500 primes residues p).card := by
  intro p hp
  obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hne, hi, hj⟩ := witness_check c (List.mem_toFinset.mp hc)
  have hh : {c.2.2.1, c.2.2.2} ⊆ privatePositions 1500 primes residues c.1 := by
    intro i hi'
    rcases Finset.mem_insert.mp hi' with rfl | hi'
    · exact hi
    · simpa only [Finset.mem_singleton.mp hi'] using hj
  simpa [hne] using Finset.card_le_card hh

private def smallWitnesses (p : ℕ) : Finset ℕ :=
  if p = 2 then {1, 3, 7, 15, 85, 93, 117} else
  if p = 3 then {2, 8, 26, 80, 122, 128, 158} else
  {4, 24, 124, 214, 234, 264, 294}

lemma small_private : ∀ p ∈ ({2, 3, 5} : Finset ℕ),
    7 ≤ (privatePositions 1500 primes residues p).card := by
  have hc : ∀ p ∈ ({2, 3, 5} : Finset ℕ),
      (smallWitnesses p).card = 7 := by decide +kernel
  have hv : ∀ p ∈ ({2, 3, 5} : Finset ℕ), ∀ i ∈ smallWitnesses p,
      i < 1500 ∧ i % p = residues p % p ∧
      ∀ d ∈ records, d.1 ≠ p → i % d.1 ≠ d.2.1 := by decide +kernel
  intro p hp
  have hsub : smallWitnesses p ⊆ privatePositions 1500 primes residues p := by
    intro i hi
    obtain ⟨him, hip, hother⟩ := hv p hp i hi
    exact private_of_record_conditions p i him hip hother
  have hh := Finset.card_le_card hsub
  rwa [hc p hp] at hh

lemma unused_prime_large (q : ℕ) (hq : q.Prime) (hqP : q ∉ primes) : 269 ≤ q := by
  have hc : ∀ q : Fin 269, q.val.Prime → ∃ c ∈ records, c.1 = q.val := by decide +kernel
  by_contra hbad
  obtain ⟨c, hcR, hcq⟩ := hc ⟨q, by omega⟩ hq
  exact hqP (Finset.mem_image.mpr ⟨c, List.mem_toFinset.mpr hcR, hcq⟩)

/-- Each class modulo an unused prime contains at most six interval positions. -/
lemma private_new_class_le_six (p q a : ℕ) (hq : 269 ≤ q) :
    ((privatePositions 1500 primes residues p).filter
      (fun i => i ≡ a [MOD q])).card ≤ 6 := by
  classical
  have hq0 : 0 < q := by omega
  have hc := Finset.card_le_card_of_injOn
    (s := (privatePositions 1500 primes residues p).filter (fun i => i ≡ a [MOD q]))
    (t := Finset.range 6) (fun i => i / q) (by
      intro i hi
      change i ∈ ((privatePositions 1500 primes residues p).filter (fun i => i ≡ a [MOD q])) at hi
      obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
      have him := ((mem_survivors _ _ _ _).mp (Finset.mem_filter.mp hi).1).1
      apply Finset.mem_range.mpr
      apply (Nat.div_lt_iff_lt_mul hq0).mpr
      omega) (by
      intro i hi j hj he
      change i ∈ ((privatePositions 1500 primes residues p).filter (fun i => i ≡ a [MOD q])) at hi
      change j ∈ ((privatePositions 1500 primes residues p).filter (fun i => i ≡ a [MOD q])) at hj
      have hiq := (Finset.mem_filter.mp hi).2
      have hjq := (Finset.mem_filter.mp hj).2
      have hm : i % q = j % q := hiq.trans hjq.symm
      have hi' := Nat.mod_add_div i q
      have hj' := Nat.mod_add_div j q
      change i / q = j / q at he
      rw [he, hm] at hi'
      omega)
  simpa using hc

lemma each_private_missed (p q a : ℕ) (hp : p ∈ primes)
    (hq : q.Prime) (hqP : q ∉ primes) :
    ∃ i ∈ privatePositions 1500 primes residues p, ¬i ≡ a [MOD q] := by
  classical
  have hqbig := unused_prime_large q hq hqP
  by_cases hsmall : p ∈ ({2, 3, 5} : Finset ℕ)
  · have hseven := small_private p hsmall
    have hsix := private_new_class_le_six p q a hqbig
    have hpart := Finset.card_filter_add_card_filter_not
      (s := privatePositions 1500 primes residues p) (fun i => i ≡ a [MOD q])
    have hpos : 0 < ((privatePositions 1500 primes residues p).filter
        (fun i => ¬i ≡ a [MOD q])).card := by omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
    exact ⟨i, (Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2⟩
  · have hp7 : 7 ≤ p := by
      have hc : ∀ v : Fin 7, v.val.Prime → v.val ∈ ({2, 3, 5} : Finset ℕ) := by
        decide +kernel
      by_contra hbad
      exact hsmall (hc ⟨p, by omega⟩ (prime_members p hp))
    apply exists_private_missed_by_new_prime 1500 primes residues p q a
      (prime_members p hp) hq _ (by nlinarith) (two_private p hp)
    intro he
    exact hqP (he ▸ hp)

/-- Erasing ANY block and inserting one unused prime, with arbitrary new residue,
strictly increases this full cover's budget. The other residues stay fixed. -/
theorem single_new_prime_stable (E : Finset ℕ) (hE : E ⊆ primes)
    (q : ℕ) (hq : q.Prime) (hqP : q ∉ primes) (s : ℕ → ℕ)
    (hagrees : ∀ p ∈ primes \ E, s p = residues p) :
    budget 1500 primes residues < budget 1500 ((primes \ E) ∪ {q}) s := by
  apply budget_lt_single_prime_replacement 1500 primes E hE residues s q hqP
    hagrees full_cover
  intro p hp
  exact each_private_missed p q (s q) (hE hp) hq hqP

/-- Nevertheless, a globally different choice of classes uses only89 primes. -/
theorem not_optimal : ¬IsOptimal 1500 primes residues := by
  intro h
  obtain ⟨Q, s, hQ, hcard, hcover, _⟩ :=
    ReoptimizedPrivateCoverExample.exists_empty_survivor_core_with_two_private
  have hb := h.2.1 Q hQ s
  simp only [budget, prime_card, full_cover, hcard, hcover, Finset.card_empty,
    Nat.add_zero] at hb
  omega

#print axioms single_new_prime_stable
#print axioms not_optimal
end Erdos970.OptimalCoverCore.LocallyStableCoverExample
