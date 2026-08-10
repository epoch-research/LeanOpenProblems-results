import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def L2000 : List Nat := [9,17,23,33,51,53,63,71,87,99,101,117,119,141,171,173,189,219,221,231,261,309,323,339,357,359,401,407,411,413,431,437,441,479,507,519,533,543,561,579,599,609,611,627,633,651,677,683,689,719,747,749,753,771,789,791,801,807,809,819,831,869,879,887,891,893,899,911,921,947,953,963,977,981,983,989,1029,1047,1107,1157,1163,1173,1179,1197,1229,1241,1247,1269,1277,1281,1289,1293,1307,1347,1359,1491,1517,1533,1541,1551,1559,1571,1589,1599,1607,1619,1647,1659,1661,1667,1727,1737,1739,1779,1787,1811,1823,1839,1841,1857,1859,1863,1871,1893,1899,1911,1949,1971,1991]
lemma L2000_nodup : L2000.Nodup := by decide
lemma L2000_bound : L2000.Forall (fun x => x < 2000) := by
  repeat constructor <;> norm_num
lemma L2000_prime : L2000.Forall (fun x => Nat.Prime (8000000 + x)) := by
  repeat constructor <;> norm_num
lemma blockL2000 : 129 ≤ Nat.count (fun k => Nat.Prime (8000000 + k)) 2000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : L2000.toFinset.card = 129 := by
    rw [List.toFinset_card_of_nodup L2000_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L2000 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp L2000_bound) x hxL, (List.forall_iff_forall_mem.mp L2000_prime) x hxL⟩
