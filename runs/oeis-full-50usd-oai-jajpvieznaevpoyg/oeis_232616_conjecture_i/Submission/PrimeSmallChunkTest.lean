import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def PB0 : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997]
lemma PB0_nodup : PB0.Nodup := by decide
lemma PB0_bound : PB0.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB0_prime : PB0.Forall (fun x => Nat.Prime (0 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_0 : 168 ≤ Nat.count (fun k => Nat.Prime (0 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB0.toFinset.card = 168 := by
    rw [List.toFinset_card_of_nodup PB0_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB0 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB0_bound) x hxL, (List.forall_iff_forall_mem.mp PB0_prime) x hxL⟩
def PB1 : List Nat := [9,13,19,21,31,33,39,49,51,61,63,69,87,91,93,97,103,109,117,123,129,151,153,163,171,181,187,193,201,213,217,223,229,231,237,249,259,277,279,283,289,291,297,301,303,307,319,321,327,361,367,373,381,399,409,423,427,429,433,439,447,451,453,459,471,481,483,487,489,493,499,511,523,531,543,549,553,559,567,571,579,583,597,601,607,609,613,619,621,627,637,657,663,667,669,693,697,699,709,721,723,733,741,747,753,759,777,783,787,789,801,811,823,831,847,861,867,871,873,877,879,889,901,907,913,931,933,949,951,973,979,987,993,997,999]
lemma PB1_nodup : PB1.Nodup := by decide
lemma PB1_bound : PB1.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB1_prime : PB1.Forall (fun x => Nat.Prime (1000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_1 : 135 ≤ Nat.count (fun k => Nat.Prime (1000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB1.toFinset.card = 135 := by
    rw [List.toFinset_card_of_nodup PB1_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB1 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB1_bound) x hxL, (List.forall_iff_forall_mem.mp PB1_prime) x hxL⟩
def PB2 : List Nat := [3,11,17,27,29,39,53,63,69,81,83,87,89,99,111,113,129,131,137,141,143,153,161,179,203,207,213,221,237,239,243,251,267,269,273,281,287,293,297,309,311,333,339,341,347,351,357,371,377,381,383,389,393,399,411,417,423,437,441,447,459,467,473,477,503,521,531,539,543,549,551,557,579,591,593,609,617,621,633,647,657,659,663,671,677,683,687,689,693,699,707,711,713,719,729,731,741,749,753,767,777,789,791,797,801,803,819,833,837,843,851,857,861,879,887,897,903,909,917,927,939,953,957,963,969,971,999]
lemma PB2_nodup : PB2.Nodup := by decide
lemma PB2_bound : PB2.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB2_prime : PB2.Forall (fun x => Nat.Prime (2000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_2 : 127 ≤ Nat.count (fun k => Nat.Prime (2000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB2.toFinset.card = 127 := by
    rw [List.toFinset_card_of_nodup PB2_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB2 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB2_bound) x hxL, (List.forall_iff_forall_mem.mp PB2_prime) x hxL⟩
def PB3 : List Nat := [1,11,19,23,37,41,49,61,67,79,83,89,109,119,121,137,163,167,169,181,187,191,203,209,217,221,229,251,253,257,259,271,299,301,307,313,319,323,329,331,343,347,359,361,371,373,389,391,407,413,433,449,457,461,463,467,469,491,499,511,517,527,529,533,539,541,547,557,559,571,581,583,593,607,613,617,623,631,637,643,659,671,673,677,691,697,701,709,719,727,733,739,761,767,769,779,793,797,803,821,823,833,847,851,853,863,877,881,889,907,911,917,919,923,929,931,943,947,967,989]
lemma PB3_nodup : PB3.Nodup := by decide
lemma PB3_bound : PB3.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB3_prime : PB3.Forall (fun x => Nat.Prime (3000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_3 : 120 ≤ Nat.count (fun k => Nat.Prime (3000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB3.toFinset.card = 120 := by
    rw [List.toFinset_card_of_nodup PB3_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB3 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB3_bound) x hxL, (List.forall_iff_forall_mem.mp PB3_prime) x hxL⟩
def PB4 : List Nat := [1,3,7,13,19,21,27,49,51,57,73,79,91,93,99,111,127,129,133,139,153,157,159,177,201,211,217,219,229,231,241,243,253,259,261,271,273,283,289,297,327,337,339,349,357,363,373,391,397,409,421,423,441,447,451,457,463,481,483,493,507,513,517,519,523,547,549,561,567,583,591,597,603,621,637,639,643,649,651,657,663,673,679,691,703,721,723,729,733,751,759,783,787,789,793,799,801,813,817,831,861,871,877,889,903,909,919,931,933,937,943,951,957,967,969,973,987,993,999]
lemma PB4_nodup : PB4.Nodup := by decide
lemma PB4_bound : PB4.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB4_prime : PB4.Forall (fun x => Nat.Prime (4000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_4 : 119 ≤ Nat.count (fun k => Nat.Prime (4000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB4.toFinset.card = 119 := by
    rw [List.toFinset_card_of_nodup PB4_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB4 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB4_bound) x hxL, (List.forall_iff_forall_mem.mp PB4_prime) x hxL⟩
def PB5 : List Nat := [3,9,11,21,23,39,51,59,77,81,87,99,101,107,113,119,147,153,167,171,179,189,197,209,227,231,233,237,261,273,279,281,297,303,309,323,333,347,351,381,387,393,399,407,413,417,419,431,437,441,443,449,471,477,479,483,501,503,507,519,521,527,531,557,563,569,573,581,591,623,639,641,647,651,653,657,659,669,683,689,693,701,711,717,737,741,743,749,779,783,791,801,807,813,821,827,839,843,849,851,857,861,867,869,879,881,897,903,923,927,939,953,981,987]
lemma PB5_nodup : PB5.Nodup := by decide
lemma PB5_bound : PB5.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB5_prime : PB5.Forall (fun x => Nat.Prime (5000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_5 : 114 ≤ Nat.count (fun k => Nat.Prime (5000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB5.toFinset.card = 114 := by
    rw [List.toFinset_card_of_nodup PB5_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB5 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB5_bound) x hxL, (List.forall_iff_forall_mem.mp PB5_prime) x hxL⟩
def PB6 : List Nat := [7,11,29,37,43,47,53,67,73,79,89,91,101,113,121,131,133,143,151,163,173,197,199,203,211,217,221,229,247,257,263,269,271,277,287,299,301,311,317,323,329,337,343,353,359,361,367,373,379,389,397,421,427,449,451,469,473,481,491,521,529,547,551,553,563,569,571,577,581,599,607,619,637,653,659,661,673,679,689,691,701,703,709,719,733,737,761,763,779,781,791,793,803,823,827,829,833,841,857,863,869,871,883,899,907,911,917,947,949,959,961,967,971,977,983,991,997]
lemma PB6_nodup : PB6.Nodup := by decide
lemma PB6_bound : PB6.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB6_prime : PB6.Forall (fun x => Nat.Prime (6000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_6 : 117 ≤ Nat.count (fun k => Nat.Prime (6000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB6.toFinset.card = 117 := by
    rw [List.toFinset_card_of_nodup PB6_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB6 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB6_bound) x hxL, (List.forall_iff_forall_mem.mp PB6_prime) x hxL⟩
def PB7 : List Nat := [1,13,19,27,39,43,57,69,79,103,109,121,127,129,151,159,177,187,193,207,211,213,219,229,237,243,247,253,283,297,307,309,321,331,333,349,351,369,393,411,417,433,451,457,459,477,481,487,489,499,507,517,523,529,537,541,547,549,559,561,573,577,583,589,591,603,607,621,639,643,649,669,673,681,687,691,699,703,717,723,727,741,753,757,759,789,793,817,823,829,841,853,867,873,877,879,883,901,907,919,927,933,937,949,951,963,993]
lemma PB7_nodup : PB7.Nodup := by decide
lemma PB7_bound : PB7.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB7_prime : PB7.Forall (fun x => Nat.Prime (7000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_7 : 107 ≤ Nat.count (fun k => Nat.Prime (7000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB7.toFinset.card = 107 := by
    rw [List.toFinset_card_of_nodup PB7_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB7 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB7_bound) x hxL, (List.forall_iff_forall_mem.mp PB7_prime) x hxL⟩
def PB8 : List Nat := [9,11,17,39,53,59,69,81,87,89,93,101,111,117,123,147,161,167,171,179,191,209,219,221,231,233,237,243,263,269,273,287,291,293,297,311,317,329,353,363,369,377,387,389,419,423,429,431,443,447,461,467,501,513,521,527,537,539,543,563,573,581,597,599,609,623,627,629,641,647,663,669,677,681,689,693,699,707,713,719,731,737,741,747,753,761,779,783,803,807,819,821,831,837,839,849,861,863,867,887,893,923,929,933,941,951,963,969,971,999]
lemma PB8_nodup : PB8.Nodup := by decide
lemma PB8_bound : PB8.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB8_prime : PB8.Forall (fun x => Nat.Prime (8000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_8 : 110 ≤ Nat.count (fun k => Nat.Prime (8000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB8.toFinset.card = 110 := by
    rw [List.toFinset_card_of_nodup PB8_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB8 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB8_bound) x hxL, (List.forall_iff_forall_mem.mp PB8_prime) x hxL⟩
def PB9 : List Nat := [1,7,11,13,29,41,43,49,59,67,91,103,109,127,133,137,151,157,161,173,181,187,199,203,209,221,227,239,241,257,277,281,283,293,311,319,323,337,341,343,349,371,377,391,397,403,413,419,421,431,433,437,439,461,463,467,473,479,491,497,511,521,533,539,547,551,587,601,613,619,623,629,631,643,649,661,677,679,689,697,719,721,733,739,743,749,767,769,781,787,791,803,811,817,829,833,839,851,857,859,871,883,887,901,907,923,929,931,941,949,967,973]
lemma PB9_nodup : PB9.Nodup := by decide
lemma PB9_bound : PB9.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB9_prime : PB9.Forall (fun x => Nat.Prime (9000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_9 : 112 ≤ Nat.count (fun k => Nat.Prime (9000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB9.toFinset.card = 112 := by
    rw [List.toFinset_card_of_nodup PB9_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB9 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB9_bound) x hxL, (List.forall_iff_forall_mem.mp PB9_prime) x hxL⟩
def PB10 : List Nat := [7,9,37,39,61,67,69,79,91,93,99,103,111,133,139,141,151,159,163,169,177,181,193,211,223,243,247,253,259,267,271,273,289,301,303,313,321,331,333,337,343,357,369,391,399,427,429,433,453,457,459,463,477,487,499,501,513,529,531,559,567,589,597,601,607,613,627,631,639,651,657,663,667,687,691,709,711,723,729,733,739,753,771,781,789,799,831,837,847,853,859,861,867,883,889,891,903,909,937,939,949,957,973,979,987,993]
lemma PB10_nodup : PB10.Nodup := by decide
lemma PB10_bound : PB10.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB10_prime : PB10.Forall (fun x => Nat.Prime (10000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_10 : 106 ≤ Nat.count (fun k => Nat.Prime (10000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB10.toFinset.card = 106 := by
    rw [List.toFinset_card_of_nodup PB10_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB10 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB10_bound) x hxL, (List.forall_iff_forall_mem.mp PB10_prime) x hxL⟩
def PB11 : List Nat := [3,27,47,57,59,69,71,83,87,93,113,117,119,131,149,159,161,171,173,177,197,213,239,243,251,257,261,273,279,287,299,311,317,321,329,351,353,369,383,393,399,411,423,437,443,447,467,471,483,489,491,497,503,519,527,549,551,579,587,593,597,617,621,633,657,677,681,689,699,701,717,719,731,743,777,779,783,789,801,807,813,821,827,831,833,839,863,867,887,897,903,909,923,927,933,939,941,953,959,969,971,981,987]
lemma PB11_nodup : PB11.Nodup := by decide
lemma PB11_bound : PB11.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB11_prime : PB11.Forall (fun x => Nat.Prime (11000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_11 : 103 ≤ Nat.count (fun k => Nat.Prime (11000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB11.toFinset.card = 103 := by
    rw [List.toFinset_card_of_nodup PB11_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB11 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB11_bound) x hxL, (List.forall_iff_forall_mem.mp PB11_prime) x hxL⟩
def PB12 : List Nat := [7,11,37,41,43,49,71,73,97,101,107,109,113,119,143,149,157,161,163,197,203,211,227,239,241,251,253,263,269,277,281,289,301,323,329,343,347,373,377,379,391,401,409,413,421,433,437,451,457,473,479,487,491,497,503,511,517,527,539,541,547,553,569,577,583,589,601,611,613,619,637,641,647,653,659,671,689,697,703,713,721,739,743,757,763,781,791,799,809,821,823,829,841,853,889,893,899,907,911,917,919,923,941,953,959,967,973,979,983]
lemma PB12_nodup : PB12.Nodup := by decide
lemma PB12_bound : PB12.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB12_prime : PB12.Forall (fun x => Nat.Prime (12000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_12 : 109 ≤ Nat.count (fun k => Nat.Prime (12000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB12.toFinset.card = 109 := by
    rw [List.toFinset_card_of_nodup PB12_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB12 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB12_bound) x hxL, (List.forall_iff_forall_mem.mp PB12_prime) x hxL⟩
def PB13 : List Nat := [1,3,7,9,33,37,43,49,63,93,99,103,109,121,127,147,151,159,163,171,177,183,187,217,219,229,241,249,259,267,291,297,309,313,327,331,337,339,367,381,397,399,411,417,421,441,451,457,463,469,477,487,499,513,523,537,553,567,577,591,597,613,619,627,633,649,669,679,681,687,691,693,697,709,711,721,723,729,751,757,759,763,781,789,799,807,829,831,841,859,873,877,879,883,901,903,907,913,921,931,933,963,967,997,999]
lemma PB13_nodup : PB13.Nodup := by decide
lemma PB13_bound : PB13.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB13_prime : PB13.Forall (fun x => Nat.Prime (13000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_13 : 105 ≤ Nat.count (fun k => Nat.Prime (13000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB13.toFinset.card = 105 := by
    rw [List.toFinset_card_of_nodup PB13_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB13 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB13_bound) x hxL, (List.forall_iff_forall_mem.mp PB13_prime) x hxL⟩
def PB14 : List Nat := [9,11,29,33,51,57,71,81,83,87,107,143,149,153,159,173,177,197,207,221,243,249,251,281,293,303,321,323,327,341,347,369,387,389,401,407,411,419,423,431,437,447,449,461,479,489,503,519,533,537,543,549,551,557,561,563,591,593,621,627,629,633,639,653,657,669,683,699,713,717,723,731,737,741,747,753,759,767,771,779,783,797,813,821,827,831,843,851,867,869,879,887,891,897,923,929,939,947,951,957,969,983]
lemma PB14_nodup : PB14.Nodup := by decide
lemma PB14_bound : PB14.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB14_prime : PB14.Forall (fun x => Nat.Prime (14000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_14 : 102 ≤ Nat.count (fun k => Nat.Prime (14000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB14.toFinset.card = 102 := by
    rw [List.toFinset_card_of_nodup PB14_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB14 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB14_bound) x hxL, (List.forall_iff_forall_mem.mp PB14_prime) x hxL⟩
def PB15 : List Nat := [13,17,31,53,61,73,77,83,91,101,107,121,131,137,139,149,161,173,187,193,199,217,227,233,241,259,263,269,271,277,287,289,299,307,313,319,329,331,349,359,361,373,377,383,391,401,413,427,439,443,451,461,467,473,493,497,511,527,541,551,559,569,581,583,601,607,619,629,641,643,647,649,661,667,671,679,683,727,731,733,737,739,749,761,767,773,787,791,797,803,809,817,823,859,877,881,887,889,901,907,913,919,923,937,959,971,973,991]
lemma PB15_nodup : PB15.Nodup := by decide
lemma PB15_bound : PB15.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB15_prime : PB15.Forall (fun x => Nat.Prime (15000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_15 : 108 ≤ Nat.count (fun k => Nat.Prime (15000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB15.toFinset.card = 108 := by
    rw [List.toFinset_card_of_nodup PB15_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB15 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB15_bound) x hxL, (List.forall_iff_forall_mem.mp PB15_prime) x hxL⟩
def PB16 : List Nat := [1,7,33,57,61,63,67,69,73,87,91,97,103,111,127,139,141,183,187,189,193,217,223,229,231,249,253,267,273,301,319,333,339,349,361,363,369,381,411,417,421,427,433,447,451,453,477,481,487,493,519,529,547,553,561,567,573,603,607,619,631,633,649,651,657,661,673,691,693,699,703,729,741,747,759,763,787,811,823,829,831,843,871,879,883,889,901,903,921,927,931,937,943,963,979,981,987,993]
lemma PB16_nodup : PB16.Nodup := by decide
lemma PB16_bound : PB16.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB16_prime : PB16.Forall (fun x => Nat.Prime (16000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_16 : 98 ≤ Nat.count (fun k => Nat.Prime (16000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB16.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB16_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB16 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB16_bound) x hxL, (List.forall_iff_forall_mem.mp PB16_prime) x hxL⟩
def PB17 : List Nat := [11,21,27,29,33,41,47,53,77,93,99,107,117,123,137,159,167,183,189,191,203,207,209,231,239,257,291,293,299,317,321,327,333,341,351,359,377,383,387,389,393,401,417,419,431,443,449,467,471,477,483,489,491,497,509,519,539,551,569,573,579,581,597,599,609,623,627,657,659,669,681,683,707,713,729,737,747,749,761,783,789,791,807,827,837,839,851,863,881,891,903,909,911,921,923,929,939,957,959,971,977,981,987,989]
lemma PB17_nodup : PB17.Nodup := by decide
lemma PB17_bound : PB17.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB17_prime : PB17.Forall (fun x => Nat.Prime (17000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_17 : 104 ≤ Nat.count (fun k => Nat.Prime (17000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB17.toFinset.card = 104 := by
    rw [List.toFinset_card_of_nodup PB17_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB17 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB17_bound) x hxL, (List.forall_iff_forall_mem.mp PB17_prime) x hxL⟩
def PB18 : List Nat := [13,41,43,47,49,59,61,77,89,97,119,121,127,131,133,143,149,169,181,191,199,211,217,223,229,233,251,253,257,269,287,289,301,307,311,313,329,341,353,367,371,379,397,401,413,427,433,439,443,451,457,461,481,493,503,517,521,523,539,541,553,583,587,593,617,637,661,671,679,691,701,713,719,731,743,749,757,773,787,793,797,803,839,859,869,899,911,913,917,919,947,959,973,979]
lemma PB18_nodup : PB18.Nodup := by decide
lemma PB18_bound : PB18.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB18_prime : PB18.Forall (fun x => Nat.Prime (18000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_18 : 94 ≤ Nat.count (fun k => Nat.Prime (18000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB18.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB18_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB18 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB18_bound) x hxL, (List.forall_iff_forall_mem.mp PB18_prime) x hxL⟩
def PB19 : List Nat := [1,9,13,31,37,51,69,73,79,81,87,121,139,141,157,163,181,183,207,211,213,219,231,237,249,259,267,273,289,301,309,319,333,373,379,381,387,391,403,417,421,423,427,429,433,441,447,457,463,469,471,477,483,489,501,507,531,541,543,553,559,571,577,583,597,603,609,661,681,687,697,699,709,717,727,739,751,753,759,763,777,793,801,813,819,841,843,853,861,867,889,891,913,919,927,937,949,961,963,973,979,991,993,997]
lemma PB19_nodup : PB19.Nodup := by decide
lemma PB19_bound : PB19.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB19_prime : PB19.Forall (fun x => Nat.Prime (19000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_19 : 104 ≤ Nat.count (fun k => Nat.Prime (19000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB19.toFinset.card = 104 := by
    rw [List.toFinset_card_of_nodup PB19_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB19 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB19_bound) x hxL, (List.forall_iff_forall_mem.mp PB19_prime) x hxL⟩
def PB20 : List Nat := [11,21,23,29,47,51,63,71,89,101,107,113,117,123,129,143,147,149,161,173,177,183,201,219,231,233,249,261,269,287,297,323,327,333,341,347,353,357,359,369,389,393,399,407,411,431,441,443,477,479,483,507,509,521,533,543,549,551,563,593,599,611,627,639,641,663,681,693,707,717,719,731,743,747,749,753,759,771,773,789,807,809,849,857,873,879,887,897,899,903,921,929,939,947,959,963,981,983]
lemma PB20_nodup : PB20.Nodup := by decide
lemma PB20_bound : PB20.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB20_prime : PB20.Forall (fun x => Nat.Prime (20000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_20 : 98 ≤ Nat.count (fun k => Nat.Prime (20000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB20.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB20_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB20 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB20_bound) x hxL, (List.forall_iff_forall_mem.mp PB20_prime) x hxL⟩
def PB21 : List Nat := [1,11,13,17,19,23,31,59,61,67,89,101,107,121,139,143,149,157,163,169,179,187,191,193,211,221,227,247,269,277,283,313,317,319,323,341,347,377,379,383,391,397,401,407,419,433,467,481,487,491,493,499,503,517,521,523,529,557,559,563,569,577,587,589,599,601,611,613,617,647,649,661,673,683,701,713,727,737,739,751,757,767,773,787,799,803,817,821,839,841,851,859,863,871,881,893,911,929,937,943,961,977,991,997]
lemma PB21_nodup : PB21.Nodup := by decide
lemma PB21_bound : PB21.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB21_prime : PB21.Forall (fun x => Nat.Prime (21000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_21 : 104 ≤ Nat.count (fun k => Nat.Prime (21000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB21.toFinset.card = 104 := by
    rw [List.toFinset_card_of_nodup PB21_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB21 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB21_bound) x hxL, (List.forall_iff_forall_mem.mp PB21_prime) x hxL⟩
def PB22 : List Nat := [3,13,27,31,37,39,51,63,67,73,79,91,93,109,111,123,129,133,147,153,157,159,171,189,193,229,247,259,271,273,277,279,283,291,303,307,343,349,367,369,381,391,397,409,433,441,447,453,469,481,483,501,511,531,541,543,549,567,571,573,613,619,621,637,639,643,651,669,679,691,697,699,709,717,721,727,739,741,751,769,777,783,787,807,811,817,853,859,861,871,877,901,907,921,937,943,961,963,973,993]
lemma PB22_nodup : PB22.Nodup := by decide
lemma PB22_bound : PB22.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB22_prime : PB22.Forall (fun x => Nat.Prime (22000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_22 : 100 ≤ Nat.count (fun k => Nat.Prime (22000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB22.toFinset.card = 100 := by
    rw [List.toFinset_card_of_nodup PB22_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB22 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB22_bound) x hxL, (List.forall_iff_forall_mem.mp PB22_prime) x hxL⟩
def PB23 : List Nat := [3,11,17,21,27,29,39,41,53,57,59,63,71,81,87,99,117,131,143,159,167,173,189,197,201,203,209,227,251,269,279,291,293,297,311,321,327,333,339,357,369,371,399,417,431,447,459,473,497,509,531,537,539,549,557,561,563,567,581,593,599,603,609,623,627,629,633,663,669,671,677,687,689,719,741,743,747,753,761,767,773,789,801,813,819,827,831,833,857,869,873,879,887,893,899,909,911,917,929,957,971,977,981,993]
lemma PB23_nodup : PB23.Nodup := by decide
lemma PB23_bound : PB23.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB23_prime : PB23.Forall (fun x => Nat.Prime (23000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_23 : 104 ≤ Nat.count (fun k => Nat.Prime (23000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB23.toFinset.card = 104 := by
    rw [List.toFinset_card_of_nodup PB23_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB23 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB23_bound) x hxL, (List.forall_iff_forall_mem.mp PB23_prime) x hxL⟩
def PB24 : List Nat := [1,7,19,23,29,43,49,61,71,77,83,91,97,103,107,109,113,121,133,137,151,169,179,181,197,203,223,229,239,247,251,281,317,329,337,359,371,373,379,391,407,413,419,421,439,443,469,473,481,499,509,517,527,533,547,551,571,593,611,623,631,659,671,677,683,691,697,709,733,749,763,767,781,793,799,809,821,841,847,851,859,877,889,907,917,919,923,943,953,967,971,977,979,989]
lemma PB24_nodup : PB24.Nodup := by decide
lemma PB24_bound : PB24.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB24_prime : PB24.Forall (fun x => Nat.Prime (24000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_24 : 94 ≤ Nat.count (fun k => Nat.Prime (24000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB24.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB24_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB24 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB24_bound) x hxL, (List.forall_iff_forall_mem.mp PB24_prime) x hxL⟩
def PB25 : List Nat := [13,31,33,37,57,73,87,97,111,117,121,127,147,153,163,169,171,183,189,219,229,237,243,247,253,261,301,303,307,309,321,339,343,349,357,367,373,391,409,411,423,439,447,453,457,463,469,471,523,537,541,561,577,579,583,589,601,603,609,621,633,639,643,657,667,673,679,693,703,717,733,741,747,759,763,771,793,799,801,819,841,847,849,867,873,889,903,913,919,931,933,939,943,951,969,981,997,999]
lemma PB25_nodup : PB25.Nodup := by decide
lemma PB25_bound : PB25.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB25_prime : PB25.Forall (fun x => Nat.Prime (25000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_25 : 98 ≤ Nat.count (fun k => Nat.Prime (25000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB25.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB25_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB25 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB25_bound) x hxL, (List.forall_iff_forall_mem.mp PB25_prime) x hxL⟩
def PB26 : List Nat := [3,17,21,29,41,53,83,99,107,111,113,119,141,153,161,171,177,183,189,203,209,227,237,249,251,261,263,267,293,297,309,317,321,339,347,357,371,387,393,399,407,417,423,431,437,449,459,479,489,497,501,513,539,557,561,573,591,597,627,633,641,647,669,681,683,687,693,699,701,711,713,717,723,729,731,737,759,777,783,801,813,821,833,839,849,861,863,879,881,891,893,903,921,927,947,951,953,959,981,987,993]
lemma PB26_nodup : PB26.Nodup := by decide
lemma PB26_bound : PB26.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB26_prime : PB26.Forall (fun x => Nat.Prime (26000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_26 : 101 ≤ Nat.count (fun k => Nat.Prime (26000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB26.toFinset.card = 101 := by
    rw [List.toFinset_card_of_nodup PB26_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB26 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB26_bound) x hxL, (List.forall_iff_forall_mem.mp PB26_prime) x hxL⟩
def PB27 : List Nat := [11,17,31,43,59,61,67,73,77,91,103,107,109,127,143,179,191,197,211,239,241,253,259,271,277,281,283,299,329,337,361,367,397,407,409,427,431,437,449,457,479,481,487,509,527,529,539,541,551,581,583,611,617,631,647,653,673,689,691,697,701,733,737,739,743,749,751,763,767,773,779,791,793,799,803,809,817,823,827,847,851,883,893,901,917,919,941,943,947,953,961,967,983,997]
lemma PB27_nodup : PB27.Nodup := by decide
lemma PB27_bound : PB27.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB27_prime : PB27.Forall (fun x => Nat.Prime (27000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_27 : 94 ≤ Nat.count (fun k => Nat.Prime (27000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB27.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB27_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB27 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB27_bound) x hxL, (List.forall_iff_forall_mem.mp PB27_prime) x hxL⟩
def PB28 : List Nat := [1,19,27,31,51,57,69,81,87,97,99,109,111,123,151,163,181,183,201,211,219,229,277,279,283,289,297,307,309,319,349,351,387,393,403,409,411,429,433,439,447,463,477,493,499,513,517,537,541,547,549,559,571,573,579,591,597,603,607,619,621,627,631,643,649,657,661,663,669,687,697,703,711,723,729,751,753,759,771,789,793,807,813,817,837,843,859,867,871,879,901,909,921,927,933,949,961,979]
lemma PB28_nodup : PB28.Nodup := by decide
lemma PB28_bound : PB28.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB28_prime : PB28.Forall (fun x => Nat.Prime (28000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_28 : 98 ≤ Nat.count (fun k => Nat.Prime (28000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB28.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB28_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB28 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB28_bound) x hxL, (List.forall_iff_forall_mem.mp PB28_prime) x hxL⟩
def PB29 : List Nat := [9,17,21,23,27,33,59,63,77,101,123,129,131,137,147,153,167,173,179,191,201,207,209,221,231,243,251,269,287,297,303,311,327,333,339,347,363,383,387,389,399,401,411,423,429,437,443,453,473,483,501,527,531,537,567,569,573,581,587,599,611,629,633,641,663,669,671,683,717,723,741,753,759,761,789,803,819,833,837,851,863,867,873,879,881,917,921,927,947,959,983,989]
lemma PB29_nodup : PB29.Nodup := by decide
lemma PB29_bound : PB29.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB29_prime : PB29.Forall (fun x => Nat.Prime (29000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_29 : 92 ≤ Nat.count (fun k => Nat.Prime (29000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB29.toFinset.card = 92 := by
    rw [List.toFinset_card_of_nodup PB29_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB29 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB29_bound) x hxL, (List.forall_iff_forall_mem.mp PB29_prime) x hxL⟩
def PB30 : List Nat := [11,13,29,47,59,71,89,91,97,103,109,113,119,133,137,139,161,169,181,187,197,203,211,223,241,253,259,269,271,293,307,313,319,323,341,347,367,389,391,403,427,431,449,467,469,491,493,497,509,517,529,539,553,557,559,577,593,631,637,643,649,661,671,677,689,697,703,707,713,727,757,763,773,781,803,809,817,829,839,841,851,853,859,869,871,881,893,911,931,937,941,949,971,977,983]
lemma PB30_nodup : PB30.Nodup := by decide
lemma PB30_bound : PB30.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB30_prime : PB30.Forall (fun x => Nat.Prime (30000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_30 : 95 ≤ Nat.count (fun k => Nat.Prime (30000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB30.toFinset.card = 95 := by
    rw [List.toFinset_card_of_nodup PB30_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB30 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB30_bound) x hxL, (List.forall_iff_forall_mem.mp PB30_prime) x hxL⟩
def PB31 : List Nat := [13,19,33,39,51,63,69,79,81,91,121,123,139,147,151,153,159,177,181,183,189,193,219,223,231,237,247,249,253,259,267,271,277,307,319,321,327,333,337,357,379,387,391,393,397,469,477,481,489,511,513,517,531,541,543,547,567,573,583,601,607,627,643,649,657,663,667,687,699,721,723,727,729,741,751,769,771,793,799,817,847,849,859,873,883,891,907,957,963,973,981,991]
lemma PB31_nodup : PB31.Nodup := by decide
lemma PB31_bound : PB31.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB31_prime : PB31.Forall (fun x => Nat.Prime (31000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_31 : 92 ≤ Nat.count (fun k => Nat.Prime (31000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB31.toFinset.card = 92 := by
    rw [List.toFinset_card_of_nodup PB31_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB31 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB31_bound) x hxL, (List.forall_iff_forall_mem.mp PB31_prime) x hxL⟩
def PB32 : List Nat := [3,9,27,29,51,57,59,63,69,77,83,89,99,117,119,141,143,159,173,183,189,191,203,213,233,237,251,257,261,297,299,303,309,321,323,327,341,353,359,363,369,371,377,381,401,411,413,423,429,441,443,467,479,491,497,503,507,531,533,537,561,563,569,573,579,587,603,609,611,621,633,647,653,687,693,707,713,717,719,749,771,779,783,789,797,801,803,831,833,839,843,869,887,909,911,917,933,939,941,957,969,971,983,987,993,999]
lemma PB32_nodup : PB32.Nodup := by decide
lemma PB32_bound : PB32.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB32_prime : PB32.Forall (fun x => Nat.Prime (32000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_32 : 106 ≤ Nat.count (fun k => Nat.Prime (32000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB32.toFinset.card = 106 := by
    rw [List.toFinset_card_of_nodup PB32_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB32 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB32_bound) x hxL, (List.forall_iff_forall_mem.mp PB32_prime) x hxL⟩
def PB33 : List Nat := [13,23,29,37,49,53,71,73,83,91,107,113,119,149,151,161,179,181,191,199,203,211,223,247,287,289,301,311,317,329,331,343,347,349,353,359,377,391,403,409,413,427,457,461,469,479,487,493,503,521,529,533,547,563,569,577,581,587,589,599,601,613,617,619,623,629,637,641,647,679,703,713,721,739,749,751,757,767,769,773,791,797,809,811,827,829,851,857,863,871,889,893,911,923,931,937,941,961,967,997]
lemma PB33_nodup : PB33.Nodup := by decide
lemma PB33_bound : PB33.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB33_prime : PB33.Forall (fun x => Nat.Prime (33000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_33 : 100 ≤ Nat.count (fun k => Nat.Prime (33000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB33.toFinset.card = 100 := by
    rw [List.toFinset_card_of_nodup PB33_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB33 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB33_bound) x hxL, (List.forall_iff_forall_mem.mp PB33_prime) x hxL⟩
def PB34 : List Nat := [19,31,33,39,57,61,123,127,129,141,147,157,159,171,183,211,213,217,231,253,259,261,267,273,283,297,301,303,313,319,327,337,351,361,367,369,381,403,421,429,439,457,469,471,483,487,499,501,511,513,519,537,543,549,583,589,591,603,607,613,631,649,651,667,673,679,687,693,703,721,729,739,747,757,759,763,781,807,819,841,843,847,849,871,877,883,897,913,919,939,949,961,963,981]
lemma PB34_nodup : PB34.Nodup := by decide
lemma PB34_bound : PB34.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB34_prime : PB34.Forall (fun x => Nat.Prime (34000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_34 : 94 ≤ Nat.count (fun k => Nat.Prime (34000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB34.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB34_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB34 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB34_bound) x hxL, (List.forall_iff_forall_mem.mp PB34_prime) x hxL⟩
def PB35 : List Nat := [23,27,51,53,59,69,81,83,89,99,107,111,117,129,141,149,153,159,171,201,221,227,251,257,267,279,281,291,311,317,323,327,339,353,363,381,393,401,407,419,423,437,447,449,461,491,507,509,521,527,531,533,537,543,569,573,591,593,597,603,617,671,677,729,731,747,753,759,771,797,801,803,809,831,837,839,851,863,869,879,897,899,911,923,933,951,963,969,977,983,993,999]
lemma PB35_nodup : PB35.Nodup := by decide
lemma PB35_bound : PB35.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB35_prime : PB35.Forall (fun x => Nat.Prime (35000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_35 : 92 ≤ Nat.count (fun k => Nat.Prime (35000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB35.toFinset.card = 92 := by
    rw [List.toFinset_card_of_nodup PB35_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB35 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB35_bound) x hxL, (List.forall_iff_forall_mem.mp PB35_prime) x hxL⟩
def PB36 : List Nat := [7,11,13,17,37,61,67,73,83,97,107,109,131,137,151,161,187,191,209,217,229,241,251,263,269,277,293,299,307,313,319,341,343,353,373,383,389,433,451,457,467,469,473,479,493,497,523,527,529,541,551,559,563,571,583,587,599,607,629,637,643,653,671,677,683,691,697,709,713,721,739,749,761,767,779,781,787,791,793,809,821,833,847,857,871,877,887,899,901,913,919,923,929,931,943,947,973,979,997]
lemma PB36_nodup : PB36.Nodup := by decide
lemma PB36_bound : PB36.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB36_prime : PB36.Forall (fun x => Nat.Prime (36000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_36 : 99 ≤ Nat.count (fun k => Nat.Prime (36000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB36.toFinset.card = 99 := by
    rw [List.toFinset_card_of_nodup PB36_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB36 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB36_bound) x hxL, (List.forall_iff_forall_mem.mp PB36_prime) x hxL⟩
def PB37 : List Nat := [3,13,19,21,39,49,57,61,87,97,117,123,139,159,171,181,189,199,201,217,223,243,253,273,277,307,309,313,321,337,339,357,361,363,369,379,397,409,423,441,447,463,483,489,493,501,507,511,517,529,537,547,549,561,567,571,573,579,589,591,607,619,633,643,649,657,663,691,693,699,717,747,781,783,799,811,813,831,847,853,861,871,879,889,897,907,951,957,963,967,987,991,993,997]
lemma PB37_nodup : PB37.Nodup := by decide
lemma PB37_bound : PB37.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB37_prime : PB37.Forall (fun x => Nat.Prime (37000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_37 : 94 ≤ Nat.count (fun k => Nat.Prime (37000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB37.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB37_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB37 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB37_bound) x hxL, (List.forall_iff_forall_mem.mp PB37_prime) x hxL⟩
def PB38 : List Nat := [11,39,47,53,69,83,113,119,149,153,167,177,183,189,197,201,219,231,237,239,261,273,281,287,299,303,317,321,327,329,333,351,371,377,393,431,447,449,453,459,461,501,543,557,561,567,569,593,603,609,611,629,639,651,653,669,671,677,693,699,707,711,713,723,729,737,747,749,767,783,791,803,821,833,839,851,861,867,873,891,903,917,921,923,933,953,959,971,977,993]
lemma PB38_nodup : PB38.Nodup := by decide
lemma PB38_bound : PB38.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB38_prime : PB38.Forall (fun x => Nat.Prime (38000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_38 : 90 ≤ Nat.count (fun k => Nat.Prime (38000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB38.toFinset.card = 90 := by
    rw [List.toFinset_card_of_nodup PB38_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB38 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB38_bound) x hxL, (List.forall_iff_forall_mem.mp PB38_prime) x hxL⟩
def PB39 : List Nat := [19,23,41,43,47,79,89,97,103,107,113,119,133,139,157,161,163,181,191,199,209,217,227,229,233,239,241,251,293,301,313,317,323,341,343,359,367,371,373,383,397,409,419,439,443,451,461,499,503,509,511,521,541,551,563,569,581,607,619,623,631,659,667,671,679,703,709,719,727,733,749,761,769,779,791,799,821,827,829,839,841,847,857,863,869,877,883,887,901,929,937,953,971,979,983,989]
lemma PB39_nodup : PB39.Nodup := by decide
lemma PB39_bound : PB39.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB39_prime : PB39.Forall (fun x => Nat.Prime (39000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_39 : 96 ≤ Nat.count (fun k => Nat.Prime (39000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB39.toFinset.card = 96 := by
    rw [List.toFinset_card_of_nodup PB39_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB39 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB39_bound) x hxL, (List.forall_iff_forall_mem.mp PB39_prime) x hxL⟩
def PB40 : List Nat := [9,13,31,37,39,63,87,93,99,111,123,127,129,151,153,163,169,177,189,193,213,231,237,241,253,277,283,289,343,351,357,361,387,423,427,429,433,459,471,483,487,493,499,507,519,529,531,543,559,577,583,591,597,609,627,637,639,693,697,699,709,739,751,759,763,771,787,801,813,819,823,829,841,847,849,853,867,879,883,897,903,927,933,939,949,961,973,993]
lemma PB40_nodup : PB40.Nodup := by decide
lemma PB40_bound : PB40.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB40_prime : PB40.Forall (fun x => Nat.Prime (40000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_40 : 88 ≤ Nat.count (fun k => Nat.Prime (40000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB40.toFinset.card = 88 := by
    rw [List.toFinset_card_of_nodup PB40_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB40 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB40_bound) x hxL, (List.forall_iff_forall_mem.mp PB40_prime) x hxL⟩
def PB41 : List Nat := [11,17,23,39,47,51,57,77,81,113,117,131,141,143,149,161,177,179,183,189,201,203,213,221,227,231,233,243,257,263,269,281,299,333,341,351,357,381,387,389,399,411,413,443,453,467,479,491,507,513,519,521,539,543,549,579,593,597,603,609,611,617,621,627,641,647,651,659,669,681,687,719,729,737,759,761,771,777,801,809,813,843,849,851,863,879,887,893,897,903,911,927,941,947,953,957,959,969,981,983,999]
lemma PB41_nodup : PB41.Nodup := by decide
lemma PB41_bound : PB41.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB41_prime : PB41.Forall (fun x => Nat.Prime (41000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_41 : 101 ≤ Nat.count (fun k => Nat.Prime (41000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB41.toFinset.card = 101 := by
    rw [List.toFinset_card_of_nodup PB41_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB41 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB41_bound) x hxL, (List.forall_iff_forall_mem.mp PB41_prime) x hxL⟩
def PB42 : List Nat := [13,17,19,23,43,61,71,73,83,89,101,131,139,157,169,179,181,187,193,197,209,221,223,227,239,257,281,283,293,299,307,323,331,337,349,359,373,379,391,397,403,407,409,433,437,443,451,457,461,463,467,473,487,491,499,509,533,557,569,571,577,589,611,641,643,649,667,677,683,689,697,701,703,709,719,727,737,743,751,767,773,787,793,797,821,829,839,841,853,859,863,899,901,923,929,937,943,953,961,967,979,989]
lemma PB42_nodup : PB42.Nodup := by decide
lemma PB42_bound : PB42.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB42_prime : PB42.Forall (fun x => Nat.Prime (42000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_42 : 102 ≤ Nat.count (fun k => Nat.Prime (42000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB42.toFinset.card = 102 := by
    rw [List.toFinset_card_of_nodup PB42_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB42 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB42_bound) x hxL, (List.forall_iff_forall_mem.mp PB42_prime) x hxL⟩
def PB43 : List Nat := [3,13,19,37,49,51,63,67,93,103,117,133,151,159,177,189,201,207,223,237,261,271,283,291,313,319,321,331,391,397,399,403,411,427,441,451,457,481,487,499,517,541,543,573,577,579,591,597,607,609,613,627,633,649,651,661,669,691,711,717,721,753,759,777,781,783,787,789,793,801,853,867,889,891,913,933,943,951,961,963,969,973,987,991,997]
lemma PB43_nodup : PB43.Nodup := by decide
lemma PB43_bound : PB43.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB43_prime : PB43.Forall (fun x => Nat.Prime (43000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_43 : 85 ≤ Nat.count (fun k => Nat.Prime (43000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB43.toFinset.card = 85 := by
    rw [List.toFinset_card_of_nodup PB43_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB43 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB43_bound) x hxL, (List.forall_iff_forall_mem.mp PB43_prime) x hxL⟩
def PB44 : List Nat := [17,21,27,29,41,53,59,71,87,89,101,111,119,123,129,131,159,171,179,189,201,203,207,221,249,257,263,267,269,273,279,281,293,351,357,371,381,383,389,417,449,453,483,491,497,501,507,519,531,533,537,543,549,563,579,587,617,621,623,633,641,647,651,657,683,687,699,701,711,729,741,753,771,773,777,789,797,809,819,839,843,851,867,879,887,893,909,917,927,939,953,959,963,971,983,987]
lemma PB44_nodup : PB44.Nodup := by decide
lemma PB44_bound : PB44.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB44_prime : PB44.Forall (fun x => Nat.Prime (44000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_44 : 96 ≤ Nat.count (fun k => Nat.Prime (44000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB44.toFinset.card = 96 := by
    rw [List.toFinset_card_of_nodup PB44_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB44 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB44_bound) x hxL, (List.forall_iff_forall_mem.mp PB44_prime) x hxL⟩
def PB45 : List Nat := [7,13,53,61,77,83,119,121,127,131,137,139,161,179,181,191,197,233,247,259,263,281,289,293,307,317,319,329,337,341,343,361,377,389,403,413,427,433,439,481,491,497,503,523,533,541,553,557,569,587,589,599,613,631,641,659,667,673,677,691,697,707,737,751,757,763,767,779,817,821,823,827,833,841,853,863,869,887,893,943,949,953,959,971,979,989]
lemma PB45_nodup : PB45.Nodup := by decide
lemma PB45_bound : PB45.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB45_prime : PB45.Forall (fun x => Nat.Prime (45000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_45 : 86 ≤ Nat.count (fun k => Nat.Prime (45000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB45.toFinset.card = 86 := by
    rw [List.toFinset_card_of_nodup PB45_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB45 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB45_bound) x hxL, (List.forall_iff_forall_mem.mp PB45_prime) x hxL⟩
def PB46 : List Nat := [21,27,49,51,61,73,91,93,99,103,133,141,147,153,171,181,183,187,199,219,229,237,261,271,273,279,301,307,309,327,337,349,351,381,399,411,439,441,447,451,457,471,477,489,499,507,511,523,549,559,567,573,589,591,601,619,633,639,643,649,663,679,681,687,691,703,723,727,747,751,757,769,771,807,811,817,819,829,831,853,861,867,877,889,901,919,933,957,993,997]
lemma PB46_nodup : PB46.Nodup := by decide
lemma PB46_bound : PB46.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB46_prime : PB46.Forall (fun x => Nat.Prime (46000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_46 : 90 ≤ Nat.count (fun k => Nat.Prime (46000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB46.toFinset.card = 90 := by
    rw [List.toFinset_card_of_nodup PB46_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB46 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB46_bound) x hxL, (List.forall_iff_forall_mem.mp PB46_prime) x hxL⟩
def PB47 : List Nat := [17,41,51,57,59,87,93,111,119,123,129,137,143,147,149,161,189,207,221,237,251,269,279,287,293,297,303,309,317,339,351,353,363,381,387,389,407,417,419,431,441,459,491,497,501,507,513,521,527,533,543,563,569,581,591,599,609,623,629,639,653,657,659,681,699,701,711,713,717,737,741,743,777,779,791,797,807,809,819,837,843,857,869,881,903,911,917,933,939,947,951,963,969,977,981]
lemma PB47_nodup : PB47.Nodup := by decide
lemma PB47_bound : PB47.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB47_prime : PB47.Forall (fun x => Nat.Prime (47000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_47 : 95 ≤ Nat.count (fun k => Nat.Prime (47000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB47.toFinset.card = 95 := by
    rw [List.toFinset_card_of_nodup PB47_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB47 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB47_bound) x hxL, (List.forall_iff_forall_mem.mp PB47_prime) x hxL⟩
def PB48 : List Nat := [17,23,29,49,73,79,91,109,119,121,131,157,163,179,187,193,197,221,239,247,259,271,281,299,311,313,337,341,353,371,383,397,407,409,413,437,449,463,473,479,481,487,491,497,523,527,533,539,541,563,571,589,593,611,619,623,647,649,661,673,677,679,731,733,751,757,761,767,779,781,787,799,809,817,821,823,847,857,859,869,871,883,889,907,947,953,973,989,991]
lemma PB48_nodup : PB48.Nodup := by decide
lemma PB48_bound : PB48.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB48_prime : PB48.Forall (fun x => Nat.Prime (48000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_48 : 89 ≤ Nat.count (fun k => Nat.Prime (48000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB48.toFinset.card = 89 := by
    rw [List.toFinset_card_of_nodup PB48_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB48 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB48_bound) x hxL, (List.forall_iff_forall_mem.mp PB48_prime) x hxL⟩
def PB49 : List Nat := [3,9,19,31,33,37,43,57,69,81,103,109,117,121,123,139,157,169,171,177,193,199,201,207,211,223,253,261,277,279,297,307,331,333,339,363,367,369,391,393,409,411,417,429,433,451,459,463,477,481,499,523,529,531,537,547,549,559,597,603,613,627,633,639,663,667,669,681,697,711,727,739,741,747,757,783,787,789,801,807,811,823,831,843,853,871,877,891,919,921,927,937,939,943,957,991,993,999]
lemma PB49_nodup : PB49.Nodup := by decide
lemma PB49_bound : PB49.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB49_prime : PB49.Forall (fun x => Nat.Prime (49000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_49 : 98 ≤ Nat.count (fun k => Nat.Prime (49000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB49.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB49_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB49 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB49_bound) x hxL, (List.forall_iff_forall_mem.mp PB49_prime) x hxL⟩
def PB50 : List Nat := [21,23,33,47,51,53,69,77,87,93,101,111,119,123,129,131,147,153,159,177,207,221,227,231,261,263,273,287,291,311,321,329,333,341,359,363,377,383,387,411,417,423,441,459,461,497,503,513,527,539,543,549,551,581,587,591,593,599,627,647,651,671,683,707,723,741,753,767,773,777,789,821,833,839,849,857,867,873,891,893,909,923,929,951,957,969,971,989,993]
lemma PB50_nodup : PB50.Nodup := by decide
lemma PB50_bound : PB50.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB50_prime : PB50.Forall (fun x => Nat.Prime (50000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_50 : 89 ≤ Nat.count (fun k => Nat.Prime (50000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB50.toFinset.card = 89 := by
    rw [List.toFinset_card_of_nodup PB50_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB50 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB50_bound) x hxL, (List.forall_iff_forall_mem.mp PB50_prime) x hxL⟩
def PB51 : List Nat := [1,31,43,47,59,61,71,109,131,133,137,151,157,169,193,197,199,203,217,229,239,241,257,263,283,287,307,329,341,343,347,349,361,383,407,413,419,421,427,431,437,439,449,461,473,479,481,487,503,511,517,521,539,551,563,577,581,593,599,607,613,631,637,647,659,673,679,683,691,713,719,721,749,767,769,787,797,803,817,827,829,839,853,859,869,871,893,899,907,913,929,941,949,971,973,977,991]
lemma PB51_nodup : PB51.Nodup := by decide
lemma PB51_bound : PB51.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB51_prime : PB51.Forall (fun x => Nat.Prime (51000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_51 : 97 ≤ Nat.count (fun k => Nat.Prime (51000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB51.toFinset.card = 97 := by
    rw [List.toFinset_card_of_nodup PB51_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB51 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB51_bound) x hxL, (List.forall_iff_forall_mem.mp PB51_prime) x hxL⟩
def PB52 : List Nat := [9,21,27,51,57,67,69,81,103,121,127,147,153,163,177,181,183,189,201,223,237,249,253,259,267,289,291,301,313,321,361,363,369,379,387,391,433,453,457,489,501,511,517,529,541,543,553,561,567,571,579,583,609,627,631,639,667,673,691,697,709,711,721,727,733,747,757,769,783,807,813,817,837,859,861,879,883,889,901,903,919,937,951,957,963,967,973,981,999]
lemma PB52_nodup : PB52.Nodup := by decide
lemma PB52_bound : PB52.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB52_prime : PB52.Forall (fun x => Nat.Prime (52000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_52 : 89 ≤ Nat.count (fun k => Nat.Prime (52000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB52.toFinset.card = 89 := by
    rw [List.toFinset_card_of_nodup PB52_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB52 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB52_bound) x hxL, (List.forall_iff_forall_mem.mp PB52_prime) x hxL⟩
def PB53 : List Nat := [3,17,47,51,69,77,87,89,93,101,113,117,129,147,149,161,171,173,189,197,201,231,233,239,267,269,279,281,299,309,323,327,353,359,377,381,401,407,411,419,437,441,453,479,503,507,527,549,551,569,591,593,597,609,611,617,623,629,633,639,653,657,681,693,699,717,719,731,759,773,777,783,791,813,819,831,849,857,861,881,887,891,897,899,917,923,927,939,951,959,987,993]
lemma PB53_nodup : PB53.Nodup := by decide
lemma PB53_bound : PB53.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB53_prime : PB53.Forall (fun x => Nat.Prime (53000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_53 : 92 ≤ Nat.count (fun k => Nat.Prime (53000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB53.toFinset.card = 92 := by
    rw [List.toFinset_card_of_nodup PB53_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB53 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB53_bound) x hxL, (List.forall_iff_forall_mem.mp PB53_prime) x hxL⟩
def PB54 : List Nat := [1,11,13,37,49,59,83,91,101,121,133,139,151,163,167,181,193,217,251,269,277,287,293,311,319,323,331,347,361,367,371,377,401,403,409,413,419,421,437,443,449,469,493,497,499,503,517,521,539,541,547,559,563,577,581,583,601,617,623,629,631,647,667,673,679,709,713,721,727,751,767,773,779,787,799,829,833,851,869,877,881,907,917,919,941,949,959,973,979,983]
lemma PB54_nodup : PB54.Nodup := by decide
lemma PB54_bound : PB54.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB54_prime : PB54.Forall (fun x => Nat.Prime (54000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_54 : 90 ≤ Nat.count (fun k => Nat.Prime (54000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB54.toFinset.card = 90 := by
    rw [List.toFinset_card_of_nodup PB54_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB54 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB54_bound) x hxL, (List.forall_iff_forall_mem.mp PB54_prime) x hxL⟩
def PB55 : List Nat := [1,9,21,49,51,57,61,73,79,103,109,117,127,147,163,171,201,207,213,217,219,229,243,249,259,291,313,331,333,337,339,343,351,373,381,399,411,439,441,457,469,487,501,511,529,541,547,579,589,603,609,619,621,631,633,639,661,663,667,673,681,691,697,711,717,721,733,763,787,793,799,807,813,817,819,823,829,837,843,849,871,889,897,901,903,921,927,931,933,949,967,987,997]
lemma PB55_nodup : PB55.Nodup := by decide
lemma PB55_bound : PB55.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB55_prime : PB55.Forall (fun x => Nat.Prime (55000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_55 : 93 ≤ Nat.count (fun k => Nat.Prime (55000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB55.toFinset.card = 93 := by
    rw [List.toFinset_card_of_nodup PB55_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB55 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB55_bound) x hxL, (List.forall_iff_forall_mem.mp PB55_prime) x hxL⟩
def PB56 : List Nat := [3,9,39,41,53,81,87,93,99,101,113,123,131,149,167,171,179,197,207,209,237,239,249,263,267,269,299,311,333,359,369,377,383,393,401,417,431,437,443,453,467,473,477,479,489,501,503,509,519,527,531,533,543,569,591,597,599,611,629,633,659,663,671,681,687,701,711,713,731,737,747,767,773,779,783,807,809,813,821,827,843,857,873,891,893,897,909,911,921,923,929,941,951,957,963,983,989,993,999]
lemma PB56_nodup : PB56.Nodup := by decide
lemma PB56_bound : PB56.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB56_prime : PB56.Forall (fun x => Nat.Prime (56000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_56 : 99 ≤ Nat.count (fun k => Nat.Prime (56000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB56.toFinset.card = 99 := by
    rw [List.toFinset_card_of_nodup PB56_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB56 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB56_bound) x hxL, (List.forall_iff_forall_mem.mp PB56_prime) x hxL⟩
def PB57 : List Nat := [37,41,47,59,73,77,89,97,107,119,131,139,143,149,163,173,179,191,193,203,221,223,241,251,259,269,271,283,287,301,329,331,347,349,367,373,383,389,397,413,427,457,467,487,493,503,527,529,557,559,571,587,593,601,637,641,649,653,667,679,689,697,709,713,719,727,731,737,751,773,781,787,791,793,803,809,829,839,847,853,859,881,899,901,917,923,943,947,973,977,991]
lemma PB57_nodup : PB57.Nodup := by decide
lemma PB57_bound : PB57.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB57_prime : PB57.Forall (fun x => Nat.Prime (57000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_57 : 91 ≤ Nat.count (fun k => Nat.Prime (57000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB57.toFinset.card = 91 := by
    rw [List.toFinset_card_of_nodup PB57_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB57 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB57_bound) x hxL, (List.forall_iff_forall_mem.mp PB57_prime) x hxL⟩
def PB58 : List Nat := [13,27,31,43,49,57,61,67,73,99,109,111,129,147,151,153,169,171,189,193,199,207,211,217,229,231,237,243,271,309,313,321,337,363,367,369,379,391,393,403,411,417,427,439,441,451,453,477,481,511,537,543,549,567,573,579,601,603,613,631,657,661,679,687,693,699,711,727,733,741,757,763,771,787,789,831,889,897,901,907,909,913,921,937,943,963,967,979,991,997]
lemma PB58_nodup : PB58.Nodup := by decide
lemma PB58_bound : PB58.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB58_prime : PB58.Forall (fun x => Nat.Prime (58000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_58 : 90 ≤ Nat.count (fun k => Nat.Prime (58000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB58.toFinset.card = 90 := by
    rw [List.toFinset_card_of_nodup PB58_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB58 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB58_bound) x hxL, (List.forall_iff_forall_mem.mp PB58_prime) x hxL⟩
def PB59 : List Nat := [9,11,21,23,29,51,53,63,69,77,83,93,107,113,119,123,141,149,159,167,183,197,207,209,219,221,233,239,243,263,273,281,333,341,351,357,359,369,377,387,393,399,407,417,419,441,443,447,453,467,471,473,497,509,513,539,557,561,567,581,611,617,621,627,629,651,659,663,669,671,693,699,707,723,729,743,747,753,771,779,791,797,809,833,863,879,887,921,929,951,957,971,981,999]
lemma PB59_nodup : PB59.Nodup := by decide
lemma PB59_bound : PB59.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB59_prime : PB59.Forall (fun x => Nat.Prime (59000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_59 : 94 ≤ Nat.count (fun k => Nat.Prime (59000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB59.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB59_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB59 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB59_bound) x hxL, (List.forall_iff_forall_mem.mp PB59_prime) x hxL⟩
def PB60 : List Nat := [13,17,29,37,41,77,83,89,91,101,103,107,127,133,139,149,161,167,169,209,217,223,251,257,259,271,289,293,317,331,337,343,353,373,383,397,413,427,443,449,457,493,497,509,521,527,539,589,601,607,611,617,623,631,637,647,649,659,661,679,689,703,719,727,733,737,757,761,763,773,779,793,811,821,859,869,887,889,899,901,913,917,919,923,937,943,953,961]
lemma PB60_nodup : PB60.Nodup := by decide
lemma PB60_bound : PB60.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB60_prime : PB60.Forall (fun x => Nat.Prime (60000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_60 : 88 ≤ Nat.count (fun k => Nat.Prime (60000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB60.toFinset.card = 88 := by
    rw [List.toFinset_card_of_nodup PB60_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB60 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB60_bound) x hxL, (List.forall_iff_forall_mem.mp PB60_prime) x hxL⟩
def PB61 : List Nat := [1,7,27,31,43,51,57,91,99,121,129,141,151,153,169,211,223,231,253,261,283,291,297,331,333,339,343,357,363,379,381,403,409,417,441,463,469,471,483,487,493,507,511,519,543,547,553,559,561,583,603,609,613,627,631,637,643,651,657,667,673,681,687,703,717,723,729,751,757,781,813,819,837,843,861,871,879,909,927,933,949,961,967,979,981,987,991]
lemma PB61_nodup : PB61.Nodup := by decide
lemma PB61_bound : PB61.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB61_prime : PB61.Forall (fun x => Nat.Prime (61000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_61 : 87 ≤ Nat.count (fun k => Nat.Prime (61000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB61.toFinset.card = 87 := by
    rw [List.toFinset_card_of_nodup PB61_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB61 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB61_bound) x hxL, (List.forall_iff_forall_mem.mp PB61_prime) x hxL⟩
def PB62 : List Nat := [3,11,17,39,47,53,57,71,81,99,119,129,131,137,141,143,171,189,191,201,207,213,219,233,273,297,299,303,311,323,327,347,351,383,401,417,423,459,467,473,477,483,497,501,507,533,539,549,563,581,591,597,603,617,627,633,639,653,659,683,687,701,723,731,743,753,761,773,791,801,819,827,851,861,869,873,897,903,921,927,929,939,969,971,981,983,987,989]
lemma PB62_nodup : PB62.Nodup := by decide
lemma PB62_bound : PB62.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB62_prime : PB62.Forall (fun x => Nat.Prime (62000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_62 : 88 ≤ Nat.count (fun k => Nat.Prime (62000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB62.toFinset.card = 88 := by
    rw [List.toFinset_card_of_nodup PB62_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB62 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB62_bound) x hxL, (List.forall_iff_forall_mem.mp PB62_prime) x hxL⟩
def PB63 : List Nat := [29,31,59,67,73,79,97,103,113,127,131,149,179,197,199,211,241,247,277,281,299,311,313,317,331,337,347,353,361,367,377,389,391,397,409,419,421,439,443,463,467,473,487,493,499,521,527,533,541,559,577,587,589,599,601,607,611,617,629,647,649,659,667,671,689,691,697,703,709,719,727,737,743,761,773,781,793,799,803,809,823,839,841,853,857,863,901,907,913,929,949,977,997]
lemma PB63_nodup : PB63.Nodup := by decide
lemma PB63_bound : PB63.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB63_prime : PB63.Forall (fun x => Nat.Prime (63000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_63 : 93 ≤ Nat.count (fun k => Nat.Prime (63000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB63.toFinset.card = 93 := by
    rw [List.toFinset_card_of_nodup PB63_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB63 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB63_bound) x hxL, (List.forall_iff_forall_mem.mp PB63_prime) x hxL⟩
def PB64 : List Nat := [7,13,19,33,37,63,67,81,91,109,123,151,153,157,171,187,189,217,223,231,237,271,279,283,301,303,319,327,333,373,381,399,403,433,439,451,453,483,489,499,513,553,567,577,579,591,601,609,613,621,627,633,661,663,667,679,693,709,717,747,763,781,783,793,811,817,849,853,871,877,879,891,901,919,921,927,937,951,969,997]
lemma PB64_nodup : PB64.Nodup := by decide
lemma PB64_bound : PB64.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB64_prime : PB64.Forall (fun x => Nat.Prime (64000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_64 : 80 ≤ Nat.count (fun k => Nat.Prime (64000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB64.toFinset.card = 80 := by
    rw [List.toFinset_card_of_nodup PB64_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB64 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB64_bound) x hxL, (List.forall_iff_forall_mem.mp PB64_prime) x hxL⟩
def PB65 : List Nat := [3,11,27,29,33,53,63,71,89,99,101,111,119,123,129,141,147,167,171,173,179,183,203,213,239,257,267,269,287,293,309,323,327,353,357,371,381,393,407,413,419,423,437,447,449,479,497,519,521,537,539,543,551,557,563,579,581,587,599,609,617,629,633,647,651,657,677,687,699,701,707,713,717,719,729,731,761,777,789,809,827,831,837,839,843,851,867,881,899,921,927,929,951,957,963,981,983,993]
lemma PB65_nodup : PB65.Nodup := by decide
lemma PB65_bound : PB65.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB65_prime : PB65.Forall (fun x => Nat.Prime (65000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_65 : 98 ≤ Nat.count (fun k => Nat.Prime (65000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB65.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB65_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB65 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB65_bound) x hxL, (List.forall_iff_forall_mem.mp PB65_prime) x hxL⟩
def PB66 : List Nat := [29,37,41,47,67,71,83,89,103,107,109,137,161,169,173,179,191,221,239,271,293,301,337,343,347,359,361,373,377,383,403,413,431,449,457,463,467,491,499,509,523,529,533,541,553,569,571,587,593,601,617,629,643,653,683,697,701,713,721,733,739,749,751,763,791,797,809,821,841,851,853,863,877,883,889,919,923,931,943,947,949,959,973,977]
lemma PB66_nodup : PB66.Nodup := by decide
lemma PB66_bound : PB66.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB66_prime : PB66.Forall (fun x => Nat.Prime (66000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_66 : 84 ≤ Nat.count (fun k => Nat.Prime (66000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB66.toFinset.card = 84 := by
    rw [List.toFinset_card_of_nodup PB66_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB66 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB66_bound) x hxL, (List.forall_iff_forall_mem.mp PB66_prime) x hxL⟩
def PB67 : List Nat := [3,21,33,43,49,57,61,73,79,103,121,129,139,141,153,157,169,181,187,189,211,213,217,219,231,247,261,271,273,289,307,339,343,349,369,391,399,409,411,421,427,429,433,447,453,477,481,489,493,499,511,523,531,537,547,559,567,577,579,589,601,607,619,631,651,679,699,709,723,733,741,751,757,759,763,777,783,789,801,807,819,829,843,853,867,883,891,901,927,931,933,939,943,957,961,967,979,987,993]
lemma PB67_nodup : PB67.Nodup := by decide
lemma PB67_bound : PB67.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB67_prime : PB67.Forall (fun x => Nat.Prime (67000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_67 : 99 ≤ Nat.count (fun k => Nat.Prime (67000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB67.toFinset.card = 99 := by
    rw [List.toFinset_card_of_nodup PB67_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB67 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB67_bound) x hxL, (List.forall_iff_forall_mem.mp PB67_prime) x hxL⟩
def PB68 : List Nat := [23,41,53,59,71,87,99,111,113,141,147,161,171,207,209,213,219,227,239,261,279,281,311,329,351,371,389,399,437,443,447,449,473,477,483,489,491,501,507,521,531,539,543,567,581,597,611,633,639,659,669,683,687,699,711,713,729,737,743,749,767,771,777,791,813,819,821,863,879,881,891,897,899,903,909,917,927,947,963,993]
lemma PB68_nodup : PB68.Nodup := by decide
lemma PB68_bound : PB68.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB68_prime : PB68.Forall (fun x => Nat.Prime (68000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_68 : 80 ≤ Nat.count (fun k => Nat.Prime (68000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB68.toFinset.card = 80 := by
    rw [List.toFinset_card_of_nodup PB68_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB68 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB68_bound) x hxL, (List.forall_iff_forall_mem.mp PB68_prime) x hxL⟩
def PB69 : List Nat := [1,11,19,29,31,61,67,73,109,119,127,143,149,151,163,191,193,197,203,221,233,239,247,257,259,263,313,317,337,341,371,379,383,389,401,403,427,431,439,457,463,467,473,481,491,493,497,499,539,557,593,623,653,661,677,691,697,709,737,739,761,763,767,779,809,821,827,829,833,847,857,859,877,899,911,929,931,941,959,991,997]
lemma PB69_nodup : PB69.Nodup := by decide
lemma PB69_bound : PB69.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB69_prime : PB69.Forall (fun x => Nat.Prime (69000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_69 : 81 ≤ Nat.count (fun k => Nat.Prime (69000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB69.toFinset.card = 81 := by
    rw [List.toFinset_card_of_nodup PB69_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB69 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB69_bound) x hxL, (List.forall_iff_forall_mem.mp PB69_prime) x hxL⟩
def PB70 : List Nat := [1,3,9,19,39,51,61,67,79,99,111,117,121,123,139,141,157,163,177,181,183,199,201,207,223,229,237,241,249,271,289,297,309,313,321,327,351,373,379,381,393,423,429,439,451,457,459,481,487,489,501,507,529,537,549,571,573,583,589,607,619,621,627,639,657,663,667,687,709,717,729,753,769,783,793,823,841,843,849,853,867,877,879,891,901,913,919,921,937,949,951,957,969,979,981,991,997,999]
lemma PB70_nodup : PB70.Nodup := by decide
lemma PB70_bound : PB70.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB70_prime : PB70.Forall (fun x => Nat.Prime (70000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_70 : 98 ≤ Nat.count (fun k => Nat.Prime (70000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB70.toFinset.card = 98 := by
    rw [List.toFinset_card_of_nodup PB70_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB70 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB70_bound) x hxL, (List.forall_iff_forall_mem.mp PB70_prime) x hxL⟩
def PB71 : List Nat := [11,23,39,59,69,81,89,119,129,143,147,153,161,167,171,191,209,233,237,249,257,261,263,287,293,317,327,329,333,339,341,347,353,359,363,387,389,399,411,413,419,429,437,443,453,471,473,479,483,503,527,537,549,551,563,569,593,597,633,647,663,671,693,699,707,711,713,719,741,761,777,789,807,809,821,837,843,849,861,867,879,881,887,899,909,917,933,941,947,963,971,983,987,993,999]
lemma PB71_nodup : PB71.Nodup := by decide
lemma PB71_bound : PB71.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB71_prime : PB71.Forall (fun x => Nat.Prime (71000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_71 : 95 ≤ Nat.count (fun k => Nat.Prime (71000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB71.toFinset.card = 95 := by
    rw [List.toFinset_card_of_nodup PB71_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB71 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB71_bound) x hxL, (List.forall_iff_forall_mem.mp PB71_prime) x hxL⟩
def PB72 : List Nat := [19,31,43,47,53,73,77,89,91,101,103,109,139,161,167,169,173,211,221,223,227,229,251,253,269,271,277,287,307,313,337,341,353,367,379,383,421,431,461,467,469,481,493,497,503,533,547,551,559,577,613,617,623,643,647,649,661,671,673,679,689,701,707,719,727,733,739,763,767,797,817,823,859,869,871,883,889,893,901,907,911,923,931,937,949,953,959,973,977,997]
lemma PB72_nodup : PB72.Nodup := by decide
lemma PB72_bound : PB72.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB72_prime : PB72.Forall (fun x => Nat.Prime (72000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_72 : 90 ≤ Nat.count (fun k => Nat.Prime (72000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB72.toFinset.card = 90 := by
    rw [List.toFinset_card_of_nodup PB72_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB72 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB72_bound) x hxL, (List.forall_iff_forall_mem.mp PB72_prime) x hxL⟩
def PB73 : List Nat := [9,13,19,37,39,43,61,63,79,91,121,127,133,141,181,189,237,243,259,277,291,303,309,327,331,351,361,363,369,379,387,417,421,433,453,459,471,477,483,517,523,529,547,553,561,571,583,589,597,607,609,613,637,643,651,673,679,681,693,699,709,721,727,751,757,771,783,819,823,847,849,859,867,877,883,897,907,939,943,951,961,973,999]
lemma PB73_nodup : PB73.Nodup := by decide
lemma PB73_bound : PB73.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB73_prime : PB73.Forall (fun x => Nat.Prime (73000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_73 : 83 ≤ Nat.count (fun k => Nat.Prime (73000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB73.toFinset.card = 83 := by
    rw [List.toFinset_card_of_nodup PB73_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB73 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB73_bound) x hxL, (List.forall_iff_forall_mem.mp PB73_prime) x hxL⟩
def PB74 : List Nat := [17,21,27,47,51,71,77,93,99,101,131,143,149,159,161,167,177,189,197,201,203,209,219,231,257,279,287,293,297,311,317,323,353,357,363,377,381,383,411,413,419,441,449,453,471,489,507,509,521,527,531,551,561,567,573,587,597,609,611,623,653,687,699,707,713,717,719,729,731,747,759,761,771,779,797,821,827,831,843,857,861,869,873,887,891,897,903,923,929,933,941,959]
lemma PB74_nodup : PB74.Nodup := by decide
lemma PB74_bound : PB74.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB74_prime : PB74.Forall (fun x => Nat.Prime (74000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_74 : 92 ≤ Nat.count (fun k => Nat.Prime (74000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB74.toFinset.card = 92 := by
    rw [List.toFinset_card_of_nodup PB74_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB74 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB74_bound) x hxL, (List.forall_iff_forall_mem.mp PB74_prime) x hxL⟩
def PB75 : List Nat := [11,13,17,29,37,41,79,83,109,133,149,161,167,169,181,193,209,211,217,223,227,239,253,269,277,289,307,323,329,337,347,353,367,377,389,391,401,403,407,431,437,479,503,511,521,527,533,539,541,553,557,571,577,583,611,617,619,629,641,653,659,679,683,689,703,707,709,721,731,743,767,773,781,787,793,797,821,833,853,869,883,913,931,937,941,967,979,983,989,991,997]
lemma PB75_nodup : PB75.Nodup := by decide
lemma PB75_bound : PB75.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB75_prime : PB75.Forall (fun x => Nat.Prime (75000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_75 : 91 ≤ Nat.count (fun k => Nat.Prime (75000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB75.toFinset.card = 91 := by
    rw [List.toFinset_card_of_nodup PB75_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB75 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB75_bound) x hxL, (List.forall_iff_forall_mem.mp PB75_prime) x hxL⟩
def PB76 : List Nat := [1,3,31,39,79,81,91,99,103,123,129,147,157,159,163,207,213,231,243,249,253,259,261,283,289,303,333,343,367,369,379,387,403,421,423,441,463,471,481,487,493,507,511,519,537,541,543,561,579,597,603,607,631,649,651,667,673,679,697,717,733,753,757,771,777,781,801,819,829,831,837,847,871,873,883,907,913,919,943,949,961,963,991]
lemma PB76_nodup : PB76.Nodup := by decide
lemma PB76_bound : PB76.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB76_prime : PB76.Forall (fun x => Nat.Prime (76000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_76 : 83 ≤ Nat.count (fun k => Nat.Prime (76000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB76.toFinset.card = 83 := by
    rw [List.toFinset_card_of_nodup PB76_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB76 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB76_bound) x hxL, (List.forall_iff_forall_mem.mp PB76_prime) x hxL⟩
def PB77 : List Nat := [3,17,23,29,41,47,69,81,93,101,137,141,153,167,171,191,201,213,237,239,243,249,261,263,267,269,279,291,317,323,339,347,351,359,369,377,383,417,419,431,447,471,477,479,489,491,509,513,521,527,543,549,551,557,563,569,573,587,591,611,617,621,641,647,659,681,687,689,699,711,713,719,723,731,743,747,761,773,783,797,801,813,839,849,863,867,893,899,929,933,951,969,977,983,999]
lemma PB77_nodup : PB77.Nodup := by decide
lemma PB77_bound : PB77.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB77_prime : PB77.Forall (fun x => Nat.Prime (77000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_77 : 95 ≤ Nat.count (fun k => Nat.Prime (77000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB77.toFinset.card = 95 := by
    rw [List.toFinset_card_of_nodup PB77_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB77 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB77_bound) x hxL, (List.forall_iff_forall_mem.mp PB77_prime) x hxL⟩
def PB78 : List Nat := [7,17,31,41,49,59,79,101,121,137,139,157,163,167,173,179,191,193,203,229,233,241,259,277,283,301,307,311,317,341,347,367,401,427,437,439,467,479,487,497,509,511,517,539,541,553,569,571,577,583,593,607,623,643,649,653,691,697,707,713,721,737,779,781,787,791,797,803,809,823,839,853,857,877,887,889,893,901,919,929,941,977,979,989]
lemma PB78_nodup : PB78.Nodup := by decide
lemma PB78_bound : PB78.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB78_prime : PB78.Forall (fun x => Nat.Prime (78000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_78 : 84 ≤ Nat.count (fun k => Nat.Prime (78000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB78.toFinset.card = 84 := by
    rw [List.toFinset_card_of_nodup PB78_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB78 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB78_bound) x hxL, (List.forall_iff_forall_mem.mp PB78_prime) x hxL⟩
def PB79 : List Nat := [31,39,43,63,87,103,111,133,139,147,151,153,159,181,187,193,201,229,231,241,259,273,279,283,301,309,319,333,337,349,357,367,379,393,397,399,411,423,427,433,451,481,493,531,537,549,559,561,579,589,601,609,613,621,627,631,633,657,669,687,691,693,697,699,757,769,777,801,811,813,817,823,829,841,843,847,861,867,873,889,901,903,907,939,943,967,973,979,987,997,999]
lemma PB79_nodup : PB79.Nodup := by decide
lemma PB79_bound : PB79.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB79_prime : PB79.Forall (fun x => Nat.Prime (79000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_79 : 91 ≤ Nat.count (fun k => Nat.Prime (79000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB79.toFinset.card = 91 := by
    rw [List.toFinset_card_of_nodup PB79_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB79 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB79_bound) x hxL, (List.forall_iff_forall_mem.mp PB79_prime) x hxL⟩
def PB80 : List Nat := [21,39,51,71,77,107,111,141,147,149,153,167,173,177,191,207,209,221,231,233,239,251,263,273,279,287,309,317,329,341,347,363,369,387,407,429,447,449,471,473,489,491,513,527,537,557,567,599,603,611,621,627,629,651,657,669,671,677,681,683,687,701,713,737,747,749,761,777,779,783,789,803,809,819,831,833,849,863,897,909,911,917,923,929,933,953,963,989]
lemma PB80_nodup : PB80.Nodup := by decide
lemma PB80_bound : PB80.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB80_prime : PB80.Forall (fun x => Nat.Prime (80000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_80 : 88 ≤ Nat.count (fun k => Nat.Prime (80000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB80.toFinset.card = 88 := by
    rw [List.toFinset_card_of_nodup PB80_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB80 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB80_bound) x hxL, (List.forall_iff_forall_mem.mp PB80_prime) x hxL⟩
def PB81 : List Nat := [1,13,17,19,23,31,41,43,47,49,71,77,83,97,101,119,131,157,163,173,181,197,199,203,223,233,239,281,283,293,299,307,331,343,349,353,359,371,373,401,409,421,439,457,463,509,517,527,533,547,551,553,559,563,569,611,619,629,637,647,649,667,671,677,689,701,703,707,727,737,749,761,769,773,799,817,839,847,853,869,883,899,901,919,929,931,937,943,953,967,971,973]
lemma PB81_nodup : PB81.Nodup := by decide
lemma PB81_bound : PB81.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB81_prime : PB81.Forall (fun x => Nat.Prime (81000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_81 : 92 ≤ Nat.count (fun k => Nat.Prime (81000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB81.toFinset.card = 92 := by
    rw [List.toFinset_card_of_nodup PB81_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB81 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB81_bound) x hxL, (List.forall_iff_forall_mem.mp PB81_prime) x hxL⟩
def PB82 : List Nat := [3,7,9,13,21,31,37,39,51,67,73,129,139,141,153,163,171,183,189,193,207,217,219,223,231,237,241,261,267,279,301,307,339,349,351,361,373,387,393,421,457,463,469,471,483,487,493,499,507,529,531,549,559,561,567,571,591,601,609,613,619,633,651,657,699,721,723,727,729,757,759,763,781,787,793,799,811,813,837,847,883,889,891,903,913,939,963,981,997]
lemma PB82_nodup : PB82.Nodup := by decide
lemma PB82_bound : PB82.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB82_prime : PB82.Forall (fun x => Nat.Prime (82000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_82 : 89 ≤ Nat.count (fun k => Nat.Prime (82000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB82.toFinset.card = 89 := by
    rw [List.toFinset_card_of_nodup PB82_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB82 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB82_bound) x hxL, (List.forall_iff_forall_mem.mp PB82_prime) x hxL⟩
def PB83 : List Nat := [3,9,23,47,59,63,71,77,89,93,101,117,137,177,203,207,219,221,227,231,233,243,257,267,269,273,299,311,339,341,357,383,389,399,401,407,417,423,431,437,443,449,459,471,477,497,537,557,561,563,579,591,597,609,617,621,639,641,653,663,689,701,717,719,737,761,773,777,791,813,833,843,857,869,873,891,903,911,921,933,939,969,983,987]
lemma PB83_nodup : PB83.Nodup := by decide
lemma PB83_bound : PB83.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB83_prime : PB83.Forall (fun x => Nat.Prime (83000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_83 : 84 ≤ Nat.count (fun k => Nat.Prime (83000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB83.toFinset.card = 84 := by
    rw [List.toFinset_card_of_nodup PB83_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB83 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB83_bound) x hxL, (List.forall_iff_forall_mem.mp PB83_prime) x hxL⟩
def PB84 : List Nat := [11,17,47,53,59,61,67,89,121,127,131,137,143,163,179,181,191,199,211,221,223,229,239,247,263,299,307,313,317,319,347,349,377,389,391,401,407,421,431,437,443,449,457,463,467,481,499,503,509,521,523,533,551,559,589,629,631,649,653,659,673,691,697,701,713,719,731,737,751,761,787,793,809,811,827,857,859,869,871,913,919,947,961,967,977,979,991]
lemma PB84_nodup : PB84.Nodup := by decide
lemma PB84_bound : PB84.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB84_prime : PB84.Forall (fun x => Nat.Prime (84000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_84 : 87 ≤ Nat.count (fun k => Nat.Prime (84000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB84.toFinset.card = 87 := by
    rw [List.toFinset_card_of_nodup PB84_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB84 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB84_bound) x hxL, (List.forall_iff_forall_mem.mp PB84_prime) x hxL⟩
def PB85 : List Nat := [9,21,27,37,49,61,81,87,91,93,103,109,121,133,147,159,193,199,201,213,223,229,237,243,247,259,297,303,313,331,333,361,363,369,381,411,427,429,439,447,451,453,469,487,513,517,523,531,549,571,577,597,601,607,619,621,627,639,643,661,667,669,691,703,711,717,733,751,781,793,817,819,829,831,837,843,847,853,889,903,909,931,933,991,999]
lemma PB85_nodup : PB85.Nodup := by decide
lemma PB85_bound : PB85.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB85_prime : PB85.Forall (fun x => Nat.Prime (85000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_85 : 85 ≤ Nat.count (fun k => Nat.Prime (85000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB85.toFinset.card = 85 := by
    rw [List.toFinset_card_of_nodup PB85_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB85 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB85_bound) x hxL, (List.forall_iff_forall_mem.mp PB85_prime) x hxL⟩
def PB86 : List Nat := [11,17,27,29,69,77,83,111,113,117,131,137,143,161,171,179,183,197,201,209,239,243,249,257,263,269,287,291,293,297,311,323,341,351,353,357,369,371,381,389,399,413,423,441,453,461,467,477,491,501,509,531,533,539,561,573,579,587,599,627,629,677,689,693,711,719,729,743,753,767,771,783,813,837,843,851,857,861,869,923,927,929,939,951,959,969,981,993]
lemma PB86_nodup : PB86.Nodup := by decide
lemma PB86_bound : PB86.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB86_prime : PB86.Forall (fun x => Nat.Prime (86000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_86 : 88 ≤ Nat.count (fun k => Nat.Prime (86000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB86.toFinset.card = 88 := by
    rw [List.toFinset_card_of_nodup PB86_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB86 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB86_bound) x hxL, (List.forall_iff_forall_mem.mp PB86_prime) x hxL⟩
def PB87 : List Nat := [11,13,37,41,49,71,83,103,107,119,121,133,149,151,179,181,187,211,221,223,251,253,257,277,281,293,299,313,317,323,337,359,383,403,407,421,427,433,443,473,481,491,509,511,517,523,539,541,547,553,557,559,583,587,589,613,623,629,631,641,643,649,671,679,683,691,697,701,719,721,739,743,751,767,793,797,803,811,833,853,869,877,881,887,911,917,931,943,959,961,973,977,991]
lemma PB87_nodup : PB87.Nodup := by decide
lemma PB87_bound : PB87.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB87_prime : PB87.Forall (fun x => Nat.Prime (87000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_87 : 93 ≤ Nat.count (fun k => Nat.Prime (87000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB87.toFinset.card = 93 := by
    rw [List.toFinset_card_of_nodup PB87_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB87 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB87_bound) x hxL, (List.forall_iff_forall_mem.mp PB87_prime) x hxL⟩
def PB88 : List Nat := [1,3,7,19,37,69,79,93,117,129,169,177,211,223,237,241,259,261,289,301,321,327,337,339,379,397,411,423,427,463,469,471,493,499,513,523,547,589,591,607,609,643,651,657,661,663,667,681,721,729,741,747,771,789,793,799,801,807,811,813,817,819,843,853,861,867,873,883,897,903,919,937,951,969,993,997]
lemma PB88_nodup : PB88.Nodup := by decide
lemma PB88_bound : PB88.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB88_prime : PB88.Forall (fun x => Nat.Prime (88000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_88 : 76 ≤ Nat.count (fun k => Nat.Prime (88000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB88.toFinset.card = 76 := by
    rw [List.toFinset_card_of_nodup PB88_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB88 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB88_bound) x hxL, (List.forall_iff_forall_mem.mp PB88_prime) x hxL⟩
def PB89 : List Nat := [3,9,17,21,41,51,57,69,71,83,87,101,107,113,119,123,137,153,189,203,209,213,227,231,237,261,269,273,293,303,317,329,363,371,381,387,393,399,413,417,431,443,449,459,477,491,501,513,519,521,527,533,561,563,567,591,597,599,603,611,627,633,653,657,659,669,671,681,689,753,759,767,779,783,797,809,819,821,833,839,849,867,891,897,899,909,917,923,939,959,963,977,983,989]
lemma PB89_nodup : PB89.Nodup := by decide
lemma PB89_bound : PB89.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB89_prime : PB89.Forall (fun x => Nat.Prime (89000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_89 : 94 ≤ Nat.count (fun k => Nat.Prime (89000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB89.toFinset.card = 94 := by
    rw [List.toFinset_card_of_nodup PB89_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB89 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB89_bound) x hxL, (List.forall_iff_forall_mem.mp PB89_prime) x hxL⟩
def PB90 : List Nat := [1,7,11,17,19,23,31,53,59,67,71,73,89,107,121,127,149,163,173,187,191,197,199,203,217,227,239,247,263,271,281,289,313,353,359,371,373,379,397,401,403,407,437,439,469,473,481,499,511,523,527,529,533,547,583,599,617,619,631,641,647,659,677,679,697,703,709,731,749,787,793,803,821,823,833,841,847,863,887,901,907,911,917,931,947,971,977,989,997]
lemma PB90_nodup : PB90.Nodup := by decide
lemma PB90_bound : PB90.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB90_prime : PB90.Forall (fun x => Nat.Prime (90000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_90 : 89 ≤ Nat.count (fun k => Nat.Prime (90000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB90.toFinset.card = 89 := by
    rw [List.toFinset_card_of_nodup PB90_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB90 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB90_bound) x hxL, (List.forall_iff_forall_mem.mp PB90_prime) x hxL⟩
def PB91 : List Nat := [9,19,33,79,81,97,99,121,127,129,139,141,151,153,159,163,183,193,199,229,237,243,249,253,283,291,297,303,309,331,367,369,373,381,387,393,397,411,423,433,453,457,459,463,493,499,513,529,541,571,573,577,583,591,621,631,639,673,691,703,711,733,753,757,771,781,801,807,811,813,823,837,841,867,873,909,921,939,943,951,957,961,967,969,997]
lemma PB91_nodup : PB91.Nodup := by decide
lemma PB91_bound : PB91.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB91_prime : PB91.Forall (fun x => Nat.Prime (91000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_91 : 85 ≤ Nat.count (fun k => Nat.Prime (91000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB91.toFinset.card = 85 := by
    rw [List.toFinset_card_of_nodup PB91_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB91 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB91_bound) x hxL, (List.forall_iff_forall_mem.mp PB91_prime) x hxL⟩
def PB92 : List Nat := [3,9,33,41,51,77,83,107,111,119,143,153,173,177,179,189,203,219,221,227,233,237,243,251,269,297,311,317,333,347,353,357,363,369,377,381,383,387,399,401,413,419,431,459,461,467,479,489,503,507,551,557,567,569,581,593,623,627,639,641,647,657,669,671,681,683,693,699,707,717,723,737,753,761,767,779,789,791,801,809,821,831,849,857,861,863,867,893,899,921,927,941,951,957,959,987,993]
lemma PB92_nodup : PB92.Nodup := by decide
lemma PB92_bound : PB92.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB92_prime : PB92.Forall (fun x => Nat.Prime (92000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_92 : 97 ≤ Nat.count (fun k => Nat.Prime (92000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB92.toFinset.card = 97 := by
    rw [List.toFinset_card_of_nodup PB92_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB92 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB92_bound) x hxL, (List.forall_iff_forall_mem.mp PB92_prime) x hxL⟩
def PB93 : List Nat := [1,47,53,59,77,83,89,97,103,113,131,133,139,151,169,179,187,199,229,239,241,251,253,257,263,281,283,287,307,319,323,329,337,371,377,383,407,419,427,463,479,481,487,491,493,497,503,523,529,553,557,559,563,581,601,607,629,637,683,701,703,719,739,761,763,787,809,811,827,851,871,887,889,893,901,911,913,923,937,941,949,967,971,979,983,997]
lemma PB93_nodup : PB93.Nodup := by decide
lemma PB93_bound : PB93.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB93_prime : PB93.Forall (fun x => Nat.Prime (93000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_93 : 86 ≤ Nat.count (fun k => Nat.Prime (93000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB93.toFinset.card = 86 := by
    rw [List.toFinset_card_of_nodup PB93_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB93 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB93_bound) x hxL, (List.forall_iff_forall_mem.mp PB93_prime) x hxL⟩
def PB94 : List Nat := [7,9,33,49,57,63,79,99,109,111,117,121,151,153,169,201,207,219,229,253,261,273,291,307,309,321,327,331,343,349,351,379,397,399,421,427,433,439,441,447,463,477,483,513,529,531,541,543,547,559,561,573,583,597,603,613,621,649,651,687,693,709,723,727,747,771,777,781,789,793,811,819,823,837,841,847,849,873,889,903,907,933,949,951,961,993,999]
lemma PB94_nodup : PB94.Nodup := by decide
lemma PB94_bound : PB94.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB94_prime : PB94.Forall (fun x => Nat.Prime (94000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_94 : 87 ≤ Nat.count (fun k => Nat.Prime (94000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB94.toFinset.card = 87 := by
    rw [List.toFinset_card_of_nodup PB94_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB94 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB94_bound) x hxL, (List.forall_iff_forall_mem.mp PB94_prime) x hxL⟩
def PB95 : List Nat := [3,9,21,27,63,71,83,87,89,93,101,107,111,131,143,153,177,189,191,203,213,219,231,233,239,257,261,267,273,279,287,311,317,327,339,369,383,393,401,413,419,429,441,443,461,467,471,479,483,507,527,531,539,549,561,569,581,597,603,617,621,629,633,651,701,707,713,717,723,731,737,747,773,783,789,791,801,803,813,819,857,869,873,881,891,911,917,923,929,947,957,959,971,987,989]
lemma PB95_nodup : PB95.Nodup := by decide
lemma PB95_bound : PB95.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB95_prime : PB95.Forall (fun x => Nat.Prime (95000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_95 : 95 ≤ Nat.count (fun k => Nat.Prime (95000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB95.toFinset.card = 95 := by
    rw [List.toFinset_card_of_nodup PB95_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB95 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB95_bound) x hxL, (List.forall_iff_forall_mem.mp PB95_prime) x hxL⟩
def PB96 : List Nat := [1,13,17,43,53,59,79,97,137,149,157,167,179,181,199,211,221,223,233,259,263,269,281,289,293,323,329,331,337,353,377,401,419,431,443,451,457,461,469,479,487,493,497,517,527,553,557,581,587,589,601,643,661,667,671,697,703,731,737,739,749,757,763,769,779,787,797,799,821,823,827,847,851,857,893,907,911,931,953,959,973,979,989,997]
lemma PB96_nodup : PB96.Nodup := by decide
lemma PB96_bound : PB96.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB96_prime : PB96.Forall (fun x => Nat.Prime (96000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_96 : 84 ≤ Nat.count (fun k => Nat.Prime (96000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB96.toFinset.card = 84 := by
    rw [List.toFinset_card_of_nodup PB96_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB96 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB96_bound) x hxL, (List.forall_iff_forall_mem.mp PB96_prime) x hxL⟩
def PB97 : List Nat := [1,3,7,21,39,73,81,103,117,127,151,157,159,169,171,177,187,213,231,241,259,283,301,303,327,367,369,373,379,381,387,397,423,429,441,453,459,463,499,501,511,523,547,549,553,561,571,577,579,583,607,609,613,649,651,673,687,711,729,771,777,787,789,813,829,841,843,847,849,859,861,871,879,883,919,927,931,943,961,967,973,987]
lemma PB97_nodup : PB97.Nodup := by decide
lemma PB97_bound : PB97.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB97_prime : PB97.Forall (fun x => Nat.Prime (97000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_97 : 82 ≤ Nat.count (fun k => Nat.Prime (97000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB97.toFinset.card = 82 := by
    rw [List.toFinset_card_of_nodup PB97_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB97 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB97_bound) x hxL, (List.forall_iff_forall_mem.mp PB97_prime) x hxL⟩
def PB98 : List Nat := [9,11,17,41,47,57,81,101,123,129,143,179,207,213,221,227,251,257,269,297,299,317,321,323,327,347,369,377,387,389,407,411,419,429,443,453,459,467,473,479,491,507,519,533,543,561,563,573,597,621,627,639,641,663,669,689,711,713,717,729,731,737,773,779,801,807,809,837,849,867,869,873,887,893,897,899,909,911,927,929,939,947,953,963,981,993,999]
lemma PB98_nodup : PB98.Nodup := by decide
lemma PB98_bound : PB98.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB98_prime : PB98.Forall (fun x => Nat.Prime (98000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_98 : 87 ≤ Nat.count (fun k => Nat.Prime (98000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB98.toFinset.card = 87 := by
    rw [List.toFinset_card_of_nodup PB98_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB98 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB98_bound) x hxL, (List.forall_iff_forall_mem.mp PB98_prime) x hxL⟩
def PB99 : List Nat := [13,17,23,41,53,79,83,89,103,109,119,131,133,137,139,149,173,181,191,223,233,241,251,257,259,277,289,317,347,349,367,371,377,391,397,401,409,431,439,469,487,497,523,527,529,551,559,563,571,577,581,607,611,623,643,661,667,679,689,707,709,713,719,721,733,761,767,787,793,809,817,823,829,833,839,859,871,877,881,901,907,923,929,961,971,989,991]
lemma PB99_nodup : PB99.Nodup := by decide
lemma PB99_bound : PB99.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma PB99_prime : PB99.Forall (fun x => Nat.Prime (99000 + x)) := by
  repeat constructor <;> norm_num
lemma prime_block_99 : 87 ≤ Nat.count (fun k => Nat.Prime (99000 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : PB99.toFinset.card = 87 := by
    rw [List.toFinset_card_of_nodup PB99_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ PB99 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp PB99_bound) x hxL, (List.forall_iff_forall_mem.mp PB99_prime) x hxL⟩
