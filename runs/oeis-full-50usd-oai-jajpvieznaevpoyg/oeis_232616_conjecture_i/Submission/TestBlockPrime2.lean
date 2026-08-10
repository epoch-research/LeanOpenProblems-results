import FormalConjectures.Util.ProblemImports
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def L0 : List Nat := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,953,967,971,977,983,991,997]
lemma L0_nodup : L0.Nodup := by decide
lemma L0_bound : L0.Forall (fun x => x < 1000) := by
  repeat constructor <;> norm_num
lemma L0_prime : L0.Forall (fun x => Nat.Prime (0 + x)) := by
  repeat constructor <;> norm_num
lemma block0 : 168 ≤ Nat.count (fun k => Nat.Prime (0 + k)) 1000 := by
  rw [Nat.count_eq_card_filter_range]
  have hcard : L0.toFinset.card = 168 := by
    rw [List.toFinset_card_of_nodup L0_nodup]
    rfl
  rw [← hcard]
  apply Finset.card_le_card
  intro x hx
  have hxL : x ∈ L0 := by simpa using (List.mem_toFinset.mp hx)
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨(List.forall_iff_forall_mem.mp L0_bound) x hxL, (List.forall_iff_forall_mem.mp L0_prime) x hxL⟩
