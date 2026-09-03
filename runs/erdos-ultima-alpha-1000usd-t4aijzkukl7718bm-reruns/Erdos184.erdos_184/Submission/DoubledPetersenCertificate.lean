import Submission.DoubledPetersenData

/-! Minimum and non-invariant partition counts in the finite doubled Petersen model.
The transfer to cycles of the subdivided simple graph is not formalized here. -/
namespace Erdos184
namespace DoubledPetersenCertificate

lemma pair_mem {a b : ℕ} (ha : a ∈ allCodes) (hb : b ∈ allCodes) :
    a + b ∈ pairSums := by
  apply List.mem_flatMap.mpr
  exact ⟨a,ha,List.mem_map.mpr ⟨b,hb,rfl⟩⟩

lemma no_four_code_sum {a b c d : ℕ}
    (ha : a ∈ allCodes) (hb : b ∈ allCodes)
    (hc : c ∈ allCodes) (hd : d ∈ allCodes) :
    a + b + c + d ≠ fullCode := by
  intro heq
  have hleft : a+b ∈ leftSums :=
    (SortedDisjointCertificate.mem_sorted _ _).mpr (pair_mem ha hb)
  have hright : a+b ∈ rightSums := by
    apply (SortedDisjointCertificate.mem_sorted _ _).mpr
    apply List.mem_map.mpr
    refine ⟨c+d,List.mem_filter.mpr ⟨pair_mem hc hd,?_⟩,?_⟩
    · simp only [decide_eq_true_eq]
      omega
    · omega
  have hh := SortedDisjointCertificate.check_sound 11000 leftSums rightSums
    (SortedDisjointCertificate.sorted_pairwise pairSums)
    (SortedDisjointCertificate.sorted_pairwise _) checked_separation
  exact hh hleft hright

lemma partition_length_lower (D : List (Fin 72)) (hD : IsPartition D) :
    5 ≤ D.length := by
  by_contra hn
  have hlen : D.length ≤ 4 := by omega
  let A := D.map code ++ List.replicate (4-D.length) 0
  have hA : A.length = 4 := by
    simp only [A,List.length_append,List.length_map,List.length_replicate]
    omega
  have hm : ∀ a ∈ A, a ∈ allCodes := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
      exact List.mem_cons_of_mem 0 (List.mem_ofFn.mpr ⟨i,rfl⟩)
    · have ha0 := (List.mem_replicate.mp ha).2
      simp [ha0,allCodes]
  have hsum : A.sum = fullCode := by
    simp only [A,List.sum_append,List.sum_replicate,smul_zero,add_zero]
    exact partition_code D hD
  obtain ⟨a,b,c,d,hlist⟩ := List.length_eq_four.mp hA
  have hma : a ∈ allCodes := hm a (by simp [hlist])
  have hmb : b ∈ allCodes := hm b (by simp [hlist])
  have hmc : c ∈ allCodes := hm c (by simp [hlist])
  have hmd : d ∈ allCodes := hm d (by simp [hlist])
  apply no_four_code_sum hma hmb hmc hmd
  simpa only [hlist,List.sum_cons,List.sum_nil,add_zero,add_assoc] using hsum

/-- Every one of the 72 represented circuit types extends to a minimum
five-piece partition of the doubled edge set. -/
lemma every_type_optimally_extendable (i : Fin 72) :
    ∃ D : List (Fin 72), i ∈ D ∧ IsPartition D ∧ D.length = 5 ∧
      ∀ E : List (Fin 72), IsPartition E → D.length ≤ E.length := by
  refine ⟨extension i,mem_extension i,extension_partition i,extension_length i,?_⟩
  intro E hE
  rw [extension_length]
  exact partition_length_lower E hE

/-- Parallel-edge pairs alone give a partition with fifteen pieces. -/
def digonPartition : List (Fin 72) :=
  [57,58,59,60,61,62,63,64,65,66,67,68,69,70,71]

lemma digon_partition : IsPartition digonPartition := by unfold IsPartition; decide
lemma digon_partition_length : digonPartition.length = 15 := rfl

lemma variable_partition_sizes :
    ∃ D E : List (Fin 72), IsPartition D ∧ IsPartition E ∧ D.length < E.length := by
  refine ⟨extension 0,digonPartition,extension_partition 0,digon_partition,?_⟩
  rw [extension_length,digon_partition_length]
  decide

end DoubledPetersenCertificate
end Erdos184
