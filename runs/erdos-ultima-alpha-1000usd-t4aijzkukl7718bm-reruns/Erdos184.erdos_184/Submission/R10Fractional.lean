import FormalConjecturesUtil

/-!
A finite binary circuit system (R10) whose integral partition count is
invariant and critical at two, but whose fractional cost is 5/3.
This is NOT a SimpleGraph and does not disprove Erdos 184. Regularity of its
signed matrix is separately certificate-checked, not asserted in this file.
-/
open scoped Classical BigOperators
namespace Erdos184.R10Fractional
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

abbrev Ground := Fin 10
abbrev Index := Fin 30

def columns : Ground → Fin 5 → ZMod 2 := ![
  ![1,0,0,0,0],
  ![0,1,0,0,0],
  ![0,0,1,0,0],
  ![0,0,0,1,0],
  ![0,0,0,0,1],
  ![1,1,0,0,1],
  ![1,1,1,0,0],
  ![0,1,1,1,0],
  ![0,0,1,1,1],
  ![1,0,0,1,1]]

def circuit : Index → Finset Ground := ![
  {0,1,4,5},
  {0,1,2,6},
  {2,4,5,6},
  {1,2,3,7},
  {0,2,3,4,5,7},
  {0,3,6,7},
  {1,3,4,5,6,7},
  {2,3,4,8},
  {0,1,2,3,5,8},
  {0,1,3,4,6,8},
  {3,5,6,8},
  {1,4,7,8},
  {0,5,7,8},
  {0,2,4,6,7,8},
  {1,2,5,6,7,8},
  {0,3,4,9},
  {1,3,5,9},
  {1,2,3,4,6,9},
  {0,2,3,5,6,9},
  {0,1,2,4,7,9},
  {2,5,7,9},
  {4,6,7,9},
  {0,1,5,6,7,9},
  {0,2,8,9},
  {1,2,4,5,8,9},
  {1,6,8,9},
  {0,4,5,6,8,9},
  {0,1,3,7,8,9},
  {3,4,5,7,8,9},
  {2,3,6,7,8,9}]

def IsEven (S : Finset Ground) : Prop := (∑ e ∈ S, columns e) = 0

instance (S : Finset Ground) : Decidable (IsEven S) := inferInstanceAs (Decidable (_ = _))

lemma even_sets_classified : ∀ S : Finset Ground,
    IsEven S ↔ S = ∅ ∨ S = Finset.univ ∨ ∃ i : Index, circuit i = S := by decide

lemma circuit_card (i : Index) : (circuit i).card = 4 ∨ (circuit i).card = 6 := by
  fin_cases i <;> decide

lemma circuit_even (i : Index) : IsEven (circuit i) :=
  (even_sets_classified _).mpr (Or.inr (Or.inr ⟨i,rfl⟩))

lemma even_nonempty_card {S : Finset Ground} (he : IsEven S) (hn : S ≠ ∅) : 4 ≤ S.card := by
  rcases (even_sets_classified S).mp he with hs | hs | ⟨i,rfl⟩
  · exact (hn hs).elim
  · subst S; decide
  · have hh := circuit_card i; omega

lemma even_sdiff {S T : Finset Ground} (hTS : T ⊆ S) (hS : IsEven S) (hT : IsEven T) :
    IsEven (S \ T) := by
  have hh := Finset.sum_sdiff (f := columns) hTS
  change (∑ e ∈ S \ T, columns e) = 0
  rw [hS,hT,add_zero] at hh
  exact hh

/-- The displayed sets really are minimal nonempty binary zero-sum sets. -/
lemma circuit_minimal (i : Index) {T : Finset Ground} (hT : T ⊆ circuit i)
    (he : IsEven T) (hne : T ≠ ∅) : T = circuit i := by
  by_contra hn
  have hdiff : circuit i \ T ≠ ∅ := by
    intro hz
    have hh := Finset.sdiff_eq_empty_iff_subset.mp hz
    exact hn (Finset.Subset.antisymm hT hh)
  have hlow := even_nonempty_card he hne
  have hlow' := even_nonempty_card (even_sdiff hT (circuit_even i) he) hdiff
  have hcount := Finset.card_sdiff_add_card_eq_card hT
  have hsize := circuit_card i
  omega

def IsCircuit (S : Finset Ground) : Prop :=
  IsEven S ∧ S ≠ ∅ ∧ ∀ T : Finset Ground, T ⊆ S → IsEven T → T ≠ ∅ → T = S

lemma isCircuit_iff (S : Finset Ground) : IsCircuit S ↔ ∃ i : Index, circuit i = S := by
  constructor
  · rintro ⟨he,hn,hm⟩
    rcases (even_sets_classified S).mp he with hz | hz | hi
    · exact (hn hz).elim
    · subst S
      have hzero : circuit 0 ≠ ∅ := by decide
      have hh := hm (circuit 0) (Finset.subset_univ _) (circuit_even 0) hzero
      have hne : circuit 0 ≠ Finset.univ := by decide
      exact (hne hh).elim
    · exact hi
  · rintro ⟨i,rfl⟩
    refine ⟨circuit_even i,?_,fun T ht he hn => circuit_minimal i ht he hn⟩
    intro hz
    have hh := circuit_card i
    rw [hz,Finset.card_empty] at hh
    omega

/-- Exact once-per-element coverage by an integral circuit subfamily. -/
def IsPartition (S : Finset Ground) (D : Finset Index) : Prop :=
  ∀ e : Ground, (D.filter (fun i => e ∈ circuit i)).card = if e ∈ S then 1 else 0

instance (S : Finset Ground) (D : Finset Index) : Decidable (IsPartition S D) :=
  inferInstanceAs (Decidable (∀ e : Ground,
    (D.filter (fun i => e ∈ circuit i)).card = if e ∈ S then 1 else 0))

lemma partition_singleton (i : Index) : IsPartition (circuit i) {i} := by
  intro e
  by_cases he : e ∈ circuit i <;> simp [Finset.filter_singleton,he]

lemma partition_empty : IsPartition ∅ ∅ := by intro e; simp

lemma partition_size_identity {S : Finset Ground} {D : Finset Index} (hD : IsPartition S D) :
    (∑ i ∈ D, (circuit i).card) = S.card := by
  calc
    (∑ i ∈ D, (circuit i).card) =
        ∑ i ∈ D, ∑ e : Ground, if e ∈ circuit i then 1 else 0 := by simp
    _ = ∑ e : Ground, ∑ i ∈ D, if e ∈ circuit i then 1 else 0 := Finset.sum_comm
    _ = ∑ e : Ground, (D.filter (fun i => e ∈ circuit i)).card := by
      simp only [Finset.card_filter]
    _ = ∑ e : Ground, if e ∈ S then 1 else 0 := Finset.sum_congr rfl (fun e _ => hD e)
    _ = S.card := by simp

lemma full_partition_card {D : Finset Index} (hD : IsPartition Finset.univ D) : D.card = 2 := by
  have hs : (∑ i ∈ D, (circuit i).card) = 10 := by
    simpa using partition_size_identity hD
  have hl : (∑ _i ∈ D, 4) ≤ ∑ i ∈ D, (circuit i).card := by
    apply Finset.sum_le_sum
    intro i _; have hh := circuit_card i; omega
  have hu : (∑ i ∈ D, (circuit i).card) ≤ ∑ _i ∈ D, 6 := by
    apply Finset.sum_le_sum
    intro i _; have hh := circuit_card i; omega
  simp only [Finset.sum_const,nsmul_eq_mul] at hl hu
  rw [hs] at hl hu
  norm_cast at hl hu
  omega

lemma full_partition_exists : IsPartition Finset.univ ({0,29} : Finset Index) := by decide

lemma proper_even_partition {S : Finset Ground} (he : IsEven S) (hp : S ≠ Finset.univ) :
    ∃ D : Finset Index, IsPartition S D ∧ D.card ≤ 1 := by
  rcases (even_sets_classified S).mp he with rfl | hs | ⟨i,rfl⟩
  · exact ⟨∅,partition_empty,by simp⟩
  · exact (hp hs).elim
  · exact ⟨{i},partition_singleton i,by simp⟩

def large : Finset Index := Finset.univ.filter (fun i => (circuit i).card = 6)

noncomputable def weight (i : Index) : ℝ := if i ∈ large then 1/9 else 0

lemma large_card : large.card = 15 := by decide

lemma large_incidence (e : Ground) : (large.filter (fun i => e ∈ circuit i)).card = 9 := by
  fin_cases e <;> decide

lemma weight_nonneg (i : Index) : 0 ≤ weight i := by unfold weight; split_ifs <;> norm_num

lemma weight_sum : (∑ i, weight i) = 5/3 := by
  simp only [weight,Finset.sum_ite_mem,Finset.univ_inter,Finset.sum_const,large_card,nsmul_eq_mul]
  norm_num

lemma weight_coverage (e : Ground) : (∑ i : Index, if e ∈ circuit i then weight i else 0) = 1 := by
  have hp : ∀ i : Index, (if e ∈ circuit i then weight i else 0) =
      (if i ∈ large ∧ e ∈ circuit i then (1 : ℝ) else 0) / 9 := by
    intro i
    by_cases hi : i ∈ large <;> by_cases he : e ∈ circuit i <;> simp [weight,hi,he]
  simp_rw [hp]
  rw [← Finset.sum_div,Finset.sum_boole]
  have hfilter : Finset.univ.filter (fun i => i ∈ large ∧ e ∈ circuit i) =
      large.filter (fun i => e ∈ circuit i) := by ext i; simp
  rw [hfilter,large_incidence]
  norm_num

def IsFractionalPartition (t : Index → ℝ) : Prop :=
  (∀ i, 0 ≤ t i) ∧ ∀ e : Ground, (∑ i : Index, if e ∈ circuit i then t i else 0) = 1

lemma fractional_size_identity {t : Index → ℝ} (ht : IsFractionalPartition t) :
    (∑ i : Index, t i * (circuit i).card) = 10 := by
  calc
    (∑ i : Index, t i * (circuit i).card) =
        ∑ i : Index, ∑ e : Ground, if e ∈ circuit i then t i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_filter]
      simp [mul_comm]
    _ = ∑ e : Ground, ∑ i : Index, if e ∈ circuit i then t i else 0 := Finset.sum_comm
    _ = ∑ _e : Ground, (1 : ℝ) := Finset.sum_congr rfl (fun e _ => ht.2 e)
    _ = 10 := by norm_num

lemma fractional_lower_bound {t : Index → ℝ} (ht : IsFractionalPartition t) :
    (5/3 : ℝ) ≤ ∑ i, t i := by
  have hs := fractional_size_identity ht
  have hu : (∑ i : Index, t i * (circuit i).card) ≤ ∑ i : Index, t i * 6 := by
    apply Finset.sum_le_sum
    intro i _
    apply mul_le_mul_of_nonneg_left _ (ht.1 i)
    have hh : (circuit i).card ≤ 6 := by have h := circuit_card i; omega
    exact_mod_cast hh
  rw [hs,← Finset.sum_mul] at hu
  linarith

lemma fractional_optimum : IsFractionalPartition weight ∧ (∑ i, weight i) = 5/3 ∧
    ∀ t : Index → ℝ, IsFractionalPartition t → (∑ i, weight i) ≤ ∑ i, t i := by
  refine ⟨⟨weight_nonneg,weight_coverage⟩,weight_sum,?_⟩
  intro t ht
  rw [weight_sum]
  exact fractional_lower_bound ht

/-- Invariance and criticality do not imply fractional exactness for arbitrary
binary circuit systems. No assertion about SimpleGraph cycles is made. -/
theorem invariant_critical_with_fractional_gap :
    (∃ D : Finset Index, IsPartition Finset.univ D) ∧
    (∀ D : Finset Index, IsPartition Finset.univ D → D.card = 2) ∧
    (∀ S : Finset Ground, IsEven S → S ≠ Finset.univ →
      ∃ D : Finset Index, IsPartition S D ∧ D.card ≤ 1) ∧
    (∀ i, 0 ≤ weight i) ∧
    (∀ e : Ground, (∑ i : Index, if e ∈ circuit i then weight i else 0) = 1) ∧
    (∑ i, weight i) = 5/3 ∧ (∑ i, weight i) < 2 := by
  refine ⟨⟨{0,29},full_partition_exists⟩,fun _ h => full_partition_card h,
    fun _ he hp => proper_even_partition he hp,weight_nonneg,weight_coverage,weight_sum,?_⟩
  rw [weight_sum]
  norm_num

end Erdos184.R10Fractional
