import FormalConjecturesUtil

/-!
An explicit binary circuit system in which deleting a parallel pair from a
three-count-critical restriction leaves a noncritical two-count restriction.
This is not a SimpleGraph and does not disprove Erdős 184.
-/
open scoped Classical BigOperators
namespace Erdos184.ParallelPairCriticalObstruction
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

abbrev Ground := Fin 11
abbrev Index := Fin 57

def columns : Ground → Fin 4 → ZMod 2 := ![
  ![1,0,1,0],
  ![0,1,1,0],
  ![1,1,1,0],
  ![0,0,0,1],
  ![1,0,0,1],
  ![0,1,0,1],
  ![0,0,1,1],
  ![1,0,1,1],
  ![0,1,1,1],
  ![0,0,1,0],
  ![0,0,1,0]]

def circuit : Index → Finset Ground := ![
  {9,10},
  {0,4,6},
  {1,5,6},
  {0,3,7},
  {2,5,7},
  {1,3,8},
  {2,4,8},
  {3,6,9},
  {4,7,9},
  {5,8,9},
  {3,6,10},
  {4,7,10},
  {5,8,10},
  {1,2,3,4},
  {0,2,3,5},
  {0,1,4,5},
  {1,2,6,7},
  {3,4,6,7},
  {0,2,6,8},
  {3,5,6,8},
  {0,1,7,8},
  {4,5,7,8},
  {0,1,2,9},
  {0,3,4,9},
  {1,3,5,9},
  {2,4,5,9},
  {0,6,7,9},
  {1,6,8,9},
  {2,7,8,9},
  {0,1,2,10},
  {0,3,4,10},
  {1,3,5,10},
  {2,4,5,10},
  {0,6,7,10},
  {1,6,8,10},
  {2,7,8,10},
  {0,1,2,3,6},
  {2,3,4,5,6},
  {0,1,2,4,7},
  {1,3,4,5,7},
  {0,1,2,5,8},
  {0,3,4,5,8},
  {2,3,6,7,8},
  {1,4,6,7,8},
  {0,5,6,7,8},
  {1,2,4,6,9},
  {0,2,5,6,9},
  {1,2,3,7,9},
  {0,1,5,7,9},
  {0,2,3,8,9},
  {0,1,4,8,9},
  {1,2,4,6,10},
  {0,2,5,6,10},
  {1,2,3,7,10},
  {0,1,5,7,10},
  {0,2,3,8,10},
  {0,1,4,8,10}]

def IsEven (S : Finset Ground) : Prop := (∑ e ∈ S, columns e) = 0
instance (S : Finset Ground) : Decidable (IsEven S) := inferInstanceAs (Decidable (_ = _))

def IsCircuit (S : Finset Ground) : Prop :=
  IsEven S ∧ S ≠ ∅ ∧ ∀ T : Finset Ground, T ⊆ S → IsEven T → T ≠ ∅ → T = S

lemma circuit_even : ∀ i : Index, IsEven (circuit i) := by decide
lemma circuit_nonempty : ∀ i : Index, circuit i ≠ ∅ := by decide
lemma circuit_card_le : ∀ i : Index, (circuit i).card ≤ 5 := by decide
lemma circuit_subsets_check : ∀ i : Index, ∀ T : (circuit i).powerset,
    IsEven T.val → T.val = ∅ ∨ T.val = circuit i := by decide
lemma circuit_subsets (i : Index) (T : Finset Ground) (hT : T ∈ (circuit i).powerset)
    (he : IsEven T) : T = ∅ ∨ T = circuit i :=
  circuit_subsets_check i ⟨T,hT⟩ he

lemma circuit_minimal (i : Index) : IsCircuit (circuit i) := by
  refine ⟨circuit_even i,circuit_nonempty i,?_⟩
  intro T hT he hn
  exact (circuit_subsets i T (Finset.mem_powerset.mpr hT) he).resolve_left hn

def base : Finset Ground := {0,1,2,3,4,5,6,7,8}
abbrev Small := base.powerset

def extend (T : Small) (b : Fin 4) : Finset Ground :=
  T.val ∪ ![∅,{9},{10},{9,10}] b

lemma represented (S : Finset Ground) : ∃ (T : Small) (b : Fin 4), extend T b = S := by
  have hs : S \ {9,10} ⊆ base := by
    intro i hi
    fin_cases i <;> simp_all [base]
  let T : Small := ⟨S \ {9,10},Finset.mem_powerset.mpr hs⟩
  by_cases h9 : (9 : Ground) ∈ S <;> by_cases h10 : (10 : Ground) ∈ S
  · refine ⟨T,3,?_⟩
    ext i; fin_cases i <;> simp [extend,T,h9,h10]
  · refine ⟨T,1,?_⟩
    ext i; fin_cases i <;> simp [extend,T,h9,h10]
  · refine ⟨T,2,?_⟩
    ext i; fin_cases i <;> simp [extend,T,h9,h10]
  · refine ⟨T,0,?_⟩
    ext i; fin_cases i <;> simp [extend,T,h9,h10]

lemma contains_listed_check : ∀ (b : Fin 4) (T : Small),
    IsEven (extend T b) → extend T b ≠ ∅ →
    ∃ i : Index, circuit i ⊆ extend T b := by decide

lemma contains_listed (S : Finset Ground) (he : IsEven S) (hn : S ≠ ∅) :
    ∃ i : Index, circuit i ⊆ S := by
  obtain ⟨T,b,rfl⟩ := represented S
  exact contains_listed_check b T he hn

lemma circuit_complete (S : Finset Ground) : IsCircuit S ↔ ∃ i : Index, circuit i = S := by
  constructor
  · rintro ⟨he,hn,hm⟩
    obtain ⟨i,hi⟩ := contains_listed S he hn
    exact ⟨i,hm (circuit i) hi (circuit_even i) (circuit_nonempty i)⟩
  · rintro ⟨i,rfl⟩
    exact circuit_minimal i

/-- Classification only for proper even restrictions. The full restriction
requires three circuits and is intentionally excluded. -/
lemma proper_even_pairs_check : ∀ (b : Fin 4) (T : Small),
    IsEven (extend T b) → extend T b ≠ Finset.univ →
    extend T b = ∅ ∨ (∃ i : Index, extend T b = circuit i) ∨
      (∃ i j : Index, Disjoint (circuit i) (circuit j) ∧ circuit i ∪ circuit j = extend T b) := by decide

lemma proper_even_pairs (S : Finset Ground) (he : IsEven S) (hn : S ≠ Finset.univ) :
    S = ∅ ∨ (∃ i : Index, S = circuit i) ∨
      (∃ i j : Index, Disjoint (circuit i) (circuit j) ∧ circuit i ∪ circuit j = S) := by
  obtain ⟨T,b,rfl⟩ := represented S
  exact proper_even_pairs_check b T he hn

def IsPartition (S : Finset Ground) (D : Finset Index) : Prop :=
  ∀ e : Ground, (D.filter (fun i => e ∈ circuit i)).card = if e ∈ S then 1 else 0
instance (S : Finset Ground) (D : Finset Index) : Decidable (IsPartition S D) :=
  inferInstanceAs (Decidable (∀ e : Ground,
    (D.filter (fun i => e ∈ circuit i)).card = if e ∈ S then 1 else 0))

def HasMinimum (S : Finset Ground) (k : ℕ) : Prop :=
  (∃ D : Finset Index, IsPartition S D ∧ D.card = k) ∧
    ∀ D : Finset Index, IsPartition S D → k ≤ D.card

def IsCountCritical (S : Finset Ground) (k : ℕ) : Prop :=
  IsEven S ∧ HasMinimum S k ∧ ∀ T : Finset Ground, T ⊂ S → IsEven T →
    ∃ D : Finset Index, IsPartition T D ∧ D.card < k

lemma partition_empty : IsPartition ∅ ∅ := by intro e; simp
lemma partition_singleton (i : Index) : IsPartition (circuit i) {i} := by
  intro e
  by_cases he : e ∈ circuit i <;> simp [Finset.filter_singleton,he]

lemma partition_pair (i j : Index) (hd : Disjoint (circuit i) (circuit j)) :
    IsPartition (circuit i ∪ circuit j) {i,j} := by
  have hij : i ≠ j := by
    rintro rfl
    exact circuit_nonempty i (disjoint_self.mp hd)
  intro e
  have hedis : ¬(e ∈ circuit i ∧ e ∈ circuit j) := fun h => Finset.disjoint_left.mp hd h.1 h.2
  by_cases hei : e ∈ circuit i <;> by_cases hej : e ∈ circuit j
  · exact (hedis ⟨hei,hej⟩).elim
  · simp [Finset.filter_insert,Finset.filter_singleton,hei,hej]
  · simp [Finset.filter_insert,Finset.filter_singleton,hei,hej]
  · simp [Finset.filter_insert,Finset.filter_singleton,hei,hej]

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

lemma partition_card_bound {S : Finset Ground} {D : Finset Index}
    (hd : IsPartition S D) : S.card ≤ 5 * D.card := by
  rw [← partition_size_identity hd]
  calc
    (∑ i ∈ D, (circuit i).card) ≤ ∑ _i ∈ D, 5 :=
      Finset.sum_le_sum (fun i _ => circuit_card_le i)
    _ = _ := by simp [Nat.mul_comm]

lemma proper_partition {S : Finset Ground} (he : IsEven S) (hp : S ≠ Finset.univ) :
    ∃ D : Finset Index, IsPartition S D ∧ D.card ≤ 2 := by
  rcases proper_even_pairs S he hp with rfl | ⟨i,rfl⟩ | ⟨i,j,hd,rfl⟩
  · exact ⟨∅,partition_empty,by simp⟩
  · exact ⟨{i},partition_singleton i,by simp⟩
  · exact ⟨{i,j},partition_pair i j hd,by by_cases h : i = j <;> simp [h]⟩

def pair : Finset Ground := {9,10}
def residual : Finset Ground := {0,1,2,3,4,5,6,7,8}
def witness : Finset Ground := {0,1,3,5,6,7}

lemma pair_parallel : columns 9 = columns 10 ∧ columns 9 ≠ 0 := by decide
lemma pair_circuit : IsCircuit pair := by
  exact circuit_minimal 0
lemma residual_eq : residual = Finset.univ \ pair := by decide
lemma witness_proper : witness ⊂ residual := by decide
lemma witness_even : IsEven witness := by decide
lemma residual_even : IsEven residual := by decide
lemma full_even : IsEven (Finset.univ : Finset Ground) := by decide

lemma full_minimum : HasMinimum Finset.univ 3 := by
  constructor
  · exact ⟨{0,13,44},by decide,by decide⟩
  · intro D hd
    have hh := partition_card_bound hd
    have hc : (Finset.univ : Finset Ground).card = 11 := by decide
    rw [hc] at hh
    omega

lemma full_critical : IsCountCritical Finset.univ 3 := by
  refine ⟨full_even,full_minimum,?_⟩
  intro T ht he
  obtain ⟨D,hd,hc⟩ := proper_partition he (ne_of_lt ht)
  exact ⟨D,hd,by omega⟩

lemma residual_minimum : HasMinimum residual 2 := by
  constructor
  · exact ⟨{13,44},by decide,by decide⟩
  · intro D hd
    have hh := partition_card_bound hd
    have hc : residual.card = 9 := by decide
    rw [hc] at hh
    omega

lemma witness_minimum : HasMinimum witness 2 := by
  constructor
  · exact ⟨{2,3},by decide,by decide⟩
  · intro D hd
    have hh := partition_card_bound hd
    have hc : witness.card = 6 := by decide
    rw [hc] at hh
    omega

lemma residual_not_critical : ¬ IsCountCritical residual 2 := by
  intro hc
  obtain ⟨D,hd,hlt⟩ := hc.2.2 witness witness_proper witness_even
  exact (not_lt_of_ge (witness_minimum.2 D hd)) hlt

lemma full_noninvariant : ∃ D E : Finset Index,
    IsPartition Finset.univ D ∧ IsPartition Finset.univ E ∧ D.card = 3 ∧ E.card = 4 := by
  exact ⟨{0,13,44},{0,1,4,5},by decide,by decide,by decide,by decide⟩

/-- A parallel pair is a circuit, the full system is critical at three,
and deleting this pair gives minimum two but not count-criticality at two. -/
theorem obstruction : IsCircuit pair ∧ pair.card = 2 ∧
    IsCountCritical Finset.univ 3 ∧ HasMinimum (Finset.univ \ pair) 2 ∧
    ¬ IsCountCritical (Finset.univ \ pair) 2 := by
  rw [← residual_eq]
  exact ⟨pair_circuit,by decide,full_critical,residual_minimum,residual_not_critical⟩

end Erdos184.ParallelPairCriticalObstruction
