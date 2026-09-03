import Submission.PointwiseCapBlockingExplore

/-! Inclusion-maximal sets under slowly growing fixed pointwise caps can
have arbitrarily late representation holes. No lower-limit implication
is extracted from maximality, and this does not settle Erdős 66. -/
namespace Erdos66MaximalCapWithHoles
open Filter AdditiveCombinatorics Erdos66PointwiseCapBlocking Erdos66Compactness
open scoped Classical Topology
set_option maxHeartbeats 1600000

structure State (q : ℕ → ℕ) where
  C : Finset ℕ
  T : ℕ
  support : ∀ a∈C, a<T
  cap : Capped q (C : Set ℕ)

noncomputable def initial (q : ℕ → ℕ) : State q :=
  ⟨∅,0,by simp,by intro n; simp [sumRep_def]⟩

def Extension {q : ℕ → ℕ} (s : State q) (k : ℕ) (t : State q × ℕ) : Prop :=
  s.C⊆t.1.C ∧ s.T<t.1.T ∧
    (∀ i<s.T, i∈t.1.C ↔ i∈s.C) ∧
    (k∈t.1.C ∨ Blocked q t.1.C k) ∧
    2*s.T<t.1.T ∧ sumRep (t.1.C : Set ℕ) (2*s.T)=0 ∧
    s.T≤t.2 ∧ t.2<t.1.T ∧ q t.2≤sumRep (t.1.C : Set ℕ) t.2+1

variable (q : ℕ → ℕ) (hqtop : Tendsto q atTop atTop)
  (hqsmall : ∀ᶠ n in atTop, (q n)^4<n/12)
include hqtop hqsmall

theorem exists_extension (s : State q) (k : ℕ) : ∃ t, Extension s k t := by
  let x := if k∈s.C then s.T else k
  have hx : x∉s.C := by
    dsimp only [x]
    split_ifs with hk
    · intro hh; have := s.support s.T hh; omega
    · exact hk
  obtain ⟨B,N,hN,hsub,hbound,hmem,hcap,hblock,hhole,hpeak⟩ :=
    exists_blocking_extension q hqtop hqsmall s.C s.T x s.support s.cap hx
  let t : State q := ⟨B,N+1,fun a ha ↦ Nat.lt_succ_of_le (hbound a ha),hcap⟩
  refine ⟨(t,N),hsub,by dsimp [t]; omega,hmem,?_,by dsimp [t]; omega,
    hhole,by omega,by dsimp [t]; omega,hpeak⟩
  by_cases hk : k∈s.C
  · exact Or.inl (hsub hk)
  · exact Or.inr (by simpa only [x,if_neg hk] using hblock)

noncomputable def step (s : State q) (k : ℕ) : State q × ℕ :=
  Classical.choose (exists_extension q hqtop hqsmall s k)

lemma step_spec (s : State q) (k : ℕ) : Extension s k (step q hqtop hqsmall s k) :=
  Classical.choose_spec (exists_extension q hqtop hqsmall s k)

noncomputable def states : ℕ → State q
  | 0 => initial q
  | k+1 => (step q hqtop hqsmall (states k) k).1

local notation "S" => states q hqtop hqsmall

noncomputable def peak (k : ℕ) : ℕ := (step q hqtop hqsmall (S k) k).2

lemma states_step (k : ℕ) :
    (S k).C⊆(S (k+1)).C ∧ (S k).T<(S (k+1)).T ∧
    (∀ i<(S k).T, i∈(S (k+1)).C ↔ i∈(S k).C) ∧
    (k∈(S (k+1)).C ∨ Blocked q (S (k+1)).C k) ∧
    2*(S k).T<(S (k+1)).T ∧ sumRep ((S (k+1)).C : Set ℕ) (2*(S k).T)=0 ∧
    (S k).T≤peak q hqtop hqsmall k ∧ peak q hqtop hqsmall k<(S (k+1)).T ∧
    q (peak q hqtop hqsmall k)≤sumRep ((S (k+1)).C : Set ℕ) (peak q hqtop hqsmall k)+1 :=
  step_spec q hqtop hqsmall (S k) k

lemma cutoff_ge (k : ℕ) : k≤(S k).T := by
  induction k with
  | zero => omega
  | succ k ih => have := (states_step q hqtop hqsmall k).2.1; omega

lemma mem_stable (j k : ℕ) (hjk : j≤k) (i : ℕ) (hi : i<(S j).T) :
    i∈(S k).C ↔ i∈(S j).C := by
  have hmono : Monotone (fun k ↦ (S k).T) :=
    monotone_nat_of_le_succ (fun k ↦ (states_step q hqtop hqsmall k).2.1.le)
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hjk ih =>
    exact ((states_step q hqtop hqsmall k).2.2.1 i (hi.trans_le (hmono hjk))).trans ih

noncomputable def maximalSet : Set ℕ := {i | i∈(S (i+1)).C}

lemma maximalSet_mem (j i : ℕ) (hi : i<(S j).T) :
    i∈maximalSet q hqtop hqsmall ↔ i∈(S j).C := by
  have hi' : i<(S (i+1)).T := lt_of_lt_of_le (Nat.lt_succ_self i) (cutoff_ge q hqtop hqsmall (i+1))
  exact (mem_stable q hqtop hqsmall (i+1) (max (i+1) j) (le_max_left _ _) i hi').symm.trans
    (mem_stable q hqtop hqsmall j (max (i+1) j) (le_max_right _ _) i hi)

lemma states_subset_maximalSet (j : ℕ) : ((S j).C : Set ℕ) ⊆ maximalSet q hqtop hqsmall := by
  intro i hi
  exact (maximalSet_mem q hqtop hqsmall j i ((S j).support i hi)).mpr hi

lemma maximalSet_rep (j n : ℕ) (hn : n<(S j).T) :
    sumRep (maximalSet q hqtop hqsmall) n=sumRep ((S j).C : Set ℕ) n := by
  apply sumRep_congr_below
  intro i hi
  exact maximalSet_mem q hqtop hqsmall j i (hi.trans_lt hn)

lemma maximalSet_capped : Capped q (maximalSet q hqtop hqsmall) := by
  intro n
  rw [maximalSet_rep q hqtop hqsmall (n+1) n
    (lt_of_lt_of_le (Nat.lt_succ_self n) (cutoff_ge q hqtop hqsmall (n+1)))]
  exact (S (n+1)).cap n

/-- Maximality holds in the full fixed-cap class, not merely among the
constructed sequence or among sets constrained to preserve its holes. -/
theorem maximalSet_maximal (B : Set ℕ) (hB : Capped q B)
    (hAB : maximalSet q hqtop hqsmall ⊆ B) : B=maximalSet q hqtop hqsmall := by
  apply Set.Subset.antisymm ?_ hAB
  intro i hi
  rcases (states_step q hqtop hqsmall i).2.2.2.1 with hi' | hblock
  · exact states_subset_maximalSet q hqtop hqsmall (i+1) hi'
  · exact False.elim ((blocked_excludes hblock
      ((states_subset_maximalSet q hqtop hqsmall (i+1)).trans hAB) hB) hi)

theorem maximalSet_holes (K : ℕ) :
    ∃ n≥K, sumRep (maximalSet q hqtop hqsmall) n=0 := by
  refine ⟨2*(S K).T,by have := cutoff_ge q hqtop hqsmall K; omega,?_⟩
  have hh := (states_step q hqtop hqsmall K).2.2.2.2
  rw [maximalSet_rep q hqtop hqsmall (K+1) (2*(S K).T) hh.1]
  exact hh.2.1

theorem maximalSet_peaks (K : ℕ) :
    ∃ n≥K, q n≤sumRep (maximalSet q hqtop hqsmall) n+1 := by
  let n := peak q hqtop hqsmall K
  have hh := (states_step q hqtop hqsmall K).2.2.2.2.2.2
  refine ⟨n, (cutoff_ge q hqtop hqsmall K).trans hh.1,?_⟩
  rw [maximalSet_rep q hqtop hqsmall (K+1) n hh.2.1]
  exact hh.2.2

theorem exists_maximal_with_holes_and_peaks :
    ∃ A : Set ℕ, Capped q A ∧
      (∀ B : Set ℕ, Capped q B → A⊆B → B=A) ∧
      (∀ K : ℕ, ∃ n≥K, sumRep A n=0) ∧
      (∀ K : ℕ, ∃ n≥K, q n≤sumRep A n+1) :=
  ⟨maximalSet q hqtop hqsmall,maximalSet_capped q hqtop hqsmall,
    maximalSet_maximal q hqtop hqsmall,maximalSet_holes q hqtop hqsmall,
    maximalSet_peaks q hqtop hqsmall⟩

end Erdos66MaximalCapWithHoles
