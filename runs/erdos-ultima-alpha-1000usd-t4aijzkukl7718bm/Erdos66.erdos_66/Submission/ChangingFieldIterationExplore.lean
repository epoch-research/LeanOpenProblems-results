import Submission.ChangingFieldLineStepExplore

/-! Actual varying-field recursive spaces and inherited line peaks.
Field and color embeddings may change at every stage; additions are allowed. -/
namespace Erdos66ChangingFieldIteration
open Erdos66ChangingFieldLineStep Erdos66LineRecoloringIteration
  Erdos66OriginRepair Erdos66ParabolaRepair
open scoped Classical
set_option maxHeartbeats 3000000
universe u
variable (G : Type u) (F : ℕ → Type u)

def Space : ℕ → Type u
  | 0 => G
  | n+1 => Space n × (F (n+1)×F (n+1))

instance spaceAddCommGroup [AddCommGroup G] [∀ n, Field (F n)] (n : ℕ) :
    AddCommGroup (Space G F n) :=
  match n with
  | 0 => inferInstanceAs (AddCommGroup G)
  | n+1 => by
    letI := spaceAddCommGroup n
    exact inferInstanceAs (AddCommGroup (Space G F n×(F (n+1)×F (n+1))))

instance spaceDecidableEq [DecidableEq G] [∀ n, DecidableEq (F n)] (n : ℕ) :
    DecidableEq (Space G F n) :=
  match n with
  | 0 => inferInstanceAs (DecidableEq G)
  | n+1 => by
    letI := spaceDecidableEq n
    exact inferInstanceAs (DecidableEq (Space G F n×(F (n+1)×F (n+1))))

instance spaceFintype [Fintype G] [∀ n, Fintype (F n)] (n : ℕ) :
    Fintype (Space G F n) :=
  match n with
  | 0 => inferInstanceAs (Fintype G)
  | n+1 => by
    letI := spaceFintype n
    exact inferInstanceAs (Fintype (Space G F n×(F (n+1)×F (n+1))))

lemma space_card_succ [Fintype G] [∀ n, Fintype (F n)] (n : ℕ) :
    Fintype.card (Space G F (n+1))=Fintype.card (Space G F n)*(Fintype.card (F (n+1)))^2 := by
  change Fintype.card (Space G F n×(F (n+1)×F (n+1)))=_
  simp only [Fintype.card_prod,pow_two]

variable {G F} [AddCommGroup G] [DecidableEq G]
  [∀ n, Field (F n)] [∀ n, Fintype (F n)] [∀ n, DecidableEq (F n)]

lemma two_step_peak
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v)
    (n : ℕ) (v : F n) (z : Space G F n) :
    ∃ z' : Space G F (n+2),
      2*pairCount (B n v) (B n v) z≤pairCount (B (n+2) 0) (B (n+2) 0) z' := by
  obtain ⟨z',hz⟩ := two_step_amplification (e n) (e (n+1)) (B n)
    (τ n) (α n) (τ (n+1)) (α (n+1)) (hα n) (hα (n+1)) v 0 z
  have hsub : step (e (n+1)) (step (e n) (B n) (τ n) (α n)) (τ (n+1)) (α (n+1)) 0⊆B (n+2) 0 :=
    (step_mono (e (n+1)) (hstep n) _ _ _).trans (hstep (n+1) 0)
  exact ⟨z',hz.trans (pairCount_mono hsub hsub z')⟩

/-- At any starting stage, a nonempty color produces exponential peaks.
This is independent of the subsequent field sizes. -/
theorem exponential_peak_from
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v)
    (N : ℕ) (v : F N) (hB : (B N v).Nonempty) :
    ∀ k : ℕ, ∃ w : F (N+2*k), ∃ z : Space G F (N+2*k),
      2^k≤pairCount (B (N+2*k) w) (B (N+2*k) w) z := by
  obtain ⟨a,ha⟩ := hB
  intro k
  induction k with
  | zero => exact ⟨v,a+a,singleton_seed (B N) v ha⟩
  | succ k ih =>
    obtain ⟨w,z,hz⟩ := ih
    obtain ⟨z',hz'⟩ := two_step_peak B e τ α hα hstep (N+2*k) w z
    have hid : N+2*(k+1)=N+2*k+2 := by omega
    rw [hid]
    refine ⟨0,z',?_⟩
    have hh := (Nat.mul_le_mul_left 2 hz).trans hz'
    simpa only [pow_succ,Nat.mul_comm (2^k) 2] using hh

lemma nonempty_stages
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F 0) (hB : (B 0 v).Nonempty) :
    ∀ n, ∃ w : F n, (B n w).Nonempty := by
  intro n
  induction n with
  | zero => exact ⟨v,hB⟩
  | succ n ih =>
    obtain ⟨w,hw⟩ := ih
    exact ⟨0,(step_nonempty (e n) (B n) (τ n) (α n) (hα n) w hw 0).mono (hstep n 0)⟩

lemma union_step_subset
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v) (n : ℕ) :
    Finset.univ.biUnion (step (e n) (B n) (τ n) (α n))⊆Finset.univ.biUnion (B (n+1)) := by
  intro a ha
  obtain ⟨v,hv,ha⟩ := Finset.mem_biUnion.mp ha
  exact Finset.mem_biUnion.mpr ⟨v,Finset.mem_univ _,hstep n v ha⟩

/-- Every stage also has a peak at least the next field size. -/
theorem field_peak_each_stage
    (B : (n : ℕ) → F n → Finset (Space G F n))
    (e : (n : ℕ) → F n ↪ F (n+1)) (τ α : (n : ℕ) → F (n+1))
    (hα : ∀ n, α n≠0)
    (hstep : ∀ n v, step (e n) (B n) (τ n) (α n) v⊆B (n+1) v)
    (v : F 0) (hB : (B 0 v).Nonempty) (n : ℕ) :
    ∃ z : Space G F (n+1), Fintype.card (F (n+1))≤
      pairCount (Finset.univ.biUnion (B (n+1))) (Finset.univ.biUnion (B (n+1))) z := by
  obtain ⟨w,hw⟩ := nonempty_stages B e τ α hα hstep v hB n
  obtain ⟨z,hz⟩ := field_size_peak (e n) (B n) (τ n) (α n) w hw
  have hs := union_step_subset B e τ α hstep n
  exact ⟨z,hz.trans (pairCount_mono hs hs z)⟩

end Erdos66ChangingFieldIteration
