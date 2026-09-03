import Submission.PrefixCopyExplore

/-! Nonstationary chains formed only by repeating their preceding entire
prefix and then padding cannot produce a logarithmic witness. -/
namespace Erdos66RepetitionChain
open Erdos66PrefixCopy Erdos66Explore Filter AdditiveCombinatorics
open scoped Classical Topology
set_option maxHeartbeats 1500000

noncomputable def repeatPrefix (P K : ℕ) (B : Finset ℕ) : Finset ℕ :=
  (Finset.range K).biUnion (fun j ↦ B.image (fun a ↦ j*P+a))

lemma mem_repeatPrefix (P K : ℕ) (B : Finset ℕ) (x : ℕ) :
    x∈repeatPrefix P K B ↔ ∃ j < K, ∃ a∈B, j*P+a=x := by
  simp only [repeatPrefix,Finset.mem_biUnion,Finset.mem_range,Finset.mem_image]

lemma repeatPrefix_one (P : ℕ) (B : Finset ℕ) : repeatPrefix P 1 B=B := by
  ext x
  simp [mem_repeatPrefix]

lemma subset_repeatPrefix (P K : ℕ) (B : Finset ℕ) (hK : 1≤K) :
    B ⊆ repeatPrefix P K B := by
  intro a ha
  exact (mem_repeatPrefix P K B a).mpr ⟨0,by omega,a,ha,by simp⟩

lemma repeatPrefix_below (P K : ℕ) (B : Finset ℕ) (hK : 1≤K)
    (x : ℕ) (hx : x<P) : x∈repeatPrefix P K B ↔ x∈B := by
  constructor
  · intro h
    obtain ⟨j,hj,a,ha,he⟩ := (mem_repeatPrefix P K B x).mp h
    have hj0 : j=0 := by
      by_contra hh
      have hj1 : 1≤j := by omega
      have hmul : P≤j*P := by nlinarith
      omega
    have hax : a=x := by simpa only [hj0,zero_mul,zero_add] using he
    exact hax ▸ ha
  · intro hxB
    exact subset_repeatPrefix P K B hK hxB

noncomputable def chainSet (B : ℕ → Finset ℕ) : Set ℕ := {a | ∃ k, a∈B k}

variable (P K : ℕ → ℕ) (B : ℕ → Finset ℕ)
    (hK : ∀ k, 1≤K k)
    (hsize : ∀ k, K k * P k ≤ P (k+1))
    (hstep : ∀ k, B (k+1)=repeatPrefix (P k) (K k) (B k))

include hK hsize in
lemma periods_mono : Monotone P := by
  apply monotone_nat_of_le_succ
  intro k
  have hh := hK k
  have hs := hsize k
  nlinarith

include hK hstep in
lemma prefixes_mono : Monotone B := by
  apply monotone_nat_of_le_succ
  intro k
  rw [hstep k]
  exact subset_repeatPrefix (P k) (K k) (B k) (hK k)

include hK hsize hstep in
lemma later_prefix_agrees (k j : ℕ) (hkj : k≤j) :
    ∀ x < P k, x∈B j ↔ x∈B k := by
  induction j, hkj using Nat.le_induction with
  | base => simp
  | succ j hj ih =>
    intro x hx
    have hjP := periods_mono P K hK hsize hj
    rw [hstep j,repeatPrefix_below (P j) (K j) (B j) (hK j) x (hx.trans_le hjP)]
    exact ih x hx

include hK hsize hstep in
lemma chainSet_below (k x : ℕ) (hx : x<P k) :
    x∈chainSet B ↔ x∈B k := by
  constructor
  · rintro ⟨j,hj⟩
    rcases le_total j k with hle|hle
    · exact prefixes_mono P K B hK hstep hle hj
    · exact (later_prefix_agrees P K B hK hsize hstep k j hle x hx).mp hj
  · intro hx
    exact ⟨k,hx⟩

include hK hsize hstep in
lemma copying_stage (k : ℕ) (hk : 2≤K k) :
    ∀ a < P k, a∈chainSet B → a+P k∈chainSet B := by
  intro a ha hmem
  have haB := (chainSet_below P K B hK hsize hstep k a ha).mp hmem
  refine ⟨k+1,?_⟩
  rw [hstep k]
  exact (mem_repeatPrefix (P k) (K k) (B k) (a+P k)).mpr
    ⟨1,by omega,a,haB,by omega⟩

include hK hstep in
lemma chainSet_finite_of_eventually_one (k : ℕ) (hk : ∀ j ≥ k, K j=1) :
    (chainSet B).Finite := by
  have htail : ∀ j ≥ k, B j=B k := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih => rw [hstep j,hk j hj,repeatPrefix_one,ih]
  apply (B k).finite_toSet.subset
  rintro a ⟨j,hj⟩
  rcases le_total j k with hle|hle
  · exact prefixes_mono P K B hK hstep hle hj
  · simpa only [htail j hle] using hj

include hK hsize hstep in
/-- Padding may be arbitrarily long and the repetition factors may vary
arbitrarily. If every new prefix is made exclusively from full copies of
the preceding one, its increasing union is not a witness. -/
theorem no_nonzero_log_limit
    (hsupp : ∀ k, ∀ a∈B k, a<P k) (c : ℝ) (hc : c≠0) :
    ¬ Tendsto (fun n ↦ (sumRep (chainSet B) n : ℝ)/Real.log n) atTop (𝓝 c) := by
  intro ht
  have hA := witness_infinite hc ht
  obtain ⟨N,hN⟩ := eventually_atTop.mp (eventually_no_full_prefix_copy hc ht)
  obtain ⟨a,ha,haN⟩ := hA.exists_gt N
  obtain ⟨k,hak⟩ := ha
  have hkP : N≤P k := by have := hsupp k a hak; omega
  have htail : ∀ j ≥ k, K j=1 := by
    intro j hj
    have hjP : N≤P j := hkP.trans (periods_mono P K hK hsize hj)
    have hnot := hN (P j) hjP
    have hKj := hK j
    by_contra hne
    exact hnot (copying_stage P K B hK hsize hstep j (by omega))
  exact hA (chainSet_finite_of_eventually_one P K B hK hstep k htail)

end Erdos66RepetitionChain
