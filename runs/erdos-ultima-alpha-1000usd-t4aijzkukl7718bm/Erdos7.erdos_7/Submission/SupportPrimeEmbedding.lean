import Submission.SupportScheduledBudget
import Submission.SupportPrimeMetadata

/-! Padding arbitrary finite odd prime supports into the auxiliary support
sieve. This file does not assert noncoverage without the budget certificate. -/
namespace Erdos7SupportPrimeEmbedding
open scoped BigOperators
open Erdos7SupportPrefixMetadata Erdos7SupportPrimeMetadata Erdos7SupportNumericLink
open Erdos7SupportScheduledBudget
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 200000

lemma prefix_strictMono : StrictMono (fun i : Fin 167 => p i) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  have h := prefix_gaps i
  change p i.val < p (i.val+1)
  omega

noncomputable def candidate (T : Finset ℕ) (i : Fin (167+T.card)) : ℕ :=
  if hi : i.val < 167 then p i else T.orderEmbOfFin rfl ⟨i.val-167,by omega⟩

lemma candidate_small (T : Finset ℕ) (i : Fin (167+T.card)) (hi : i.val < 167) :
    candidate T i=p i := by simp only [candidate,dif_pos hi]

lemma candidate_tail_mem (T : Finset ℕ) (i : Fin (167+T.card)) (hi : 167 ≤ i.val) : candidate T i ∈ T := by
  simp only [candidate,dif_neg (Nat.not_lt.mpr hi)]
  exact T.orderEmbOfFin_mem rfl _

lemma candidate_strictMono (T : Finset ℕ) (hT : ∀ q ∈ T,1000 < q) : StrictMono (candidate T) := by
  intro i j hij
  have hij' : i.val < j.val := hij
  by_cases hi : i.val < 167
  · by_cases hj : j.val < 167
    · rw [candidate_small T i hi,candidate_small T j hj]
      exact prefix_strictMono (show (⟨i.val,hi⟩:Fin 167) < ⟨j.val,hj⟩ from hij')
    · rw [candidate_small T i hi]
      exact (prefix_primes ⟨i.val,hi⟩).2.trans (hT _ (candidate_tail_mem T j (by omega)))
  · have hj : ¬ j.val < 167 := by omega
    simp only [candidate,dif_neg hi,dif_neg hj]
    exact (T.orderEmbOfFin rfl).strictMono (by change i.val-167 < j.val-167; omega)

lemma candidate_prime (T : Finset ℕ) (hT : ∀ q ∈ T,q.Prime ∧ 1000 < q)
    (i : Fin (167+T.card)) : (candidate T i).Prime ∧ 3 ≤ candidate T i := by
  by_cases hi : i.val < 167
  · rw [candidate_small T i hi]
    exact ⟨(prefix_primes ⟨i.val,hi⟩).1,(Erdos7SupportPrefixMetadata.cap_bounds ⟨i.val,hi⟩).2.2⟩
  · have h := hT _ (candidate_tail_mem T i (by omega))
    exact ⟨h.1,by omega⟩

lemma candidate_tail_covers (T : Finset ℕ) (q : ℕ) (hq : q ∈ T) :
    ∃ i : Fin (167+T.card),candidate T i=q := by
  let j : Fin T.card := (T.orderIsoOfFin rfl).symm ⟨q,hq⟩
  let i : Fin (167+T.card) := ⟨167+j.val,by have := j.isLt; omega⟩
  refine ⟨i,?_⟩
  have hi : ¬ i.val < 167 := by dsimp [i]; omega
  simp only [candidate,dif_neg hi]
  have hj : (⟨i.val-167,by have := i.isLt; omega⟩:Fin T.card)=j := by
    apply Fin.ext
    simp only [i,Nat.add_sub_cancel_left]
  rw [hj]
  exact congrArg Subtype.val ((T.orderIsoOfFin rfl).apply_symm_apply ⟨q,hq⟩)

lemma candidate_covers (T : Finset ℕ) (q : ℕ) (hq : q.Prime) (hq0 : 3 ≤ q)
    (hqT : 1000 < q → q ∈ T) : ∃ i : Fin (167+T.card),candidate T i=q := by
  by_cases hs : q ≤ 1000
  · obtain ⟨j,hj⟩ := prefix_covers ⟨q,by omega⟩ hq (by change q≠2; omega)
    let i : Fin (167+T.card) := ⟨j.val,by have := j.isLt; omega⟩
    exact ⟨i,by simpa only [candidate_small T i j.isLt] using hj⟩
  · exact candidate_tail_covers T q (hqT (by omega))

noncomputable def primeSeq (T : Finset ℕ) (i : ℕ) : ℕ :=
  if hi : i < 167+T.card then candidate T ⟨i,hi⟩ else T.sup id+1001

def capSeq (i : ℕ) : ℚ := if i < 167 then cap i else 5/4

lemma primeSeq_at (T : Finset ℕ) (i : Fin (167+T.card)) : primeSeq T i=candidate T i := by
  simp only [primeSeq,dif_pos i.isLt]

lemma odd_prime_gap {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp0 : 3 ≤ p) (hpq : p < q) : p+2 ≤ q := by
  obtain ⟨a,ha⟩ := hp.odd_of_ne_two (by omega)
  obtain ⟨b,hb⟩ := hq.odd_of_ne_two (by omega)
  omega

lemma primeSeq_tail_large (T : Finset ℕ) (hT : ∀ q ∈ T,1000 < q) (i : ℕ) (hi : 167 ≤ i) :
    1001 ≤ primeSeq T i := by
  by_cases hn : i < 167+T.card
  · have h := hT _ (candidate_tail_mem T ⟨i,hn⟩ hi)
    simpa only [primeSeq,dif_pos hn] using (show 1001 ≤ candidate T ⟨i,hn⟩ by omega)
  · simp only [primeSeq,dif_neg hn]
    omega

lemma primeSeq_tail_gap (T : Finset ℕ) (hT : ∀ q ∈ T,q.Prime ∧ 1000 < q)
    (i : ℕ) (hi : 167 ≤ i) (hn : i < 167+T.card) : primeSeq T i+2 ≤ primeSeq T (i+1) := by
  by_cases hn' : i+1 < 167+T.card
  · have h₁ := candidate_prime T hT ⟨i,hn⟩
    have h₂ := candidate_prime T hT ⟨i+1,hn'⟩
    have hmono := candidate_strictMono T (fun q hq => (hT q hq).2)
      (show (⟨i,hn⟩:Fin (167+T.card)) < ⟨i+1,hn'⟩ by simp)
    simpa only [primeSeq,dif_pos hn,dif_pos hn'] using odd_prime_gap h₁.1 h₂.1 h₁.2 hmono
  · have hm := candidate_tail_mem T ⟨i,hn⟩ hi
    have hb : candidate T ⟨i,hn⟩ ≤ T.sup id := Finset.le_sup (f := id) hm
    simp only [primeSeq,dif_pos hn,dif_neg hn']
    omega

/-- A finite exponent profile can always be padded beyond the retained depth.
Only the prime-prefix and tail spacing requirements matter to the schedule. -/
theorem padded_schedule (T : Finset ℕ) (hT : ∀ q ∈ T,q.Prime ∧ 1000 < q)
    (E : ℕ → ℕ) (hE : ∀ i : Fin 167,12 < E i) :
    Schedule (167+T.card) (primeSeq T) E capSeq := by
  refine ⟨by omega,?_,?_,hE,?_,?_,?_,?_⟩
  · intro i
    have hi : i.val < 167+T.card := lt_of_lt_of_le i.isLt (by omega)
    simp only [primeSeq,dif_pos hi,candidate,dif_pos i.isLt]
  · intro i
    exact if_pos i.isLt
  · intro i hi
    have hp := candidate_prime T hT ⟨i,hi⟩
    have he : primeSeq T i=candidate T ⟨i,hi⟩ := primeSeq_at T ⟨i,hi⟩
    refine ⟨by rw [he]; omega,?_⟩
    by_cases hs : i < 167
    · have hc := cap_rat_bounds ⟨i,hs⟩
      have hseq : primeSeq T i=p i := by rw [he,candidate_small T ⟨i,hi⟩ hs]
      simpa only [capSeq,if_pos hs,hseq] using hc
    · have hpQ : (3:ℚ) ≤ primeSeq T i := by rw [he]; exact_mod_cast hp.2
      simp only [capSeq,if_neg hs]
      constructor <;> linarith
  · intro i hi _
    exact primeSeq_tail_large T (fun q hq => (hT q hq).2) i hi
  · intro i hi hn
    exact primeSeq_tail_gap T hT i hi hn
  · intro i hi _
    exact if_neg (by omega)

#print axioms candidate_covers
#print axioms padded_schedule
end Erdos7SupportPrimeEmbedding
