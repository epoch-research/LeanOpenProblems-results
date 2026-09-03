import Submission.FourExceptionHybrid

/-! Padding arbitrary no-three prime supports by the certified mixed-cap prefix. -/
namespace Erdos7FourExceptionPrimes
open scoped BigOperators
open Erdos7FourExceptionScalar
set_option maxHeartbeats 4000000

lemma small_primes_complete (q : ℕ) (hq : q.Prime) (hlo : 5 ≤ q)
    (hhi : q ≤ 2503) : ∃ i : Fin 366, primes i=q := by
  have hmem : q ∈ Finset.univ.image primes := by
    rw [Erdos7FourExceptionHybrid.prefix_set]
    by_cases h3 : q=5
    · simp [h3]
    · have h7 : 7 ≤ q := by
        by_contra h
        have h6 : q ≤ 6 := by omega
        interval_cases q <;> norm_num at *
      apply Finset.mem_union_right
      apply List.mem_toFinset.mpr
      simp only [Erdos7NoFiveRawPrefix.primes,List.mem_filter,List.mem_range,
        Bool.and_eq_true,decide_eq_true_eq]
      exact ⟨by omega,h7,hq⟩
  obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hmem
  exact ⟨i,hi⟩

lemma padded_primes (P : Finset ℕ) (hP : ∀ q∈P, q.Prime ∧ 5 ≤ q) :
    ∃ n, ∃ hn : 366 ≤ n, ∃ p : Fin n → ℕ,
      (∀ i, (p i).Prime ∧ 5 ≤ p i) ∧ StrictMono p ∧
      (∀ i : Fin 366, p (Fin.castLE hn i)=primes i) ∧
      ∀ q∈P, ∃ i, p i=q := by
  classical
  let T := P.filter (fun q => 2503<q)
  let p : Fin (366+T.card) → ℕ := Fin.addCases primes (T.orderEmbOfFin rfl)
  have hp (i : Fin (366+T.card)) : (p i).Prime ∧ 5 ≤ p i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · have hh : (primes i).Prime ∧ 5 ≤ primes i := ⟨(prime_metadata.1 i).1,(prime_metadata.1 i).2.1⟩
      simpa only [p,Fin.addCases_left] using hh
    · have hi : (T.orderEmbOfFin rfl) i ∈ P :=
        (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl i)).1
      simpa only [p,Fin.addCases_right] using hP _ hi
  have hmono : StrictMono p := by
    intro i j hij
    revert hij
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
      refine Fin.addCases (fun j => ?_) (fun j => ?_) j
    · intro hij
      simp only [p,Fin.addCases_left]
      apply prime_metadata.2
      exact hij
    · intro hij
      simp only [p,Fin.addCases_left,Fin.addCases_right]
      have hl := (prime_metadata.1 i).2.2
      have hr := (Finset.mem_filter.mp (T.orderEmbOfFin_mem rfl j)).2
      omega
    · intro hij
      have hh := i.isLt
      have hj := j.isLt
      change 366+i.val < j.val at hij
      omega
    · intro hij
      simp only [p,Fin.addCases_right]
      apply (T.orderEmbOfFin rfl).strictMono
      change i.val < j.val
      change 366+i.val < 366+j.val at hij
      omega
  refine ⟨366+T.card,by omega,p,hp,hmono,?_,?_⟩
  · intro i
    change p (Fin.castAdd T.card i)=primes i
    exact Fin.addCases_left i
  · intro q hq
    by_cases hq2503 : q≤2503
    · obtain ⟨i,hi⟩ := small_primes_complete q (hP q hq).1 (hP q hq).2 hq2503
      exact ⟨Fin.castAdd T.card i,by simpa only [p,Fin.addCases_left] using hi⟩
    · have hqT : q∈T := Finset.mem_filter.mpr ⟨hq,by omega⟩
      obtain ⟨i,hi⟩ := (T.orderIsoOfFin rfl).surjective ⟨q,hqT⟩
      refine ⟨Fin.natAdd 366 i,?_⟩
      simpa only [p,Fin.addCases_right] using congrArg Subtype.val hi

#print axioms padded_primes
end Erdos7FourExceptionPrimes
