import Submission.SharpDirectFiveScalar
import Submission.NoFiveRawPrefix
import Submission.SharpRawBudget
import Submission.DoubleExceptionHybrid

/-! A uniform loss bound with control 20/11 at five and 5/4 at every later prime. -/
namespace Erdos7SharpDirectFiveHybrid
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion Erdos7SharpDirectFiveScalar
open Erdos7DoubleExceptionHybrid (sum_prefix prod_prefix envelope_prefix raw sum_raw)
set_option maxHeartbeats 10000000
set_option maxRecDepth 200000
set_option Elab.async false

lemma prefix_set : Finset.univ.image primes =
    {5} ∪ Erdos7NoFiveRawPrefix.primes.toFinset := by
  decide +kernel

lemma raw_prefix_lower : (3213/4000 : ℚ) <
    Erdos7No23Sieve.budgetCost (Finset.univ.image primes) := by
  have hT (p : ℕ) (hp : p∈Erdos7NoFiveRawPrefix.primes.toFinset) : 7 ≤ p := by
    have hh := (List.mem_filter.mp (List.mem_toFinset.mp hp)).2
    have hh' := Bool.and_eq_true_iff.mp hh
    exact of_decide_eq_true hh'.1
  rw [prefix_set,Erdos7No23Sieve.budgetCost_union (by
    intro a ha b hb
    rw [Finset.mem_singleton.mp ha]
    have := hT b hb
    omega),Erdos7No23Sieve.budgetCost_singleton,Erdos7No23Sieve.budgetProduct_singleton]
  norm_num [Erdos7No23Sieve.charge,Erdos7No23Sieve.multiplier]
  linarith [Erdos7NoFiveRawPrefix.budget_lower]

lemma raw_prefix {n : ℕ} (hn : 366 ≤ n) (p : Fin n → ℕ)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=primes i) (i : Fin 366) :
    raw p (Fin.castLE hn i)=raw primes i := by
  unfold raw
  rw [hpre]
  congr 1
  have hset : (Finset.univ.filter (fun j : Fin n => j < Fin.castLE hn i)) =
      Finset.univ.filter (fun j : Fin n => j.val < i.val) := rfl
  have hset' : (Finset.univ.filter (fun j : Fin 366 => j < i)) =
      Finset.univ.filter (fun j : Fin 366 => j.val < i.val) := rfl
  rw [hset,hset',prod_prefix (show i.val ≤ n by omega),prod_prefix i.isLt.le]
  apply Finset.prod_congr rfl
  intro j hj
  have he : (Fin.castLE (show i.val ≤ n by omega) j) =
      Fin.castLE hn (Fin.castLE i.isLt.le j) := rfl
  rw [he,hpre]

theorem hybrid_lt_nine_twentieths {n : ℕ} (hn : 366 ≤ n)
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=primes i)
    (L : Fin n → ℚ)
    (hraw : ∀ i, 366 ≤ i.val → L i ≤ (912/737 : ℚ)*raw p i)
    (hearly : ∀ i, i.val<366 → L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
        (fun x => Erdos7Distortion.residual (cap (p i)) (1/(p i-1 : ℚ)*x+offset (p i))) i.val 1) :
    (∑ i, L i) < 9/20 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => i.val<366)
  have hfront : (∑ i ∈ S, L i) ≤ (states 0).eval 1 := by
    rw [sum_prefix hn]
    apply le_trans (Finset.sum_le_sum (fun i _ => hearly (Fin.castLE hn i) i.isLt))
    have he (i : Fin 366) :
        exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
          (fun x => Erdos7Distortion.residual (cap (p (Fin.castLE hn i))) (1/(p (Fin.castLE hn i)-1 : ℚ)*x+offset (p (Fin.castLE hn i)))) i.val 1 =
        exponentEnvelope (fun i => E (Fin.castLE hn i))
          (tails (fun i => E (Fin.castLE hn i)))
          (fun x => Erdos7Distortion.residual (cap (primes i)) (1/(primes i-1 : ℚ)*x+offset (primes i))) i.val 1 := by
      rw [envelope_prefix hn E _ _ i.val i.isLt.le,hpre]
      congr 1
      funext j g
      dsimp only [tails]
      rw [hpre]
    change (∑ i : Fin 366, exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
      (fun x => Erdos7Distortion.residual (cap (p (Fin.castLE hn i))) (1/(p (Fin.castLE hn i)-1 : ℚ)*x+offset (p (Fin.castLE hn i)))) i.val 1) ≤ _
    simp_rw [he]
    exact prefix_cost_bound _
  have hrawfront : (∑ i ∈ S, raw p i) =
      Erdos7No23Sieve.budgetCost (Finset.univ.image primes) := by
    rw [sum_prefix hn]
    simp_rw [raw_prefix hn p hpre]
    rw [sum_raw,Erdos7No23Sieve.secondMomentCost_eq_budgetCost primes prime_metadata.2]
  have htotal : (∑ i, raw p i) < 419/500 := by
    rw [sum_raw,Erdos7No23Sieve.secondMomentCost_eq_budgetCost p hmono]
    apply Erdos7SharpRawBudget.budgetCost_lt_419_500
    intro q hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    exact hp i
  have hrest : (∑ i ∈ Sᶜ, L i) ≤ (912/737 : ℚ)*(∑ i ∈ Sᶜ, raw p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hh : 366 ≤ i.val := by
      have hh := Finset.mem_compl.mp hi
      simp only [S,Finset.mem_filter,Finset.mem_univ,true_and] at hh
      omega
    exact hraw i hh
  have hsplit := Finset.sum_add_sum_compl S L
  have hsplitraw := Finset.sum_add_sum_compl S (raw p)
  have hlower := raw_prefix_lower
  rw [← hrawfront] at hlower
  have hinit := initial_bound
  nlinarith

#print axioms hybrid_lt_nine_twentieths
end Erdos7SharpDirectFiveHybrid
