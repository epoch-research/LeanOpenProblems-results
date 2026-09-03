import Submission.DoubleExceptionHybrid
import Submission.SharpRawBudget

/-! Combine two existing certificates: raw cost below419/500 and the
prefix saving above2/5. No new numerical table is assumed. -/
namespace Erdos7SharpExceptionBudget
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion Erdos7DoubleExceptionScalar
open Erdos7DoubleExceptionHybrid
set_option maxHeartbeats 4000000

/-- A loss sequence with the certified prefix and raw tail has a uniform bound below 219/500. All exponent caps in the prefix are arbitrary. -/
theorem hybrid_lt_219_500 {n : ℕ} (hn : 94 ≤ n)
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=primes i)
    (L : Fin n → ℚ)
    (hraw : ∀ i, L i ≤ raw p i)
    (hearly : ∀ i, i.val<94 → L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (5/4) (E j))
        (fun x => Erdos7Distortion.residual (5/4) (1/(p i-1 : ℚ)*x)) i.val 1) :
    (∑ i, L i) < 219/500 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => i.val<94)
  have hfront : (∑ i ∈ S, L i) ≤ (states 0).eval 1 := by
    rw [sum_prefix hn]
    apply le_trans (Finset.sum_le_sum (fun i _ => hearly (Fin.castLE hn i) i.isLt))
    have he (i : Fin 94) :
        exponentEnvelope E (fun j => powerTail (p j) (5/4) (E j))
          (fun x => Erdos7Distortion.residual (5/4) (1/(p (Fin.castLE hn i)-1 : ℚ)*x)) i.val 1 =
        exponentEnvelope (fun i => E (Fin.castLE hn i))
          (tails (fun i => E (Fin.castLE hn i)))
          (fun x => Erdos7Distortion.residual (5/4) (1/(primes i-1 : ℚ)*x)) i.val 1 := by
      rw [envelope_prefix hn E _ _ i.val i.isLt.le,hpre]
      congr 1
      funext j g
      dsimp only [tails]
      rw [hpre]
    change (∑ i : Fin 94, exponentEnvelope E (fun j => powerTail (p j) (5/4) (E j))
      (fun x => Erdos7Distortion.residual (5/4) (1/(p (Fin.castLE hn i)-1 : ℚ)*x)) i.val 1) ≤ _
    simp_rw [he]
    exact prefix_cost_bound _
  have hrawfront : (∑ i ∈ S, raw p i) =
      Erdos7No23Sieve.budgetCost (Finset.univ.image primes) := by
    rw [sum_prefix hn]
    simp_rw [raw_prefix hn p hpre]
    rw [sum_raw,Erdos7No23Sieve.secondMomentCost_eq_budgetCost primes certified_prefix_mono]
  have htotal : (∑ i, raw p i) < 419/500 := by
    rw [sum_raw,Erdos7No23Sieve.secondMomentCost_eq_budgetCost p hmono]
    apply Erdos7SharpRawBudget.budgetCost_lt_419_500
    intro q hq
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
    exact hp i
  have hrest : (∑ i ∈ Sᶜ, L i) ≤ ∑ i ∈ Sᶜ, raw p i :=
    Finset.sum_le_sum (fun i _ => hraw i)
  have hsplit := Finset.sum_add_sum_compl S L
  have hsplitraw := Finset.sum_add_sum_compl S (raw p)
  have hsave := saving_certificate
  rw [← hrawfront] at hsave
  linarith

#print axioms hybrid_lt_219_500
end Erdos7SharpExceptionBudget
