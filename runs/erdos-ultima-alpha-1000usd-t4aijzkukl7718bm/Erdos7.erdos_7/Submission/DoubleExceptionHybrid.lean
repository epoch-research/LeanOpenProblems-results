import Submission.DoubleExceptionScalar
import Submission.NoThreeRawBudget

/-!
# Combining the certified hinge prefix with the old second-moment tail

This is a scalar hybrid criterion; applying it to an arithmetic near-cover
requires separate layer and exceptional-mass bounds.
-/
namespace Erdos7DoubleExceptionHybrid
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion Erdos7DoubleExceptionScalar
set_option maxHeartbeats 4000000

lemma sum_prefix {n k : ℕ} (hkn : k ≤ n) (f : Fin n → ℚ) :
    (∑ i ∈ Finset.univ.filter (fun i : Fin n => i.val<k), f i) =
      ∑ i : Fin k, f (Fin.castLE hkn i) := by
  classical
  apply Finset.sum_bij (fun i hi => (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin k))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij; exact Fin.ext (congrArg (fun z : Fin k => z.val) hij)
  · intro j hj
    refine ⟨Fin.castLE hkn j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.isLt⟩,?_⟩
    rfl
  · intro i hi; rfl

lemma prod_prefix {n k : ℕ} (hkn : k ≤ n) (f : Fin n → ℚ) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin n => i.val<k), f i) =
      ∏ i : Fin k, f (Fin.castLE hkn i) := by
  classical
  apply Finset.prod_bij (fun i hi => (⟨i.val,(Finset.mem_filter.mp hi).2⟩ : Fin k))
  · intro i hi; exact Finset.mem_univ _
  · intro i hi j hj hij; exact Fin.ext (congrArg (fun z : Fin k => z.val) hij)
  · intro j hj
    refine ⟨Fin.castLE hkn j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,j.isLt⟩,?_⟩
    rfl
  · intro i hi; rfl

lemma envelope_prefix {n k : ℕ} (hkn : k ≤ n)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ) (φ : ℚ → ℚ)
    (t : ℕ) (ht : t ≤ k) (M : ℕ) :
    exponentEnvelope E q φ t M =
      exponentEnvelope (fun i => E (Fin.castLE hkn i))
        (fun i => q (Fin.castLE hkn i)) φ t M := by
  induction t generalizing M with
  | zero => rfl
  | succ t ih =>
    have htk : t<k := by omega
    have htn : t<n := by omega
    simp only [exponentEnvelope,htk,htn,dif_pos]
    rw [ih (by omega)]
    congr 1
    apply Finset.sum_congr rfl
    intro g hg
    rw [ih (by omega)]
    rfl

/-- The old scalar raw charge at a stage. -/
def raw {n : ℕ} (p : Fin n → ℕ) (i : Fin n) : ℚ :=
  Erdos7No23Sieve.charge (p i) *
    ∏ j ∈ Finset.univ.filter (fun j => j < i), Erdos7No23Sieve.multiplier (p j)

lemma sum_raw {n : ℕ} (p : Fin n → ℕ) :
    (∑ i, raw p i) = secondMomentCost p (fun _ => 5/4) := by
  unfold raw secondMomentCost Erdos7No23Sieve.charge Erdos7No23Sieve.multiplier
  norm_num
  apply Finset.sum_congr rfl
  intro i hi
  ring

lemma raw_prefix {n : ℕ} (hn : 94 ≤ n) (p : Fin n → ℕ)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=primes i) (i : Fin 94) :
    raw p (Fin.castLE hn i)=raw primes i := by
  unfold raw
  rw [hpre]
  congr 1
  have hset : (Finset.univ.filter (fun j : Fin n => j < Fin.castLE hn i)) =
      Finset.univ.filter (fun j : Fin n => j.val < i.val) := rfl
  have hset' : (Finset.univ.filter (fun j : Fin 94 => j < i)) =
      Finset.univ.filter (fun j : Fin 94 => j.val < i.val) := rfl
  rw [hset,hset',prod_prefix (show i.val ≤ n by omega),prod_prefix i.isLt.le]
  apply Finset.prod_congr rfl
  intro j hj
  have he : (Fin.castLE (show i.val ≤ n by omega) j) =
      Fin.castLE hn (Fin.castLE i.isLt.le j) := rfl
  rw [he,hpre]

lemma certified_prefix_mono : StrictMono primes := by
  decide +kernel

/-- A loss sequence with the certified prefix and raw tail cannot reach
one half. All exponent caps in the prefix are arbitrary. -/
theorem hybrid_lt_one_half {n : ℕ} (hn : 94 ≤ n)
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 5 ≤ p i) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 94, p (Fin.castLE hn i)=primes i)
    (L : Fin n → ℚ)
    (hraw : ∀ i, L i ≤ raw p i)
    (hearly : ∀ i, i.val<94 → L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (5/4) (E j))
        (fun x => Erdos7Distortion.residual (5/4) (1/(p i-1 : ℚ)*x)) i.val 1) :
    (∑ i, L i) < 1/2 := by
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
  have htotal : (∑ i, raw p i) < 9/10 := by
    rw [sum_raw,Erdos7No23Sieve.secondMomentCost_eq_budgetCost p hmono]
    apply Erdos7NoThreeRawBudget.budgetCost_lt_nine_tenths
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

#print axioms envelope_prefix
#print axioms raw_prefix
#print axioms hybrid_lt_one_half
end Erdos7DoubleExceptionHybrid
