import Submission.NoFiveScalarSoundness
import Submission.NoFiveSaving
import Submission.DoubleExceptionHybrid

/-! Combining the mixed-cap hinge prefix with the uniform raw tail. -/
namespace Erdos7NoFiveHybrid
open scoped BigOperators
open Erdos7CompressionSieve Erdos7Distortion Erdos7NoFiveScalar Erdos7NoFiveRaw
open Erdos7DoubleExceptionHybrid (sum_prefix prod_prefix envelope_prefix)
set_option maxHeartbeats 6000000

lemma certified_prefix_mono : StrictMono primes := by
  apply Fin.strictMono_iff_lt_succ.mpr
  decide +kernel

variable (hcert :
    (∀ i : Fin 366, 3 ≤ primes i ∧ primes i ≤ 2503 ∧
      Row (primes i) (states i.castSucc) (states i.succ)) ∧
    (∀ x : Fin 501, (states 366).values x=0) ∧
    (states 366).slope=0 ∧ (states 366).intercept=0)

lemma raw_prefix {n : ℕ} (hn : 366 ≤ n) (p : Fin n → ℕ)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=primes i) (i : Fin 366) :
    raw p (Fin.castLE hn i)=raw primes i := by
  unfold Erdos7NoFiveRaw.raw
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

include hcert in
theorem hybrid_lt_one {n : ℕ} (hn : 366 ≤ n)
    (p E : Fin n → ℕ) (hp : ∀ i, (p i).Prime ∧ 3 ≤ p i ∧ p i ≠ 5) (hmono : StrictMono p)
    (hpre : ∀ i : Fin 366, p (Fin.castLE hn i)=primes i)
    (L : Fin n → ℚ)
    (hraw : ∀ i, L i ≤ raw p i)
    (hearly : ∀ i, i.val<366 → L i ≤
      exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
        (fun x => Erdos7Distortion.residual (cap (p i)) (1/(p i-1 : ℚ)*x)) i.val 1) :
    (∑ i, L i) < 1 := by
  classical
  let S := Finset.univ.filter (fun i : Fin n => i.val<366)
  have hfront : (∑ i ∈ S, L i) ≤ (states 0).eval 1 := by
    rw [sum_prefix hn]
    apply le_trans (Finset.sum_le_sum (fun i _ => hearly (Fin.castLE hn i) i.isLt))
    have he (i : Fin 366) :
        exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
          (fun x => Erdos7Distortion.residual (cap (p (Fin.castLE hn i))) (1/(p (Fin.castLE hn i)-1 : ℚ)*x)) i.val 1 =
        exponentEnvelope (fun i => E (Fin.castLE hn i))
          (tails (fun i => E (Fin.castLE hn i)))
          (fun x => Erdos7Distortion.residual (cap (primes i)) (1/(primes i-1 : ℚ)*x)) i.val 1 := by
      rw [envelope_prefix hn E _ _ i.val i.isLt.le,hpre]
      congr 1
      funext j g
      dsimp only [tails]
      rw [hpre]
    change (∑ i : Fin 366, exponentEnvelope E (fun j => powerTail (p j) (cap (p j)) (E j))
      (fun x => Erdos7Distortion.residual (cap (p (Fin.castLE hn i))) (1/(p (Fin.castLE hn i)-1 : ℚ)*x)) i.val 1) ≤ _
    simp_rw [he]
    exact prefix_cost_bound_of_certificate hcert _
  have hrawfront : (∑ i ∈ S, raw p i) =
      costC (Finset.univ.image primes) := by
    rw [sum_prefix hn]
    simp_rw [raw_prefix hn p hpre]
    rw [sum_raw,Erdos7NoFiveRaw.secondMomentCost_eq primes certified_prefix_mono]
  have htotal : (∑ i, raw p i) < (27041/13400 : ℚ) := by
    rw [sum_raw,Erdos7NoFiveRaw.secondMomentCost_eq p hmono]
    apply costC_lt_bound
    · refine Finset.mem_image.mpr ⟨Fin.castLE hn (0 : Fin 366),Finset.mem_univ _,?_⟩
      rw [hpre]
      rfl
    · intro q hq
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hq
      exact hp i
  have hrest : (∑ i ∈ Sᶜ, L i) ≤ ∑ i ∈ Sᶜ, raw p i :=
    Finset.sum_le_sum (fun i _ => hraw i)
  have hsplit := Finset.sum_add_sum_compl S L
  have hsplitraw := Finset.sum_add_sum_compl S (raw p)
  have hsave := Erdos7NoFiveSaving.saving_certificate
  rw [← hrawfront] at hsave
  linarith


#print axioms hybrid_lt_one
end Erdos7NoFiveHybrid
