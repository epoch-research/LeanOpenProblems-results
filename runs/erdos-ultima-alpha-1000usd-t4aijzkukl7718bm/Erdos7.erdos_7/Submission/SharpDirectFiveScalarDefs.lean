import Submission.SharpDirectFiveRootData
import Submission.NoFiveScalarCertificate
import Submission.NoFiveScalarSoundness

/-! A modified control at five, followed by the already certified no-five suffix. -/
namespace Erdos7SharpDirectFiveScalar
open scoped BigOperators
open Erdos7NoFiveScalar (State)
open Erdos7RationalGeometricBudget Erdos7CompressionSieve Erdos7Distortion
open Erdos7BinarySieve (expect expect_add expect_le)
open Erdos7ExponentLaw
set_option maxHeartbeats 5000000
set_option maxRecDepth 200000
set_option Elab.async false
attribute [local instance] Nat.decidablePrime'

def cap (p : ℕ) : ℚ := if p=5 then 20/11 else 5/4

def offset (p : ℕ) : ℚ := if p=5 then 1/5 else 0

def primes (i : Fin 366) : ℕ := if i.val=0 then 5 else Erdos7NoFiveScalar.primes i

noncomputable def states (i : Fin 367) : State :=
  if i.val=0 then rootState else Erdos7NoFiveScalar.states i

def loss (p x : ℕ) : ℚ := max 0 (cap p*(x/(p-1)+offset p)-(cap p-1))

def Row (p : ℕ) (s t : State) : Prop :=
  s.Good ∧ t.Good ∧
  (∀ x : Fin 502, loss p x.val + budget p (cap p) t.eval t.slope (501/x) x.val ≤ s.eval x.val) ∧
  cap p/(p-1)+(1+cap p/(p-1))*t.slope ≤ s.slope

lemma cap_bounds (p : ℕ) : (5/4 : ℚ) ≤ cap p ∧ cap p ≤ 2 := by
  unfold cap
  split_ifs <;> norm_num

lemma cap_le_prime (p : ℕ) (hp : 5 ≤ p) : cap p ≤ p := by
  have hq : (5 : ℚ) ≤ p := by exact_mod_cast hp
  exact (cap_bounds p).2.trans (by linarith)

lemma prime_metadata : (∀ i : Fin 366, (primes i).Prime ∧ 5 ≤ primes i ∧ primes i ≤ 2503) ∧
    StrictMono primes := by
  constructor
  · decide +kernel
  · apply Fin.strictMono_iff_lt_succ.mpr
    decide +kernel

lemma row_suffix (i : Fin 366) (hi : 1 ≤ i.val) :
    Row (primes i) (states i.castSucc) (states i.succ) := by
  have hp : 7 ≤ Erdos7NoFiveScalar.primes i := by
    have hh := Erdos7NoFiveScalar.certified_prefix_mono.monotone
      (show (1 : Fin 366) ≤ i by exact hi)
    change 7 ≤ Erdos7NoFiveScalar.primes i at hh
    exact hh
  have hp3 : Erdos7NoFiveScalar.primes i ≠ 3 := by omega
  have hp5 : Erdos7NoFiveScalar.primes i ≠ 5 := by omega
  have hh := (Erdos7NoFiveScalar.certificate.1 i).2.2
  have h0 : i.val ≠ 0 := by omega
  have hs0 : i.val+1 ≠ 0 := by omega
  simpa only [Row,loss,primes,states,Fin.val_castSucc,Fin.val_succ,
    if_neg h0,if_neg hs0,
    cap,offset,if_neg hp5,add_zero,mul_div_assoc,Erdos7NoFiveScalar.Row,
    Erdos7NoFiveScalar.loss,Erdos7NoFiveScalar.cap,if_neg hp3] using hh

lemma loss_affine (p x : ℕ) (hp : 5 ≤ p) (hhi : p ≤ 2503) (hx : 501 ≤ x) :
    loss p x=cap p/(p-1)*x-(cap p-1)+cap p*offset p := by
  have hpQ : (5 : ℚ) ≤ p := by exact_mod_cast hp
  have hpQhi : (p : ℚ) ≤ 2503 := by exact_mod_cast hhi
  have hxQ : (501 : ℚ) ≤ x := by exact_mod_cast hx
  have hnon : 0 ≤ cap p*(x/(p-1)+offset p)-(cap p-1) := by
    by_cases h5 : p=5
    · subst p; norm_num [cap,offset]; linarith
    · simp only [cap,offset,if_neg h5,add_zero]
      apply sub_nonneg.mpr
      have hd : (0 : ℚ)<p-1 := by linarith
      have hh : (1/4 : ℚ) ≤ (5/4*x)/(p-1) := by
        apply (le_div_iff₀ hd).mpr
        nlinarith
      convert hh using 1 <;> ring
  unfold loss
  rw [max_eq_right hnon]
  ring

lemma row_budget (p : ℕ) (hp : 5 ≤ p) (hhi : p ≤ 2503)
    (s t : State) (hr : Row p s t) (x : ℕ) :
    loss p x+budget p (cap p) t.eval t.slope (501/x) x ≤ s.eval x := by
  by_cases hx : x<502
  · exact hr.2.2.1 ⟨x,hx⟩
  · have h11 : 501 ≤ x := by omega
    have hpQ : (1 : ℚ)<p := by exact_mod_cast (show 1<p by omega)
    have hrow := hr.2.2.1 (501 : Fin 502)
    change loss p 501+budget p (cap p) t.eval t.slope (501/501) 501 ≤ s.eval 501 at hrow
    rw [loss_affine p 501 hp hhi (by omega),
      budget_affine p (cap p) hpQ t.eval 501 t.slope t.intercept
        (fun x hx => t.eval_affine x hx) (501/501) 501 (by omega),
      s.eval_affine 501 (by omega)] at hrow
    rw [loss_affine p x hp hhi h11,
      budget_affine p (cap p) hpQ t.eval 501 t.slope t.intercept
        (fun x hx => t.eval_affine x hx) (501/x) x h11,
      s.eval_affine x h11]
    have hxQ : (501 : ℚ) ≤ x := by exact_mod_cast h11
    nlinarith [hr.2.2.2]

lemma row_op (i : Fin 366) (hr : Row (primes i) (states i.castSucc) (states i.succ))
    (E x : ℕ) :
    loss (primes i) x + op (primes i) (cap (primes i)) (states i.succ).eval E x ≤
      (states i.castSucc).eval x := by
  obtain ⟨_,hp,hhi⟩ := prime_metadata.1 i
  have hh := row_budget (primes i) hp hhi _ _ hr x
  apply (add_le_add (le_refl (loss (primes i) x)) ?_).trans hh
  by_cases hx : x=0
  · subst x
    rw [op_zero,budget_zero]
  · apply op_le_budget (primes i) (cap (primes i)) (by exact_mod_cast (show 1<primes i by omega))
      (by have := (cap_bounds (primes i)).1; linarith) _ (State.monotone _ hr.2.1) 501 _ _ hr.2.1.1
      (fun x hx => State.eval_affine _ x hx) (501/x) E x
    have ht := Nat.lt_mul_div_succ 501 (show 0<x by omega)
    simpa only [Nat.mul_comm] using ht.le

#print axioms row_op
#print axioms row_suffix
end Erdos7SharpDirectFiveScalar
