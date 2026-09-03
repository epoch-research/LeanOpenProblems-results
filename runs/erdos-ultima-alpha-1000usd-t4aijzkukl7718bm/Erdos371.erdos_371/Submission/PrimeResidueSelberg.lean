import Submission.ProgressionSelberg
import Submission.RoughSelbergBound

/-! A one-prime arithmetic-progression sieve with its modulus factor and
polynomial error retained. -/
namespace Erdos371.FiniteSieve
open Finset

def primeResidueSet (p r L z : ℕ) : Finset ℕ :=
  (range L).filter fun q => q.Prime ∧ z < q ∧ q%p=r

lemma primeResidueSet_selberg_bound (p r L z : ℕ) (hp : p.Prime) (hr : r < p) (hz : 1 ≤ z) :
    ((primeResidueSet p r L z).card : ℝ) ≤
      2*Real.exp 2*L/(p*Real.log (z+1 : ℝ))+2*(p : ℝ)^8*(z+1 : ℝ)^32 := by
  let S := (z+1).primesBelow.erase p
  have hS (q : ℕ) (hq : q ∈ S) : q.Prime ∧ q ≤ z ∧ q ≠ p := by
    obtain ⟨hqp,hq⟩ := mem_erase.mp hq
    obtain ⟨hqz,hq⟩ := Nat.mem_primesBelow.mp hq
    exact ⟨hq,by omega,hqp⟩
  have hcop (q : ℕ) (hq : q ∈ S) : p.Coprime q :=
    (Nat.coprime_primes hp (hS q hq).1).mpr (hS q hq).2.2.symm
  have hpair : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro q hq r hr hqr
    exact (Nat.coprime_primes (hS q hq).1 (hS r hr).1).mpr hqr
  have hZ : (1 : ℝ) < (z+1 : ℝ)^8 :=
    one_lt_pow₀ (by exact_mod_cast (show 1 < z+1 by omega)) (by decide)
  have hlog : 0 < Real.log (z+1 : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega))
  have hm : (∑ q ∈ S, Real.log q*(({0} : Finset ℕ).card : ℝ)/q) ≤
      Real.log ((z+1 : ℝ)^8)/2 := by
    simp only [card_singleton,Nat.cast_one,mul_one,Real.log_pow,Nat.cast_ofNat]
    have he : (∑ q ∈ S, Real.log q/(q : ℝ)) ≤
        ∑ q ∈ (z+1).primesBelow, Real.log q/((q : ℝ)-1) := by
      apply (sum_le_sum ?_).trans
        (sum_le_sum_of_subset_of_nonneg (erase_subset _ _) ?_)
      · intro q hq
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (hS q hq).1.two_le
        exact div_le_div_of_nonneg_left (Real.log_nonneg (by linarith)) (by linarith) (by linarith)
      · intro q hq _
        have hq2 : (2 : ℝ) ≤ q := by exact_mod_cast (Nat.mem_primesBelow.mp hq).2.two_le
        exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    have he' := prime_log_div_pred_sum_le (z+1)
    push_cast at he'
    linarith
  have hh := residue_selberg_progression_bound S (fun _ => ({0} : Finset ℕ)) p r L hp.pos hr
    (notMem_erase p _) hcop (fun q hq => (hS q hq).1.ne_zero) hpair
    (fun q hq => by simpa only [singleton_subset_iff,mem_range] using (hS q hq).1.pos)
    (fun q hq => by simpa only [card_singleton] using And.intro (by decide : 0<1) (hS q hq).1.one_lt)
    ((z+1 : ℝ)^8) hZ hm
  have hcount : (primeResidueSet p r L z).card ≤
      ((range L).filter (fun q => q%p=r ∧ ∀ l ∈ S, q%l ∉ ({0} : Finset ℕ))).card := by
    apply card_le_card
    intro q hq
    obtain ⟨hqL,hq,hzq,hqr⟩ := mem_filter.mp hq
    refine mem_filter.mpr ⟨hqL,hqr,?_⟩
    intro l hl hbad
    have hd : l ∣ q := Nat.dvd_iff_mod_eq_zero.mpr (mem_singleton.mp hbad)
    have he := (hq.dvd_iff_eq (hS l hl).1.ne_one).mp hd
    have := (hS l hl).2.1
    omega
  have hmass : primeHarmonic z-1 ≤ ∑ q ∈ S, (1 : ℝ)/q := by
    have hfull : (∑ q ∈ (z+1).primesBelow, (1 : ℝ)/q)=primeHarmonic z := by
      simp only [primeHarmonic,primeReciprocalSum,Nat.primesBelow]
    by_cases hpS : p ∈ (z+1).primesBelow
    · have he := sum_erase_add (z+1).primesBelow (fun q => (1 : ℝ)/q) hpS
      rw [hfull] at he
      have hp1 : (1 : ℝ)/p ≤ 1 := by
        apply (div_le_one (by exact_mod_cast hp.pos)).mpr
        exact_mod_cast hp.one_le
      dsimp only [S]
      linarith
    · simp only [S,erase_eq_of_notMem hpS,hfull]
      linarith
  have hExp : Real.exp (-(∑ q ∈ S, (1 : ℝ)/q)) ≤ Real.exp 2/Real.log (z+1 : ℝ) := by
    calc
      _ ≤ Real.exp (1-primeHarmonic z) := Real.exp_le_exp.mpr (by linarith)
      _ = Real.exp 1*Real.exp (-primeHarmonic z) := by rw [sub_eq_add_neg,Real.exp_add]
      _ ≤ Real.exp 1*(Real.exp 1/Real.log (z+1 : ℝ)) :=
        mul_le_mul_of_nonneg_left (exp_neg_primeHarmonic_le z hz) (Real.exp_nonneg 1)
      _ = _ := by rw [← mul_div_assoc,← Real.exp_add]; norm_num
  simp only [card_singleton,Nat.cast_one,← pow_mul,Nat.reduceMul] at hh
  apply ((Nat.cast_le (α := ℝ)).mpr hcount).trans
  apply hh.trans
  apply add_le_add _ le_rfl
  have he := mul_le_mul_of_nonneg_left hExp (by positivity : (0 : ℝ) ≤ 2*L/p)
  convert he using 1; ring

/-- Any linear congruence with invertible slope selects just one residue
class. The class need not be chosen uniformly as the parameters vary. -/
lemma prime_linear_congruence_bound (p a b L z : ℕ) (hp : p.Prime)
    (ha : p.Coprime a) (hz : 1 ≤ z) :
    (((range L).filter (fun q => q.Prime ∧ z<q ∧ Nat.ModEq p (a*q) b)).card : ℝ) ≤
      2*Real.exp 2*L/(p*Real.log (z+1 : ℝ))+2*(p : ℝ)^8*(z+1 : ℝ)^32 := by
  let T := (range L).filter (fun q => q.Prime ∧ z<q ∧ Nat.ModEq p (a*q) b)
  by_cases hT : T.Nonempty
  · obtain ⟨q₀,hq₀⟩ := hT
    have hb := (mem_filter.mp hq₀).2.2.2
    have hsub : T ⊆ primeResidueSet p (q₀%p) L z := by
      intro q hq
      obtain ⟨hqL,hq,hzq,hbq⟩ := mem_filter.mp hq
      have he := Nat.ModEq.cancel_left_of_coprime ha (hbq.trans hb.symm)
      exact mem_filter.mpr ⟨hqL,hq,hzq,he⟩
    exact ((Nat.cast_le (α := ℝ)).mpr (card_le_card hsub)).trans
      (primeResidueSet_selberg_bound p (q₀%p) L z hp (Nat.mod_lt _ hp.pos) hz)
  · have he := not_nonempty_iff_eq_empty.mp hT
    change (T.card : ℝ) ≤ _
    rw [he,card_empty,Nat.cast_zero]
    have hlog := Real.log_pos (by exact_mod_cast (show 1 < z+1 by omega) : (1 : ℝ) < z+1)
    positivity

#print axioms primeResidueSet_selberg_bound
#print axioms prime_linear_congruence_bound
end Erdos371.FiniteSieve
