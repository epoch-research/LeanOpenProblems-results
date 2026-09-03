import FormalConjecturesUtil
import Submission.ProductTransportFibers
import Submission.OffDiagonalEnergy
import Submission.LogarithmicSmoothCommutator

/-! Nonpositive same-winner correlations in a large-gcd/short-gap region.
The signed correlations in the complementary region are not estimated. -/

namespace Erdos371GcdCorrelation

open Finset Erdos371PrimeDiscrepancy Erdos371ProductSignTransport
open Erdos371ProductTransportFibers Erdos371OffDiagonalEnergy

lemma lower_lt_of_same_winner {n m : ℕ} (hn : 1<n) (hnm : n < m)
    (hw : winner n=winner m) : lower n<lower m := by
  have ha := lower_bounds n
  have hb := lower_bounds m
  have hne : lower n≠lower m := fun h => Nat.ne_of_lt hnm
    (lower_injective_fixed_winner hn (by omega) rfl hw.symm h)
  omega

lemma winner_coprime_lower {n : ℕ} (hn : 0<n) : (winner n).Coprime (lower n) := by
  apply (winner_prime hn).coprime_iff_not_dvd.mpr
  intro h
  have hx := lower_bounds n
  exact (not_le.mpr (lower_prime_lt n))
    (Nat.le_maxPrimeFac (by omega) (winner_prime hn) h)

lemma same_sign_gap_divisible {n m : ℕ} (hn : 1<n) (hnm : n < m)
    (hw : winner n=winner m) (hs : sign n=sign m) :
    winner n*Nat.gcd (lower n) (lower m) ∣ lower m-lower n := by
  have hlt := lower_lt_of_same_winner hn hnm hw
  have hp : winner n∣lower m-lower n := by
    apply (CharP.cast_eq_zero_iff (ZMod (winner n)) (winner n) _).mp
    rw [Nat.cast_sub hlt.le,lower_residue m (winner n) hw.symm,
      lower_residue n (winner n) rfl,hs,sub_self]
  have hc : (winner n).Coprime (Nat.gcd (lower n) (lower m)) :=
    (winner_coprime_lower (by omega : 0<n)).of_dvd_right (Nat.gcd_dvd_left _ _)
  exact hc.mul_dvd_of_dvd_of_dvd hp
    (Nat.dvd_sub (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))

/-- Positive off-diagonal correlations can occur only beyond this gcd-scaled
separation. This uses actual winning primes, not a model height function. -/
theorem same_sign_gap_bound {n m : ℕ} (hn : 1<n) (hnm : n < m)
    (hw : winner n=winner m) (hs : sign n=sign m) :
    winner n*Nat.gcd (lower n) (lower m) ≤ lower m-lower n :=
  Nat.le_of_dvd (Nat.sub_pos_of_lt (lower_lt_of_same_winner hn hnm hw))
    (same_sign_gap_divisible hn hnm hw hs)

def close (n m : ℕ) : Prop :=
  1<n ∧ n < m ∧ winner n=winner m ∧
    lower m-lower n < winner n*Nat.gcd (lower n) (lower m)

instance (n m : ℕ) : Decidable (close n m) := inferInstanceAs (Decidable (_ ∧ _))

lemma close_signs_opposite {n m : ℕ} (h : close n m) : sign n≠sign m :=
  fun hs => (not_le.mpr h.2.2.2) (same_sign_gap_bound h.1 h.2.1 h.2.2.1 hs)

lemma close_correlation {n m : ℕ} (h : close n m) : correlation n m = -1 := by
  rw [correlation,if_pos ⟨by have := h.1; omega,by have := h.2.1; omega,h.2.2.1⟩,
    sign_product,if_neg (close_signs_opposite h)]

def closeRow (n N : ℕ) : Finset ℕ := (range N).filter (close n)

def closeCount (N : ℕ) : ℕ := ∑ n ∈ range N, (closeRow n N).card

noncomputable def closeSum (N : ℕ) : ℝ :=
  ∑ n ∈ range N, ∑ m ∈ closeRow n N, correlation n m

lemma closeSum_eq (N : ℕ) : closeSum N=-(closeCount N:ℝ) := by
  unfold closeSum closeCount
  push_cast
  rw [← sum_neg_distrib]
  apply sum_congr rfl
  intro n hn
  calc
    _ = ∑ _m ∈ closeRow n N, (-1:ℝ) := sum_congr rfl
      (fun m hm => close_correlation (mem_filter.mp hm).2)
    _ = _ := by simp

lemma closeSum_nonpos (N : ℕ) : closeSum N≤0 := by
  rw [closeSum_eq]
  exact neg_nonpos.mpr (Nat.cast_nonneg _)

lemma close_gcd_injective {n m k : ℕ} (hm : close n m) (hk : close n k)
    (hg : Nat.gcd (lower n) (lower m)=Nat.gcd (lower n) (lower k)) : m = k := by
  have hn := hm.1
  have hnm := hm.2.1
  have hnk := hk.2.1
  have hs : sign m = sign k := by
    have h1 := close_signs_opposite hm
    have h2 := close_signs_opposite hk
    unfold sign at *
    split_ifs at * <;> omega
  have hw : winner m = winner k := hm.2.2.1.symm.trans hk.2.2.1
  have hltm := lower_lt_of_same_winner hm.1 hm.2.1 hm.2.2.1
  have hltk := lower_lt_of_same_winner hk.1 hk.2.1 hk.2.2.1
  have hdiv : Nat.gcd (lower n) (lower m)∣Nat.gcd (lower m) (lower k) := by
    apply Nat.dvd_gcd (Nat.gcd_dvd_right _ _)
    rw [hg]
    exact Nat.gcd_dvd_right _ _
  have hdle : Nat.gcd (lower n) (lower m)≤Nat.gcd (lower m) (lower k) :=
    Nat.le_of_dvd (Nat.gcd_pos_of_pos_left _ (by omega)) hdiv
  rcases lt_trichotomy m k with hmk | he | hkm
  · have hb := same_sign_gap_bound (by omega) hmk hw hs
    have hc := Nat.mul_le_mul_left (winner m) hdle
    rw [← hm.2.2.1] at hb hc
    have hh := hk.2.2.2
    rw [← hg] at hh
    omega
  · exact he
  · have hb := same_sign_gap_bound (by omega) hkm hw.symm hs.symm
    rw [Nat.gcd_comm (lower k) (lower m),← hk.2.2.1] at hb
    have hc := Nat.mul_le_mul_left (winner n) hdle
    have hh := hm.2.2.2
    omega

/-- For each earlier comparison, the negative region contains at most one
later comparison for each divisor of its losing endpoint. -/
theorem closeRow_card_le (n N : ℕ) : (closeRow n N).card≤(lower n).divisors.card := by
  apply card_le_card_of_injOn (fun m => Nat.gcd (lower n) (lower m))
  · intro m hm
    have hh := (mem_filter.mp (show m ∈ (range N).filter (close n) from hm)).2
    have hl := lower_bounds n
    exact Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left _ _,by have := hh.1; omega⟩
  · intro m hm k hk hg
    exact close_gcd_injective (mem_filter.mp (show m ∈ (range N).filter (close n) from hm)).2
      (mem_filter.mp (show k ∈ (range N).filter (close n) from hk)).2 hg

theorem closeCount_le_divisor_sum (N : ℕ) :
    closeCount N≤∑ n ∈ range N, (lower n).divisors.card :=
  sum_le_sum (fun n _ => closeRow_card_le n N)

lemma divisor_sum_eq (N : ℕ) :
    (∑ n ∈ Icc 1 N, n.divisors.card)=∑ d ∈ Icc 1 N, N/d := by
  simpa using Erdos371LogarithmicSmoothCommutator.sum_divisors_reindex N
    (fun _ _ => (1:ℕ))

lemma shifted_divisor_sum (N : ℕ) :
    (∑ n ∈ range N, (n+1).divisors.card)=∑ n ∈ Icc 1 N, n.divisors.card := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ,sum_Icc_succ_top (by omega),ih]

lemma lower_divisor_sum_le (N : ℕ) :
    (∑ n ∈ range N, (lower n).divisors.card)≤2*∑ n ∈ Icc 1 N, n.divisors.card := by
  have hpt (n : ℕ) : (lower n).divisors.card≤n.divisors.card+(n+1).divisors.card := by
    unfold lower
    split_ifs <;> omega
  have hh : (∑ n ∈ range N, n.divisors.card)+N.divisors.card=
      ∑ n ∈ range N, (n+1).divisors.card := by
    rw [← sum_range_succ,sum_range_succ']
    simp
  have h := sum_le_sum (fun n (_ : n∈range N) => hpt n)
  rw [sum_add_distrib,shifted_divisor_sum] at h
  rw [shifted_divisor_sum] at hh
  omega

lemma divisor_sum_bound (N : ℕ) :
    ((∑ n ∈ Icc 1 N, n.divisors.card : ℕ):ℝ)≤N*(1+Real.log (N:ℝ)) := by
  have hh : (∑ d ∈ Icc 1 N, 1/(d:ℝ))=(harmonic N:ℝ) := by
    rw [harmonic_eq_sum_Icc]
    push_cast
    simp only [one_div]
  rw [divisor_sum_eq,Nat.cast_sum]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, (N:ℝ)/d := sum_le_sum (fun d _ => Nat.cast_div_le)
    _ = (N:ℝ)*(harmonic N:ℝ) := by rw [← hh,mul_sum]; apply sum_congr rfl; intro d hd; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_le_one_add_log N) (Nat.cast_nonneg N)

/-- This rigorously negative part is at most divisor-summatory sized. Thus
isolating it leaves all potentially superlinear cancellations in the
complementary pair region. -/
theorem closeCount_bound (N : ℕ) :
    (closeCount N:ℝ)≤2*N*(1+Real.log (N:ℝ)) := by
  have h := (closeCount_le_divisor_sum N).trans (lower_divisor_sum_le N)
  have hc : (closeCount N:ℝ)≤2*((∑ n ∈ Icc 1 N, n.divisors.card : ℕ):ℝ) := by exact_mod_cast h
  nlinarith [divisor_sum_bound N]

noncomputable def farSum (N : ℕ) : ℝ :=
  ∑ m ∈ range N, ∑ n ∈ range m, if close n m then 0 else correlation n m

lemma closeSum_eq_triangle (N : ℕ) : closeSum N=
    ∑ m ∈ range N, ∑ n ∈ range m, if close n m then correlation n m else 0 := by
  unfold closeSum closeRow
  simp only [sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro m hm
  symm
  apply sum_subset (range_mono (mem_range.mp hm).le)
  intro n hn hnm
  have hnm' : ¬n < m := by simpa only [mem_range] using hnm
  simp [close,hnm']

lemma offDiagonal_eq_far_sub_close (N : ℕ) :
    offDiagonal N=farSum N-(closeCount N:ℝ) := by
  have he : offDiagonal N=farSum N+closeSum N := by
    rw [closeSum_eq_triangle]
    unfold offDiagonal farSum
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro m hm
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    split_ifs <;> ring
  rw [he,closeSum_eq]
  ring

/-- Exact remaining signed problem after removing the controlled negative
region. No near-linear bound on `farSum` has been proved. -/
theorem energy_eq_far (N : ℕ) : Erdos371PrimeEnergy.energy N=
    (N-1:ℕ)+2*farSum N-2*(closeCount N:ℝ) := by
  rw [energy_expansion,offDiagonal_eq_far_sub_close]
  ring

end Erdos371GcdCorrelation

#print axioms Erdos371GcdCorrelation.same_sign_gap_bound
#print axioms Erdos371GcdCorrelation.closeSum_nonpos
#print axioms Erdos371GcdCorrelation.closeCount_le_divisor_sum

#print axioms Erdos371GcdCorrelation.closeCount_bound

#print axioms Erdos371GcdCorrelation.energy_eq_far
