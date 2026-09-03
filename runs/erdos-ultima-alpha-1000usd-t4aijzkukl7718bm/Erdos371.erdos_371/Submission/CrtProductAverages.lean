import Submission.CoprimeResidueSieve

/-! CRT factorization of product averages, and quantitative periodic mean
bounds for functions which need not be indicator functions. -/

namespace Erdos371
namespace FiniteSieve
open Finset
variable {ι : Type*}

lemma sum_prod_residues_eq_prod_sum (S : Finset ι) (s : ι → ℕ)
    (f : ι → ℕ → ℝ) (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s)) :
    (∑ n ∈ range (∏ i ∈ S, s i), ∏ i ∈ S, f i (n % s i)) =
      ∏ i ∈ S, ∑ r ∈ range (s i), f i r := by
  classical
  rw [prod_sum]
  apply sum_bij (fun n _ i _ => n % s i)
  · intro n hn
    exact mem_pi.mpr fun i hi => mem_range.mpr (Nat.mod_lt _ (Nat.pos_of_ne_zero (hs i hi)))
  · intro a ha b hb hab
    apply ((modEq_finset_prod_iff S s hc a b).mpr ?_).eq_of_lt_of_lt
      (mem_range.mp ha) (mem_range.mp hb)
    intro i hi
    exact congrFun (congrFun hab i) hi
  · intro r hr
    let a : ι → ℕ := fun i => if hi : i ∈ S then r i hi else 0
    let n := Nat.chineseRemainderOfFinset a s S hs hc
    have hnmod (i : ι) (hi : i ∈ S) : n.val % s i = r i hi := by
      have h : n.val % s i = a i % s i := n.property i hi
      have hlt := mem_range.mp (mem_pi.mp hr i hi)
      simpa [a,hi,Nat.mod_eq_of_lt hlt] using h
    refine ⟨n.val,mem_range.mpr (Nat.chineseRemainderOfFinset_lt_prod a s hs hc),?_⟩
    funext i hi
    exact hnmod i hi
  · intro n hn
    exact (Finset.prod_attach S (fun i => f i (n % s i))).symm

lemma periodic_zero_sum_bound (f : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (C : ℝ) (hC : 0 ≤ C) (hp : Function.Periodic f Q)
    (hz : ∑ n ∈ range Q, f n = 0) (hb : ∀ n, |f n| ≤ C) (N : ℕ) :
    |∑ n ∈ range N, f n| ≤ Q*C := by
  have hper (k n : ℕ) : f (k*Q+n) = f n := by
    simpa only [Nat.cast_id,Nat.add_comm] using hp.nat_mul k n
  have hsum (k : ℕ) : ∑ n ∈ range (k*Q), f n = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.succ_mul,sum_range_add,ih]
      simpa only [hper,zero_add] using hz
  have he : (∑ n ∈ range N, f n) = ∑ n ∈ range (N%Q), f n := by
    conv_lhs => rw [← Nat.mod_add_div' N Q,Nat.add_comm,sum_range_add]
    simp only [hsum,hper,zero_add]
  rw [he]
  calc
    _ ≤ ∑ n ∈ range (N%Q), |f n| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ range (N%Q), C := sum_le_sum fun n _ => hb n
    _ = (N%Q : ℕ)*C := by simp
    _ ≤ Q*C := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.mod_lt N hQ).le) hC

lemma periodic_mean_error_bound (f : ℕ → ℝ) (Q : ℕ) (hQ : 0 < Q)
    (C : ℝ) (hC : 0 ≤ C) (hp : Function.Periodic f Q) (hb : ∀ n, |f n| ≤ C)
    (N : ℕ) :
    |(∑ n ∈ range N, f n) - (N : ℝ)/Q*(∑ n ∈ range Q, f n)| ≤ 2*Q*C := by
  let a : ℝ := (∑ n ∈ range Q, f n)/Q
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have ha : |a| ≤ C := by
    dsimp only [a]
    rw [abs_div,abs_of_nonneg hQ0.le]
    apply (div_le_iff₀ hQ0).mpr
    calc
      _ ≤ ∑ n ∈ range Q, |f n| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ range Q, C := sum_le_sum fun n _ => hb n
      _ = _ := by simp [mul_comm]
  have hper : Function.Periodic (fun n => f n-a) Q := fun n => by dsimp; rw [hp n]
  have hz : (∑ n ∈ range Q, (f n-a)) = 0 := by
    rw [sum_sub_distrib]
    simp only [sum_const,card_range,nsmul_eq_mul]
    dsimp only [a]
    field_simp
    ring
  have hbound (n : ℕ) : |f n-a| ≤ 2*C := by
    have h := abs_sub (f n) a
    linarith [hb n,ha]
  have h := periodic_zero_sum_bound _ Q hQ (2*C) (by positivity) hper hz hbound N
  rw [sum_sub_distrib] at h
  simp only [sum_const,card_range,nsmul_eq_mul] at h
  convert h using 1 <;> dsimp only [a] <;> ring

#print axioms sum_prod_residues_eq_prod_sum
#print axioms periodic_mean_error_bound
end FiniteSieve
end Erdos371
