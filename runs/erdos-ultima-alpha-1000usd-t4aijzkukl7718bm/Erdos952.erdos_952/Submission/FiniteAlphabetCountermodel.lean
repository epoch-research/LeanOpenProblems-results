import Submission.AutomaticIncrementObstruction

/-! Finitely many possible increments do not imply a finite base-q kernel.
This countermodel concerns that inference only, not Gaussian primality. -/
namespace Erdos952Investigation
namespace FiniteAlphabetCountermodel

open AutomaticIncrementObstruction
set_option maxHeartbeats 0

noncomputable def spike (n : ℕ) : ℤ := by
  classical
  exact if ∃ k : ℕ, n = 2^(2^k) then 1 else 0

noncomputable def step (n : ℕ) : GaussianInt := ⟨1,spike n⟩

lemma spike_dpower (k : ℕ) : spike (2^(2^k)) = 1 := by
  classical
  rw [spike, if_pos (show ∃ v : ℕ, 2^(2^k) = 2^(2^v) from ⟨k, rfl⟩)]

lemma spike_range (n : ℕ) : spike n = 0 ∨ spike n = 1 := by
  classical
  unfold spike
  split_ifs <;> simp

lemma subsequences_injective : Function.Injective (fun k : ℕ => fun n => step (2^k*n)) := by
  intro k l he
  by_contra hne
  wlog hkl : k < l generalizing k l
  · exact this (k := l) (l := k) he.symm (Ne.symm hne) (by omega)
  let t := 2^l-k
  have hbase : l < 2^l := Nat.lt_two_pow_self
  have hkt : k+t = 2^l := by dsimp [t]; omega
  have hlo : 2^l < l+t := by dsimp [t]; omega
  have hhi : l+t < 2^(l+1) := by rw [pow_succ]; dsimp [t]; omega
  have hnot : ¬ ∃ v : ℕ, 2^(l+t) = 2^(2^v) := by
    rintro ⟨v,hv⟩
    have hv' := Nat.pow_right_injective (by decide : 2 ≤ 2) hv
    have hlow : l < v := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
    have hhigh : v < l+1 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by omega)
    omega
  have hh := congrArg (fun f : ℕ → GaussianInt => (f (2^t)).im) he
  change spike (2^k*2^t) = spike (2^l*2^t) at hh
  rw [← pow_add,← pow_add,hkt,spike_dpower] at hh
  have hzero : spike (2^(l+t)) = 0 := by
    classical
    simp only [spike,if_neg hnot]
  rw [hzero] at hh
  norm_num at hh

lemma step_kernel_infinite : (Kernel 2 step).Infinite := by
  apply (Set.infinite_range_of_injective subsequences_injective).mono
  rintro f ⟨k,rfl⟩
  exact ⟨k,0,by positivity,by funext n; simp⟩

noncomputable def walk (n : ℕ) : GaussianInt := ⟨n,∑ j ∈ Finset.range n, spike j⟩

lemma walk_injective : Function.Injective walk := by
  intro i j he
  exact Int.natCast_inj.mp (congrArg Zsqrtd.re he)

lemma walk_increment (n : ℕ) : walk (n+1)-walk n = step n := by
  apply Zsqrtd.ext <;> simp [walk,step,Finset.sum_range_succ]

lemma walk_step_bound (n : ℕ) : (walk (n+1)-walk n).norm < 3 := by
  rw [walk_increment]
  rcases spike_range n with h | h <;> norm_num [step,gaussian_norm_sq,h]

/-- The finite-kernel obstruction does not follow merely from injectivity and
a uniform step bound. This path is not claimed to consist of primes. -/
theorem bounded_step_infinite_kernel_counterexample :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (x (n+1)-x n).norm < 3) ∧
      (Kernel 2 (fun n => x (n+1)-x n)).Infinite := by
  exact ⟨walk,walk_injective,walk_step_bound,by
    simpa only [walk_increment] using step_kernel_infinite⟩

#print axioms subsequences_injective
#print axioms bounded_step_infinite_kernel_counterexample

end FiniteAlphabetCountermodel
end Erdos952Investigation
