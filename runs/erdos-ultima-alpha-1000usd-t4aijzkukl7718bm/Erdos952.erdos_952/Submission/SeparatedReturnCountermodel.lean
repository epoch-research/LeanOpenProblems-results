import Submission.GeodesicAdmissibleLimit

/-! Separation and uniform recurrence do not give a recurrence bound depending
only on the jump bound. These examples are neither prime nor asserted admissible. -/
namespace Erdos952Investigation.SeparatedReturnCountermodel
open MinimalWordLimit RecurrentAdmissibleReduction GeodesicAdmissibleLimit
set_option maxHeartbeats 0

def word (P n : ℕ) : GaussianInt := ⟨3,if n%P = 0 then 1 else -1⟩
def path (P : ℕ) : ℕ → GaussianInt := integral (word P)

lemma path_increment (P n : ℕ) : increment (path P) n = word P n :=
  integral_increment _ _

lemma path_real (P n : ℕ) : (path P n).re = 3*(n : ℤ) := by
  induction n with
  | zero => simp [path,integral_zero]
  | succ n ih =>
    change (integral (word P) (n+1)).re = _
    rw [integral_succ]
    change (path P n).re+3 = _
    rw [ih]
    push_cast
    ring

lemma path_injective (P : ℕ) : Function.Injective (path P) := by
  intro i j he
  have hh := congrArg Zsqrtd.re he
  rw [path_real,path_real] at hh
  exact_mod_cast (show (i : ℤ) = j by omega)

lemma path_step_norm (P n : ℕ) : (increment (path P) n).norm = 10 := by
  rw [path_increment]
  by_cases hn : n%P = 0 <;> norm_num [word,gaussian_norm_sq,hn]

lemma path_separated (P : ℕ) : Separated 11 (path P) := by
  intro i j hij
  have hdiff : (2 : ℤ) ≤ (j : ℤ)-i := by omega
  rw [gaussian_norm_sq]
  change 11 ≤ ((path P j).re-(path P i).re)^2+
    ((path P j).im-(path P i).im)^2
  rw [path_real,path_real]
  nlinarith [sq_nonneg ((path P j).im-(path P i).im)]

lemma first_increment_match_iff (P n : ℕ) :
    increment (path P) n = increment (path P) 0 ↔ n%P = 0 := by
  rw [path_increment,path_increment]
  by_cases hn : n%P = 0
  · simp [word,hn]
  · constructor
    · intro he
      have hh := congrArg Zsqrtd.im he
      norm_num [word,hn] at hh
    · exact False.elim ∘ hn

lemma path_uniformly_recurrent (P : ℕ) (hP : 0 < P) :
    UniformlyRecurrent (increment (path P)) := by
  intro L
  refine ⟨P,?_⟩
  intro N
  let n := P*(N/P+1)
  have hn : N ≤ n ∧ n ≤ N+P := by
    have he := Nat.mod_add_div N P
    have hm := Nat.mod_lt N hP
    dsimp [n]
    rw [Nat.mul_add,Nat.mul_one]
    omega
  refine ⟨n,hn.1,hn.2,?_⟩
  intro i _
  rw [path_increment,path_increment]
  have hn0 : n%P = 0 := by simp [n]
  have he : (n+i)%P = i%P := by rw [Nat.add_mod,hn0]; simp
  simp only [word,he]

/-- Even the return bound for the first increment can be arbitrarily large at
one fixed geometric jump bound. -/
lemma first_return_bound_lower (P R : ℕ)
    (hR : ∀ N : ℕ, ∃ n, N ≤ n ∧ n ≤ N+R ∧
      increment (path P) n = increment (path P) 0) : P ≤ R+1 := by
  obtain ⟨n,hn,hnR,he⟩ := hR 1
  have hd : P ∣ n := Nat.dvd_of_mod_eq_zero ((first_increment_match_iff P n).mp he)
  have hle := Nat.le_of_dvd (by omega : 0 < n) hd
  omega

/-- No universal recurrence bound for these separated, uniformly recurrent
bounded-step paths follows from geometry alone. -/
theorem arbitrarily_large_first_return_bound (B : ℕ) :
    ∃ x : ℕ → GaussianInt, Function.Injective x ∧
      (∀ n, (increment x n).norm < 11) ∧ Separated 11 x ∧
      UniformlyRecurrent (increment x) ∧
      ¬ ∀ N : ℕ, ∃ n, N ≤ n ∧ n ≤ N+B ∧ increment x n = increment x 0 := by
  refine ⟨path (B+2),path_injective _,fun n => ?_,path_separated _,
    path_uniformly_recurrent _ (by omega),?_⟩
  · rw [path_step_norm]; norm_num
  · intro hR
    have hh := first_return_bound_lower (B+2) B hR
    omega

#print axioms arbitrarily_large_first_return_bound
end Erdos952Investigation.SeparatedReturnCountermodel
