import Submission.BinaryWeightedCertificates

/-! A limitation of single-digit additive potentials, not a settlement of Erdős 406. -/
namespace Erdos406BinaryDigitCost

noncomputable def digitCost (a b : ℝ) (n : ℕ) : ℝ :=
  ((Nat.digits 2 n).map (fun d => if d = 0 then a else b)).sum

lemma cost_zero (a b : ℝ) : digitCost a b 0 = 0 := by simp [digitCost]
lemma cost_one (a b : ℝ) : digitCost a b 1 = b := by simp [digitCost]
lemma cost_even (a b : ℝ) (n : ℕ) (hn : 0 < n) :
    digitCost a b (2*n) = a + digitCost a b n := by
  rw [digitCost, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) (by omega : 0 < 2*n)]
  simp [digitCost]
lemma cost_odd (a b : ℝ) (n : ℕ) :
    digitCost a b (2*n+1) = b + digitCost a b n := by
  rw [digitCost, Nat.digits_of_two_le_of_pos (by decide : 2 ≤ 2) (by omega : 0 < 2*n+1)]
  have hd : (2*n+1)/2 = n := by omega
  have hm : (2*n+1)%2 = 1 := by omega
  simp [digitCost,hd,hm]
lemma cost_power (a b : ℝ) (k : ℕ) : digitCost a b (2^k) = a*k+b := by
  induction k with
  | zero => simp [cost_one]
  | succ k ih =>
    rw [pow_succ',cost_even a b _ (by positivity),ih]
    push_cast
    ring

private def alternator : ℕ → ℕ
  | 0 => 0
  | k+1 => 4*alternator k+1
private lemma alternator_identity (k : ℕ) : 3*alternator k+1 = 4^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [alternator,pow_succ]; nlinarith
private lemma alternator_pos (k : ℕ) : 0 < alternator (k+1) := by
  simp only [alternator]; omega
private lemma alternator_cost (a b : ℝ) (k : ℕ) :
    digitCost a b (alternator (k+1)) = (a+b)*k+b := by
  induction k with
  | zero => simp [alternator,cost_one]
  | succ k ih =>
    have he : alternator (k+1+1) = 2*(2*alternator (k+1))+1 := by rw [alternator]; ring
    rw [he,cost_odd,cost_even a b _ (alternator_pos k),ih]
    push_cast
    ring
private def ones : ℕ → ℕ
  | 0 => 0
  | k+1 => 2*ones k+1
private lemma ones_identity (k : ℕ) : ones k+1 = 2^k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [ones,pow_succ]; nlinarith
private lemma ones_cost (a b : ℝ) (k : ℕ) : digitCost a b (ones k) = b*k := by
  induction k with
  | zero => simp [ones,cost_zero]
  | succ k ih => rw [ones,cost_odd,ih]; push_cast; ring
private lemma three_alternator (k : ℕ) : 3*alternator k = ones (2*k) := by
  have h := alternator_identity k
  have h' := ones_identity (2*k)
  have he : (2:ℕ)^(2*k)=4^k := by rw [pow_mul]; rfl
  rw [he] at h'
  omega

private lemma slope_le (x y B : ℝ) (h : ∀ k : ℕ, (x-y)*k ≤ B) : x ≤ y := by
  by_contra hn
  have hp : 0 < x-y := by linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (B/(x-y))
  have hh := (div_lt_iff₀ hp).mp hk
  nlinarith [h k]

/-- Bounded perturbations cannot assign distinct asymptotic costs to binary
zero and one if both ternary construction maps have uniformly bounded cost. -/
theorem coefficients_eq (V : ℕ → ℝ) (a b C D : ℝ)
    (happrox : ∀ n, |V n-digitCost a b n| ≤ C)
    (hstep : ∀ n d : ℕ, d < 2 → V (3*n+d) ≤ V n+D) : a=b := by
  have hs (n d : ℕ) (hd : d<2) :
      digitCost a b (3*n+d) ≤ digitCost a b n+D+2*C := by
    have h1 := (abs_le.mp (happrox n)).2
    have h2 := (abs_le.mp (happrox (3*n+d))).1
    have h3 := hstep n d hd
    linarith
  have hab : a ≤ b := by
    apply slope_le a b (D+2*C-2*a)
    intro k
    have h := hs (alternator (k+1)) 1 (by decide)
    rw [alternator_identity] at h
    have he : (4:ℕ)^(k+1)=2^(2*(k+1)) := by rw [pow_mul]; rfl
    rw [he,cost_power,alternator_cost] at h
    push_cast at h
    nlinarith
  have hba : b ≤ a := by
    apply slope_le b a (D+2*C-b)
    intro k
    have h := hs (alternator (k+1)) 0 (by decide)
    simp only [add_zero,three_alternator,ones_cost,alternator_cost] at h
    push_cast at h
    nlinarith
  exact le_antisymm hab hba

lemma equal_cost (a : ℝ) (n : ℕ) : digitCost a a n = a*(Nat.digits 2 n).length := by
  unfold digitCost
  generalize Nat.digits 2 n = L
  induction L with
  | nil => simp
  | cons d L ih =>
    simp only [ite_self] at ih ⊢
    simp only [List.map_cons,List.sum_cons,List.length_cons,ih]
    push_cast
    ring

/-- The single-digit bounded-perturbation class cannot provide the required
strict growth rate. This says nothing about arbitrary weighted automata. -/
theorem not_supercritical (V : ℕ → ℝ) (a b C α B : ℝ)
    (happrox : ∀ n, |V n-digitCost a b n| ≤ C)
    (hstep : ∀ n d : ℕ, d < 2 → V (3*n+d) ≤ V n+1)
    (hpower : ∀ k : ℕ, α*k-B ≤ V (2^k)) : ¬ Real.log 2 < α*Real.log 3 := by
  have hab := coefficients_eq V a b C 1 happrox hstep
  subst b
  have ha : α ≤ a := by
    apply slope_le α a (B+a+C)
    intro k
    have h := (abs_le.mp (happrox (2^k))).2
    rw [cost_power] at h
    nlinarith [hpower k]
  have hbound : ∀ n : ℕ, 0<n → a*(Nat.digits 2 n).length-C ≤ V n := by
    intro n _
    have h := (abs_le.mp (happrox n)).1
    rw [equal_cost] at h
    linarith
  have hh := Erdos406BinaryWeighted.not_supercritical_of_global_binary_lower_bound V a C hstep hbound
  intro hc
  apply hh
  have hl : 0 < Real.log 3 := Real.log_pos (by norm_num)
  exact hc.trans_le (mul_le_mul_of_nonneg_right ha hl.le)

#print axioms coefficients_eq
#print axioms not_supercritical
end Erdos406BinaryDigitCost
