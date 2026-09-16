import FormalConjectures.Util.ProblemImports
open Nat Finset

def a (n : ℕ) : ℕ :=
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k
  numerator / denominator

def num (n : ℕ) := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
def den (n : ℕ) := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

lemma a_eq (n : ℕ) : a n = num n / den n := rfl

lemma num_ne_zero (n : ℕ) : num n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro j hj
  apply prod_ne_zero_iff.mpr
  intro k _
  apply Nat.ne_of_gt
  apply Nat.pos_of_ne_zero
  intro h
  have : j = 0 := (Nat.gcd_eq_zero_iff.mp h).1
  rw [mem_Icc] at hj
  omega

lemma den_ne_zero (n : ℕ) : den n ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro k _
  positivity

lemma padicValNat_prod {α : Type*} {s : Finset α} {f : α → ℕ} {p : ℕ} [hp : Fact p.Prime]
    (h0 : ∀ x ∈ s, f x ≠ 0) :
    padicValNat p (s.prod f) = s.sum (fun x => padicValNat p (f x)) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s has ih =>
    rw [prod_cons, sum_cons]
    have h1 : f a ≠ 0 := h0 a (mem_cons_self a s)
    have h2 : ∀ x ∈ s, f x ≠ 0 := fun x hx => h0 x (mem_cons_of_mem hx)
    have h3 : s.prod f ≠ 0 := prod_ne_zero_iff.mpr h2
    rw [padicValNat.mul h1 h3]
    congr 1
    exact ih h2

lemma val_le_n {n p j : ℕ} (hp : Fact p.Prime) (hj : j ∈ Icc 1 n) : padicValNat p j ≤ n := by
  have hj0 : j ≠ 0 := by rw [mem_Icc] at hj; omega
  have h1 : p ^ (padicValNat p j) ≤ j := by
    apply Nat.le_of_dvd (by omega)
    rw [← Nat.factorization_def j hp.out]
    exact (hp.out.pow_dvd_iff_le_factorization hj0).mpr le_rfl
  have h2 : padicValNat p j ≤ p ^ (padicValNat p j) := le_of_lt (Nat.lt_pow_self hp.out.one_lt)
  rw [mem_Icc] at hj
  omega

lemma val_eq_sum {n p j : ℕ} (hp : Fact p.Prime) (hj : j ∈ Icc 1 n) :
    padicValNat p j = (Icc 1 n).sum (fun e => if p^e ∣ j then 1 else 0) := by
  have hj0 : j ≠ 0 := by rw [mem_Icc] at hj; omega
  have eq1 : (fun e => if p^e ∣ j then (1:ℕ) else 0) = (fun e => if e ≤ padicValNat p j then (1:ℕ) else 0) := by
    ext e
    congr 1
    rw [← Nat.factorization_def j hp.out]
    exact propext (hp.out.pow_dvd_iff_le_factorization hj0)
  rw [eq1, sum_boole]
  have eq2 : ((Icc 1 n).filter (fun e => e ≤ padicValNat p j)) = Icc 1 (padicValNat p j) := by
    ext x
    rw [mem_filter, mem_Icc, mem_Icc]
    have := val_le_n hp hj
    omega
  rw [eq2, Nat.card_Icc, Nat.add_sub_cancel]
  rfl

lemma val_gcd_eq_sum {n p j k : ℕ} (hp : Fact p.Prime) (hj : j ∈ Icc 1 n) (hk : k ∈ Icc 1 n) :
    padicValNat p (Nat.gcd j k) = (Icc 1 n).sum (fun e => if p^e ∣ j ∧ p^e ∣ k then 1 else 0) := by
  have hgcd : Nat.gcd j k ∈ Icc 1 n := by
    rw [mem_Icc] at hj hk ⊢
    have h1 : 1 ≤ Nat.gcd j k := by
      apply Nat.pos_of_ne_zero
      intro h
      have : j = 0 := (Nat.gcd_eq_zero_iff.mp h).1
      omega
    have h2 : Nat.gcd j k ≤ j := Nat.gcd_le_left k (by omega)
    exact ⟨h1, le_trans h2 hj.2⟩
  have := val_eq_sum hp hgcd
  have eq1 : (fun e => if p^e ∣ Nat.gcd j k then (1:ℕ) else 0) = (fun e => if p^e ∣ j ∧ p^e ∣ k then (1:ℕ) else 0) := by
    ext e
    congr 1
    exact propext (Nat.dvd_gcd_iff)
  rw [eq1] at this
  exact this

lemma sum_sum_boole_and {n : ℕ} {f : ℕ → Prop} [DecidablePred f] :
    (Icc 1 n).sum (fun j => (Icc 1 n).sum (fun k => if f j ∧ f k then (1:ℕ) else 0)) =
    ((Icc 1 n).filter f).card ^ 2 := by
  have eq1 : ∀ j, (Icc 1 n).sum (fun k => if f j ∧ f k then (1:ℕ) else 0) =
      if f j then ((Icc 1 n).filter f).card else 0 := by
    intro j
    by_cases h : f j
    · have : (fun k => if f j ∧ f k then (1:ℕ) else 0) = (fun k => if f k then (1:ℕ) else 0) := by
        ext k; congr 1; exact propext ⟨fun h2 => h2.2, fun h2 => ⟨h, h2⟩⟩
      rw [this, sum_boole, if_pos h]; rfl
    · have : (fun k => if f j ∧ f k then (1:ℕ) else 0) = (fun k => 0) := by
        ext k; have h2 : ¬(f j ∧ f k) := fun h3 => h h3.1; simp only [h2, if_false]
      rw [this, sum_const_zero, if_neg h]
  have eq2 : (Icc 1 n).sum (fun j => if f j then ((Icc 1 n).filter f).card else 0) =
      ((Icc 1 n).filter f).card * ((Icc 1 n).filter f).card := by
    have : (fun j => if f j then ((Icc 1 n).filter f).card else 0) =
        (fun j => ((Icc 1 n).filter f).card * if f j then (1:ℕ) else 0) := by
      ext j; by_cases h : f j
      · rw [if_pos h, if_pos h, mul_one]
      · rw [if_neg h, if_neg h, mul_zero]
    rw [this, ← mul_sum, sum_boole]
    rfl
  rw [sum_congr rfl (fun j _ => eq1 j)]
  exact eq2.trans (sq _).symm

lemma card_multiples (n d : ℕ) (hd : d ≠ 0) :
    ((Icc 1 n).filter (fun x => d ∣ x)).card = n / d := by
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd
  let s := ((Icc 1 n).filter (fun x => d ∣ x))
  have eq1 : s.card = (Icc 1 (n / d)).card := by
    apply Finset.card_bij (fun x _ => x / d)
    · intro a ha
      rw [mem_filter, mem_Icc] at ha
      rw [mem_Icc]
      have eq : a / d * d = a := Nat.div_mul_cancel ha.2
      have h1 : 1 ≤ a / d := by
        apply Nat.pos_of_ne_zero
        intro hz
        rw [hz, zero_mul] at eq
        omega
      have h2 : a / d ≤ n / d := Nat.div_le_div_right ha.1.2
      exact ⟨h1, h2⟩
    · intro a ha b hb eq
      rw [mem_filter] at ha hb
      have eq2 : a / d * d = b / d * d := by rw [eq]
      rw [Nat.div_mul_cancel ha.2, Nat.div_mul_cancel hb.2] at eq2
      exact eq2
    · intro b hb
      rw [mem_Icc] at hb
      have : b * d ∈ s := by
        rw [mem_filter, mem_Icc]
        have h1 : 1 ≤ b * d := by nlinarith
        have eq : (n / d) * d ≤ n := Nat.div_mul_le_self n d
        have h2 : b * d ≤ n := by nlinarith
        exact ⟨⟨h1, h2⟩, dvd_mul_left d b⟩
      exact ⟨b * d, this, Nat.mul_div_cancel b hd_pos⟩
  rw [eq1, Nat.card_Icc, Nat.add_sub_cancel]

lemma val_num_eq {n p : ℕ} (hp : Fact p.Prime) :
    padicValNat p (num n) =
    (Icc 1 n).sum (fun e => ((Icc 1 n).filter (fun x => p^e ∣ x)).card ^ 2) := by
  have h0 : ∀ j ∈ Icc 1 n, (Icc 1 n).prod (fun k => Nat.gcd j k) ≠ 0 := by
    intro j hj
    apply prod_ne_zero_iff.mpr
    intro k _
    apply Nat.ne_of_gt
    apply Nat.pos_of_ne_zero
    intro h
    have : j = 0 := (Nat.gcd_eq_zero_iff.mp h).1
    rw [mem_Icc] at hj
    omega
  rw [num, padicValNat_prod h0]
  have eq1 : ∀ j ∈ Icc 1 n, padicValNat p ((Icc 1 n).prod (fun k => Nat.gcd j k)) =
      (Icc 1 n).sum (fun k => (Icc 1 n).sum (fun e => if p^e ∣ j ∧ p^e ∣ k then (1:ℕ) else 0)) := by
    intro j hj
    have h1 : ∀ k ∈ Icc 1 n, Nat.gcd j k ≠ 0 := by
      intro k _
      apply Nat.ne_of_gt
      apply Nat.pos_of_ne_zero
      intro h
      have : j = 0 := (Nat.gcd_eq_zero_iff.mp h).1
      rw [mem_Icc] at hj; omega
    rw [padicValNat_prod h1]
    apply sum_congr rfl
    intro k hk
    exact val_gcd_eq_sum hp hj hk
  rw [sum_congr rfl eq1]
  have eq2 : (Icc 1 n).sum (fun j => (Icc 1 n).sum (fun k => (Icc 1 n).sum (fun e => if p^e ∣ j ∧ p^e ∣ k then (1:ℕ) else 0))) =
      (Icc 1 n).sum (fun e => (Icc 1 n).sum (fun j => (Icc 1 n).sum (fun k => if p^e ∣ j ∧ p^e ∣ k then (1:ℕ) else 0))) := by
    calc
      _ = (Icc 1 n).sum (fun j => (Icc 1 n).sum (fun e => (Icc 1 n).sum (fun k => if p^e ∣ j ∧ p^e ∣ k then (1:ℕ) else 0))) := by
        apply sum_congr rfl
        intro j _
        rw [sum_comm]
      _ = _ := by
        rw [sum_comm]
  rw [eq2]
  apply sum_congr rfl
  intro e _
  exact sum_sum_boole_and

lemma val_num_final {n p : ℕ} (hp : Fact p.Prime) :
    padicValNat p (num n) =
    (Icc 1 n).sum (fun e => (n / p^e) ^ 2) := by
  rw [val_num_eq hp]
  apply sum_congr rfl
  intro e _
  have h_ne : p^e ≠ 0 := by
    have : 0 < p := hp.out.pos
    positivity
  rw [card_multiples n (p^e) h_ne]

lemma val_den_fact {n m p : ℕ} (hp : Fact p.Prime) (hm : m ≤ n) :
    padicValNat p (m.factorial) = (Icc 1 n).sum (fun e => m / p^e) := by
  have hb : Nat.log p m < n + 1 := by
    have : 2 ≤ p := hp.out.two_le
    have h1 : Nat.log p m ≤ m := Nat.log_le_self p m
    omega
  have := padicValNat_factorial (b := n + 1) hb
  have eq : Ico 1 (n + 1) = Icc 1 n := by
    ext x
    rw [mem_Ico, mem_Icc]
    omega
  rw [eq] at this
  exact this

lemma val_den_eq {n p : ℕ} (hp : Fact p.Prime) :
    padicValNat p (den n) =
    (Icc 1 n).sum (fun k => k * (Icc 1 n).sum (fun e => (n / k) / p^e)) := by
  have h0 : ∀ k ∈ Icc 1 n, (Nat.factorial (n / k)) ^ k ≠ 0 := by
    intro k _
    have h1 : (n / k).factorial ≠ 0 := factorial_ne_zero (n / k)
    positivity
  rw [den, padicValNat_prod h0]
  apply sum_congr rfl
  intro k _
  have h1 : (n / k).factorial ≠ 0 := factorial_ne_zero (n / k)
  rw [padicValNat.pow k h1, val_den_fact hp (Nat.div_le_self n k)]

lemma val_den_final {n p : ℕ} (hp : Fact p.Prime) :
    padicValNat p (den n) =
    (Icc 1 n).sum (fun e => (Icc 1 n).sum (fun k => k * ((n / p^e) / k))) := by
  rw [val_den_eq hp]
  have eq : (Icc 1 n).sum (fun k => k * (Icc 1 n).sum (fun e => (n / k) / p^e)) =
      (Icc 1 n).sum (fun e => (Icc 1 n).sum (fun k => k * ((n / p^e) / k))) := by
    calc
      _ = (Icc 1 n).sum (fun k => (Icc 1 n).sum (fun e => k * ((n / k) / p^e))) := by
        apply sum_congr rfl
        intro k _
        rw [mul_sum]
      _ = (Icc 1 n).sum (fun k => (Icc 1 n).sum (fun e => k * ((n / p^e) / k))) := by
        apply sum_congr rfl
        intro k _
        apply sum_congr rfl
        intro e _
        have h1 : (n / k) / p^e = n / (k * p^e) := Nat.div_div_eq_div_mul n k (p^e)
        have h2 : (n / p^e) / k = n / (p^e * k) := Nat.div_div_eq_div_mul n (p^e) k
        rw [mul_comm k (p^e)] at h1
        rw [h1, h2]
      _ = _ := by rw [sum_comm]
  rw [eq]

lemma sum_k_div_k_le (x n : ℕ) : (Icc 1 n).sum (fun k => k * (x / k)) ≤ x^2 := by
  have eq : (Icc 1 n).sum (fun k => k * (x / k)) = ((Icc 1 n).filter (fun k => k ≤ x)).sum (fun k => k * (x / k)) := by
    apply Eq.symm
    apply sum_subset (filter_subset _ _)
    intro k hk1 hk2
    simp only [mem_filter, hk1, true_and, not_le] at hk2
    have : x / k = 0 := Nat.div_eq_of_lt hk2
    rw [this, mul_zero]
  rw [eq]
  have h_le : ((Icc 1 n).filter (fun k => k ≤ x)).sum (fun k => k * (x / k)) ≤ ((Icc 1 n).filter (fun k => k ≤ x)).sum (fun _ => x) := by
    apply sum_le_sum
    intro k _
    exact Nat.mul_div_le x k
  have h_card : ((Icc 1 n).filter (fun k => k ≤ x)).card ≤ x := by
    have subset : ((Icc 1 n).filter (fun k => k ≤ x)) ⊆ Icc 1 x := by
      intro a ha
      rw [mem_filter, mem_Icc] at ha
      rw [mem_Icc]
      exact ⟨ha.1.1, ha.2⟩
    have := card_le_card subset
    rw [Nat.card_Icc] at this
    omega
  rw [sum_const] at h_le
  have : ((Icc 1 n).filter (fun k => k ≤ x)).card * x ≤ x * x := Nat.mul_le_mul_right x h_card
  rw [sq]
  exact le_trans h_le this

lemma sum_k_div_k_lt (x n : ℕ) (hx : 3 ≤ x) (hn : x ≤ n) : (Icc 1 n).sum (fun k => k * (x / k)) < x^2 := by
  have eq : (Icc 1 n).sum (fun k => k * (x / k)) = ((Icc 1 n).filter (fun k => k ≤ x)).sum (fun k => k * (x / k)) := by
    apply Eq.symm
    apply sum_subset (filter_subset _ _)
    intro k hk1 hk2
    simp only [mem_filter, hk1, true_and, not_le] at hk2
    have : x / k = 0 := Nat.div_eq_of_lt hk2
    rw [this, mul_zero]
  rw [eq]
  have eq2 : ((Icc 1 n).filter (fun k => k ≤ x)) = Icc 1 x := by
    ext a
    rw [mem_filter, mem_Icc, mem_Icc]
    omega
  rw [eq2]
  have sum_eq_x2 : (Icc 1 x).sum (fun _ => x) = x^2 := by
    rw [sum_const, Nat.card_Icc]
    have : x + 1 - 1 = x := by omega
    rw [this]
    simp [sq]
  have h_le : ∀ k ∈ Icc 1 x, k * (x / k) ≤ x := by
    intro k _
    exact Nat.mul_div_le x k
  have h_strict : (x - 1) * (x / (x - 1)) < x := by
    have h1 : x / (x - 1) = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · omega
    rw [h1, mul_one]
    omega
  have h_mem : x - 1 ∈ Icc 1 x := by
    rw [mem_Icc]
    omega
  have : (Icc 1 x).sum (fun k => k * (x / k)) < (Icc 1 x).sum (fun _ => x) := by
    apply sum_lt_sum h_le
    use x - 1
  rwa [sum_eq_x2] at this

lemma val_le_div {n p : ℕ} (h_p : p ≤ n / 3) (hp_pos : 0 < p) : 3 ≤ n / p := by
  apply Nat.le_div_iff_mul_le hp_pos |>.mpr
  have h1 : (n / 3) * 3 ≤ n := Nat.div_mul_le_self n 3
  nlinarith

lemma val_ineq {n p : ℕ} (hp : Fact p.Prime) :
    padicValNat p (den n) ≤ padicValNat p (num n) := by
  rw [val_den_final hp, val_num_final hp]
  apply sum_le_sum
  intro e _
  exact sum_k_div_k_le (n / p^e) n

lemma den_dvd_num (n : ℕ) : den n ∣ num n := by
  apply Nat.dvd_iff_prime_pow_dvd_dvd (num n) (den n) |>.mpr
  intro p k hp hk
  have h_fact : Fact p.Prime := ⟨hp⟩
  have h1 : k ≤ padicValNat p (den n) := by
    rw [← Nat.factorization_def (den n) hp]
    exact (hp.pow_dvd_iff_le_factorization (den_ne_zero n)).mp hk
  have h2 : padicValNat p (den n) ≤ padicValNat p (num n) := val_ineq h_fact
  have h3 : k ≤ padicValNat p (num n) := le_trans h1 h2
  rw [← Nat.factorization_def (num n) hp] at h3
  exact (hp.pow_dvd_iff_le_factorization (num_ne_zero n)).mpr h3

lemma a_ne_zero (n : ℕ) : a n ≠ 0 := by
  have h_dvd := den_dvd_num n
  rw [a_eq]
  intro h
  have eq : num n = den n * (num n / den n) := (Nat.mul_div_cancel' h_dvd).symm
  rw [h, mul_zero] at eq
  exact num_ne_zero n eq

lemma p_dvd_a_iff (n p : ℕ) (hp : p.Prime) :
    p ∣ a n ↔ padicValNat p (den n) < padicValNat p (num n) := by
  have h_dvd := den_dvd_num n
  have eq : num n = den n * a n := by
    rw [a_eq]
    exact (Nat.mul_div_cancel' h_dvd).symm
  have h_a : a n ≠ 0 := a_ne_zero n
  have val_eq : padicValNat p (num n) = padicValNat p (den n) + padicValNat p (a n) := by
    have h_Fact : Fact p.Prime := ⟨hp⟩
    rw [eq, padicValNat.mul (den_ne_zero n) h_a]
  constructor
  · intro h
    have : 1 ≤ padicValNat p (a n) := by
      have h1 : 1 ≤ (a n).factorization p := (hp.dvd_iff_one_le_factorization h_a).mp h
      rw [Nat.factorization_def (a n) hp] at h1
      exact h1
    omega
  · intro h
    have : 1 ≤ padicValNat p (a n) := by omega
    have h2 : p^1 ∣ a n := by
      have h3 : 1 ≤ (a n).factorization p := by
        rw [Nat.factorization_def (a n) hp]
        exact this
      exact (hp.pow_dvd_iff_le_factorization h_a).mpr h3
    rwa [pow_one] at h2

lemma val_strict_ineq {n p : ℕ} (hp : Fact p.Prime) (hn : 0 < n) (h_p : p ≤ n / 3) :
    padicValNat p (den n) < padicValNat p (num n) := by
  rw [val_den_final hp, val_num_final hp]
  apply sum_lt_sum
  · intro e _
    exact sum_k_div_k_le (n / p^e) n
  · use 1
    have h1 : 1 ∈ Icc 1 n := by
      rw [mem_Icc]
      omega
    use h1
    have hp_pos : 0 < p := hp.out.pos
    have h_div : 3 ≤ n / p := val_le_div h_p hp_pos
    have h2 : n / p^1 = n / p := by rw [pow_one]
    rw [h2]
    apply sum_k_div_k_lt (n / p) n h_div
    apply Nat.div_le_self

lemma sum_k_div_k_eq_of_le_2 (x n : ℕ) (hx : x ≤ 2) (hn : x ≤ n) : (Icc 1 n).sum (fun k => k * (x / k)) = x^2 := by
  have eq : (Icc 1 n).sum (fun k => k * (x / k)) = ((Icc 1 n).filter (fun k => k ≤ x)).sum (fun k => k * (x / k)) := by
    apply Eq.symm
    apply sum_subset (filter_subset _ _)
    intro k hk1 hk2
    simp only [mem_filter, hk1, true_and, not_le] at hk2
    have : x / k = 0 := Nat.div_eq_of_lt hk2
    rw [this, mul_zero]
  rw [eq]
  have eq2 : ((Icc 1 n).filter (fun k => k ≤ x)) = Icc 1 x := by
    ext a
    rw [mem_filter, mem_Icc, mem_Icc]
    omega
  rw [eq2]
  have h0 : 0 ≤ x := Nat.zero_le x
  interval_cases x
  · rfl
  · rfl
  · rfl

lemma val_eq_of_le_2 {n p : ℕ} (hp : Fact p.Prime) (hn : 0 < n) (h_p : n / 3 < p) :
    padicValNat p (den n) = padicValNat p (num n) := by
  rw [val_den_final hp, val_num_final hp]
  apply sum_congr rfl
  intro e he
  have h_pos : 0 < p := hp.out.pos
  have h1 : n / p ≤ 2 := by
    apply Nat.lt_succ_iff.mp
    apply Nat.div_lt_of_lt_mul
    have : n / 3 * 3 ≤ n := Nat.div_mul_le_self n 3
    omega
  have h2 : n / p^e ≤ n / p := by
    apply Nat.div_le_div_left
    have h_e : 1 ≤ e := by
      rw [mem_Icc] at he
      exact he.1
    have h_pow : p^1 ≤ p^e := Nat.pow_le_pow_right hp.out.pos h_e
    rwa [pow_one] at h_pow
    positivity
  have hx : n / p^e ≤ 2 := le_trans h2 h1
  have hxn : n / p^e ≤ n := by
    apply Nat.div_le_self
  exact sum_k_div_k_eq_of_le_2 (n / p^e) n hx hxn

theorem oeis_a129365_conjecture_B (n p : ℕ) (hn : 0 < n) (hp : Nat.Prime p) :
  p ∣ a n ↔ p ≤ n / 3 := by
  have h_Fact : Fact p.Prime := ⟨hp⟩
  rw [p_dvd_a_iff n p hp]
  constructor
  · intro h
    by_contra h_contra
    push_neg at h_contra
    have eq := val_eq_of_le_2 h_Fact hn h_contra
    omega
  · intro h
    exact val_strict_ineq h_Fact hn h

theorem oeis_a129365_conjecture_B.disproof : ¬ (type_of% @oeis_a129365_conjecture_B) := sorry
