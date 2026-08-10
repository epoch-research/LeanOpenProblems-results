import FormalConjectures.Util.ProblemImports
open Nat Finset

-- Helper lemmas for the proof of oeis_a129365_conjecture_C

theorem sum_eq_of_zero_on_extra {α : Type*} [AddCommMonoid α] (A B : ℕ) (f : ℕ → α)
    (hf : ∀ x, A < x → x ≤ A + B → f x = 0) :
    ∑ x ∈ Icc 1 (A + B), f x = ∑ x ∈ Icc 1 A, f x := by
  have h1 : Icc 1 (A + B) = Icc 1 A ∪ Ioc A (A + B) := by
    ext x
    simp only [mem_Icc, mem_union, mem_Ioc]
    omega
  rw [h1, sum_union]
  · have h2 : ∑ x ∈ Ioc A (A + B), f x = 0 := by
      rw [sum_eq_zero]
      intro x hx
      rw [mem_Ioc] at hx
      exact hf x hx.1 hx.2
    rw [h2, add_zero]
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Icc] at ha
    rw [mem_Ioc] at hb
    omega

lemma not_dvd_of_range (n p k j : ℕ) (hk : k < p) (hj1 : n * p < j) (hj2 : j ≤ n * p + k) :
    ¬ p ∣ j := by
  intro hp
  rcases hp with ⟨c, rfl⟩
  have h_p_pos : 0 < p := by omega
  have h_n_lt : p * n < p * c := by
    calc p * n = n * p := by ring
    _ < p * c := hj1
  have h_n_lt_c : n < c := lt_of_mul_lt_mul_left h_n_lt (by omega)
  have h_j_lt : p * c < p * (n + 1) := by
    calc p * c ≤ n * p + k := hj2
    _ < n * p + p := by omega
    _ = p * (n + 1) := by ring
  have h_c_lt : c < n + 1 := lt_of_mul_lt_mul_left h_j_lt (by omega)
  omega

lemma factorization_gcd_eq_zero_of_not_dvd (j i p : ℕ) (hj : ¬ p ∣ j) :
    (Nat.gcd j i).factorization p = 0 := by
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hj (dvd_zero p)
  have h_gcd_ne_zero : Nat.gcd j i ≠ 0 := by
    apply Nat.gcd_ne_zero_left hj0
  have h_dvd : Nat.gcd j i ∣ j := Nat.gcd_dvd_left j i
  have h_le_all : (Nat.gcd j i).factorization ≤ j.factorization := by
    rwa [Nat.factorization_le_iff_dvd h_gcd_ne_zero hj0]
  have h_le : (Nat.gcd j i).factorization p ≤ j.factorization p := h_le_all p
  have h_j_fac : j.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hj
  omega

theorem double_sum_eq_of_zero_extra (A B : ℕ) (f : ℕ → ℕ → ℕ)
    (hf1 : ∀ j, A < j → j ≤ A + B → ∀ i, f j i = 0)
    (hf2 : ∀ i, A < i → i ≤ A + B → ∀ j, f j i = 0) :
    ∑ j ∈ Icc 1 (A + B), ∑ i ∈ Icc 1 (A + B), f j i = ∑ j ∈ Icc 1 A, ∑ i ∈ Icc 1 A, f j i := by
  have step1 : ∑ j ∈ Icc 1 (A + B), ∑ i ∈ Icc 1 (A + B), f j i = ∑ j ∈ Icc 1 A, ∑ i ∈ Icc 1 (A + B), f j i := by
    apply sum_eq_of_zero_on_extra A B
    intro j hj1 hj2
    have : ∑ i ∈ Icc 1 (A + B), f j i = 0 := by
      apply sum_eq_zero
      intro i hi
      exact hf1 j hj1 hj2 i
    exact this
  rw [step1]
  have step2 : ∑ j ∈ Icc 1 A, ∑ i ∈ Icc 1 (A + B), f j i = ∑ j ∈ Icc 1 A, ∑ i ∈ Icc 1 A, f j i := by
    apply sum_congr rfl
    intro j hj
    apply sum_eq_of_zero_on_extra A B
    intro i hi1 hi2
    exact hf2 i hi1 hi2 j
  rw [step2]

lemma factorization_U_eq_sum (m : ℕ) (p : ℕ) :
    ((Icc 1 m).prod fun j => (Icc 1 m).prod fun i => Nat.gcd j i).factorization p =
    ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, (Nat.gcd j i).factorization p := by
  rw [Nat.factorization_prod]
  · simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    apply sum_congr rfl
    intro j hj
    rw [Nat.factorization_prod]
    · simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    · intro i hi
      have : Nat.gcd j i ≠ 0 := by
        rw [mem_Icc] at hj hi
        apply Nat.gcd_ne_zero_left
        omega
      exact this
  · intro j hj
    rw [prod_ne_zero_iff]
    intro i hi
    rw [mem_Icc] at hj hi
    apply Nat.gcd_ne_zero_left
    omega

theorem U_factorization_eq (n p k : ℕ) (hk : k < p) :
    ((Icc 1 (n * p + k)).prod fun j => (Icc 1 (n * p + k)).prod fun i => Nat.gcd j i).factorization p =
    ((Icc 1 (n * p)).prod fun j => (Icc 1 (n * p)).prod fun i => Nat.gcd j i).factorization p := by
  rw [factorization_U_eq_sum, factorization_U_eq_sum]
  apply double_sum_eq_of_zero_extra (n * p) k (fun j i => (Nat.gcd j i).factorization p)
  · intro j hj1 hj2 i
    apply factorization_gcd_eq_zero_of_not_dvd
    apply not_dvd_of_range n p k j hk hj1 hj2
  · intro i hi1 hi2 j
    rw [Nat.gcd_comm]
    apply factorization_gcd_eq_zero_of_not_dvd
    apply not_dvd_of_range n p k i hk hi1 hi2

lemma factorization_D_eq_sum (m : ℕ) (p : ℕ) :
    ((Icc 1 m).prod fun i => (factorial (m / i)) ^ i).factorization p =
    ∑ i ∈ Icc 1 m, i * (factorial (m / i)).factorization p := by
  rw [Nat.factorization_prod]
  · simp only [Finsupp.coe_finset_sum, Finset.sum_apply]
    apply sum_congr rfl
    intro i hi
    rw [Nat.factorization_pow]
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
  · intro i hi
    apply pow_ne_zero
    apply factorial_ne_zero

lemma div_eq_zero_or_one (n p k i : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) (hi : n * p < i) :
    (n * p + k) / i = 0 ∨ (n * p + k) / i = 1 := by
  have h_p_ge2 : 2 ≤ p := hp.two_le
  have h_p_le : p ≤ n * p := by
    calc p = 1 * p := by ring
    _ ≤ n * p := Nat.mul_le_mul_right p hn
  have h_lt2 : n * p + k < 2 * i := by omega
  have h_div_lt : (n * p + k) / i < 2 := by
    rw [Nat.div_lt_iff_lt_mul]
    · exact h_lt2
    · omega
  have h_div_ge : 0 ≤ (n * p + k) / i := Nat.zero_le _
  omega

lemma factorization_factorial_div_eq_zero (n p k i : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) (hi : n * p < i) :
    (factorial ((n * p + k) / i)).factorization p = 0 := by
  rcases div_eq_zero_or_one n p k i hn hp hk hi with h | h
  · rw [h]
    simp
  · rw [h]
    simp

lemma add_mul_div_self (n p k : ℕ) (hp : p.Prime) (hk : k < p) : (n * p + k) / p = n := by
  have h_pos : p > 0 := hp.pos
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ h_pos]
  rw [Nat.div_eq_of_lt hk, zero_add]

lemma div_mul_div_self (n p k i r : ℕ) (hp : p.Prime) (hk : k < p) (hr : r ≥ 1) :
    (n * p + k) / (i * p^r) = (n * p) / (i * p^r) := by
  have h_pos : p > 0 := hp.pos
  have h_pow : p^r = p^(r - 1) * p := by
    have h_r : r = r - 1 + 1 := (Nat.sub_add_cancel hr).symm
    conv_lhs => rw [h_r]
    rw [pow_succ]
  have h_mul : i * p^r = p * (i * p^(r - 1)) := by
    rw [h_pow]
    ring
  rw [h_mul]
  simp_rw [← Nat.div_div_eq_div_mul]
  rw [add_mul_div_self n p k hp hk]
  rw [Nat.mul_div_cancel _ h_pos]

lemma term_by_term_eq (n p k i : ℕ) (hp : p.Prime) (hk : k < p) (Y : ℕ) :
    ∀ r ∈ Ico 1 (Y + 1), ((n * p + k) / i) / p^r = ((n * p) / i) / p^r := by
  intro r hr
  rw [mem_Ico] at hr
  rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
  rw [div_mul_div_self n p k i r hp hk (by omega)]

lemma sum_factorial_eq (n p k i : ℕ) (hp : p.Prime) (hk : k < p) :
    (factorial ((n * p + k) / i)).factorization p = (factorial ((n * p) / i)).factorization p := by
  have h_log : log p ((n * p + k) / i) < ((n * p + k) / i) + 1 := by
    have := Nat.log_le_self p ((n * p + k) / i)
    omega
  have h_log2 : log p ((n * p) / i) < ((n * p + k) / i) + 1 := by
    have h1 := Nat.log_le_self p ((n * p) / i)
    have h2 : (n * p) / i ≤ (n * p + k) / i := Nat.div_le_div_right (by omega)
    omega
  rw [Nat.factorization_factorial hp h_log, Nat.factorization_factorial hp h_log2]
  apply sum_congr rfl
  exact term_by_term_eq n p k i hp hk _

theorem D_factorization_eq (n p k : ℕ) (hn : 0 < n) (hp : p.Prime) (hk : k < p) :
    ((Icc 1 (n * p + k)).prod fun i => (factorial ((n * p + k) / i)) ^ i).factorization p =
    ((Icc 1 (n * p)).prod fun i => (factorial ((n * p) / i)) ^ i).factorization p := by
  rw [factorization_D_eq_sum, factorization_D_eq_sum]
  have step1 : ∑ i ∈ Icc 1 (n * p + k), i * (factorial ((n * p + k) / i)).factorization p =
               ∑ i ∈ Icc 1 (n * p), i * (factorial ((n * p + k) / i)).factorization p := by
    apply sum_eq_of_zero_on_extra (n * p) k
    intro i hi1 hi2
    rw [factorization_factorial_div_eq_zero n p k i hn hp hk hi1, mul_zero]
  rw [step1]
  apply sum_congr rfl
  intro i hi
  rw [sum_factorial_eq n p k i hp hk]

lemma div_div_comm (m i j : ℕ) : (m / i) / j = (m / j) / i := by
  rw [Nat.div_div_eq_div_mul, mul_comm, ← Nat.div_div_eq_div_mul]

lemma sum_i_div_le_sq (m N : ℕ) (hN : N ≤ m) :
    ∑ i ∈ Icc 1 m, i * (N / i) ≤ N^2 := by
  have h_split : ∑ i ∈ Icc 1 m, i * (N / i) = ∑ i ∈ Icc 1 N, i * (N / i) := by
    have h_eq : m = N + (m - N) := (Nat.add_sub_of_le hN).symm
    nth_rw 1 [h_eq]
    apply sum_eq_of_zero_on_extra N (m - N)
    intro i hi1 hi2
    have : N / i = 0 := Nat.div_eq_of_lt hi1
    rw [this, mul_zero]
  rw [h_split]
  have h_le : ∑ i ∈ Icc 1 N, i * (N / i) ≤ ∑ i ∈ Icc 1 N, N := by
    apply sum_le_sum
    intro i hi
    apply Nat.mul_div_le
  have h_const : ∑ i ∈ Icc 1 N, N = N^2 := by
    rw [sum_const, card_Icc, smul_eq_mul, sq]
    have h_card : N + 1 - 1 = N := by omega
    rw [h_card]
  omega

theorem sum_boole_le_eq_self (x M : ℕ) (h : x ≤ M) :
    ∑ s ∈ Ico 1 (M + 1), (if s ≤ x then 1 else 0) = x := by
  have h1 : Ico 1 (M + 1) = Ico 1 (x + 1) ∪ Ico (x + 1) (M + 1) := by
    rw [Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [h1, sum_union]
  · have s1 : ∑ s ∈ Ico 1 (x + 1), (if s ≤ x then 1 else 0) = ∑ s ∈ Ico 1 (x + 1), 1 := by
      apply sum_congr rfl
      intro s hs
      rw [mem_Ico] at hs
      have : s ≤ x := by omega
      simp [this]
    have s2 : ∑ s ∈ Ico (x + 1) (M + 1), (if s ≤ x then 1 else 0) = ∑ s ∈ Ico (x + 1) (M + 1), 0 := by
      apply sum_congr rfl
      intro s hs
      rw [mem_Ico] at hs
      have : ¬ s ≤ x := by omega
      simp [this]
    rw [s1, s2, sum_const, sum_const, smul_eq_mul, mul_one, smul_eq_mul, mul_zero, add_zero]
    rw [card_Ico, add_tsub_cancel_right]
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega

lemma factorization_le_self (x q : ℕ) : x.factorization q ≤ x := by
  by_cases h : x.factorization q = 0
  · rw [h]
    omega
  · have hx : x ≠ 0 := by
      rintro rfl
      simp at h
    have hq : q.Prime := by
      by_contra h_not
      have := Nat.factorization_eq_zero_of_not_prime x h_not
      exact h this
    have hdvd : q ^ (x.factorization q) ∣ x := by
      rw [hq.pow_dvd_iff_le_factorization hx]
    have hle1 : q ^ (x.factorization q) ≤ x := Nat.le_of_dvd (Nat.pos_of_ne_zero hx) hdvd
    have hle2 : x.factorization q ≤ q ^ (x.factorization q) := (Nat.lt_pow_self hq.one_lt).le
    omega

lemma sum_le_sum_of_subset (A B : ℕ) (h : A ≤ B) (f : ℕ → ℕ) :
    ∑ s ∈ Ico 1 (A + 1), f s ≤ ∑ s ∈ Ico 1 (B + 1), f s := by
  have h_eq : Ico 1 (B + 1) = Ico 1 (A + 1) ∪ Ico (A + 1) (B + 1) := by
    rw [Ico_union_Ico_eq_Ico (by omega) (by omega)]
  rw [h_eq, sum_union]
  · omega
  · rw [disjoint_iff_ne]
    intro a ha b hb hab
    rw [mem_Ico] at ha hb
    omega

theorem sum_div_boole_eq_div (n d : ℕ) :
    ∑ j ∈ Icc 1 n, (if d ∣ j then 1 else 0) = n / d := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by
      ext x
      simp only [mem_Icc, mem_insert]
      omega
    rw [h1, sum_insert (by simp), ih, add_comm, Nat.succ_div]

lemma sum_boole_gcd_eq (m q s : ℕ) :
    ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, (if q^s ∣ Nat.gcd j i then 1 else 0) = (m / q^s)^2 := by
  have h_eq : ∀ j i, (if q^s ∣ Nat.gcd j i then 1 else 0) = (if q^s ∣ j then 1 else 0) * (if q^s ∣ i then 1 else 0) := by
    intro j i
    simp only [Nat.dvd_gcd_iff]
    split_ifs <;> omega
  simp_rw [h_eq, ← mul_sum, ← sum_mul, sum_div_boole_eq_div]
  ring

lemma U_factorization_eq_sum_sq (m : ℕ) (q : ℕ) (hq : q.Prime) :
    ((Icc 1 m).prod fun j => (Icc 1 m).prod fun i => Nat.gcd j i).factorization q =
    ∑ s ∈ Ico 1 (m + 1), (m / q^s)^2 := by
  rw [factorization_U_eq_sum]
  have h_gcd : ∀ a ∈ Icc 1 m, ∀ x ∈ Icc 1 m,
      (Nat.gcd a x).factorization q = ∑ s ∈ Ico 1 (m + 1), (if q^s ∣ Nat.gcd a x then 1 else 0) := by
    intro a ha x hx
    rw [mem_Icc] at ha hx
    have h_le_m : (Nat.gcd a x).factorization q ≤ m := by
      have h1 := factorization_le_self (Nat.gcd a x) q
      have h_x_pos : 0 < x := hx.1
      have h2 : Nat.gcd a x ≤ x := by
        rw [Nat.gcd_comm]
        exact Nat.gcd_le_left a h_x_pos
      omega
    rw [← sum_boole_le_eq_self _ m h_le_m]
    apply sum_congr rfl
    intro s hs
    rw [mem_Ico] at hs
    have h_gcd_nz : Nat.gcd a x ≠ 0 := by
      apply Nat.gcd_ne_zero_left
      omega
    simp only [hq.pow_dvd_iff_le_factorization h_gcd_nz]
  have h_rw : ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, (Nat.gcd j i).factorization q =
              ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, ∑ s ∈ Ico 1 (m + 1), (if q^s ∣ Nat.gcd j i then 1 else 0) := by
    apply sum_congr rfl
    intro j hj
    apply sum_congr rfl
    intro i hi
    exact h_gcd j hj i hi
  rw [h_rw]
  have h_comm1 : (∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, ∑ s ∈ Ico 1 (m + 1), (if q^s ∣ Nat.gcd j i then 1 else 0)) =
                 (∑ j ∈ Icc 1 m, ∑ s ∈ Ico 1 (m + 1), ∑ i ∈ Icc 1 m, (if q^s ∣ Nat.gcd j i then 1 else 0)) := by
    apply sum_congr rfl
    intro j hj
    rw [sum_comm]
  have h_comm2 : (∑ j ∈ Icc 1 m, ∑ s ∈ Ico 1 (m + 1), ∑ i ∈ Icc 1 m, (if q^s ∣ Nat.gcd j i then 1 else 0)) =
                 (∑ s ∈ Ico 1 (m + 1), ∑ j ∈ Icc 1 m, ∑ i ∈ Icc 1 m, (if q^s ∣ Nat.gcd j i then 1 else 0)) := by
    rw [sum_comm]
  rw [h_comm1, h_comm2]
  apply sum_congr rfl
  intro s hs
  exact sum_boole_gcd_eq m q s

lemma D_le_U_factorization (m : ℕ) (q : ℕ) :
    ((Icc 1 m).prod fun i => (factorial (m / i)) ^ i).factorization q ≤
    ((Icc 1 m).prod fun j => (Icc 1 m).prod fun i => Nat.gcd j i).factorization q := by
  by_cases hq : q.Prime
  · rw [factorization_D_eq_sum, U_factorization_eq_sum_sq m q hq]
    have h_le : ∑ i ∈ Icc 1 m, i * (factorial (m / i)).factorization q ≤
                ∑ i ∈ Icc 1 m, ∑ s ∈ Ico 1 (m + 1), i * ((m / i) / q^s) := by
      apply sum_le_sum
      intro i hi
      rw [Nat.factorization_factorial hq]
      · simp_rw [mul_sum]
        apply sum_le_sum_of_subset (m / i) m _ (fun s => i * ((m / i) / q^s))
        apply Nat.div_le_self
      · have h_log : log q (m / i) < m / i + 1 := by
          have := Nat.log_le_self q (m / i)
          omega
        exact h_log
    have h_comm : ∑ i ∈ Icc 1 m, ∑ s ∈ Ico 1 (m + 1), i * ((m / i) / q^s) =
                  ∑ s ∈ Ico 1 (m + 1), ∑ i ∈ Icc 1 m, i * ((m / i) / q^s) := by
      rw [sum_comm]
    have h_div : ∑ s ∈ Ico 1 (m + 1), ∑ i ∈ Icc 1 m, i * ((m / i) / q^s) ≤
                 ∑ s ∈ Ico 1 (m + 1), (m / q^s)^2 := by
      apply sum_le_sum
      intro s hs
      have h_rw : ∑ i ∈ Icc 1 m, i * ((m / i) / q^s) = ∑ i ∈ Icc 1 m, i * ((m / q^s) / i) := by
        apply sum_congr rfl
        intro i hi
        rw [div_div_comm]
      rw [h_rw]
      apply sum_i_div_le_sq
      apply Nat.div_le_self
    omega
  · have h1 : ((Icc 1 m).prod fun i => (factorial (m / i)) ^ i).factorization q = 0 :=
      Nat.factorization_eq_zero_of_not_prime _ hq
    rw [h1]
    omega

lemma D_dvd_U (m : ℕ) :
    ((Icc 1 m).prod fun i => (factorial (m / i)) ^ i) ∣
    ((Icc 1 m).prod fun j => (Icc 1 m).prod fun i => Nat.gcd j i) := by
  by_cases hm : m = 0
  · subst hm
    simp
  · have hD0 : ((Icc 1 m).prod fun i => (factorial (m / i)) ^ i) ≠ 0 := by
      rw [prod_ne_zero_iff]
      intro i hi
      apply pow_ne_zero
      apply factorial_ne_zero
    have hU0 : ((Icc 1 m).prod fun j => (Icc 1 m).prod fun i => Nat.gcd j i) ≠ 0 := by
      rw [prod_ne_zero_iff]
      intro j hj
      rw [prod_ne_zero_iff]
      intro i hi
      rw [mem_Icc] at hj hi
      apply Nat.gcd_ne_zero_left
      omega
    rw [← Nat.factorization_le_iff_dvd hD0 hU0]
    intro q
    exact D_le_U_factorization m q

/--
A129365: $a(n) = A092287(n)/A129364(n)$.
$$a(n) = \frac{\prod_{j=1}^n \prod_{k=1}^n \gcd(j,k)}{\prod_{k=1}^n (\lfloor n/k \rfloor!)^k}$$
-/
def a (n : ℕ) : ℕ :=
  -- A092287(n) = Product Product gcd(j,k)
  let numerator : ℕ := (Icc 1 n).prod fun j => (Icc 1 n).prod fun k => Nat.gcd j k
  -- A129364(n) = Product (floor(n/k)!)^k
  let denominator : ℕ := (Icc 1 n).prod fun k => (Nat.factorial (n / k)) ^ k

  -- The conjecture guarantees that the division is exact.
  numerator / denominator

-- Helper function for A004125, b(n) = floor(n/2)
def b (n : ℕ) : ℕ := n / 2

-- Note: `(m.factorization p)` is the exponent of p in the prime factorization of m,
-- corresponding to ordp(m, p).

/--
oeis_a129365_conjecture_C: For each positive integer n and prime p,
ordp(a(n*p),p) = ordp(a(n*p+1),p) = ordp(a(n*p+2),p) = ... = ordp(a(n*p+p-1),p).
-/
theorem oeis_a129365_conjecture_C (n p k : ℕ) (hn : 0 < n) (hp : Nat.Prime p) (hk : k < p) :
    (a (n * p)).factorization p = (a (n * p + k)).factorization p := by
  change (((Icc 1 (n * p)).prod fun j => (Icc 1 (n * p)).prod fun i => Nat.gcd j i) /
          ((Icc 1 (n * p)).prod fun i => (factorial ((n * p) / i)) ^ i)).factorization p =
         (((Icc 1 (n * p + k)).prod fun j => (Icc 1 (n * p + k)).prod fun i => Nat.gcd j i) /
          ((Icc 1 (n * p + k)).prod fun i => (factorial ((n * p + k) / i)) ^ i)).factorization p
  rw [Nat.factorization_div (D_dvd_U (n * p)), Nat.factorization_div (D_dvd_U (n * p + k))]
  rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
  rw [U_factorization_eq n p k hk, D_factorization_eq n p k hn hp hk]

