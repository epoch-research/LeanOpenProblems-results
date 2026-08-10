import FormalConjectures.Util.ProblemImports

open Rat Nat Finset

def IsPIntegral (p : ℕ) (q : ℚ) : Prop :=
  ¬ p ∣ q.den

lemma isPIntegral_add {p : ℕ} (hp : Nat.Prime p) {x y : ℚ}
    (hx : IsPIntegral p x) (hy : IsPIntegral p y) : IsPIntegral p (x + y) := by
  intro h
  have h_dvd := Rat.add_den_dvd x y
  have h_p_dvd : p ∣ x.den * y.den := h.trans h_dvd
  rcases hp.dvd_mul.mp h_p_dvd with h1 | h2
  · exact hx h1
  · exact hy h2

lemma isPIntegral_sub {p : ℕ} (hp : Nat.Prime p) {x y : ℚ}
    (hx : IsPIntegral p x) (hy : IsPIntegral p y) : IsPIntegral p (x - y) := by
  intro h
  have h_dvd := Rat.sub_den_dvd x y
  have h_p_dvd : p ∣ x.den * y.den := h.trans h_dvd
  rcases hp.dvd_mul.mp h_p_dvd with h1 | h2
  · exact hx h1
  · exact hy h2

lemma isPIntegral_mul {p : ℕ} (hp : Nat.Prime p) {x y : ℚ}
    (hx : IsPIntegral p x) (hy : IsPIntegral p y) : IsPIntegral p (x * y) := by
  intro h
  have h_dvd := Rat.mul_den_dvd x y
  have h_p_dvd : p ∣ x.den * y.den := h.trans h_dvd
  rcases hp.dvd_mul.mp h_p_dvd with h1 | h2
  · exact hx h1
  · exact hy h2

lemma isPIntegral_natCast (p : ℕ) (hp : Nat.Prime p) (n : ℕ) : IsPIntegral p (n : ℚ) := by
  intro h
  have : (n : ℚ).den = 1 := Rat.den_natCast n
  rw [this] at h
  have : p ≤ 1 := Nat.le_of_dvd (by decide) h
  have : p > 1 := hp.one_lt
  omega

axiom isPIntegral_div_coprime {p : ℕ} (hp : Nat.Prime p) {x : ℚ} (hx : IsPIntegral p x)
    {m : ℕ} (hm : Nat.Coprime p m) (hm0 : m ≠ 0) : IsPIntegral p (x / (m : ℚ))

lemma isPIntegral_sum {α : Type*} {p : ℕ} (hp : Nat.Prime p) (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, IsPIntegral p (f x)) : IsPIntegral p (∑ x ∈ s, f x) := by
  haveI := Classical.decEq α
  induction' s using Finset.induction with x s hx ih
  · simp only [Finset.sum_empty]
    exact isPIntegral_natCast p hp 0
  · simp only [Finset.sum_insert hx]
    apply isPIntegral_add hp
    · exact h x (Finset.mem_insert_self x s)
    · apply ih
      intro y hy
      exact h y (Finset.mem_insert_of_mem hy)

axiom bernoulli_identity (p k : ℕ) :
    ((k + 1 : ℚ) * (p : ℚ) * bernoulli k) =
      (k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k) -
        ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))

lemma term_eq_choose (k i : ℕ) (hi : i < k) :
    ((k + 1).choose i : ℚ) / (k + 1 : ℚ) = (k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ) := by
  have h1 : ((k.choose i * (k + 1) : ℕ) : ℚ) = (((k + 1).choose i * (k + 1 - i) : ℕ) : ℚ) := by
    congr 1
    rw [Nat.choose_mul_succ_eq]
  push_cast at h1
  have h2 : (k + 1 : ℚ) ≠ 0 := by positivity
  have h3 : ((k + 1 - i : ℕ) : ℚ) ≠ 0 := by
    have : k + 1 - i > 0 := by omega
    positivity
  rw [div_eq_div_iff h2 h3]
  exact h1.symm

lemma term_eq_choose_rearranged (k i : ℕ) (p : ℕ) (hi : i < k) :
    bernoulli i * ((k + 1).choose i : ℚ) * (p : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ) =
      (p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ)) := by
  have h1 : ((k + 1).choose i : ℚ) / (k + 1 : ℚ) = (k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ) := term_eq_choose k i hi
  have h_pow : (p : ℚ) ^ (k + 1 - i) = (p : ℚ) * (p : ℚ) ^ (k - i) := by
    have : k + 1 - i = 1 + (k - i) := by omega
    rw [this, pow_add, pow_one]
  rw [h_pow]
  calc
    bernoulli i * ((k + 1).choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - i)) / (k + 1 : ℚ)
      = (bernoulli i * (p : ℚ) * (p : ℚ) ^ (k - i)) * (((k + 1).choose i : ℚ) / (k + 1 : ℚ)) := by ring
    _ = (bernoulli i * (p : ℚ) * (p : ℚ) ^ (k - i)) * ((k.choose i : ℚ) / ((k + 1 - i : ℕ) : ℚ)) := by rw [h1]
    _ = (p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ)) := by ring

lemma bernoulli_identity_divided (p k : ℕ) (hk : k > 0) :
    (p : ℚ) * bernoulli k =
      (∑ x ∈ range p, (x : ℚ) ^ k) -
        ∑ i ∈ range k, ((p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) := by
  have h_nz : (k + 1 : ℚ) ≠ 0 := by positivity
  have h_id := bernoulli_identity p k
  have h_div : ((k + 1 : ℚ) * (p : ℚ) * bernoulli k) / (k + 1 : ℚ) =
      ((k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) := by
    rw [h_id]
  have h_lhs : ((k + 1 : ℚ) * (p : ℚ) * bernoulli k) / (k + 1 : ℚ) = (p : ℚ) * bernoulli k := by
    calc
      _ = (k + 1 : ℚ) * ((p : ℚ) * bernoulli k) / (k + 1 : ℚ) := by ring
      _ = (p : ℚ) * bernoulli k := by rw [mul_div_cancel_left₀ _ h_nz]
  have h_rhs : ((k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) =
      (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) := by
    calc
      _ = ((k + 1 : ℚ) * (∑ x ∈ range p, (x : ℚ) ^ k)) / (k + 1 : ℚ) - (∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) := by rw [sub_div]
      _ = (∑ x ∈ range p, (x : ℚ) ^ k) - (∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i))) / (k + 1 : ℚ) := by rw [mul_div_cancel_left₀ _ h_nz]
      _ = (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, (bernoulli i * ((k + 1).choose i) * (p : ℚ) ^ (k + 1 - i) / (k + 1 : ℚ)) := by rw [sum_div]
      _ = (∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) := by
        congr 1
        apply sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        exact term_eq_choose_rearranged k i p hi
  rw [h_lhs] at h_div
  rw [h_rhs] at h_div
  exact h_div

lemma p_pow_div_m_p_integral (p : ℕ) (hp : Nat.Prime p) (m : ℕ) (hm : m ≥ 2) :
    IsPIntegral p ((p : ℚ) ^ (m - 1) / (m : ℚ)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hpm : p ∣ m
    · rcases hpm with ⟨a, rfl⟩
      have ha0 : a ≠ 0 := by
        rintro rfl
        omega
      have ha_pos : a > 0 := Nat.pos_of_ne_zero ha0
      by_cases ha1 : a = 1
      · subst ha1
        have hp2 : p ≥ 2 := hp.two_le
        have h_goal : (p : ℚ) ^ (p * 1 - 1) / ((p * 1 : ℕ) : ℚ) = (p : ℚ) ^ (p - 1) / (p : ℚ) := by
          have h_m_eq : p * 1 = p := by omega
          rw [h_m_eq]
        rw [h_goal]
        have : ((p : ℚ) ^ (p - 1) / (p : ℚ)) = (p : ℚ) ^ (p - 2) := by
          have : p - 1 = (p - 2) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          rw [mul_div_cancel_right₀ _ h_nz]
        rw [this]
        have : (p : ℚ) ^ (p - 2) = ((p ^ (p - 2) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp (p ^ (p - 2))
      · have ha2 : a ≥ 2 := by omega
        have h_am : a < p * a := by
          have hp2 : p ≥ 2 := hp.two_le
          nlinarith
        have ih_a := ih a h_am ha2
        have h_eq : (p : ℚ) ^ (p * a - 1) / ((p * a : ℕ) : ℚ) = (p : ℚ) ^ (p * a - 2) / (a : ℚ) := by
          have hp2 : p ≥ 2 := hp.two_le
          have : p * a - 1 = (p * a - 2) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          calc
            (p : ℚ) ^ (p * a - 2) * (p : ℚ) / ((p * a : ℕ) : ℚ)
              = (p : ℚ) ^ (p * a - 2) * (p : ℚ) / ((p : ℚ) * (a : ℚ)) := by push_cast; rfl
            _ = (p : ℚ) * (p : ℚ) ^ (p * a - 2) / ((p : ℚ) * (a : ℚ)) := by ring
            _ = (p : ℚ) ^ (p * a - 2) / (a : ℚ) := by rw [mul_div_mul_left _ _ h_nz]
        rw [h_eq]
        have h_sub : p * a - 2 ≥ a - 1 := by
          have hp2 : p ≥ 2 := hp.two_le
          have : p * a ≥ 2 * a := Nat.mul_le_mul_right a hp2
          omega
        have h_eq2 : (p : ℚ) ^ (p * a - 2) / (a : ℚ) = (p : ℚ) ^ (p * a - 2 - (a - 1)) * ((p : ℚ) ^ (a - 1) / (a : ℚ)) := by
          rw [← mul_div_assoc]
          congr 1
          rw [← pow_add]
          congr 1
          omega
        rw [h_eq2]
        apply isPIntegral_mul hp
        · have : (p : ℚ) ^ (p * a - 2 - (a - 1)) = ((p ^ (p * a - 2 - (a - 1)) : ℕ) : ℚ) := by push_cast; rfl
          rw [this]
          exact isPIntegral_natCast p hp _
        · exact ih_a
    · have h_cop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
      apply isPIntegral_div_coprime hp
      · have : (p : ℚ) ^ (m - 1) = ((p ^ (m - 1) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp _
      · exact h_cop
      · omega

lemma p_pow_sub_two_div_m_p_integral (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (m : ℕ) (hm : m ≥ 2) :
    IsPIntegral p ((p : ℚ) ^ (m - 2) / (m : ℚ)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hpm : p ∣ m
    · rcases hpm with ⟨a, rfl⟩
      have ha0 : a ≠ 0 := by
        rintro rfl
        omega
      have ha_pos : a > 0 := Nat.pos_of_ne_zero ha0
      by_cases ha1 : a = 1
      · subst ha1
        have h_goal : (p : ℚ) ^ (p * 1 - 2) / ((p * 1 : ℕ) : ℚ) = (p : ℚ) ^ (p - 2) / (p : ℚ) := by
          have h_m_eq : p * 1 = p := by omega
          rw [h_m_eq]
        rw [h_goal]
        have : ((p : ℚ) ^ (p - 2) / (p : ℚ)) = (p : ℚ) ^ (p - 3) := by
          have : p - 2 = (p - 3) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          rw [mul_div_cancel_right₀ _ h_nz]
        rw [this]
        have : (p : ℚ) ^ (p - 3) = ((p ^ (p - 3) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp (p ^ (p - 3))
      · have ha2 : a ≥ 2 := by omega
        have h_am : a < p * a := by
          nlinarith
        have ih_a := ih a h_am ha2
        have h_eq : (p : ℚ) ^ (p * a - 2) / ((p * a : ℕ) : ℚ) = (p : ℚ) ^ (p * a - 3) / (a : ℚ) := by
          have : p * a - 2 = (p * a - 3) + 1 := by omega
          rw [this, pow_add, pow_one]
          have h_nz : (p : ℚ) ≠ 0 := by positivity
          calc
            (p : ℚ) ^ (p * a - 3) * (p : ℚ) / ((p * a : ℕ) : ℚ)
              = (p : ℚ) ^ (p * a - 3) * (p : ℚ) / ((p : ℚ) * (a : ℚ)) := by push_cast; rfl
            _ = (p : ℚ) * (p : ℚ) ^ (p * a - 3) / ((p : ℚ) * (a : ℚ)) := by ring
            _ = (p : ℚ) ^ (p * a - 3) / (a : ℚ) := by rw [mul_div_mul_left _ _ h_nz]
        rw [h_eq]
        have h_sub : p * a - 3 ≥ a - 2 := by
          have : p * a ≥ 3 * a := Nat.mul_le_mul_right a hp3
          omega
        have h_eq2 : (p : ℚ) ^ (p * a - 3) / (a : ℚ) = (p : ℚ) ^ (p * a - 3 - (a - 2)) * ((p : ℚ) ^ (a - 2) / (a : ℚ)) := by
          rw [← mul_div_assoc]
          congr 1
          rw [← pow_add]
          congr 1
          omega
        rw [h_eq2]
        apply isPIntegral_mul hp
        · have : (p : ℚ) ^ (p * a - 3 - (a - 2)) = ((p ^ (p * a - 3 - (a - 2)) : ℕ) : ℚ) := by push_cast; rfl
          rw [this]
          exact isPIntegral_natCast p hp _
        · exact ih_a
    · have h_cop : Nat.Coprime p m := hp.coprime_iff_not_dvd.mpr hpm
      apply isPIntegral_div_coprime hp
      · have : (p : ℚ) ^ (m - 2) = ((p ^ (m - 2) : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp _
      · exact h_cop
      · omega

lemma p_bernoulli_p_integral (p : ℕ) (hp : Nat.Prime p) (k : ℕ) :
    IsPIntegral p (p * bernoulli k) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k = 0
    · subst hk
      have : (p : ℚ) * bernoulli 0 = (p : ℚ) := by
        rw [bernoulli_zero]
        ring
      rw [this]
      exact isPIntegral_natCast p hp p
    · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk
      rw [bernoulli_identity_divided p k hk_pos]
      apply isPIntegral_sub hp
      · apply isPIntegral_sum hp
        intro x hx
        have : (x : ℚ) ^ k = ((x ^ k : ℕ) : ℚ) := by push_cast; rfl
        rw [this]
        exact isPIntegral_natCast p hp (x ^ k)
      · apply isPIntegral_sum hp
        intro i hi
        rw [Finset.mem_range] at hi
        apply isPIntegral_mul hp
        · exact ih i hi
        · set m := k + 1 - i
          have hm : m ≥ 2 := by
            have : i < k := hi
            omega
          have h_pow_eq : (p : ℚ) ^ (k - i) = (p : ℚ) ^ (m - 1) := by
            congr 1
            omega
          have h_den_eq : ((k + 1 - i : ℕ) : ℚ) = (m : ℚ) := by
            dsimp [m]
          rw [h_pow_eq]
          rw [h_den_eq]
          have h_mul : ((k.choose i : ℚ) * (p : ℚ) ^ (m - 1) / (m : ℚ)) = (k.choose i : ℚ) * ((p : ℚ) ^ (m - 1) / (m : ℚ)) := by ring
          rw [h_mul]
          apply isPIntegral_mul hp
          · exact isPIntegral_natCast p hp (k.choose i)
          · exact p_pow_div_m_p_integral p hp m hm

lemma bernoulli_identity_divided_add_one_div_p (p k : ℕ) (hp : Nat.Prime p) (hk : k > 0) :
    bernoulli k + (1 : ℚ) / (p : ℚ) =
      ((∑ x ∈ range p, (x : ℚ) ^ k) + 1) / (p : ℚ) -
        ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by
  have h_nz : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := hp.ne_zero
    positivity
  have h_id := bernoulli_identity_divided p k hk
  have h_div : bernoulli k = (∑ x ∈ range p, (x : ℚ) ^ k) / (p : ℚ) -
      (∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) := by
    calc
      bernoulli k = ((p : ℚ) * bernoulli k) / (p : ℚ) := by rw [mul_div_cancel_left₀ _ h_nz]
      _ = ((∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) := by rw [h_id]
      _ = _ := by rw [sub_div]
  rw [h_div]
  have h_sum_div : (∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) =
      ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by
    rw [sum_div]
    apply sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    have h_pow : (p : ℚ) ^ (k - i) = (p : ℚ) * (p : ℚ) ^ (k - 1 - i) := by
      have : k - i = 1 + (k - 1 - i) := by omega
      rw [this, pow_add, pow_one]
    rw [h_pow]
    calc
      ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - 1 - i)) / ((k + 1 - i : ℕ) : ℚ)) / (p : ℚ)
        = ((p : ℚ) * bernoulli i) * (((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ)) / (p : ℚ) := by ring
      _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ) / (p : ℚ) := by ring
      _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by rw [mul_div_cancel_right₀ _ h_nz]
  rw [h_sum_div]
  ring

lemma sum_pow_zmod (p i : ℕ) [Fact p.Prime] (hi : i > 0) :
    (∑ x : ZMod p, x ^ i) = if p - 1 ∣ i then -1 else 0 := by
  have h_univ : (∑ x : ZMod p, x ^ i) = ∑ x ∈ univ \ {0}, x ^ i := by
    rw [← sum_sdiff ({0} : Finset (ZMod p)).subset_univ, sum_singleton, zero_pow hi.ne', add_zero]
  let phi := Function.Embedding.mk (fun x : Units (ZMod p) ↦ (x : ZMod p)) Units.val_injective
  have h_map : univ.map phi = univ \ {0} := by
    ext x
    simpa only [mem_map, mem_univ, Function.Embedding.coeFn_mk, true_and, mem_sdiff,
      mem_singleton] using isUnit_iff_ne_zero
  rw [← h_map, sum_map] at h_univ
  rw [h_univ]
  have h_card : Fintype.card (ZMod p) = p := ZMod.card p
  have h_sum := FiniteField.sum_pow_units (ZMod p) i
  rw [h_card] at h_sum
  exact h_sum

lemma bernoulli_p_integral_of_not_dvd (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) (k : ℕ) (hk : k > 0)
    (h_not_dvd : ¬ (p - 1) ∣ k) (ih : ∀ i < k, IsPIntegral p (p * bernoulli i)) :
    IsPIntegral p (bernoulli k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h_nz : (p : ℚ) ≠ 0 := by
    have : p ≠ 0 := hp.ne_zero
    positivity
  have h_div : bernoulli k = (∑ x ∈ range p, (x : ℚ) ^ k) / (p : ℚ) -
      ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by
    calc
      bernoulli k = ((p : ℚ) * bernoulli k) / (p : ℚ) := by rw [mul_div_cancel_left₀ _ h_nz]
      _ = ((∑ x ∈ range p, (x : ℚ) ^ k) - ∑ i ∈ range k, ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - i) / ((k + 1 - i : ℕ) : ℚ))) / (p : ℚ) := by
        rw [bernoulli_identity_divided p k hk]
      _ = _ := by
        rw [sub_div]
        apply congrArg₂ _ rfl
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        rw [Finset.mem_range] at hi
        have h_pow : (p : ℚ) ^ (k - i) = (p : ℚ) * (p : ℚ) ^ (k - 1 - i) := by
          have : k - i = 1 + (k - 1 - i) := by omega
          rw [this, pow_add, pow_one]
        rw [h_pow]
        calc
          ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * ((p : ℚ) * (p : ℚ) ^ (k - 1 - i)) / ((k + 1 - i : ℕ) : ℚ)) / (p : ℚ)
            = ((p : ℚ) * bernoulli i) * (((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ)) / (p : ℚ) := by ring
          _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) * (p : ℚ) / (p : ℚ) := by ring
          _ = ((p : ℚ) * bernoulli i) * ((k.choose i : ℚ) * (p : ℚ) ^ (k - 1 - i) / ((k + 1 - i : ℕ) : ℚ)) := by rw [mul_div_cancel_right₀ _ h_nz]
  rw [h_div]
  apply isPIntegral_sub hp
  · have h_sum_zero : ((∑ x ∈ range p, x ^ k : ℕ) : ZMod p) = 0 := by
      have h_cast : ((∑ x ∈ range p, x ^ k : ℕ) : ZMod p) = ∑ x ∈ range p, (x : ZMod p) ^ k := by
        push_cast
        rfl
      rw [h_cast]
      have h_univ : (∑ x ∈ range p, (x : ZMod p) ^ k) = ∑ x : ZMod p, x ^ k := by
        rcases p with _ | p_pred
        · contradiction
        · have h_fin := Fin.sum_univ_eq_sum_range (n := p_pred + 1) (fun (x : ℕ) ↦ (x : ZMod (p_pred + 1)) ^ k)
          rw [← h_fin]
          apply sum_congr rfl
          intro i hi
          congr 1
          apply Fin.ext
          exact Nat.mod_eq_of_lt i.is_lt
      rw [h_univ]
      rw [sum_pow_zmod (p := p) (i := k) (hi := hk)]
      rw [if_neg h_not_dvd]
    have h_dvd : p ∣ ∑ x ∈ range p, x ^ k := by
      rw [← ZMod.natCast_eq_zero_iff]
      exact h_sum_zero
    rcases h_dvd with ⟨M, hM⟩
    have h_eq_M : ((∑ x ∈ range p, (x : ℚ) ^ k) / (p : ℚ)) = (M : ℚ) := by
      have h_cast2 : (∑ x ∈ range p, (x : ℚ) ^ k) = ((∑ x ∈ range p, x ^ k : ℕ) : ℚ) := by
        exact_mod_cast rfl
      rw [h_cast2]
      rw [hM]
      push_cast
      exact mul_div_cancel_left₀ _ h_nz
    rw [h_eq_M]
    exact isPIntegral_natCast p hp M
  · apply isPIntegral_sum hp
    intro i hi
    rw [Finset.mem_range] at hi
    apply isPIntegral_mul hp
    · exact ih i hi
    · set m := k + 1 - i
      have hm : m ≥ 2 := by omega
      have h_pow_eq : (p : ℚ) ^ (k - 1 - i) = (p : ℚ) ^ (m - 2) := by
        congr 1
        omega
      rw [h_pow_eq]
      have h_mul : ((k.choose i : ℚ) * (p : ℚ) ^ (m - 2) / (m : ℚ)) = (k.choose i : ℚ) * ((p : ℚ) ^ (m - 2) / (m : ℚ)) := by ring
      rw [h_mul]
      apply isPIntegral_mul hp
      · exact isPIntegral_natCast p hp (k.choose i)
      · exact p_pow_sub_two_div_m_p_integral p hp hp3 m hm

lemma p_dvd_den_of_isPIntegral {p : ℕ} (hp : Nat.Prime p) (k : ℕ)
    (h_int : IsPIntegral p (bernoulli k + (1 : ℚ) / (p : ℚ))) : p ∣ (bernoulli k).den := by
  by_contra h_not_dvd
  have h_int_bernoulli : IsPIntegral p (bernoulli k) := h_not_dvd
  have h_diff : IsPIntegral p (bernoulli k + (1 : ℚ) / (p : ℚ) - bernoulli k) := by
    apply isPIntegral_sub hp h_int h_int_bernoulli
  have h_simpl : bernoulli k + (1 : ℚ) / (p : ℚ) - bernoulli k = (1 : ℚ) / (p : ℚ) := by ring
  rw [h_simpl] at h_diff
  have h_den : ((1 : ℚ) / (p : ℚ)).den = p := by
    have hp_pos : p > 0 := hp.pos
    have h_inv : (1 : ℚ) / (p : ℚ) = (p : ℚ)⁻¹ := by ring
    rw [h_inv]
    exact Rat.inv_natCast_den_of_pos hp_pos
  unfold IsPIntegral at h_diff
  rw [h_den] at h_diff
  have h_dvd_self : p ∣ p := dvd_rfl
  contradiction



