import FormalConjectures.Util.ProblemImports

open Nat BigOperators Finset

def superfactorial (n : ℕ) : ℕ := (Finset.range n).prod fun k => k.factorial

theorem superfactorial_succ (n : ℕ) : superfactorial (n+1) = superfactorial n * n.factorial := by
  unfold superfactorial; rw [Finset.prod_range_succ]

theorem prod_Icc_id (n : ℕ) : ∏ j ∈ Finset.Icc 1 n, j = n.factorial := by
  rw [← Ico_add_one_right_eq_Icc, Finset.prod_Ico_id_eq_factorial]

theorem superfactorial_eq_prod (n : ℕ) :
    superfactorial n = ∏ j ∈ Finset.Icc 1 n, j ^ (n - j) := by
  induction n with
  | zero => simp [superfactorial]
  | succ n ih =>
    rw [superfactorial_succ, ih]
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n+1)]
    rw [Nat.sub_self, pow_zero, mul_one]
    rw [← prod_Icc_id n]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Finset.mem_Icc] at hj
    rw [show n + 1 - j = (n - j) + 1 by omega, pow_succ]

-- Rational cast of superfactorial product formula
theorem superfactorial_eq_prod_rat (n : ℕ) :
    (superfactorial n : ℚ) = ∏ j ∈ Finset.Icc 1 n, (j : ℚ) ^ (n - j) := by
  rw [superfactorial_eq_prod]; push_cast; rfl

-- The "box exponent" function E(j) for plane partition F.
-- pos terms: a, b, c, a+b+c ; neg: a+b, a+c, b+c.  As (X - j) clamped at 0 = (X-j) for j ≤ X else 0.
-- We use ℤ exponents. Define using superfactorial directly instead.

-- F as a rational, via the four superfactorials.
noncomputable def Frat (a b c : ℕ) : ℚ :=
  (superfactorial a * superfactorial b * superfactorial c * superfactorial (a+b+c) : ℚ) /
  (superfactorial (a+b) * superfactorial (a+c) * superfactorial (b+c) : ℚ)

-- superfactorial over an extended range: for M ≥ n, extra factors j^(n-j)=j^0=1
theorem superfactorial_eq_prod_ext (n M : ℕ) (h : n ≤ M) :
    (superfactorial n : ℚ) = ∏ j ∈ Finset.Icc 1 M, (j : ℚ) ^ (n - j) := by
  rw [superfactorial_eq_prod_rat]
  apply Finset.prod_subset
  · intro x hx; simp only [Finset.mem_Icc] at *; omega
  · intro x hx hx2
    simp only [Finset.mem_Icc] at hx hx2
    have : n - x = 0 := by omega
    rw [this, pow_zero]

-- integer box-exponent
def Ebox (a b c j : ℕ) : ℤ :=
  ((a-j:ℕ):ℤ) + ((b-j:ℕ):ℤ) + ((c-j:ℕ):ℤ) + ((a+b+c-j:ℕ):ℤ)
    - ((a+b-j:ℕ):ℤ) - ((a+c-j:ℕ):ℤ) - ((b+c-j:ℕ):ℤ)

theorem Frat_eq_prod (a b c : ℕ) :
    Frat a b c = ∏ j ∈ Finset.Icc 1 (a+b+c), (j : ℚ) ^ (Ebox a b c j) := by
  have hpos : ∀ j ∈ Finset.Icc 1 (a+b+c), (j:ℚ) ≠ 0 := by
    intro j hj; simp only [Finset.mem_Icc] at hj
    exact_mod_cast (by omega : j ≠ 0)
  unfold Frat
  rw [superfactorial_eq_prod_ext a (a+b+c) (by omega),
      superfactorial_eq_prod_ext b (a+b+c) (by omega),
      superfactorial_eq_prod_ext c (a+b+c) (by omega),
      superfactorial_eq_prod_ext (a+b+c) (a+b+c) (by omega),
      superfactorial_eq_prod_ext (a+b) (a+b+c) (by omega),
      superfactorial_eq_prod_ext (a+c) (a+b+c) (by omega),
      superfactorial_eq_prod_ext (b+c) (a+b+c) (by omega)]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [Ebox]
  have hj0 : (j:ℚ) ≠ 0 := hpos j hj
  rw [zpow_sub₀ hj0, zpow_sub₀ hj0, zpow_sub₀ hj0]
  rw [zpow_add₀ hj0, zpow_add₀ hj0, zpow_add₀ hj0]
  simp only [zpow_natCast]
  ring

-- ∑_{j∈Icc 1 N} (X - j) = ∑_{k∈range X} k  (ℕ), for X ≤ N
theorem sum_sub_eq_range (X N : ℕ) (h : X ≤ N) :
    ∑ j ∈ Finset.Icc 1 N, (X - j) = ∑ k ∈ Finset.range X, k := by
  rw [← Finset.sum_subset (s₁ := Finset.Icc 1 X)]
  · -- ∑_{Icc 1 X}(X-j) = ∑_{range X} k
    apply Finset.sum_nbij' (fun j => X - j) (fun k => X - k)
    · intro j hj; simp only [Finset.mem_Icc] at hj; simp only [Finset.mem_range]; omega
    · intro k hk; simp only [Finset.mem_range] at hk; simp only [Finset.mem_Icc]; omega
    · intro j hj; simp only [Finset.mem_Icc] at hj; omega
    · intro k hk; simp only [Finset.mem_range] at hk; omega
    · intro j hj; rfl
  · intro x hx; simp only [Finset.mem_Icc] at *; omega
  · intro x hx hx2; simp only [Finset.mem_Icc, Finset.mem_Icc] at hx hx2
    have : X - x = 0 := by omega
    exact this

theorem sum_castsub (X N : ℕ) (h : X ≤ N) :
    (2:ℤ) * ∑ j ∈ Finset.Icc 1 N, ((X - j : ℕ):ℤ) = (X:ℤ)*((X:ℤ)-1) := by
  have : ∑ j ∈ Finset.Icc 1 N, ((X - j : ℕ):ℤ) = ((∑ k ∈ Finset.range X, k : ℕ):ℤ) := by
    rw [← sum_sub_eq_range X N h]; push_cast; rfl
  rw [this]
  have h2 := Finset.sum_range_id_mul_two X
  -- (∑ i in range X, i) * 2 = X * (X-1)
  have : ((∑ k ∈ Finset.range X, k : ℕ):ℤ) * 2 = (X:ℤ)*((X:ℤ)-1) := by
    have := congrArg (Nat.cast : ℕ → ℤ) h2
    push_cast at this ⊢
    rcases Nat.eq_zero_or_pos X with hX | hX
    · subst hX; simp
    · rw [Nat.cast_sub (by omega)] at this; push_cast at this; linarith
  linarith

theorem sum_Ebox_zero (a b c : ℕ) :
    ∑ j ∈ Finset.Icc 1 (a+b+c), Ebox a b c j = 0 := by
  have key : (2:ℤ) * ∑ j ∈ Finset.Icc 1 (a+b+c), Ebox a b c j = 0 := by
    unfold Ebox
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    have ea := sum_castsub a (a+b+c) (by omega)
    have eb := sum_castsub b (a+b+c) (by omega)
    have ec := sum_castsub c (a+b+c) (by omega)
    have eabc := sum_castsub (a+b+c) (a+b+c) (by omega)
    have eab := sum_castsub (a+b) (a+b+c) (by omega)
    have eac := sum_castsub (a+c) (a+b+c) (by omega)
    have ebc := sum_castsub (b+c) (a+b+c) (by omega)
    push_cast at ea eb ec eabc eab eac ebc ⊢
    linear_combination ea + eb + ec + eabc - eab - eac - ebc
  linarith

theorem Ebox_scale (p a b c j : ℕ) :
    Ebox (p*a) (p*b) (p*c) (p*j) = p * Ebox a b c j := by
  unfold Ebox
  simp only [← Nat.mul_add, ← Nat.mul_sub]
  push_cast
  ring

lemma prod_zpow_eq_zpow_sum {ι : Type*} (s : Finset ι) (a : ℚ) (ha : a ≠ 0) (f : ι → ℤ) :
    ∏ i ∈ s, a ^ (f i) = a ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.sum_insert hx, ih, ← zpow_add₀ ha]

-- the p∣j part of the product equals Frat a b c ^ p
theorem prod_pdvd (p a b c : ℕ) (hp : 0 < p) :
    ∏ j ∈ (Finset.Icc 1 (p*a+p*b+p*c)).filter (fun j => p ∣ j),
      (j:ℚ) ^ Ebox (p*a) (p*b) (p*c) j = Frat a b c ^ p := by
  have hN : p*a+p*b+p*c = p*(a+b+c) := by ring
  -- reindex j = p*i
  have himg : (Finset.Icc 1 (p*a+p*b+p*c)).filter (fun j => p ∣ j)
      = (Finset.Icc 1 (a+b+c)).image (fun i => p*i) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, k, rfl⟩
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at h1)
      have hk2 : k ≤ a+b+c := by rw [hN] at h2; exact Nat.le_of_mul_le_mul_left h2 hp
      exact ⟨k, ⟨hk1, hk2⟩, by ring⟩
    · rintro ⟨i, ⟨hi1, hi2⟩, rfl⟩
      have h1 : 1 ≤ p*i := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      have h2 : p*i ≤ p*a+p*b+p*c := by rw [hN]; exact Nat.mul_le_mul_left p hi2
      exact ⟨⟨h1, h2⟩, ⟨i, rfl⟩⟩
  rw [himg, Finset.prod_image (by intro x _ y _ h; exact Nat.eq_of_mul_eq_mul_left hp h)]
  -- now ∏_{i∈Icc 1 (a+b+c)} (p*i)^{Ebox(pa,pb,pc,p*i)}
  have step : ∀ i ∈ Finset.Icc 1 (a+b+c),
      ((p*i:ℕ):ℚ) ^ Ebox (p*a) (p*b) (p*c) (p*i)
        = (p:ℚ) ^ (p * Ebox a b c i) * ((i:ℚ) ^ Ebox a b c i) ^ p := by
    intro i hi
    rw [Ebox_scale]
    rw [show ((p*i:ℕ):ℚ) = (p:ℚ)*(i:ℚ) by push_cast; ring]
    rw [mul_zpow]
    congr 1
    rw [mul_comm (p:ℤ) (Ebox a b c i), zpow_mul, zpow_natCast]
  rw [Finset.prod_congr rfl step]
  rw [Finset.prod_mul_distrib, Finset.prod_pow]
  -- second factor = Frat^p
  have hFrat : ∏ i ∈ Finset.Icc 1 (a+b+c), (i:ℚ) ^ Ebox a b c i = Frat a b c := (Frat_eq_prod a b c).symm
  rw [hFrat]
  -- first factor = 1
  have hp0 : (p:ℚ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
  rw [prod_zpow_eq_zpow_sum _ _ hp0]
  have : ∑ i ∈ Finset.Icc 1 (a+b+c), p * Ebox a b c i = 0 := by
    rw [← Finset.mul_sum, sum_Ebox_zero, mul_zero]
  rw [this, zpow_zero, one_mul]

-- The unit product P (over p∤j)
noncomputable def Punit (p a b c : ℕ) : ℚ :=
  ∏ j ∈ (Finset.Icc 1 (p*a+p*b+p*c)).filter (fun j => ¬ p ∣ j),
    (j:ℚ) ^ Ebox (p*a) (p*b) (p*c) j

theorem Frat_reduction (p a b c : ℕ) (hp : 0 < p) :
    Frat (p*a) (p*b) (p*c) = Punit p a b c * Frat a b c ^ p := by
  have h := Frat_eq_prod (p*a) (p*b) (p*c)
  rw [show p*a+p*b+p*c = p*a+p*b+p*c from rfl] at h
  -- (p*a)+(p*b)+(p*c) is the upper bound
  have hsum : p*a + p*b + p*c = (p*a) + (p*b) + (p*c) := rfl
  rw [Frat_eq_prod]
  rw [← Finset.prod_filter_mul_prod_filter_not (Finset.Icc 1 (p*a+p*b+p*c)) (fun j => p ∣ j)]
  rw [prod_pdvd p a b c hp]
  rw [Punit]
  ring

-- ===== SKELETON: top-level assembly =====
-- Spec's F
def F (a b c : ℕ) : ℕ :=
  superfactorial a * superfactorial b * superfactorial c * superfactorial (a+b+c) /
  (superfactorial (a+b) * superfactorial (a+c) * superfactorial (b+c))

theorem superfactorial_pos (n : ℕ) : 0 < superfactorial n := by
  unfold superfactorial
  apply Finset.prod_pos
  intro i _; exact Nat.factorial_pos i

-- H(n,Q) = ∑_{m<n} ⌊m/Q⌋
def Hf (n Q : ℕ) : ℕ := ∑ m ∈ Finset.range n, m / Q

-- superfactorial factorization at prime q equals ∑_i Hf n (q^i)
theorem superfactorial_factorization (n q : ℕ) (hq : q.Prime) (b : ℕ) (hb : Nat.log q n < b) :
    (superfactorial n).factorization q = ∑ i ∈ Finset.Ico 1 b, Hf n (q ^ i) := by
  unfold superfactorial Hf
  rw [Nat.factorization_prod (by intro m _; exact (Nat.factorial_pos m).ne')]
  simp only [Finsupp.finset_sum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  simp only [Finset.mem_range] at hm
  rw [Nat.factorization_factorial hq (b := b) (by
    calc Nat.log q m ≤ Nat.log q n := Nat.log_mono_right (by omega)
      _ < b := hb)]

theorem Hf_succ (n Q : ℕ) : Hf (n+1) Q = Hf n Q + n / Q := by
  unfold Hf; rw [Finset.sum_range_succ]

theorem two_Q_Hf (n Q : ℕ) (hQ : 0 < Q) :
    2 * (Q:ℤ) * (Hf n Q : ℤ) = (n:ℤ)*((n:ℤ)-(Q:ℤ)) + ((n % Q : ℕ):ℤ)*((Q:ℤ)-((n%Q:ℕ):ℤ)) := by
  induction n with
  | zero => simp [Hf]
  | succ n ih =>
    rw [Hf_succ]
    have hdm : Q * (n / Q) + n % Q = n := Nat.div_add_mod n Q
    have e2 : (Q:ℤ) * ((n / Q : ℕ):ℤ) = (n:ℤ) - ((n % Q : ℕ):ℤ) := by
      have : (Q:ℤ) * ((n/Q:ℕ):ℤ) + ((n%Q:ℕ):ℤ) = (n:ℤ) := by
        rw [← Nat.cast_mul, ← Nat.cast_add, hdm]
      linarith
    have hmlt : n % Q < Q := Nat.mod_lt n hQ
    rcases Nat.lt_or_ge (n % Q + 1) Q with h | h
    · have hQ2 : 1 < Q := by omega
      have e3 : (n+1) % Q = n % Q + 1 := by
        rw [Nat.add_mod, Nat.mod_eq_of_lt hQ2, Nat.mod_eq_of_lt h]
      rw [e3]
      push_cast [e3] at ih e2 ⊢
      linear_combination ih + 2 * e2
    · have hQe : n % Q + 1 = Q := by omega
      have hdvd : Q ∣ (n+1) := ⟨n/Q+1, by rw [Nat.mul_add, Nat.mul_one]; omega⟩
      have e3 : (n+1) % Q = 0 := by
        obtain ⟨k, hk⟩ := hdvd; rw [hk, Nat.mul_mod_right]
      rw [e3]
      push_cast at ih e2 ⊢
      have hr : (↑n % ↑Q : ℤ) = (Q:ℤ) - 1 := by
        have h2 : n % Q = Q - 1 := by omega
        have hc : (↑n % ↑Q : ℤ) = ((n % Q : ℕ) : ℤ) := (Int.natCast_mod n Q).symm
        rw [hc, h2, Nat.cast_sub (by omega : 1 ≤ Q), Nat.cast_one]
      rw [hr] at ih e2
      linear_combination ih + 2 * e2

set_option maxHeartbeats 1000000 in
theorem resineq_core (Q x y z i j k m : ℤ) (hQ : 0 < Q)
    (hx : 0 ≤ x) (hx' : x < Q) (hy : 0 ≤ y) (hy' : y < Q) (hz : 0 ≤ z) (hz' : z < Q)
    (hpb : 0 ≤ x + y - Q * i) (hpb' : x + y - Q * i < Q)
    (hqb : 0 ≤ x + z - Q * j) (hqb' : x + z - Q * j < Q)
    (htb : 0 ≤ y + z - Q * k) (htb' : y + z - Q * k < Q)
    (hsb : 0 ≤ x + y + z - Q * m) (hsb' : x + y + z - Q * m < Q)
    (hi0 : 0 ≤ i) (hi1 : i ≤ 1) (hj0 : 0 ≤ j) (hj1 : j ≤ 1)
    (hk0 : 0 ≤ k) (hk1 : k ≤ 1) (hm0 : 0 ≤ m) (hm1 : m ≤ 2) :
    (x+y-Q*i)*(Q-(x+y-Q*i)) + (x+z-Q*j)*(Q-(x+z-Q*j)) + (y+z-Q*k)*(Q-(y+z-Q*k)) ≤
      x*(Q-x) + y*(Q-y) + z*(Q-z) + (x+y+z-Q*m)*(Q-(x+y+z-Q*m)) := by
  interval_cases i <;> interval_cases j <;> interval_cases k <;> interval_cases m <;>
    nlinarith [hx, hx', hy, hy', hz, hz', hQ]

-- residue/carry identity: ((a+b)%Q : ℤ) = a%Q + b%Q - Q*((a%Q+b%Q)/Q)
theorem mod_add_carry (a b Q : ℕ) :
    ((((a+b) % Q : ℕ)):ℤ) = ((a%Q:ℕ):ℤ) + ((b%Q:ℕ):ℤ) - (Q:ℤ) * (((a%Q+b%Q)/Q : ℕ):ℤ) := by
  have h1 : (a+b) % Q = (a%Q + b%Q) % Q := by rw [Nat.add_mod]
  rw [h1]
  have h2 : Q * ((a%Q+b%Q)/Q) + (a%Q+b%Q)%Q = a%Q+b%Q := Nat.div_add_mod _ _
  have hc : ((Q * ((a%Q+b%Q)/Q) + (a%Q+b%Q)%Q : ℕ):ℤ) = ((a%Q+b%Q : ℕ):ℤ) := by exact_mod_cast h2
  push_cast at hc ⊢
  linarith

set_option maxHeartbeats 1000000 in
theorem Hf_ineq (a b c Q : ℕ) (hQ : 0 < Q) :
    Hf (a+b) Q + Hf (a+c) Q + Hf (b+c) Q ≤ Hf a Q + Hf b Q + Hf c Q + Hf (a+b+c) Q := by
  rw [← Nat.cast_le (α := ℤ)]
  push_cast
  have hQz : (0:ℤ) < Q := by exact_mod_cast hQ
  have Ta := two_Q_Hf a Q hQ
  have Tb := two_Q_Hf b Q hQ
  have Tc := two_Q_Hf c Q hQ
  have Tabc := two_Q_Hf (a+b+c) Q hQ
  have Tab := two_Q_Hf (a+b) Q hQ
  have Tac := two_Q_Hf (a+c) Q hQ
  have Tbc := two_Q_Hf (b+c) Q hQ
  -- carries (in explicit form)
  have hab := mod_add_carry a b Q
  have hac := mod_add_carry a c Q
  have hbc := mod_add_carry b c Q
  have habc : ((((a+b+c) % Q : ℕ)):ℤ)
      = ((a%Q:ℕ):ℤ) + ((b%Q:ℕ):ℤ) + ((c%Q:ℕ):ℤ) - (Q:ℤ) * ((((a%Q+b%Q+c%Q))/Q : ℕ):ℤ) := by
    have h1 : (a+b+c) % Q = (a%Q + b%Q + c%Q) % Q :=
      (Nat.ModEq.add (Nat.ModEq.add (Nat.mod_modEq a Q) (Nat.mod_modEq b Q)) (Nat.mod_modEq c Q)).symm
    rw [h1]
    have h2 : Q * ((a%Q+b%Q+c%Q)/Q) + (a%Q+b%Q+c%Q)%Q = a%Q+b%Q+c%Q := Nat.div_add_mod _ _
    have hc : ((Q * ((a%Q+b%Q+c%Q)/Q) + (a%Q+b%Q+c%Q)%Q : ℕ):ℤ) = ((a%Q+b%Q+c%Q : ℕ):ℤ) := by
      exact_mod_cast h2
    push_cast at hc ⊢; linarith
  set x := ((a%Q:ℕ):ℤ) with hxdef
  set y := ((b%Q:ℕ):ℤ) with hydef
  set z := ((c%Q:ℕ):ℤ) with hzdef
  -- bounds for residues
  have hx0 : 0 ≤ x := by positivity
  have hxlt : x < Q := by rw [hxdef]; exact_mod_cast Nat.mod_lt a hQ
  have hy0 : 0 ≤ y := by positivity
  have hylt : y < Q := by rw [hydef]; exact_mod_cast Nat.mod_lt b hQ
  have hz0 : 0 ≤ z := by positivity
  have hzlt : z < Q := by rw [hzdef]; exact_mod_cast Nat.mod_lt c hQ
  set i := (((a%Q+b%Q)/Q : ℕ):ℤ) with hidef
  set j := (((a%Q+c%Q)/Q : ℕ):ℤ) with hjdef
  set k := (((b%Q+c%Q)/Q : ℕ):ℤ) with hkdef
  set m := ((((a%Q+b%Q+c%Q))/Q : ℕ):ℤ) with hmdef
  have hi0 : 0 ≤ i := by positivity
  have hi1 : i ≤ 1 := by
    have : (a%Q+b%Q)/Q < 2 := Nat.div_lt_of_lt_mul (by have:=Nat.mod_lt a hQ; have:=Nat.mod_lt b hQ; omega)
    rw [hidef]; exact_mod_cast Nat.lt_succ_iff.mp this
  have hj0 : 0 ≤ j := by positivity
  have hj1 : j ≤ 1 := by
    have : (a%Q+c%Q)/Q < 2 := Nat.div_lt_of_lt_mul (by have:=Nat.mod_lt a hQ; have:=Nat.mod_lt c hQ; omega)
    rw [hjdef]; exact_mod_cast Nat.lt_succ_iff.mp this
  have hk0 : 0 ≤ k := by positivity
  have hk1 : k ≤ 1 := by
    have : (b%Q+c%Q)/Q < 2 := Nat.div_lt_of_lt_mul (by have:=Nat.mod_lt b hQ; have:=Nat.mod_lt c hQ; omega)
    rw [hkdef]; exact_mod_cast Nat.lt_succ_iff.mp this
  have hm0 : 0 ≤ m := by positivity
  have hm1 : m ≤ 2 := by
    have : (a%Q+b%Q+c%Q)/Q < 3 := Nat.div_lt_of_lt_mul (by have:=Nat.mod_lt a hQ; have:=Nat.mod_lt b hQ; have:=Nat.mod_lt c hQ; omega)
    rw [hmdef]; exact_mod_cast Nat.lt_succ_iff.mp this
  -- residue ranges (they equal actual mods, hence in [0,Q))
  have pab0 : 0 ≤ x+y-Q*i := by rw [← hab]; positivity
  have pab1 : x+y-Q*i < Q := by rw [← hab]; exact_mod_cast Nat.mod_lt (a+b) hQ
  have pac0 : 0 ≤ x+z-Q*j := by rw [← hac]; positivity
  have pac1 : x+z-Q*j < Q := by rw [← hac]; exact_mod_cast Nat.mod_lt (a+c) hQ
  have pbc0 : 0 ≤ y+z-Q*k := by rw [← hbc]; positivity
  have pbc1 : y+z-Q*k < Q := by rw [← hbc]; exact_mod_cast Nat.mod_lt (b+c) hQ
  have ps0 : 0 ≤ x+y+z-Q*m := by rw [← habc]; positivity
  have ps1 : x+y+z-Q*m < Q := by rw [← habc]; exact_mod_cast Nat.mod_lt (a+b+c) hQ
  have R := resineq_core Q x y z i j k m hQz hx0 hxlt hy0 hylt hz0 hzlt
    pab0 pab1 pac0 pac1 pbc0 pbc1 ps0 ps1 hi0 hi1 hj0 hj1 hk0 hk1 hm0 hm1
  -- now combine. rewrite residues in T's
  rw [hab] at Tab; rw [hac] at Tac; rw [hbc] at Tbc; rw [habc] at Tabc
  -- 2Q*(RHS - LHS) ≥ 0
  have key : (0:ℤ) ≤ 2*Q*(((Hf a Q:ℤ)+(Hf b Q:ℤ)+(Hf c Q:ℤ)+(Hf (a+b+c) Q:ℤ))
              - ((Hf (a+b) Q:ℤ)+(Hf (a+c) Q:ℤ)+(Hf (b+c) Q:ℤ))) := by
    have expand : 2*(Q:ℤ)*(((Hf a Q:ℤ)+(Hf b Q:ℤ)+(Hf c Q:ℤ)+(Hf (a+b+c) Q:ℤ))
              - ((Hf (a+b) Q:ℤ)+(Hf (a+c) Q:ℤ)+(Hf (b+c) Q:ℤ)))
        = (x*(Q-x)+y*(Q-y)+z*(Q-z)+(x+y+z-Q*m)*(Q-(x+y+z-Q*m)))
        - ((x+y-Q*i)*(Q-(x+y-Q*i))+(x+z-Q*j)*(Q-(x+z-Q*j))+(y+z-Q*k)*(Q-(y+z-Q*k))) := by
      push_cast at Ta Tb Tc Tab Tac Tbc Tabc
      linear_combination Ta + Tb + Tc + Tabc - Tab - Tac - Tbc
    rw [expand]; linarith [R]
  have h2Q : (0:ℤ) < 2*↑Q := by linarith
  have hD : (0:ℤ) ≤ (((Hf a Q:ℤ)+(Hf b Q:ℤ)+(Hf c Q:ℤ)+(Hf (a+b+c) Q:ℤ))
              - ((Hf (a+b) Q:ℤ)+(Hf (a+c) Q:ℤ)+(Hf (b+c) Q:ℤ))) :=
    le_of_mul_le_mul_left (by rw [mul_zero]; exact key) h2Q
  linarith [hD]

theorem F_den_dvd_num (a b c : ℕ) :
    superfactorial (a+b) * superfactorial (a+c) * superfactorial (b+c) ∣
    superfactorial a * superfactorial b * superfactorial c * superfactorial (a+b+c) := by
  have sfne : ∀ n, superfactorial n ≠ 0 := fun n => (superfactorial_pos n).ne'
  rw [← Nat.factorization_le_iff_dvd
    (Nat.mul_ne_zero (Nat.mul_ne_zero (sfne _) (sfne _)) (sfne _))
    (Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (sfne _) (sfne _)) (sfne _)) (sfne _))]
  rw [Finsupp.le_iff]
  intro q hq
  by_cases hqp : q.Prime
  · set B := Nat.log q (a+b+c) + 1 with hBdef
    have hbnd : ∀ n, n ≤ a+b+c → Nat.log q n < B := by
      intro n hn; calc Nat.log q n ≤ Nat.log q (a+b+c) := Nat.log_mono_right hn
        _ < B := by omega
    have lhs_eq : (superfactorial (a+b) * superfactorial (a+c) * superfactorial (b+c)).factorization q
        = ∑ i ∈ Finset.Ico 1 B, (Hf (a+b) (q^i) + Hf (a+c) (q^i) + Hf (b+c) (q^i)) := by
      rw [Nat.factorization_mul (Nat.mul_ne_zero (sfne _) (sfne _)) (sfne _),
          Nat.factorization_mul (sfne _) (sfne _)]
      simp only [Finsupp.add_apply]
      rw [superfactorial_factorization _ _ hqp _ (hbnd _ (by omega)),
          superfactorial_factorization _ _ hqp _ (hbnd _ (by omega)),
          superfactorial_factorization _ _ hqp _ (hbnd _ (by omega))]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    have rhs_eq : (superfactorial a * superfactorial b * superfactorial c * superfactorial (a+b+c)).factorization q
        = ∑ i ∈ Finset.Ico 1 B, (Hf a (q^i) + Hf b (q^i) + Hf c (q^i) + Hf (a+b+c) (q^i)) := by
      rw [Nat.factorization_mul (Nat.mul_ne_zero (Nat.mul_ne_zero (sfne _) (sfne _)) (sfne _)) (sfne _),
          Nat.factorization_mul (Nat.mul_ne_zero (sfne _) (sfne _)) (sfne _),
          Nat.factorization_mul (sfne _) (sfne _)]
      simp only [Finsupp.add_apply]
      rw [superfactorial_factorization _ _ hqp _ (hbnd _ (by omega)),
          superfactorial_factorization _ _ hqp _ (hbnd _ (by omega)),
          superfactorial_factorization _ _ hqp _ (hbnd _ (by omega)),
          superfactorial_factorization _ _ hqp _ (hbnd _ (by omega))]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [lhs_eq, rhs_eq]
    apply Finset.sum_le_sum
    intro i hi
    simp only [Finset.mem_Ico] at hi
    exact Hf_ineq a b c (q^i) (pow_pos hqp.pos i)
  · simp [Nat.factorization_eq_zero_of_not_prime _ hqp]

-- integrality: (F a b c : ℚ) = Frat a b c
theorem F_eq_Frat (a b c : ℕ) : (F a b c : ℚ) = Frat a b c := by
  unfold F Frat
  rw [Nat.cast_div (F_den_dvd_num a b c)]
  · push_cast; ring
  · have h1 := superfactorial_pos (a+b)
    have h2 := superfactorial_pos (a+c)
    have h3 := superfactorial_pos (b+c)
    push_cast
    positivity

-- F nonneg integer so Frat ≥ 0 valuation:
theorem Frat_pos (a b c : ℕ) : 0 < Frat a b c := by
  unfold Frat
  apply _root_.div_pos
  · have := superfactorial_pos a
    have := superfactorial_pos b
    have := superfactorial_pos c
    have := superfactorial_pos (a+b+c)
    positivity
  · have := superfactorial_pos (a+b)
    have := superfactorial_pos (a+c)
    have := superfactorial_pos (b+c)
    positivity

-- CORE (p odd): padicValRat bound
theorem core_odd (p A B C : ℕ) (hp : p.Prime) (hodd : p ≠ 2) (hA : 0 < A) :
    (4 * (1 + min (padicValNat p A) (min (padicValNat p B) (padicValNat p C))) : ℤ)
      ≤ padicValRat p (Punit p A B C - 1) := by sorry
