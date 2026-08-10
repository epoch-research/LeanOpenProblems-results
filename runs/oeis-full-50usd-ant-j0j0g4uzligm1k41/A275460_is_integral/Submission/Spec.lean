import FormalConjectures.Util.ProblemImports
open Nat Int Rat
open scoped Finset
open Finset

/--
A275460: The rational-valued auxiliary function for the sequence, defined by the recurrence relation:
$a(n) = a(n-1) \cdot \frac{3(9n-7)(9n-5)(9n-2)}{n^2(3n-2)}$ for $n \ge 1$, with $a(0)=1$.
This recurrence is equivalent to the generating function definition.
-/
noncomputable def A275460_rational : ℕ → ℚ
  | 0 => 1
  | Nat.succ k =>
    let n : ℕ := k + 1
    let a_prev : ℚ := A275460_rational k
    let n_q : ℚ := n.cast
    -- Recurrence coefficient: 3 * (9n-7)(9n-5)(9n-2) / (n^2 * (3n-2))
    let num : ℚ := 3 * (9 * n_q - 7) * (9 * n_q - 5) * (9 * n_q - 2)
    let den : ℚ := n_q^2 * (3 * n_q - 2)
    a_prev * (num / den)

/--
A275460: G.f.: $\hphantom{}_3F_2([2/9, 4/9, 7/9], [1/3, 1], 729 x)$.
The coefficients are natural numbers, so we cast the rational result to $\mathbb{N}$.
We use the recurrence definition as it is the simplest algebraic representation of the D-finite series coefficients.
-/
@[simp] noncomputable def a (n : ℕ) : ℕ :=
  (A275460_rational n).floor.toNat

/-! ## Auxiliary integer numerator and denominator -/

/-- Numerator: `3^n * ∏_{j<n} (9j+2)(9j+4)(9j+7)`. -/
def Nnum (n : ℕ) : ℕ := 3^n * ∏ j ∈ Finset.range n, ((9*j+2)*(9*j+4)*(9*j+7))

/-- Denominator: `(n!)^2 * ∏_{j<n} (3j+1)`. -/
def Dden (n : ℕ) : ℕ := (n !)^2 * ∏ j ∈ Finset.range n, (3*j+1)

lemma Dden_pos (n : ℕ) : 0 < Dden n := by
  unfold Dden
  apply Nat.mul_pos
  · exact pow_pos (Nat.factorial_pos n) 2
  · apply Finset.prod_pos; intro j _; positivity

lemma Nnum_pos (n : ℕ) : 0 < Nnum n := by
  unfold Nnum
  apply Nat.mul_pos
  · exact pow_pos (by norm_num) n
  · apply Finset.prod_pos; intro j _; positivity

lemma Nnum_succ (k : ℕ) : Nnum (k+1) = Nnum k * (3 * ((9*k+2)*(9*k+4)*(9*k+7))) := by
  unfold Nnum
  rw [Finset.prod_range_succ, pow_succ]
  ring

lemma Dden_succ (k : ℕ) : Dden (k+1) = Dden k * ((k+1)^2 * (3*k+1)) := by
  unfold Dden
  rw [Finset.prod_range_succ, Nat.factorial_succ]
  ring

/-- The rational sequence equals `Nnum n / Dden n`. -/
lemma rational_eq (n : ℕ) : A275460_rational n = (Nnum n : ℚ) / (Dden n : ℚ) := by
  induction n with
  | zero =>
    have h1 : Nnum 0 = 1 := by decide
    have h2 : Dden 0 = 1 := by decide
    rw [h1, h2]
    norm_num
    rfl
  | succ k ih =>
    rw [A275460_rational]
    rw [ih, Nnum_succ, Dden_succ]
    have hDk : (Dden k : ℚ) ≠ 0 := by exact_mod_cast (Dden_pos k).ne'
    have hk1 : ((k:ℚ)+1) ≠ 0 := by positivity
    have hden : (3 * ((k:ℚ)+1) - 2) ≠ 0 := by
      have : (3 * ((k:ℚ)+1) - 2) = 3*(k:ℚ)+1 := by ring
      rw [this]; positivity
    push_cast
    field_simp
    ring

/-! ## Counting in residue classes -/

/-- count of `j < n` in residue class `a` mod `m`. -/
def cnt (n m a : ℕ) : ℕ := #{j ∈ Finset.range n | j ≡ a [MOD m]}

/-- A member of residue class `a` (with `a < m`) is `≥ a` and `m ∣ j - a`. -/
lemma cong_ge (m a j : ℕ) (ha : a < m) (h : j ≡ a [MOD m]) : a ≤ j ∧ m ∣ j - a := by
  have h1 : a % m = j % m := h.symm
  have haj : a ≤ j := by
    have h2 : a = j % m := by rw [← h1, Nat.mod_eq_of_lt ha]
    rw [h2]; exact Nat.mod_le j m
  exact ⟨haj, (Nat.modEq_iff_dvd' haj).mp h.symm⟩

/-- Monotonicity: smaller representative gives larger (or equal) count. -/
lemma cnt_mono (n m a b : ℕ) (hab : a ≤ b) (hb : b < m) :
    cnt n m b ≤ cnt n m a := by
  unfold cnt
  apply Finset.card_le_card_of_injOn (fun j => j - (b - a))
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hj
    obtain ⟨hjn, hjcong⟩ := hj
    obtain ⟨hjb, hdvd⟩ := cong_ge m b j hb hjcong
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    have heq : j - (b - a) = a + (j - b) := by omega
    rw [heq]
    have : m ∣ (a + (j - b)) - a := by simpa using hdvd
    exact ((Nat.modEq_iff_dvd' (by omega)).mpr this).symm
  · intro x hx y hy hxy
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    obtain ⟨hxb, _⟩ := cong_ge m b x hb hx.2
    obtain ⟨hyb, _⟩ := cong_ge m b y hb hy.2
    simp only at hxy
    omega

/-- `m ∣ c*j+r ↔ j ≡ a [MOD m]` given a solution `a`. -/
lemma dvd_iff_cong (m a c r : ℕ) (hcop : Nat.Coprime c m) (hsol : m ∣ c*a + r) (j : ℕ) :
    m ∣ c*j + r ↔ j ≡ a [MOD m] := by
  constructor
  · intro hj
    have h1 : c*j + r ≡ c*a + r [MOD m] :=
      (Nat.modEq_zero_iff_dvd.mpr hj).trans (Nat.modEq_zero_iff_dvd.mpr hsol).symm
    have h2 : c*j ≡ c*a [MOD m] := Nat.ModEq.add_right_cancel' r h1
    exact Nat.ModEq.cancel_left_of_coprime (Nat.coprime_comm.mp hcop) h2
  · intro hj
    have h1 : c*j ≡ c*a [MOD m] := hj.mul_left c
    have h2 : c*j + r ≡ c*a + r [MOD m] := h1.add_right r
    exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr hsol))

lemma setcount (n m a c r : ℕ) (hcop : Nat.Coprime c m) (hsol : m ∣ c*a + r) :
    #{j ∈ Finset.range n | m ∣ c*j + r} = cnt n m a := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro j _
  exact dvd_iff_cong m a c r hcop hsol j

/-- Combine four solutions to deduce the per-modulus counting inequality. -/
lemma combine (n m a2 a4 a7 a3 : ℕ) (hm : 0 < m)
    (cop9 : Nat.Coprime 9 m) (cop3 : Nat.Coprime 3 m)
    (l2 : a2 < m) (s2 : m ∣ 9*a2+2)
    (l4 : a4 < m) (s4 : m ∣ 9*a4+4)
    (l7 : a7 < m) (s7 : m ∣ 9*a7+7)
    (l3 : a3 < m) (s3 : m ∣ 3*a3+1)
    (hmin : a2 ≤ a3 ∨ a4 ≤ a3 ∨ a7 ≤ a3) :
    2 * #{j ∈ Finset.range n | m ∣ j+1} + #{j ∈ Finset.range n | m ∣ 3*j+1}
      ≤ #{j ∈ Finset.range n | m ∣ 9*j+2} + #{j ∈ Finset.range n | m ∣ 9*j+4} + #{j ∈ Finset.range n | m ∣ 9*j+7} := by
  have e1 : #{j ∈ Finset.range n | m ∣ j+1} = cnt n m (m-1) := by
    have := setcount n m (m-1) 1 1 (Nat.coprime_one_left m) (by
      have : 1*(m-1)+1 = m := by omega
      rw [this])
    simpa using this
  have e3 : #{j ∈ Finset.range n | m ∣ 3*j+1} = cnt n m a3 := setcount n m a3 3 1 cop3 s3
  have e2 : #{j ∈ Finset.range n | m ∣ 9*j+2} = cnt n m a2 := setcount n m a2 9 2 cop9 s2
  have e4 : #{j ∈ Finset.range n | m ∣ 9*j+4} = cnt n m a4 := setcount n m a4 9 4 cop9 s4
  have e7 : #{j ∈ Finset.range n | m ∣ 9*j+7} = cnt n m a7 := setcount n m a7 9 7 cop9 s7
  rw [e1, e2, e3, e4, e7]
  have m2 : cnt n m (m-1) ≤ cnt n m a2 := cnt_mono n m a2 (m-1) (by omega) (by omega)
  have m4 : cnt n m (m-1) ≤ cnt n m a4 := cnt_mono n m a4 (m-1) (by omega) (by omega)
  have m7 : cnt n m (m-1) ≤ cnt n m a7 := cnt_mono n m a7 (m-1) (by omega) (by omega)
  rcases hmin with h | h | h
  · have : cnt n m a3 ≤ cnt n m a2 := cnt_mono n m a2 a3 h l3
    omega
  · have : cnt n m a3 ≤ cnt n m a4 := cnt_mono n m a4 a3 h l3
    omega
  · have : cnt n m a3 ≤ cnt n m a7 := cnt_mono n m a7 a3 h l3
    omega

/-- The per-modulus counting inequality (the heart of the integrality). -/
lemma core (m n : ℕ) (hm : 0 < m) (h3 : ¬ 3 ∣ m) :
    2 * #{j ∈ Finset.range n | m ∣ j+1} + #{j ∈ Finset.range n | m ∣ 3*j+1}
      ≤ #{j ∈ Finset.range n | m ∣ 9*j+2} + #{j ∈ Finset.range n | m ∣ 9*j+4} + #{j ∈ Finset.range n | m ∣ 9*j+7} := by
  have cop3 : Nat.Coprime 3 m := (Nat.prime_three.coprime_iff_not_dvd).mpr h3
  have cop9 : Nat.Coprime 9 m := by have := cop3.pow_left 2; simpa using this
  have ht : m%9=1∨m%9=2∨m%9=4∨m%9=5∨m%9=7∨m%9=8 := by omega
  rcases ht with h|h|h|h|h|h
  · exact combine n m ((2*m-2)/9) ((4*m-4)/9) ((7*m-7)/9) ((1*m-1)/3) hm cop9 cop3 (by omega) ⟨2, by omega⟩ (by omega) ⟨4, by omega⟩ (by omega) ⟨7, by omega⟩ (by omega) ⟨1, by omega⟩ (Or.inl (by omega))
  · exact combine n m ((1*m-2)/9) ((2*m-4)/9) ((8*m-7)/9) ((2*m-1)/3) hm cop9 cop3 (by omega) ⟨1, by omega⟩ (by omega) ⟨2, by omega⟩ (by omega) ⟨8, by omega⟩ (by omega) ⟨2, by omega⟩ (Or.inl (by omega))
  · exact combine n m ((5*m-2)/9) ((1*m-4)/9) ((4*m-7)/9) ((1*m-1)/3) hm cop9 cop3 (by omega) ⟨5, by omega⟩ (by omega) ⟨1, by omega⟩ (by omega) ⟨4, by omega⟩ (by omega) ⟨1, by omega⟩ (Or.inr (Or.inl (by omega)))
  · exact combine n m ((4*m-2)/9) ((8*m-4)/9) ((5*m-7)/9) ((2*m-1)/3) hm cop9 cop3 (by omega) ⟨4, by omega⟩ (by omega) ⟨8, by omega⟩ (by omega) ⟨5, by omega⟩ (by omega) ⟨2, by omega⟩ (Or.inl (by omega))
  · exact combine n m ((8*m-2)/9) ((7*m-4)/9) ((1*m-7)/9) ((1*m-1)/3) hm cop9 cop3 (by omega) ⟨8, by omega⟩ (by omega) ⟨7, by omega⟩ (by omega) ⟨1, by omega⟩ (by omega) ⟨1, by omega⟩ (Or.inr (Or.inr (by omega)))
  · exact combine n m ((7*m-2)/9) ((5*m-4)/9) ((2*m-7)/9) ((2*m-1)/3) hm cop9 cop3 (by omega) ⟨7, by omega⟩ (by omega) ⟨5, by omega⟩ (by omega) ⟨2, by omega⟩ (by omega) ⟨2, by omega⟩ (Or.inr (Or.inr (by omega)))

/-! ## From counts to valuations -/

lemma sum_fact_eq_sum_count (p n b : ℕ) (hp : p.Prime) (g : ℕ → ℕ)
    (hg : ∀ j ∈ Finset.range n, g j ≠ 0) (hb : ∀ j ∈ Finset.range n, g j < p^b) :
    ∑ j ∈ Finset.range n, (g j).factorization p
      = ∑ i ∈ Finset.Ico 1 b, #{j ∈ Finset.range n | p^i ∣ g j} := by
  have key : ∀ j ∈ Finset.range n, (g j).factorization p
      = ∑ i ∈ Finset.Ico 1 b, (if p^i ∣ g j then 1 else 0) := by
    intro j hj
    rw [Nat.factorization_eq_card_pow_dvd_of_lt hp (Nat.pos_of_ne_zero (hg j hj)) (hb j hj),
        Finset.card_filter]
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_filter]

lemma Nnum_factorization (n p : ℕ) :
    (Nnum n).factorization p
      = n * ((3:ℕ).factorization p)
      + ∑ j ∈ Finset.range n, (((9*j+2).factorization p) + ((9*j+4).factorization p) + ((9*j+7).factorization p)) := by
  unfold Nnum
  rw [Nat.factorization_mul (by positivity) (by
        apply Finset.prod_ne_zero_iff.mpr; intro j _; positivity)]
  simp only [Finsupp.add_apply]
  congr 1
  · rw [Nat.factorization_pow]; simp
  · rw [Nat.factorization_prod_apply (by intro j _; positivity)]
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_mul (by positivity) (by positivity)]
    simp [Finsupp.add_apply]

lemma Dden_factorization (n p : ℕ) :
    (Dden n).factorization p
      = 2 * ((n)!).factorization p + ∑ j ∈ Finset.range n, ((3*j+1).factorization p) := by
  unfold Dden
  rw [Nat.factorization_mul (by positivity) (by
        apply Finset.prod_ne_zero_iff.mpr; intro j _; positivity)]
  simp only [Finsupp.add_apply]
  congr 1
  · rw [Nat.factorization_pow]; simp
  · rw [Nat.factorization_prod_apply (by intro j _; positivity)]

/-- The key valuation inequality for primes `p ≠ 3`. -/
lemma prime_ne3_ineq (p n : ℕ) (hp : p.Prime) (hp3 : p ≠ 3) :
    2 * ((n)!).factorization p + ∑ j ∈ Finset.range n, ((3*j+1).factorization p)
      ≤ ∑ j ∈ Finset.range n, ((9*j+2).factorization p)
        + ∑ j ∈ Finset.range n, ((9*j+4).factorization p)
        + ∑ j ∈ Finset.range n, ((9*j+7).factorization p) := by
  set b := 9*n+8 with hbdef
  have hbnd : ∀ x, x ≤ 9*n+7 → x < p^b := by
    intro x hx
    have h2 : b < 2^b := Nat.lt_two_pow_self
    have h3 : (2:ℕ)^b ≤ p^b := Nat.pow_le_pow_left hp.two_le _
    omega
  have hlogb : Nat.log p n < b := by have := Nat.log_le_self p n; omega
  have hfact : ((n)!).factorization p = ∑ i ∈ Finset.Ico 1 b, #{j ∈ Finset.range n | p^i ∣ j+1} := by
    rw [Nat.factorization_factorial hp hlogb]
    apply Finset.sum_congr rfl; intro i _
    rw [Nat.card_multiples n (p^i)]
  have c31 : ∑ j ∈ Finset.range n, ((3*j+1).factorization p)
      = ∑ i ∈ Finset.Ico 1 b, #{j ∈ Finset.range n | p^i ∣ 3*j+1} :=
    sum_fact_eq_sum_count p n b hp _ (fun j _ => by positivity)
      (fun j hj => by rw [Finset.mem_range] at hj; exact hbnd _ (by omega))
  have c92 : ∑ j ∈ Finset.range n, ((9*j+2).factorization p)
      = ∑ i ∈ Finset.Ico 1 b, #{j ∈ Finset.range n | p^i ∣ 9*j+2} :=
    sum_fact_eq_sum_count p n b hp _ (fun j _ => by positivity)
      (fun j hj => by rw [Finset.mem_range] at hj; exact hbnd _ (by omega))
  have c94 : ∑ j ∈ Finset.range n, ((9*j+4).factorization p)
      = ∑ i ∈ Finset.Ico 1 b, #{j ∈ Finset.range n | p^i ∣ 9*j+4} :=
    sum_fact_eq_sum_count p n b hp _ (fun j _ => by positivity)
      (fun j hj => by rw [Finset.mem_range] at hj; exact hbnd _ (by omega))
  have c97 : ∑ j ∈ Finset.range n, ((9*j+7).factorization p)
      = ∑ i ∈ Finset.Ico 1 b, #{j ∈ Finset.range n | p^i ∣ 9*j+7} :=
    sum_fact_eq_sum_count p n b hp _ (fun j _ => by positivity)
      (fun j hj => by rw [Finset.mem_range] at hj; exact hbnd _ (by omega))
  rw [hfact, c31, c92, c94, c97]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i hi
  have hpi : 0 < p^i := pow_pos hp.pos i
  have h3pi : ¬ 3 ∣ p^i := by
    intro hd
    have hdp : (3:ℕ) ∣ p := Nat.prime_three.dvd_of_dvd_pow hd
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp hdp).symm
  have hc := core (p^i) n hpi h3pi
  omega

/-! ## The divisibility and final integrality -/

lemma key_dvd (n : ℕ) : Dden n ∣ Nnum n := by
  rw [← Nat.factorization_le_iff_dvd (Dden_pos n).ne' (Nnum_pos n).ne']
  rw [Finsupp.le_def]
  intro p
  rw [Nnum_factorization, Dden_factorization]
  by_cases hp : p.Prime
  · by_cases hp3 : p = 3
    · subst hp3
      have h3self : (3:ℕ).factorization 3 = 1 := Nat.Prime.factorization_self Nat.prime_three
      have hz1 : ∀ j ∈ Finset.range n, (3*j+1).factorization 3 = 0 := by
        intro j _; apply Nat.factorization_eq_zero_of_not_dvd; omega
      have hz2 : ∀ j ∈ Finset.range n, (9*j+2).factorization 3 = 0 := by
        intro j _; apply Nat.factorization_eq_zero_of_not_dvd; omega
      have hz4 : ∀ j ∈ Finset.range n, (9*j+4).factorization 3 = 0 := by
        intro j _; apply Nat.factorization_eq_zero_of_not_dvd; omega
      have hz7 : ∀ j ∈ Finset.range n, (9*j+7).factorization 3 = 0 := by
        intro j _; apply Nat.factorization_eq_zero_of_not_dvd; omega
      rw [Finset.sum_congr rfl hz1, Finset.sum_const_zero]
      rw [Finset.sum_congr rfl (fun j hj => by
            rw [hz2 j hj, hz4 j hj, hz7 j hj])]
      simp only [Finset.sum_const_zero, h3self, mul_one, add_zero]
      have hle : (n !).factorization 3 ≤ n / (3-1) :=
        Nat.factorization_factorial_le_div_pred Nat.prime_three n
      omega
    · have h3p : (3:ℕ).factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hd
        exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hd)
      rw [h3p, mul_zero, zero_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      exact prime_ne3_ineq p n hp hp3
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/--
oeis_275460_conjecture_0: "Other hypergeometric 'blind spots' for Christol’s conjecture" - (see Bostan link).
The necessary condition for the OEIS definition `A275460_rational n` to correspond to a sequence of natural numbers is that these rational values are always integers.
This specific conjecture states that all coefficients $a(n)$ are integers.
-/
theorem A275460_is_integral (n : ℕ) : (A275460_rational n).isInt := by
  have hD : (Dden n : ℚ) ≠ 0 := by exact_mod_cast (Dden_pos n).ne'
  have hdvd := key_dvd n
  have heq : A275460_rational n = ((Nnum n / Dden n : ℕ) : ℚ) := by
    rw [rational_eq, Nat.cast_div hdvd hD]
  rw [heq]
  show (((Nnum n / Dden n : ℕ) : ℚ).den == 1) = true
  rw [Rat.den_natCast]
  rfl
