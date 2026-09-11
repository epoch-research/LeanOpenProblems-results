import FormalConjectures.Util.ProblemImports

open Nat Finset Int

/--
A301376: Number of ways to write $n^2$ as $x^2 + y^2 + z^2 + w^2$ with $x,y,z,w$ nonnegative integers and $z \le w$ such that $x^2-(3y)^2 = 4^k$ for some $k = 0,1,2,\ldots$.
-/
noncomputable def a (n : ℕ) : ℕ :=
  let R := Finset.range (n + 1)
  -- Search space for (x, y, z, w) as nested products ((x, y), (z, w)).
  let domain : Finset ((ℕ × ℕ) × (ℕ × ℕ)) := (R.product R).product (R.product R)

  Finset.card $ domain.filter (λ p : (ℕ × ℕ) × (ℕ × ℕ) =>
    let x := p.fst.fst; let y := p.fst.snd;
    let z := p.snd.fst; let w := p.snd.snd;

    x^2 + y^2 + z^2 + w^2 = n^2 ∧
    z ≤ w ∧
    -- The condition: x^2 - (3*y)^2 = 4^k. Casted to ℤ for subtraction, then compared to 4^k (which is in ℕ and implicitly cast to ℤ).
    -- Bounded existence: 4^k <= n^2 implies k is bounded by log_4(n^2). range (n + 1) is a safe upper bound for k.
    (∃ k ∈ Finset.range (n + 1), (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
  )


/-!
### Provable structure

* `Good n` is the bound-free form of the predicate defining `a n`; `a_pos_iff` shows
  `0 < a n ↔ Good n` (the range bounds in the definition are automatically satisfied).
* `Good.double` is the lift `n ↦ 2n` (scale `x,y,z,w` by `2`, `k ↦ k+1`), so by strong
  induction the conjecture reduces to odd `n` (`Good.of_pos`).
* `classify` determines all solutions of `x² − (3y)² = 4ᵏ`: either `(x,y) = (2ᵏ,0)` or
  `(x,y) = 2^(a-1)·(4ʲ+1, (4ʲ-1)/3)` with `k = a + j`.

Hence the conjecture is equivalent to: for every odd `n`, one of the numbers
`n² − 4ᵏ`, `n² − 4^(a-1)·((4ʲ+1)² + ((4ʲ-1)/3)²)` is a sum of two squares.
This is the genuinely open core (`Good.of_odd`); it has been verified numerically for all
`n ≤ 10⁹`.
-/

/-- The "unbounded" form of the predicate. -/
def Good (n : ℕ) : Prop :=
  ∃ x y z w k : ℕ, x^2 + y^2 + z^2 + w^2 = n^2 ∧ z ≤ w ∧ (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)

lemma le_of_sq_le_sq' {u n : ℕ} (h : u^2 ≤ n^2) : u ≤ n := by
  nlinarith [Nat.lt_or_ge u (n+1)]

lemma pow_le_of_four_pow_le {k n : ℕ} (_hn : 0 < n) (h : 4^k ≤ n^2) : k ≤ n := by
  have h1 : 2^k ≤ n := by
    have : (2^k)^2 = 4^k := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    exact le_of_sq_le_sq' (this ▸ h)
  have h2 : k < 2^k := Nat.lt_two_pow_self
  omega

theorem a_pos_iff (n : ℕ) (hn : 0 < n) : 0 < a n ↔ Good n := by
  unfold a
  simp only
  rw [Finset.card_pos]
  constructor
  · rintro ⟨⟨⟨x, y⟩, ⟨z, w⟩⟩, hp⟩
    rw [Finset.mem_filter] at hp
    obtain ⟨_, h1, h2, k, _, h3⟩ := hp
    exact ⟨x, y, z, w, k, h1, h2, h3⟩
  · rintro ⟨x, y, z, w, k, h1, h2, h3⟩
    refine ⟨⟨⟨x, y⟩, ⟨z, w⟩⟩, ?_⟩
    rw [Finset.mem_filter]
    have hx : x ≤ n := le_of_sq_le_sq' (by nlinarith)
    have hy : y ≤ n := le_of_sq_le_sq' (by nlinarith)
    have hz : z ≤ n := le_of_sq_le_sq' (by nlinarith)
    have hw : w ≤ n := le_of_sq_le_sq' (by nlinarith)
    have hk : k ≤ n := by
      apply pow_le_of_four_pow_le hn
      have : (4:ℤ)^k ≤ (n:ℤ)^2 := by
        rw [← h3]; nlinarith [sq_nonneg (y:ℤ), sq_nonneg (z:ℤ), sq_nonneg (w:ℤ)]
      exact_mod_cast this
    refine ⟨?_, h1, h2, k, ?_, h3⟩
    · simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_range]
      omega
    · simp only [Finset.mem_range]; omega

/-- Doubling lift. -/
theorem Good.double {n : ℕ} (h : Good n) : Good (2 * n) := by
  obtain ⟨x, y, z, w, k, h1, h2, h3⟩ := h
  refine ⟨2*x, 2*y, 2*z, 2*w, k+1, ?_, by omega, ?_⟩
  · nlinarith [h1]
  · push_cast; rw [pow_succ]; linear_combination 4 * h3

theorem Good.one : Good 1 := ⟨1, 0, 0, 0, 0, by norm_num, le_rfl, by norm_num⟩

lemma two_pow_pred {s : ℕ} (hs : 0 < s) : 2^s = 2 * 2^(s-1) := by
  rw [← _root_.pow_succ']; congr 1; omega

/-- Classification of nonnegative solutions of `x² − (3y)² = 4ᵏ`. -/
theorem classify {x y k : ℕ} (h : (x:ℤ)^2 - (3 * (y:ℤ))^2 = 4^k) :
    (y = 0 ∧ x = 2^k) ∨
    ∃ a j : ℕ, 1 ≤ a ∧ 1 ≤ j ∧ k = a + j ∧ x = 2^(a-1) * (4^j + 1) ∧ 3 * y = 2^(a-1) * (4^j - 1) := by
  have hxy : 3 * y < x := by
    by_contra hc
    push_neg at hc
    have : (x:ℤ)^2 ≤ (3*(y:ℤ))^2 := by
      have : (x:ℤ) ≤ 3 * y := by exact_mod_cast hc
      nlinarith
    have : (0:ℤ) < 4^k := by positivity
    linarith
  have hprod : (x - 3*y) * (x + 3*y) = 2^(2*k) := by
    have h4 : (4:ℤ)^k = (2:ℤ)^(2*k) := by rw [pow_mul]; norm_num
    rw [h4] at h
    have : ((x - 3*y : ℕ) : ℤ) * ((x + 3*y : ℕ) : ℤ) = ((2^(2*k) : ℕ) : ℤ) := by
      push_cast [hxy.le]
      linear_combination h
    exact_mod_cast this
  have hs : ∃ s, x - 3*y = 2^s := by
    have : (x - 3*y) ∣ 2^(2*k) := Dvd.intro _ hprod
    exact (Nat.dvd_prime_pow Nat.prime_two).1 this |>.imp fun s hs => hs.2
  have ht : ∃ t, x + 3*y = 2^t := by
    have : (x + 3*y) ∣ 2^(2*k) := Dvd.intro_left _ hprod
    exact (Nat.dvd_prime_pow Nat.prime_two).1 this |>.imp fun s hs => hs.2
  obtain ⟨s, hs⟩ := hs
  obtain ⟨t, ht⟩ := ht
  have hst : s + t = 2 * k := by
    rw [hs, ht, ← pow_add] at hprod
    exact Nat.pow_right_injective le_rfl hprod
  have hsle : s ≤ t := by
    have : 2^s ≤ 2^t := by rw [← hs, ← ht]; omega
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  rcases Nat.eq_or_lt_of_le hsle with heq | hlt
  · subst heq
    left
    have hy : y = 0 := by omega
    subst hy
    have hk : s = k := by omega
    subst hk
    exact ⟨rfl, by omega⟩
  · right
    have h6 : 6 * y = 2^t - 2^s := by omega
    have hpos : 0 < s := by
      by_contra h0
      push_neg at h0
      have hs0 : s = 0 := by omega
      subst hs0
      have hodd : Odd (2^t - 1) := by
        have h1 : 1 ≤ 2^t := Nat.one_le_two_pow
        have := (Nat.even_pow (n := t) (m := 2)).2 ⟨even_two, (by omega : t ≠ 0)⟩
        exact Nat.Even.sub_odd h1 this odd_one
      have heven : Even (2^t - 1) := by
        have : 2^t - 1 = 6 * y := by rw [h6]; simp
        rw [this]; exact ⟨3*y, by ring⟩
      exact (Nat.not_even_iff_odd.2 hodd) heven
    obtain ⟨m, rfl⟩ : ∃ m, t = s + m := ⟨t - s, by omega⟩
    have hm : 0 < m := by omega
    have h6' : 3 * y = 2^(s-1) * (2^m - 1) := by
      have h2s := two_pow_pred hpos
      have h1 : 1 ≤ 2^m := Nat.one_le_two_pow
      have hh : 6 * y = 2^s * (2^m - 1) := by
        rw [Nat.mul_sub, mul_one, ← pow_add]; exact h6
      rw [h2s, mul_assoc] at hh
      omega
    have h3 : 3 ∣ 2^m - 1 := by
      have : 3 ∣ 2^(s-1) * (2^m - 1) := ⟨y, by rw [← h6']⟩
      exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.pow_right _ (by norm_num)) this)
    obtain ⟨j, hj⟩ : ∃ j, m = 2 * j := by
      rcases Nat.even_or_odd m with ⟨j, hj⟩ | ⟨j, hj⟩
      · exact ⟨j, by omega⟩
      · exfalso
        subst hj
        have h1 : 1 ≤ 2^(2*j+1) := Nat.one_le_two_pow
        have h2 : 2^(2*j+1) % 3 = 2 := by
          rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]; norm_num
        omega
    subst hj
    have hj : 1 ≤ j := by omega
    refine ⟨s, j, hpos, hj, by omega, ?_, ?_⟩
    · have h2s := two_pow_pred hpos
      have h4 : (4:ℕ)^j = 2^(2*j) := by rw [pow_mul]; norm_num
      have hpa : 2^(s + 2*j) = 2^s * 2^(2*j) := pow_add _ _ _
      rw [h4]
      have hx2 : 2 * x = 2^s + 2^(s+2*j) := by omega
      rw [hpa, h2s] at hx2
      nlinarith
    · rw [h6']; congr 1; rw [pow_mul]; norm_num


lemma three_dvd_four_pow_sub_one (j : ℕ) : 3 ∣ 4^j - 1 := by
  have : 4^j % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have h1 : 1 ≤ 4^j := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- Explicit form of `Good`: one of the numbers `n² − 4ᵏ` or
`n² − 4^(a-1)·((4ʲ+1)² + ((4ʲ-1)/3)²)` is a sum of two squares. -/
theorem Good_iff (n : ℕ) : Good n ↔
    (∃ k z w : ℕ, z ≤ w ∧ 4^k + z^2 + w^2 = n^2) ∨
    (∃ a j z w : ℕ, 1 ≤ a ∧ 1 ≤ j ∧ z ≤ w ∧
      (2^(a-1) * (4^j + 1))^2 + (2^(a-1) * ((4^j - 1) / 3))^2 + z^2 + w^2 = n^2) := by
  constructor
  · rintro ⟨x, y, z, w, k, h1, h2, h3⟩
    rcases classify h3 with ⟨rfl, rfl⟩ | ⟨a, j, ha, hj, rfl, rfl, hy⟩
    · left
      refine ⟨k, z, w, h2, ?_⟩
      rw [← h1, ← pow_mul, mul_comm, pow_mul]; norm_num
    · right
      refine ⟨a, j, z, w, ha, hj, h2, ?_⟩
      have : y = 2^(a-1) * ((4^j - 1) / 3) := by
        obtain ⟨t, ht⟩ := three_dvd_four_pow_sub_one j
        rw [ht, Nat.mul_div_cancel_left _ (by norm_num)]
        rw [ht] at hy
        linarith [hy]
      rw [← this]; exact h1
  · rintro (⟨k, z, w, h2, h1⟩ | ⟨a, j, z, w, ha, hj, h2, h1⟩)
    · refine ⟨2^k, 0, z, w, k, ?_, h2, ?_⟩
      · rw [← h1, ← pow_mul, mul_comm, pow_mul]; norm_num
      · push_cast; rw [← pow_mul, mul_comm, pow_mul]; norm_num
    · refine ⟨2^(a-1) * (4^j + 1), 2^(a-1) * ((4^j - 1) / 3), z, w, a + j, h1, h2, ?_⟩
      obtain ⟨t, ht⟩ := three_dvd_four_pow_sub_one j
      have h4 : 4^j = 3 * t + 1 := by
        have : 1 ≤ 4^j := Nat.one_le_pow _ _ (by norm_num); omega
      rw [ht, Nat.mul_div_cancel_left _ (by norm_num)]
      push_cast
      have h4' : ((4:ℤ)^j) = 3 * t + 1 := by exact_mod_cast h4
      have hpow : (2:ℤ)^(a-1) * 2 = 2^a := by
        rw [← pow_succ]; congr 1; omega
      have : (4:ℤ)^(a+j) = (2^a)^2 * 4^j := by
        rw [pow_add, ← pow_mul, mul_comm a 2, pow_mul]; norm_num
      rw [this, ← hpow, h4']
      ring

/-- The open core (Zhi-Wei Sun's conjecture, verified for `n ≤ 10⁹`): for every odd `n`,
one of the numbers `n² − 4ᵏ`, `n² − 4^(a-1)·((4ʲ+1)² + ((4ʲ-1)/3)²)` is a sum of two squares. -/
theorem core_odd (n : ℕ) (hn : Odd n) :
    (∃ k z w : ℕ, z ≤ w ∧ 4^k + z^2 + w^2 = n^2) ∨
    (∃ a j z w : ℕ, 1 ≤ a ∧ 1 ≤ j ∧ z ≤ w ∧
      (2^(a-1) * (4^j + 1))^2 + (2^(a-1) * ((4^j - 1) / 3))^2 + z^2 + w^2 = n^2) := by
  sorry

theorem Good.of_odd (n : ℕ) (hn : Odd n) : Good n := (Good_iff n).2 (core_odd n hn)

theorem Good.of_pos : ∀ n : ℕ, 0 < n → Good n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.even_or_odd n with he | ho
    · obtain ⟨m, hm⟩ := he
      have hm' : n = 2 * m := by omega
      have : 0 < m := by omega
      rw [hm']
      exact (ih m (by omega) this).double
    · exact Good.of_odd n ho


/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := fun n hn =>
  (a_pos_iff n hn).2 (Good.of_pos n hn)

theorem A301376_conjecture.disproof : ¬ (type_of% @A301376_conjecture) := sorry
