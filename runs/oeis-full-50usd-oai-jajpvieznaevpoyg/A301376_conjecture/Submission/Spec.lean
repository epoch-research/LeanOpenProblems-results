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


lemma a_pos_of_witness {n x y z w k : ℕ}
    (hx : x ≤ n) (hy : y ≤ n) (hz : z ≤ n) (hw : w ≤ n)
    (hsum : x^2 + y^2 + z^2 + w^2 = n^2)
    (hzw : z ≤ w) (hk : k ≤ n)
    (hpell : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ)) : a n > 0 := by
  classical
  unfold a
  simp only
  apply Finset.card_pos.mpr
  refine ⟨((x,y),(z,w)), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · simp [Finset.mem_product]
    omega
  · exact ⟨hsum, hzw, ⟨k, by omega, hpell⟩⟩

lemma a_pos_two_pow (k : ℕ) : a (2^k) > 0 := by
  apply a_pos_of_witness (x:=2^k) (y:=0) (z:=0) (w:=0) (k:=k)
  · rfl
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · simp
  · exact Nat.zero_le _
  · induction k with
    | zero => simp
    | succ k ih =>
        calc
          k + 1 ≤ 2^k + 1 := Nat.succ_le_succ ih
          _ ≤ 2^k + 2^k := by
            exact Nat.add_le_add_left (Nat.one_le_pow k 2 (by norm_num)) _
          _ = 2^(k+1) := by rw [pow_succ]; ring
  · norm_num
    rw [← pow_mul]
    change (2:ℤ)^(k * 2) = ((2:ℤ)^2)^k
    rw [← pow_mul, mul_comm]

lemma a_pos_double {m : ℕ} (hm : a m > 0) : a (2*m) > 0 := by
  classical
  rcases m with _ | m
  · exfalso
    simp [a] at hm
    rcases hm with ⟨p, hp⟩
    rcases hp with ⟨rfl, hp⟩
  unfold a at hm
  simp only at hm
  rcases Finset.card_pos.mp hm with ⟨⟨⟨x,y⟩,⟨z,w⟩⟩, hp⟩
  simp only [Finset.mem_filter, Finset.mem_range] at hp
  rcases hp with ⟨hmem, hsum, hzw, k, hk, hpell⟩
  simp [Finset.mem_product] at hmem
  rcases hmem with ⟨⟨hx, hy⟩, hz, hw⟩
  apply a_pos_of_witness (n:=2*(m+1)) (x:=2*x) (y:=2*y) (z:=2*z) (w:=2*w) (k:=k+1)
  · omega
  · omega
  · omega
  · omega
  · nlinarith [hsum]
  · omega
  · omega
  · calc
      ((2 * x)^2 : ℤ) - (3 * (2 * y) : ℤ)^2
          = 4 * ((x^2 : ℤ) - (3 * y : ℤ)^2) := by ring
      _ = 4 * (4^k : ℤ) := by rw [hpell]
      _ = (4^(k+1) : ℤ) := by
        rw [pow_succ]
        ring


lemma a_pos_mul_two_pow (k m : ℕ) (hm : a m > 0) : a ((2^k) * m) > 0 := by
  induction k with
  | zero => simpa using hm
  | succ k ih =>
      have h := a_pos_double ih
      simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using h



lemma a_pos_of_pell_and_two_squares {n x y k z w : ℕ}
    (hx : x ≤ n) (hy : y ≤ n) (hk : k ≤ n)
    (hpell : (x^2 : ℤ) - (3 * y : ℤ)^2 = (4^k : ℤ))
    (hsum : x^2 + y^2 + z^2 + w^2 = n^2) : a n > 0 := by
  have hzle : z ≤ n := by nlinarith [hsum]
  have hwle : w ≤ n := by nlinarith [hsum]
  by_cases hzw : z ≤ w
  · exact a_pos_of_witness hx hy hzle hwle hsum hzw hk hpell
  · have hwz : w ≤ z := le_of_not_ge hzw
    have hsum' : x^2 + y^2 + w^2 + z^2 = n^2 := by nlinarith [hsum]
    exact a_pos_of_witness hx hy hwle hzle hsum' hwz hk hpell

/--
Conjecture: a(n) > 0 for all n > 0. Moreover, any positive square n² can be written as
x² + y² + z² + w² with x,y,z,w integers and y even such that x² - (3*y)² = 4ᵏ for some k = 0,1,2,....
-/
theorem A301376_conjecture : ∀ (n : ℕ), n > 0 → a n > 0 := by
  sorry
