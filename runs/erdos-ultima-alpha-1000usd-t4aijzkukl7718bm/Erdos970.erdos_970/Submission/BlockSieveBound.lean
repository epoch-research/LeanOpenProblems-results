import Submission.BlockFactors

/-!
A finite block-sieve criterion. It keeps the pointwise, main-term, and remainder
estimates separate; all hypotheses are explicit.
-/
namespace Erdos970.BlockSieve

open SievePolynomial

/-- A hit in one block forces the combined lower weight to be nonpositive. -/
theorem pointwise_product_le_error_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (U E : ι → ℝ) (hU : ∀ i, 0 ≤ U i) (hE : ∀ i, 0 ≤ E i)
    (hhit : ∃ i, U i ≤ E i) :
    (∏ j, U j) ≤ ∑ i, ∏ j, if j = i then E j else U j := by
  obtain ⟨i, hi⟩ := hhit
  calc
    (∏ j, U j) ≤ ∏ j, if j = i then E j else U j := by
      apply Finset.prod_le_prod (fun j _ => hU j)
      intro j hj
      by_cases hji : j = i
      · simpa [hji] using hi
      · simp [hji]
    _ ≤ _ := Finset.single_le_sum (f := fun i : ι => ∏ j, if j = i then E j else U j)
      (fun i _ => Finset.prod_nonneg (fun j _ => by split_ifs <;> aesop)) (Finset.mem_univ i)

/-- Geometrically small relative errors leave a positive combined main term. -/
theorem product_main_lower {ι : Type} [Fintype ι] [DecidableEq ι]
    (A B D ε : ι → ℝ) (hD : ∀ i, 0 ≤ D i) (hA : ∀ i, D i / 2 ≤ A i)
    (hB0 : ∀ i, 0 ≤ B i) (hε0 : ∀ i, 0 ≤ ε i) (hB : ∀ i, B i ≤ ε i * D i)
    (hε : (∑ i, ε i) ≤ 1 / 4) :
    (∏ i, D i) / (2 : ℝ) ^ (Fintype.card ι + 1) ≤
      (∏ i, A i) - ∑ i, ∏ j, if j = i then B j else A j := by
  have hA0 (i : ι) : 0 ≤ A i := (div_nonneg (hD i) (by norm_num)).trans (hA i)
  have hprod0 : 0 ≤ ∏ i, A i := Finset.prod_nonneg (fun i _ => hA0 i)
  have hBi (i : ι) : B i ≤ (2 * ε i) * A i := by
    have hh := mul_le_mul_of_nonneg_left (hA i) (hε0 i)
    nlinarith only [hB i, hh]
  have hterm (i : ι) : (∏ j, if j = i then B j else A j) ≤ (2 * ε i) * ∏ j, A j := by
    calc
      (∏ j, if j = i then B j else A j) ≤ ∏ j, (if j = i then 2 * ε i else 1) * A j := by
        apply Finset.prod_le_prod
        · intro j hj
          split_ifs <;> aesop
        · intro j hj
          by_cases hji : j = i
          · simpa [hji] using hBi i
          · simp [hji]
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have hsum : (∑ i, ∏ j, if j = i then B j else A j) ≤ (1 / 2 : ℝ) * ∏ j, A j := by
    calc
      _ ≤ ∑ i, (2 * ε i) * ∏ j, A j := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (2 * ∑ i, ε i) * ∏ j, A j := by rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hprod0
  have hprod : (∏ i, D i) / (2 : ℝ) ^ Fintype.card ι ≤ ∏ i, A i := by
    have hh : (∏ i, D i / 2) ≤ ∏ i, A i := Finset.prod_le_prod
      (fun i _ => div_nonneg (hD i) (by norm_num)) (fun i _ => hA i)
    simpa only [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] using hh
  have hh := div_le_div_of_nonneg_right hprod (by norm_num : (0 : ℝ) ≤ 2)
  rw [div_div, ← pow_succ] at hh
  linarith

/-- Abstract finite block-sieve estimate, using arbitrary upper and error polynomials. -/
theorem block_cover_bound {ι : Type} [Fintype ι] [DecidableEq ι]
    (U E : ι → SievePolynomial) (P : ι → Finset ℕ)
    (hU : ∀ j, (U j).SupportedOn (P j)) (hE : ∀ j, (E j).SupportedOn (P j))
    (hP : ∀ j, ∀ p ∈ P j, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (r : ℕ → ℕ) (m : ℕ)
    (hpoint : ∀ x < m, (∀ j, 0 ≤ (U j).value r x) ∧ (∀ j, 0 ≤ (E j).value r x) ∧
      ∃ j, (U j).value r x ≤ (E j).value r x) :
    (m : ℝ) * ((∏ j, (U j).mean) - ∑ i, ∏ j, (if j = i then E j else U j).mean) ≤
      (∏ j, (U j).cost) + ∑ i, ∏ j, (if j = i then E j else U j).cost := by
  classical
  let V (i : ι) (j : ι) := if j = i then E j else U j
  have hV (i j : ι) : (V i j).SupportedOn (P j) := by
    dsimp only [V]
    split_ifs <;> aesop
  have hprimeU : ∀ a, ∀ p ∈ (product U).primes a, p.Prime := by
    intro a p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p (hU j (a j) hpj)
  have hprimeV (i : ι) : ∀ a, ∀ p ∈ (product (V i)).primes a, p.Prime := by
    intro a p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p (hV i j (a j) hpj)
  have hintU := interval_error (product U) hprimeU r m
  rw [mean_product U P hU hdis, cost_product] at hintU
  have hintV (i : ι) :
      (∑ x ∈ Finset.range m, (product (V i)).value r x) ≤
        (m : ℝ) * (∏ j, (V i j).mean) + ∏ j, (V i j).cost := by
    have hh := interval_error (product (V i)) (hprimeV i) r m
    rw [mean_product (V i) P (hV i) hdis, cost_product] at hh
    have hh' := (abs_le.mp hh).2
    linarith
  have hsum : (∑ x ∈ Finset.range m, (product U).value r x) ≤
      ∑ i, ∑ x ∈ Finset.range m, (product (V i)).value r x := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro x hx
    obtain ⟨hxU, hxE, hxhit⟩ := hpoint x (Finset.mem_range.mp hx)
    simp only [value_product]
    have hh := pointwise_product_le_error_sum (fun j => (U j).value r x) (fun j => (E j).value r x)
      hxU hxE hxhit
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [V]
    split_ifs <;> rfl
  have hvsum := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset ι)) => hintV i)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hvsum
  have hu := (abs_le.mp hintU).1
  change (m : ℝ) * ((∏ j, (U j).mean) - ∑ i, ∏ j, (V i j).mean) ≤
    (∏ j, (U j).cost) + ∑ i, ∏ j, (V i j).cost
  linarith

/-- A numerical cover-length estimate for disjoint blocks with bounded reciprocal mass. -/
theorem cover_bound_of_blocks (b k : ℕ) (P : Fin b → Finset ℕ) (n : Fin b → ℕ)
    (hP : ∀ j, ∀ p ∈ P j, p.Prime) (hdis : Pairwise (fun i j => Disjoint (P i) (P j)))
    (hcard : (Finset.univ.biUnion P).card ≤ k)
    (hmass : ∀ j, (∑ p ∈ P j, (1 : ℝ) / p) ≤ 4)
    (hε : (∑ j, (1 : ℝ) / 2 ^ (n j + 3)) ≤ 1 / 4)
    (r : ℕ → ℕ) (m : ℕ) (hcover : ∀ x < m, ∃ j, ∃ p ∈ P j, x ≡ r p [MOD p]) :
    m ≤ (b + 1) * (k + 1) * 2 ^ (b + 1) *
      ∏ j, ((P j).card + 1) ^ (2 * (n j + 18) + 1) := by
  classical
  let U (j : Fin b) := upper (P j) (2 * (n j + 18))
  let E (j : Fin b) := errorTerm (P j) (2 * (n j + 18))
  let D (j : Fin b) := ∏ p ∈ P j, (1 - 1 / (p : ℝ))
  let ε (j : Fin b) : ℝ := 1 / 2 ^ (n j + 3)
  let N (j : Fin b) := ((P j).card + 1) ^ (2 * (n j + 18) + 1)
  have hUs (j : Fin b) : (U j).SupportedOn (P j) := upper_supportedOn _ _
  have hEs (j : Fin b) : (E j).SupportedOn (P j) := errorTerm_supportedOn _ _
  have hpoint : ∀ x < m, (∀ j, 0 ≤ (U j).value r x) ∧ (∀ j, 0 ≤ (E j).value r x) ∧
      ∃ j, (U j).value r x ≤ (E j).value r x := by
    intro x hx
    have hb (j : Fin b) := value_factor_bounds (P j) r x (2 * (n j + 18)) (even_two_mul _)
    refine ⟨fun j => (hb j).1, fun j => (hb j).2.1, ?_⟩
    obtain ⟨j, p, hp, hxp⟩ := hcover x hx
    exact ⟨j, (hb j).2.2 ⟨p, hp, hxp⟩⟩
  have hc := block_cover_bound U E P hUs hEs hP hdis r m hpoint
  have hDj (j : Fin b) : 0 < D j := by
    have hh := (Erdos970.BrunCriterion.prime_product_exp_bounds (P j) (hP j)).1
    exact (Real.exp_pos _).trans_le hh
  have hb (j : Fin b) := block_mean_bounds (P j) (hP j) (n j) (hmass j)
  have hA (j : Fin b) : D j / 2 ≤ (U j).mean := (hb j).1
  have hB (j : Fin b) : (E j).mean ≤ ε j * D j := by
    have hh := (hb j).2
    simpa only [ε, D, div_eq_mul_inv, one_mul, mul_comm] using hh
  have hB0 (j : Fin b) : 0 ≤ (E j).mean := by
    change 0 ≤ ∑ Q : ↥((P j).powersetCard (2 * (n j + 18) + 1)),
      (1 : ℝ) / ∏ p ∈ Q.val, (p : ℝ)
    exact Finset.sum_nonneg (fun Q _ => by positivity)
  have hmain0 := product_main_lower (fun j => (U j).mean) (fun j => (E j).mean) D ε
    (fun j => (hDj j).le) hA hB0 (fun j => by dsimp [ε]; positivity) hB hε
  have hmain : (∏ j, D j) / (2 : ℝ) ^ (b + 1) ≤
      (∏ j, (U j).mean) - ∑ i, ∏ j, (if j = i then E j else U j).mean := by
    simpa only [Fintype.card_fin, apply_ite] using hmain0
  have hPall : ∀ p ∈ Finset.univ.biUnion P, p.Prime := by
    intro p hp
    obtain ⟨j, hj, hpj⟩ := Finset.mem_biUnion.mp hp
    exact hP j p hpj
  have hdall : (↑(Finset.univ : Finset (Fin b)) : Set (Fin b)).PairwiseDisjoint P :=
    fun i hi j hj hij => hdis hij
  have hDall : (1 : ℝ) / (k + 1) ≤ ∏ j, D j := by
    have hh := (Erdos970.BrunCriterion.prime_product_bounds (Finset.univ.biUnion P) hPall).1
    rw [Finset.prod_biUnion hdall] at hh
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hcard 1)).trans hh
  let Q : ℕ := (k + 1) * 2 ^ (b + 1)
  have hQpos : 0 < (Q : ℝ) := by dsimp [Q]; positivity
  have hmain' : 1 / (Q : ℝ) ≤
      (∏ j, (U j).mean) - ∑ i, ∏ j, (if j = i then E j else U j).mean := by
    have hh := (div_le_div_of_nonneg_right hDall (by positivity : (0 : ℝ) ≤ 2 ^ (b + 1))).trans hmain
    simpa only [Q, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat, div_div] using hh
  have hCU : (∏ j, (U j).cost) ≤ ∏ j, (N j : ℝ) :=
    Finset.prod_le_prod (fun j _ => cost_nonneg _) (fun j _ => by
      simpa only [N, Nat.cast_pow] using (factor_cost_bounds (P j) (2 * (n j + 18))).1)
  have hCE (i : Fin b) : (∏ j, (if j = i then E j else U j).cost) ≤ ∏ j, (N j : ℝ) := by
    apply Finset.prod_le_prod (fun j _ => cost_nonneg _)
    intro j hj
    have hh := factor_cost_bounds (P j) (2 * (n j + 18))
    by_cases hji : j = i
    · simpa only [if_pos hji, N, Nat.cast_pow] using hh.2
    · simpa only [if_neg hji, N, Nat.cast_pow] using hh.1
  have hCsum : (∏ j, (U j).cost) + ∑ i, ∏ j, (if j = i then E j else U j).cost ≤
      ((b : ℝ) + 1) * ∏ j, (N j : ℝ) := by
    have hh := Finset.sum_le_sum (fun i (_hi : i ∈ (Finset.univ : Finset (Fin b))) => hCE i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
    nlinarith only [hh, hCU]
  have hmQ : (m : ℝ) / Q ≤ ((b : ℝ) + 1) * ∏ j, (N j : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left hmain' (Nat.cast_nonneg m)
    simpa only [mul_one_div] using hh.trans (hc.trans hCsum)
  have hmle := (div_le_iff₀ hQpos).mp hmQ
  have hnat : m ≤ (b + 1) * (∏ j, N j) * Q := by
    exact_mod_cast hmle
  dsimp only [Q, N] at hnat
  convert hnat using 1 <;> ring

#print axioms product_main_lower
#print axioms block_cover_bound
#print axioms cover_bound_of_blocks
end Erdos970.BlockSieve
