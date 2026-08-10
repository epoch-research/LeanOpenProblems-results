import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 500000
set_option maxHeartbeats 2000000
open Nat
open scoped ArithmeticFunction.sigma
def a (n : ℕ) : ℤ :=
  (divisors n).sum fun d =>
    (2 * d : ℤ) - (ArithmeticFunction.sigma 1 d : ℤ)

lemma a_of_prime (p : ℕ) (hp : p.Prime) : a p = p := by
  have h_div : divisors p = {1, p} := hp.divisors
  have h_not_mem : 1 ∉ ({p} : Finset ℕ) := by simp [hp.ne_one.symm]
  simp [a, h_div, Finset.sum_insert h_not_mem, ArithmeticFunction.sigma_apply]
  omega

lemma exists_proper_divisor (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    ∃ d ∈ n.properDivisors, d ≠ 1 := by
  have h_ne_one : n.properDivisors ≠ {1} := by
    rw [ne_eq, properDivisors_eq_singleton_one_iff_prime]
    exact h_not_prime
  have h_one_mem : 1 ∈ n.properDivisors := by
    rw [mem_properDivisors]
    refine ⟨one_dvd n, ?_⟩
    omega
  by_contra h_all_one
  push_neg at h_all_one
  have h_eq : n.properDivisors = {1} := by
    ext x
    simp only [Finset.mem_singleton]
    constructor
    · intro hx
      exact h_all_one x hx
    · intro hx
      subst hx
      exact h_one_mem
  contradiction

lemma distinct_divisors (n : ℕ) (hn12 : n > 12) (d : ℕ) (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1) :
    d ∈ n.divisors ∧ 1 ∈ n.divisors ∧ n ∈ n.divisors ∧ d ≠ 1 ∧ d ≠ n ∧ 1 ≠ n := by
  have hd_div : d ∈ n.divisors := by
    rw [mem_properDivisors] at hd
    exact mem_divisors.mpr ⟨hd.1, by omega⟩
  have h1_div : 1 ∈ n.divisors := by
    exact one_mem_divisors.mpr (by omega)
  have hn_div : n ∈ n.divisors := by
    rw [mem_divisors]
    exact ⟨dvd_rfl, by omega⟩
  have hd_lt_n : d < n := by
    rw [mem_properDivisors] at hd
    exact hd.2
  refine ⟨hd_div, h1_div, hn_div, hd1, (by omega), (by omega)⟩

lemma subset_divisors (n : ℕ) (hn12 : n > 12) (d : ℕ) (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1) :
    ({1, d, n} : Finset ℕ) ⊆ n.divisors := by
  have hd_divs := distinct_divisors n hn12 d hd hd1
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact hd_divs.2.1
  · exact hd_divs.1
  · exact hd_divs.2.2.1

lemma sum_le_sum_divisors (n : ℕ) (hn12 : n > 12) (d : ℕ) (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1) :
    ∑ c ∈ ({1, d, n} : Finset ℕ), (σ 1 c : ℤ) ≤ ∑ c ∈ n.divisors, (σ 1 c : ℤ) := by
  have h_sub := subset_divisors n hn12 d hd hd1
  refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
  intro x hx hx_not
  omega

lemma sum_three (n : ℕ) (hn12 : n > 12) (d : ℕ) (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1) :
    ∑ c ∈ ({1, d, n} : Finset ℕ), (σ 1 c : ℤ) = (σ 1 1 : ℤ) + (σ 1 d : ℤ) + (σ 1 n : ℤ) := by
  have hd_divs := distinct_divisors n hn12 d hd hd1
  have hd1_symm : 1 ≠ d := hd_divs.2.2.2.1.symm
  have hn1_symm : 1 ≠ n := hd_divs.2.2.2.2.2
  have h_not_mem1 : 1 ∉ ({d, n} : Finset ℕ) := by
    simp [hd1_symm, hn1_symm]
  have h_not_mem2 : d ∉ ({n} : Finset ℕ) := by
    simp [hd_divs.2.2.2.2.1]
  rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_singleton, add_assoc]

lemma d_ge_two (n : ℕ) (hn12 : n > 12) (d : ℕ) (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1) :
    d ≥ 2 := by
  have hd_div : d ∈ n.divisors := by
    rw [mem_properDivisors] at hd
    exact mem_divisors.mpr ⟨hd.1, by omega⟩
  have hd_pos : d > 0 := pos_of_mem_divisors hd_div
  omega

lemma d_divisors (d : ℕ) (hd2 : d ≥ 2) :
    1 ∈ d.divisors ∧ d ∈ d.divisors ∧ 1 ≠ d := by
  have h1 : 1 ∈ d.divisors := one_mem_divisors.mpr (by omega)
  have hd : d ∈ d.divisors := mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  exact ⟨h1, hd, (by omega)⟩

lemma subset_d_divisors (d : ℕ) (hd2 : d ≥ 2) :
    ({1, d} : Finset ℕ) ⊆ d.divisors := by
  have h_divs := d_divisors d hd2
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact h_divs.1
  · exact h_divs.2.1

lemma sigma_d_ge_three (d : ℕ) (hd2 : d ≥ 2) :
    (σ 1 d : ℤ) ≥ 3 := by
  have h_sub := subset_d_divisors d hd2
  have h_le : ∑ c ∈ ({1, d} : Finset ℕ), (c : ℤ) ≤ ∑ c ∈ d.divisors, (c : ℤ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro x hx hx_not
    omega
  have h_sum : ∑ c ∈ ({1, d} : Finset ℕ), (c : ℤ) = 1 + (d : ℤ) := by
    have hd1_symm : 1 ≠ d := (by omega)
    have h_not_mem : 1 ∉ ({d} : Finset ℕ) := by simp [hd1_symm]
    rw [Finset.sum_insert h_not_mem, Finset.sum_singleton]
    rfl
  have h_sigma : (σ 1 d : ℤ) = ∑ c ∈ d.divisors, (c : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  omega

lemma a_eq_formula (n : ℕ) : a n = 2 * (σ 1 n : ℤ) - ∑ d ∈ divisors n, (σ 1 d : ℤ) := by
  rw [a, Finset.sum_sub_distrib]
  have h_mul : (divisors n).sum (fun d => (2 * d : ℤ)) = 2 * (divisors n).sum (fun d => (d : ℤ)) := by
    rw [← Finset.mul_sum]
  have h_sigma : (σ 1 n : ℤ) = (divisors n).sum (fun d => (d : ℤ)) := by
    simp [ArithmeticFunction.sigma_one_apply]
  rw [h_mul, ← h_sigma]


lemma a_eq_sigma_sub_proper (n : ℕ) (hn0 : n ≠ 0) :
    a n = (σ 1 n : ℤ) - ∑ d ∈ n.properDivisors, (σ 1 d : ℤ) := by
  have h_eq := a_eq_formula n
  have h_sum : ∑ d ∈ divisors n, (σ 1 d : ℤ) = (σ 1 n : ℤ) + ∑ d ∈ n.properDivisors, (σ 1 d : ℤ) := by
    rw [← insert_self_properDivisors hn0, Finset.sum_insert self_notMem_properDivisors]
  omega


lemma composite_has_extra_divisor (k : ℕ) (hk : ¬ k.Prime) (hk_gt : k > 250) :
    ∃ x ∈ (4 * k).divisors, x ∉ ({1, 2, 4, k, 2 * k, 4 * k} : Finset ℕ) := by
  have hk12 : k > 12 := by omega
  rcases exists_proper_divisor k hk12 hk with ⟨d, hd, hd1⟩
  have hd_div_k : d ∣ k := by
    rw [mem_properDivisors] at hd
    exact hd.1
  have hd_lt_k : d < k := by
    rw [mem_properDivisors] at hd
    exact hd.2
  have hd_pos : d > 0 := by
    have : k > 0 := by omega
    exact Nat.pos_of_dvd_of_pos hd_div_k this
  have hd_gt_1 : d > 1 := by
    have : d ≠ 0 := by omega
    omega
  by_cases hd2 : d = 2
  · -- d = 2, so 2 | k. Let m = k / 2
    have h2_dvd : 2 ∣ k := by rwa [hd2] at hd_div_k
    let m := k / 2
    have h_km : k = 2 * m := (Nat.mul_div_cancel' h2_dvd).symm
    have hm_div_k : m ∣ k := by
      rw [h_km]
      exact dvd_mul_left m 2
    have hm_div_4k : m ∣ 4 * k := dvd_mul_of_dvd_right hm_div_k 4
    have hm_pos : m > 0 := by
      have : k > 0 := by omega
      rw [h_km] at this
      omega
    have hm_mem : m ∈ (4 * k).divisors := by
      rw [mem_divisors]
      refine ⟨hm_div_4k, by omega⟩
    use m, hm_mem
    have hm_val : m > 125 := by omega
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with hm1 | hm2 | hm3 | hm4 | hm5 | hm6
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  · by_cases hd4 : d = 4
    · -- d = 4, so 4 | k. Let m = k / 4
      have h4_dvd : 4 ∣ k := by rwa [hd4] at hd_div_k
      let m := k / 4
      have h_km : k = 4 * m := (Nat.mul_div_cancel' h4_dvd).symm
      have hm_div_k : m ∣ k := by
        rw [h_km]
        exact dvd_mul_left m 4
      have hm_div_4k : m ∣ 4 * k := dvd_mul_of_dvd_right hm_div_k 4
      have hm_pos : m > 0 := by
        have : k > 0 := by omega
        rw [h_km] at this
        omega
      have hm_mem : m ∈ (4 * k).divisors := by
        rw [mem_divisors]
        refine ⟨hm_div_4k, by omega⟩
      use m, hm_mem
      have hm_val : m > 62 := by omega
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hc
      rcases hc with hm1 | hm2 | hm3 | hm4 | hm5 | hm6
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
    · -- d is not 2 or 4.
      have hd_div_4k : d ∣ 4 * k := dvd_mul_of_dvd_right hd_div_k 4
      have hd_mem : d ∈ (4 * k).divisors := by
        rw [mem_divisors]
        refine ⟨hd_div_4k, by omega⟩
      use d, hd_mem
      simp only [Finset.mem_insert, Finset.mem_singleton]
      intro hc
      rcases hc with hd_1 | hd_2 | hd_4 | hd_k | hd_2k | hd_4k
      · omega
      · contradiction
      · contradiction
      · omega
      · omega
      · omega

lemma a_eq_n_sub_sum_f (n : ℕ) (hn0 : n ≠ 0) :
    a n = (n : ℤ) - ∑ d ∈ n.properDivisors, ((σ 1 d : ℤ) - (d : ℤ)) := by
  have h_a := a_eq_sigma_sub_proper n hn0
  have h_sig : (σ 1 n : ℤ) = (n : ℤ) + ∑ d ∈ n.properDivisors, (d : ℤ) := by
    have h_sigma_n : (σ 1 n : ℤ) = ∑ y ∈ divisors n, (y : ℤ) := by
      simp [ArithmeticFunction.sigma_one_apply]
    rw [h_sigma_n]
    have h_sum : ∑ d ∈ divisors n, (d : ℤ) = (n : ℤ) + ∑ d ∈ n.properDivisors, (d : ℤ) := by
      rw [← insert_self_properDivisors hn0, Finset.sum_insert self_notMem_properDivisors]
    exact h_sum
  rw [h_a, h_sig, Finset.sum_sub_distrib]
  ring



lemma sigma_le_of_dvd (n c : ℕ) (hn : n > 0) (hc : c ∈ divisors n) :
    ((n / c : ℕ) : ℤ) * (σ 1 c : ℤ) ≤ (σ 1 n : ℤ) := by
  have hc0 : c ≠ 0 := by
    intro hc0
    subst hc0
    have := pos_of_mem_divisors hc
    omega
  have h_div : (n / c) * c = n := Nat.div_mul_cancel (dvd_of_mem_divisors hc)
  have hk0 : n / c > 0 := Nat.div_pos (Nat.le_of_dvd hn (dvd_of_mem_divisors hc)) (pos_of_mem_divisors hc)
  let emb : ℕ ↪ ℕ := ⟨fun x => (n/c) * x, fun x y h => by
    dsimp at h
    have : n / c ≠ 0 := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero this) h⟩
  have h_sub : Finset.map emb (divisors c) ⊆ divisors n := by
    intro y hy
    rw [Finset.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [mem_divisors] at hx ⊢
    rcases hx with ⟨h_xdvd, h_x0⟩
    refine ⟨?_, by omega⟩
    have h_dvd_c := dvd_of_mem_divisors hc
    have h_eq : n = (n / c) * c := h_div.symm
    rw [h_eq]
    exact mul_dvd_mul_left (n / c) h_xdvd
  have h_sum_le : ∑ x ∈ Finset.map emb (divisors c), (x : ℤ) ≤ ∑ y ∈ divisors n, (y : ℤ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro y hy h_not
    omega
  rw [Finset.sum_map] at h_sum_le
  have h_eq_sum : ∑ x ∈ divisors c, (emb x : ℤ) = ((n / c : ℕ) : ℤ) * ∑ x ∈ divisors c, (x : ℤ) := by
    simp_rw [emb, Function.Embedding.coeFn_mk]
    push_cast
    rw [← Finset.mul_sum]
  rw [h_eq_sum] at h_sum_le
  have h_sigma_c : (σ 1 c : ℤ) = ∑ x ∈ divisors c, (x : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  have h_sigma_n : (σ 1 n : ℤ) = ∑ y ∈ divisors n, (y : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  rw [h_sigma_c, h_sigma_n]
  exact h_sum_le


lemma sigma_le_of_proper_dvd (n d : ℕ) (hn0 : n > 0) (hd : d ∈ n.properDivisors) (hd1 : d ≠ 1) :
    ((n / d : ℕ) : ℤ) * (σ 1 d : ℤ) ≤ (σ 1 n : ℤ) - 1 := by
  have hd_divs : d ∈ n.divisors := by
    rw [mem_properDivisors] at hd
    exact mem_divisors.mpr ⟨hd.1, by omega⟩
  have hd0 : d ≠ 0 := by
    intro hd0
    subst hd0
    have := pos_of_mem_divisors hd_divs
    omega
  have h_div : (n / d) * d = n := Nat.div_mul_cancel (dvd_of_mem_divisors hd_divs)
  have hk0 : n / d > 0 := Nat.div_pos (Nat.le_of_dvd hn0 (dvd_of_mem_divisors hd_divs)) (pos_of_mem_divisors hd_divs)
  have h_div_ge2 : n / d ≥ 2 := by
    rw [mem_properDivisors] at hd
    have hd_lt : d < n := hd.2
    have h_eq : n = (n / d) * d := h_div.symm
    by_contra hc
    have : n / d = 1 ∨ n / d = 0 := by omega
    rcases this with h1 | h0
    · rw [h1, one_mul] at h_eq
      subst h_eq
      omega
    · rw [h0, zero_mul] at h_eq
      omega
  let emb : ℕ ↪ ℕ := ⟨fun x => (n/d) * x, fun x y h => by
    dsimp at h
    have : n / d ≠ 0 := by omega
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero this) h⟩
  have h_sub : Finset.map emb (divisors d) ⊆ (divisors n).erase 1 := by
    intro y hy
    rw [Finset.mem_map] at hy
    rcases hy with ⟨x, hx, rfl⟩
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · dsimp [emb]
      have hx0 : x ≠ 0 := by
        intro hx0
        subst hx0
        have := pos_of_mem_divisors hx
        omega
      have : x ≥ 1 := by omega
      have h_mul_ge : (n / d) * x ≥ 2 * 1 := by
        refine Nat.mul_le_mul h_div_ge2 (by omega)
      omega
    · rw [mem_divisors] at hx ⊢
      rcases hx with ⟨h_xdvd, h_x0⟩
      refine ⟨?_, by omega⟩
      have h_dvd_d := dvd_of_mem_divisors hd_divs
      have h_eq : n = (n / d) * d := h_div.symm
      rw [h_eq]
      exact mul_dvd_mul_left (n / d) h_xdvd
  have h_sum_le : ∑ x ∈ Finset.map emb (divisors d), (x : ℤ) ≤ ∑ y ∈ (divisors n).erase 1, (y : ℤ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro y hy h_not
    omega
  rw [Finset.sum_map] at h_sum_le
  have h_eq_sum : ∑ x ∈ divisors d, (emb x : ℤ) = ((n / d : ℕ) : ℤ) * ∑ x ∈ divisors d, (x : ℤ) := by
    simp_rw [emb, Function.Embedding.coeFn_mk]
    push_cast
    rw [← Finset.mul_sum]
  rw [h_eq_sum] at h_sum_le
  have h_sigma_d : (σ 1 d : ℤ) = ∑ x ∈ divisors d, (x : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  have h_sigma_n : (σ 1 n : ℤ) = ∑ y ∈ divisors n, (y : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  have h_erase : ∑ y ∈ (divisors n).erase 1, (y : ℤ) = (σ 1 n : ℤ) - 1 := by
    rw [h_sigma_n]
    have h1_mem : 1 ∈ divisors n := one_mem_divisors.mpr (by omega)
    have h_sum_er := Finset.sum_erase_add (divisors n) (fun (y : ℕ) => (y : ℤ)) h1_mem
    dsimp only at h_sum_er
    omega
  rw [← h_sigma_d, h_erase] at h_sum_le
  exact h_sum_le



lemma sigma_proper_le_sigma_div_two (n d : ℕ) (hn : n > 0) (hd : d ∈ divisors n) (hd_proper : d < n) :
    2 * (σ 1 d : ℤ) ≤ (σ 1 n : ℤ) := by
  have hd_div : n / d ≥ 2 := by
    have h_dvd := dvd_of_mem_divisors hd
    have hd0 : d ≠ 0 := by
      intro hc
      subst hc
      have := pos_of_mem_divisors hd
      omega
    have h_eq : n = (n / d) * d := (Nat.div_mul_cancel h_dvd).symm
    have h_lt : d < (n / d) * d := by omega
    have h_div_gt : n / d > 1 := by
      by_contra hc
      generalize h_kd : n / d = k at *
      interval_cases k
      · omega
      · omega
    omega
  have h_le := sigma_le_of_dvd n d hn hd
  have h_sigma_pos : (σ 1 d : ℤ) ≥ 0 := by
    have : (σ 1 d : ℤ) = ∑ c ∈ divisors d, (c : ℤ) := by
      simp [ArithmeticFunction.sigma_one_apply]
    rw [this]
    refine Finset.sum_nonneg ?_
    intro c hc
    omega
  have h_mul_le : 2 * (σ 1 d : ℤ) ≤ ((n / d : ℕ) : ℤ) * (σ 1 d : ℤ) := by
    refine mul_le_mul_of_nonneg_right ?_ h_sigma_pos
    omega
  omega

lemma sum_sigma_le_sigma_sq (n : ℕ) (hn : n > 0) :
    (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) ≤ (σ 1 n : ℤ) * (σ 1 n : ℤ) := by
  have h_sum : (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) = ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) := by
    rw [Finset.mul_sum]
  have h_sum_le : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) ≤ ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) := by
    refine Finset.sum_le_sum ?_
    intro c hc
    have h_div_mul : (n / c : ℕ) * c = n := Nat.div_mul_cancel (dvd_of_mem_divisors hc)
    have h_cast : ((n : ℤ) * (σ 1 c : ℤ)) = (c : ℤ) * (((n / c : ℕ) : ℤ) * (σ 1 c : ℤ)) := by
      generalize h_kd : n / c = k
      have h_div_mul_k : k * c = n := by
        rw [← h_kd]
        exact h_div_mul
      exact_mod_cast (by rw [← h_div_mul_k]; ring : n * (σ 1 c) = c * (k * (σ 1 c)))
    rw [h_cast]
    have h_le := sigma_le_of_dvd n c hn hc
    have hc_ge : (c : ℤ) ≥ 0 := by omega
    nlinarith
  have h_sq : ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) = (σ 1 n : ℤ) * (σ 1 n : ℤ) := by
    rw [← Finset.sum_mul]
    have h_sigma : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
      simp [ArithmeticFunction.sigma_one_apply]
    rw [h_sigma, mul_comm]
  omega


lemma sigma_ge_three_add_n (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    (σ 1 n : ℤ) ≥ (n : ℤ) + 3 := by
  rcases exists_proper_divisor n hn12 h_not_prime with ⟨d, hd, hd1⟩
  rcases distinct_divisors n hn12 d hd hd1 with ⟨_, _, _, hd_ne, hdn, _⟩
  have h_sum : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  have h_sub : ({1, d, n} : Finset ℕ) ⊆ divisors n := subset_divisors n hn12 d hd hd1
  have h_le_divs : ∑ c ∈ ({1, d, n} : Finset ℕ), (c : ℤ) ≤ ∑ c ∈ divisors n, (c : ℤ) := by
    refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
    intro y hy h_not
    omega
  have h_sum_three : ∑ c ∈ ({1, d, n} : Finset ℕ), (c : ℤ) = 1 + (d : ℤ) + (n : ℤ) := by
    have hn_ne : n ≠ 1 := by omega
    have h_not_mem1 : 1 ∉ ({d, n} : Finset ℕ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨hd_ne.symm, hn_ne.symm⟩
    have h_not_mem2 : d ∉ ({n} : Finset ℕ) := by
      simp only [Finset.mem_singleton]
      exact hdn
    rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_singleton]
    ring
  have h_d_ge : (d : ℤ) ≥ 2 := by
    have : d ≥ 2 := d_ge_two n hn12 d hd hd1
    omega
  rw [h_sum]
  omega

lemma sum_sigma_lt_sigma_sq (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) < (σ 1 n : ℤ) * (σ 1 n : ℤ) := by
  have hn0 : n > 0 := by omega
  have h1_mem : 1 ∈ divisors n := one_mem_divisors.mpr (by omega)
  have h_sum_LHS : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) = (n : ℤ) * (σ 1 1 : ℤ) + ∑ c ∈ (divisors n).erase 1, ((n : ℤ) * (σ 1 c : ℤ)) := by
    have h_sum_er := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (n : ℤ) * (σ 1 c : ℤ)) h1_mem
    dsimp only at h_sum_er
    omega
  have h_sum_RHS : ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) = (1 : ℤ) * (σ 1 n : ℤ) + ∑ c ∈ (divisors n).erase 1, ((c : ℤ) * (σ 1 n : ℤ)) := by
    have h_sum_er := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (c : ℤ) * (σ 1 n : ℤ)) h1_mem
    dsimp only at h_sum_er
    omega
  have h_sigma_one : (σ 1 1 : ℤ) = 1 := by simp [ArithmeticFunction.sigma_one]
  have h_sigma_ge := sigma_ge_three_add_n n hn12 h_not_prime
  have h_strict : (n : ℤ) * (σ 1 1 : ℤ) < (1 : ℤ) * (σ 1 n : ℤ) := by
    rw [h_sigma_one, mul_one, one_mul]
    omega
  have h_le : ∑ c ∈ (divisors n).erase 1, ((n : ℤ) * (σ 1 c : ℤ)) ≤ ∑ c ∈ (divisors n).erase 1, ((c : ℤ) * (σ 1 n : ℤ)) := by
    refine Finset.sum_le_sum ?_
    intro c hc
    have hc_mem : c ∈ divisors n := Finset.mem_of_mem_erase hc
    have h_div_mul : (n / c : ℕ) * c = n := Nat.div_mul_cancel (dvd_of_mem_divisors hc_mem)
    have h_cast : ((n : ℤ) * (σ 1 c : ℤ)) = (c : ℤ) * (((n / c : ℕ) : ℤ) * (σ 1 c : ℤ)) := by
      generalize h_kd : n / c = k
      have h_div_mul_k : k * c = n := by
        rw [← h_kd]
        exact h_div_mul
      exact_mod_cast (by rw [← h_div_mul_k]; ring : n * (σ 1 c) = c * (k * (σ 1 c)))
    rw [h_cast]
    have h_le_dvd := sigma_le_of_dvd n c hn0 hc_mem
    have hc_ge : (c : ℤ) ≥ 0 := by omega
    nlinarith
  have h_sum_strict : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) < ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) := by
    rw [h_sum_LHS, h_sum_RHS]
    omega
  have h_mul_LHS : (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) = ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) := by
    rw [Finset.mul_sum]
  have h_mul_RHS : (σ 1 n : ℤ) * (σ 1 n : ℤ) = ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) := by
    rw [← Finset.sum_mul]
    have h_sigma : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
      simp [ArithmeticFunction.sigma_one_apply]
    rw [h_sigma, mul_comm]
  rw [h_mul_LHS, h_mul_RHS]
  exact h_sum_strict

lemma sum_sigma_le_sigma_sq_sub_five (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) ≤ (σ 1 n : ℤ) * (σ 1 n : ℤ) + (n : ℤ) - (σ 1 n : ℤ) - 2 := by
  have hn0 : n > 0 := by omega
  have h1_mem : 1 ∈ divisors n := one_mem_divisors.mpr (by omega)
  rcases exists_proper_divisor n hn12 h_not_prime with ⟨d, hd, hd1⟩
  have hd_divs : d ∈ divisors n := by
    rw [mem_properDivisors] at hd
    exact mem_divisors.mpr ⟨hd.1, by omega⟩
  have hd_ne_one : d ≠ 1 := hd1
  have hd_mem_erase : d ∈ (divisors n).erase 1 := by
    rw [Finset.mem_erase]
    exact ⟨hd_ne_one, hd_divs⟩
  have h_sum_LHS : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) = (n : ℤ) * (σ 1 1 : ℤ) + (n : ℤ) * (σ 1 d : ℤ) + ∑ c ∈ ((divisors n).erase 1).erase d, ((n : ℤ) * (σ 1 c : ℤ)) := by
    have h_sum_er1 := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (n : ℤ) * (σ 1 c : ℤ)) h1_mem
    have h_sum_er2 := Finset.sum_erase_add ((divisors n).erase 1) (fun (c : ℕ) => (n : ℤ) * (σ 1 c : ℤ)) hd_mem_erase
    dsimp only at h_sum_er1 h_sum_er2
    omega
  have h_sum_RHS : ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) = (1 : ℤ) * (σ 1 n : ℤ) + (d : ℤ) * (σ 1 n : ℤ) + ∑ c ∈ ((divisors n).erase 1).erase d, ((c : ℤ) * (σ 1 n : ℤ)) := by
    have h_sum_er1 := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (c : ℤ) * (σ 1 n : ℤ)) h1_mem
    have h_sum_er2 := Finset.sum_erase_add ((divisors n).erase 1) (fun (c : ℕ) => (c : ℤ) * (σ 1 n : ℤ)) hd_mem_erase
    dsimp only at h_sum_er1 h_sum_er2
    omega
  have h_sigma_one : (σ 1 1 : ℤ) = 1 := by simp [ArithmeticFunction.sigma_one]
  have h_le_d : ((n : ℤ) * (σ 1 d : ℤ)) ≤ (d : ℤ) * (σ 1 n : ℤ) - 2 := by
    have h_div_mul : (n / d : ℕ) * d = n := Nat.div_mul_cancel (dvd_of_mem_divisors hd_divs)
    have h_cast : ((n : ℤ) * (σ 1 d : ℤ)) = (d : ℤ) * (((n / d : ℕ) : ℤ) * (σ 1 d : ℤ)) := by
      generalize h_kd : n / d = k
      have h_div_mul_k : k * d = n := by
        rw [← h_kd]
        exact h_div_mul
      exact_mod_cast (by rw [← h_div_mul_k]; ring : n * (σ 1 d) = d * (k * (σ 1 d)))
    rw [h_cast]
    have h_le_dvd := sigma_le_of_proper_dvd n d hn0 hd hd1
    have hd_ge : d ≥ 2 := d_ge_two n hn12 d hd hd1
    have hd_ge_cast : (d : ℤ) ≥ 2 := by omega
    nlinarith
  have h_le_others : ∑ c ∈ ((divisors n).erase 1).erase d, ((n : ℤ) * (σ 1 c : ℤ)) ≤ ∑ c ∈ ((divisors n).erase 1).erase d, ((c : ℤ) * (σ 1 n : ℤ)) := by
    refine Finset.sum_le_sum ?_
    intro c hc
    have hc_mem : c ∈ divisors n := by
      have h1 := Finset.mem_of_mem_erase hc
      exact Finset.mem_of_mem_erase h1
    have h_div_mul : (n / c : ℕ) * c = n := Nat.div_mul_cancel (dvd_of_mem_divisors hc_mem)
    have h_cast : ((n : ℤ) * (σ 1 c : ℤ)) = (c : ℤ) * (((n / c : ℕ) : ℤ) * (σ 1 c : ℤ)) := by
      generalize h_kd : n / c = k
      have h_div_mul_k : k * c = n := by
        rw [← h_kd]
        exact h_div_mul
      exact_mod_cast (by rw [← h_div_mul_k]; ring : n * (σ 1 c) = c * (k * (σ 1 c)))
    rw [h_cast]
    have h_le_dvd := sigma_le_of_dvd n c hn0 hc_mem
    have hc_ge : (c : ℤ) ≥ 0 := by omega
    nlinarith
  have h_sum_le : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) ≤ (σ 1 n : ℤ) * (σ 1 n : ℤ) + (n : ℤ) - (σ 1 n : ℤ) - 2 := by
    rw [h_sum_LHS]
    have h_RHS_eq : (σ 1 n : ℤ) * (σ 1 n : ℤ) = ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) := by
      rw [← Finset.sum_mul]
      have h_sigma : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
        simp [ArithmeticFunction.sigma_one_apply]
      rw [h_sigma, mul_comm]
    rw [h_RHS_eq, h_sum_RHS]
    rw [h_sigma_one]
    omega
  have h_mul_LHS : (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) = ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) := by
    rw [Finset.mul_sum]
  rw [h_mul_LHS]
  exact h_sum_le


lemma sum_sigma_le_sigma_sq_strong (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) ≤ (σ 1 n : ℤ) * (σ 1 n : ℤ) - 2 * (σ 1 n : ℤ) + 2 * (n : ℤ) + 1 := by
  have hn0 : n > 0 := by omega
  have h1_mem : 1 ∈ divisors n := one_mem_divisors.mpr (by omega)
  have hn_mem : n ∈ (divisors n).erase 1 := by
    rw [Finset.mem_erase]
    refine ⟨by omega, ?_⟩
    rw [mem_divisors]
    exact ⟨dvd_rfl, by omega⟩
  have h_sum_LHS : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) = (n : ℤ) * (σ 1 1 : ℤ) + (n : ℤ) * (σ 1 n : ℤ) + ∑ c ∈ ((divisors n).erase 1).erase n, ((n : ℤ) * (σ 1 c : ℤ)) := by
    have h_sum_er1 := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (n : ℤ) * (σ 1 c : ℤ)) h1_mem
    have h_sum_er2 := Finset.sum_erase_add ((divisors n).erase 1) (fun (c : ℕ) => (n : ℤ) * (σ 1 c : ℤ)) hn_mem
    dsimp only at h_sum_er1 h_sum_er2
    omega
  have h_sum_RHS : ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) = (1 : ℤ) * (σ 1 n : ℤ) + (n : ℤ) * (σ 1 n : ℤ) + ∑ c ∈ ((divisors n).erase 1).erase n, ((c : ℤ) * (σ 1 n : ℤ)) := by
    have h_sum_er1 := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (c : ℤ) * (σ 1 n : ℤ)) h1_mem
    have h_sum_er2 := Finset.sum_erase_add ((divisors n).erase 1) (fun (c : ℕ) => (c : ℤ) * (σ 1 n : ℤ)) hn_mem
    dsimp only at h_sum_er1 h_sum_er2
    omega
  have h_sigma_one : (σ 1 1 : ℤ) = 1 := by simp [ArithmeticFunction.sigma_one]
  have h_mem : ∀ c ∈ ((divisors n).erase 1).erase n, c ∈ n.properDivisors ∧ c ≠ 1 := by
    intro c hc
    rw [Finset.mem_erase, Finset.mem_erase] at hc
    rcases hc with ⟨hcn, hc1, hc_divs⟩
    rw [mem_divisors] at hc_divs
    have hc_le : c ≤ n := Nat.le_of_dvd (by omega) hc_divs.1
    have hc_lt : c < n := lt_of_le_of_ne hc_le hcn
    rw [mem_properDivisors]
    exact ⟨⟨hc_divs.1, hc_lt⟩, hc1⟩
  have h_le_others : ∑ c ∈ ((divisors n).erase 1).erase n, ((n : ℤ) * (σ 1 c : ℤ)) ≤ ∑ c ∈ ((divisors n).erase 1).erase n, ((c : ℤ) * (σ 1 n : ℤ) - (c : ℤ)) := by
    refine Finset.sum_le_sum ?_
    intro c hc
    have h_c := h_mem c hc
    have hc_mem : c ∈ divisors n := by
      have h1 := Finset.mem_of_mem_erase hc
      exact Finset.mem_of_mem_erase h1
    have h_div_mul : (n / c : ℕ) * c = n := Nat.div_mul_cancel (dvd_of_mem_divisors hc_mem)
    have h_cast : ((n : ℤ) * (σ 1 c : ℤ)) = (c : ℤ) * (((n / c : ℕ) : ℤ) * (σ 1 c : ℤ)) := by
      generalize h_kd : n / c = k
      have h_div_mul_k : k * c = n := by
        rw [← h_kd]
        exact h_div_mul
      exact_mod_cast (by rw [← h_div_mul_k]; ring : n * (σ 1 c) = c * (k * (σ 1 c)))
    rw [h_cast]
    have h_le_dvd := sigma_le_of_proper_dvd n c hn0 h_c.1 h_c.2
    have hc_ge : (c : ℤ) ≥ 0 := by omega
    nlinarith
  have h_sum_le : ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) ≤ (σ 1 n : ℤ) * (σ 1 n : ℤ) - 2 * (σ 1 n : ℤ) + 2 * (n : ℤ) + 1 := by
    rw [h_sum_LHS]
    have h_RHS_eq : (σ 1 n : ℤ) * (σ 1 n : ℤ) = ∑ c ∈ divisors n, ((c : ℤ) * (σ 1 n : ℤ)) := by
      rw [← Finset.sum_mul]
      have h_sigma : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
        simp [ArithmeticFunction.sigma_one_apply]
      rw [h_sigma, mul_comm]
    rw [h_RHS_eq, h_sum_RHS]
    rw [h_sigma_one]
    have h_sum_sub : ∑ c ∈ ((divisors n).erase 1).erase n, ((c : ℤ) * (σ 1 n : ℤ) - (c : ℤ)) =
        ∑ c ∈ ((divisors n).erase 1).erase n, ((c : ℤ) * (σ 1 n : ℤ)) - ∑ c ∈ ((divisors n).erase 1).erase n, (c : ℤ) := by
      rw [Finset.sum_sub_distrib]
    have h_sum_c : ∑ c ∈ ((divisors n).erase 1).erase n, (c : ℤ) = (σ 1 n : ℤ) - (n : ℤ) - 1 := by
      have h_sigma : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
        simp [ArithmeticFunction.sigma_one_apply]
      rw [h_sigma]
      have h_sum_er1 := Finset.sum_erase_add (divisors n) (fun (c : ℕ) => (c : ℤ)) h1_mem
      have h_sum_er2 := Finset.sum_erase_add ((divisors n).erase 1) (fun (c : ℕ) => (c : ℤ)) hn_mem
      dsimp only at h_sum_er1 h_sum_er2
      omega
    nlinarith [h_le_others, h_sum_sub, h_sum_c]
  have h_mul_LHS : (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) = ∑ c ∈ divisors n, ((n : ℤ) * (σ 1 c : ℤ)) := by
    rw [Finset.mul_sum]
  rw [h_mul_LHS]
  exact h_sum_le


lemma sigma_ge_two_n_plus_two (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) (h_ab : (σ 1 n : ℤ) > 2 * (n : ℤ)) (ha1 : a n = 1) :
    (σ 1 n : ℤ) ≥ 2 * (n : ℤ) + 2 := by
  have hn0 : n > 0 := by omega
  have h_le := sum_sigma_le_sigma_sq_strong n hn12 h_not_prime
  have h_a := a_eq_formula n
  have h_mul_a : (n : ℤ) * a n = 2 * (n : ℤ) * (σ 1 n : ℤ) - (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) := by
    rw [h_a, mul_sub, ← mul_assoc]
    ring
  rw [ha1, mul_one] at h_mul_a
  have h_quad : (σ 1 n : ℤ) * (σ 1 n : ℤ) - 2 * ((n : ℤ) + 1) * (σ 1 n : ℤ) + 3 * (n : ℤ) + 1 ≥ 0 := by
    nlinarith [h_le, h_mul_a]
  have h_cases : (σ 1 n : ℤ) = 2 * (n : ℤ) + 1 ∨ (σ 1 n : ℤ) ≥ 2 * (n : ℤ) + 2 := by
    omega
  rcases h_cases with h_eq | h_ge
  · rw [h_eq] at h_quad
    have h_neg : (2 * (n : ℤ) + 1) * (2 * (n : ℤ) + 1) - 2 * ((n : ℤ) + 1) * (2 * (n : ℤ) + 1) + 3 * (n : ℤ) + 1 = (n : ℤ) := by
      ring
    rw [h_neg] at h_quad
    omega
  · exact h_ge




lemma a_ge_two_of_deficient (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) (h_def : (σ 1 n : ℤ) < 2 * (n : ℤ)) :
    a n ≥ 2 := by
  have hn0 : n > 0 := by omega
  have h_le := sum_sigma_le_sigma_sq n hn0
  have h_a_eq := a_eq_formula n
  have h_mul_a : (n : ℤ) * a n = 2 * (n : ℤ) * (σ 1 n : ℤ) - (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) := by
    rw [h_a_eq, mul_sub, ← mul_assoc]
    ring
  have h_bound : (n : ℤ) * a n ≥ (σ 1 n : ℤ) * (2 * (n : ℤ) - (σ 1 n : ℤ)) := by
    nlinarith
  have h_def_diff : 2 * (n : ℤ) - (σ 1 n : ℤ) ≥ 1 := by omega
  have h_sigma_pos : (σ 1 n : ℤ) ≥ 0 := by
    have : (σ 1 n : ℤ) = ∑ c ∈ divisors n, (c : ℤ) := by
      simp [ArithmeticFunction.sigma_one_apply]
    rw [this]
    refine Finset.sum_nonneg ?_
    intro c hc
    omega
  have h_bound2 : (n : ℤ) * a n ≥ (σ 1 n : ℤ) := by
    have h_mul_le : (σ 1 n : ℤ) * (2 * (n : ℤ) - (σ 1 n : ℤ)) ≥ (σ 1 n : ℤ) * 1 := by
      refine mul_le_mul_of_nonneg_left ?_ h_sigma_pos
      omega
    rw [mul_one] at h_mul_le
    omega
  have h_sigma_ge := sigma_ge_three_add_n n hn12 h_not_prime
  by_contra hc_a
  push_neg at hc_a
  have h_mul_le_n : (n : ℤ) * a n ≤ (n : ℤ) * 1 := by
    refine mul_le_mul_of_nonneg_left ?_ (by omega)
    omega
  rw [mul_one] at h_mul_le_n
  omega

lemma a_ne_one_of_perfect (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) (h_perf : (σ 1 n : ℤ) = 2 * (n : ℤ)) :
    a n ≠ 1 := by
  intro hn1
  have hn0 : n > 0 := by omega
  have h_le := sum_sigma_le_sigma_sq_sub_five n hn12 h_not_prime
  have h_a := a_eq_formula n
  have h_mul_a : (n : ℤ) * a n = 2 * (n : ℤ) * (σ 1 n : ℤ) - (n : ℤ) * ∑ c ∈ divisors n, (σ 1 c : ℤ) := by
    rw [h_a, mul_sub, ← mul_assoc]
    ring
  have h_mul_a_eq : (n : ℤ) * a n = (n : ℤ) := by rw [hn1, mul_one]
  rw [h_perf] at h_mul_a h_le
  omega


lemma a_le_sigma_sub_four (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    a n ≤ (σ 1 n : ℤ) - 4 := by
  have h_eq := a_eq_formula n
  rcases exists_proper_divisor n hn12 h_not_prime with ⟨d, hd, hd1⟩
  have hd2 : d ≥ 2 := d_ge_two n hn12 d hd hd1
  have h_sigma_d := sigma_d_ge_three d hd2
  have h_le := sum_le_sum_divisors n hn12 d hd hd1
  have h_three := sum_three n hn12 d hd hd1
  have h_sigma_one : (σ 1 1 : ℤ) = 1 := by
    simp [ArithmeticFunction.sigma_one]
  omega

lemma composite_eq_mul (n : ℕ) (h_not_prime : ¬ n.Prime) (hn12 : n > 12) :
    ∃ p m, p.Prime ∧ m ≥ 2 ∧ n = p * m := by
  have hn2 : n ≥ 2 := by omega
  have h_minFac : (minFac n).Prime := minFac_prime (by omega)
  have h_dvd : minFac n ∣ n := minFac_dvd n
  let m := n / minFac n
  use minFac n, m
  have h_mul_eq : n = minFac n * m := (Nat.mul_div_cancel' h_dvd).symm
  refine ⟨h_minFac, ?_, h_mul_eq⟩
  have h_mul : m * minFac n = n := Nat.div_mul_cancel h_dvd
  have h_div_pos : m ≠ 0 := by
    intro h_zero
    rw [h_zero, zero_mul] at h_mul
    omega
  have h_div_not_one : m ≠ 1 := by
    intro h_one
    rw [h_one, one_mul] at h_mul
    have h_prime_n : n.Prime := by
      rw [← h_mul]
      exact h_minFac
    exact h_not_prime h_prime_n
  by_contra hc_m
  have : m ≤ 1 := by omega
  interval_cases m
  · contradiction
  · contradiction

lemma coprime_two_of_odd (x : ℕ) (hx : ¬ 2 ∣ x) : Coprime x 2 := by
  rw [Nat.Coprime]
  have h := Nat.gcd_dvd_right x 2
  have h_gcd_le : Nat.gcd x 2 ≤ 2 := Nat.le_of_dvd (by decide) h
  have h_gcd_pos : Nat.gcd x 2 > 0 := Nat.gcd_pos_of_pos_right x (by decide)
  have h_gcd_dvd := Nat.gcd_dvd_left x 2
  interval_cases Nat.gcd x 2
  · rfl
  · have h_dvd : 2 ∣ x := h_gcd_dvd
    contradiction

lemma dvd_two_mul_of_odd (m x : ℕ) (hm : m % 2 = 1) :
    x ∣ 2 * m ↔ x ∣ m ∨ (∃ y, y ∣ m ∧ x = 2 * y) := by
  constructor
  · intro h
    by_cases hx : 2 ∣ x
    · rcases hx with ⟨y, rfl⟩
      right
      use y
      refine ⟨?_, rfl⟩
      rcases h with ⟨k, hk⟩
      use k
      have h_eq : 2 * m = 2 * (y * k) := by
        rw [hk, mul_assoc]
      exact Nat.eq_of_mul_eq_mul_left (by decide) h_eq
    · left
      have h_cop := coprime_two_of_odd x hx
      rwa [Coprime.dvd_mul_left h_cop] at h
  · rintro (h1 | ⟨y, hy, rfl⟩)
    · exact dvd_mul_of_dvd_right h1 2
    · exact mul_dvd_mul_left 2 hy

lemma divisors_two_mul_of_odd (m : ℕ) (hm : m % 2 = 1) :
    divisors (2 * m) = divisors m ∪ Finset.map ⟨fun x => 2 * x, fun x y h => by dsimp at h; omega⟩ (divisors m) := by
  ext x
  simp only [mem_divisors, Finset.mem_union, Finset.mem_map, Function.Embedding.coeFn_mk]
  have hm0 : m ≠ 0 := by omega
  have h2m0 : 2 * m ≠ 0 := by omega
  simp [hm0, h2m0]
  rw [dvd_two_mul_of_odd m x hm]
  simp_rw [eq_comm]

lemma disjoint_divisors_map (m : ℕ) (hm : m % 2 = 1) :
    Disjoint (divisors m) (Finset.map ⟨fun x => 2 * x, fun x y h => by dsimp at h; omega⟩ (divisors m)) := by
  rw [Finset.disjoint_left]
  intro x hx h_map
  rw [Finset.mem_map] at h_map
  rcases h_map with ⟨y, hy, rfl⟩
  rw [mem_divisors] at hx
  rcases hx.1 with ⟨k, hk⟩
  have h_even : 2 * (y * k) = m := by
    rw [← mul_assoc]
    exact hk.symm
  have h_mod : m % 2 = 0 := by
    rw [← h_even]
    simp
  omega

lemma sigma_two_mul_of_odd (d : ℕ) (hd : d % 2 = 1) :
    (ArithmeticFunction.sigma 1 (2 * d) : ℤ) = 3 * (ArithmeticFunction.sigma 1 d : ℤ) := by
  have h_cop : Coprime d 2 := coprime_two_of_odd d (by omega)
  have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (@ArithmeticFunction.isMultiplicative_sigma 1) h_cop.symm
  have h_sigma_two : ArithmeticFunction.sigma 1 2 = 3 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  rw [h_mul, h_sigma_two]
  push_cast
  ring

lemma a_two_mul_of_odd (m : ℕ) (hm : m % 2 = 1) :
    ∃ k : ℤ, a (2 * m) = 2 * k := by
  have h_divs := divisors_two_mul_of_odd m hm
  have h_disj := disjoint_divisors_map m hm
  let emb : ℕ ↪ ℕ := ⟨fun x => 2 * x, fun x y h => by dsimp at h; omega⟩
  have h_sum : ∑ d ∈ divisors (2 * m), ((2 * d : ℤ) - (σ 1 d : ℤ)) =
      ∑ d ∈ divisors m, ((2 * d : ℤ) - (σ 1 d : ℤ)) +
      ∑ d ∈ Finset.map emb (divisors m), ((2 * d : ℤ) - (σ 1 d : ℤ)) := by
    have h_divs_eq : divisors (2 * m) = divisors m ∪ Finset.map emb (divisors m) := h_divs
    rw [h_divs_eq, Finset.sum_union h_disj]
  have h_map : ∑ d ∈ Finset.map emb (divisors m), ((2 * d : ℤ) - (σ 1 d : ℤ)) =
      ∑ d ∈ divisors m, ((2 * (2 * d) : ℤ) - (σ 1 (2 * d) : ℤ)) := by
    rw [Finset.sum_map]
    rfl
  rw [a, h_sum, h_map]
  have h_sigma : ∀ d ∈ divisors m, (σ 1 (2 * d) : ℤ) = 3 * (σ 1 d : ℤ) := by
    intro d hd
    rw [mem_divisors] at hd
    have hd_odd : d % 2 = 1 := by
      have hd_dvd : d ∣ m := hd.1
      rcases hd_dvd with ⟨k, rfl⟩
      rw [mul_mod] at hm
      have h_mod : (d % 2 * (k % 2)) % 2 = 1 := hm
      by_contra hc
      have : d % 2 = 0 := by omega
      rw [this, zero_mul, zero_mod] at h_mod
      omega
    exact sigma_two_mul_of_odd d hd_odd
  rw [← Finset.sum_add_distrib]
  have h_combine : ∑ d ∈ divisors m, (((2 * d : ℤ) - (σ 1 d : ℤ)) + ((2 * (2 * d) : ℤ) - (σ 1 (2 * d) : ℤ))) =
      ∑ d ∈ divisors m, (2 * (3 * (d : ℤ) - 2 * (σ 1 d : ℤ))) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    rw [h_sigma d hd]
    ring
  rw [h_combine, ← Finset.mul_sum]
  use ∑ d ∈ divisors m, (3 * (d : ℤ) - 2 * (σ 1 d : ℤ))

lemma a_ne_one_of_two_mul_odd (m : ℕ) (hm : m % 2 = 1) : a (2 * m) ≠ 1 := by
  intro h
  rcases a_two_mul_of_odd m hm with ⟨k, hk⟩
  rw [hk] at h
  omega

lemma even_cases (n : ℕ) (hn : 2 ∣ n) : (∃ m, m % 2 = 1 ∧ n = 2 * m) ∨ 4 ∣ n := by
  rcases hn with ⟨m, rfl⟩
  by_cases hm : m % 2 = 1
  · left
    use m
  · right
    have h_even : 2 ∣ m := by
      rw [Nat.dvd_iff_mod_eq_zero]
      omega
    rcases h_even with ⟨k, rfl⟩
    use k
    ring

def check_range (start len : ℕ) : Bool :=
  match len with
  | 0 => true
  | len' + 1 =>
    let n := start + len'
    (decide (n.Prime) || decide (a n ≠ 1)) && check_range start len'

lemma check_range_sound (start len n : ℕ) (h_check : check_range start len = true) (hn_ge : start ≤ n) (hn_lt : n < start + len) (hp : ¬ n.Prime) : a n ≠ 1 := by
  induction len with
  | zero =>
    omega
  | succ len' ih =>
    simp [check_range] at h_check
    rcases h_check with ⟨h_step, h_rec⟩
    by_cases hn_eq : n = start + len'
    · subst hn_eq
      simp [hp] at h_step
      exact h_step
    · have hn_lt' : n < start + len' := by omega
      exact ih h_rec hn_lt'

lemma a_ne_one_0 (n : ℕ) (h_start : n ≥ 13) (h_end : n ≤ 112) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 13 100 = true := by decide
  refine check_range_sound 13 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_1 (n : ℕ) (h_start : n ≥ 113) (h_end : n ≤ 212) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 113 100 = true := by decide
  refine check_range_sound 113 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_2 (n : ℕ) (h_start : n ≥ 213) (h_end : n ≤ 312) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 213 100 = true := by decide
  refine check_range_sound 213 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_3 (n : ℕ) (h_start : n ≥ 313) (h_end : n ≤ 412) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 313 100 = true := by decide
  refine check_range_sound 313 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_4 (n : ℕ) (h_start : n ≥ 413) (h_end : n ≤ 512) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 413 100 = true := by decide
  refine check_range_sound 413 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_5 (n : ℕ) (h_start : n ≥ 513) (h_end : n ≤ 612) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 513 100 = true := by decide
  refine check_range_sound 513 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_6 (n : ℕ) (h_start : n ≥ 613) (h_end : n ≤ 712) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 613 100 = true := by decide
  refine check_range_sound 613 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_7 (n : ℕ) (h_start : n ≥ 713) (h_end : n ≤ 812) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 713 100 = true := by decide
  refine check_range_sound 713 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_8 (n : ℕ) (h_start : n ≥ 813) (h_end : n ≤ 912) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 813 100 = true := by decide
  refine check_range_sound 813 100 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_9 (n : ℕ) (h_start : n ≥ 913) (h_end : n ≤ 1000) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  have h_check : check_range 913 88 = true := by decide
  refine check_range_sound 913 88 n h_check h_start (by omega) h_not_prime

lemma a_ne_one_small (n : ℕ) (hn12 : n > 12) (hn1000 : n ≤ 1000) (h_not_prime : ¬ n.Prime) : a n ≠ 1 := by
  by_cases h0 : n ≤ 112
  · exact a_ne_one_0 n (by omega) h0 h_not_prime
  · by_cases h1 : n ≤ 212
    · exact a_ne_one_1 n (by omega) h1 h_not_prime
    · by_cases h2 : n ≤ 312
      · exact a_ne_one_2 n (by omega) h2 h_not_prime
      · by_cases h3 : n ≤ 412
        · exact a_ne_one_3 n (by omega) h3 h_not_prime
        · by_cases h4 : n ≤ 512
          · exact a_ne_one_4 n (by omega) h4 h_not_prime
          · by_cases h5 : n ≤ 612
            · exact a_ne_one_5 n (by omega) h5 h_not_prime
            · by_cases h6 : n ≤ 712
              · exact a_ne_one_6 n (by omega) h6 h_not_prime
              · by_cases h7 : n ≤ 812
                · exact a_ne_one_7 n (by omega) h7 h_not_prime
                · by_cases h8 : n ≤ 912
                  · exact a_ne_one_8 n (by omega) h8 h_not_prime
                  · exact a_ne_one_9 n (by omega) hn1000 h_not_prime

lemma divisors_subset_four_dvd (n : ℕ) (hn12 : n > 12) (h4 : 4 ∣ n) :
    ({1, 2, 4, n/4, n/2, n} : Finset ℕ) ⊆ n.divisors := by
  have h2 : 2 ∣ n := by
    rcases h4 with ⟨k, hk⟩
    use 2 * k
    omega
  have h_div4 : 4 ∈ n.divisors := mem_divisors.mpr ⟨h4, by omega⟩
  have h_div2 : 2 ∈ n.divisors := mem_divisors.mpr ⟨h2, by omega⟩
  have h_div1 : 1 ∈ n.divisors := one_mem_divisors.mpr (by omega)
  have h_divn : n ∈ n.divisors := mem_divisors.mpr ⟨dvd_rfl, by omega⟩
  have h_div_n2 : n / 2 ∈ n.divisors := by
    rw [mem_divisors]
    refine ⟨Nat.div_dvd_of_dvd h2, by omega⟩
  have h_div_n4 : n / 4 ∈ n.divisors := by
    rw [mem_divisors]
    refine ⟨Nat.div_dvd_of_dvd h4, by omega⟩
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h_div1
  · exact h_div2
  · exact h_div4
  · exact h_div_n4
  · exact h_div_n2
  · exact h_divn

lemma sum_subset_le_sum_divisors_four_dvd (n : ℕ) (hn12 : n > 12) (h4 : 4 ∣ n) :
    ∑ d ∈ ({1, 2, 4, n/4, n/2, n} : Finset ℕ), (σ 1 d : ℤ) ≤ ∑ d ∈ n.divisors, (σ 1 d : ℤ) := by
  have h_sub := divisors_subset_four_dvd n hn12 h4
  refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
  intro x hx hx_not
  have : (σ 1 x : ℤ) ≥ 0 := by
    have h_eq : (σ 1 x : ℤ) = ∑ c ∈ divisors x, (c : ℤ) := by
      simp [ArithmeticFunction.sigma_one_apply]
    rw [h_eq]
    refine Finset.sum_nonneg ?_
    intro c hc
    omega
  omega

lemma sum_six_divisors (n : ℕ) (hn1000 : n > 1000) (h4 : 4 ∣ n) :
    ∑ c ∈ ({1, 2, 4, n/4, n/2, n} : Finset ℕ), (σ 1 c : ℤ) =
      (σ 1 1 : ℤ) + (σ 1 2 : ℤ) + (σ 1 4 : ℤ) + (σ 1 (n/4) : ℤ) + (σ 1 (n/2) : ℤ) + (σ 1 n : ℤ) := by
  have hn2 : 2 < n/4 := by omega
  have hn4 : 4 < n/4 := by omega
  have hn_div : n/4 < n/2 := by omega
  have hn_div2 : n/2 < n := by omega
  have h_not_mem1 : 1 ∉ ({2, 4, n/4, n/2, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
  have h_not_mem2 : 2 ∉ ({4, n/4, n/2, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h
    · omega
    · omega
    · omega
    · omega
  have h_not_mem3 : 4 ∉ ({n/4, n/2, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h
    · omega
    · omega
    · omega
  have h_not_mem4 : n/4 ∉ ({n/2, n} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h
    · omega
    · omega
  have h_not_mem5 : n/2 ∉ ({n} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    intro hc
    omega
  rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_insert h_not_mem3, Finset.sum_insert h_not_mem4, Finset.sum_insert h_not_mem5, Finset.sum_singleton]
  ring

lemma a_le_of_four_dvd (n : ℕ) (hn1000 : n > 1000) (h4 : 4 ∣ n) :
    a n ≤ (σ 1 n : ℤ) - (σ 1 (n/2) : ℤ) - (σ 1 (n/4) : ℤ) - 11 := by
  have hn12 : n > 12 := by omega
  have h_eq := a_eq_formula n
  have h_sub := sum_subset_le_sum_divisors_four_dvd n hn12 h4
  have h_six := sum_six_divisors n hn1000 h4
  have h_sig1 : (σ 1 1 : ℤ) = 1 := by simp [ArithmeticFunction.sigma_one]
  have h_sig2 : (σ 1 2 : ℤ) = 3 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  have h_sig4 : (σ 1 4 : ℤ) = 7 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  rw [h_six, h_sig1, h_sig2, h_sig4] at h_sub
  omega


lemma dvd_four_cases {x : ℕ} (hx : x ∣ 4) (hx0 : x ≠ 0) : x = 1 ∨ x = 2 ∨ x = 4 := by
  have h_pos : x ≥ 1 := Nat.pos_of_ne_zero hx0
  have : x ≤ 4 := Nat.le_of_dvd (by decide) hx
  interval_cases x
  · left; rfl
  · right; left; rfl
  · exfalso
    revert hx
    decide
  · right; right; rfl

lemma divisors_four_mul_prime (k : ℕ) (hk : k.Prime) (hk2 : k > 2) :
    (4 * k).divisors = {1, 2, 4, k, 2 * k, 4 * k} := by
  ext x
  simp only [mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  have h4k_ne : 4 * k ≠ 0 := by omega
  rw [and_iff_left h4k_ne]
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by
      intro h_zero
      subst h_zero
      exact h4k_ne (zero_dvd_iff.mp hx)
    have h_or : k.Coprime x ∨ k ∣ x := Nat.coprime_or_dvd_of_prime hk x
    rcases h_or with h_cop | h_dvd
    · have h_dvd_4 : x ∣ 4 := h_cop.symm.dvd_of_dvd_mul_right hx
      have h_cases := dvd_four_cases h_dvd_4 hx0
      rcases h_cases with rfl | rfl | rfl
      · left; rfl
      · right; left; rfl
      · right; right; left; rfl
    · rcases h_dvd with ⟨y, rfl⟩
      have hx_rew : k * y ∣ k * 4 := by
        rw [mul_comm k 4]
        exact hx
      have hk0 : 0 < k := by omega
      rw [Nat.mul_dvd_mul_iff_left hk0] at hx_rew
      have hy0 : y ≠ 0 := by
        intro hy_zero
        subst hy_zero
        simp at hx0
      have h_cases := dvd_four_cases hx_rew hy0
      rcases h_cases with rfl | rfl | rfl
      · right; right; right; left; ring
      · right; right; right; right; left; ring
      · right; right; right; right; right; ring
  · intro hx
    rcases hx with rfl | rfl | h
    · exact one_dvd (4 * k)
    · use 2 * k; ring
    · rcases h with rfl | rfl | h2
      · use k
      · use 4; ring
      · rcases h2 with rfl | rfl
        · use 2; ring
        · exact dvd_rfl

lemma a_four_mul_prime (k : ℕ) (hk : k.Prime) (hk_gt : k > 250) :
    a (4 * k) = 3 * (k : ℤ) - 8 := by
  have hk2 : k > 2 := by omega
  have h_divs := divisors_four_mul_prime k hk hk2
  have h_not_mem1 : 1 ∉ ({2, 4, k, 2 * k, 4 * k} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h | h <;> omega
  have h_not_mem2 : 2 ∉ ({4, k, 2 * k, 4 * k} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h <;> omega
  have h_not_mem3 : 4 ∉ ({k, 2 * k, 4 * k} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h <;> omega
  have h_not_mem4 : k ∉ ({2 * k, 4 * k} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h <;> omega
  have h_not_mem5 : 2 * k ∉ ({4 * k} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    intro hc
    omega
  have h_sum : a (4 * k) =
      (2 * 1 - (σ 1 1 : ℤ)) +
      (2 * 2 - (σ 1 2 : ℤ)) +
      (2 * 4 - (σ 1 4 : ℤ)) +
      (2 * (k : ℤ) - (σ 1 k : ℤ)) +
      (2 * (2 * k : ℤ) - (σ 1 (2 * k) : ℤ)) +
      (2 * (4 * k : ℤ) - (σ 1 (4 * k) : ℤ)) := by
    rw [a, h_divs]
    rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_insert h_not_mem3, Finset.sum_insert h_not_mem4, Finset.sum_insert h_not_mem5, Finset.sum_singleton]
    push_cast
    ring
  have h_sig1 : (σ 1 1 : ℤ) = 1 := by simp [ArithmeticFunction.sigma_one]
  have h_sig2 : (σ 1 2 : ℤ) = 3 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  have h_sig4 : (σ 1 4 : ℤ) = 7 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  have h_sigk : (σ 1 k : ℤ) = k + 1 := by
    have h_div : divisors k = {1, k} := hk.divisors
    have h_not_mem : 1 ∉ ({k} : Finset ℕ) := by simp [hk.ne_one.symm]
    have h_eq : σ 1 k = 1 + k := by
      simp [ArithmeticFunction.sigma_one_apply, h_div, Finset.sum_insert h_not_mem]
    rw [h_eq]
    omega
  have h_odd : ¬ 2 ∣ k := by
    intro hd
    have h_cases := hk.eq_one_or_self_of_dvd 2 hd
    omega
  have h_sig2k : (σ 1 (2 * k) : ℤ) = 3 * (k + 1) := by
    have h_cop : Coprime 2 k := (coprime_two_of_odd k h_odd).symm
    have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (@ArithmeticFunction.isMultiplicative_sigma 1) h_cop
    have h_sigma_two : ArithmeticFunction.sigma 1 2 = 3 := by
      simp [ArithmeticFunction.sigma_apply]
      decide
    rw [h_mul, h_sigma_two]
    push_cast
    have h_div : divisors k = {1, k} := hk.divisors
    have h_not_mem : 1 ∉ ({k} : Finset ℕ) := by simp [hk.ne_one.symm]
    have h_eq : σ 1 k = 1 + k := by
      simp [ArithmeticFunction.sigma_one_apply, h_div, Finset.sum_insert h_not_mem]
    rw [h_eq]
    push_cast
    ring
  have h_sig4k : (σ 1 (4 * k) : ℤ) = 7 * (k + 1) := by
    have h_cop : Coprime 4 k := by
      have h_copk4 : Coprime k 4 := by
        have : ¬ k ∣ 4 := by
          intro hd
          have : k ≤ 4 := Nat.le_of_dvd (by decide) hd
          omega
        exact (Nat.Prime.coprime_iff_not_dvd hk).mpr this
      exact h_copk4.symm
    have h_mul := ArithmeticFunction.IsMultiplicative.map_mul_of_coprime (@ArithmeticFunction.isMultiplicative_sigma 1) h_cop
    have h_sigma_four : ArithmeticFunction.sigma 1 4 = 7 := by
      simp [ArithmeticFunction.sigma_apply]
      decide
    rw [h_mul, h_sigma_four]
    push_cast
    have h_div : divisors k = {1, k} := hk.divisors
    have h_not_mem : 1 ∉ ({k} : Finset ℕ) := by simp [hk.ne_one.symm]
    have h_eq : σ 1 k = 1 + k := by
      simp [ArithmeticFunction.sigma_one_apply, h_div, Finset.sum_insert h_not_mem]
    rw [h_eq]
    push_cast
    ring
  rw [h_sum, h_sig1, h_sig2, h_sig4, h_sigk, h_sig2k, h_sig4k]
  ring



lemma divisors_subset_composite (k x : ℕ) (hk_gt : k > 250) (hx_mem : x ∈ (4 * k).divisors) :
    ({1, 2, 4, k, 2 * k, 4 * k, x} : Finset ℕ) ⊆ (4 * k).divisors := by
  intro y hy
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact one_mem_divisors.mpr (by omega)
  · rw [mem_divisors]; exact ⟨dvd_mul_of_dvd_right (dvd_refl 2) k, by omega⟩
  · rw [mem_divisors]; exact ⟨dvd_mul_right 4 k, by omega⟩
  · rw [mem_divisors]; exact ⟨dvd_mul_left k 4, by omega⟩
  · rw [mem_divisors]; exact ⟨⟨2, by ring⟩, by omega⟩
  · rw [mem_divisors]; exact ⟨dvd_rfl, by omega⟩
  · exact hx_mem

lemma sum_subset_le_sum_divisors_composite (k x : ℕ) (hk_gt : k > 250) (hx_mem : x ∈ (4 * k).divisors) :
    ∑ d ∈ ({1, 2, 4, k, 2 * k, 4 * k, x} : Finset ℕ), (σ 1 d : ℤ) ≤ ∑ d ∈ (4 * k).divisors, (σ 1 d : ℤ) := by
  have h_sub := divisors_subset_composite k x hk_gt hx_mem
  refine Finset.sum_le_sum_of_subset_of_nonneg h_sub ?_
  intro y hy hy_not
  have : (σ 1 y : ℤ) = ∑ c ∈ divisors y, (c : ℤ) := by
    simp [ArithmeticFunction.sigma_one_apply]
  rw [this]
  refine Finset.sum_nonneg ?_
  intro c hc
  omega

lemma sum_seven_divisors (k x : ℕ) (hk_gt : k > 250) (hx_not : x ∉ ({1, 2, 4, k, 2 * k, 4 * k} : Finset ℕ)) :
    ∑ c ∈ ({1, 2, 4, k, 2 * k, 4 * k, x} : Finset ℕ), (σ 1 c : ℤ) =
      (σ 1 1 : ℤ) + (σ 1 2 : ℤ) + (σ 1 4 : ℤ) + (σ 1 k : ℤ) + (σ 1 (2 * k) : ℤ) + (σ 1 (4 * k) : ℤ) + (σ 1 x : ℤ) := by
  have h_not_mem1 : 1 ∉ ({2, 4, k, 2 * k, 4 * k, x} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · omega
    · exact hx_not (by simp)
  have h_not_mem2 : 2 ∉ ({4, k, 2 * k, 4 * k, x} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h | h
    · omega
    · omega
    · omega
    · omega
    · exact hx_not (by simp)
  have h_not_mem3 : 4 ∉ ({k, 2 * k, 4 * k, x} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h | h
    · omega
    · omega
    · omega
    · exact hx_not (by simp)
  have h_not_mem4 : k ∉ ({2 * k, 4 * k, x} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h | h
    · omega
    · omega
    · exact hx_not (by simp)
  have h_not_mem5 : 2 * k ∉ ({4 * k, x} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    intro hc
    rcases hc with h | h
    · omega
    · exact hx_not (by simp)
  have h_not_mem6 : 4 * k ∉ ({x} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    intro hc
    subst hc
    exact hx_not (by simp)
  rw [Finset.sum_insert h_not_mem1, Finset.sum_insert h_not_mem2, Finset.sum_insert h_not_mem3, Finset.sum_insert h_not_mem4, Finset.sum_insert h_not_mem5, Finset.sum_insert h_not_mem6, Finset.sum_singleton]
  ring

lemma a_le_of_four_dvd_composite (k x : ℕ) (hk_gt : k > 250) (hx_mem : x ∈ (4 * k).divisors)
    (hx_not : x ∉ ({1, 2, 4, k, 2 * k, 4 * k} : Finset ℕ)) :
    a (4 * k) ≤ (σ 1 (4 * k) : ℤ) - (σ 1 (2 * k) : ℤ) - (σ 1 k : ℤ) - (σ 1 x : ℤ) - 11 := by
  have h_eq := a_eq_formula (4 * k)
  have h_sub := sum_subset_le_sum_divisors_composite k x hk_gt hx_mem
  have h_seven := sum_seven_divisors k x hk_gt hx_not
  have h_sig1 : (σ 1 1 : ℤ) = 1 := by simp [ArithmeticFunction.sigma_one]
  have h_sig2 : (σ 1 2 : ℤ) = 3 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  have h_sig4 : (σ 1 4 : ℤ) = 7 := by
    simp [ArithmeticFunction.sigma_apply]
    decide
  rw [h_seven, h_sig1, h_sig2, h_sig4] at h_sub
  omega

lemma a_ne_one_of_abundant (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) (h_abund : (σ 1 n : ℤ) > 2 * (n : ℤ)) :
    a n ≠ 1 := by
  sorry


lemma a_ne_one (n : ℕ) (hn12 : n > 12) (h_not_prime : ¬ n.Prime) :
    a n ≠ 1 := by
  by_cases h1000 : n ≤ 1000
  · exact a_ne_one_small n hn12 h1000 h_not_prime
  · by_cases h_def : (σ 1 n : ℤ) < 2 * (n : ℤ)
    · have := a_ge_two_of_deficient n hn12 h_not_prime h_def
      omega
    · by_cases h_perf : (σ 1 n : ℤ) = 2 * (n : ℤ)
      · exact a_ne_one_of_perfect n hn12 h_not_prime h_perf
      · have h_abund : (σ 1 n : ℤ) > 2 * (n : ℤ) := by omega
        exact a_ne_one_of_abundant n hn12 h_not_prime h_abund
theorem oeis_296075_conjecture_0 : ∀ n : ℕ,
  a n = 1 ↔ n = 1 ∨ n = 12 := by
  intro n
  constructor
  · intro h
    by_cases hn : n ≤ 12
    · interval_cases n
      · revert h; decide
      · exact Or.inl rfl
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · revert h; decide
      · exact Or.inr rfl
    · -- n > 12
      by_cases hp : n.Prime
      · have h_ap : a n = n := a_of_prime n hp
        omega
      · -- n is composite and n > 12
        exfalso
        have hn12 : n > 12 := by omega
        exact a_ne_one n hn12 hp h
  · intro h
    rcases h with rfl | rfl
    · rfl
    · rfl
