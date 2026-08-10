import FormalConjectures.Util.ProblemImports

open Nat Finset Set BigOperators

lemma Nat.sInf_eq {s : Set ℕ} {a : ℕ} (ha : a ∈ s) (h_low : ∀ x ∈ s, a ≤ x) : sInf s = a := by
  have : IsLeast s a := ⟨ha, h_low⟩
  exact IsLeast.csInf_eq this

/--
$P_k$ is the product of the first $k$ primes.
-/
noncomputable def prod_first_k_primes (k : ℕ) : ℕ :=
  (range k).prod (fun i => Nat.nth Nat.Prime i)

/--
A210186: $a(n) = \text{least integer } m>1 \text{ such that } m \text{ divides none of } P_i + P_j$
with $0<i<j \le n$ where $P_k$ is the product of the first $k$ primes.
-/
noncomputable def A210186 (n : ℕ) : ℕ :=
  sInf { m : ℕ |
    1 < m ∧
    ∀ i j : ℕ,
      (1 ≤ i ∧ i < j ∧ j ≤ n) →
      ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }

/--
A210186 Conjecture: all the terms are primes and a(n) < n^2 for all n > 1.
- $\forall n : \mathbb{N}, \text{Prime } (A210186(n))$
- $\forall n : \mathbb{N}, n > 1 \implies A210186(n) < n^2$
-/

lemma prod_first_k_primes_zero : prod_first_k_primes 0 = 1 := by
  unfold prod_first_k_primes
  rw [prod_range_zero]

lemma prod_first_k_primes_one : prod_first_k_primes 1 = 2 := by
  unfold prod_first_k_primes
  rw [prod_range_succ, prod_range_zero]
  rw [nth_prime_zero_eq_two]
  rfl

lemma prod_first_k_primes_two : prod_first_k_primes 2 = 6 := by
  unfold prod_first_k_primes
  rw [prod_range_succ, prod_range_succ, prod_range_zero]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three]
  rfl

lemma prod_first_k_primes_three : prod_first_k_primes 3 = 30 := by
  unfold prod_first_k_primes
  rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five]
  rfl

lemma prod_first_k_primes_four : prod_first_k_primes 4 = 210 := by
  unfold prod_first_k_primes
  rw [prod_range_succ, prod_range_succ, prod_range_succ, prod_range_succ, prod_range_zero]
  rw [nth_prime_zero_eq_two, nth_prime_one_eq_three, nth_prime_two_eq_five, nth_prime_three_eq_seven]
  rfl

lemma prod_first_k_primes_mono {a b : ℕ} (h : a ≤ b) : prod_first_k_primes a ≤ prod_first_k_primes b := by
  dsimp [prod_first_k_primes]
  have h_subset : range a ⊆ range b := by
    intro x hx
    simp at hx
    simp
    omega
  exact Finset.prod_le_prod_of_subset_of_one_le' h_subset (fun i _ => by
    have : 2 ≤ Nat.nth Nat.Prime i := Nat.Prime.two_le (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i)
    omega)

lemma prod_first_k_primes_pos (k : ℕ) : 0 < prod_first_k_primes k := by
  dsimp [prod_first_k_primes]
  exact prod_pos (fun i _ => by
    have : 2 ≤ Nat.nth Nat.Prime i := Nat.Prime.two_le (Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i)
    omega)


theorem A210186_zero : A210186 0 = 2 := by
  have h2 : 2 ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 0) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } := by
    simp
    intro i j hi hj h_j
    omega
  have h_low : ∀ m ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 0) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }, 2 ≤ m := by
    intro m hm
    simp at hm
    omega
  exact Nat.sInf_eq h2 h_low


lemma A210186_one : A210186 1 = 2 := by
  have h2 : 2 ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 1) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } := by
    simp
    intro i j hi hij hj
    omega
  have h_low : ∀ m ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 1) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }, 2 ≤ m := by
    intro m hm
    simp at hm
    omega
  exact Nat.sInf_eq h2 h_low


lemma A210186_two : A210186 2 = 3 := by
  have h3 : 3 ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 2) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } := by
    simp only [Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    intro i j hij
    have hi : 1 ≤ i := hij.1
    have h_cond : i < j := hij.2.1
    have hj : j ≤ 2 := hij.2.2
    have hi1 : i = 1 := by omega
    have hj2 : j = 2 := by omega
    subst hi1 hj2
    rw [prod_first_k_primes_one, prod_first_k_primes_two]
    decide
  have h_low : ∀ m ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 2) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }, 3 ≤ m := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    by_contra h_lt
    have : m = 2 := by omega
    subst this
    have h_dvd := hm.2 1 2 ⟨by decide, by decide, by decide⟩
    apply h_dvd
    rw [prod_first_k_primes_one, prod_first_k_primes_two]
    decide
  exact Nat.sInf_eq h3 h_low

lemma A210186_three : A210186 3 = 5 := by
  have h5 : 5 ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 3) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } := by
    simp only [Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    intro i j hij
    have hi : 1 ≤ i := hij.1
    have h_cond : i < j := hij.2.1
    have hj : j ≤ 3 := hij.2.2
    have h_cases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 3) := by omega
    rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [prod_first_k_primes_one, prod_first_k_primes_two]; decide
    · rw [prod_first_k_primes_one, prod_first_k_primes_three]; decide
    · rw [prod_first_k_primes_two, prod_first_k_primes_three]; decide
  have h_low : ∀ m ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 3) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }, 5 ≤ m := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    by_contra h_lt
    have h_cases : m = 2 ∨ m = 3 ∨ m = 4 := by omega
    rcases h_cases with rfl | rfl | rfl
    · have h_dvd := hm.2 1 2 ⟨by decide, by decide, by decide⟩
      apply h_dvd
      rw [prod_first_k_primes_one, prod_first_k_primes_two]
      decide
    · have h_dvd := hm.2 2 3 ⟨by decide, by decide, by decide⟩
      apply h_dvd
      rw [prod_first_k_primes_two, prod_first_k_primes_three]
      decide
    · have h_dvd := hm.2 1 2 ⟨by decide, by decide, by decide⟩
      apply h_dvd
      rw [prod_first_k_primes_one, prod_first_k_primes_two]
      decide
  exact Nat.sInf_eq h5 h_low

lemma A210186_four : A210186 4 = 7 := by
  have h7 : 7 ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 4) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } := by
    simp only [Set.mem_setOf_eq]
    refine ⟨by omega, ?_⟩
    intro i j hij
    have hi : 1 ≤ i := hij.1
    have h_cond : i < j := hij.2.1
    have hj : j ≤ 4 := hij.2.2
    have h_cases : (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) ∨ (i = 1 ∧ j = 4) ∨
                   (i = 2 ∧ j = 3) ∨ (i = 2 ∧ j = 4) ∨ (i = 3 ∧ j = 4) := by omega
    rcases h_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [prod_first_k_primes_one, prod_first_k_primes_two]; decide
    · rw [prod_first_k_primes_one, prod_first_k_primes_three]; decide
    · rw [prod_first_k_primes_one, prod_first_k_primes_four]; decide
    · rw [prod_first_k_primes_two, prod_first_k_primes_three]; decide
    · rw [prod_first_k_primes_two, prod_first_k_primes_four]; decide
    · rw [prod_first_k_primes_three, prod_first_k_primes_four]; decide
  have h_low : ∀ m ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ 4) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }, 7 ≤ m := by
    intro m hm
    simp only [Set.mem_setOf_eq] at hm
    by_contra h_lt
    have h_cases : m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 := by omega
    rcases h_cases with rfl | rfl | rfl | rfl | rfl
    · have h_dvd := hm.2 1 2 ⟨by decide, by decide, by decide⟩
      apply h_dvd; rw [prod_first_k_primes_one, prod_first_k_primes_two]; decide
    · have h_dvd := hm.2 2 3 ⟨by decide, by decide, by decide⟩
      apply h_dvd; rw [prod_first_k_primes_two, prod_first_k_primes_three]; decide
    · have h_dvd := hm.2 1 2 ⟨by decide, by decide, by decide⟩
      apply h_dvd; rw [prod_first_k_primes_one, prod_first_k_primes_two]; decide
    · have h_dvd := hm.2 3 4 ⟨by decide, by decide, by decide⟩
      apply h_dvd; rw [prod_first_k_primes_three, prod_first_k_primes_four]; decide
    · have h_dvd := hm.2 2 3 ⟨by decide, by decide, by decide⟩
      apply h_dvd; rw [prod_first_k_primes_two, prod_first_k_primes_three]; decide
  exact Nat.sInf_eq h7 h_low


noncomputable def T_set (n : ℕ) : Finset ℕ :=
  Finset.biUnion (Finset.filter (fun p : ℕ × ℕ => p.1 < p.2) (Finset.product (Finset.Icc 1 n) (Finset.Icc 1 n)))
    (fun p => (prod_first_k_primes p.1 + prod_first_k_primes p.2).primeFactors)


lemma prime_notin_T_set_iff (n : ℕ) {p : ℕ} (hp : p.Prime) :
    p ∉ T_set n ↔ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ n) → ¬ p ∣ (prod_first_k_primes i + prod_first_k_primes j) := by
  dsimp [T_set]
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro h i j hij hdvd
    apply h
    use (i, j)
    refine ⟨by simp; omega, ?_⟩
    rw [Nat.mem_primeFactors]
    refine ⟨hp, hdvd, ?_⟩
    have h1 := prod_first_k_primes_pos i
    have h2 := prod_first_k_primes_pos j
    linarith
  · rintro h ⟨a, ha_prod, hp_mem⟩
    simp only [and_imp] at h
    rw [Nat.mem_primeFactors] at hp_mem
    have h_cond : 1 ≤ a.1 ∧ a.1 < a.2 ∧ a.2 ≤ n := by omega
    exact h a.1 a.2 h_cond.1 h_cond.2.1 h_cond.2.2 hp_mem.2.1


lemma prime_mem_S_iff (n : ℕ) {p : ℕ} (hp : p.Prime) :
    p ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ n) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } ↔ p ∉ T_set n := by
  simp only [Set.mem_setOf_eq]
  constructor
  · intro h
    rw [prime_notin_T_set_iff n hp]
    exact h.2
  · intro h
    refine ⟨Nat.Prime.one_lt hp, ?_⟩
    rw [← prime_notin_T_set_iff n hp]
    exact h


lemma S_nonempty (n : ℕ) :
    { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ n) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }.Nonempty := by
  -- Let M = 2 * prod_first_k_primes n + 2
  let M := 2 * prod_first_k_primes n + 2
  -- By Nat.exists_infinite_primes, there is a prime p >= M
  obtain ⟨p, hp_ge, hp_prime⟩ := Nat.exists_infinite_primes M
  refine ⟨p, ?_⟩
  simp
  constructor
  · have hM : 2 ≤ M := by
      have hpos := prod_first_k_primes_pos n
      omega
    have : 2 ≤ p := hp_ge.trans' hM
    exact Nat.Prime.one_lt hp_prime
  · intro i j hi hij hj hdvd
    have h_i_le_n : i ≤ n := by omega
    have h_j_le_n : j ≤ n := by omega
    have h_Pi_le : prod_first_k_primes i ≤ prod_first_k_primes n := prod_first_k_primes_mono h_i_le_n
    have h_Pj_le : prod_first_k_primes j ≤ prod_first_k_primes n := prod_first_k_primes_mono h_j_le_n
    have h_sum_le : prod_first_k_primes i + prod_first_k_primes j ≤ 2 * prod_first_k_primes n := by omega
    have h_sum_lt_p : prod_first_k_primes i + prod_first_k_primes j < p := by omega
    have h_sum_pos : 0 < prod_first_k_primes i + prod_first_k_primes j := by
      have h_Pi_pos := prod_first_k_primes_pos i
      omega
    have h_le_of_dvd := Nat.le_of_dvd h_sum_pos hdvd
    omega

lemma A210186_mem (n : ℕ) : A210186 n ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ n) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } :=
  Nat.sInf_mem (S_nonempty n)

lemma A210186_gt_one (n : ℕ) : 1 < A210186 n :=
  (A210186_mem n).1

lemma A210186_not_dvd (n : ℕ) {i j : ℕ} (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ n) : ¬ (A210186 n ∣ (prod_first_k_primes i + prod_first_k_primes j)) :=
  (A210186_mem n).2 i j ⟨hi, hij, hj⟩

lemma A210186_le_of_mem (n : ℕ) {m : ℕ} (hm : m ∈ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ n) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) }) : A210186 n ≤ m :=
  Nat.sInf_le hm


lemma A210186_mono {a b : ℕ} (hab : a ≤ b) : A210186 a ≤ A210186 b := by
  apply A210186_le_of_mem
  have h_mem := A210186_mem b
  simp only [Set.mem_setOf_eq] at h_mem ⊢
  refine ⟨h_mem.1, ?_⟩
  intro i j hij
  apply h_mem.2
  omega


lemma prime_dvd_prod_iff {p : ℕ} (hp : p.Prime) {s : Finset ℕ} {f : ℕ → ℕ} :
    p ∣ s.prod f ↔ ∃ i ∈ s, p ∣ f i := by
  have h_prime : _root_.Prime p := hp.prime
  exact _root_.Prime.dvd_finset_prod_iff h_prime f

lemma prime_dvd_prod_first_k_primes {p : ℕ} (hp : p.Prime) {k : ℕ} :
    p ∣ prod_first_k_primes k ↔ ∃ i < k, p = Nat.nth Nat.Prime i := by
  unfold prod_first_k_primes
  rw [prime_dvd_prod_iff hp]
  simp only [Finset.mem_range]
  have h_eq (i : ℕ) : p ∣ Nat.nth Nat.Prime i ↔ p = Nat.nth Nat.Prime i := by
    have h_nth : (Nat.nth Nat.Prime i).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
    constructor
    · intro hdvd
      exact ((Nat.Prime.dvd_iff_eq h_nth hp.ne_one).mp hdvd).symm
    · rintro rfl
      exact dvd_rfl
  simp_rw [h_eq]

lemma prime_nth_dvd_sum (n : ℕ) (k : ℕ) (hk : k ≤ n - 2) (hn : 2 ≤ n) :
    Nat.nth Nat.Prime k ∣ prod_first_k_primes (k + 1) + prod_first_k_primes n := by
  have hp : (Nat.nth Nat.Prime k).Prime := Nat.nth_mem_of_infinite Nat.infinite_setOf_prime k
  have hdvd1 : Nat.nth Nat.Prime k ∣ prod_first_k_primes (k + 1) := by
    rw [prime_dvd_prod_first_k_primes hp]
    use k
    refine ⟨by omega, rfl⟩
  have hdvd2 : Nat.nth Nat.Prime k ∣ prod_first_k_primes n := by
    rw [prime_dvd_prod_first_k_primes hp]
    use k
    have : k < n := by omega
    refine ⟨this, rfl⟩
  exact dvd_add hdvd1 hdvd2

lemma nth_prime_ge_idx (n : ℕ) : n + 2 ≤ Nat.nth Nat.Prime n := by
  induction n with
  | zero =>
    rw [nth_prime_zero_eq_two]
  | succ n ih =>
    have h1 := (nth_lt_nth Nat.infinite_setOf_prime).mpr (Nat.lt_succ_self n)
    change nth (fun p => Nat.Prime p) n < nth (fun p => Nat.Prime p) (n + 1) at h1
    change n + 2 ≤ nth (fun p => Nat.Prime p) n at ih
    change n + 1 + 2 ≤ nth (fun p => Nat.Prime p) (n + 1)
    omega

lemma prime_le_nth_prime_of_lt {p : ℕ} (hp : p.Prime) {n : ℕ} (hp_lt : p < Nat.nth Nat.Prime n) :
    ∃ k < n, p = Nat.nth Nat.Prime k := by
  have hp_mem : p ∈ {x | Nat.Prime x} := hp
  have h_range := range_nth_of_infinite Nat.infinite_setOf_prime
  rw [← h_range] at hp_mem
  obtain ⟨k, hk_eq⟩ := hp_mem
  use k
  constructor
  · by_contra h
    have : n ≤ k := by omega
    have h_le := (nth_le_nth Nat.infinite_setOf_prime).mpr this
    change Nat.nth Nat.Prime n ≤ Nat.nth Nat.Prime k at h_le
    rw [hk_eq] at h_le
    omega
  · exact hk_eq.symm

lemma prime_dvd_P_of_lt {p : ℕ} (hp : p.Prime) {n : ℕ} (hp_lt : p < Nat.nth Nat.Prime n) :
    p ∣ prod_first_k_primes n := by
  rw [prime_dvd_prod_first_k_primes hp]
  exact prime_le_nth_prime_of_lt hp hp_lt

lemma prime_of_coprime_and_lt_sq {n : ℕ} (h_coprime : Nat.gcd (A210186 n) (prod_first_k_primes (n - 1)) = 1)
    (h_lt : A210186 n < n^2) (hn : 5 ≤ n) : Nat.Prime (A210186 n) := by
  let M := A210186 n
  have hM_gt : 1 < M := A210186_gt_one n
  by_contra h_not_prime
  have h_comp : ∃ a b, 1 < a ∧ a ≤ b ∧ b < M ∧ M = a * b := by
    have h_exists_dvd : ∃ d, 1 < d ∧ d < M ∧ d ∣ M := by
      by_contra h_no_dvd
      push_neg at h_no_dvd
      have h_prime : Nat.Prime M := by
        refine Nat.prime_def_lt.mpr ⟨hM_gt, ?_⟩
        intro m hm_dvd hm_lt
        by_cases hm1 : m = 1
        · exact hm1
        · have hm_pos : 0 < m := Nat.pos_of_dvd_of_pos hm_lt (by omega : 0 < M)
          have : 1 < m := by omega
          have := h_no_dvd m this hm_dvd hm_lt
          contradiction
      exact h_not_prime h_prime
    obtain ⟨a, ha1, ha_lt, ha_dvd⟩ := h_exists_dvd
    obtain ⟨b, hb_eq⟩ := ha_dvd
    have hb1 : 1 < b := by
      by_contra h_le
      have : b = 0 ∨ b = 1 := by omega
      rcases this with rfl | rfl
      · rw [hb_eq] at hM_gt
        simp at hM_gt
      · rw [hb_eq] at ha_lt
        simp at ha_lt
    by_cases hab : a ≤ b
    · use a, b, ha1, hab
      have hb_lt_M : b < M := by
        rw [hb_eq]
        have : 1 < a := ha1
        nlinarith
      exact ⟨hb_lt_M, hb_eq⟩
    · use b, a, hb1, (by omega)
      have ha_lt_M : a < M := by
        rw [hb_eq]
        have : 1 < b := hb1
        nlinarith
      have h_eq_comm : M = b * a := by
        rw [hb_eq, mul_comm]
      exact ⟨ha_lt_M, h_eq_comm⟩

  obtain ⟨a, b, ha1, hab, hb_lt, h_eq⟩ := h_comp
  have ha2 : a^2 ≤ M := by
    calc
      a^2 = a * a := sq a
      _ ≤ a * b := Nat.mul_le_mul_left a hab
      _ = M := h_eq.symm
  have ha_lt_n : a < n := by
    by_contra h_ge
    have : n ≤ a := by omega
    have : n^2 ≤ a^2 := Nat.pow_le_pow_left this 2
    omega
  obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd (by omega : a ≠ 1)
  have hp_le : p ≤ a := Nat.le_of_dvd (by omega) hp_dvd
  have hp_lt_n : p < n := by omega
  have h_nth : n < Nat.nth Nat.Prime (n - 1) := by
    have h_idx := nth_prime_ge_idx (n - 1)
    have : n - 1 + 2 = n + 1 := by omega
    omega
  have hp_lt_nth : p < Nat.nth Nat.Prime (n - 1) := by omega
  have hp_dvd_P : p ∣ prod_first_k_primes (n - 1) := prime_dvd_P_of_lt hp_prime hp_lt_nth
  have hp_dvd_M : p ∣ M := by
    rw [h_eq]
    exact dvd_mul_of_dvd_left hp_dvd b
  have hp_dvd_gcd : p ∣ Nat.gcd M (prod_first_k_primes (n - 1)) := Nat.dvd_gcd hp_dvd_M hp_dvd_P
  rw [h_coprime] at hp_dvd_gcd
  have : p ≤ 1 := Nat.le_of_dvd (by decide) hp_dvd_gcd
  have : 2 ≤ p := hp_prime.two_le
  omega


lemma exists_prime_between_n_and_n_sq (n : ℕ) (hn : 5 ≤ n) : ∃ q, Nat.Prime q ∧ n < q ∧ q < n^2 := by
  have hn0 : n ≠ 0 := by omega
  obtain ⟨q, hp, h_lt, h_le⟩ := exists_prime_lt_and_le_two_mul n hn0
  refine ⟨q, hp, h_lt, ?_⟩
  have : 2 * n < n^2 := by
    have : 2 < n := by omega
    nlinarith
  omega

theorem oeis_210186_conjecture :
  (∀ n : ℕ, Nat.Prime (A210186 n)) ∧ (∀ n : ℕ, 1 < n → A210186 n < n^2) := by
  constructor
  · intro n
    have h_gt : 1 < A210186 n := A210186_gt_one n
    obtain ⟨p, hp_prime, hp_dvd⟩ := Nat.exists_prime_and_dvd h_gt.ne'
    have hp_le : p ≤ A210186 n := Nat.le_of_dvd (by omega) hp_dvd
    rcases eq_or_lt_of_le hp_le with rfl | hp_lt
    · exact hp_prime
    · have hp_notin : p ∉ { m : ℕ | 1 < m ∧ ∀ i j : ℕ, (1 ≤ i ∧ i < j ∧ j ≤ n) → ¬ (m ∣ (prod_first_k_primes i + prod_first_k_primes j)) } := by
        intro h_mem
        have := A210186_le_of_mem n h_mem
        omega
      simp only [Set.mem_setOf_eq, not_and, not_forall, not_not, exists_prop] at hp_notin
      have hp_gt1 : 1 < p := Nat.Prime.one_lt hp_prime
      have hp_dvd_some := hp_notin hp_gt1
      rcases hp_dvd_some with ⟨i, j, hij, hp_dvd_sum⟩
      sorry
  · intro n hn
    rcases eq_or_ne n 2 with rfl | hn2
    · rw [A210186_two]
      decide
    · rcases eq_or_ne n 3 with rfl | hn3
      · rw [A210186_three]
        decide
      · rcases eq_or_ne n 4 with rfl | hn4
        · rw [A210186_four]
          decide
        · sorry
