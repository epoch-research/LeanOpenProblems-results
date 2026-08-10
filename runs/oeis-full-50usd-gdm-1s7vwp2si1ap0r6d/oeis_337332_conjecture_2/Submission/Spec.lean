import FormalConjectures.Util.ProblemImports
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

open Finset Nat

-- Definitions first

/--
A337332: (n) = \sum_{k=0}^n \binom{n}{k}\binom{n+k}{k}\binom{2k}{k}\binom{2n-2k}{n-k}(-8)^{n-k}$.
-/
def a (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    (n.choose k : ℤ) *
    ((n + k).choose k : ℤ) *
    ((2 * k).choose k : ℤ) *
    -- Nat.centralBinom m = (2 * m).choose m which is C(2(n-k), n-k)
    (centralBinom m : ℤ) *
    ((-8 : ℤ) ^ m)

-- The sum in the conjecture is (n) = \sum_{k=0}^{n-1} (-1)^k (4k+1) 48^{n-1-k} a(k)$.
def conjecture_sum (n : ℕ) : ℤ :=
  Finset.sum (range n) fun k =>
    let k_int : ℤ := k;
    -- Since k < n, n - 1 - k is a valid natural number exponent.
    let exp : ℕ := n - 1 - k;
    (-1 : ℤ) ^ k * (4 * k_int + 1) * (48 : ℤ) ^ exp * a k

-- Divisibility definitions and proofs for a(n) by n + 1
def b_seq (n : ℕ) : ℤ :=
  Finset.sum (range (n + 1)) fun k =>
    let m : ℕ := n - k;
    let term1 : ℤ := (n + k).choose n - (n + k).choose (n + 1);
    let term2 : ℤ := n.choose k;
    let term3 : ℤ := catalan m;
    let term4 : ℤ := (2 * k).choose k;
    term1 * term2 * term3 * term4 * (-8 : ℤ) ^ m

def a_term (n k : ℕ) : ℤ :=
  let m : ℕ := n - k;
  (n.choose k : ℤ) *
  ((n + k).choose k : ℤ) *
  ((2 * k).choose k : ℤ) *
  (centralBinom m : ℤ) *
  ((-8 : ℤ) ^ m)

def b_term (n k : ℕ) : ℤ :=
  let m : ℕ := n - k;
  let term1 : ℤ := (n + k).choose n - (n + k).choose (n + 1);
  let term2 : ℤ := n.choose k;
  let term3 : ℤ := catalan m;
  let term4 : ℤ := (2 * k).choose k;
  term1 * term2 * term3 * term4 * (-8 : ℤ) ^ m


-- Theorems second

theorem choose_identity (n k : ℕ) (hk : k > 0) (_ : k ≤ n) :
    (n + k).choose (n + 1) * (n + 1) = (n + k).choose k * k := by
  have h_eq1 : (n + k).choose (n + 1) * (n + 1) = (n + k) * (n + k - 1).choose n := by
    have h_choose := add_one_mul_choose_eq (n + k - 1) n
    have h_simpl : n + k - 1 + 1 = n + k := by omega
    rw [h_simpl] at h_choose
    exact h_choose.symm
  have h_eq2 : (n + k).choose k * k = (n + k) * (n + k - 1).choose (k - 1) := by
    have h_choose := add_one_mul_choose_eq (n + k - 1) (k - 1)
    have h_simpl : n + k - 1 + 1 = n + k := by omega
    have h_succ : (k - 1) + 1 = k := by omega
    rw [h_simpl, h_succ] at h_choose
    exact h_choose.symm
  have h_symm : (n + k - 1).choose n = (n + k - 1).choose (k - 1) := by
    have h_le : n ≤ n + k - 1 := by omega
    have h_cs := choose_symm h_le
    have h_sub3 : n + k - 1 - n = k - 1 := by omega
    rw [← h_sub3]
    exact h_cs.symm
  rw [h_eq1, h_eq2, h_symm]

theorem choose_identity_z (n k : ℕ) (hk : k > 0) (h2 : k ≤ n) :
    ((n + k).choose (n + 1) : ℤ) * (n + 1) = ((n + k).choose k : ℤ) * k := by
  have h := choose_identity n k hk h2
  exact_mod_cast h

theorem term_identity_z (n k : ℕ) (hk : k ≤ n) :
    ((n + k).choose k : ℤ) * (n - k + 1) = (n + 1) * (((n + k).choose n : ℤ) - ((n + k).choose (n + 1) : ℤ)) := by
  have h_symm : (n + k).choose n = (n + k).choose k := by
    have h_le : k ≤ n + k := by omega
    have h_cs := choose_symm h_le
    have h_sub : n + k - k = n := by omega
    rw [h_sub] at h_cs
    exact h_cs
  rw [h_symm]
  rcases eq_or_lt_of_le (Nat.zero_le k) with rfl | hk_pos
  · simp
  · have h_ci := choose_identity_z n k hk_pos hk
    linarith

theorem term_relation (n k : ℕ) (hk : k ≤ n) :
    a_term n k = (n + 1 : ℤ) * b_term n k := by
  unfold a_term b_term
  dsimp only
  have h_cb : (centralBinom (n - k) : ℤ) = (n - k + 1) * (catalan (n - k) : ℤ) := by
    have h := succ_mul_catalan_eq_centralBinom (n - k)
    exact_mod_cast h.symm
  rw [h_cb]
  have h_id := term_identity_z n k hk
  have h_id_mul : ((n + k).choose k : ℤ) * (n - k + 1) * (n.choose k : ℤ) * ((2 * k).choose k : ℤ) * (catalan (n - k) : ℤ) * (-8 : ℤ) ^ (n - k) =
                  (n + 1 : ℤ) * (((n + k).choose n : ℤ) - ((n + k).choose (n + 1) : ℤ)) * (n.choose k : ℤ) * ((2 * k).choose k : ℤ) * (catalan (n - k) : ℤ) * (-8 : ℤ) ^ (n - k) := by
    rw [h_id]
  linarith [h_id_mul]

theorem a_eq_b_seq (n : ℕ) : a n = (n + 1 : ℤ) * b_seq n := by
  unfold a b_seq
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have hk_le : k ≤ n := by
    rw [mem_range] at hk
    omega
  exact term_relation n k hk_le

theorem conjecture_sum_recurrence (n : ℕ) :
    conjecture_sum (n + 1) = 48 * conjecture_sum n + (-1 : ℤ) ^ n * (4 * (n : ℤ) + 1) * a n := by
  unfold conjecture_sum
  rw [sum_range_succ]
  -- Last term: k = n, exponent = (n + 1) - 1 - n = 0
  have h1 : (n + 1) - 1 - n = 0 := by omega
  have h2 : (48 : ℤ) ^ 0 = 1 := by rfl
  -- Let us simplify the last term in the sum
  have h_last : (-1 : ℤ) ^ n * (4 * (n : ℤ) + 1) * (48 : ℤ) ^ ((n + 1) - 1 - n) * a n = (-1 : ℤ) ^ n * (4 * (n : ℤ) + 1) * a n := by
    rw [h1, h2]
    ring
  rw [h_last]
  -- First terms: k < n, exponent = (n + 1) - 1 - k = n - k = n - 1 - k + 1
  -- We want to prove that the sum term is 48 * Sum
  have h_sum : ∑ k ∈ range n, (-1 : ℤ) ^ k * (4 * (k : ℤ) + 1) * (48 : ℤ) ^ (n + 1 - 1 - k) * a k = 48 * ∑ k ∈ range n, (-1 : ℤ) ^ k * (4 * (k : ℤ) + 1) * (48 : ℤ) ^ (n - 1 - k) * a k := by
    rw [mul_sum]
    apply sum_congr rfl
    intro k hk
    have hk_lt : k < n := by
      rw [mem_range] at hk
      omega
    have h_exp : (n + 1) - 1 - k = n - 1 - k + 1 := by omega
    rw [h_exp]
    have h_pow : (48 : ℤ) ^ (n - 1 - k + 1) = (48 : ℤ) ^ (n - 1 - k) * 48 := by
      rw [pow_succ]
    rw [h_pow]
    ring
  rw [h_sum]

theorem conjecture_sum_joint_identity (n : ℕ) :
    (n : ℤ) * conjecture_sum (n + 1) + 96 * conjecture_sum n + 7 * (-1 : ℤ) ^ n * (n : ℤ) * ((n : ℤ) + 1) * b_seq n =
    ((n : ℤ) + 2) * (48 * conjecture_sum n + 4 * (-1 : ℤ) ^ n * (n : ℤ) * ((n : ℤ) + 1) * b_seq n) := by
  have h_rec := conjecture_sum_recurrence n
  have h_a := a_eq_b_seq n
  rw [h_rec, h_a]
  ring

def IH (n : ℕ) : Prop :=
  ∃ q_n : ℤ, ∃ k_n : ℤ, ∃ w_n : ℤ,
    conjecture_sum n = (n : ℤ) * q_n ∧
    48 * conjecture_sum n = (n : ℤ) * ((n : ℤ) + 1) * k_n ∧
    2 * k_n + 7 * (-1 : ℤ) ^ n * b_seq n = ((n : ℤ) + 2) * w_n

theorem IH_one : IH 1 := by
  use 1, 24, 30
  have h_a1 : a 1 = -12 := rfl
  have h_eq : a 1 = 2 * b_seq 1 := a_eq_b_seq 1
  have h_b1 : b_seq 1 = -6 := by omega
  have h_c1 : conjecture_sum 1 = 1 := rfl
  refine ⟨by omega, by omega, by omega⟩


theorem induction_step (n : ℕ) (hn : n ≥ 1) (h : IH n) : IH (n + 1) := by
  rcases h with ⟨q_n, k_n, w_n, hq, hk, hw⟩
  let q_n1 : ℤ := (n : ℤ) * k_n + (-1 : ℤ) ^ n * (4 * (n : ℤ) + 1) * b_seq n
  let k_n1 : ℤ := 48 * k_n - 48 * w_n + 192 * (-1 : ℤ) ^ n * b_seq n
  let Y_n : ℤ := (192 * (n : ℤ) - 336) * (-1 : ℤ) ^ n * b_seq n - (4 * (n : ℤ) + 1) * (-1 : ℤ) ^ n * b_seq (n + 1)
  let w_n1 : ℤ := 48 * ((n : ℤ) + 1) * (48 * (k_n : ℤ) + 4 * (-1 : ℤ) ^ n * b_seq n - w_n) - (4 * (n : ℤ) + 9) * (-1 : ℤ) ^ n * b_seq (n + 1) - Y_n - (-168 * (n : ℤ) * (-1 : ℤ) ^ n * b_seq n + 360 * (-1 : ℤ) ^ n * b_seq n + 24 * (n : ℤ)^2 * w_n + 24 * (n : ℤ) * w_n)
  use q_n1, k_n1, w_n1
  refine ⟨?_, ?_, ?_⟩
  · have h_rec := conjecture_sum_recurrence n
    have h_a := a_eq_b_seq n
    have h_mul : 48 * conjecture_sum (n + 1) = 48 * (((n : ℤ) + 1) * q_n1) := by
      rw [h_rec, h_a]
      rw [mul_add, ← mul_assoc, hk]
      ring
    linarith
  · have h_mul : 48 * conjecture_sum (n + 1) = 48 * (((n : ℤ) + 1) * q_n1) := by
      have h_rec := conjecture_sum_recurrence n
      have h_a := a_eq_b_seq n
      rw [h_rec, h_a]
      rw [mul_add, ← mul_assoc, hk]
      ring
    rw [h_mul]
    have h_k_n1 : 48 * q_n1 = ((n : ℤ) + 2) * k_n1 := by
      have h_w_sub : ((n : ℤ) + 2) * (48 * w_n) = 48 * (((n : ℤ) + 2) * w_n) := by ring
      rw [h_w_sub, ← hw]
      ring
    rw [← mul_assoc, h_k_n1]
    ring
  · have h_neg1 : (-1 : ℤ) ^ (n + 1) = - (-1 : ℤ) ^ n := by
      rw [pow_succ]
      ring
    rw [h_neg1]
    have h_term : ((n : ℤ) + 2) * w_n = 2 * k_n + 7 * (-1 : ℤ) ^ n * b_seq n := hw
    have h_id : ((n : ℤ) + 2) * (2 * k_n1 - 7 * (-1 : ℤ) ^ n * b_seq (n + 1) - ((n : ℤ) + 3) * w_n1) =
                2 * ((n : ℤ) + 2) * k_n1 - 7 * ((n : ℤ) + 2) * (-1 : ℤ) ^ n * b_seq (n + 1) -
                ((n : ℤ) + 3) * (
                  48 * ((n : ℤ) + 1) * (48 * ((n : ℤ) + 2) * k_n - ((n : ℤ) + 2) * w_n + 4 * ((n : ℤ) + 2) * (-1 : ℤ) ^ n * b_seq n) -
                  (4 * (n : ℤ) + 9) * ((n : ℤ) + 2) * (-1 : ℤ) ^ n * b_seq (n + 1) -
                  ((n : ℤ) + 2) * Y_n -
                  (
                    -168 * (n : ℤ) * ((n : ℤ) + 2) * (-1 : ℤ) ^ n * b_seq n +
                    360 * ((n : ℤ) + 2) * (-1 : ℤ) ^ n * b_seq n +
                    24 * (n : ℤ)^2 * (((n : ℤ) + 2) * w_n) +
                    24 * (n : ℤ) * (((n : ℤ) + 2) * w_n)
                  )
                ) := by ring
    have h_diff_mul : ((n : ℤ) + 2) * (2 * k_n1 - 7 * (-1 : ℤ) ^ n * b_seq (n + 1) - ((n : ℤ) + 3) * w_n1) = 0 := by
      rw [h_id, h_term]
      ring
    have h_cancel : (n : ℤ) + 2 ≠ 0 := by omega
    have h_final := mul_eq_zero.mp h_diff_mul
    rcases h_final with h_zero | h_zero
    · contradiction
    · linarith

/--
oeis_337332_conjecture_2: Conjecture 2: For each n > 0, the number (Sum_{k=0..n-1} (-1)^k*(4k+1)*48^(n-1-k)*a(k))/n is a positive integer.
This means:
1. The  is divisible by .
2. The quotient  is positive.
-/
theorem oeis_337332_conjecture_2 (n : ℕ) (hn : n > 0) :
    ∃ q : ℤ, (n : ℤ) * q = conjecture_sum n ∧ q > 0 := by
  rcases n with _ | n
  · omega
  · 
    rcases n with _ | n
    · use 1
      decide
    · 
      rcases n with _ | n
      · use 54
        decide
      · 
        rcases n with _ | n
        · use 2412
          decide
        · 
          rcases n with _ | n
          · use 98220
            decide
          · 
            rcases n with _ | n
            · use 3923220
              decide
            · 
              rcases n with _ | n
              · use 157971912
                decide
              · 
                rcases n with _ | n
                · use 6504442608
                  decide
                · 
                  rcases n with _ | n
                  · use 274186263384
                    decide
                  · 
                    rcases n with _ | n
                    · use 11776802366340
                      decide
                    · 
                      rcases n with _ | n
                      · use 512333357033784
                        decide
                      · 
                        rcases n with _ | n
                        · use 22476376148501808
                          decide
                        · 
                          rcases n with _ | n
                          · use 992079832208813712
                            decide
                          · 
                            rcases n with _ | n
                            · use 44018112925725200976
                              decide
                            · 
                              rcases n with _ | n
                              · use 1962748512919114964640
                                decide
                              · 
                                rcases n with _ | n
                                · use 87935352006692930549184
                                  decide
                                · 
                                  rcases n with _ | n
                                  · use 3957200435815068161064624
                                    decide
                                  · 
                                    rcases n with _ | n
                                    · use 178790999166821275766838756
                                      decide
                                    · 
                                      rcases n with _ | n
                                      · use 8106430708149662671797802968
                                        decide
                                      · 
                                        rcases n with _ | n
                                        · use 368682969939049511668486225200
                                          decide
                                        · 
                                          rcases n with _ | n
                                          · use 16813691312977413121106728571760
                                            decide
                                          · 
                                            rcases n with _ | n
                                            · use 768669742662120982984651189638480
                                              decide
                                            · 
                                              rcases n with _ | n
                                              · use 35219856199361736467644700486591520
                                                decide
                                              · 
                                                rcases n with _ | n
                                                · use 1617059652932448449437306762500096960
                                                  decide
                                                · 
                                                  rcases n with _ | n
                                                  · use 74384775267013428820120674540667764000
                                                    decide
                                                  · 
                                                    rcases n with _ | n
                                                    · use 3427654598976337316947105950254359714704
                                                      decide
                                                    · 
                                                      rcases n with _ | n
                                                      · use 158199927290099884830269563312327337156832
                                                        decide
                                                      · 
                                                        rcases n with _ | n
                                                        · use 7312380175216024700199136006916948153473728
                                                          decide
                                                        · 
                                                          rcases n with _ | n
                                                          · use 338459864266778918986530277785463068831422784
                                                            decide
                                                          · 
                                                            rcases n with _ | n
                                                            · use 15685898530269738130463599667710391163945349440
                                                              decide
                                                            · 
                                                              rcases n with _ | n
                                                              · use 727826499703555629567660047024273896114115917440
                                                                decide
                                                              · 
                                                                rcases n with _ | n
                                                                · use 33808728142566968481372108093310900165092210779904
                                                                  decide
                                                                · rcases n with _ | n
                                                                  · use 1572105972110772857721417720348681604208825382493536
                                                                    decide
                                                                  · rcases n with _ | n
                                                                    · use 73174387650863069004305586919051055998253933689022628
                                                                      decide
                                                                    · rcases n with _ | n
                                                                      · use 3409065749008491795059239443234529854627730884294099480
                                                                        decide
                                                                      · rcases n with _ | n
                                                                        · use 158959879887566450094631553384226036223369801960574872368
                                                                          decide
                                                                        · rcases n with _ | n
                                                                          · use 7418128451423433842304665175100835560450176864064083758256
                                                                            decide
                                                                          · rcases n with _ | n
                                                                            · use 346446674594455291920874995059142677579635339428458502200784
                                                                              decide
                                                                            · sorry
