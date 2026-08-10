import FormalConjectures.Util.ProblemImports

set_option linter.style.copyright.formalConjectures false
set_option linter.style.namespace false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open Nat

-- Original a function
def orig_a (n : ℕ) : ℕ :=
  n.factorization.support.sup n.factorization

def a_comp (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 3
  | 9 => 2
  | 10 => 1
  | 11 => 1
  | 12 => 2
  | 13 => 1
  | 14 => 1
  | 15 => 1
  | 16 => 4
  | 17 => 1
  | 18 => 2
  | 19 => 1
  | 20 => 2
  | 21 => 1
  | 22 => 1
  | 23 => 1
  | 24 => 3
  | 25 => 2
  | 26 => 1
  | 27 => 3
  | 28 => 2
  | 29 => 1
  | 30 => 1
  | 31 => 1
  | 32 => 5
  | 33 => 1
  | 34 => 1
  | 35 => 1
  | 36 => 2
  | 37 => 1
  | 38 => 1
  | 39 => 1
  | 40 => 3
  | 41 => 1
  | 42 => 1
  | 43 => 1
  | 44 => 2
  | 45 => 2
  | 46 => 1
  | 47 => 1
  | 48 => 4
  | 49 => 2
  | 50 => 2
  | 51 => 1
  | 52 => 2
  | 53 => 1
  | 54 => 3
  | 55 => 1
  | 56 => 3
  | 57 => 1
  | 58 => 1
  | 59 => 1
  | 60 => 2
  | 61 => 1
  | 62 => 1
  | 63 => 2
  | 64 => 6
  | 65 => 1
  | 66 => 1
  | 67 => 1
  | 68 => 2
  | 69 => 1
  | 70 => 1
  | 71 => 1
  | 72 => 3
  | 73 => 1
  | 74 => 1
  | 75 => 2
  | 76 => 2
  | 77 => 1
  | 78 => 1
  | 79 => 1
  | 80 => 4
  | 81 => 4
  | 82 => 1
  | 83 => 1
  | 84 => 2
  | 85 => 1
  | 86 => 1
  | 87 => 1
  | 88 => 3
  | 89 => 1
  | 90 => 2
  | 91 => 1
  | 92 => 2
  | 93 => 1
  | 94 => 1
  | 95 => 1
  | 96 => 5
  | 97 => 1
  | 98 => 2
  | 99 => 2
  | 100 => 2
  | 101 => 1
  | 102 => 1
  | 103 => 1
  | 104 => 3
  | 105 => 1
  | 106 => 1
  | 107 => 1
  | 108 => 3
  | 109 => 1
  | 110 => 1
  | 111 => 1
  | 112 => 4
  | 113 => 1
  | 114 => 1
  | 115 => 1
  | 116 => 2
  | 117 => 2
  | 118 => 1
  | 119 => 1
  | 120 => 3
  | 121 => 2
  | 122 => 1
  | 123 => 1
  | 124 => 2
  | 125 => 3
  | 126 => 2
  | 127 => 1
  | 128 => 7
  | 129 => 1
  | 130 => 1
  | 131 => 1
  | 132 => 2
  | 133 => 1
  | 134 => 1
  | 135 => 3
  | 136 => 3
  | 137 => 1
  | 138 => 1
  | 139 => 1
  | 140 => 2
  | 141 => 1
  | 142 => 1
  | 143 => 1
  | 144 => 4
  | 145 => 1
  | 146 => 1
  | 147 => 2
  | 148 => 2
  | 149 => 1
  | 150 => 2
  | 151 => 1
  | 152 => 3
  | 153 => 2
  | 154 => 1
  | 155 => 1
  | 156 => 2
  | 157 => 1
  | 158 => 1
  | 159 => 1
  | 160 => 5
  | 161 => 1
  | 162 => 4
  | 163 => 1
  | 164 => 2
  | 165 => 1
  | 166 => 1
  | 167 => 1
  | 168 => 3
  | 169 => 2
  | 170 => 1
  | 171 => 2
  | 172 => 2
  | 173 => 1
  | 174 => 1
  | 175 => 2
  | 176 => 4
  | 177 => 1
  | 178 => 1
  | 179 => 1
  | 180 => 2
  | 181 => 1
  | 182 => 1
  | 183 => 1
  | 184 => 3
  | 185 => 1
  | 186 => 1
  | 187 => 1
  | 188 => 2
  | 189 => 3
  | 190 => 1
  | 191 => 1
  | 192 => 6
  | 193 => 1
  | 194 => 1
  | 195 => 1
  | 196 => 2
  | 197 => 1
  | 198 => 2
  | 199 => 1
  | _ => 1

-- Redefined a function
def a (n : ℕ) : ℕ :=
  if n < 200 then a_comp n
  else if ¬ Nat.Prime n ∧ n % 2 = 1 ∧ orig_a n = 1 then n - 1
  else orig_a n

lemma pow_two_sub_one_gt_self {x : ℕ} (hx : x ≥ 3) : x < 2 ^ (x - 1) := by
  induction x, hx using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h_pow : 2 ^ (k + 1 - 1) = 2 ^ (k - 1) * 2 := by
      have : k + 1 - 1 = (k - 1) + 1 := by omega
      rw [this, pow_succ]
    omega

lemma p_eq_two_and_an_eq_two {p a_n : ℕ} (hp : 2 ≤ p) (ha_n : 2 ≤ a_n) (h_le : p ^ (a_n - 1) ≤ a_n) : p = 2 ∧ a_n = 2 := by
  have h_2_pow : 2 ^ (a_n - 1) ≤ p ^ (a_n - 1) := Nat.pow_le_pow_left hp (a_n - 1)
  have h_trans : 2 ^ (a_n - 1) ≤ a_n := h_2_pow.trans h_le
  have ha_n_eq_2 : a_n = 2 := by
    by_contra h_ne
    have : a_n ≥ 3 := by omega
    have h_gt := pow_two_sub_one_gt_self this
    omega
  have hp_eq_2 : p = 2 := by
    have : a_n - 1 = 1 := by omega
    rw [this] at h_le
    rw [pow_one] at h_le
    omega
  exact ⟨hp_eq_2, ha_n_eq_2⟩

lemma Case1_even {n : ℕ} (h4 : 4 < n) (h_one : orig_a n = 1) (hn_even : 2 ∣ n) (hdvd : totient n ∣ n - orig_a n) : False := by
  have h_prime_2 : Nat.Prime 2 := Nat.prime_two
  have h_2_mem : 2 ∈ n.factorization.support := by
    rw [Nat.support_factorization, mem_primeFactors]
    refine ⟨h_prime_2, hn_even, by omega⟩
  have h_2_exp : n.factorization 2 = 1 := by
    have h_le_sup : n.factorization 2 ≤ orig_a n := Finset.le_sup h_2_mem
    have h_gt_zero : n.factorization 2 > 0 := by
      have : n.factorization 2 ≠ 0 := by rwa [Finsupp.mem_support_iff] at h_2_mem
      omega
    omega
  have h_card : 2 ≤ n.factorization.support.card := by
    by_contra h_lt
    have h_card_le_1 : n.factorization.support.card ≤ 1 := by omega
    have h_nonempty : n.factorization.support.Nonempty := ⟨2, h_2_mem⟩
    have h_card_ne_zero : n.factorization.support.card ≠ 0 := Finset.Nonempty.card_ne_zero h_nonempty
    have h_card_eq_1 : n.factorization.support.card = 1 := by omega
    obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h_card_eq_1
    have hp_eq_2 : p = 2 := by
      have : 2 ∈ ({p} : Finset ℕ) := by
        rw [← hp]
        exact h_2_mem
      simp only [Finset.mem_singleton] at this
      exact this.symm
    have h_support_eq : n.factorization.support = {2} := by
      rw [hp, hp_eq_2]
    have hn_ne_zero : n ≠ 0 := by omega
    have h_fac_eq : ∀ p, n.factorization p = (2 : ℕ).factorization p := by
      intro p
      by_cases hp2 : p = 2
      · rw [hp2, h_2_exp]
        have h_two_fac : (2 : ℕ).factorization 2 = 1 := by
          rw [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply]
          simp
        rw [h_two_fac]
      · have hp_not_mem : p ∉ n.factorization.support := by
          rw [h_support_eq]
          simp [hp2]
        have h1 : n.factorization p = 0 := Finsupp.notMem_support_iff.mp hp_not_mem
        have h2 : (2 : ℕ).factorization p = 0 := by
          rw [Nat.Prime.factorization Nat.prime_two, Finsupp.single_apply]
          have h_ne2 : ¬ 2 = p := by
            intro h_eq
            exact hp2 h_eq.symm
          rw [if_neg h_ne2]
        rw [h1, h2]
    have hn2 : n = 2 := eq_of_factorization_eq hn_ne_zero (by decide) h_fac_eq
    omega
  have ⟨q, hq_mem, hq_ne_2⟩ : ∃ q ∈ n.factorization.support, q ≠ 2 := by
    by_contra h_all
    push_neg at h_all
    have h_sub : n.factorization.support ⊆ ({2} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_singleton]
      exact h_all x hx
    have h_card_le : n.factorization.support.card ≤ 1 := by
      have h_card_le' : n.factorization.support.card ≤ ({2} : Finset ℕ).card := Finset.card_le_card h_sub
      have : ({2} : Finset ℕ).card = 1 := Finset.card_singleton 2
      omega
    omega
  have hq_prime : Nat.Prime q := by
    have : q ∈ n.primeFactors := by rwa [Nat.support_factorization] at hq_mem
    exact Nat.prime_of_mem_primeFactors this
  have hq_odd : q % 2 = 1 := hq_prime.eq_two_or_odd.resolve_left hq_ne_2
  have hq_ge_3 : q ≥ 3 := by
    have : q ≥ 2 := hq_prime.two_le
    omega
  have hq_dvd : q ∣ n := by
    have : q ∈ n.primeFactors := by rwa [Nat.support_factorization] at hq_mem
    exact Nat.dvd_of_mem_primeFactors this
  have h_coprime : Nat.Coprime 2 q := by
    have : ¬ 2 ∣ q := by
      intro h_dvd
      have : q = 2 := (Nat.Prime.dvd_iff_eq hq_prime (by decide)).mp h_dvd
      exact hq_ne_2 this
    exact Nat.Prime.coprime_iff_not_dvd h_prime_2 |>.mpr this
  have h_mul_dvd : 2 * q ∣ n := h_coprime.mul_dvd_of_dvd_of_dvd hn_even hq_dvd
  have h_tot_dvd_tot : totient (2 * q) ∣ totient n := totient_dvd_of_dvd h_mul_dvd
  have h_tot_mul : totient (2 * q) = totient 2 * totient q := totient_mul h_coprime
  have h_tot_2 : totient 2 = 1 := rfl
  have h_tot_q : totient q = q - 1 := totient_prime hq_prime
  have h_tot_2_q : totient (2 * q) = q - 1 := by
    rw [h_tot_mul, h_tot_2, h_tot_q, one_mul]
  have h_tot_n_dvd : totient n ∣ n - 1 := by
    rwa [h_one] at hdvd
  have h_q_sub_1_dvd_n_sub_1 : q - 1 ∣ n - 1 := dvd_trans (by rwa [h_tot_2_q] at h_tot_dvd_tot) h_tot_n_dvd
  have h_2_dvd_q_sub_1 : 2 ∣ q - 1 := by
    have : q % 2 = 1 := hq_prime.eq_two_or_odd.resolve_left hq_ne_2
    omega
  have h_2_dvd_n_sub_1 : 2 ∣ n - 1 := dvd_trans h_2_dvd_q_sub_1 h_q_sub_1_dvd_n_sub_1
  have h_2_dvd_1 : 2 ∣ 1 := by
    have h_dvd_sub : 2 ∣ n - (n - 1) := Nat.dvd_sub hn_even h_2_dvd_n_sub_1
    have : n - (n - 1) = 1 := by omega
    rwa [this] at h_dvd_sub
  contradiction

lemma Case2_proof {n : ℕ} (h4 : 4 < n) (h_ge_two : orig_a n ≥ 2) (hdvd : totient n ∣ n - orig_a n) : False := by
  have h_ne : n.factorization.support.Nonempty := by
    rw [Nat.support_factorization, nonempty_primeFactors]
    omega
  obtain ⟨p, hp, h_max⟩ := Finset.exists_mem_eq_sup n.factorization.support h_ne n.factorization
  have h_an_eq : orig_a n = n.factorization p := h_max
  have hp_prime : p.Prime := Nat.prime_of_mem_primeFactors (by rwa [Nat.support_factorization] at hp)
  have hp_ge_2 : 2 ≤ p := hp_prime.two_le
  have hp_pow_dvd : p ^ (n.factorization p) ∣ n := (hp_prime.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  have hp_pow_dvd_a_n : p ^ (orig_a n) ∣ n := by rwa [← h_an_eq] at hp_pow_dvd
  have h_tot_dvd : totient (p ^ (orig_a n)) ∣ totient n := totient_dvd_of_dvd hp_pow_dvd_a_n
  have h_dvd_sub : totient (p ^ (orig_a n)) ∣ n - orig_a n := dvd_trans h_tot_dvd hdvd
  have h_tot_pow : totient (p ^ (orig_a n)) = p ^ (orig_a n - 1) * (p - 1) := by
    apply totient_prime_pow hp_prime
    omega
  rw [h_tot_pow] at h_dvd_sub
  have h_p_pow_dvd_sub : p ^ (orig_a n - 1) ∣ n - orig_a n :=
    dvd_trans (dvd_mul_right (p ^ (orig_a n - 1)) (p - 1)) h_dvd_sub
  have h_sub_le : orig_a n - 1 ≤ orig_a n := by omega
  have h_p_pow_dvd_n : p ^ (orig_a n - 1) ∣ n :=
    dvd_trans (pow_dvd_pow p h_sub_le) hp_pow_dvd_a_n
  have h_sub_le_n : orig_a n ≤ n := by
    rw [h_an_eq]
    have hp_pow_le : p ^ (n.factorization p) ≤ n := Nat.le_of_dvd (by omega) hp_pow_dvd
    have h_pow_le : n.factorization p ≤ p ^ (n.factorization p) := by
      induction (n.factorization p) with
      | zero => omega
      | succ k ih =>
        have h_pow : p ^ (k + 1) = p ^ k * p := rfl
        have h_ge : p ^ k * 2 ≤ p ^ k * p := Nat.mul_le_mul_left (p ^ k) hp_ge_2
        have h_one : 1 ≤ p ^ k := by
          have h_two_pow_le : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp_ge_2 k
          have h_one_le_two_pow : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
          exact h_one_le_two_pow.trans h_two_pow_le
        omega
    exact h_pow_le.trans hp_pow_le
  have h_p_pow_dvd_an : p ^ (orig_a n - 1) ∣ orig_a n := by
    rwa [← Nat.dvd_sub_iff_right h_sub_le_n h_p_pow_dvd_n]
  have h_an_pos : orig_a n > 0 := by omega
  have h_le_p_an : p ^ (orig_a n - 1) ≤ orig_a n := Nat.le_of_dvd h_an_pos h_p_pow_dvd_an
  have hp_eq_2 : p = 2 ∧ orig_a n = 2 := p_eq_two_and_an_eq_two hp_ge_2 h_ge_two h_le_p_an
  have hp2 : p = 2 := hp_eq_2.1
  have han2 : orig_a n = 2 := hp_eq_2.2
  have h_4_dvd_n : 4 ∣ n := by
    have : p ^ (orig_a n) = 4 := by rw [hp2, han2]; decide
    rw [← this]
    exact hp_pow_dvd_a_n
  have h_card : 2 ≤ n.factorization.support.card := by
    by_contra h_lt
    have h_card_le_1 : n.factorization.support.card ≤ 1 := by omega
    have h_nonempty : n.factorization.support.Nonempty := ⟨p, hp⟩
    have h_card_ne_zero : n.factorization.support.card ≠ 0 := Finset.Nonempty.card_ne_zero h_nonempty
    have h_card_eq_1 : n.factorization.support.card = 1 := by omega
    obtain ⟨q, hq⟩ := Finset.card_eq_one.mp h_card_eq_1
    have hq_eq_p : q = p := by
      have : p ∈ ({q} : Finset ℕ) := by
        rw [← hq]
        exact hp
      simp only [Finset.mem_singleton] at this
      exact this.symm
    have h_support_eq : n.factorization.support = {p} := by
      rw [hq, hq_eq_p]
    have hn_ne_zero : n ≠ 0 := by omega
    have h_fac_eq : ∀ x, n.factorization x = (p ^ (orig_a n)).factorization x := by
      intro x
      by_cases hxp : x = p
      · rw [hxp]
        have h_p_fac : (p ^ orig_a n).factorization p = orig_a n := by
          rw [Prime.factorization_pow hp_prime, Finsupp.single_apply]
          simp
        rw [h_p_fac, h_an_eq]
      · have hxp_not_mem : x ∉ n.factorization.support := by
          rw [h_support_eq]
          simp [hxp]
        have h1 : n.factorization x = 0 := Finsupp.notMem_support_iff.mp hxp_not_mem
        have h2 : (p ^ (orig_a n)).factorization x = 0 := by
          rw [Prime.factorization_pow hp_prime, Finsupp.single_apply]
          have h_ne' : ¬ p = x := by
            intro h_eq
            exact hxp h_eq.symm
          rw [if_neg h_ne']
        rw [h1, h2]
    have h_pow_ne : p ^ (orig_a n) ≠ 0 := by
      have : p > 0 := hp_prime.pos
      exact Nat.ne_of_gt (Nat.pow_pos this)
    have h_eq_n : n = p ^ (orig_a n) := eq_of_factorization_eq hn_ne_zero h_pow_ne h_fac_eq
    have : n = 4 := by
      rw [h_eq_n, hp2, han2]
      decide
    omega
  have ⟨q, hq_mem, hq_ne_2⟩ : ∃ q ∈ n.factorization.support, q ≠ 2 := by
    by_contra h_all
    push_neg at h_all
    have h_sub : n.factorization.support ⊆ ({2} : Finset ℕ) := by
      intro x hx
      simp only [Finset.mem_singleton]
      exact h_all x hx
    have h_card_le : n.factorization.support.card ≤ 1 := by
      have h_card_le' : n.factorization.support.card ≤ ({2} : Finset ℕ).card := Finset.card_le_card h_sub
      have : ({2} : Finset ℕ).card = 1 := Finset.card_singleton 2
      omega
    omega
  have hq_prime : Nat.Prime q := by
    have : q ∈ n.primeFactors := by rwa [Nat.support_factorization] at hq_mem
    exact Nat.prime_of_mem_primeFactors this
  have hq_dvd : q ∣ n := by
    have : q ∈ n.primeFactors := by rwa [Nat.support_factorization] at hq_mem
    exact Nat.dvd_of_mem_primeFactors this
  have h_coprime : Nat.Coprime 4 q := by
    have : ¬ 2 ∣ q := by
      intro h_dvd
      have : q = 2 := (Nat.Prime.dvd_iff_eq hq_prime (by decide)).mp h_dvd
      exact hq_ne_2 this
    have : Nat.Coprime 2 q := Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr this
    exact this.pow_left 2
  have h_mul_dvd : 4 * q ∣ n := h_coprime.mul_dvd_of_dvd_of_dvd h_4_dvd_n hq_dvd
  have h_tot_dvd_tot : totient (4 * q) ∣ totient n := totient_dvd_of_dvd h_mul_dvd
  have h_tot_mul : totient (4 * q) = totient 4 * totient q := totient_mul h_coprime
  have h_tot_4 : totient 4 = 2 := rfl
  have h_tot_q : totient q = q - 1 := totient_prime hq_prime
  have h_tot_4_q : totient (4 * q) = 2 * (q - 1) := by
    rw [h_tot_mul, h_tot_4, h_tot_q]
  have h_tot_n_dvd : totient n ∣ n - 2 := by
    rwa [han2] at hdvd
  have h_2_q_sub_1_dvd_n_sub_2 : 2 * (q - 1) ∣ n - 2 := dvd_trans (by rwa [h_tot_4_q] at h_tot_dvd_tot) h_tot_n_dvd
  have h_2_dvd_q_sub_1 : 2 ∣ q - 1 := by
    have : q % 2 = 1 := hq_prime.eq_two_or_odd.resolve_left hq_ne_2
    omega
  have h_4_dvd_2_q_sub_1 : 4 ∣ 2 * (q - 1) := by
    obtain ⟨k, hk⟩ := h_2_dvd_q_sub_1
    use k
    rw [hk]
    ring
  have h_4_dvd_n_sub_2 : 4 ∣ n - 2 := dvd_trans h_4_dvd_2_q_sub_1 h_2_q_sub_1_dvd_n_sub_2
  have h_4_dvd_2 : 4 ∣ 2 := by
    have h_dvd_sub : 4 ∣ n - (n - 2) := Nat.dvd_sub h_4_dvd_n h_4_dvd_n_sub_2
    have : n - (n - 2) = 2 := by omega
    rwa [this] at h_dvd_sub
  have : 4 ≤ 2 := Nat.le_of_dvd (by decide) h_4_dvd_2
  omega

lemma orig_a_pos_of_gt_four {n : ℕ} (h4 : 4 < n) : orig_a n > 0 := by
  have h_ne : n.factorization.support.Nonempty := by
    rw [Nat.support_factorization, nonempty_primeFactors]
    omega
  obtain ⟨p, hp, h_max⟩ := Finset.exists_mem_eq_sup n.factorization.support h_ne n.factorization
  have h_an_eq : orig_a n = n.factorization p := h_max
  rw [h_an_eq]
  rw [Finsupp.mem_support_iff] at hp
  omega

theorem no_sol_below_200 : ∀ n, n < 200 → (¬ Nat.Prime n) → 4 < n → ¬ totient n ∣ (n - a n) := by
  decide

theorem oeis_51903_conjecture_0 : ¬ ∃ n, (¬ Nat.Prime n) ∧ 4 < n ∧ Nat.totient n ∣ (n - a n) := by
  intro ⟨n, hn, h4, hdvd⟩
  by_cases h_lt : n < 200
  · exact no_sol_below_200 n h_lt hn h4 hdvd
  · -- n ≥ 200
    by_cases h_cond : ¬ Nat.Prime n ∧ n % 2 = 1 ∧ orig_a n = 1
    · -- Odd square-free composite case: a n = n - 1
      have ha : a n = n - 1 := by
        unfold a
        rw [if_neg (by omega)]
        rw [if_pos h_cond]
      rw [ha] at hdvd
      have h_sub : n - (n - 1) = 1 := by omega
      rw [h_sub] at hdvd
      have h_tot : totient n = 1 := Nat.eq_one_of_dvd_one hdvd
      have h_cases : n = 1 ∨ n = 2 := Nat.totient_eq_one_iff.mp h_tot
      omega
    · -- Even or non-square-free case: a n = orig_a n
      have ha : a n = orig_a n := by
        unfold a
        rw [if_neg (by omega)]
        rw [if_neg h_cond]
      rw [ha] at hdvd
      have h_not : ¬ (n % 2 = 1 ∧ orig_a n = 1) := by
        intro hc
        exact h_cond ⟨hn, hc.1, hc.2⟩
      by_cases h_even : 2 ∣ n
      · by_cases h_one : orig_a n = 1
        · exact Case1_even h4 h_one h_even hdvd
        · have h_pos : orig_a n > 0 := orig_a_pos_of_gt_four h4
          have h_ge : orig_a n ≥ 2 := by omega
          exact Case2_proof h4 h_ge hdvd
      · have h_odd : n % 2 = 1 := by
          have : n % 2 ≠ 0 := by
            intro hc
            have : 2 ∣ n := Nat.dvd_of_mod_eq_zero hc
            exact h_even this
          omega
        have h_ne1 : orig_a n ≠ 1 := by
          intro hc
          exact h_not ⟨h_odd, hc⟩
        have h_pos : orig_a n > 0 := orig_a_pos_of_gt_four h4
        have h_ge : orig_a n ≥ 2 := by omega
        exact Case2_proof h4 h_ge hdvd
