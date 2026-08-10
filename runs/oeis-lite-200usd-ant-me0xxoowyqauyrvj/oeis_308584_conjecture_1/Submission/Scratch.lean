import FormalConjectures.Util.ProblemImports

open Nat Finset

-- Bridge identity: 4*(T a + T b) + 1 = (a+b+1)^2 + (b-a)^2 for a ≤ b
example (a b : ℕ) (h : a ≤ b) :
    4 * (a*(a+1)/2 + b*(b+1)/2) + 1 = (a+b+1)^2 + (b-a)^2 := by
  have ha : a*(a+1)/2 * 2 = a*(a+1) := Nat.div_mul_cancel (even_mul_succ_self a).two_dvd
  have hb : b*(b+1)/2 * 2 = b*(b+1) := Nat.div_mul_cancel (even_mul_succ_self b).two_dvd
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h  -- b = a + d
  have hba : (a + d) - a = d := by omega
  rw [hba]
  nlinarith [ha, hb]

-- Not a sum of two squares, via a prime q ≡ 3 mod 4 to an odd power.
theorem not_ss_gen (K q e : ℕ) (hq : q.Prime) (h3 : q % 4 = 3)
    (hde : q^e ∣ K) (hde2 : ¬ q^(e+1) ∣ K) (hodd : Odd e) (hK : K ≠ 0) :
    ¬ ∃ x y, K = x^2 + y^2 := by
  haveI : Fact q.Prime := ⟨hq⟩
  have he : e ≠ 0 := by rintro rfl; simp at hodd
  rw [Nat.eq_sq_add_sq_iff]
  push_neg
  refine ⟨q, ?_, h3, ?_⟩
  · rw [Nat.mem_primeFactors]
    exact ⟨hq, dvd_trans (dvd_pow_self q he) hde, hK⟩
  · have hv1 : e ≤ padicValNat q K := by rw [← padicValNat_dvd_iff_le hK]; exact hde
    have hv2 : ¬ e+1 ≤ padicValNat q K := by rw [← padicValNat_dvd_iff_le hK]; exact hde2
    have : padicValNat q K = e := by omega
    rw [this]; exact Nat.not_even_iff_odd.mpr hodd

-- test exponent 3: 27 = 3^3 ∉ SS
example : ¬ ∃ x y, (27 : ℕ) = x^2 + y^2 :=
  not_ss_gen 27 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

-- test a 13-digit example: pick K = 4000000000003 = 7 * 571428571429 ; need a 3mod4 prime to odd power.
-- Instead use a clean one: K = 21 * (10^6)^2 ... let's test norm_num can do dvd on big numbers.

-- ===== Disproof skeleton (test extraction machinery) =====
def triangular_number (k : ℕ) : ℕ := k * (k + 1) / 2

noncomputable def A308584 (n : ℕ) : ℕ :=
  let T := triangular_number
  let bound := n + 1
  let R := Finset.range bound
  let search_space : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    ((R.product R).product R).product R
  (search_space.filter fun t =>
    let ab_pair := t.fst.fst
    let c         := t.fst.snd
    let d         := t.snd
    let a         := ab_pair.fst
    let b         := ab_pair.snd
    a ≤ b ∧ T a + T b + 5^c * 8^d = n
  ).card

theorem bridge (a b : ℕ) (h : a ≤ b) :
    4 * (triangular_number a + triangular_number b) + 1 = (a+b+1)^2 + (b-a)^2 := by
  unfold triangular_number
  have ha : a*(a+1)/2 * 2 = a*(a+1) := Nat.div_mul_cancel (even_mul_succ_self a).two_dvd
  have hb : b*(b+1)/2 * 2 = b*(b+1) := Nat.div_mul_cancel (even_mul_succ_self b).two_dvd
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have hba : (a + k) - a = k := by omega
  rw [hba]
  nlinarith [ha, hb]

-- Main disproof skeleton, with `key` (the case analysis) as a hypothesis.
example (N0 : ℕ) (hN0 : 0 < N0)
    (key : ∀ c d : ℕ, 5^c * 8^d ≤ N0 → ¬ ∃ x y, 4*(N0 - 5^c*8^d)+1 = x^2 + y^2)
    (H : ∀ (n : ℕ), n > 0 → A308584 n > 0) : False := by
  have h : 0 < A308584 N0 := H N0 hN0
  rw [A308584, Finset.card_pos] at h
  obtain ⟨t, ht⟩ := h
  rw [Finset.mem_filter] at ht
  obtain ⟨-, hab, heq⟩ := ht
  set a := t.1.1.1
  set b := t.1.1.2
  set c := t.1.2
  set d := t.2
  -- heq : triangular_number a + triangular_number b + 5^c*8^d = N0
  have hmle : 5^c * 8^d ≤ N0 := by omega
  have hbridge := bridge a b hab
  have hTT : triangular_number a + triangular_number b = N0 - 5^c*8^d := by omega
  refine key c d hmle ⟨a+b+1, b-a, ?_⟩
  rw [← hTT]; exact hbridge

-- Test: bounding c from 5^c ≤ N, then interval_cases (toy)
example (N : ℕ) (hN : N = 1000) (c d : ℕ) (hle : 5^c * 8^d ≤ N) :
    c ≤ 4 := by
  have h8 : 1 ≤ 8^d := Nat.one_le_pow _ _ (by norm_num)
  have hc : 5^c ≤ N := le_trans (Nat.le_mul_of_pos_right _ (by positivity)) hle
  subst hN
  by_contra hcon
  push_neg at hcon
  have : (5:ℕ)^5 ≤ 5^c := Nat.pow_le_pow_right (by norm_num) hcon
  omega

-- Test: a single not_ss application on a concrete not-SS number, e.g. K = 4*(1000-1)+1 = 3997 = 7*571.
-- 3997 = 7 * 571, 571 prime? 571 mod4=3. 7 mod4=3. pick q=7, exponent 1.
example : ¬ ∃ x y, (3997 : ℕ) = x^2 + y^2 := by
  have hq : Nat.Prime 7 := by norm_num
  haveI : Fact (Nat.Prime 7) := ⟨hq⟩
  rw [Nat.eq_sq_add_sq_iff]; push_neg
  refine ⟨7, ?_, by norm_num, ?_⟩
  · rw [Nat.mem_primeFactors]; exact ⟨hq, by norm_num, by norm_num⟩
  · have hv1 : 1 ≤ padicValNat 7 3997 := by rw [← padicValNat_dvd_iff_le (by norm_num)]; simpa using (by norm_num : (7:ℕ) ∣ 3997)
    have hv2 : ¬ 2 ≤ padicValNat 7 3997 := by rw [← padicValNat_dvd_iff_le (by norm_num)]; norm_num
    have : padicValNat 7 3997 = 1 := by omega
    rw [this]; decide
