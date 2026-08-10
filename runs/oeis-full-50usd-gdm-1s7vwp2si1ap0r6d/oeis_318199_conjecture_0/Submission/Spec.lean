import FormalConjectures.Util.ProblemImports

open Nat Real

/--
A318199: $a(n)$ is the largest integer $m$ such that $m^n \le n^{\mathrm{prime}(n)}$.
Equivalently, $a(n) = \lfloor n^{\mathrm{prime}(n)/n} \rfloor$.
-/
noncomputable def A318199 (n : ℕ) : ℕ :=
  if n = 0 then 0
  else
    let p_n : ℕ := Nat.nth Nat.Prime (n - 1)
    let result_real : ℝ := (n : ℝ) ^ ((p_n : ℝ) / n)
    (Int.toNat (floor result_real))

lemma step_ineq_div (n p q : ℕ) (hn : 1 ≤ n) (hpq : (n + 1) * p ≤ n * q) : 
  (p : ℝ) / (n : ℝ) ≤ (q : ℝ) / (n + 1 : ℝ) := by
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn1_pos : 0 < (n + 1 : ℝ) := by positivity
  rw [div_le_div_iff₀ hn_pos hn1_pos]
  rw [mul_comm (p : ℝ), mul_comm (q : ℝ)]
  exact_mod_cast hpq

lemma step_ineq (n p q : ℕ) (hn : 1 ≤ n) (hpn : n ≤ p) (hpq : (n + 1) * p ≤ n * q) :
  (n : ℝ) ^ ((p : ℝ) / n) + 1 ≤ (n + 1 : ℝ) ^ ((q : ℝ) / (n + 1)) := by
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn1_pos : 0 < (n + 1 : ℝ) := by positivity
  have h_div : (p : ℝ) / (n : ℝ) ≤ (q : ℝ) / (n + 1 : ℝ) := step_ineq_div n p q hn hpq
  have h_exp_le : (n + 1 : ℝ) ^ ((p : ℝ) / n) ≤ (n + 1 : ℝ) ^ ((q : ℝ) / (n + 1)) := by
    apply rpow_le_rpow_of_exponent_le
    · linarith
    · exact h_div
  have h_add_le : (n : ℝ) ^ ((p : ℝ) / n) + 1 ≤ (n + 1 : ℝ) ^ ((p : ℝ) / n) := by
    have hc : 1 ≤ (p : ℝ) / n := by
      rw [one_le_div hn_pos]
      exact_mod_cast hpn
    have h_add := @Real.add_rpow_le_rpow_add ((p : ℝ) / n) (n : ℝ) 1 (by positivity) (by positivity) hc
    simp only [one_rpow] at h_add
    exact h_add
  linarith

lemma floor_lt_floor_of_add_one_le {x y : ℝ} (h : x + 1 ≤ y) :
  Int.floor x < Int.floor y := by
  have h1 : Int.floor (x + 1) ≤ Int.floor y := Int.floor_mono h
  rw [Int.floor_add_one] at h1
  linarith

lemma toNat_lt_toNat_of_lt {a b : ℤ} (ha : 0 ≤ a) (h : a < b) :
  Int.toNat a < Int.toNat b := by
  omega

lemma Nat.floor_lt_floor_of_add_one_le {x y : ℝ} (hx : 0 ≤ x) (h : x + 1 ≤ y) :
  Nat.floor x < Nat.floor y := by
  have h1 : (Nat.floor x : ℤ) < (Nat.floor y : ℤ) := by
    rw [Int.natCast_floor_eq_floor hx]
    have hy : 0 ≤ y := by linarith
    rw [Int.natCast_floor_eq_floor hy]
    exact _root_.floor_lt_floor_of_add_one_le h
  exact_mod_cast h1

lemma A318199_step (n p q : ℕ) (hn : 1 ≤ n) (hp : Nat.nth Nat.Prime (n - 1) = p) (hq : Nat.nth Nat.Prime n = q)
  (hpn : n ≤ p) (hpq : (n + 1) * p ≤ n * q) : A318199 n < A318199 (n + 1) := by
  have hn_nz : n ≠ 0 := by omega
  have hn1_nz : n + 1 ≠ 0 := by omega
  unfold A318199
  rw [if_neg hn_nz, if_neg hn1_nz]
  have h_eq : n + 1 - 1 = n := by omega
  rw [h_eq]
  rw [hp, hq]
  simp only [Int.toNat_natCast]
  have hx : 0 ≤ (n : ℝ) ^ ((p : ℝ) / n) := by positivity
  apply Nat.floor_lt_floor_of_add_one_le hx
  exact_mod_cast step_ineq n p q hn hpn hpq

lemma count_lt_self_of_not_prime {n : ℕ} (hn : 0 < n) :
  count Nat.Prime n < n := by
  by_contra h_eq
  have h_le : count Nat.Prime n ≤ n := count_le (p := Nat.Prime)
  have h_eq' : count Nat.Prime n = n := by omega
  rw [count_iff_forall] at h_eq'
  have h0 : Nat.Prime 0 := h_eq' 0 hn
  exact Nat.not_prime_zero h0

def N : ℕ := 10073436

lemma base_count : count Nat.Prime 180820951 = 10073435 := by sorry

lemma prime_180820951 : Nat.Prime 180820951 := by norm_num
lemma prime_180820987 : Nat.Prime 180820987 := by norm_num
lemma prime_180821023 : Nat.Prime 180821023 := by norm_num
lemma prime_180821041 : Nat.Prime 180821041 := by norm_num
lemma prime_180821059 : Nat.Prime 180821059 := by norm_num
lemma prime_180821093 : Nat.Prime 180821093 := by norm_num
lemma prime_180821117 : Nat.Prime 180821117 := by norm_num
lemma prime_180821143 : Nat.Prime 180821143 := by norm_num
lemma prime_180821161 : Nat.Prime 180821161 := by norm_num
lemma prime_180821189 : Nat.Prime 180821189 := by norm_num
lemma prime_180821237 : Nat.Prime 180821237 := by norm_num
lemma prime_180821261 : Nat.Prime 180821261 := by norm_num
lemma prime_180821287 : Nat.Prime 180821287 := by norm_num
lemma prime_180821317 : Nat.Prime 180821317 := by norm_num
lemma prime_180821339 : Nat.Prime 180821339 := by norm_num
lemma prime_180821387 : Nat.Prime 180821387 := by norm_num
lemma prime_180821429 : Nat.Prime 180821429 := by norm_num
lemma prime_180821447 : Nat.Prime 180821447 := by norm_num

lemma npc_180820952 : ¬ Nat.Prime 180820952 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820952) (by decide) (by decide)
lemma npc_180820953 : ¬ Nat.Prime 180820953 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820953) (by decide) (by decide)
lemma npc_180820954 : ¬ Nat.Prime 180820954 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820954) (by decide) (by decide)
lemma npc_180820955 : ¬ Nat.Prime 180820955 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180820955) (by decide) (by decide)
lemma npc_180820956 : ¬ Nat.Prime 180820956 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820956) (by decide) (by decide)
lemma npc_180820957 : ¬ Nat.Prime 180820957 := Nat.not_prime_of_dvd_of_lt (by decide : 137 ∣ 180820957) (by decide) (by decide)
lemma npc_180820958 : ¬ Nat.Prime 180820958 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820958) (by decide) (by decide)
lemma npc_180820959 : ¬ Nat.Prime 180820959 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820959) (by decide) (by decide)
lemma npc_180820960 : ¬ Nat.Prime 180820960 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820960) (by decide) (by decide)
lemma npc_180820961 : ¬ Nat.Prime 180820961 := Nat.not_prime_of_dvd_of_lt (by decide : 37 ∣ 180820961) (by decide) (by decide)
lemma npc_180820962 : ¬ Nat.Prime 180820962 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820962) (by decide) (by decide)
lemma npc_180820963 : ¬ Nat.Prime 180820963 := Nat.not_prime_of_dvd_of_lt (by decide : 23 ∣ 180820963) (by decide) (by decide)
lemma npc_180820964 : ¬ Nat.Prime 180820964 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820964) (by decide) (by decide)
lemma npc_180820965 : ¬ Nat.Prime 180820965 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820965) (by decide) (by decide)
lemma npc_180820966 : ¬ Nat.Prime 180820966 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820966) (by decide) (by decide)
lemma npc_180820967 : ¬ Nat.Prime 180820967 := Nat.not_prime_of_dvd_of_lt (by decide : 19 ∣ 180820967) (by decide) (by decide)
lemma npc_180820968 : ¬ Nat.Prime 180820968 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820968) (by decide) (by decide)
lemma npc_180820969 : ¬ Nat.Prime 180820969 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180820969) (by decide) (by decide)
lemma npc_180820970 : ¬ Nat.Prime 180820970 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820970) (by decide) (by decide)
lemma npc_180820971 : ¬ Nat.Prime 180820971 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820971) (by decide) (by decide)
lemma npc_180820972 : ¬ Nat.Prime 180820972 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820972) (by decide) (by decide)
lemma npc_180820973 : ¬ Nat.Prime 180820973 := Nat.not_prime_of_dvd_of_lt (by decide : 2749 ∣ 180820973) (by decide) (by decide)
lemma npc_180820974 : ¬ Nat.Prime 180820974 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820974) (by decide) (by decide)
lemma npc_180820975 : ¬ Nat.Prime 180820975 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180820975) (by decide) (by decide)
lemma npc_180820976 : ¬ Nat.Prime 180820976 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820976) (by decide) (by decide)
lemma npc_180820977 : ¬ Nat.Prime 180820977 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820977) (by decide) (by decide)
lemma npc_180820978 : ¬ Nat.Prime 180820978 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820978) (by decide) (by decide)
lemma npc_180820979 : ¬ Nat.Prime 180820979 := Nat.not_prime_of_dvd_of_lt (by decide : 7793 ∣ 180820979) (by decide) (by decide)
lemma npc_180820980 : ¬ Nat.Prime 180820980 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820980) (by decide) (by decide)
lemma npc_180820981 : ¬ Nat.Prime 180820981 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180820981) (by decide) (by decide)
lemma npc_180820982 : ¬ Nat.Prime 180820982 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820982) (by decide) (by decide)
lemma npc_180820983 : ¬ Nat.Prime 180820983 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820983) (by decide) (by decide)
lemma npc_180820984 : ¬ Nat.Prime 180820984 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820984) (by decide) (by decide)
lemma npc_180820985 : ¬ Nat.Prime 180820985 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180820985) (by decide) (by decide)
lemma npc_180820986 : ¬ Nat.Prime 180820986 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820986) (by decide) (by decide)
lemma npc_180820988 : ¬ Nat.Prime 180820988 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820988) (by decide) (by decide)
lemma npc_180820989 : ¬ Nat.Prime 180820989 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820989) (by decide) (by decide)
lemma npc_180820990 : ¬ Nat.Prime 180820990 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820990) (by decide) (by decide)
lemma npc_180820991 : ¬ Nat.Prime 180820991 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180820991) (by decide) (by decide)
lemma npc_180820992 : ¬ Nat.Prime 180820992 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820992) (by decide) (by decide)
lemma npc_180820993 : ¬ Nat.Prime 180820993 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180820993) (by decide) (by decide)
lemma npc_180820994 : ¬ Nat.Prime 180820994 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820994) (by decide) (by decide)
lemma npc_180820995 : ¬ Nat.Prime 180820995 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180820995) (by decide) (by decide)
lemma npc_180820996 : ¬ Nat.Prime 180820996 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820996) (by decide) (by decide)
lemma npc_180820997 : ¬ Nat.Prime 180820997 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180820997) (by decide) (by decide)
lemma npc_180820998 : ¬ Nat.Prime 180820998 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180820998) (by decide) (by decide)
lemma npc_180820999 : ¬ Nat.Prime 180820999 := Nat.not_prime_of_dvd_of_lt (by decide : 467 ∣ 180820999) (by decide) (by decide)
lemma npc_180821000 : ¬ Nat.Prime 180821000 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821000) (by decide) (by decide)
lemma npc_180821001 : ¬ Nat.Prime 180821001 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821001) (by decide) (by decide)
lemma npc_180821002 : ¬ Nat.Prime 180821002 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821002) (by decide) (by decide)
lemma npc_180821003 : ¬ Nat.Prime 180821003 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821003) (by decide) (by decide)
lemma npc_180821004 : ¬ Nat.Prime 180821004 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821004) (by decide) (by decide)
lemma npc_180821005 : ¬ Nat.Prime 180821005 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821005) (by decide) (by decide)
lemma npc_180821006 : ¬ Nat.Prime 180821006 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821006) (by decide) (by decide)
lemma npc_180821007 : ¬ Nat.Prime 180821007 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821007) (by decide) (by decide)
lemma npc_180821008 : ¬ Nat.Prime 180821008 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821008) (by decide) (by decide)
lemma npc_180821009 : ¬ Nat.Prime 180821009 := Nat.not_prime_of_dvd_of_lt (by decide : 23 ∣ 180821009) (by decide) (by decide)
lemma npc_180821010 : ¬ Nat.Prime 180821010 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821010) (by decide) (by decide)
lemma npc_180821011 : ¬ Nat.Prime 180821011 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821011) (by decide) (by decide)
lemma npc_180821012 : ¬ Nat.Prime 180821012 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821012) (by decide) (by decide)
lemma npc_180821013 : ¬ Nat.Prime 180821013 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821013) (by decide) (by decide)
lemma npc_180821014 : ¬ Nat.Prime 180821014 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821014) (by decide) (by decide)
lemma npc_180821015 : ¬ Nat.Prime 180821015 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821015) (by decide) (by decide)
lemma npc_180821016 : ¬ Nat.Prime 180821016 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821016) (by decide) (by decide)
lemma npc_180821017 : ¬ Nat.Prime 180821017 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821017) (by decide) (by decide)
lemma npc_180821018 : ¬ Nat.Prime 180821018 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821018) (by decide) (by decide)
lemma npc_180821019 : ¬ Nat.Prime 180821019 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821019) (by decide) (by decide)
lemma npc_180821020 : ¬ Nat.Prime 180821020 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821020) (by decide) (by decide)
lemma npc_180821021 : ¬ Nat.Prime 180821021 := Nat.not_prime_of_dvd_of_lt (by decide : 2389 ∣ 180821021) (by decide) (by decide)
lemma npc_180821022 : ¬ Nat.Prime 180821022 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821022) (by decide) (by decide)
lemma npc_180821024 : ¬ Nat.Prime 180821024 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821024) (by decide) (by decide)
lemma npc_180821025 : ¬ Nat.Prime 180821025 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821025) (by decide) (by decide)
lemma npc_180821026 : ¬ Nat.Prime 180821026 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821026) (by decide) (by decide)
lemma npc_180821027 : ¬ Nat.Prime 180821027 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180821027) (by decide) (by decide)
lemma npc_180821028 : ¬ Nat.Prime 180821028 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821028) (by decide) (by decide)
lemma npc_180821029 : ¬ Nat.Prime 180821029 := Nat.not_prime_of_dvd_of_lt (by decide : 41 ∣ 180821029) (by decide) (by decide)
lemma npc_180821030 : ¬ Nat.Prime 180821030 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821030) (by decide) (by decide)
lemma npc_180821031 : ¬ Nat.Prime 180821031 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821031) (by decide) (by decide)
lemma npc_180821032 : ¬ Nat.Prime 180821032 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821032) (by decide) (by decide)
lemma npc_180821033 : ¬ Nat.Prime 180821033 := Nat.not_prime_of_dvd_of_lt (by decide : 89 ∣ 180821033) (by decide) (by decide)
lemma npc_180821034 : ¬ Nat.Prime 180821034 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821034) (by decide) (by decide)
lemma npc_180821035 : ¬ Nat.Prime 180821035 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821035) (by decide) (by decide)
lemma npc_180821036 : ¬ Nat.Prime 180821036 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821036) (by decide) (by decide)
lemma npc_180821037 : ¬ Nat.Prime 180821037 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821037) (by decide) (by decide)
lemma npc_180821038 : ¬ Nat.Prime 180821038 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821038) (by decide) (by decide)
lemma npc_180821039 : ¬ Nat.Prime 180821039 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821039) (by decide) (by decide)
lemma npc_180821040 : ¬ Nat.Prime 180821040 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821040) (by decide) (by decide)
lemma npc_180821042 : ¬ Nat.Prime 180821042 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821042) (by decide) (by decide)
lemma npc_180821043 : ¬ Nat.Prime 180821043 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821043) (by decide) (by decide)
lemma npc_180821044 : ¬ Nat.Prime 180821044 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821044) (by decide) (by decide)
lemma npc_180821045 : ¬ Nat.Prime 180821045 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821045) (by decide) (by decide)
lemma npc_180821046 : ¬ Nat.Prime 180821046 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821046) (by decide) (by decide)
lemma npc_180821047 : ¬ Nat.Prime 180821047 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821047) (by decide) (by decide)
lemma npc_180821048 : ¬ Nat.Prime 180821048 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821048) (by decide) (by decide)
lemma npc_180821049 : ¬ Nat.Prime 180821049 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821049) (by decide) (by decide)
lemma npc_180821050 : ¬ Nat.Prime 180821050 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821050) (by decide) (by decide)
lemma npc_180821051 : ¬ Nat.Prime 180821051 := Nat.not_prime_of_dvd_of_lt (by decide : 607 ∣ 180821051) (by decide) (by decide)
lemma npc_180821052 : ¬ Nat.Prime 180821052 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821052) (by decide) (by decide)
lemma npc_180821053 : ¬ Nat.Prime 180821053 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821053) (by decide) (by decide)
lemma npc_180821054 : ¬ Nat.Prime 180821054 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821054) (by decide) (by decide)
lemma npc_180821055 : ¬ Nat.Prime 180821055 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821055) (by decide) (by decide)
lemma npc_180821056 : ¬ Nat.Prime 180821056 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821056) (by decide) (by decide)
lemma npc_180821057 : ¬ Nat.Prime 180821057 := Nat.not_prime_of_dvd_of_lt (by decide : 337 ∣ 180821057) (by decide) (by decide)
lemma npc_180821058 : ¬ Nat.Prime 180821058 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821058) (by decide) (by decide)
lemma npc_180821060 : ¬ Nat.Prime 180821060 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821060) (by decide) (by decide)
lemma npc_180821061 : ¬ Nat.Prime 180821061 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821061) (by decide) (by decide)
lemma npc_180821062 : ¬ Nat.Prime 180821062 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821062) (by decide) (by decide)
lemma npc_180821063 : ¬ Nat.Prime 180821063 := Nat.not_prime_of_dvd_of_lt (by decide : 43 ∣ 180821063) (by decide) (by decide)
lemma npc_180821064 : ¬ Nat.Prime 180821064 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821064) (by decide) (by decide)
lemma npc_180821065 : ¬ Nat.Prime 180821065 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821065) (by decide) (by decide)
lemma npc_180821066 : ¬ Nat.Prime 180821066 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821066) (by decide) (by decide)
lemma npc_180821067 : ¬ Nat.Prime 180821067 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821067) (by decide) (by decide)
lemma npc_180821068 : ¬ Nat.Prime 180821068 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821068) (by decide) (by decide)
lemma npc_180821069 : ¬ Nat.Prime 180821069 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821069) (by decide) (by decide)
lemma npc_180821070 : ¬ Nat.Prime 180821070 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821070) (by decide) (by decide)
lemma npc_180821071 : ¬ Nat.Prime 180821071 := Nat.not_prime_of_dvd_of_lt (by decide : 7103 ∣ 180821071) (by decide) (by decide)
lemma npc_180821072 : ¬ Nat.Prime 180821072 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821072) (by decide) (by decide)
lemma npc_180821073 : ¬ Nat.Prime 180821073 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821073) (by decide) (by decide)
lemma npc_180821074 : ¬ Nat.Prime 180821074 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821074) (by decide) (by decide)
lemma npc_180821075 : ¬ Nat.Prime 180821075 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821075) (by decide) (by decide)
lemma npc_180821076 : ¬ Nat.Prime 180821076 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821076) (by decide) (by decide)
lemma npc_180821077 : ¬ Nat.Prime 180821077 := Nat.not_prime_of_dvd_of_lt (by decide : 1117 ∣ 180821077) (by decide) (by decide)
lemma npc_180821078 : ¬ Nat.Prime 180821078 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821078) (by decide) (by decide)
lemma npc_180821079 : ¬ Nat.Prime 180821079 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821079) (by decide) (by decide)
lemma npc_180821080 : ¬ Nat.Prime 180821080 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821080) (by decide) (by decide)
lemma npc_180821081 : ¬ Nat.Prime 180821081 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821081) (by decide) (by decide)
lemma npc_180821082 : ¬ Nat.Prime 180821082 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821082) (by decide) (by decide)
lemma npc_180821083 : ¬ Nat.Prime 180821083 := Nat.not_prime_of_dvd_of_lt (by decide : 5189 ∣ 180821083) (by decide) (by decide)
lemma npc_180821084 : ¬ Nat.Prime 180821084 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821084) (by decide) (by decide)
lemma npc_180821085 : ¬ Nat.Prime 180821085 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821085) (by decide) (by decide)
lemma npc_180821086 : ¬ Nat.Prime 180821086 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821086) (by decide) (by decide)
lemma npc_180821087 : ¬ Nat.Prime 180821087 := Nat.not_prime_of_dvd_of_lt (by decide : 167 ∣ 180821087) (by decide) (by decide)
lemma npc_180821088 : ¬ Nat.Prime 180821088 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821088) (by decide) (by decide)
lemma npc_180821089 : ¬ Nat.Prime 180821089 := Nat.not_prime_of_dvd_of_lt (by decide : 9001 ∣ 180821089) (by decide) (by decide)
lemma npc_180821090 : ¬ Nat.Prime 180821090 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821090) (by decide) (by decide)
lemma npc_180821091 : ¬ Nat.Prime 180821091 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821091) (by decide) (by decide)
lemma npc_180821092 : ¬ Nat.Prime 180821092 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821092) (by decide) (by decide)
lemma npc_180821094 : ¬ Nat.Prime 180821094 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821094) (by decide) (by decide)
lemma npc_180821095 : ¬ Nat.Prime 180821095 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821095) (by decide) (by decide)
lemma npc_180821096 : ¬ Nat.Prime 180821096 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821096) (by decide) (by decide)
lemma npc_180821097 : ¬ Nat.Prime 180821097 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821097) (by decide) (by decide)
lemma npc_180821098 : ¬ Nat.Prime 180821098 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821098) (by decide) (by decide)
lemma npc_180821099 : ¬ Nat.Prime 180821099 := Nat.not_prime_of_dvd_of_lt (by decide : 1361 ∣ 180821099) (by decide) (by decide)
lemma npc_180821100 : ¬ Nat.Prime 180821100 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821100) (by decide) (by decide)
lemma npc_180821101 : ¬ Nat.Prime 180821101 := Nat.not_prime_of_dvd_of_lt (by decide : 23 ∣ 180821101) (by decide) (by decide)
lemma npc_180821102 : ¬ Nat.Prime 180821102 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821102) (by decide) (by decide)
lemma npc_180821103 : ¬ Nat.Prime 180821103 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821103) (by decide) (by decide)
lemma npc_180821104 : ¬ Nat.Prime 180821104 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821104) (by decide) (by decide)
lemma npc_180821105 : ¬ Nat.Prime 180821105 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821105) (by decide) (by decide)
lemma npc_180821106 : ¬ Nat.Prime 180821106 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821106) (by decide) (by decide)
lemma npc_180821107 : ¬ Nat.Prime 180821107 := Nat.not_prime_of_dvd_of_lt (by decide : 53 ∣ 180821107) (by decide) (by decide)
lemma npc_180821108 : ¬ Nat.Prime 180821108 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821108) (by decide) (by decide)
lemma npc_180821109 : ¬ Nat.Prime 180821109 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821109) (by decide) (by decide)
lemma npc_180821110 : ¬ Nat.Prime 180821110 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821110) (by decide) (by decide)
lemma npc_180821111 : ¬ Nat.Prime 180821111 := Nat.not_prime_of_dvd_of_lt (by decide : 41 ∣ 180821111) (by decide) (by decide)
lemma npc_180821112 : ¬ Nat.Prime 180821112 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821112) (by decide) (by decide)
lemma npc_180821113 : ¬ Nat.Prime 180821113 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821113) (by decide) (by decide)
lemma npc_180821114 : ¬ Nat.Prime 180821114 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821114) (by decide) (by decide)
lemma npc_180821115 : ¬ Nat.Prime 180821115 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821115) (by decide) (by decide)
lemma npc_180821116 : ¬ Nat.Prime 180821116 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821116) (by decide) (by decide)
lemma npc_180821118 : ¬ Nat.Prime 180821118 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821118) (by decide) (by decide)
lemma npc_180821119 : ¬ Nat.Prime 180821119 := Nat.not_prime_of_dvd_of_lt (by decide : 19 ∣ 180821119) (by decide) (by decide)
lemma npc_180821120 : ¬ Nat.Prime 180821120 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821120) (by decide) (by decide)
lemma npc_180821121 : ¬ Nat.Prime 180821121 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821121) (by decide) (by decide)
lemma npc_180821122 : ¬ Nat.Prime 180821122 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821122) (by decide) (by decide)
lemma npc_180821123 : ¬ Nat.Prime 180821123 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821123) (by decide) (by decide)
lemma npc_180821124 : ¬ Nat.Prime 180821124 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821124) (by decide) (by decide)
lemma npc_180821125 : ¬ Nat.Prime 180821125 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821125) (by decide) (by decide)
lemma npc_180821126 : ¬ Nat.Prime 180821126 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821126) (by decide) (by decide)
lemma npc_180821127 : ¬ Nat.Prime 180821127 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821127) (by decide) (by decide)
lemma npc_180821128 : ¬ Nat.Prime 180821128 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821128) (by decide) (by decide)
lemma npc_180821129 : ¬ Nat.Prime 180821129 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180821129) (by decide) (by decide)
lemma npc_180821130 : ¬ Nat.Prime 180821130 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821130) (by decide) (by decide)
lemma npc_180821131 : ¬ Nat.Prime 180821131 := Nat.not_prime_of_dvd_of_lt (by decide : 113 ∣ 180821131) (by decide) (by decide)
lemma npc_180821132 : ¬ Nat.Prime 180821132 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821132) (by decide) (by decide)
lemma npc_180821133 : ¬ Nat.Prime 180821133 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821133) (by decide) (by decide)
lemma npc_180821134 : ¬ Nat.Prime 180821134 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821134) (by decide) (by decide)
lemma npc_180821135 : ¬ Nat.Prime 180821135 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821135) (by decide) (by decide)
lemma npc_180821136 : ¬ Nat.Prime 180821136 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821136) (by decide) (by decide)
lemma npc_180821137 : ¬ Nat.Prime 180821137 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821137) (by decide) (by decide)
lemma npc_180821138 : ¬ Nat.Prime 180821138 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821138) (by decide) (by decide)
lemma npc_180821139 : ¬ Nat.Prime 180821139 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821139) (by decide) (by decide)
lemma npc_180821140 : ¬ Nat.Prime 180821140 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821140) (by decide) (by decide)
lemma npc_180821141 : ¬ Nat.Prime 180821141 := Nat.not_prime_of_dvd_of_lt (by decide : 61 ∣ 180821141) (by decide) (by decide)
lemma npc_180821142 : ¬ Nat.Prime 180821142 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821142) (by decide) (by decide)
lemma npc_180821144 : ¬ Nat.Prime 180821144 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821144) (by decide) (by decide)
lemma npc_180821145 : ¬ Nat.Prime 180821145 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821145) (by decide) (by decide)
lemma npc_180821146 : ¬ Nat.Prime 180821146 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821146) (by decide) (by decide)
lemma npc_180821147 : ¬ Nat.Prime 180821147 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821147) (by decide) (by decide)
lemma npc_180821148 : ¬ Nat.Prime 180821148 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821148) (by decide) (by decide)
lemma npc_180821149 : ¬ Nat.Prime 180821149 := Nat.not_prime_of_dvd_of_lt (by decide : 43 ∣ 180821149) (by decide) (by decide)
lemma npc_180821150 : ¬ Nat.Prime 180821150 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821150) (by decide) (by decide)
lemma npc_180821151 : ¬ Nat.Prime 180821151 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821151) (by decide) (by decide)
lemma npc_180821152 : ¬ Nat.Prime 180821152 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821152) (by decide) (by decide)
lemma npc_180821153 : ¬ Nat.Prime 180821153 := Nat.not_prime_of_dvd_of_lt (by decide : 251 ∣ 180821153) (by decide) (by decide)
lemma npc_180821154 : ¬ Nat.Prime 180821154 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821154) (by decide) (by decide)
lemma npc_180821155 : ¬ Nat.Prime 180821155 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821155) (by decide) (by decide)
lemma npc_180821156 : ¬ Nat.Prime 180821156 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821156) (by decide) (by decide)
lemma npc_180821157 : ¬ Nat.Prime 180821157 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821157) (by decide) (by decide)
lemma npc_180821158 : ¬ Nat.Prime 180821158 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821158) (by decide) (by decide)
lemma npc_180821159 : ¬ Nat.Prime 180821159 := Nat.not_prime_of_dvd_of_lt (by decide : 887 ∣ 180821159) (by decide) (by decide)
lemma npc_180821160 : ¬ Nat.Prime 180821160 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821160) (by decide) (by decide)
lemma npc_180821162 : ¬ Nat.Prime 180821162 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821162) (by decide) (by decide)
lemma npc_180821163 : ¬ Nat.Prime 180821163 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821163) (by decide) (by decide)
lemma npc_180821164 : ¬ Nat.Prime 180821164 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821164) (by decide) (by decide)
lemma npc_180821165 : ¬ Nat.Prime 180821165 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821165) (by decide) (by decide)
lemma npc_180821166 : ¬ Nat.Prime 180821166 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821166) (by decide) (by decide)
lemma npc_180821167 : ¬ Nat.Prime 180821167 := Nat.not_prime_of_dvd_of_lt (by decide : 71 ∣ 180821167) (by decide) (by decide)
lemma npc_180821168 : ¬ Nat.Prime 180821168 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821168) (by decide) (by decide)
lemma npc_180821169 : ¬ Nat.Prime 180821169 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821169) (by decide) (by decide)
lemma npc_180821170 : ¬ Nat.Prime 180821170 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821170) (by decide) (by decide)
lemma npc_180821171 : ¬ Nat.Prime 180821171 := Nat.not_prime_of_dvd_of_lt (by decide : 31 ∣ 180821171) (by decide) (by decide)
lemma npc_180821172 : ¬ Nat.Prime 180821172 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821172) (by decide) (by decide)
lemma npc_180821173 : ¬ Nat.Prime 180821173 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821173) (by decide) (by decide)
lemma npc_180821174 : ¬ Nat.Prime 180821174 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821174) (by decide) (by decide)
lemma npc_180821175 : ¬ Nat.Prime 180821175 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821175) (by decide) (by decide)
lemma npc_180821176 : ¬ Nat.Prime 180821176 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821176) (by decide) (by decide)
lemma npc_180821177 : ¬ Nat.Prime 180821177 := Nat.not_prime_of_dvd_of_lt (by decide : 29 ∣ 180821177) (by decide) (by decide)
lemma npc_180821178 : ¬ Nat.Prime 180821178 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821178) (by decide) (by decide)
lemma npc_180821179 : ¬ Nat.Prime 180821179 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821179) (by decide) (by decide)
lemma npc_180821180 : ¬ Nat.Prime 180821180 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821180) (by decide) (by decide)
lemma npc_180821181 : ¬ Nat.Prime 180821181 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821181) (by decide) (by decide)
lemma npc_180821182 : ¬ Nat.Prime 180821182 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821182) (by decide) (by decide)
lemma npc_180821183 : ¬ Nat.Prime 180821183 := Nat.not_prime_of_dvd_of_lt (by decide : 37 ∣ 180821183) (by decide) (by decide)
lemma npc_180821184 : ¬ Nat.Prime 180821184 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821184) (by decide) (by decide)
lemma npc_180821185 : ¬ Nat.Prime 180821185 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821185) (by decide) (by decide)
lemma npc_180821186 : ¬ Nat.Prime 180821186 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821186) (by decide) (by decide)
lemma npc_180821187 : ¬ Nat.Prime 180821187 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821187) (by decide) (by decide)
lemma npc_180821188 : ¬ Nat.Prime 180821188 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821188) (by decide) (by decide)
lemma npc_180821190 : ¬ Nat.Prime 180821190 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821190) (by decide) (by decide)
lemma npc_180821191 : ¬ Nat.Prime 180821191 := Nat.not_prime_of_dvd_of_lt (by decide : 11257 ∣ 180821191) (by decide) (by decide)
lemma npc_180821192 : ¬ Nat.Prime 180821192 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821192) (by decide) (by decide)
lemma npc_180821193 : ¬ Nat.Prime 180821193 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821193) (by decide) (by decide)
lemma npc_180821194 : ¬ Nat.Prime 180821194 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821194) (by decide) (by decide)
lemma npc_180821195 : ¬ Nat.Prime 180821195 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821195) (by decide) (by decide)
lemma npc_180821196 : ¬ Nat.Prime 180821196 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821196) (by decide) (by decide)
lemma npc_180821197 : ¬ Nat.Prime 180821197 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180821197) (by decide) (by decide)
lemma npc_180821198 : ¬ Nat.Prime 180821198 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821198) (by decide) (by decide)
lemma npc_180821199 : ¬ Nat.Prime 180821199 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821199) (by decide) (by decide)
lemma npc_180821200 : ¬ Nat.Prime 180821200 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821200) (by decide) (by decide)
lemma npc_180821201 : ¬ Nat.Prime 180821201 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821201) (by decide) (by decide)
lemma npc_180821202 : ¬ Nat.Prime 180821202 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821202) (by decide) (by decide)
lemma npc_180821203 : ¬ Nat.Prime 180821203 := Nat.not_prime_of_dvd_of_lt (by decide : 127 ∣ 180821203) (by decide) (by decide)
lemma npc_180821204 : ¬ Nat.Prime 180821204 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821204) (by decide) (by decide)
lemma npc_180821205 : ¬ Nat.Prime 180821205 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821205) (by decide) (by decide)
lemma npc_180821206 : ¬ Nat.Prime 180821206 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821206) (by decide) (by decide)
lemma npc_180821207 : ¬ Nat.Prime 180821207 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821207) (by decide) (by decide)
lemma npc_180821208 : ¬ Nat.Prime 180821208 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821208) (by decide) (by decide)
lemma npc_180821209 : ¬ Nat.Prime 180821209 := Nat.not_prime_of_dvd_of_lt (by decide : 101 ∣ 180821209) (by decide) (by decide)
lemma npc_180821210 : ¬ Nat.Prime 180821210 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821210) (by decide) (by decide)
lemma npc_180821211 : ¬ Nat.Prime 180821211 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821211) (by decide) (by decide)
lemma npc_180821212 : ¬ Nat.Prime 180821212 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821212) (by decide) (by decide)
lemma npc_180821213 : ¬ Nat.Prime 180821213 := Nat.not_prime_of_dvd_of_lt (by decide : 53 ∣ 180821213) (by decide) (by decide)
lemma npc_180821214 : ¬ Nat.Prime 180821214 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821214) (by decide) (by decide)
lemma npc_180821215 : ¬ Nat.Prime 180821215 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821215) (by decide) (by decide)
lemma npc_180821216 : ¬ Nat.Prime 180821216 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821216) (by decide) (by decide)
lemma npc_180821217 : ¬ Nat.Prime 180821217 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821217) (by decide) (by decide)
lemma npc_180821218 : ¬ Nat.Prime 180821218 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821218) (by decide) (by decide)
lemma npc_180821219 : ¬ Nat.Prime 180821219 := Nat.not_prime_of_dvd_of_lt (by decide : 73 ∣ 180821219) (by decide) (by decide)
lemma npc_180821220 : ¬ Nat.Prime 180821220 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821220) (by decide) (by decide)
lemma npc_180821221 : ¬ Nat.Prime 180821221 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821221) (by decide) (by decide)
lemma npc_180821222 : ¬ Nat.Prime 180821222 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821222) (by decide) (by decide)
lemma npc_180821223 : ¬ Nat.Prime 180821223 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821223) (by decide) (by decide)
lemma npc_180821224 : ¬ Nat.Prime 180821224 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821224) (by decide) (by decide)
lemma npc_180821225 : ¬ Nat.Prime 180821225 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821225) (by decide) (by decide)
lemma npc_180821226 : ¬ Nat.Prime 180821226 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821226) (by decide) (by decide)
lemma npc_180821227 : ¬ Nat.Prime 180821227 := Nat.not_prime_of_dvd_of_lt (by decide : 83 ∣ 180821227) (by decide) (by decide)
lemma npc_180821228 : ¬ Nat.Prime 180821228 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821228) (by decide) (by decide)
lemma npc_180821229 : ¬ Nat.Prime 180821229 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821229) (by decide) (by decide)
lemma npc_180821230 : ¬ Nat.Prime 180821230 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821230) (by decide) (by decide)
lemma npc_180821231 : ¬ Nat.Prime 180821231 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180821231) (by decide) (by decide)
lemma npc_180821232 : ¬ Nat.Prime 180821232 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821232) (by decide) (by decide)
lemma npc_180821233 : ¬ Nat.Prime 180821233 := Nat.not_prime_of_dvd_of_lt (by decide : 19 ∣ 180821233) (by decide) (by decide)
lemma npc_180821234 : ¬ Nat.Prime 180821234 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821234) (by decide) (by decide)
lemma npc_180821235 : ¬ Nat.Prime 180821235 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821235) (by decide) (by decide)
lemma npc_180821236 : ¬ Nat.Prime 180821236 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821236) (by decide) (by decide)
lemma npc_180821238 : ¬ Nat.Prime 180821238 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821238) (by decide) (by decide)
lemma npc_180821239 : ¬ Nat.Prime 180821239 := Nat.not_prime_of_dvd_of_lt (by decide : 23 ∣ 180821239) (by decide) (by decide)
lemma npc_180821240 : ¬ Nat.Prime 180821240 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821240) (by decide) (by decide)
lemma npc_180821241 : ¬ Nat.Prime 180821241 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821241) (by decide) (by decide)
lemma npc_180821242 : ¬ Nat.Prime 180821242 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821242) (by decide) (by decide)
lemma npc_180821243 : ¬ Nat.Prime 180821243 := Nat.not_prime_of_dvd_of_lt (by decide : 547 ∣ 180821243) (by decide) (by decide)
lemma npc_180821244 : ¬ Nat.Prime 180821244 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821244) (by decide) (by decide)
lemma npc_180821245 : ¬ Nat.Prime 180821245 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821245) (by decide) (by decide)
lemma npc_180821246 : ¬ Nat.Prime 180821246 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821246) (by decide) (by decide)
lemma npc_180821247 : ¬ Nat.Prime 180821247 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821247) (by decide) (by decide)
lemma npc_180821248 : ¬ Nat.Prime 180821248 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821248) (by decide) (by decide)
lemma npc_180821249 : ¬ Nat.Prime 180821249 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821249) (by decide) (by decide)
lemma npc_180821250 : ¬ Nat.Prime 180821250 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821250) (by decide) (by decide)
lemma npc_180821251 : ¬ Nat.Prime 180821251 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821251) (by decide) (by decide)
lemma npc_180821252 : ¬ Nat.Prime 180821252 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821252) (by decide) (by decide)
lemma npc_180821253 : ¬ Nat.Prime 180821253 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821253) (by decide) (by decide)
lemma npc_180821254 : ¬ Nat.Prime 180821254 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821254) (by decide) (by decide)
lemma npc_180821255 : ¬ Nat.Prime 180821255 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821255) (by decide) (by decide)
lemma npc_180821256 : ¬ Nat.Prime 180821256 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821256) (by decide) (by decide)
lemma npc_180821257 : ¬ Nat.Prime 180821257 := Nat.not_prime_of_dvd_of_lt (by decide : 37 ∣ 180821257) (by decide) (by decide)
lemma npc_180821258 : ¬ Nat.Prime 180821258 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821258) (by decide) (by decide)
lemma npc_180821259 : ¬ Nat.Prime 180821259 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821259) (by decide) (by decide)
lemma npc_180821260 : ¬ Nat.Prime 180821260 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821260) (by decide) (by decide)
lemma npc_180821262 : ¬ Nat.Prime 180821262 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821262) (by decide) (by decide)
lemma npc_180821263 : ¬ Nat.Prime 180821263 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821263) (by decide) (by decide)
lemma npc_180821264 : ¬ Nat.Prime 180821264 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821264) (by decide) (by decide)
lemma npc_180821265 : ¬ Nat.Prime 180821265 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821265) (by decide) (by decide)
lemma npc_180821266 : ¬ Nat.Prime 180821266 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821266) (by decide) (by decide)
lemma npc_180821267 : ¬ Nat.Prime 180821267 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821267) (by decide) (by decide)
lemma npc_180821268 : ¬ Nat.Prime 180821268 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821268) (by decide) (by decide)
lemma npc_180821269 : ¬ Nat.Prime 180821269 := Nat.not_prime_of_dvd_of_lt (by decide : 6053 ∣ 180821269) (by decide) (by decide)
lemma npc_180821270 : ¬ Nat.Prime 180821270 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821270) (by decide) (by decide)
lemma npc_180821271 : ¬ Nat.Prime 180821271 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821271) (by decide) (by decide)
lemma npc_180821272 : ¬ Nat.Prime 180821272 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821272) (by decide) (by decide)
lemma npc_180821273 : ¬ Nat.Prime 180821273 := Nat.not_prime_of_dvd_of_lt (by decide : 5021 ∣ 180821273) (by decide) (by decide)
lemma npc_180821274 : ¬ Nat.Prime 180821274 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821274) (by decide) (by decide)
lemma npc_180821275 : ¬ Nat.Prime 180821275 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821275) (by decide) (by decide)
lemma npc_180821276 : ¬ Nat.Prime 180821276 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821276) (by decide) (by decide)
lemma npc_180821277 : ¬ Nat.Prime 180821277 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821277) (by decide) (by decide)
lemma npc_180821278 : ¬ Nat.Prime 180821278 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821278) (by decide) (by decide)
lemma npc_180821279 : ¬ Nat.Prime 180821279 := Nat.not_prime_of_dvd_of_lt (by decide : 163 ∣ 180821279) (by decide) (by decide)
lemma npc_180821280 : ¬ Nat.Prime 180821280 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821280) (by decide) (by decide)
lemma npc_180821281 : ¬ Nat.Prime 180821281 := Nat.not_prime_of_dvd_of_lt (by decide : 233 ∣ 180821281) (by decide) (by decide)
lemma npc_180821282 : ¬ Nat.Prime 180821282 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821282) (by decide) (by decide)
lemma npc_180821283 : ¬ Nat.Prime 180821283 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821283) (by decide) (by decide)
lemma npc_180821284 : ¬ Nat.Prime 180821284 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821284) (by decide) (by decide)
lemma npc_180821285 : ¬ Nat.Prime 180821285 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821285) (by decide) (by decide)
lemma npc_180821286 : ¬ Nat.Prime 180821286 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821286) (by decide) (by decide)
lemma npc_180821288 : ¬ Nat.Prime 180821288 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821288) (by decide) (by decide)
lemma npc_180821289 : ¬ Nat.Prime 180821289 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821289) (by decide) (by decide)
lemma npc_180821290 : ¬ Nat.Prime 180821290 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821290) (by decide) (by decide)
lemma npc_180821291 : ¬ Nat.Prime 180821291 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821291) (by decide) (by decide)
lemma npc_180821292 : ¬ Nat.Prime 180821292 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821292) (by decide) (by decide)
lemma npc_180821293 : ¬ Nat.Prime 180821293 := Nat.not_prime_of_dvd_of_lt (by decide : 29 ∣ 180821293) (by decide) (by decide)
lemma npc_180821294 : ¬ Nat.Prime 180821294 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821294) (by decide) (by decide)
lemma npc_180821295 : ¬ Nat.Prime 180821295 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821295) (by decide) (by decide)
lemma npc_180821296 : ¬ Nat.Prime 180821296 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821296) (by decide) (by decide)
lemma npc_180821297 : ¬ Nat.Prime 180821297 := Nat.not_prime_of_dvd_of_lt (by decide : 4129 ∣ 180821297) (by decide) (by decide)
lemma npc_180821298 : ¬ Nat.Prime 180821298 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821298) (by decide) (by decide)
lemma npc_180821299 : ¬ Nat.Prime 180821299 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180821299) (by decide) (by decide)
lemma npc_180821300 : ¬ Nat.Prime 180821300 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821300) (by decide) (by decide)
lemma npc_180821301 : ¬ Nat.Prime 180821301 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821301) (by decide) (by decide)
lemma npc_180821302 : ¬ Nat.Prime 180821302 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821302) (by decide) (by decide)
lemma npc_180821303 : ¬ Nat.Prime 180821303 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821303) (by decide) (by decide)
lemma npc_180821304 : ¬ Nat.Prime 180821304 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821304) (by decide) (by decide)
lemma npc_180821305 : ¬ Nat.Prime 180821305 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821305) (by decide) (by decide)
lemma npc_180821306 : ¬ Nat.Prime 180821306 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821306) (by decide) (by decide)
lemma npc_180821307 : ¬ Nat.Prime 180821307 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821307) (by decide) (by decide)
lemma npc_180821308 : ¬ Nat.Prime 180821308 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821308) (by decide) (by decide)
lemma npc_180821309 : ¬ Nat.Prime 180821309 := Nat.not_prime_of_dvd_of_lt (by decide : 19 ∣ 180821309) (by decide) (by decide)
lemma npc_180821310 : ¬ Nat.Prime 180821310 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821310) (by decide) (by decide)
lemma npc_180821311 : ¬ Nat.Prime 180821311 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821311) (by decide) (by decide)
lemma npc_180821312 : ¬ Nat.Prime 180821312 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821312) (by decide) (by decide)
lemma npc_180821313 : ¬ Nat.Prime 180821313 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821313) (by decide) (by decide)
lemma npc_180821314 : ¬ Nat.Prime 180821314 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821314) (by decide) (by decide)
lemma npc_180821315 : ¬ Nat.Prime 180821315 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821315) (by decide) (by decide)
lemma npc_180821316 : ¬ Nat.Prime 180821316 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821316) (by decide) (by decide)
lemma npc_180821318 : ¬ Nat.Prime 180821318 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821318) (by decide) (by decide)
lemma npc_180821319 : ¬ Nat.Prime 180821319 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821319) (by decide) (by decide)
lemma npc_180821320 : ¬ Nat.Prime 180821320 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821320) (by decide) (by decide)
lemma npc_180821321 : ¬ Nat.Prime 180821321 := Nat.not_prime_of_dvd_of_lt (by decide : 43 ∣ 180821321) (by decide) (by decide)
lemma npc_180821322 : ¬ Nat.Prime 180821322 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821322) (by decide) (by decide)
lemma npc_180821323 : ¬ Nat.Prime 180821323 := Nat.not_prime_of_dvd_of_lt (by decide : 937 ∣ 180821323) (by decide) (by decide)
lemma npc_180821324 : ¬ Nat.Prime 180821324 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821324) (by decide) (by decide)
lemma npc_180821325 : ¬ Nat.Prime 180821325 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821325) (by decide) (by decide)
lemma npc_180821326 : ¬ Nat.Prime 180821326 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821326) (by decide) (by decide)
lemma npc_180821327 : ¬ Nat.Prime 180821327 := Nat.not_prime_of_dvd_of_lt (by decide : 4271 ∣ 180821327) (by decide) (by decide)
lemma npc_180821328 : ¬ Nat.Prime 180821328 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821328) (by decide) (by decide)
lemma npc_180821329 : ¬ Nat.Prime 180821329 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821329) (by decide) (by decide)
lemma npc_180821330 : ¬ Nat.Prime 180821330 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821330) (by decide) (by decide)
lemma npc_180821331 : ¬ Nat.Prime 180821331 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821331) (by decide) (by decide)
lemma npc_180821332 : ¬ Nat.Prime 180821332 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821332) (by decide) (by decide)
lemma npc_180821333 : ¬ Nat.Prime 180821333 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821333) (by decide) (by decide)
lemma npc_180821334 : ¬ Nat.Prime 180821334 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821334) (by decide) (by decide)
lemma npc_180821335 : ¬ Nat.Prime 180821335 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821335) (by decide) (by decide)
lemma npc_180821336 : ¬ Nat.Prime 180821336 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821336) (by decide) (by decide)
lemma npc_180821337 : ¬ Nat.Prime 180821337 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821337) (by decide) (by decide)
lemma npc_180821338 : ¬ Nat.Prime 180821338 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821338) (by decide) (by decide)
lemma npc_180821340 : ¬ Nat.Prime 180821340 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821340) (by decide) (by decide)
lemma npc_180821341 : ¬ Nat.Prime 180821341 := Nat.not_prime_of_dvd_of_lt (by decide : 103 ∣ 180821341) (by decide) (by decide)
lemma npc_180821342 : ¬ Nat.Prime 180821342 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821342) (by decide) (by decide)
lemma npc_180821343 : ¬ Nat.Prime 180821343 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821343) (by decide) (by decide)
lemma npc_180821344 : ¬ Nat.Prime 180821344 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821344) (by decide) (by decide)
lemma npc_180821345 : ¬ Nat.Prime 180821345 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821345) (by decide) (by decide)
lemma npc_180821346 : ¬ Nat.Prime 180821346 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821346) (by decide) (by decide)
lemma npc_180821347 : ¬ Nat.Prime 180821347 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821347) (by decide) (by decide)
lemma npc_180821348 : ¬ Nat.Prime 180821348 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821348) (by decide) (by decide)
lemma npc_180821349 : ¬ Nat.Prime 180821349 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821349) (by decide) (by decide)
lemma npc_180821350 : ¬ Nat.Prime 180821350 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821350) (by decide) (by decide)
lemma npc_180821351 : ¬ Nat.Prime 180821351 := Nat.not_prime_of_dvd_of_lt (by decide : 29 ∣ 180821351) (by decide) (by decide)
lemma npc_180821352 : ¬ Nat.Prime 180821352 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821352) (by decide) (by decide)
lemma npc_180821353 : ¬ Nat.Prime 180821353 := Nat.not_prime_of_dvd_of_lt (by decide : 181 ∣ 180821353) (by decide) (by decide)
lemma npc_180821354 : ¬ Nat.Prime 180821354 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821354) (by decide) (by decide)
lemma npc_180821355 : ¬ Nat.Prime 180821355 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821355) (by decide) (by decide)
lemma npc_180821356 : ¬ Nat.Prime 180821356 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821356) (by decide) (by decide)
lemma npc_180821357 : ¬ Nat.Prime 180821357 := Nat.not_prime_of_dvd_of_lt (by decide : 31 ∣ 180821357) (by decide) (by decide)
lemma npc_180821358 : ¬ Nat.Prime 180821358 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821358) (by decide) (by decide)
lemma npc_180821359 : ¬ Nat.Prime 180821359 := Nat.not_prime_of_dvd_of_lt (by decide : 1201 ∣ 180821359) (by decide) (by decide)
lemma npc_180821360 : ¬ Nat.Prime 180821360 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821360) (by decide) (by decide)
lemma npc_180821361 : ¬ Nat.Prime 180821361 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821361) (by decide) (by decide)
lemma npc_180821362 : ¬ Nat.Prime 180821362 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821362) (by decide) (by decide)
lemma npc_180821363 : ¬ Nat.Prime 180821363 := Nat.not_prime_of_dvd_of_lt (by decide : 1087 ∣ 180821363) (by decide) (by decide)
lemma npc_180821364 : ¬ Nat.Prime 180821364 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821364) (by decide) (by decide)
lemma npc_180821365 : ¬ Nat.Prime 180821365 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821365) (by decide) (by decide)
lemma npc_180821366 : ¬ Nat.Prime 180821366 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821366) (by decide) (by decide)
lemma npc_180821367 : ¬ Nat.Prime 180821367 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821367) (by decide) (by decide)
lemma npc_180821368 : ¬ Nat.Prime 180821368 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821368) (by decide) (by decide)
lemma npc_180821369 : ¬ Nat.Prime 180821369 := Nat.not_prime_of_dvd_of_lt (by decide : 8893 ∣ 180821369) (by decide) (by decide)
lemma npc_180821370 : ¬ Nat.Prime 180821370 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821370) (by decide) (by decide)
lemma npc_180821371 : ¬ Nat.Prime 180821371 := Nat.not_prime_of_dvd_of_lt (by decide : 59 ∣ 180821371) (by decide) (by decide)
lemma npc_180821372 : ¬ Nat.Prime 180821372 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821372) (by decide) (by decide)
lemma npc_180821373 : ¬ Nat.Prime 180821373 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821373) (by decide) (by decide)
lemma npc_180821374 : ¬ Nat.Prime 180821374 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821374) (by decide) (by decide)
lemma npc_180821375 : ¬ Nat.Prime 180821375 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821375) (by decide) (by decide)
lemma npc_180821376 : ¬ Nat.Prime 180821376 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821376) (by decide) (by decide)
lemma npc_180821377 : ¬ Nat.Prime 180821377 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821377) (by decide) (by decide)
lemma npc_180821378 : ¬ Nat.Prime 180821378 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821378) (by decide) (by decide)
lemma npc_180821379 : ¬ Nat.Prime 180821379 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821379) (by decide) (by decide)
lemma npc_180821380 : ¬ Nat.Prime 180821380 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821380) (by decide) (by decide)
lemma npc_180821381 : ¬ Nat.Prime 180821381 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821381) (by decide) (by decide)
lemma npc_180821382 : ¬ Nat.Prime 180821382 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821382) (by decide) (by decide)
lemma npc_180821383 : ¬ Nat.Prime 180821383 := Nat.not_prime_of_dvd_of_lt (by decide : 1637 ∣ 180821383) (by decide) (by decide)
lemma npc_180821384 : ¬ Nat.Prime 180821384 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821384) (by decide) (by decide)
lemma npc_180821385 : ¬ Nat.Prime 180821385 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821385) (by decide) (by decide)
lemma npc_180821386 : ¬ Nat.Prime 180821386 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821386) (by decide) (by decide)
lemma npc_180821388 : ¬ Nat.Prime 180821388 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821388) (by decide) (by decide)
lemma npc_180821389 : ¬ Nat.Prime 180821389 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821389) (by decide) (by decide)
lemma npc_180821390 : ¬ Nat.Prime 180821390 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821390) (by decide) (by decide)
lemma npc_180821391 : ¬ Nat.Prime 180821391 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821391) (by decide) (by decide)
lemma npc_180821392 : ¬ Nat.Prime 180821392 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821392) (by decide) (by decide)
lemma npc_180821393 : ¬ Nat.Prime 180821393 := Nat.not_prime_of_dvd_of_lt (by decide : 83 ∣ 180821393) (by decide) (by decide)
lemma npc_180821394 : ¬ Nat.Prime 180821394 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821394) (by decide) (by decide)
lemma npc_180821395 : ¬ Nat.Prime 180821395 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821395) (by decide) (by decide)
lemma npc_180821396 : ¬ Nat.Prime 180821396 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821396) (by decide) (by decide)
lemma npc_180821397 : ¬ Nat.Prime 180821397 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821397) (by decide) (by decide)
lemma npc_180821398 : ¬ Nat.Prime 180821398 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821398) (by decide) (by decide)
lemma npc_180821399 : ¬ Nat.Prime 180821399 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821399) (by decide) (by decide)
lemma npc_180821400 : ¬ Nat.Prime 180821400 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821400) (by decide) (by decide)
lemma npc_180821401 : ¬ Nat.Prime 180821401 := Nat.not_prime_of_dvd_of_lt (by decide : 17 ∣ 180821401) (by decide) (by decide)
lemma npc_180821402 : ¬ Nat.Prime 180821402 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821402) (by decide) (by decide)
lemma npc_180821403 : ¬ Nat.Prime 180821403 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821403) (by decide) (by decide)
lemma npc_180821404 : ¬ Nat.Prime 180821404 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821404) (by decide) (by decide)
lemma npc_180821405 : ¬ Nat.Prime 180821405 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821405) (by decide) (by decide)
lemma npc_180821406 : ¬ Nat.Prime 180821406 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821406) (by decide) (by decide)
lemma npc_180821407 : ¬ Nat.Prime 180821407 := Nat.not_prime_of_dvd_of_lt (by decide : 13 ∣ 180821407) (by decide) (by decide)
lemma npc_180821408 : ¬ Nat.Prime 180821408 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821408) (by decide) (by decide)
lemma npc_180821409 : ¬ Nat.Prime 180821409 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821409) (by decide) (by decide)
lemma npc_180821410 : ¬ Nat.Prime 180821410 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821410) (by decide) (by decide)
lemma npc_180821411 : ¬ Nat.Prime 180821411 := Nat.not_prime_of_dvd_of_lt (by decide : 101 ∣ 180821411) (by decide) (by decide)
lemma npc_180821412 : ¬ Nat.Prime 180821412 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821412) (by decide) (by decide)
lemma npc_180821413 : ¬ Nat.Prime 180821413 := Nat.not_prime_of_dvd_of_lt (by decide : 12143 ∣ 180821413) (by decide) (by decide)
lemma npc_180821414 : ¬ Nat.Prime 180821414 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821414) (by decide) (by decide)
lemma npc_180821415 : ¬ Nat.Prime 180821415 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821415) (by decide) (by decide)
lemma npc_180821416 : ¬ Nat.Prime 180821416 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821416) (by decide) (by decide)
lemma npc_180821417 : ¬ Nat.Prime 180821417 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821417) (by decide) (by decide)
lemma npc_180821418 : ¬ Nat.Prime 180821418 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821418) (by decide) (by decide)
lemma npc_180821419 : ¬ Nat.Prime 180821419 := Nat.not_prime_of_dvd_of_lt (by decide : 31 ∣ 180821419) (by decide) (by decide)
lemma npc_180821420 : ¬ Nat.Prime 180821420 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821420) (by decide) (by decide)
lemma npc_180821421 : ¬ Nat.Prime 180821421 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821421) (by decide) (by decide)
lemma npc_180821422 : ¬ Nat.Prime 180821422 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821422) (by decide) (by decide)
lemma npc_180821423 : ¬ Nat.Prime 180821423 := Nat.not_prime_of_dvd_of_lt (by decide : 19 ∣ 180821423) (by decide) (by decide)
lemma npc_180821424 : ¬ Nat.Prime 180821424 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821424) (by decide) (by decide)
lemma npc_180821425 : ¬ Nat.Prime 180821425 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821425) (by decide) (by decide)
lemma npc_180821426 : ¬ Nat.Prime 180821426 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821426) (by decide) (by decide)
lemma npc_180821427 : ¬ Nat.Prime 180821427 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821427) (by decide) (by decide)
lemma npc_180821428 : ¬ Nat.Prime 180821428 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821428) (by decide) (by decide)
lemma npc_180821430 : ¬ Nat.Prime 180821430 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821430) (by decide) (by decide)
lemma npc_180821431 : ¬ Nat.Prime 180821431 := Nat.not_prime_of_dvd_of_lt (by decide : 7 ∣ 180821431) (by decide) (by decide)
lemma npc_180821432 : ¬ Nat.Prime 180821432 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821432) (by decide) (by decide)
lemma npc_180821433 : ¬ Nat.Prime 180821433 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821433) (by decide) (by decide)
lemma npc_180821434 : ¬ Nat.Prime 180821434 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821434) (by decide) (by decide)
lemma npc_180821435 : ¬ Nat.Prime 180821435 := Nat.not_prime_of_dvd_of_lt (by decide : 5 ∣ 180821435) (by decide) (by decide)
lemma npc_180821436 : ¬ Nat.Prime 180821436 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821436) (by decide) (by decide)
lemma npc_180821437 : ¬ Nat.Prime 180821437 := Nat.not_prime_of_dvd_of_lt (by decide : 349 ∣ 180821437) (by decide) (by decide)
lemma npc_180821438 : ¬ Nat.Prime 180821438 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821438) (by decide) (by decide)
lemma npc_180821439 : ¬ Nat.Prime 180821439 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821439) (by decide) (by decide)
lemma npc_180821440 : ¬ Nat.Prime 180821440 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821440) (by decide) (by decide)
lemma npc_180821441 : ¬ Nat.Prime 180821441 := Nat.not_prime_of_dvd_of_lt (by decide : 79 ∣ 180821441) (by decide) (by decide)
lemma npc_180821442 : ¬ Nat.Prime 180821442 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821442) (by decide) (by decide)
lemma npc_180821443 : ¬ Nat.Prime 180821443 := Nat.not_prime_of_dvd_of_lt (by decide : 11 ∣ 180821443) (by decide) (by decide)
lemma npc_180821444 : ¬ Nat.Prime 180821444 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821444) (by decide) (by decide)
lemma npc_180821445 : ¬ Nat.Prime 180821445 := Nat.not_prime_of_dvd_of_lt (by decide : 3 ∣ 180821445) (by decide) (by decide)
lemma npc_180821446 : ¬ Nat.Prime 180821446 := Nat.not_prime_of_dvd_of_lt (by decide : 2 ∣ 180821446) (by decide) (by decide)

lemma count_relation_0 : count Nat.Prime 180820951 = 10073435 := base_count

lemma count_relation_1 : count Nat.Prime 180820987 = 10073435 + 1 := by
  rw [count_succ_eq_count npc_180820986]
  rw [count_succ_eq_count npc_180820985]
  rw [count_succ_eq_count npc_180820984]
  rw [count_succ_eq_count npc_180820983]
  rw [count_succ_eq_count npc_180820982]
  rw [count_succ_eq_count npc_180820981]
  rw [count_succ_eq_count npc_180820980]
  rw [count_succ_eq_count npc_180820979]
  rw [count_succ_eq_count npc_180820978]
  rw [count_succ_eq_count npc_180820977]
  rw [count_succ_eq_count npc_180820976]
  rw [count_succ_eq_count npc_180820975]
  rw [count_succ_eq_count npc_180820974]
  rw [count_succ_eq_count npc_180820973]
  rw [count_succ_eq_count npc_180820972]
  rw [count_succ_eq_count npc_180820971]
  rw [count_succ_eq_count npc_180820970]
  rw [count_succ_eq_count npc_180820969]
  rw [count_succ_eq_count npc_180820968]
  rw [count_succ_eq_count npc_180820967]
  rw [count_succ_eq_count npc_180820966]
  rw [count_succ_eq_count npc_180820965]
  rw [count_succ_eq_count npc_180820964]
  rw [count_succ_eq_count npc_180820963]
  rw [count_succ_eq_count npc_180820962]
  rw [count_succ_eq_count npc_180820961]
  rw [count_succ_eq_count npc_180820960]
  rw [count_succ_eq_count npc_180820959]
  rw [count_succ_eq_count npc_180820958]
  rw [count_succ_eq_count npc_180820957]
  rw [count_succ_eq_count npc_180820956]
  rw [count_succ_eq_count npc_180820955]
  rw [count_succ_eq_count npc_180820954]
  rw [count_succ_eq_count npc_180820953]
  rw [count_succ_eq_count npc_180820952]
  rw [count_succ_eq_succ_count prime_180820951]
  rw [count_relation_0]

lemma count_relation_2 : count Nat.Prime 180821023 = 10073435 + 2 := by
  rw [count_succ_eq_count npc_180821022]
  rw [count_succ_eq_count npc_180821021]
  rw [count_succ_eq_count npc_180821020]
  rw [count_succ_eq_count npc_180821019]
  rw [count_succ_eq_count npc_180821018]
  rw [count_succ_eq_count npc_180821017]
  rw [count_succ_eq_count npc_180821016]
  rw [count_succ_eq_count npc_180821015]
  rw [count_succ_eq_count npc_180821014]
  rw [count_succ_eq_count npc_180821013]
  rw [count_succ_eq_count npc_180821012]
  rw [count_succ_eq_count npc_180821011]
  rw [count_succ_eq_count npc_180821010]
  rw [count_succ_eq_count npc_180821009]
  rw [count_succ_eq_count npc_180821008]
  rw [count_succ_eq_count npc_180821007]
  rw [count_succ_eq_count npc_180821006]
  rw [count_succ_eq_count npc_180821005]
  rw [count_succ_eq_count npc_180821004]
  rw [count_succ_eq_count npc_180821003]
  rw [count_succ_eq_count npc_180821002]
  rw [count_succ_eq_count npc_180821001]
  rw [count_succ_eq_count npc_180821000]
  rw [count_succ_eq_count npc_180820999]
  rw [count_succ_eq_count npc_180820998]
  rw [count_succ_eq_count npc_180820997]
  rw [count_succ_eq_count npc_180820996]
  rw [count_succ_eq_count npc_180820995]
  rw [count_succ_eq_count npc_180820994]
  rw [count_succ_eq_count npc_180820993]
  rw [count_succ_eq_count npc_180820992]
  rw [count_succ_eq_count npc_180820991]
  rw [count_succ_eq_count npc_180820990]
  rw [count_succ_eq_count npc_180820989]
  rw [count_succ_eq_count npc_180820988]
  rw [count_succ_eq_succ_count prime_180820987]
  rw [count_relation_1]

lemma count_relation_3 : count Nat.Prime 180821041 = 10073435 + 3 := by
  rw [count_succ_eq_count npc_180821040]
  rw [count_succ_eq_count npc_180821039]
  rw [count_succ_eq_count npc_180821038]
  rw [count_succ_eq_count npc_180821037]
  rw [count_succ_eq_count npc_180821036]
  rw [count_succ_eq_count npc_180821035]
  rw [count_succ_eq_count npc_180821034]
  rw [count_succ_eq_count npc_180821033]
  rw [count_succ_eq_count npc_180821032]
  rw [count_succ_eq_count npc_180821031]
  rw [count_succ_eq_count npc_180821030]
  rw [count_succ_eq_count npc_180821029]
  rw [count_succ_eq_count npc_180821028]
  rw [count_succ_eq_count npc_180821027]
  rw [count_succ_eq_count npc_180821026]
  rw [count_succ_eq_count npc_180821025]
  rw [count_succ_eq_count npc_180821024]
  rw [count_succ_eq_succ_count prime_180821023]
  rw [count_relation_2]

lemma count_relation_4 : count Nat.Prime 180821059 = 10073435 + 4 := by
  rw [count_succ_eq_count npc_180821058]
  rw [count_succ_eq_count npc_180821057]
  rw [count_succ_eq_count npc_180821056]
  rw [count_succ_eq_count npc_180821055]
  rw [count_succ_eq_count npc_180821054]
  rw [count_succ_eq_count npc_180821053]
  rw [count_succ_eq_count npc_180821052]
  rw [count_succ_eq_count npc_180821051]
  rw [count_succ_eq_count npc_180821050]
  rw [count_succ_eq_count npc_180821049]
  rw [count_succ_eq_count npc_180821048]
  rw [count_succ_eq_count npc_180821047]
  rw [count_succ_eq_count npc_180821046]
  rw [count_succ_eq_count npc_180821045]
  rw [count_succ_eq_count npc_180821044]
  rw [count_succ_eq_count npc_180821043]
  rw [count_succ_eq_count npc_180821042]
  rw [count_succ_eq_succ_count prime_180821041]
  rw [count_relation_3]

lemma count_relation_5 : count Nat.Prime 180821093 = 10073435 + 5 := by
  rw [count_succ_eq_count npc_180821092]
  rw [count_succ_eq_count npc_180821091]
  rw [count_succ_eq_count npc_180821090]
  rw [count_succ_eq_count npc_180821089]
  rw [count_succ_eq_count npc_180821088]
  rw [count_succ_eq_count npc_180821087]
  rw [count_succ_eq_count npc_180821086]
  rw [count_succ_eq_count npc_180821085]
  rw [count_succ_eq_count npc_180821084]
  rw [count_succ_eq_count npc_180821083]
  rw [count_succ_eq_count npc_180821082]
  rw [count_succ_eq_count npc_180821081]
  rw [count_succ_eq_count npc_180821080]
  rw [count_succ_eq_count npc_180821079]
  rw [count_succ_eq_count npc_180821078]
  rw [count_succ_eq_count npc_180821077]
  rw [count_succ_eq_count npc_180821076]
  rw [count_succ_eq_count npc_180821075]
  rw [count_succ_eq_count npc_180821074]
  rw [count_succ_eq_count npc_180821073]
  rw [count_succ_eq_count npc_180821072]
  rw [count_succ_eq_count npc_180821071]
  rw [count_succ_eq_count npc_180821070]
  rw [count_succ_eq_count npc_180821069]
  rw [count_succ_eq_count npc_180821068]
  rw [count_succ_eq_count npc_180821067]
  rw [count_succ_eq_count npc_180821066]
  rw [count_succ_eq_count npc_180821065]
  rw [count_succ_eq_count npc_180821064]
  rw [count_succ_eq_count npc_180821063]
  rw [count_succ_eq_count npc_180821062]
  rw [count_succ_eq_count npc_180821061]
  rw [count_succ_eq_count npc_180821060]
  rw [count_succ_eq_succ_count prime_180821059]
  rw [count_relation_4]

lemma count_relation_6 : count Nat.Prime 180821117 = 10073435 + 6 := by
  rw [count_succ_eq_count npc_180821116]
  rw [count_succ_eq_count npc_180821115]
  rw [count_succ_eq_count npc_180821114]
  rw [count_succ_eq_count npc_180821113]
  rw [count_succ_eq_count npc_180821112]
  rw [count_succ_eq_count npc_180821111]
  rw [count_succ_eq_count npc_180821110]
  rw [count_succ_eq_count npc_180821109]
  rw [count_succ_eq_count npc_180821108]
  rw [count_succ_eq_count npc_180821107]
  rw [count_succ_eq_count npc_180821106]
  rw [count_succ_eq_count npc_180821105]
  rw [count_succ_eq_count npc_180821104]
  rw [count_succ_eq_count npc_180821103]
  rw [count_succ_eq_count npc_180821102]
  rw [count_succ_eq_count npc_180821101]
  rw [count_succ_eq_count npc_180821100]
  rw [count_succ_eq_count npc_180821099]
  rw [count_succ_eq_count npc_180821098]
  rw [count_succ_eq_count npc_180821097]
  rw [count_succ_eq_count npc_180821096]
  rw [count_succ_eq_count npc_180821095]
  rw [count_succ_eq_count npc_180821094]
  rw [count_succ_eq_succ_count prime_180821093]
  rw [count_relation_5]

lemma count_relation_7 : count Nat.Prime 180821143 = 10073435 + 7 := by
  rw [count_succ_eq_count npc_180821142]
  rw [count_succ_eq_count npc_180821141]
  rw [count_succ_eq_count npc_180821140]
  rw [count_succ_eq_count npc_180821139]
  rw [count_succ_eq_count npc_180821138]
  rw [count_succ_eq_count npc_180821137]
  rw [count_succ_eq_count npc_180821136]
  rw [count_succ_eq_count npc_180821135]
  rw [count_succ_eq_count npc_180821134]
  rw [count_succ_eq_count npc_180821133]
  rw [count_succ_eq_count npc_180821132]
  rw [count_succ_eq_count npc_180821131]
  rw [count_succ_eq_count npc_180821130]
  rw [count_succ_eq_count npc_180821129]
  rw [count_succ_eq_count npc_180821128]
  rw [count_succ_eq_count npc_180821127]
  rw [count_succ_eq_count npc_180821126]
  rw [count_succ_eq_count npc_180821125]
  rw [count_succ_eq_count npc_180821124]
  rw [count_succ_eq_count npc_180821123]
  rw [count_succ_eq_count npc_180821122]
  rw [count_succ_eq_count npc_180821121]
  rw [count_succ_eq_count npc_180821120]
  rw [count_succ_eq_count npc_180821119]
  rw [count_succ_eq_count npc_180821118]
  rw [count_succ_eq_succ_count prime_180821117]
  rw [count_relation_6]

lemma count_relation_8 : count Nat.Prime 180821161 = 10073435 + 8 := by
  rw [count_succ_eq_count npc_180821160]
  rw [count_succ_eq_count npc_180821159]
  rw [count_succ_eq_count npc_180821158]
  rw [count_succ_eq_count npc_180821157]
  rw [count_succ_eq_count npc_180821156]
  rw [count_succ_eq_count npc_180821155]
  rw [count_succ_eq_count npc_180821154]
  rw [count_succ_eq_count npc_180821153]
  rw [count_succ_eq_count npc_180821152]
  rw [count_succ_eq_count npc_180821151]
  rw [count_succ_eq_count npc_180821150]
  rw [count_succ_eq_count npc_180821149]
  rw [count_succ_eq_count npc_180821148]
  rw [count_succ_eq_count npc_180821147]
  rw [count_succ_eq_count npc_180821146]
  rw [count_succ_eq_count npc_180821145]
  rw [count_succ_eq_count npc_180821144]
  rw [count_succ_eq_succ_count prime_180821143]
  rw [count_relation_7]

lemma count_relation_9 : count Nat.Prime 180821189 = 10073435 + 9 := by
  rw [count_succ_eq_count npc_180821188]
  rw [count_succ_eq_count npc_180821187]
  rw [count_succ_eq_count npc_180821186]
  rw [count_succ_eq_count npc_180821185]
  rw [count_succ_eq_count npc_180821184]
  rw [count_succ_eq_count npc_180821183]
  rw [count_succ_eq_count npc_180821182]
  rw [count_succ_eq_count npc_180821181]
  rw [count_succ_eq_count npc_180821180]
  rw [count_succ_eq_count npc_180821179]
  rw [count_succ_eq_count npc_180821178]
  rw [count_succ_eq_count npc_180821177]
  rw [count_succ_eq_count npc_180821176]
  rw [count_succ_eq_count npc_180821175]
  rw [count_succ_eq_count npc_180821174]
  rw [count_succ_eq_count npc_180821173]
  rw [count_succ_eq_count npc_180821172]
  rw [count_succ_eq_count npc_180821171]
  rw [count_succ_eq_count npc_180821170]
  rw [count_succ_eq_count npc_180821169]
  rw [count_succ_eq_count npc_180821168]
  rw [count_succ_eq_count npc_180821167]
  rw [count_succ_eq_count npc_180821166]
  rw [count_succ_eq_count npc_180821165]
  rw [count_succ_eq_count npc_180821164]
  rw [count_succ_eq_count npc_180821163]
  rw [count_succ_eq_count npc_180821162]
  rw [count_succ_eq_succ_count prime_180821161]
  rw [count_relation_8]

lemma count_relation_10 : count Nat.Prime 180821237 = 10073435 + 10 := by
  rw [count_succ_eq_count npc_180821236]
  rw [count_succ_eq_count npc_180821235]
  rw [count_succ_eq_count npc_180821234]
  rw [count_succ_eq_count npc_180821233]
  rw [count_succ_eq_count npc_180821232]
  rw [count_succ_eq_count npc_180821231]
  rw [count_succ_eq_count npc_180821230]
  rw [count_succ_eq_count npc_180821229]
  rw [count_succ_eq_count npc_180821228]
  rw [count_succ_eq_count npc_180821227]
  rw [count_succ_eq_count npc_180821226]
  rw [count_succ_eq_count npc_180821225]
  rw [count_succ_eq_count npc_180821224]
  rw [count_succ_eq_count npc_180821223]
  rw [count_succ_eq_count npc_180821222]
  rw [count_succ_eq_count npc_180821221]
  rw [count_succ_eq_count npc_180821220]
  rw [count_succ_eq_count npc_180821219]
  rw [count_succ_eq_count npc_180821218]
  rw [count_succ_eq_count npc_180821217]
  rw [count_succ_eq_count npc_180821216]
  rw [count_succ_eq_count npc_180821215]
  rw [count_succ_eq_count npc_180821214]
  rw [count_succ_eq_count npc_180821213]
  rw [count_succ_eq_count npc_180821212]
  rw [count_succ_eq_count npc_180821211]
  rw [count_succ_eq_count npc_180821210]
  rw [count_succ_eq_count npc_180821209]
  rw [count_succ_eq_count npc_180821208]
  rw [count_succ_eq_count npc_180821207]
  rw [count_succ_eq_count npc_180821206]
  rw [count_succ_eq_count npc_180821205]
  rw [count_succ_eq_count npc_180821204]
  rw [count_succ_eq_count npc_180821203]
  rw [count_succ_eq_count npc_180821202]
  rw [count_succ_eq_count npc_180821201]
  rw [count_succ_eq_count npc_180821200]
  rw [count_succ_eq_count npc_180821199]
  rw [count_succ_eq_count npc_180821198]
  rw [count_succ_eq_count npc_180821197]
  rw [count_succ_eq_count npc_180821196]
  rw [count_succ_eq_count npc_180821195]
  rw [count_succ_eq_count npc_180821194]
  rw [count_succ_eq_count npc_180821193]
  rw [count_succ_eq_count npc_180821192]
  rw [count_succ_eq_count npc_180821191]
  rw [count_succ_eq_count npc_180821190]
  rw [count_succ_eq_succ_count prime_180821189]
  rw [count_relation_9]

lemma count_relation_11 : count Nat.Prime 180821261 = 10073435 + 11 := by
  rw [count_succ_eq_count npc_180821260]
  rw [count_succ_eq_count npc_180821259]
  rw [count_succ_eq_count npc_180821258]
  rw [count_succ_eq_count npc_180821257]
  rw [count_succ_eq_count npc_180821256]
  rw [count_succ_eq_count npc_180821255]
  rw [count_succ_eq_count npc_180821254]
  rw [count_succ_eq_count npc_180821253]
  rw [count_succ_eq_count npc_180821252]
  rw [count_succ_eq_count npc_180821251]
  rw [count_succ_eq_count npc_180821250]
  rw [count_succ_eq_count npc_180821249]
  rw [count_succ_eq_count npc_180821248]
  rw [count_succ_eq_count npc_180821247]
  rw [count_succ_eq_count npc_180821246]
  rw [count_succ_eq_count npc_180821245]
  rw [count_succ_eq_count npc_180821244]
  rw [count_succ_eq_count npc_180821243]
  rw [count_succ_eq_count npc_180821242]
  rw [count_succ_eq_count npc_180821241]
  rw [count_succ_eq_count npc_180821240]
  rw [count_succ_eq_count npc_180821239]
  rw [count_succ_eq_count npc_180821238]
  rw [count_succ_eq_succ_count prime_180821237]
  rw [count_relation_10]

lemma count_relation_12 : count Nat.Prime 180821287 = 10073435 + 12 := by
  rw [count_succ_eq_count npc_180821286]
  rw [count_succ_eq_count npc_180821285]
  rw [count_succ_eq_count npc_180821284]
  rw [count_succ_eq_count npc_180821283]
  rw [count_succ_eq_count npc_180821282]
  rw [count_succ_eq_count npc_180821281]
  rw [count_succ_eq_count npc_180821280]
  rw [count_succ_eq_count npc_180821279]
  rw [count_succ_eq_count npc_180821278]
  rw [count_succ_eq_count npc_180821277]
  rw [count_succ_eq_count npc_180821276]
  rw [count_succ_eq_count npc_180821275]
  rw [count_succ_eq_count npc_180821274]
  rw [count_succ_eq_count npc_180821273]
  rw [count_succ_eq_count npc_180821272]
  rw [count_succ_eq_count npc_180821271]
  rw [count_succ_eq_count npc_180821270]
  rw [count_succ_eq_count npc_180821269]
  rw [count_succ_eq_count npc_180821268]
  rw [count_succ_eq_count npc_180821267]
  rw [count_succ_eq_count npc_180821266]
  rw [count_succ_eq_count npc_180821265]
  rw [count_succ_eq_count npc_180821264]
  rw [count_succ_eq_count npc_180821263]
  rw [count_succ_eq_count npc_180821262]
  rw [count_succ_eq_succ_count prime_180821261]
  rw [count_relation_11]

lemma count_relation_13 : count Nat.Prime 180821317 = 10073435 + 13 := by
  rw [count_succ_eq_count npc_180821316]
  rw [count_succ_eq_count npc_180821315]
  rw [count_succ_eq_count npc_180821314]
  rw [count_succ_eq_count npc_180821313]
  rw [count_succ_eq_count npc_180821312]
  rw [count_succ_eq_count npc_180821311]
  rw [count_succ_eq_count npc_180821310]
  rw [count_succ_eq_count npc_180821309]
  rw [count_succ_eq_count npc_180821308]
  rw [count_succ_eq_count npc_180821307]
  rw [count_succ_eq_count npc_180821306]
  rw [count_succ_eq_count npc_180821305]
  rw [count_succ_eq_count npc_180821304]
  rw [count_succ_eq_count npc_180821303]
  rw [count_succ_eq_count npc_180821302]
  rw [count_succ_eq_count npc_180821301]
  rw [count_succ_eq_count npc_180821300]
  rw [count_succ_eq_count npc_180821299]
  rw [count_succ_eq_count npc_180821298]
  rw [count_succ_eq_count npc_180821297]
  rw [count_succ_eq_count npc_180821296]
  rw [count_succ_eq_count npc_180821295]
  rw [count_succ_eq_count npc_180821294]
  rw [count_succ_eq_count npc_180821293]
  rw [count_succ_eq_count npc_180821292]
  rw [count_succ_eq_count npc_180821291]
  rw [count_succ_eq_count npc_180821290]
  rw [count_succ_eq_count npc_180821289]
  rw [count_succ_eq_count npc_180821288]
  rw [count_succ_eq_succ_count prime_180821287]
  rw [count_relation_12]

lemma count_relation_14 : count Nat.Prime 180821339 = 10073435 + 14 := by
  rw [count_succ_eq_count npc_180821338]
  rw [count_succ_eq_count npc_180821337]
  rw [count_succ_eq_count npc_180821336]
  rw [count_succ_eq_count npc_180821335]
  rw [count_succ_eq_count npc_180821334]
  rw [count_succ_eq_count npc_180821333]
  rw [count_succ_eq_count npc_180821332]
  rw [count_succ_eq_count npc_180821331]
  rw [count_succ_eq_count npc_180821330]
  rw [count_succ_eq_count npc_180821329]
  rw [count_succ_eq_count npc_180821328]
  rw [count_succ_eq_count npc_180821327]
  rw [count_succ_eq_count npc_180821326]
  rw [count_succ_eq_count npc_180821325]
  rw [count_succ_eq_count npc_180821324]
  rw [count_succ_eq_count npc_180821323]
  rw [count_succ_eq_count npc_180821322]
  rw [count_succ_eq_count npc_180821321]
  rw [count_succ_eq_count npc_180821320]
  rw [count_succ_eq_count npc_180821319]
  rw [count_succ_eq_count npc_180821318]
  rw [count_succ_eq_succ_count prime_180821317]
  rw [count_relation_13]

lemma count_relation_15 : count Nat.Prime 180821387 = 10073435 + 15 := by
  rw [count_succ_eq_count npc_180821386]
  rw [count_succ_eq_count npc_180821385]
  rw [count_succ_eq_count npc_180821384]
  rw [count_succ_eq_count npc_180821383]
  rw [count_succ_eq_count npc_180821382]
  rw [count_succ_eq_count npc_180821381]
  rw [count_succ_eq_count npc_180821380]
  rw [count_succ_eq_count npc_180821379]
  rw [count_succ_eq_count npc_180821378]
  rw [count_succ_eq_count npc_180821377]
  rw [count_succ_eq_count npc_180821376]
  rw [count_succ_eq_count npc_180821375]
  rw [count_succ_eq_count npc_180821374]
  rw [count_succ_eq_count npc_180821373]
  rw [count_succ_eq_count npc_180821372]
  rw [count_succ_eq_count npc_180821371]
  rw [count_succ_eq_count npc_180821370]
  rw [count_succ_eq_count npc_180821369]
  rw [count_succ_eq_count npc_180821368]
  rw [count_succ_eq_count npc_180821367]
  rw [count_succ_eq_count npc_180821366]
  rw [count_succ_eq_count npc_180821365]
  rw [count_succ_eq_count npc_180821364]
  rw [count_succ_eq_count npc_180821363]
  rw [count_succ_eq_count npc_180821362]
  rw [count_succ_eq_count npc_180821361]
  rw [count_succ_eq_count npc_180821360]
  rw [count_succ_eq_count npc_180821359]
  rw [count_succ_eq_count npc_180821358]
  rw [count_succ_eq_count npc_180821357]
  rw [count_succ_eq_count npc_180821356]
  rw [count_succ_eq_count npc_180821355]
  rw [count_succ_eq_count npc_180821354]
  rw [count_succ_eq_count npc_180821353]
  rw [count_succ_eq_count npc_180821352]
  rw [count_succ_eq_count npc_180821351]
  rw [count_succ_eq_count npc_180821350]
  rw [count_succ_eq_count npc_180821349]
  rw [count_succ_eq_count npc_180821348]
  rw [count_succ_eq_count npc_180821347]
  rw [count_succ_eq_count npc_180821346]
  rw [count_succ_eq_count npc_180821345]
  rw [count_succ_eq_count npc_180821344]
  rw [count_succ_eq_count npc_180821343]
  rw [count_succ_eq_count npc_180821342]
  rw [count_succ_eq_count npc_180821341]
  rw [count_succ_eq_count npc_180821340]
  rw [count_succ_eq_succ_count prime_180821339]
  rw [count_relation_14]

lemma count_relation_16 : count Nat.Prime 180821429 = 10073435 + 16 := by
  rw [count_succ_eq_count npc_180821428]
  rw [count_succ_eq_count npc_180821427]
  rw [count_succ_eq_count npc_180821426]
  rw [count_succ_eq_count npc_180821425]
  rw [count_succ_eq_count npc_180821424]
  rw [count_succ_eq_count npc_180821423]
  rw [count_succ_eq_count npc_180821422]
  rw [count_succ_eq_count npc_180821421]
  rw [count_succ_eq_count npc_180821420]
  rw [count_succ_eq_count npc_180821419]
  rw [count_succ_eq_count npc_180821418]
  rw [count_succ_eq_count npc_180821417]
  rw [count_succ_eq_count npc_180821416]
  rw [count_succ_eq_count npc_180821415]
  rw [count_succ_eq_count npc_180821414]
  rw [count_succ_eq_count npc_180821413]
  rw [count_succ_eq_count npc_180821412]
  rw [count_succ_eq_count npc_180821411]
  rw [count_succ_eq_count npc_180821410]
  rw [count_succ_eq_count npc_180821409]
  rw [count_succ_eq_count npc_180821408]
  rw [count_succ_eq_count npc_180821407]
  rw [count_succ_eq_count npc_180821406]
  rw [count_succ_eq_count npc_180821405]
  rw [count_succ_eq_count npc_180821404]
  rw [count_succ_eq_count npc_180821403]
  rw [count_succ_eq_count npc_180821402]
  rw [count_succ_eq_count npc_180821401]
  rw [count_succ_eq_count npc_180821400]
  rw [count_succ_eq_count npc_180821399]
  rw [count_succ_eq_count npc_180821398]
  rw [count_succ_eq_count npc_180821397]
  rw [count_succ_eq_count npc_180821396]
  rw [count_succ_eq_count npc_180821395]
  rw [count_succ_eq_count npc_180821394]
  rw [count_succ_eq_count npc_180821393]
  rw [count_succ_eq_count npc_180821392]
  rw [count_succ_eq_count npc_180821391]
  rw [count_succ_eq_count npc_180821390]
  rw [count_succ_eq_count npc_180821389]
  rw [count_succ_eq_count npc_180821388]
  rw [count_succ_eq_succ_count prime_180821387]
  rw [count_relation_15]

lemma count_relation_17 : count Nat.Prime 180821447 = 10073435 + 17 := by
  rw [count_succ_eq_count npc_180821446]
  rw [count_succ_eq_count npc_180821445]
  rw [count_succ_eq_count npc_180821444]
  rw [count_succ_eq_count npc_180821443]
  rw [count_succ_eq_count npc_180821442]
  rw [count_succ_eq_count npc_180821441]
  rw [count_succ_eq_count npc_180821440]
  rw [count_succ_eq_count npc_180821439]
  rw [count_succ_eq_count npc_180821438]
  rw [count_succ_eq_count npc_180821437]
  rw [count_succ_eq_count npc_180821436]
  rw [count_succ_eq_count npc_180821435]
  rw [count_succ_eq_count npc_180821434]
  rw [count_succ_eq_count npc_180821433]
  rw [count_succ_eq_count npc_180821432]
  rw [count_succ_eq_count npc_180821431]
  rw [count_succ_eq_count npc_180821430]
  rw [count_succ_eq_succ_count prime_180821429]
  rw [count_relation_16]

lemma nth_prime_step_0 : Nat.nth Nat.Prime (N - 1 + 0) = 180820951 := by
  have h_eq : N - 1 + 0 = count Nat.Prime 180820951 := by
    unfold N
    rw [count_relation_0]
  rw [h_eq]
  exact Nat.nth_count prime_180820951

lemma nth_prime_step_0_next : Nat.nth Nat.Prime (N + 0) = 180820987 := by
  have h_eq : N + 0 = count Nat.Prime 180820987 := by
    unfold N
    rw [count_relation_1]
  rw [h_eq]
  exact Nat.nth_count prime_180820987

lemma nth_prime_step_1 : Nat.nth Nat.Prime (N - 1 + 1) = 180820987 := by
  have h_eq : N - 1 + 1 = count Nat.Prime 180820987 := by
    unfold N
    rw [count_relation_1]
  rw [h_eq]
  exact Nat.nth_count prime_180820987

lemma nth_prime_step_1_next : Nat.nth Nat.Prime (N + 1) = 180821023 := by
  have h_eq : N + 1 = count Nat.Prime 180821023 := by
    unfold N
    rw [count_relation_2]
  rw [h_eq]
  exact Nat.nth_count prime_180821023

lemma nth_prime_step_2 : Nat.nth Nat.Prime (N - 1 + 2) = 180821023 := by
  have h_eq : N - 1 + 2 = count Nat.Prime 180821023 := by
    unfold N
    rw [count_relation_2]
  rw [h_eq]
  exact Nat.nth_count prime_180821023

lemma nth_prime_step_2_next : Nat.nth Nat.Prime (N + 2) = 180821041 := by
  have h_eq : N + 2 = count Nat.Prime 180821041 := by
    unfold N
    rw [count_relation_3]
  rw [h_eq]
  exact Nat.nth_count prime_180821041

lemma nth_prime_step_3 : Nat.nth Nat.Prime (N - 1 + 3) = 180821041 := by
  have h_eq : N - 1 + 3 = count Nat.Prime 180821041 := by
    unfold N
    rw [count_relation_3]
  rw [h_eq]
  exact Nat.nth_count prime_180821041

lemma nth_prime_step_3_next : Nat.nth Nat.Prime (N + 3) = 180821059 := by
  have h_eq : N + 3 = count Nat.Prime 180821059 := by
    unfold N
    rw [count_relation_4]
  rw [h_eq]
  exact Nat.nth_count prime_180821059

lemma nth_prime_step_4 : Nat.nth Nat.Prime (N - 1 + 4) = 180821059 := by
  have h_eq : N - 1 + 4 = count Nat.Prime 180821059 := by
    unfold N
    rw [count_relation_4]
  rw [h_eq]
  exact Nat.nth_count prime_180821059

lemma nth_prime_step_4_next : Nat.nth Nat.Prime (N + 4) = 180821093 := by
  have h_eq : N + 4 = count Nat.Prime 180821093 := by
    unfold N
    rw [count_relation_5]
  rw [h_eq]
  exact Nat.nth_count prime_180821093

lemma nth_prime_step_5 : Nat.nth Nat.Prime (N - 1 + 5) = 180821093 := by
  have h_eq : N - 1 + 5 = count Nat.Prime 180821093 := by
    unfold N
    rw [count_relation_5]
  rw [h_eq]
  exact Nat.nth_count prime_180821093

lemma nth_prime_step_5_next : Nat.nth Nat.Prime (N + 5) = 180821117 := by
  have h_eq : N + 5 = count Nat.Prime 180821117 := by
    unfold N
    rw [count_relation_6]
  rw [h_eq]
  exact Nat.nth_count prime_180821117

lemma nth_prime_step_6 : Nat.nth Nat.Prime (N - 1 + 6) = 180821117 := by
  have h_eq : N - 1 + 6 = count Nat.Prime 180821117 := by
    unfold N
    rw [count_relation_6]
  rw [h_eq]
  exact Nat.nth_count prime_180821117

lemma nth_prime_step_6_next : Nat.nth Nat.Prime (N + 6) = 180821143 := by
  have h_eq : N + 6 = count Nat.Prime 180821143 := by
    unfold N
    rw [count_relation_7]
  rw [h_eq]
  exact Nat.nth_count prime_180821143

lemma nth_prime_step_7 : Nat.nth Nat.Prime (N - 1 + 7) = 180821143 := by
  have h_eq : N - 1 + 7 = count Nat.Prime 180821143 := by
    unfold N
    rw [count_relation_7]
  rw [h_eq]
  exact Nat.nth_count prime_180821143

lemma nth_prime_step_7_next : Nat.nth Nat.Prime (N + 7) = 180821161 := by
  have h_eq : N + 7 = count Nat.Prime 180821161 := by
    unfold N
    rw [count_relation_8]
  rw [h_eq]
  exact Nat.nth_count prime_180821161

lemma nth_prime_step_8 : Nat.nth Nat.Prime (N - 1 + 8) = 180821161 := by
  have h_eq : N - 1 + 8 = count Nat.Prime 180821161 := by
    unfold N
    rw [count_relation_8]
  rw [h_eq]
  exact Nat.nth_count prime_180821161

lemma nth_prime_step_8_next : Nat.nth Nat.Prime (N + 8) = 180821189 := by
  have h_eq : N + 8 = count Nat.Prime 180821189 := by
    unfold N
    rw [count_relation_9]
  rw [h_eq]
  exact Nat.nth_count prime_180821189

lemma nth_prime_step_9 : Nat.nth Nat.Prime (N - 1 + 9) = 180821189 := by
  have h_eq : N - 1 + 9 = count Nat.Prime 180821189 := by
    unfold N
    rw [count_relation_9]
  rw [h_eq]
  exact Nat.nth_count prime_180821189

lemma nth_prime_step_9_next : Nat.nth Nat.Prime (N + 9) = 180821237 := by
  have h_eq : N + 9 = count Nat.Prime 180821237 := by
    unfold N
    rw [count_relation_10]
  rw [h_eq]
  exact Nat.nth_count prime_180821237

lemma nth_prime_step_10 : Nat.nth Nat.Prime (N - 1 + 10) = 180821237 := by
  have h_eq : N - 1 + 10 = count Nat.Prime 180821237 := by
    unfold N
    rw [count_relation_10]
  rw [h_eq]
  exact Nat.nth_count prime_180821237

lemma nth_prime_step_10_next : Nat.nth Nat.Prime (N + 10) = 180821261 := by
  have h_eq : N + 10 = count Nat.Prime 180821261 := by
    unfold N
    rw [count_relation_11]
  rw [h_eq]
  exact Nat.nth_count prime_180821261

lemma nth_prime_step_11 : Nat.nth Nat.Prime (N - 1 + 11) = 180821261 := by
  have h_eq : N - 1 + 11 = count Nat.Prime 180821261 := by
    unfold N
    rw [count_relation_11]
  rw [h_eq]
  exact Nat.nth_count prime_180821261

lemma nth_prime_step_11_next : Nat.nth Nat.Prime (N + 11) = 180821287 := by
  have h_eq : N + 11 = count Nat.Prime 180821287 := by
    unfold N
    rw [count_relation_12]
  rw [h_eq]
  exact Nat.nth_count prime_180821287

lemma nth_prime_step_12 : Nat.nth Nat.Prime (N - 1 + 12) = 180821287 := by
  have h_eq : N - 1 + 12 = count Nat.Prime 180821287 := by
    unfold N
    rw [count_relation_12]
  rw [h_eq]
  exact Nat.nth_count prime_180821287

lemma nth_prime_step_12_next : Nat.nth Nat.Prime (N + 12) = 180821317 := by
  have h_eq : N + 12 = count Nat.Prime 180821317 := by
    unfold N
    rw [count_relation_13]
  rw [h_eq]
  exact Nat.nth_count prime_180821317

lemma nth_prime_step_13 : Nat.nth Nat.Prime (N - 1 + 13) = 180821317 := by
  have h_eq : N - 1 + 13 = count Nat.Prime 180821317 := by
    unfold N
    rw [count_relation_13]
  rw [h_eq]
  exact Nat.nth_count prime_180821317

lemma nth_prime_step_13_next : Nat.nth Nat.Prime (N + 13) = 180821339 := by
  have h_eq : N + 13 = count Nat.Prime 180821339 := by
    unfold N
    rw [count_relation_14]
  rw [h_eq]
  exact Nat.nth_count prime_180821339

lemma nth_prime_step_14 : Nat.nth Nat.Prime (N - 1 + 14) = 180821339 := by
  have h_eq : N - 1 + 14 = count Nat.Prime 180821339 := by
    unfold N
    rw [count_relation_14]
  rw [h_eq]
  exact Nat.nth_count prime_180821339

lemma nth_prime_step_14_next : Nat.nth Nat.Prime (N + 14) = 180821387 := by
  have h_eq : N + 14 = count Nat.Prime 180821387 := by
    unfold N
    rw [count_relation_15]
  rw [h_eq]
  exact Nat.nth_count prime_180821387

lemma nth_prime_step_15 : Nat.nth Nat.Prime (N - 1 + 15) = 180821387 := by
  have h_eq : N - 1 + 15 = count Nat.Prime 180821387 := by
    unfold N
    rw [count_relation_15]
  rw [h_eq]
  exact Nat.nth_count prime_180821387

lemma nth_prime_step_15_next : Nat.nth Nat.Prime (N + 15) = 180821429 := by
  have h_eq : N + 15 = count Nat.Prime 180821429 := by
    unfold N
    rw [count_relation_16]
  rw [h_eq]
  exact Nat.nth_count prime_180821429

lemma nth_prime_step_16 : Nat.nth Nat.Prime (N - 1 + 16) = 180821429 := by
  have h_eq : N - 1 + 16 = count Nat.Prime 180821429 := by
    unfold N
    rw [count_relation_16]
  rw [h_eq]
  exact Nat.nth_count prime_180821429

lemma nth_prime_step_16_next : Nat.nth Nat.Prime (N + 16) = 180821447 := by
  have h_eq : N + 16 = count Nat.Prime 180821447 := by
    unfold N
    rw [count_relation_17]
  rw [h_eq]
  exact Nat.nth_count prime_180821447

lemma nth_prime_step_17 : Nat.nth Nat.Prime (N - 1 + 17) = 180821447 := by
  have h_eq : N - 1 + 17 = count Nat.Prime 180821447 := by
    unfold N
    rw [count_relation_17]
  rw [h_eq]
  exact Nat.nth_count prime_180821447

lemma step_proof_0 : A318199 (N + 0) < A318199 (N + 0 + 1) := by
  apply A318199_step (N + 0) 180820951 180820987
  · unfold N; omega
  · have h_eq : N + 0 - 1 = N - 1 + 0 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_0
  · exact nth_prime_step_0_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_1 : A318199 (N + 1) < A318199 (N + 1 + 1) := by
  apply A318199_step (N + 1) 180820987 180821023
  · unfold N; omega
  · have h_eq : N + 1 - 1 = N - 1 + 1 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_1
  · exact nth_prime_step_1_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_2 : A318199 (N + 2) < A318199 (N + 2 + 1) := by
  apply A318199_step (N + 2) 180821023 180821041
  · unfold N; omega
  · have h_eq : N + 2 - 1 = N - 1 + 2 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_2
  · exact nth_prime_step_2_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_3 : A318199 (N + 3) < A318199 (N + 3 + 1) := by
  apply A318199_step (N + 3) 180821041 180821059
  · unfold N; omega
  · have h_eq : N + 3 - 1 = N - 1 + 3 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_3
  · exact nth_prime_step_3_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_4 : A318199 (N + 4) < A318199 (N + 4 + 1) := by
  apply A318199_step (N + 4) 180821059 180821093
  · unfold N; omega
  · have h_eq : N + 4 - 1 = N - 1 + 4 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_4
  · exact nth_prime_step_4_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_5 : A318199 (N + 5) < A318199 (N + 5 + 1) := by
  apply A318199_step (N + 5) 180821093 180821117
  · unfold N; omega
  · have h_eq : N + 5 - 1 = N - 1 + 5 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_5
  · exact nth_prime_step_5_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_6 : A318199 (N + 6) < A318199 (N + 6 + 1) := by
  apply A318199_step (N + 6) 180821117 180821143
  · unfold N; omega
  · have h_eq : N + 6 - 1 = N - 1 + 6 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_6
  · exact nth_prime_step_6_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_7 : A318199 (N + 7) < A318199 (N + 7 + 1) := by
  apply A318199_step (N + 7) 180821143 180821161
  · unfold N; omega
  · have h_eq : N + 7 - 1 = N - 1 + 7 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_7
  · exact nth_prime_step_7_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_8 : A318199 (N + 8) < A318199 (N + 8 + 1) := by
  apply A318199_step (N + 8) 180821161 180821189
  · unfold N; omega
  · have h_eq : N + 8 - 1 = N - 1 + 8 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_8
  · exact nth_prime_step_8_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_9 : A318199 (N + 9) < A318199 (N + 9 + 1) := by
  apply A318199_step (N + 9) 180821189 180821237
  · unfold N; omega
  · have h_eq : N + 9 - 1 = N - 1 + 9 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_9
  · exact nth_prime_step_9_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_10 : A318199 (N + 10) < A318199 (N + 10 + 1) := by
  apply A318199_step (N + 10) 180821237 180821261
  · unfold N; omega
  · have h_eq : N + 10 - 1 = N - 1 + 10 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_10
  · exact nth_prime_step_10_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_11 : A318199 (N + 11) < A318199 (N + 11 + 1) := by
  apply A318199_step (N + 11) 180821261 180821287
  · unfold N; omega
  · have h_eq : N + 11 - 1 = N - 1 + 11 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_11
  · exact nth_prime_step_11_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_12 : A318199 (N + 12) < A318199 (N + 12 + 1) := by
  apply A318199_step (N + 12) 180821287 180821317
  · unfold N; omega
  · have h_eq : N + 12 - 1 = N - 1 + 12 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_12
  · exact nth_prime_step_12_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_13 : A318199 (N + 13) < A318199 (N + 13 + 1) := by
  apply A318199_step (N + 13) 180821317 180821339
  · unfold N; omega
  · have h_eq : N + 13 - 1 = N - 1 + 13 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_13
  · exact nth_prime_step_13_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_14 : A318199 (N + 14) < A318199 (N + 14 + 1) := by
  apply A318199_step (N + 14) 180821339 180821387
  · unfold N; omega
  · have h_eq : N + 14 - 1 = N - 1 + 14 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_14
  · exact nth_prime_step_14_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_15 : A318199 (N + 15) < A318199 (N + 15 + 1) := by
  apply A318199_step (N + 15) 180821387 180821429
  · unfold N; omega
  · have h_eq : N + 15 - 1 = N - 1 + 15 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_15
  · exact nth_prime_step_15_next
  · unfold N; omega
  · unfold N; decide

lemma step_proof_16 : A318199 (N + 16) < A318199 (N + 16 + 1) := by
  apply A318199_step (N + 16) 180821429 180821447
  · unfold N; omega
  · have h_eq : N + 16 - 1 = N - 1 + 16 := by unfold N; omega
    rw [h_eq]
    exact nth_prime_step_16
  · exact nth_prime_step_16_next
  · unfold N; omega
  · unfold N; decide

set_option linter.unusedVariables false in
theorem oeis_318199_conjecture_0.disproof :
  ¬ ¬ ∃ (N : ℕ) (hN : 0 < N),
    ∀ (i : ℕ), i < 17 → A318199 (N + i) < A318199 (N + i + 1) := by
  intro h
  apply h
  use N
  have hN_pos : 0 < N := by unfold N; omega
  use hN_pos
  intro i hi
  interval_cases i
  · exact step_proof_0
  · exact step_proof_1
  · exact step_proof_2
  · exact step_proof_3
  · exact step_proof_4
  · exact step_proof_5
  · exact step_proof_6
  · exact step_proof_7
  · exact step_proof_8
  · exact step_proof_9
  · exact step_proof_10
  · exact step_proof_11
  · exact step_proof_12
  · exact step_proof_13
  · exact step_proof_14
  · exact step_proof_15
  · exact step_proof_16


#print axioms oeis_318199_conjecture_0.disproof