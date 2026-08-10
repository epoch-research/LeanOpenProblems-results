import FormalConjectures.Util.ProblemImports

set_option maxHeartbeats 0
set_option maxRecDepth 8000

open Finset Nat

noncomputable def a (n : ℕ) : ℕ :=
  let pn : ℕ := Nat.nth Nat.Prime (n - 1)
  Finset.card (Finset.filter (fun k : ℕ => Nat.Prime (k ^ 2 - k + pn)) (Finset.Icc 1 n))

lemma card_filter_lt_card_of_exists_not {α : Type*} (s : Finset α) (p : α → Prop) [DecidablePred p] (x : α) (hx : x ∈ s) (hpx : ¬ p x) :
    Finset.card (Finset.filter p s) < Finset.card s := by
  have hle := Finset.card_filter_le s p
  have hne : Finset.card (Finset.filter p s) ≠ Finset.card s := by
    intro h
    rw [Finset.card_filter_eq_iff] at h
    exact hpx (h x hx)
  exact lt_of_le_of_ne hle hne

lemma test_mod_general (p : ℕ) (d : ℕ) (hd_pos : d ≥ 2) (hd_le : d ≤ 13) (hp : p ≥ 43) (off : ℕ) (h_mod : (p + off) % d = 0) (h_off_pos : off ≥ 2) : ¬ Nat.Prime (p + off) := by
  have hd : d ∣ p + off := Nat.dvd_of_mod_eq_zero h_mod
  have h_lt : d < p + off := by omega
  exact Nat.not_prime_of_dvd_of_lt hd hd_pos h_lt

lemma test_mod_general_large (p : ℕ) (d : ℕ) (hd_pos : d ≥ 2) (hd_le : d ≤ 47) (hp : p ≥ 199) (off : ℕ) (h_mod : (p + off) % d = 0) (h_off_pos : off ≥ 2) : ¬ Nat.Prime (p + off) := by
  have hd : d ∣ p + off := Nat.dvd_of_mod_eq_zero h_mod
  have h_lt : d < p + off := by omega
  exact Nat.not_prime_of_dvd_of_lt hd hd_pos h_lt

lemma not_prime_by_factor (val : ℕ) (d : ℕ) (hd_pos : d ≥ 2) (hd_le : d < val) (h_mod : val % d = 0) : ¬ Nat.Prime val := by
  have hd : d ∣ val := Nat.dvd_of_mod_eq_zero h_mod
  exact Nat.not_prime_of_dvd_of_lt hd hd_pos hd_le

lemma helper_exceptions_g0 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 333491 ∨ p = 601037 ∨ p = 1084997 ∨ p = 1525367 ∨ p = 1960391 ∨ p = 2367767 ∨ p = 2528621 ∨ p = 2533367 ∨ p = 2561681 ∨ p = 2567177 ∨ p = 2925821 ∨ p = 3322337 ∨ p = 3372221 ∨ p = 3558407 ∨ p = 3733397 ∨ p = 3754691 ∨ p = 4253267 ∨ p = 4402787 ∨ p = 4773227 ∨ p = 4876451) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 333491) 359 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 601037) 619 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 1084997) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 1525367) 229 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 1960391) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 2367767) 419 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 2528621) 257 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 2533367) 761 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 2561681) 89 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 2567177) 271 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 2925821) 67 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 3322337) 239 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 3372221) 1117 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 3558407) 127 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 3733397) 179 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 3754691) 71 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 4253267) 419 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 4402787) 163 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 4773227) 53 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 4876451) 233 (by decide) (by decide) (by decide)

lemma helper_exceptions_g1 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 5108561 ∨ p = 5237651 ∨ p = 5240591 ∨ p = 5324441 ∨ p = 5499077 ∨ p = 5570417 ∨ p = 5574971 ∨ p = 5608697 ∨ p = 5840951 ∨ p = 6275177 ∨ p = 6385397 ∨ p = 7325231 ∨ p = 7410497 ∨ p = 7507937 ∨ p = 7527251 ∨ p = 7800827 ∨ p = 8139641 ∨ p = 8395061 ∨ p = 9195731 ∨ p = 9464837) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 5108561) 691 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 5237651) 103 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 5240591) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 5324441) 313 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 5499077) 673 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 5570417) 97 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 5574971) 61 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 5608697) 2027 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 5840951) 71 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 6275177) 1511 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 6385397) 701 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 7325231) 127 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 7410497) 107 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 7507937) 163 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 7527251) 641 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 7800827) 251 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 8139641) 2371 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 8395061) 2621 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 9195731) 439 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 9464837) 59 (by decide) (by decide) (by decide)

lemma helper_exceptions_g2 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 9563621 ∨ p = 9572021 ∨ p = 10058177 ∨ p = 10325657 ∨ p = 10416137 ∨ p = 10661237 ∨ p = 10907021 ∨ p = 10997081 ∨ p = 11420567 ∨ p = 11445647 ∨ p = 11638631 ∨ p = 11691851 ∨ p = 11867897 ∨ p = 11984717 ∨ p = 12362951 ∨ p = 12414287 ∨ p = 12507617 ∨ p = 12935051 ∨ p = 13023737 ∨ p = 13111181) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 9563621) 1997 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 9572021) 349 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 10058177) 139 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 10325657) 607 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 10416137) 53 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 10661237) 101 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 10907021) 787 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 10997081) 2957 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 11420567) 89 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 11445647) 151 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 11638631) 2143 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 11691851) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 11867897) 137 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 11984717) 139 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 12362951) 1399 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 12414287) 1787 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 12507617) 61 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 12935051) 193 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 13023737) 1321 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 13111181) 1699 (by decide) (by decide) (by decide)

lemma helper_exceptions_g3 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 13611041 ∨ p = 13911407 ∨ p = 14396477 ∨ p = 14400767 ∨ p = 14437457 ∨ p = 14549891 ∨ p = 14728157 ∨ p = 14751701 ∨ p = 14812277 ∨ p = 14899721 ∨ p = 14940281 ∨ p = 15062891 ∨ p = 15102077 ∨ p = 15243311 ∨ p = 15346607 ∨ p = 15405317 ∨ p = 15410567 ∨ p = 15708347 ∨ p = 15715517 ∨ p = 15837947) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 13611041) 2957 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 13911407) 223 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 14396477) 131 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 14400767) 1301 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 14437457) 1721 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 14549891) 241 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 14728157) 233 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 14751701) 1259 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 14812277) 977 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 14899721) 199 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 14940281) 181 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 15062891) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 15102077) 859 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 15243311) 109 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 15346607) 163 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 15405317) 577 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 15410567) 2297 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 15708347) 107 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 15715517) 2089 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 15837947) 373 (by decide) (by decide) (by decide)

lemma helper_exceptions_g4 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 16625591 ∨ p = 16773431 ∨ p = 16827647 ∨ p = 17695187 ∨ p = 17912261 ∨ p = 18172391 ∨ p = 19003337 ∨ p = 20217137 ∨ p = 20404817 ∨ p = 20740397 ∨ p = 21277337 ∨ p = 21390491 ∨ p = 21456047 ∨ p = 21522101 ∨ p = 21832751 ∨ p = 21977777 ∨ p = 22072487 ∨ p = 22758077 ∨ p = 23028611 ∨ p = 23362511) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 16625591) 379 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 16773431) 193 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 16827647) 67 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 17695187) 673 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 17912261) 2381 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 18172391) 103 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 19003337) 607 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 20217137) 569 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 20404817) 157 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 20740397) 61 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 21277337) 61 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 21390491) 83 (by decide) (by decide) (by decide)
  · use 9
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (9 ^ 2 - 9 + 21456047) 2089 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 21522101) 229 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 21832751) 181 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 21977777) 109 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 22072487) 337 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 22758077) 79 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 23028611) 3697 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 23362511) 1597 (by decide) (by decide) (by decide)

lemma helper_exceptions_g5 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 23429951 ∨ p = 23594171 ∨ p = 23654231 ∨ p = 23990231 ∨ p = 24004061 ∨ p = 24102977 ∨ p = 24417137 ∨ p = 24519617 ∨ p = 24731381 ∨ p = 24838481 ∨ p = 24868001 ∨ p = 25082567 ∨ p = 25187837 ∨ p = 25684781 ∨ p = 26072171 ∨ p = 26692067 ∨ p = 26769287 ∨ p = 27064547 ∨ p = 27252761 ∨ p = 27441767) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 23429951) 3593 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 23594171) 659 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 23654231) 1031 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 23990231) 353 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 24004061) 439 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 24102977) 79 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 24417137) 2161 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 24519617) 269 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 24731381) 3877 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 24838481) 1879 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 24868001) 2711 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 25082567) 263 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 25187837) 1571 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 25684781) 4871 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 26072171) 193 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 26692067) 113 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 26769287) 53 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 27064547) 733 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 27252761) 359 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 27441767) 1009 (by decide) (by decide) (by decide)

lemma helper_exceptions_g6 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 27543611 ∨ p = 27648347 ∨ p = 27674741 ∨ p = 28377257 ∨ p = 28399487 ∨ p = 28435697 ∨ p = 28537121 ∨ p = 28869011 ∨ p = 29185811 ∨ p = 29282711 ∨ p = 29333387 ∨ p = 29479181 ∨ p = 29570267 ∨ p = 30554201 ∨ p = 30624947 ∨ p = 30671087 ∨ p = 30691937 ∨ p = 30806507 ∨ p = 30825647 ∨ p = 30932411) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 27543611) 1277 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 27648347) 433 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 27674741) 241 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 28377257) 197 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 28399487) 199 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 28435697) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 28537121) 1889 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 28869011) 1031 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 29185811) 233 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 29282711) 139 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 29333387) 131 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 29479181) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 29570267) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 30554201) 1103 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 30624947) 1097 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 30671087) 2671 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 30691937) 1553 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 30806507) 2011 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 30825647) 173 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 30932411) 647 (by decide) (by decide) (by decide)

lemma helper_exceptions_g7 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 30975557 ∨ p = 31102781 ∨ p = 31123637 ∨ p = 31278251 ∨ p = 31316267 ∨ p = 31384007 ∨ p = 31626977 ∨ p = 31965821 ∨ p = 31999271 ∨ p = 32186237 ∨ p = 32188691 ∨ p = 32381807 ∨ p = 32571557 ∨ p = 32940221 ∨ p = 33090371 ∨ p = 33252377 ∨ p = 33502367 ∨ p = 34011821 ∨ p = 34778657 ∨ p = 35077241) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 30975557) 137 (by decide) (by decide) (by decide)
  · use 7
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (7 ^ 2 - 7 + 31102781) 109 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 31123637) 2267 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 31278251) 1283 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 31316267) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 31384007) 673 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 31626977) 739 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 31965821) 4549 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 31999271) 173 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 32186237) 97 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 32188691) 73 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 32381807) 67 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 32571557) 433 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 32940221) 4001 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 33090371) 577 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 33252377) 1549 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 33502367) 83 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 34011821) 83 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 34778657) 5483 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 35077241) 1163 (by decide) (by decide) (by decide)

lemma helper_exceptions_g8 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 35184971 ∨ p = 35347511 ∨ p = 35598581 ∨ p = 35604551 ∨ p = 35831921 ∨ p = 36018107 ∨ p = 36155501 ∨ p = 36256037 ∨ p = 36474827 ∨ p = 36531221 ∨ p = 37631411 ∨ p = 37837841 ∨ p = 37989431 ∨ p = 38250461 ∨ p = 38606957 ∨ p = 38939267 ∨ p = 39965267 ∨ p = 40305761 ∨ p = 41194997 ∨ p = 41219597) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 35184971) 71 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 35347511) 197 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 35598581) 647 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 35604551) 59 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 35831921) 313 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 36018107) 571 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 36155501) 127 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 36256037) 769 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 36474827) 313 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 36531221) 5743 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 37631411) 79 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 37837841) 193 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 37989431) 101 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 38250461) 2237 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 38606957) 5417 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 38939267) 109 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 39965267) 811 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 40305761) 1931 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 41194997) 673 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 41219597) 163 (by decide) (by decide) (by decide)

lemma helper_exceptions_g9 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 42124541 ∨ p = 42521651 ∨ p = 43149257 ∨ p = 43746737 ∨ p = 44028197 ∨ p = 44422991 ∨ p = 44496581 ∨ p = 45154841 ∨ p = 45181307 ∨ p = 45695717 ∨ p = 46036577 ∨ p = 47009507 ∨ p = 47509661 ∨ p = 47876681 ∨ p = 48363167 ∨ p = 48606911 ∨ p = 48891107 ∨ p = 48957341 ∨ p = 49938101 ∨ p = 50227271) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 42124541) 3209 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 42521651) 109 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 43149257) 929 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 43746737) 3109 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 44028197) 97 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 44422991) 97 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 44496581) 197 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 45154841) 1979 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 45181307) 3947 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 45695717) 659 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 46036577) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 47009507) 103 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 47509661) 167 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 47876681) 5569 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 48363167) 199 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 48606911) 179 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 48891107) 103 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 48957341) 137 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 49938101) 139 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 50227271) 577 (by decide) (by decide) (by decide)

lemma helper_exceptions_g10 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 50921021 ∨ p = 51090497 ∨ p = 51256481 ∨ p = 51344387 ∨ p = 51804407 ∨ p = 52119491 ∨ p = 52325081 ∨ p = 52340537 ∨ p = 52412027 ∨ p = 52639877 ∨ p = 52742771 ∨ p = 53487881 ∨ p = 53949167 ∨ p = 54029147 ∨ p = 54758591 ∨ p = 54828197 ∨ p = 54898511 ∨ p = 55040261 ∨ p = 55477517 ∨ p = 55534751) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 50921021) 97 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 51090497) 1777 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 51256481) 109 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 51344387) 331 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 51804407) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 52119491) 181 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 52325081) 71 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 52340537) 4643 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 52412027) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 52639877) 2287 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 52742771) 317 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 53487881) 101 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 53949167) 97 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 54029147) 491 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 54758591) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 54828197) 109 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 54898511) 53 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 55040261) 4951 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 55477517) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 55534751) 59 (by decide) (by decide) (by decide)

lemma helper_exceptions_g11 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 55793951 ∨ p = 55839851 ∨ p = 56188877 ∨ p = 56406431 ∨ p = 56533571 ∨ p = 56719571 ∨ p = 57279767 ∨ p = 57330017 ∨ p = 57345677 ∨ p = 57685151 ∨ p = 57867191 ∨ p = 57966761 ∨ p = 58073837 ∨ p = 58095041 ∨ p = 58388567 ∨ p = 58636967 ∨ p = 58759397 ∨ p = 58803581 ∨ p = 58928687 ∨ p = 59427617) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 9
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (9 ^ 2 - 9 + 55793951) 1949 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 55839851) 3089 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 56188877) 5939 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 56406431) 73 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 56533571) 991 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 56719571) 1433 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 57279767) 2677 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 57330017) 151 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 57345677) 101 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 57685151) 71 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 57867191) 97 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 57966761) 2689 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 58073837) 673 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 58095041) 421 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 58388567) 113 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 58636967) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 58759397) 97 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 58803581) 1511 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 58928687) 79 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 59427617) 811 (by decide) (by decide) (by decide)

lemma helper_exceptions_g12 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 60307757 ∨ p = 60345821 ∨ p = 60425861 ∨ p = 60765071 ∨ p = 60957497 ∨ p = 61187507 ∨ p = 61251887 ∨ p = 62331251 ∨ p = 62423651 ∨ p = 62898191 ∨ p = 62913437 ∨ p = 63211397 ∨ p = 63627491 ∨ p = 64558931 ∨ p = 65510171 ∨ p = 65625731 ∨ p = 65812127 ∨ p = 66091757 ∨ p = 66376757 ∨ p = 67374467) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 60307757) 373 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 60345821) 1049 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 60425861) 3803 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 60765071) 53 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 60957497) 3181 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 61187507) 1021 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 61251887) 4021 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 62331251) 83 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 62423651) 3547 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 62898191) 67 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 62913437) 79 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 63211397) 3559 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 63627491) 173 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 64558931) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 65510171) 53 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 65625731) 1193 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 65812127) 109 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 66091757) 331 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 66376757) 691 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 67374467) 1723 (by decide) (by decide) (by decide)

lemma helper_exceptions_g13 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 67538687 ∨ p = 68302601 ∨ p = 68583917 ∨ p = 69340487 ∨ p = 70316627 ∨ p = 70553501 ∨ p = 70688201 ∨ p = 70876697 ∨ p = 71026721 ∨ p = 71396177 ∨ p = 71483801 ∨ p = 71848871 ∨ p = 71961971 ∨ p = 72028037 ∨ p = 72172481 ∨ p = 72739211 ∨ p = 72960047 ∨ p = 73188287 ∨ p = 74028167 ∨ p = 74084597) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 67538687) 109 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 68302601) 3643 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 68583917) 521 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 69340487) 439 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 70316627) 1663 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 70553501) 379 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 70688201) 61 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 70876697) 331 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 71026721) 1049 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 71396177) 131 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 71483801) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 71848871) 1151 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 71961971) 953 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 72028037) 101 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 72172481) 181 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 72739211) 8461 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 72960047) 59 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 73188287) 3343 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 74028167) 97 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 74084597) 2281 (by decide) (by decide) (by decide)

lemma helper_exceptions_g14 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 74497331 ∨ p = 74788601 ∨ p = 74904101 ∨ p = 75031337 ∨ p = 75231041 ∨ p = 75287867 ∨ p = 75864641 ∨ p = 76488017 ∨ p = 76724861 ∨ p = 77000447 ∨ p = 77287907 ∨ p = 77389511 ∨ p = 77737811 ∨ p = 78109307 ∨ p = 78982721 ∨ p = 79052651 ∨ p = 79782707 ∨ p = 80183417 ∨ p = 80382551 ∨ p = 80443787) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 74497331) 643 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 74788601) 107 (by decide) (by decide) (by decide)
  · use 8
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (8 ^ 2 - 8 + 74904101) 61 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 75031337) 599 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 75231041) 5783 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 75287867) 79 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 75864641) 4027 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 76488017) 1069 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 76724861) 53 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 77000447) 911 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 77287907) 107 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 77389511) 3929 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 77737811) 79 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 78109307) 5953 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 78982721) 313 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 79052651) 113 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 79782707) 2069 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 80183417) 59 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 80382551) 433 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 80443787) 173 (by decide) (by decide) (by decide)

lemma helper_exceptions_g15 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 80654927 ∨ p = 80756717 ∨ p = 80827781 ∨ p = 81332831 ∨ p = 81388751 ∨ p = 81642287 ∨ p = 81682817 ∨ p = 81715421 ∨ p = 81806897 ∨ p = 82163591 ∨ p = 82196327 ∨ p = 82220051 ∨ p = 82249691 ∨ p = 82351121 ∨ p = 82416401 ∨ p = 82477667 ∨ p = 82510511 ∨ p = 82642577 ∨ p = 82717751 ∨ p = 83185847) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 80654927) 59 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 80756717) 79 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 80827781) 5711 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 81332831) 757 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 81388751) 937 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 81642287) 797 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 81682817) 131 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 81715421) 337 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 81806897) 521 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82163591) 131 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82196327) 1039 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82220051) 1019 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82249691) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82351121) 113 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82416401) 89 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 82477667) 61 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82510511) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 82642577) 719 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 82717751) 89 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 83185847) 1129 (by decide) (by decide) (by decide)

lemma helper_exceptions_g16 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 83327261 ∨ p = 83406287 ∨ p = 85425227 ∨ p = 85649147 ∨ p = 85668881 ∨ p = 85899257 ∨ p = 86237687 ∨ p = 86604767 ∨ p = 87829031 ∨ p = 88516511 ∨ p = 88536647 ∨ p = 88645091 ∨ p = 88746731 ∨ p = 88971131 ∨ p = 89149871 ∨ p = 89156357 ∨ p = 89521967 ∨ p = 89784677 ∨ p = 90336371 ∨ p = 90404387) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 83327261) 421 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 83406287) 383 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 85425227) 4007 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 85649147) 1889 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 85668881) 1031 (by decide) (by decide) (by decide)
  · use 6
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (6 ^ 2 - 6 + 85899257) 397 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 86237687) 131 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 86604767) 103 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 87829031) 773 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 88516511) 167 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 88536647) 1049 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 88645091) 193 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 88746731) 1523 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 88971131) 787 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 89149871) 137 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 89156357) 83 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 89521967) 5471 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 89784677) 71 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 90336371) 4651 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 90404387) 101 (by decide) (by decide) (by decide)

lemma helper_exceptions_g17 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 90468797 ∨ p = 92280647 ∨ p = 92460827 ∨ p = 92553737 ∨ p = 92661971 ∨ p = 92683751 ∨ p = 92955407 ∨ p = 93086291 ∨ p = 94014647 ∨ p = 94142297 ∨ p = 94410047 ∨ p = 94606277 ∨ p = 94670657 ∨ p = 94922141 ∨ p = 95134211 ∨ p = 95217581 ∨ p = 95479061 ∨ p = 95494307 ∨ p = 96124487 ∨ p = 96519167) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 90468797) 347 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 92280647) 271 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 92460827) 647 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 92553737) 541 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 92661971) 239 (by decide) (by decide) (by decide)
  · use 7
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (7 ^ 2 - 7 + 92683751) 73 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 92955407) 401 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 93086291) 827 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 94014647) 577 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 94142297) 67 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 94410047) 71 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 94606277) 5407 (by decide) (by decide) (by decide)
  · use 5
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (5 ^ 2 - 5 + 94670657) 79 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 94922141) 113 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 95134211) 2903 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 95217581) 2243 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 95479061) 601 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 95494307) 1031 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 96124487) 461 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 96519167) 4547 (by decide) (by decide) (by decide)

lemma helper_exceptions_g18 (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : p = 96802787 ∨ p = 96850991 ∨ p = 97062851 ∨ p = 97675157 ∨ p = 97939607 ∨ p = 98937857 ∨ p = 99396611 ∨ p = 99509561 ∨ p = 99539591 ∨ p = 99769487 ∨ p = 99848657 ∨ p = 99891917) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 96802787) 661 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 96850991) 179 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 97062851) 463 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 97675157) 7451 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 97939607) 7639 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 98937857) 977 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 99396611) 2129 (by decide) (by decide) (by decide)
  · use 3
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (3 ^ 2 - 3 + 99509561) 53 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 99539591) 311 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 99769487) 2531 (by decide) (by decide) (by decide)
  · use 2
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (2 ^ 2 - 2 + 99848657) 3989 (by decide) (by decide) (by decide)
  · use 4
    refine ⟨by rw [Finset.mem_Icc]; constructor <;> omega, ?_⟩
    exact not_prime_by_factor (4 ^ 2 - 4 + 99891917) 101 (by decide) (by decide) (by decide)

lemma helper_exceptions (p : ℕ) (n : ℕ) (h_ge : n ≥ 46) (h_ex : (p = 333491 ∨ p = 601037 ∨ p = 1084997 ∨ p = 1525367 ∨ p = 1960391 ∨ p = 2367767 ∨ p = 2528621 ∨ p = 2533367 ∨ p = 2561681 ∨ p = 2567177 ∨ p = 2925821 ∨ p = 3322337 ∨ p = 3372221 ∨ p = 3558407 ∨ p = 3733397 ∨ p = 3754691 ∨ p = 4253267 ∨ p = 4402787 ∨ p = 4773227 ∨ p = 4876451) ∨ (p = 5108561 ∨ p = 5237651 ∨ p = 5240591 ∨ p = 5324441 ∨ p = 5499077 ∨ p = 5570417 ∨ p = 5574971 ∨ p = 5608697 ∨ p = 5840951 ∨ p = 6275177 ∨ p = 6385397 ∨ p = 7325231 ∨ p = 7410497 ∨ p = 7507937 ∨ p = 7527251 ∨ p = 7800827 ∨ p = 8139641 ∨ p = 8395061 ∨ p = 9195731 ∨ p = 9464837) ∨ (p = 9563621 ∨ p = 9572021 ∨ p = 10058177 ∨ p = 10325657 ∨ p = 10416137 ∨ p = 10661237 ∨ p = 10907021 ∨ p = 10997081 ∨ p = 11420567 ∨ p = 11445647 ∨ p = 11638631 ∨ p = 11691851 ∨ p = 11867897 ∨ p = 11984717 ∨ p = 12362951 ∨ p = 12414287 ∨ p = 12507617 ∨ p = 12935051 ∨ p = 13023737 ∨ p = 13111181) ∨ (p = 13611041 ∨ p = 13911407 ∨ p = 14396477 ∨ p = 14400767 ∨ p = 14437457 ∨ p = 14549891 ∨ p = 14728157 ∨ p = 14751701 ∨ p = 14812277 ∨ p = 14899721 ∨ p = 14940281 ∨ p = 15062891 ∨ p = 15102077 ∨ p = 15243311 ∨ p = 15346607 ∨ p = 15405317 ∨ p = 15410567 ∨ p = 15708347 ∨ p = 15715517 ∨ p = 15837947) ∨ (p = 16625591 ∨ p = 16773431 ∨ p = 16827647 ∨ p = 17695187 ∨ p = 17912261 ∨ p = 18172391 ∨ p = 19003337 ∨ p = 20217137 ∨ p = 20404817 ∨ p = 20740397 ∨ p = 21277337 ∨ p = 21390491 ∨ p = 21456047 ∨ p = 21522101 ∨ p = 21832751 ∨ p = 21977777 ∨ p = 22072487 ∨ p = 22758077 ∨ p = 23028611 ∨ p = 23362511) ∨ (p = 23429951 ∨ p = 23594171 ∨ p = 23654231 ∨ p = 23990231 ∨ p = 24004061 ∨ p = 24102977 ∨ p = 24417137 ∨ p = 24519617 ∨ p = 24731381 ∨ p = 24838481 ∨ p = 24868001 ∨ p = 25082567 ∨ p = 25187837 ∨ p = 25684781 ∨ p = 26072171 ∨ p = 26692067 ∨ p = 26769287 ∨ p = 27064547 ∨ p = 27252761 ∨ p = 27441767) ∨ (p = 27543611 ∨ p = 27648347 ∨ p = 27674741 ∨ p = 28377257 ∨ p = 28399487 ∨ p = 28435697 ∨ p = 28537121 ∨ p = 28869011 ∨ p = 29185811 ∨ p = 29282711 ∨ p = 29333387 ∨ p = 29479181 ∨ p = 29570267 ∨ p = 30554201 ∨ p = 30624947 ∨ p = 30671087 ∨ p = 30691937 ∨ p = 30806507 ∨ p = 30825647 ∨ p = 30932411) ∨ (p = 30975557 ∨ p = 31102781 ∨ p = 31123637 ∨ p = 31278251 ∨ p = 31316267 ∨ p = 31384007 ∨ p = 31626977 ∨ p = 31965821 ∨ p = 31999271 ∨ p = 32186237 ∨ p = 32188691 ∨ p = 32381807 ∨ p = 32571557 ∨ p = 32940221 ∨ p = 33090371 ∨ p = 33252377 ∨ p = 33502367 ∨ p = 34011821 ∨ p = 34778657 ∨ p = 35077241) ∨ (p = 35184971 ∨ p = 35347511 ∨ p = 35598581 ∨ p = 35604551 ∨ p = 35831921 ∨ p = 36018107 ∨ p = 36155501 ∨ p = 36256037 ∨ p = 36474827 ∨ p = 36531221 ∨ p = 37631411 ∨ p = 37837841 ∨ p = 37989431 ∨ p = 38250461 ∨ p = 38606957 ∨ p = 38939267 ∨ p = 39965267 ∨ p = 40305761 ∨ p = 41194997 ∨ p = 41219597) ∨ (p = 42124541 ∨ p = 42521651 ∨ p = 43149257 ∨ p = 43746737 ∨ p = 44028197 ∨ p = 44422991 ∨ p = 44496581 ∨ p = 45154841 ∨ p = 45181307 ∨ p = 45695717 ∨ p = 46036577 ∨ p = 47009507 ∨ p = 47509661 ∨ p = 47876681 ∨ p = 48363167 ∨ p = 48606911 ∨ p = 48891107 ∨ p = 48957341 ∨ p = 49938101 ∨ p = 50227271) ∨ (p = 50921021 ∨ p = 51090497 ∨ p = 51256481 ∨ p = 51344387 ∨ p = 51804407 ∨ p = 52119491 ∨ p = 52325081 ∨ p = 52340537 ∨ p = 52412027 ∨ p = 52639877 ∨ p = 52742771 ∨ p = 53487881 ∨ p = 53949167 ∨ p = 54029147 ∨ p = 54758591 ∨ p = 54828197 ∨ p = 54898511 ∨ p = 55040261 ∨ p = 55477517 ∨ p = 55534751) ∨ (p = 55793951 ∨ p = 55839851 ∨ p = 56188877 ∨ p = 56406431 ∨ p = 56533571 ∨ p = 56719571 ∨ p = 57279767 ∨ p = 57330017 ∨ p = 57345677 ∨ p = 57685151 ∨ p = 57867191 ∨ p = 57966761 ∨ p = 58073837 ∨ p = 58095041 ∨ p = 58388567 ∨ p = 58636967 ∨ p = 58759397 ∨ p = 58803581 ∨ p = 58928687 ∨ p = 59427617) ∨ (p = 60307757 ∨ p = 60345821 ∨ p = 60425861 ∨ p = 60765071 ∨ p = 60957497 ∨ p = 61187507 ∨ p = 61251887 ∨ p = 62331251 ∨ p = 62423651 ∨ p = 62898191 ∨ p = 62913437 ∨ p = 63211397 ∨ p = 63627491 ∨ p = 64558931 ∨ p = 65510171 ∨ p = 65625731 ∨ p = 65812127 ∨ p = 66091757 ∨ p = 66376757 ∨ p = 67374467) ∨ (p = 67538687 ∨ p = 68302601 ∨ p = 68583917 ∨ p = 69340487 ∨ p = 70316627 ∨ p = 70553501 ∨ p = 70688201 ∨ p = 70876697 ∨ p = 71026721 ∨ p = 71396177 ∨ p = 71483801 ∨ p = 71848871 ∨ p = 71961971 ∨ p = 72028037 ∨ p = 72172481 ∨ p = 72739211 ∨ p = 72960047 ∨ p = 73188287 ∨ p = 74028167 ∨ p = 74084597) ∨ (p = 74497331 ∨ p = 74788601 ∨ p = 74904101 ∨ p = 75031337 ∨ p = 75231041 ∨ p = 75287867 ∨ p = 75864641 ∨ p = 76488017 ∨ p = 76724861 ∨ p = 77000447 ∨ p = 77287907 ∨ p = 77389511 ∨ p = 77737811 ∨ p = 78109307 ∨ p = 78982721 ∨ p = 79052651 ∨ p = 79782707 ∨ p = 80183417 ∨ p = 80382551 ∨ p = 80443787) ∨ (p = 80654927 ∨ p = 80756717 ∨ p = 80827781 ∨ p = 81332831 ∨ p = 81388751 ∨ p = 81642287 ∨ p = 81682817 ∨ p = 81715421 ∨ p = 81806897 ∨ p = 82163591 ∨ p = 82196327 ∨ p = 82220051 ∨ p = 82249691 ∨ p = 82351121 ∨ p = 82416401 ∨ p = 82477667 ∨ p = 82510511 ∨ p = 82642577 ∨ p = 82717751 ∨ p = 83185847) ∨ (p = 83327261 ∨ p = 83406287 ∨ p = 85425227 ∨ p = 85649147 ∨ p = 85668881 ∨ p = 85899257 ∨ p = 86237687 ∨ p = 86604767 ∨ p = 87829031 ∨ p = 88516511 ∨ p = 88536647 ∨ p = 88645091 ∨ p = 88746731 ∨ p = 88971131 ∨ p = 89149871 ∨ p = 89156357 ∨ p = 89521967 ∨ p = 89784677 ∨ p = 90336371 ∨ p = 90404387) ∨ (p = 90468797 ∨ p = 92280647 ∨ p = 92460827 ∨ p = 92553737 ∨ p = 92661971 ∨ p = 92683751 ∨ p = 92955407 ∨ p = 93086291 ∨ p = 94014647 ∨ p = 94142297 ∨ p = 94410047 ∨ p = 94606277 ∨ p = 94670657 ∨ p = 94922141 ∨ p = 95134211 ∨ p = 95217581 ∨ p = 95479061 ∨ p = 95494307 ∨ p = 96124487 ∨ p = 96519167) ∨ (p = 96802787 ∨ p = 96850991 ∨ p = 97062851 ∨ p = 97675157 ∨ p = 97939607 ∨ p = 98937857 ∨ p = 99396611 ∨ p = 99509561 ∨ p = 99539591 ∨ p = 99769487 ∨ p = 99848657 ∨ p = 99891917)) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_ex with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18
  · exact helper_exceptions_g0 p n h_ge h0
  · exact helper_exceptions_g1 p n h_ge h1
  · exact helper_exceptions_g2 p n h_ge h2
  · exact helper_exceptions_g3 p n h_ge h3
  · exact helper_exceptions_g4 p n h_ge h4
  · exact helper_exceptions_g5 p n h_ge h5
  · exact helper_exceptions_g6 p n h_ge h6
  · exact helper_exceptions_g7 p n h_ge h7
  · exact helper_exceptions_g8 p n h_ge h8
  · exact helper_exceptions_g9 p n h_ge h9
  · exact helper_exceptions_g10 p n h_ge h10
  · exact helper_exceptions_g11 p n h_ge h11
  · exact helper_exceptions_g12 p n h_ge h12
  · exact helper_exceptions_g13 p n h_ge h13
  · exact helper_exceptions_g14 p n h_ge h14
  · exact helper_exceptions_g15 p n h_ge h15
  · exact helper_exceptions_g16 p n h_ge h16
  · exact helper_exceptions_g17 p n h_ge h17
  · exact helper_exceptions_g18 p n h_ge h18

lemma helper_concrete_14 : ∃ k ∈ Finset.Icc 1 14, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (14 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (14 - 1) = 43 := by
    have h_sub : 14 - 1 = 13 := by rfl
    have hc : count Nat.Prime 43 = 13 := by decide
    have hp : Nat.Prime 43 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 43) = 43 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 14 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_15 : ∃ k ∈ Finset.Icc 1 15, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (15 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (15 - 1) = 47 := by
    have h_sub : 15 - 1 = 14 := by rfl
    have hc : count Nat.Prime 47 = 14 := by decide
    have hp : Nat.Prime 47 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 47) = 47 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 15 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_16 : ∃ k ∈ Finset.Icc 1 16, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (16 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (16 - 1) = 53 := by
    have h_sub : 16 - 1 = 15 := by rfl
    have hc : count Nat.Prime 53 = 15 := by decide
    have hp : Nat.Prime 53 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 53) = 53 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 16 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_17 : ∃ k ∈ Finset.Icc 1 17, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (17 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (17 - 1) = 59 := by
    have h_sub : 17 - 1 = 16 := by rfl
    have hc : count Nat.Prime 59 = 16 := by decide
    have hp : Nat.Prime 59 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 59) = 59 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 3
  have h_in : 3 ∈ Finset.Icc 1 17 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_18 : ∃ k ∈ Finset.Icc 1 18, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (18 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (18 - 1) = 61 := by
    have h_sub : 18 - 1 = 17 := by rfl
    have hc : count Nat.Prime 61 = 17 := by decide
    have hp : Nat.Prime 61 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 61) = 61 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 18 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_19 : ∃ k ∈ Finset.Icc 1 19, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (19 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (19 - 1) = 67 := by
    have h_sub : 19 - 1 = 18 := by rfl
    have hc : count Nat.Prime 67 = 18 := by decide
    have hp : Nat.Prime 67 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 67) = 67 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 19 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_20 : ∃ k ∈ Finset.Icc 1 20, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (20 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (20 - 1) = 71 := by
    have h_sub : 20 - 1 = 19 := by rfl
    have hc : count Nat.Prime 71 = 19 := by decide
    have hp : Nat.Prime 71 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 71) = 71 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 3
  have h_in : 3 ∈ Finset.Icc 1 20 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_21 : ∃ k ∈ Finset.Icc 1 21, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (21 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (21 - 1) = 73 := by
    have h_sub : 21 - 1 = 20 := by rfl
    have hc : count Nat.Prime 73 = 20 := by decide
    have hp : Nat.Prime 73 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 73) = 73 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 21 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_22 : ∃ k ∈ Finset.Icc 1 22, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (22 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (22 - 1) = 79 := by
    have h_sub : 22 - 1 = 21 := by rfl
    have hc : count Nat.Prime 79 = 21 := by decide
    have hp : Nat.Prime 79 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 79) = 79 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 22 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_23 : ∃ k ∈ Finset.Icc 1 23, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (23 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (23 - 1) = 83 := by
    have h_sub : 23 - 1 = 22 := by rfl
    have hc : count Nat.Prime 83 = 22 := by decide
    have hp : Nat.Prime 83 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 83) = 83 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 23 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_24 : ∃ k ∈ Finset.Icc 1 24, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (24 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (24 - 1) = 89 := by
    have h_sub : 24 - 1 = 23 := by rfl
    have hc : count Nat.Prime 89 = 23 := by decide
    have hp : Nat.Prime 89 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 89) = 89 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 24 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_25 : ∃ k ∈ Finset.Icc 1 25, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (25 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (25 - 1) = 97 := by
    have h_sub : 25 - 1 = 24 := by rfl
    have hc : count Nat.Prime 97 = 24 := by decide
    have hp : Nat.Prime 97 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 97) = 97 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 25 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_26 : ∃ k ∈ Finset.Icc 1 26, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (26 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (26 - 1) = 101 := by
    have h_sub : 26 - 1 = 25 := by rfl
    have hc : count Nat.Prime 101 = 25 := by decide
    have hp : Nat.Prime 101 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 101) = 101 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 5
  have h_in : 5 ∈ Finset.Icc 1 26 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_27 : ∃ k ∈ Finset.Icc 1 27, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (27 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (27 - 1) = 103 := by
    have h_sub : 27 - 1 = 26 := by rfl
    have hc : count Nat.Prime 103 = 26 := by decide
    have hp : Nat.Prime 103 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 103) = 103 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 27 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_28 : ∃ k ∈ Finset.Icc 1 28, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (28 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (28 - 1) = 107 := by
    have h_sub : 28 - 1 = 27 := by rfl
    have hc : count Nat.Prime 107 = 27 := by decide
    have hp : Nat.Prime 107 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 107) = 107 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 4
  have h_in : 4 ∈ Finset.Icc 1 28 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_29 : ∃ k ∈ Finset.Icc 1 29, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (29 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (29 - 1) = 109 := by
    have h_sub : 29 - 1 = 28 := by rfl
    have hc : count Nat.Prime 109 = 28 := by decide
    have hp : Nat.Prime 109 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 109) = 109 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 29 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_30 : ∃ k ∈ Finset.Icc 1 30, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (30 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (30 - 1) = 113 := by
    have h_sub : 30 - 1 = 29 := by rfl
    have hc : count Nat.Prime 113 = 29 := by decide
    have hp : Nat.Prime 113 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 113) = 113 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 30 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_31 : ∃ k ∈ Finset.Icc 1 31, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (31 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (31 - 1) = 127 := by
    have h_sub : 31 - 1 = 30 := by rfl
    have hc : count Nat.Prime 127 = 30 := by decide
    have hp : Nat.Prime 127 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 127) = 127 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 31 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_32 : ∃ k ∈ Finset.Icc 1 32, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (32 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (32 - 1) = 131 := by
    have h_sub : 32 - 1 = 31 := by rfl
    have hc : count Nat.Prime 131 = 31 := by decide
    have hp : Nat.Prime 131 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 131) = 131 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 32 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_33 : ∃ k ∈ Finset.Icc 1 33, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (33 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (33 - 1) = 137 := by
    have h_sub : 33 - 1 = 32 := by rfl
    have hc : count Nat.Prime 137 = 32 := by decide
    have hp : Nat.Prime 137 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 137) = 137 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 3
  have h_in : 3 ∈ Finset.Icc 1 33 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_34 : ∃ k ∈ Finset.Icc 1 34, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (34 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (34 - 1) = 139 := by
    have h_sub : 34 - 1 = 33 := by rfl
    have hc : count Nat.Prime 139 = 33 := by decide
    have hp : Nat.Prime 139 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 139) = 139 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 34 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_35 : ∃ k ∈ Finset.Icc 1 35, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (35 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (35 - 1) = 149 := by
    have h_sub : 35 - 1 = 34 := by rfl
    have hc : count Nat.Prime 149 = 34 := by decide
    have hp : Nat.Prime 149 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 149) = 149 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 3
  have h_in : 3 ∈ Finset.Icc 1 35 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_36 : ∃ k ∈ Finset.Icc 1 36, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (36 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (36 - 1) = 151 := by
    have h_sub : 36 - 1 = 35 := by rfl
    have hc : count Nat.Prime 151 = 35 := by decide
    have hp : Nat.Prime 151 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 151) = 151 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 36 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_37 : ∃ k ∈ Finset.Icc 1 37, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (37 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (37 - 1) = 157 := by
    have h_sub : 37 - 1 = 36 := by rfl
    have hc : count Nat.Prime 157 = 36 := by decide
    have hp : Nat.Prime 157 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 157) = 157 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 37 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_38 : ∃ k ∈ Finset.Icc 1 38, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (38 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (38 - 1) = 163 := by
    have h_sub : 38 - 1 = 37 := by rfl
    have hc : count Nat.Prime 163 = 37 := by decide
    have hp : Nat.Prime 163 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 163) = 163 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 38 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_39 : ∃ k ∈ Finset.Icc 1 39, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (39 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (39 - 1) = 167 := by
    have h_sub : 39 - 1 = 38 := by rfl
    have hc : count Nat.Prime 167 = 38 := by decide
    have hp : Nat.Prime 167 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 167) = 167 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 39 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_40 : ∃ k ∈ Finset.Icc 1 40, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (40 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (40 - 1) = 173 := by
    have h_sub : 40 - 1 = 39 := by rfl
    have hc : count Nat.Prime 173 = 39 := by decide
    have hp : Nat.Prime 173 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 173) = 173 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 40 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_41 : ∃ k ∈ Finset.Icc 1 41, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (41 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (41 - 1) = 179 := by
    have h_sub : 41 - 1 = 40 := by rfl
    have hc : count Nat.Prime 179 = 40 := by decide
    have hp : Nat.Prime 179 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 179) = 179 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 3
  have h_in : 3 ∈ Finset.Icc 1 41 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_42 : ∃ k ∈ Finset.Icc 1 42, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (42 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (42 - 1) = 181 := by
    have h_sub : 42 - 1 = 41 := by rfl
    have hc : count Nat.Prime 181 = 41 := by decide
    have hp : Nat.Prime 181 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 181) = 181 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 42 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_43 : ∃ k ∈ Finset.Icc 1 43, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (43 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (43 - 1) = 191 := by
    have h_sub : 43 - 1 = 42 := by rfl
    have hc : count Nat.Prime 191 = 42 := by decide
    have hp : Nat.Prime 191 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 191) = 191 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 4
  have h_in : 4 ∈ Finset.Icc 1 43 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_44 : ∃ k ∈ Finset.Icc 1 44, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (44 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (44 - 1) = 193 := by
    have h_sub : 44 - 1 = 43 := by rfl
    have hc : count Nat.Prime 193 = 43 := by decide
    have hp : Nat.Prime 193 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 193) = 193 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 44 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_45 : ∃ k ∈ Finset.Icc 1 45, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (45 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (45 - 1) = 197 := by
    have h_sub : 45 - 1 = 44 := by rfl
    have hc : count Nat.Prime 197 = 44 := by decide
    have hp : Nat.Prime 197 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 197) = 197 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 3
  have h_in : 3 ∈ Finset.Icc 1 45 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_46 : ∃ k ∈ Finset.Icc 1 46, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (46 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (46 - 1) = 199 := by
    have h_sub : 46 - 1 = 45 := by rfl
    have hc : count Nat.Prime 199 = 45 := by decide
    have hp : Nat.Prime 199 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 199) = 199 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 46 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_concrete_47 : ∃ k ∈ Finset.Icc 1 47, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (47 - 1)) := by
  have h_eq : Nat.nth Nat.Prime (47 - 1) = 211 := by
    have h_sub : 47 - 1 = 46 := by rfl
    have hc : count Nat.Prime 211 = 46 := by decide
    have hp : Nat.Prime 211 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 211) = 211 := nth_count hp
    rw [hc] at h3
    rw [h_sub, h3]
  use 2
  have h_in : 2 ∈ Finset.Icc 1 47 := by decide
  refine ⟨h_in, ?_⟩
  rw [h_eq]
  decide

lemma helper_mod_3_to_11 (p : ℕ) (n : ℕ) (hn : n ≥ 48) (hp_ge : p ≥ 199) (h_mod : p % 3 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 5 ∨ p % 11 = 2 ∨ p % 11 = 3 ∨ p % 11 = 5 ∨ p % 11 = 9 ∨ p % 11 = 10) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_mod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 3 = 0 := by omega
    exact test_mod_general_large p 3 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 5 = 0 := by omega
    exact test_mod_general_large p 5 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 5 = 0 := by omega
    exact test_mod_general_large p 5 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 7 = 0 := by omega
    exact test_mod_general_large p 7 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 7 = 0 := by omega
    exact test_mod_general_large p 7 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 7 = 0 := by omega
    exact test_mod_general_large p 7 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 11 = 0 := by omega
    exact test_mod_general_large p 11 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 11 = 0 := by omega
    exact test_mod_general_large p 11 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 11 = 0 := by omega
    exact test_mod_general_large p 11 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 11 = 0 := by omega
    exact test_mod_general_large p 11 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 11 = 0 := by omega
    exact test_mod_general_large p 11 (by decide) (by decide) hp_ge 12 h_mod (by decide)

lemma helper_mod_13_to_19 (p : ℕ) (n : ℕ) (hn : n ≥ 48) (hp_ge : p ≥ 199) (h_mod : p % 13 = 1 ∨ p % 13 = 6 ∨ p % 13 = 7 ∨ p % 13 = 9 ∨ p % 13 = 10 ∨ p % 13 = 11 ∨ p % 17 = 4 ∨ p % 17 = 5 ∨ p % 17 = 9 ∨ p % 17 = 11 ∨ p % 17 = 12 ∨ p % 17 = 13 ∨ p % 17 = 14 ∨ p % 17 = 15 ∨ p % 19 = 1 ∨ p % 19 = 4 ∨ p % 19 = 5 ∨ p % 19 = 7 ∨ p % 19 = 8 ∨ p % 19 = 13 ∨ p % 19 = 15 ∨ p % 19 = 17 ∨ p % 19 = 18) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_mod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 13 = 0 := by omega
    exact test_mod_general_large p 13 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 13 = 0 := by omega
    exact test_mod_general_large p 13 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 13 = 0 := by omega
    exact test_mod_general_large p 13 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 13 = 0 := by omega
    exact test_mod_general_large p 13 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 13 = 0 := by omega
    exact test_mod_general_large p 13 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 13 = 0 := by omega
    exact test_mod_general_large p 13 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 17 = 0 := by omega
    exact test_mod_general_large p 17 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 19 = 0 := by omega
    exact test_mod_general_large p 19 (by decide) (by decide) hp_ge 20 h_mod (by decide)

lemma helper_mod_23_to_31 (p : ℕ) (n : ℕ) (hn : n ≥ 48) (hp_ge : p ≥ 199) (h_mod : p % 23 = 2 ∨ p % 23 = 3 ∨ p % 23 = 4 ∨ p % 23 = 5 ∨ p % 23 = 6 ∨ p % 23 = 11 ∨ p % 23 = 13 ∨ p % 23 = 16 ∨ p % 23 = 17 ∨ p % 23 = 20 ∨ p % 23 = 21 ∨ p % 29 = 2 ∨ p % 29 = 6 ∨ p % 29 = 9 ∨ p % 29 = 13 ∨ p % 29 = 15 ∨ p % 29 = 16 ∨ p % 29 = 17 ∨ p % 29 = 18 ∨ p % 29 = 21 ∨ p % 29 = 22 ∨ p % 29 = 23 ∨ p % 29 = 26 ∨ p % 29 = 27 ∨ p % 29 = 28 ∨ p % 31 = 1 ∨ p % 31 = 3 ∨ p % 31 = 4 ∨ p % 31 = 6 ∨ p % 31 = 7 ∨ p % 31 = 8 ∨ p % 31 = 11 ∨ p % 31 = 14 ∨ p % 31 = 19 ∨ p % 31 = 20 ∨ p % 31 = 21 ∨ p % 31 = 23 ∨ p % 31 = 25 ∨ p % 31 = 29 ∨ p % 31 = 30) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_mod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 23 = 0 := by omega
    exact test_mod_general_large p 23 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 13
    have h_in : 13 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 13 ^ 2 - 13 + p = p + 156 := by ring
    rw [h_eq]
    have h_mod : (p + 156) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 156 h_mod (by decide)
  · use 14
    have h_in : 14 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 14 ^ 2 - 14 + p = p + 182 := by ring
    rw [h_eq]
    have h_mod : (p + 182) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 182 h_mod (by decide)
  · use 15
    have h_in : 15 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 15 ^ 2 - 15 + p = p + 210 := by ring
    rw [h_eq]
    have h_mod : (p + 210) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 210 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 29 = 0 := by omega
    exact test_mod_general_large p 29 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 14
    have h_in : 14 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 14 ^ 2 - 14 + p = p + 182 := by ring
    rw [h_eq]
    have h_mod : (p + 182) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 182 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 15
    have h_in : 15 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 15 ^ 2 - 15 + p = p + 210 := by ring
    rw [h_eq]
    have h_mod : (p + 210) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 210 h_mod (by decide)
  · use 16
    have h_in : 16 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 16 ^ 2 - 16 + p = p + 240 := by ring
    rw [h_eq]
    have h_mod : (p + 240) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 240 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 13
    have h_in : 13 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 13 ^ 2 - 13 + p = p + 156 := by ring
    rw [h_eq]
    have h_mod : (p + 156) % 31 = 0 := by omega
    exact test_mod_general_large p 31 (by decide) (by decide) hp_ge 156 h_mod (by decide)

lemma helper_mod_37_to_47 (p : ℕ) (n : ℕ) (hn : n ≥ 48) (hp_ge : p ≥ 199) (h_mod : p % 37 = 1 ∨ p % 37 = 2 ∨ p % 37 = 3 ∨ p % 37 = 7 ∨ p % 37 = 12 ∨ p % 37 = 16 ∨ p % 37 = 17 ∨ p % 37 = 18 ∨ p % 37 = 19 ∨ p % 37 = 21 ∨ p % 37 = 24 ∨ p % 37 = 25 ∨ p % 37 = 27 ∨ p % 37 = 28 ∨ p % 37 = 29 ∨ p % 37 = 31 ∨ p % 37 = 32 ∨ p % 37 = 35 ∨ p % 41 = 6 ∨ p % 41 = 8 ∨ p % 41 = 10 ∨ p % 41 = 11 ∨ p % 41 = 13 ∨ p % 41 = 15 ∨ p % 41 = 21 ∨ p % 41 = 22 ∨ p % 41 = 23 ∨ p % 41 = 26 ∨ p % 41 = 27 ∨ p % 41 = 29 ∨ p % 41 = 30 ∨ p % 41 = 31 ∨ p % 41 = 32 ∨ p % 41 = 33 ∨ p % 41 = 35 ∨ p % 41 = 36 ∨ p % 41 = 39 ∨ p % 41 = 40 ∨ p % 43 = 1 ∨ p % 43 = 2 ∨ p % 43 = 5 ∨ p % 43 = 7 ∨ p % 43 = 10 ∨ p % 43 = 11 ∨ p % 43 = 13 ∨ p % 43 = 14 ∨ p % 43 = 16 ∨ p % 43 = 18 ∨ p % 43 = 19 ∨ p % 43 = 23 ∨ p % 43 = 29 ∨ p % 43 = 30 ∨ p % 43 = 31 ∨ p % 43 = 33 ∨ p % 43 = 37 ∨ p % 43 = 38 ∨ p % 43 = 39 ∨ p % 43 = 40 ∨ p % 43 = 41 ∨ p % 47 = 3 ∨ p % 47 = 4 ∨ p % 47 = 5 ∨ p % 47 = 6 ∨ p % 47 = 8 ∨ p % 47 = 9 ∨ p % 47 = 10 ∨ p % 47 = 11 ∨ p % 47 = 12 ∨ p % 47 = 17 ∨ p % 47 = 22 ∨ p % 47 = 23 ∨ p % 47 = 25 ∨ p % 47 = 27 ∨ p % 47 = 31 ∨ p % 47 = 32 ∨ p % 47 = 34 ∨ p % 47 = 35 ∨ p % 47 = 38 ∨ p % 47 = 41 ∨ p % 47 = 42 ∨ p % 47 = 43 ∨ p % 47 = 45) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + p) := by
  rcases h_mod with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15 | h16 | h17 | h18 | h19 | h20 | h21 | h22 | h23 | h24 | h25 | h26 | h27 | h28 | h29 | h30 | h31 | h32 | h33 | h34 | h35 | h36 | h37 | h38 | h39 | h40 | h41 | h42 | h43 | h44 | h45 | h46 | h47 | h48 | h49 | h50 | h51 | h52 | h53 | h54 | h55 | h56 | h57 | h58 | h59 | h60 | h61 | h62 | h63 | h64 | h65 | h66 | h67 | h68 | h69 | h70 | h71 | h72 | h73 | h74 | h75 | h76 | h77 | h78 | h79 | h80 | h81
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 14
    have h_in : 14 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 14 ^ 2 - 14 + p = p + 182 := by ring
    rw [h_eq]
    have h_mod : (p + 182) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 182 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 15
    have h_in : 15 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 15 ^ 2 - 15 + p = p + 210 := by ring
    rw [h_eq]
    have h_mod : (p + 210) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 210 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 16
    have h_in : 16 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 16 ^ 2 - 16 + p = p + 240 := by ring
    rw [h_eq]
    have h_mod : (p + 240) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 240 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 17
    have h_in : 17 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 17 ^ 2 - 17 + p = p + 272 := by ring
    rw [h_eq]
    have h_mod : (p + 272) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 272 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 18
    have h_in : 18 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 18 ^ 2 - 18 + p = p + 306 := by ring
    rw [h_eq]
    have h_mod : (p + 306) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 306 h_mod (by decide)
  · use 19
    have h_in : 19 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 19 ^ 2 - 19 + p = p + 342 := by ring
    rw [h_eq]
    have h_mod : (p + 342) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 342 h_mod (by decide)
  · use 13
    have h_in : 13 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 13 ^ 2 - 13 + p = p + 156 := by ring
    rw [h_eq]
    have h_mod : (p + 156) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 156 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 37 = 0 := by omega
    exact test_mod_general_large p 37 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 16
    have h_in : 16 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 16 ^ 2 - 16 + p = p + 240 := by ring
    rw [h_eq]
    have h_mod : (p + 240) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 240 h_mod (by decide)
  · use 13
    have h_in : 13 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 13 ^ 2 - 13 + p = p + 156 := by ring
    rw [h_eq]
    have h_mod : (p + 156) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 156 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 17
    have h_in : 17 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 17 ^ 2 - 17 + p = p + 272 := by ring
    rw [h_eq]
    have h_mod : (p + 272) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 272 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 18
    have h_in : 18 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 18 ^ 2 - 18 + p = p + 306 := by ring
    rw [h_eq]
    have h_mod : (p + 306) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 306 h_mod (by decide)
  · use 14
    have h_in : 14 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 14 ^ 2 - 14 + p = p + 182 := by ring
    rw [h_eq]
    have h_mod : (p + 182) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 182 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 19
    have h_in : 19 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 19 ^ 2 - 19 + p = p + 342 := by ring
    rw [h_eq]
    have h_mod : (p + 342) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 342 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 20
    have h_in : 20 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 20 ^ 2 - 20 + p = p + 380 := by ring
    rw [h_eq]
    have h_mod : (p + 380) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 380 h_mod (by decide)
  · use 21
    have h_in : 21 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 21 ^ 2 - 21 + p = p + 420 := by ring
    rw [h_eq]
    have h_mod : (p + 420) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 420 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 15
    have h_in : 15 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 15 ^ 2 - 15 + p = p + 210 := by ring
    rw [h_eq]
    have h_mod : (p + 210) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 210 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 41 = 0 := by omega
    exact test_mod_general_large p 41 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 19
    have h_in : 19 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 19 ^ 2 - 19 + p = p + 342 := by ring
    rw [h_eq]
    have h_mod : (p + 342) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 342 h_mod (by decide)
  · use 15
    have h_in : 15 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 15 ^ 2 - 15 + p = p + 210 := by ring
    rw [h_eq]
    have h_mod : (p + 210) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 210 h_mod (by decide)
  · use 20
    have h_in : 20 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 20 ^ 2 - 20 + p = p + 380 := by ring
    rw [h_eq]
    have h_mod : (p + 380) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 380 h_mod (by decide)
  · use 21
    have h_in : 21 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 21 ^ 2 - 21 + p = p + 420 := by ring
    rw [h_eq]
    have h_mod : (p + 420) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 420 h_mod (by decide)
  · use 22
    have h_in : 22 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 22 ^ 2 - 22 + p = p + 462 := by ring
    rw [h_eq]
    have h_mod : (p + 462) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 462 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 13
    have h_in : 13 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 13 ^ 2 - 13 + p = p + 156 := by ring
    rw [h_eq]
    have h_mod : (p + 156) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 156 h_mod (by decide)
  · use 16
    have h_in : 16 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 16 ^ 2 - 16 + p = p + 240 := by ring
    rw [h_eq]
    have h_mod : (p + 240) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 240 h_mod (by decide)
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 17
    have h_in : 17 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 17 ^ 2 - 17 + p = p + 272 := by ring
    rw [h_eq]
    have h_mod : (p + 272) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 272 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 14
    have h_in : 14 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 14 ^ 2 - 14 + p = p + 182 := by ring
    rw [h_eq]
    have h_mod : (p + 182) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 182 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 18
    have h_in : 18 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 18 ^ 2 - 18 + p = p + 306 := by ring
    rw [h_eq]
    have h_mod : (p + 306) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 306 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 43 = 0 := by omega
    exact test_mod_general_large p 43 (by decide) (by decide) hp_ge 2 h_mod (by decide)
  · use 21
    have h_in : 21 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 21 ^ 2 - 21 + p = p + 420 := by ring
    rw [h_eq]
    have h_mod : (p + 420) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 420 h_mod (by decide)
  · use 10
    have h_in : 10 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 10 ^ 2 - 10 + p = p + 90 := by ring
    rw [h_eq]
    have h_mod : (p + 90) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 90 h_mod (by decide)
  · use 7
    have h_in : 7 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 7 ^ 2 - 7 + p = p + 42 := by ring
    rw [h_eq]
    have h_mod : (p + 42) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 42 h_mod (by decide)
  · use 14
    have h_in : 14 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 14 ^ 2 - 14 + p = p + 182 := by ring
    rw [h_eq]
    have h_mod : (p + 182) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 182 h_mod (by decide)
  · use 22
    have h_in : 22 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 22 ^ 2 - 22 + p = p + 462 := by ring
    rw [h_eq]
    have h_mod : (p + 462) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 462 h_mod (by decide)
  · use 12
    have h_in : 12 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 12 ^ 2 - 12 + p = p + 132 := by ring
    rw [h_eq]
    have h_mod : (p + 132) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 132 h_mod (by decide)
  · use 17
    have h_in : 17 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 17 ^ 2 - 17 + p = p + 272 := by ring
    rw [h_eq]
    have h_mod : (p + 272) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 272 h_mod (by decide)
  · use 23
    have h_in : 23 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 23 ^ 2 - 23 + p = p + 506 := by ring
    rw [h_eq]
    have h_mod : (p + 506) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 506 h_mod (by decide)
  · use 24
    have h_in : 24 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 24 ^ 2 - 24 + p = p + 552 := by ring
    rw [h_eq]
    have h_mod : (p + 552) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 552 h_mod (by decide)
  · use 6
    have h_in : 6 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 6 ^ 2 - 6 + p = p + 30 := by ring
    rw [h_eq]
    have h_mod : (p + 30) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 30 h_mod (by decide)
  · use 9
    have h_in : 9 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 9 ^ 2 - 9 + p = p + 72 := by ring
    rw [h_eq]
    have h_mod : (p + 72) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 72 h_mod (by decide)
  · use 18
    have h_in : 18 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 18 ^ 2 - 18 + p = p + 306 := by ring
    rw [h_eq]
    have h_mod : (p + 306) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 306 h_mod (by decide)
  · use 15
    have h_in : 15 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 15 ^ 2 - 15 + p = p + 210 := by ring
    rw [h_eq]
    have h_mod : (p + 210) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 210 h_mod (by decide)
  · use 5
    have h_in : 5 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 5 ^ 2 - 5 + p = p + 20 := by ring
    rw [h_eq]
    have h_mod : (p + 20) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 20 h_mod (by decide)
  · use 11
    have h_in : 11 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 11 ^ 2 - 11 + p = p + 110 := by ring
    rw [h_eq]
    have h_mod : (p + 110) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 110 h_mod (by decide)
  · use 13
    have h_in : 13 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 13 ^ 2 - 13 + p = p + 156 := by ring
    rw [h_eq]
    have h_mod : (p + 156) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 156 h_mod (by decide)
  · use 19
    have h_in : 19 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 19 ^ 2 - 19 + p = p + 342 := by ring
    rw [h_eq]
    have h_mod : (p + 342) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 342 h_mod (by decide)
  · use 4
    have h_in : 4 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 4 ^ 2 - 4 + p = p + 12 := by ring
    rw [h_eq]
    have h_mod : (p + 12) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 12 h_mod (by decide)
  · use 8
    have h_in : 8 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 8 ^ 2 - 8 + p = p + 56 := by ring
    rw [h_eq]
    have h_mod : (p + 56) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 56 h_mod (by decide)
  · use 3
    have h_in : 3 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 3 ^ 2 - 3 + p = p + 6 := by ring
    rw [h_eq]
    have h_mod : (p + 6) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 6 h_mod (by decide)
  · use 16
    have h_in : 16 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 16 ^ 2 - 16 + p = p + 240 := by ring
    rw [h_eq]
    have h_mod : (p + 240) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 240 h_mod (by decide)
  · use 20
    have h_in : 20 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 20 ^ 2 - 20 + p = p + 380 := by ring
    rw [h_eq]
    have h_mod : (p + 380) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 380 h_mod (by decide)
  · use 2
    have h_in : 2 ∈ Finset.Icc 1 n := by rw [Finset.mem_Icc]; constructor <;> omega
    refine ⟨h_in, ?_⟩
    have h_eq : 2 ^ 2 - 2 + p = p + 2 := by ring
    rw [h_eq]
    have h_mod : (p + 2) % 47 = 0 := by omega
    exact test_mod_general_large p 47 (by decide) (by decide) hp_ge 2 h_mod (by decide)

lemma helper (n : ℕ) (h : n > 13) : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := by
  have hpn_ge_43 : Nat.nth Nat.Prime (n - 1) ≥ 43 := by
    have h1 : n - 1 ≥ 13 := by omega
    have h2 : Nat.nth Nat.Prime 13 ≤ Nat.nth Nat.Prime (n - 1) := by
      rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
      exact h1
    have hc : count Nat.Prime 43 = 13 := by decide
    have hp : Nat.Prime 43 := by decide
    have h3 : Nat.nth Nat.Prime (count Nat.Prime 43) = 43 := nth_count hp
    rw [hc] at h3
    omega
  have hpn_prime : Nat.Prime (Nat.nth Nat.Prime (n - 1)) :=
    Nat.nth_mem_of_infinite Nat.infinite_setOf_prime (n - 1)
  let p := Nat.nth Nat.Prime (n - 1)
  rcases (by omega : n = 14 ∨ n = 15 ∨ n = 16 ∨ n = 17 ∨ n = 18 ∨ n = 19 ∨ n = 20 ∨ n = 21 ∨ n = 22 ∨ n = 23 ∨ n = 24 ∨ n = 25 ∨ n = 26 ∨ n = 27 ∨ n = 28 ∨ n = 29 ∨ n = 30 ∨ n = 31 ∨ n = 32 ∨ n = 33 ∨ n = 34 ∨ n = 35 ∨ n = 36 ∨ n = 37 ∨ n = 38 ∨ n = 39 ∨ n = 40 ∨ n = 41 ∨ n = 42 ∨ n = 43 ∨ n = 44 ∨ n = 45 ∨ n = 46 ∨ n = 47 ∨ n ≥ 48) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | h_ge
  · exact helper_concrete_14
  · exact helper_concrete_15
  · exact helper_concrete_16
  · exact helper_concrete_17
  · exact helper_concrete_18
  · exact helper_concrete_19
  · exact helper_concrete_20
  · exact helper_concrete_21
  · exact helper_concrete_22
  · exact helper_concrete_23
  · exact helper_concrete_24
  · exact helper_concrete_25
  · exact helper_concrete_26
  · exact helper_concrete_27
  · exact helper_concrete_28
  · exact helper_concrete_29
  · exact helper_concrete_30
  · exact helper_concrete_31
  · exact helper_concrete_32
  · exact helper_concrete_33
  · exact helper_concrete_34
  · exact helper_concrete_35
  · exact helper_concrete_36
  · exact helper_concrete_37
  · exact helper_concrete_38
  · exact helper_concrete_39
  · exact helper_concrete_40
  · exact helper_concrete_41
  · exact helper_concrete_42
  · exact helper_concrete_43
  · exact helper_concrete_44
  · exact helper_concrete_45
  · exact helper_concrete_46
  · exact helper_concrete_47
  · have hp_ge_199 : p ≥ 199 := by
      have h1 : n - 1 ≥ 47 := by omega
      have h2 : Nat.nth Nat.Prime 47 ≤ Nat.nth Nat.Prime (n - 1) := by
        rw [Nat.nth_le_nth Nat.infinite_setOf_prime]
        exact h1
      have hc : count Nat.Prime 223 = 47 := by decide
      have hp : Nat.Prime 223 := by decide
      have h3 : Nat.nth Nat.Prime (count Nat.Prime 223) = 223 := nth_count hp
      rw [hc] at h3
      omega
    by_cases h_ex : (p = 333491 ∨ p = 601037 ∨ p = 1084997 ∨ p = 1525367 ∨ p = 1960391 ∨ p = 2367767 ∨ p = 2528621 ∨ p = 2533367 ∨ p = 2561681 ∨ p = 2567177 ∨ p = 2925821 ∨ p = 3322337 ∨ p = 3372221 ∨ p = 3558407 ∨ p = 3733397 ∨ p = 3754691 ∨ p = 4253267 ∨ p = 4402787 ∨ p = 4773227 ∨ p = 4876451) ∨ (p = 5108561 ∨ p = 5237651 ∨ p = 5240591 ∨ p = 5324441 ∨ p = 5499077 ∨ p = 5570417 ∨ p = 5574971 ∨ p = 5608697 ∨ p = 5840951 ∨ p = 6275177 ∨ p = 6385397 ∨ p = 7325231 ∨ p = 7410497 ∨ p = 7507937 ∨ p = 7527251 ∨ p = 7800827 ∨ p = 8139641 ∨ p = 8395061 ∨ p = 9195731 ∨ p = 9464837) ∨ (p = 9563621 ∨ p = 9572021 ∨ p = 10058177 ∨ p = 10325657 ∨ p = 10416137 ∨ p = 10661237 ∨ p = 10907021 ∨ p = 10997081 ∨ p = 11420567 ∨ p = 11445647 ∨ p = 11638631 ∨ p = 11691851 ∨ p = 11867897 ∨ p = 11984717 ∨ p = 12362951 ∨ p = 12414287 ∨ p = 12507617 ∨ p = 12935051 ∨ p = 13023737 ∨ p = 13111181) ∨ (p = 13611041 ∨ p = 13911407 ∨ p = 14396477 ∨ p = 14400767 ∨ p = 14437457 ∨ p = 14549891 ∨ p = 14728157 ∨ p = 14751701 ∨ p = 14812277 ∨ p = 14899721 ∨ p = 14940281 ∨ p = 15062891 ∨ p = 15102077 ∨ p = 15243311 ∨ p = 15346607 ∨ p = 15405317 ∨ p = 15410567 ∨ p = 15708347 ∨ p = 15715517 ∨ p = 15837947) ∨ (p = 16625591 ∨ p = 16773431 ∨ p = 16827647 ∨ p = 17695187 ∨ p = 17912261 ∨ p = 18172391 ∨ p = 19003337 ∨ p = 20217137 ∨ p = 20404817 ∨ p = 20740397 ∨ p = 21277337 ∨ p = 21390491 ∨ p = 21456047 ∨ p = 21522101 ∨ p = 21832751 ∨ p = 21977777 ∨ p = 22072487 ∨ p = 22758077 ∨ p = 23028611 ∨ p = 23362511) ∨ (p = 23429951 ∨ p = 23594171 ∨ p = 23654231 ∨ p = 23990231 ∨ p = 24004061 ∨ p = 24102977 ∨ p = 24417137 ∨ p = 24519617 ∨ p = 24731381 ∨ p = 24838481 ∨ p = 24868001 ∨ p = 25082567 ∨ p = 25187837 ∨ p = 25684781 ∨ p = 26072171 ∨ p = 26692067 ∨ p = 26769287 ∨ p = 27064547 ∨ p = 27252761 ∨ p = 27441767) ∨ (p = 27543611 ∨ p = 27648347 ∨ p = 27674741 ∨ p = 28377257 ∨ p = 28399487 ∨ p = 28435697 ∨ p = 28537121 ∨ p = 28869011 ∨ p = 29185811 ∨ p = 29282711 ∨ p = 29333387 ∨ p = 29479181 ∨ p = 29570267 ∨ p = 30554201 ∨ p = 30624947 ∨ p = 30671087 ∨ p = 30691937 ∨ p = 30806507 ∨ p = 30825647 ∨ p = 30932411) ∨ (p = 30975557 ∨ p = 31102781 ∨ p = 31123637 ∨ p = 31278251 ∨ p = 31316267 ∨ p = 31384007 ∨ p = 31626977 ∨ p = 31965821 ∨ p = 31999271 ∨ p = 32186237 ∨ p = 32188691 ∨ p = 32381807 ∨ p = 32571557 ∨ p = 32940221 ∨ p = 33090371 ∨ p = 33252377 ∨ p = 33502367 ∨ p = 34011821 ∨ p = 34778657 ∨ p = 35077241) ∨ (p = 35184971 ∨ p = 35347511 ∨ p = 35598581 ∨ p = 35604551 ∨ p = 35831921 ∨ p = 36018107 ∨ p = 36155501 ∨ p = 36256037 ∨ p = 36474827 ∨ p = 36531221 ∨ p = 37631411 ∨ p = 37837841 ∨ p = 37989431 ∨ p = 38250461 ∨ p = 38606957 ∨ p = 38939267 ∨ p = 39965267 ∨ p = 40305761 ∨ p = 41194997 ∨ p = 41219597) ∨ (p = 42124541 ∨ p = 42521651 ∨ p = 43149257 ∨ p = 43746737 ∨ p = 44028197 ∨ p = 44422991 ∨ p = 44496581 ∨ p = 45154841 ∨ p = 45181307 ∨ p = 45695717 ∨ p = 46036577 ∨ p = 47009507 ∨ p = 47509661 ∨ p = 47876681 ∨ p = 48363167 ∨ p = 48606911 ∨ p = 48891107 ∨ p = 48957341 ∨ p = 49938101 ∨ p = 50227271) ∨ (p = 50921021 ∨ p = 51090497 ∨ p = 51256481 ∨ p = 51344387 ∨ p = 51804407 ∨ p = 52119491 ∨ p = 52325081 ∨ p = 52340537 ∨ p = 52412027 ∨ p = 52639877 ∨ p = 52742771 ∨ p = 53487881 ∨ p = 53949167 ∨ p = 54029147 ∨ p = 54758591 ∨ p = 54828197 ∨ p = 54898511 ∨ p = 55040261 ∨ p = 55477517 ∨ p = 55534751) ∨ (p = 55793951 ∨ p = 55839851 ∨ p = 56188877 ∨ p = 56406431 ∨ p = 56533571 ∨ p = 56719571 ∨ p = 57279767 ∨ p = 57330017 ∨ p = 57345677 ∨ p = 57685151 ∨ p = 57867191 ∨ p = 57966761 ∨ p = 58073837 ∨ p = 58095041 ∨ p = 58388567 ∨ p = 58636967 ∨ p = 58759397 ∨ p = 58803581 ∨ p = 58928687 ∨ p = 59427617) ∨ (p = 60307757 ∨ p = 60345821 ∨ p = 60425861 ∨ p = 60765071 ∨ p = 60957497 ∨ p = 61187507 ∨ p = 61251887 ∨ p = 62331251 ∨ p = 62423651 ∨ p = 62898191 ∨ p = 62913437 ∨ p = 63211397 ∨ p = 63627491 ∨ p = 64558931 ∨ p = 65510171 ∨ p = 65625731 ∨ p = 65812127 ∨ p = 66091757 ∨ p = 66376757 ∨ p = 67374467) ∨ (p = 67538687 ∨ p = 68302601 ∨ p = 68583917 ∨ p = 69340487 ∨ p = 70316627 ∨ p = 70553501 ∨ p = 70688201 ∨ p = 70876697 ∨ p = 71026721 ∨ p = 71396177 ∨ p = 71483801 ∨ p = 71848871 ∨ p = 71961971 ∨ p = 72028037 ∨ p = 72172481 ∨ p = 72739211 ∨ p = 72960047 ∨ p = 73188287 ∨ p = 74028167 ∨ p = 74084597) ∨ (p = 74497331 ∨ p = 74788601 ∨ p = 74904101 ∨ p = 75031337 ∨ p = 75231041 ∨ p = 75287867 ∨ p = 75864641 ∨ p = 76488017 ∨ p = 76724861 ∨ p = 77000447 ∨ p = 77287907 ∨ p = 77389511 ∨ p = 77737811 ∨ p = 78109307 ∨ p = 78982721 ∨ p = 79052651 ∨ p = 79782707 ∨ p = 80183417 ∨ p = 80382551 ∨ p = 80443787) ∨ (p = 80654927 ∨ p = 80756717 ∨ p = 80827781 ∨ p = 81332831 ∨ p = 81388751 ∨ p = 81642287 ∨ p = 81682817 ∨ p = 81715421 ∨ p = 81806897 ∨ p = 82163591 ∨ p = 82196327 ∨ p = 82220051 ∨ p = 82249691 ∨ p = 82351121 ∨ p = 82416401 ∨ p = 82477667 ∨ p = 82510511 ∨ p = 82642577 ∨ p = 82717751 ∨ p = 83185847) ∨ (p = 83327261 ∨ p = 83406287 ∨ p = 85425227 ∨ p = 85649147 ∨ p = 85668881 ∨ p = 85899257 ∨ p = 86237687 ∨ p = 86604767 ∨ p = 87829031 ∨ p = 88516511 ∨ p = 88536647 ∨ p = 88645091 ∨ p = 88746731 ∨ p = 88971131 ∨ p = 89149871 ∨ p = 89156357 ∨ p = 89521967 ∨ p = 89784677 ∨ p = 90336371 ∨ p = 90404387) ∨ (p = 90468797 ∨ p = 92280647 ∨ p = 92460827 ∨ p = 92553737 ∨ p = 92661971 ∨ p = 92683751 ∨ p = 92955407 ∨ p = 93086291 ∨ p = 94014647 ∨ p = 94142297 ∨ p = 94410047 ∨ p = 94606277 ∨ p = 94670657 ∨ p = 94922141 ∨ p = 95134211 ∨ p = 95217581 ∨ p = 95479061 ∨ p = 95494307 ∨ p = 96124487 ∨ p = 96519167) ∨ (p = 96802787 ∨ p = 96850991 ∨ p = 97062851 ∨ p = 97675157 ∨ p = 97939607 ∨ p = 98937857 ∨ p = 99396611 ∨ p = 99509561 ∨ p = 99539591 ∨ p = 99769487 ∨ p = 99848657 ∨ p = 99891917)
    · exact helper_exceptions p n (by omega) h_ex
    by_cases h_mod_helper_mod_3_to_11 : p % 3 = 1 ∨ p % 5 = 3 ∨ p % 5 = 4 ∨ p % 7 = 1 ∨ p % 7 = 2 ∨ p % 7 = 5 ∨ p % 11 = 2 ∨ p % 11 = 3 ∨ p % 11 = 5 ∨ p % 11 = 9 ∨ p % 11 = 10
    · exact helper_mod_3_to_11 p n h_ge hp_ge_199 h_mod_helper_mod_3_to_11
    by_cases h_mod_helper_mod_13_to_19 : p % 13 = 1 ∨ p % 13 = 6 ∨ p % 13 = 7 ∨ p % 13 = 9 ∨ p % 13 = 10 ∨ p % 13 = 11 ∨ p % 17 = 4 ∨ p % 17 = 5 ∨ p % 17 = 9 ∨ p % 17 = 11 ∨ p % 17 = 12 ∨ p % 17 = 13 ∨ p % 17 = 14 ∨ p % 17 = 15 ∨ p % 19 = 1 ∨ p % 19 = 4 ∨ p % 19 = 5 ∨ p % 19 = 7 ∨ p % 19 = 8 ∨ p % 19 = 13 ∨ p % 19 = 15 ∨ p % 19 = 17 ∨ p % 19 = 18
    · exact helper_mod_13_to_19 p n h_ge hp_ge_199 h_mod_helper_mod_13_to_19
    by_cases h_mod_helper_mod_23_to_31 : p % 23 = 2 ∨ p % 23 = 3 ∨ p % 23 = 4 ∨ p % 23 = 5 ∨ p % 23 = 6 ∨ p % 23 = 11 ∨ p % 23 = 13 ∨ p % 23 = 16 ∨ p % 23 = 17 ∨ p % 23 = 20 ∨ p % 23 = 21 ∨ p % 29 = 2 ∨ p % 29 = 6 ∨ p % 29 = 9 ∨ p % 29 = 13 ∨ p % 29 = 15 ∨ p % 29 = 16 ∨ p % 29 = 17 ∨ p % 29 = 18 ∨ p % 29 = 21 ∨ p % 29 = 22 ∨ p % 29 = 23 ∨ p % 29 = 26 ∨ p % 29 = 27 ∨ p % 29 = 28 ∨ p % 31 = 1 ∨ p % 31 = 3 ∨ p % 31 = 4 ∨ p % 31 = 6 ∨ p % 31 = 7 ∨ p % 31 = 8 ∨ p % 31 = 11 ∨ p % 31 = 14 ∨ p % 31 = 19 ∨ p % 31 = 20 ∨ p % 31 = 21 ∨ p % 31 = 23 ∨ p % 31 = 25 ∨ p % 31 = 29 ∨ p % 31 = 30
    · exact helper_mod_23_to_31 p n h_ge hp_ge_199 h_mod_helper_mod_23_to_31
    by_cases h_mod_helper_mod_37_to_47 : p % 37 = 1 ∨ p % 37 = 2 ∨ p % 37 = 3 ∨ p % 37 = 7 ∨ p % 37 = 12 ∨ p % 37 = 16 ∨ p % 37 = 17 ∨ p % 37 = 18 ∨ p % 37 = 19 ∨ p % 37 = 21 ∨ p % 37 = 24 ∨ p % 37 = 25 ∨ p % 37 = 27 ∨ p % 37 = 28 ∨ p % 37 = 29 ∨ p % 37 = 31 ∨ p % 37 = 32 ∨ p % 37 = 35 ∨ p % 41 = 6 ∨ p % 41 = 8 ∨ p % 41 = 10 ∨ p % 41 = 11 ∨ p % 41 = 13 ∨ p % 41 = 15 ∨ p % 41 = 21 ∨ p % 41 = 22 ∨ p % 41 = 23 ∨ p % 41 = 26 ∨ p % 41 = 27 ∨ p % 41 = 29 ∨ p % 41 = 30 ∨ p % 41 = 31 ∨ p % 41 = 32 ∨ p % 41 = 33 ∨ p % 41 = 35 ∨ p % 41 = 36 ∨ p % 41 = 39 ∨ p % 41 = 40 ∨ p % 43 = 1 ∨ p % 43 = 2 ∨ p % 43 = 5 ∨ p % 43 = 7 ∨ p % 43 = 10 ∨ p % 43 = 11 ∨ p % 43 = 13 ∨ p % 43 = 14 ∨ p % 43 = 16 ∨ p % 43 = 18 ∨ p % 43 = 19 ∨ p % 43 = 23 ∨ p % 43 = 29 ∨ p % 43 = 30 ∨ p % 43 = 31 ∨ p % 43 = 33 ∨ p % 43 = 37 ∨ p % 43 = 38 ∨ p % 43 = 39 ∨ p % 43 = 40 ∨ p % 43 = 41 ∨ p % 47 = 3 ∨ p % 47 = 4 ∨ p % 47 = 5 ∨ p % 47 = 6 ∨ p % 47 = 8 ∨ p % 47 = 9 ∨ p % 47 = 10 ∨ p % 47 = 11 ∨ p % 47 = 12 ∨ p % 47 = 17 ∨ p % 47 = 22 ∨ p % 47 = 23 ∨ p % 47 = 25 ∨ p % 47 = 27 ∨ p % 47 = 31 ∨ p % 47 = 32 ∨ p % 47 = 34 ∨ p % 47 = 35 ∨ p % 47 = 38 ∨ p % 47 = 41 ∨ p % 47 = 42 ∨ p % 47 = 43 ∨ p % 47 = 45
    · exact helper_mod_37_to_47 p n h_ge hp_ge_199 h_mod_helper_mod_37_to_47
    sorry
theorem oeis_117531_conjecture_0 (n : ℕ) (h : n > 13) : a n < n := by
  unfold a
  have h_card : Finset.card (Finset.Icc 1 n) = n := Nat.card_Icc 1 n
  have h_ex : ∃ k ∈ Finset.Icc 1 n, ¬ Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1)) := helper n h
  rcases h_ex with ⟨k, hk_in, hk_not_prime⟩
  have h_lt := card_filter_lt_card_of_exists_not (Finset.Icc 1 n) (fun k : ℕ => Nat.Prime (k ^ 2 - k + Nat.nth Nat.Prime (n - 1))) k hk_in hk_not_prime
  rw [h_card] at h_lt
  exact h_lt