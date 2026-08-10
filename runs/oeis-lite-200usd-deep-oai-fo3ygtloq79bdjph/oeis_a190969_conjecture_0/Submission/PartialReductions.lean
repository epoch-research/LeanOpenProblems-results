import FormalConjectures.Util.ProblemImports

def a : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 => 5 * a (n + 1) - 8 * a n

open Finset Nat
open scoped BigOperators

def b : ℕ → ℤ
| 0 => 0
| 1 => 45
| n + 2 => -47 * b (n + 1) - 4096 * b n

lemma central_choose_dvd_of_half {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    p ∣ (2 * k).choose k := by
  apply hp.dvd_choose (a := k) (b := 2 * k)
  · exact hk
  · have hsub : 2 * k - k = k := by omega
    simpa [hsub] using hk
  · exact hhalf

lemma cube_dvd_of_dvd {p c : ℕ} (h : p ∣ c) : p ^ 3 ∣ c ^ 3 := by
  rcases h with ⟨d, rfl⟩
  use d ^ 3
  ring

lemma central_choose_cube_dvd_of_half {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    p ^ 3 ∣ ((2 * k).choose k) ^ 3 := by
  exact cube_dvd_of_dvd (central_choose_dvd_of_half hp hk hhalf)

lemma central_choose_cast_cube_eq_zero_zmod_pow2 {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    (((2 * k).choose k : ℕ) : ZMod (p ^ 2)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact (pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans
    (central_choose_cube_dvd_of_half hp hk hhalf)

lemma central_choose_cast_cube_eq_zero_zmod_pow3 {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    (((2 * k).choose k : ℕ) : ZMod (p ^ 3)) ^ 3 = 0 := by
  rw [← Nat.cast_pow, ZMod.natCast_eq_zero_iff]
  exact central_choose_cube_dvd_of_half hp hk hhalf

lemma original_upper_half_term_zero_pow2 {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    (let num : ZMod (p ^ 2) := (a (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
     let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
     num * den⁻¹) = 0 := by
  dsimp
  rw [central_choose_cast_cube_eq_zero_zmod_pow2 hp hk hhalf]
  simp

lemma original_upper_half_term_zero_pow3 {p k : ℕ} (hp : p.Prime) (hk : k < p) (hhalf : p ≤ 2 * k) :
    (let num : ZMod (p ^ 3) := (a (4 * k) : ZMod (p ^ 3)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3
     let den : ZMod (p ^ 3) := ((-4096 : ℤ) : ZMod (p ^ 3)) ^ k
     num * den⁻¹) = 0 := by
  dsimp
  rw [central_choose_cast_cube_eq_zero_zmod_pow3 hp hk hhalf]
  simp



def c (n : ℕ) : ℤ := a (n + 8) + 47 * a (n + 4) + 4096 * a n

lemma c_succ_succ (n : ℕ) : c (n + 2) = 5 * c (n + 1) - 8 * c n := by
  unfold c
  -- normalize all offsets so the defining recurrence for `a` unfolds
  change a ((n + 8) + 2) + 47 * a ((n + 4) + 2) + 4096 * a (n + 2) =
    5 * (a ((n + 7) + 2) + 47 * a ((n + 3) + 2) + 4096 * a (n + 1)) -
      8 * (a (n + 8) + 47 * a (n + 4) + 4096 * a n)
  simp [a]
  ring

lemma c_eq_zero (n : ℕ) : c n = 0 := by
  suffices h : c n = 0 ∧ c (n + 1) = 0 from h.1
  induction n with
  | zero => norm_num [c, a]
  | succ n ih =>
      exact ⟨ih.2, by rw [c_succ_succ n, ih.1, ih.2]; ring⟩

lemma a_add_eight (n : ℕ) : a (n + 8) = -47 * a (n + 4) - 4096 * a n := by
  have h := c_eq_zero n
  unfold c at h
  omega

lemma a_four_mul_eq_b_pair (k : ℕ) : a (4 * k) = b k ∧ a (4 * (k + 1)) = b (k + 1) := by
  induction k with
  | zero => norm_num [a, b]
  | succ k ih =>
      refine ⟨ih.2, ?_⟩
      rw [b]
      have h := a_add_eight (4 * k)
      have h1 : 4 * (k + 1) = 4 * k + 4 := by omega
      have h2 : 4 * (k + 2) = 4 * k + 8 := by omega
      rw [h2, h, ← h1, ih.2, ih.1]

lemma a_four_mul_eq_b (k : ℕ) : a (4 * k) = b k :=
  (a_four_mul_eq_b_pair k).1


lemma sum_eq_filter_lower_pow2 (p : ℕ) (hp : p.Prime) :
    (range p).sum (fun k =>
      let num : ZMod (p ^ 2) := (a (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
      let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
      num * den⁻¹) =
    ((range p).filter (fun k => 2 * k < p)).sum (fun k =>
      let num : ZMod (p ^ 2) := (a (4 * k) : ZMod (p ^ 2)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 2)) ^ 3
      let den : ZMod (p ^ 2) := ((-4096 : ℤ) : ZMod (p ^ 2)) ^ k
      num * den⁻¹) := by
  rw [← sum_filter_add_sum_filter_not (s := range p) (p := fun k => 2 * k < p)]
  simp only [add_eq_left]
  apply sum_eq_zero
  intro k hk
  simp only [mem_filter, mem_range, not_lt] at hk
  exact original_upper_half_term_zero_pow2 hp hk.1 hk.2

lemma sum_eq_filter_lower_pow3 (p : ℕ) (hp : p.Prime) :
    (range p).sum (fun k =>
      let num : ZMod (p ^ 3) := (a (4 * k) : ZMod (p ^ 3)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3
      let den : ZMod (p ^ 3) := ((-4096 : ℤ) : ZMod (p ^ 3)) ^ k
      num * den⁻¹) =
    ((range p).filter (fun k => 2 * k < p)).sum (fun k =>
      let num : ZMod (p ^ 3) := (a (4 * k) : ZMod (p ^ 3)) * ((choose (2 * k) k : ℕ) : ZMod (p ^ 3)) ^ 3
      let den : ZMod (p ^ 3) := ((-4096 : ℤ) : ZMod (p ^ 3)) ^ k
      num * den⁻¹) := by
  rw [← sum_filter_add_sum_filter_not (s := range p) (p := fun k => 2 * k < p)]
  simp only [add_eq_left]
  apply sum_eq_zero
  intro k hk
  simp only [mem_filter, mem_range, not_lt] at hk
  exact original_upper_half_term_zero_pow3 hp hk.1 hk.2
