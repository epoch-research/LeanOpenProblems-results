import FormalConjecturesUtil

/-!
A formal degree-eight collision. In particular, even imposing a digit sum
smaller than the base does not repair the base-two Eisenstein construction.
This is NOT a disproof of Erdős 773.
-/
namespace Erdos773.FormalHistogram

private def words : Fin 4 → Fin 9 → ℕ :=
  ![![6,18,4,14,22,6,2,4,1],
    ![22,14,6,18,6,4,4,2,1],
    ![18,6,4,22,14,6,4,2,1],
    ![14,22,6,6,18,4,2,4,1]]

private def val (B : ℕ) (j : Fin 4) : ℕ := ∑ i : Fin 9, words j i * B ^ i.val

lemma conditions : ∀ j : Fin 4,
    words j 8 = 1 ∧ words j 0 % 4 = 2 ∧
    (∀ i : Fin 9, i.val < 8 → 2 ∣ words j i) ∧
    (∑ i : Fin 9, words j i) = 77 ∧
    (∑ i : Fin 9, (words j i) ^ 2) = 1113 := by decide

lemma digit_bounds (B : ℕ) (hB : 77 < B) (j : Fin 4) (i : Fin 9) :
    2 * words j i < B := by
  have hb : ∀ j : Fin 4, ∀ i : Fin 9, words j i ≤ 22 := by decide
  have := hb j i
  omega

lemma histograms : ∀ j : Fin 4, ∀ n ∈ Finset.range 23,
    ((Finset.univ : Finset (Fin 9)).filter (fun i => words j i = n)).card =
    ((Finset.univ : Finset (Fin 9)).filter (fun i => words 0 i = n)).card := by decide

lemma collision (B : ℕ) : val B 0 ^ 2 + val B 1 ^ 2 = val B 2 ^ 2 + val B 3 ^ 2 := by
  simp [val, words, Fin.sum_univ_succ]
  ring

lemma nontrivial (B : ℕ) (hB : 77 < B) :
    val B 0 ≠ val B 2 ∧ val B 0 ≠ val B 3 := by
  have hm (j : Fin 4) : val B j % B = words j 0 := by
    fin_cases j <;> simp [val, Fin.sum_univ_succ, words, Nat.add_mod, Nat.mul_mod, Nat.pow_succ]
    all_goals exact Nat.mod_eq_of_lt (by omega)
  constructor <;> intro h
  · have hh : val B 0 % B = val B 2 % B := congrArg (· % B) h
    rw [hm 0, hm 2] at hh
    change (6 : ℕ) = 18 at hh
    omega
  · have hh : val B 0 % B = val B 3 % B := congrArg (· % B) h
    rw [hm 0, hm 3] at hh
    change (6 : ℕ) = 14 at hh
    omega

lemma not_sidon (B : ℕ) (hB : 77 < B) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image (fun j => val B j ^ 2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : val B j ^ 2 ∈
      (((Finset.univ : Finset (Fin 4)).image (fun j => val B j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision B) with h | h
  · exact (nontrivial B hB).1 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)
  · exact (nontrivial B hB).2 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)

lemma primitive_example :
    Nat.gcd (Nat.gcd (val 80 0) (val 80 1))
      (Nat.gcd (val 80 2) (val 80 3)) = 2 := by decide

lemma digit_sum_lt_base (B : ℕ) (hB : 77 < B) (j : Fin 4) :
    (∑ i : Fin 9, words j i) < B := by
  rw [(conditions j).2.2.2.1]
  exact hB

lemma bezout (B : ℕ) :
    (15 * B + 47) * val B 2 + (27 * B + 39) * val B 3 =
      308 + ((29 * B + 45) * val B 0 + (13 * B + 37) * val B 1) := by
  simp [val, words, Fin.sum_univ_succ]
  ring

lemma val_mod_of_dvd (B m : ℕ) (hm : m ∣ B) (j : Fin 4) :
    val B j % m = words j 0 % m := by
  simp [val, words, Fin.sum_univ_succ, Nat.add_mod, Nat.mul_mod,
    Nat.pow_succ, Nat.mod_eq_zero_of_dvd hm]

section
attribute [local irreducible] val
set_option maxHeartbeats 1000000

lemma primitive_family (t : ℕ) :
    Nat.gcd (Nat.gcd (val (308 * (t + 1)) 0) (val (308 * (t + 1)) 1))
      (Nat.gcd (val (308 * (t + 1)) 2) (val (308 * (t + 1)) 3)) = 2 := by
  let B := 308 * (t + 1)
  let g := Nat.gcd (Nat.gcd (val B 0) (val B 1)) (Nat.gcd (val B 2) (val B 3))
  have h0 : g ∣ val B 0 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have h1 : g ∣ val B 1 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have h2 : g ∣ val B 2 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have h3 : g ∣ val B 3 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hl : g ∣ (15 * B + 47) * val B 2 + (27 * B + 39) * val B 3 :=
    dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h3 _)
  have hr : g ∣ (29 * B + 45) * val B 0 + (13 * B + 37) * val B 1 :=
    dvd_add (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right h1 _)
  rw [bezout] at hl
  have hg308 : g ∣ 308 := (Nat.dvd_add_iff_left hr).mpr hl
  have hB : 308 ∣ B := ⟨t + 1, rfl⟩
  have hm : val B 0 % 308 = 6 := by
    rw [val_mod_of_dvd B 308 hB]
    decide
  have hg6 : g ∣ 6 := by
    rw [← hm]
    exact (Nat.dvd_mod_iff hg308).mpr h0
  have hg2 : g ∣ 2 := by
    have hh := Nat.dvd_gcd hg308 hg6
    norm_num at hh
    exact hh
  have hBeven : 2 ∣ B := dvd_trans (by decide : 2 ∣ 308) hB
  have he (j : Fin 4) : 2 ∣ val B j := by
    apply Nat.dvd_of_mod_eq_zero
    rw [val_mod_of_dvd B 2 hBeven]
    fin_cases j <;> decide
  have h2g : 2 ∣ g := Nat.dvd_gcd (Nat.dvd_gcd (he 0) (he 1)) (Nat.dvd_gcd (he 2) (he 3))
  exact Nat.dvd_antisymm hg2 h2g

end

#print axioms not_sidon
#print axioms primitive_family
end Erdos773.FormalHistogram
