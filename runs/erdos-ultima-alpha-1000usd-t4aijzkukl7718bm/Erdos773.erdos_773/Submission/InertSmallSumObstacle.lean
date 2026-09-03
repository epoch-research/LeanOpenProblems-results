import FormalConjecturesUtil

/-!
A fixed-degree, unbounded-base obstruction to the base-three digit construction.
All words have the same histogram, leading digit 1, lower digits divisible by 3,
and constant digits congruent to 3 modulo 9. The common digit sum is less than
the base. Their squares nevertheless collide nontrivially.
This does NOT disprove Erdős 773.
-/
namespace Erdos773.InertSmallSum
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

private def base (t : ℕ) : ℕ := 864 * (t + 6)

private def words (t : ℕ) : Fin 4 → Fin 17 → ℕ :=
  ![![21,0,219,0,480,0,219,0,309,0,1056,135*(t+6),0,297*(t+6),0,0,1],
    ![309,0,219,0,1056,0,219,0,21,0,480,297*(t+6),0,135*(t+6),0,0,1],
    ![219,0,21,0,480,0,309,0,219,0,1056,297*(t+6),0,135*(t+6),0,0,1],
    ![219,0,309,0,1056,0,21,0,219,0,480,135*(t+6),0,297*(t+6),0,0,1]]

private def val (t : ℕ) (j : Fin 4) : ℕ :=
  ∑ i : Fin 17, words t j i * (base t) ^ i.val

lemma leading (t : ℕ) (j : Fin 4) : words t j 16 = 1 := by
  fin_cases j <;> rfl

lemma constant_mod (t : ℕ) (j : Fin 4) : words t j 0 % 9 = 3 := by
  fin_cases j <;> norm_num [words]

lemma lower_divisible (t : ℕ) (j : Fin 4) (i : Fin 17) (hi : i.val < 16) :
    3 ∣ words t j i := by
  have h135 : 3 ∣ 135 * (t + 6) := dvd_mul_of_dvd_left (by decide) _
  have h297 : 3 ∣ 297 * (t + 6) := dvd_mul_of_dvd_left (by decide) _
  fin_cases j <;> fin_cases i <;> simp [words, h135, h297] at hi ⊢

lemma digit_sum (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 17, words t j i) = 2305 + 432 * (t + 6) := by
  fin_cases j <;> simp [words, Fin.sum_univ_succ] <;> ring

lemma digit_norm (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 17, (words t j i) ^ 2) = 1537381 + 106434 * (t + 6) ^ 2 := by
  fin_cases j <;> norm_num [words, Fin.sum_univ_succ, mul_pow] <;> omega

lemma conditions (t : ℕ) (j : Fin 4) :
    words t j 16 = 1 ∧ words t j 0 % 9 = 3 ∧
    (∀ i : Fin 17, i.val < 16 → 3 ∣ words t j i) ∧
    (∑ i : Fin 17, words t j i) = 2305 + 432 * (t + 6) ∧
    (∑ i : Fin 17, (words t j i) ^ 2) = 1537381 + 106434 * (t + 6) ^ 2 :=
  ⟨leading t j, constant_mod t j, lower_divisible t j, digit_sum t j, digit_norm t j⟩

lemma digit_bounds (t : ℕ) (j : Fin 4) (i : Fin 17) :
    2 * words t j i < base t := by
  fin_cases j <;> fin_cases i <;> simp [words, base] <;> omega

lemma digit_sum_lt_base (t : ℕ) (j : Fin 4) :
    (∑ i : Fin 17, words t j i) < base t := by
  rw [(conditions t j).2.2.2.1]
  dsimp [base]
  omega

lemma histogram_perm (t : ℕ) (j : Fin 4) :
    List.Perm (List.ofFn (words t j)) (List.ofFn (words t 0)) := by
  apply List.perm_iff_count.mpr
  intro a
  fin_cases j <;> simp [words, List.ofFn_succ, List.count_cons] <;> omega

lemma collision (t : ℕ) : val t 0 ^ 2 + val t 1 ^ 2 = val t 2 ^ 2 + val t 3 ^ 2 := by
  simp [val, words, Fin.sum_univ_succ, base]
  ring

lemma nontrivial (t : ℕ) : val t 0 ≠ val t 2 ∧ val t 0 ≠ val t 3 := by
  have hm (j : Fin 4) : val t j % base t = words t j 0 := by
    fin_cases j <;> simp [val, Fin.sum_univ_succ, words, Nat.add_mod, Nat.mul_mod, Nat.pow_succ]
    all_goals exact Nat.mod_eq_of_lt (by dsimp [base]; omega)
  constructor <;> intro h
  · have hh : val t 0 % base t = _ := congrArg (· % base t) h
    dsimp only at hh
    rw [hm 0, hm 2] at hh
    change (21 : ℕ) = 219 at hh
    omega
  · have hh : val t 0 % base t = _ := congrArg (· % base t) h
    dsimp only at hh
    rw [hm 0, hm 3] at hh
    change (21 : ℕ) = 219 at hh
    omega

lemma not_sidon (t : ℕ) :
    ¬ IsSidon (((Finset.univ : Finset (Fin 4)).image (fun j => val t j ^ 2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : val t j ^ 2 ∈
      (((Finset.univ : Finset (Fin 4)).image (fun j => val t j ^ 2)) : Set ℕ) := by
    simp only [Finset.mem_coe, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, rfl⟩
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t) with h | h
  · exact (nontrivial t).1 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)
  · exact (nontrivial t).2 (Nat.pow_left_injective (by decide : 2 ≠ 0) h.1)

lemma primitive_example :
    Nat.gcd (Nat.gcd (val 0 0) (val 0 1)) (Nat.gcd (val 0 2) (val 0 3)) = 3 := by
  decide +kernel

lemma bezout (t : ℕ) :
    (43333 * base t ^ 2 + 985120 * base t ^ 4) * val t 0 + 226836 * val t 3 =
      47806848 + 16073 * val t 0 + (4092 + 184656 * base t ^ 2) * val t 1 +
        (1225 + 43387 * base t ^ 2 + 985120 * base t ^ 4) * val t 2 := by
  simp [val, words, Fin.sum_univ_succ, base]
  ring

lemma val_mod_of_dvd (t m : ℕ) (hm : m ∣ base t) (j : Fin 4) :
    val t j % m = words t j 0 % m := by
  simp [val, words, Fin.sum_univ_succ, Nat.add_mod, Nat.mul_mod,
    Nat.pow_succ, Nat.mod_eq_zero_of_dvd hm]

section
attribute [local irreducible] val

lemma primitive_family (u : ℕ) :
    let t := 55332 * u + 55326
    Nat.gcd (Nat.gcd (val t 0) (val t 1)) (Nat.gcd (val t 2) (val t 3)) = 3 := by
  dsimp only
  let t := 55332 * u + 55326
  let g := Nat.gcd (Nat.gcd (val t 0) (val t 1)) (Nat.gcd (val t 2) (val t 3))
  have h0 : g ∣ val t 0 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
  have h1 : g ∣ val t 1 := (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
  have h2 : g ∣ val t 2 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have h3 : g ∣ val t 3 := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have hl : g ∣ (43333 * base t ^ 2 + 985120 * base t ^ 4) * val t 0 +
      226836 * val t 3 :=
    dvd_add (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right h3 _)
  have hr : g ∣ 16073 * val t 0 + (4092 + 184656 * base t ^ 2) * val t 1 +
      (1225 + 43387 * base t ^ 2 + 985120 * base t ^ 4) * val t 2 :=
    dvd_add (dvd_add (dvd_mul_of_dvd_right h0 _) (dvd_mul_of_dvd_right h1 _))
      (dvd_mul_of_dvd_right h2 _)
  rw [bezout, add_assoc, add_assoc] at hl
  have hgC : g ∣ 47806848 := (Nat.dvd_add_iff_left (by simpa only [add_assoc] using hr)).mpr hl
  have hB : 47806848 ∣ base t := by
    refine ⟨u + 1, ?_⟩
    dsimp [base,t]
    ring
  have hm : val t 0 % 47806848 = 21 := by
    rw [val_mod_of_dvd t 47806848 hB]
    rfl
  have hg21 : g ∣ 21 := by
    rw [← hm]
    exact (Nat.dvd_mod_iff hgC).mpr h0
  have hg3 : g ∣ 3 := by
    have hh := Nat.dvd_gcd hgC hg21
    norm_num at hh
    exact hh
  have hB3 : 3 ∣ base t := dvd_trans (by decide : 3 ∣ 47806848) hB
  have he (j : Fin 4) : 3 ∣ val t j := by
    apply Nat.dvd_of_mod_eq_zero
    rw [val_mod_of_dvd t 3 hB3]
    fin_cases j <;> norm_num [words]
  have h3g : 3 ∣ g := Nat.dvd_gcd (Nat.dvd_gcd (he 0) (he 1)) (Nat.dvd_gcd (he 2) (he 3))
  exact Nat.dvd_antisymm hg3 h3g

end

#print axioms conditions
#print axioms histogram_perm
#print axioms not_sidon
#print axioms primitive_example
#print axioms primitive_family
end Erdos773.InertSmallSum
