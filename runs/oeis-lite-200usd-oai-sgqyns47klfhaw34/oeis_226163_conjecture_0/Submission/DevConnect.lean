import FormalConjectures.Dev.Zero
import FormalConjectures.Dev.One

open Matrix Nat Int Finset MulChar
open scoped BigOperators

/-- Local copy for development; final proof will use the existing definition in Spec.lean. -/
noncomputable def A226163 (n : ℕ) : ℤ :=
  if h : n < 2 then 0 else
  let p : ℕ := Nat.nth Nat.Prime (n - 1)
  let m : ℕ := (p - 1) / 2
  let C : ℤ := m.factorial.cast
  let M : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    let i' : ℤ := (i.val + 1).cast
    let j' : ℤ := (j.val + 1).cast
    let arg : ℤ := i' * i' - C * j'
    jacobiSym arg p
  M.det


noncomputable def origIntMatrix (p m : ℕ) : Matrix (Fin m) (Fin m) ℤ := fun i j =>
  let Cint : ℤ := m.factorial.cast
  let ii : ℤ := (i.val + 1).cast
  let jj : ℤ := (j.val + 1).cast
  jacobiSym (ii * ii - Cint * jj) p

lemma zmod_prod_y_eq_factorial {p m : ℕ} :
    (∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p))) = ((m.factorial : ℕ) : ZMod p) := by
  have hprod_nat : (∏ j : Fin m, (j.val + 1 : ℕ)) = m.factorial := by
    rw [Fin.prod_univ_eq_prod_range (fun j : ℕ => j + 1) m]
    exact Finset.prod_range_add_one_eq_factorial m
  rw [← Finset.prod_natCast, hprod_nat]

lemma zmod_ringChar_ne_two_of_prime_mod_four_eq_three {p : ℕ} (hp4 : p % 4 = 3) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  intro h
  rw [h] at hp4
  norm_num at hp4

lemma zmod_quadraticChar_neg_one_of_prime_mod_four_eq_three {p : ℕ} [Fact p.Prime]
    (hp4 : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := zmod_ringChar_ne_two_of_prime_mod_four_eq_three hp4
  rw [quadraticChar_neg_one hF, ZMod.card]
  exact ZMod.χ₄_nat_three_mod_four hp4

lemma m_odd_of_p_mod_four_three {p m : ℕ} (hp : p = 2*m+1) (hp4 : p % 4 = 3) : Odd m := by
  have hdiv := (Nat.div_add_mod p 4).symm
  rw [hp4] at hdiv
  refine ⟨p / 4, ?_⟩
  rw [hp] at hdiv
  omega

lemma p_eq_two_mul_half_add_one_of_prime_ne_two {p : ℕ} (hpprime : p.Prime) (hpne2 : p ≠ 2) :
    p = 2 * ((p - 1) / 2) + 1 := by
  have hodd : Odd p := hpprime.odd_of_ne_two hpne2
  rcases hodd with ⟨k, hk⟩
  rw [hk]
  have : (k + k + 1 - 1) / 2 = k := by omega
  omega

lemma cast_origInt_to_rat (p m : ℕ) :
    (((origIntMatrix p m).det : ℤ) : ℚ) = (origRatMatrix p m).det := by
  rw [Int.cast_det]
  rfl

lemma cast_origInt_to_zmod_power {p m : ℕ} [Fact p.Prime] (hp : p = 2*m+1) :
    Matrix.det (((Int.castRingHom (ZMod p)).mapMatrix (origIntMatrix p m))) =
    Matrix.det (fun i j : Fin m =>
      ((((i.val + 1 : ℕ) : ZMod p)^2) - ((m.factorial : ℕ) : ZMod p) * ((j.val + 1 : ℕ) : ZMod p)) ^ m) := by
  congr 1
  ext i j
  dsimp [origIntMatrix]
  rw [← jacobiSym.legendreSym.to_jacobiSym]
  have hpdiv : p / 2 = m := by rw [hp]; omega
  have he := legendreSym.eq_pow p (((i.val + 1 : ℤ) * (i.val + 1 : ℤ) - (m.factorial : ℤ) * (j.val + 1 : ℤ)))
  rw [hpdiv] at he
  rw [he]
  congr 1
  norm_num [sq]

lemma nth_prime_of_ge_one_ne_two {k : ℕ} (hk : 1 ≤ k) : Nat.nth Nat.Prime k ≠ 2 := by
  have hge : 3 ≤ Nat.nth Nat.Prime k := by
    calc
      3 = Nat.nth Nat.Prime 1 := by norm_num [Nat.nth_prime_one_eq_three]
      _ ≤ Nat.nth Nat.Prime k := (Nat.nth_le_nth Nat.infinite_setOf_prime).2 hk
  exact Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hge)

lemma nth_prime_n_sub_one_ne_two {n : ℕ} (hn : 2 ≤ n) : Nat.nth Nat.Prime (n - 1) ≠ 2 := by
  apply nth_prime_of_ge_one_ne_two
  omega

lemma A226163_eq_origInt (n : ℕ) (hn : 2 ≤ n) :
    A226163 n = (origIntMatrix (Nat.nth Nat.Prime (n-1)) ((Nat.nth Nat.Prime (n-1)-1)/2)).det := by
  unfold A226163
  have hnot : ¬ n < 2 := by omega
  simp [hnot]
  unfold origIntMatrix
  rfl

lemma oeis_zero_of_mod_three (n : ℕ) (hn : 2 ≤ n)
    (hp4 : Nat.nth Nat.Prime (n-1) % 4 = 3) : A226163 n = 0 := by
  let p := Nat.nth Nat.Prime (n-1)
  let m := (p-1)/2
  have hpprime : p.Prime := Nat.prime_nth_prime _
  have hpne2 : p ≠ 2 := nth_prime_n_sub_one_ne_two hn
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp_eq : p = 2*m+1 := by
    dsimp [m]
    exact p_eq_two_mul_half_add_one_of_prime_ne_two hpprime hpne2
  have hp2 : ringChar (ZMod p) ≠ 2 := zmod_ringChar_ne_two_of_prime_mod_four_eq_three hp4
  have hneg1 : quadraticChar (ZMod p) (-1) = -1 := zmod_quadraticChar_neg_one_of_prime_mod_four_eq_three hp4
  have hoddm : Odd m := m_odd_of_p_mod_four_three hp_eq hp4
  have hCprod : ((m.factorial : ℕ) : ZMod p) = ∏ j : Fin m, (((j.val + 1 : ℕ) : ZMod p)) := by
    exact (zmod_prod_y_eq_factorial (p:=p) (m:=m)).symm
  have hrat : (origRatMatrix p m).det = 0 := paley_zero_orig_rat hp_eq hp2 hneg1 hoddm hCprod
  have hA := A226163_eq_origInt n hn
  rw [hA]
  have hcastzero : (((origIntMatrix p m).det : ℤ) : ℚ) = 0 := by
    rw [cast_origInt_to_rat]
    exact hrat
  exact Int.cast_eq_zero.mp hcastzero

lemma oeis_ne_zero_of_mod_one (n : ℕ) (hn : 2 ≤ n)
    (hp4 : Nat.nth Nat.Prime (n-1) % 4 = 1) : A226163 n ≠ 0 := by
  let p := Nat.nth Nat.Prime (n-1)
  let m := (p-1)/2
  have hpprime : p.Prime := Nat.prime_nth_prime _
  have hpne2 : p ≠ 2 := by
    intro h2
    change p % 4 = 1 at hp4
    rw [h2] at hp4
    norm_num at hp4
  haveI : Fact p.Prime := ⟨hpprime⟩
  have hp_eq : p = 2*m+1 := by
    dsimp [m]
    exact p_eq_two_mul_half_add_one_of_prime_ne_two hpprime hpne2
  have hdet_ne := zmod_power_det_ne_zero_mod_one hp_eq hp4
  intro hA0
  have hA := A226163_eq_origInt n hn
  rw [hA] at hA0
  have hdet0 : (origIntMatrix p m).det = 0 := by
    simpa [p, m] using hA0
  have hmap : Matrix.det (((Int.castRingHom (ZMod p)).mapMatrix (origIntMatrix p m))) = 0 := by
    rw [← RingHom.map_det]
    simp [hdet0]
  rw [cast_origInt_to_zmod_power hp_eq] at hmap
  exact hdet_ne hmap

lemma prime_mod_four_eq_one_or_three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have hodd : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two hp).mpr hp2
  have hmod2 : p % 4 % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 4), hodd]
  have hlt : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases h : p % 4 <;> simp_all

lemma nth_prime_n_sub_one_mod_four_eq_one_or_three {n : ℕ} (hn : 2 ≤ n) :
    Nat.nth Nat.Prime (n - 1) % 4 = 1 ∨ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  exact prime_mod_four_eq_one_or_three (Nat.prime_nth_prime _) (nth_prime_n_sub_one_ne_two hn)

lemma oeis_conjecture_dev (n : ℕ) (hn : 2 ≤ n) :
    A226163 n = 0 ↔ Nat.nth Nat.Prime (n - 1) % 4 = 3 := by
  constructor
  · intro hzero
    rcases nth_prime_n_sub_one_mod_four_eq_one_or_three hn with h1 | h3
    · exfalso
      exact oeis_ne_zero_of_mod_one n hn h1 hzero
    · exact h3
  · intro h3
    exact oeis_zero_of_mod_three n hn h3

#print axioms oeis_conjecture_dev
