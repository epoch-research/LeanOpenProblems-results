import Submission.PrimePowerBoxRealization
import Submission.PresentCylinderArithmetic

/-! Exact geometric-root sharpness inside a divisor-closed irredundant partial
arithmetic family. The constructed family has an explicit hole: it is NOT an
odd covering system and does not settle Erdős 7. -/
namespace Erdos7RootMarginalSharpness
open scoped BigOperators
open Erdos7PrimePowerCombFamily Erdos7PrimePowerBoxRealization
open Erdos7PresentCylinderArithmetic Erdos7PresentCylinderLower
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

abbrev Label (E : ℕ) := Fin E ⊕ Fin (E+1)
def bases (q : ℕ) : Fin 2 → ℕ := ![3,q]
def caps (E : ℕ) : Fin 2 → ℕ := ![E,1]
def exps {E : ℕ} : Label E → Fin 2 → ℕ
  | Sum.inl j => ![j.val+1,0]
  | Sum.inr j => ![j.val,1]
def target {E : ℕ} : Label E → Fin 2 → ℤ
  | Sum.inl j => ![exitValue 3 (j.val+1) 1,0]
  | Sum.inr j => ![1,(j.val : ℤ)]
def witness {E : ℕ} : Label E → Fin 2 → ℤ
  | Sum.inl j => ![exitValue 3 (j.val+1) 1,(E+1 : ℕ)]
  | Sum.inr j => ![if j.val = 0 then -1 else 1,(j.val : ℤ)]
def hole (E : ℕ) : Fin 2 → ℤ := ![-1,(E+1 : ℕ)]

lemma bases_prime {q : ℕ} (hq : q.Prime) : ∀ i, (bases q i).Prime := by
  intro i; fin_cases i <;> simp [bases, Nat.prime_three, hq]
lemma bases_injective {q : ℕ} (hq : 3 < q) : Function.Injective (bases q) := by
  intro i j hij; fin_cases i <;> fin_cases j <;> simp_all [bases] <;> omega
lemma exps_bound {E : ℕ} (j : Label E) : exps j ≤ caps E := by
  intro i; cases j with
  | inl j => fin_cases i <;> simp [exps,caps] <;> omega
  | inr j => fin_cases i <;> simp [exps,caps] <;> omega
lemma exps_injective (E : ℕ) : Function.Injective (@exps E) := by
  intro i j hij
  have h0 := congrFun hij 0
  have h1 := congrFun hij 1
  cases i with
  | inl i => cases j with
    | inl j => congr 1; apply Fin.ext; simpa [exps] using h0
    | inr j => simp [exps] at h1
  | inr i => cases j with
    | inl j => simp [exps] at h1
    | inr j => congr 1; apply Fin.ext; simpa [exps] using h0

lemma one_not_exit (e : ℕ) (he : 0 < e) :
    ¬ (3 : ℤ) ∣ 1-exitValue 3 e 1 := by
  intro h
  have hh : (3 : ℤ)^min 1 e ∣ exitValue 3 1 2-exitValue 3 e 1 := by
    simpa [min_eq_left (show 1 ≤ e by omega), exitValue] using h
  have := (exit_congruent_iff (by norm_num : 0 < (3:ℕ)) (by omega : 0 < (1:ℕ))
    he (by omega : 0 < (2:ℕ)) (by omega : 0 < (1:ℕ))
    (by omega : 2 < (3:ℕ)) (by omega : 1 < (3:ℕ))).mp hh
  omega
lemma stem_not_exit (e : ℕ) (he : 0 < e) :
    ¬ (3 : ℤ)^e ∣ -1-exitValue 3 e 1 := by
  intro h
  apply exit_not_stem (by omega : 0 < (3:ℕ)) he (by omega : 0 < (1:ℕ))
    (by omega : 1 < (3:ℕ))
  convert dvd_neg.mpr h using 1 <;> ring

lemma private_coordinates {E q : ℕ} (hq : E+1 < q) (j k : Label E) :
    (∀ i, (bases q i : ℤ)^exps k i ∣ witness j i-target k i) ↔ k = j := by
  constructor
  · intro h
    have h0 := h 0
    have h1 := h 1
    cases j with
    | inl j => cases k with
      | inl k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_zero] at h0
        have hh := (exit_congruent_iff (by omega : 0 < (3:ℕ))
          (Nat.succ_pos j.val) (Nat.succ_pos k.val) (by omega : 0 < (1:ℕ))
          (by omega : 0 < (1:ℕ)) (by omega : 1 < (3:ℕ))
          (by omega : 1 < (3:ℕ))).mp
          ((pow_dvd_pow (3:ℤ) (min_le_right _ _)).trans h0)
        congr 1; apply Fin.ext; omega
      | inr k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_one,Matrix.cons_val_zero,
          pow_one] at h1
        have := bounded_congruent_eq (by positivity : (0:ℤ) ≤ (E+1:ℕ))
          (by positivity : (0:ℤ) ≤ k.val) (by exact_mod_cast hq)
          (by exact_mod_cast (show k.val < q by omega)) h1
        have hk := k.isLt
        norm_cast at this
        omega
    | inr j => cases k with
      | inl k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_zero] at h0
        by_cases hj : j.val = 0
        · rw [if_pos hj] at h0
          exact (stem_not_exit (k.val+1) (by omega) h0).elim
        · rw [if_neg hj] at h0
          exact (one_not_exit (k.val+1) (by omega)
            ((pow_dvd_pow (3:ℤ) (by omega : 1 ≤ k.val+1)).trans h0)).elim
      | inr k =>
        simp only [bases,exps,witness,target,Matrix.cons_val_one,Matrix.cons_val_zero,
          pow_one] at h1
        have hh := bounded_congruent_eq (by positivity : (0:ℤ) ≤ j.val)
          (by positivity : (0:ℤ) ≤ k.val)
          (by exact_mod_cast (show j.val < q by omega))
          (by exact_mod_cast (show k.val < q by omega)) h1
        congr 1; apply Fin.ext
        exact_mod_cast hh.symm
  · rintro rfl i
    cases k with
    | inl j => fin_cases i <;> simp [bases,exps,witness,target]
    | inr j =>
      fin_cases i
      · by_cases hj : j.val = 0 <;> simp [bases,exps,witness,target,hj]
      · simp [bases,exps,witness,target]

lemma hole_coordinates {E q : ℕ} (hq : E+1 < q) (k : Label E) :
    ¬ ∀ i, (bases q i : ℤ)^exps k i ∣ hole E i-target k i := by
  intro h
  cases k with
  | inl k =>
    exact stem_not_exit (k.val+1) (by omega) (by simpa [bases,exps,hole,target] using h 0)
  | inr k =>
    have hh : (q : ℤ) ∣ ((E+1:ℕ):ℤ)-k.val := by simpa [bases,exps,hole,target] using h 1
    have := bounded_congruent_eq (by positivity : (0:ℤ) ≤ (E+1:ℕ))
      (by positivity : (0:ℤ) ≤ k.val) (by exact_mod_cast hq)
      (by exact_mod_cast (show k.val < q by omega)) hh
    norm_cast at this
    have hk := k.isLt
    omega

lemma exps_complete {E : ℕ} (f : Fin 2 → ℕ) (hf : f ≤ caps E)
    (h0 : f ≠ fun _ => 0) : ∃ j : Label E, exps j = f := by
  have hf0 := hf 0
  have hf1 := hf 1
  simp only [caps,Matrix.cons_val_zero,Matrix.cons_val_one] at hf0 hf1
  by_cases h1 : f 1 = 0
  · have hp : 0 < f 0 := by
      by_contra hn
      apply h0; funext i; fin_cases i <;> simp_all
    refine ⟨Sum.inl ⟨f 0-1,by omega⟩,?_⟩
    funext i; fin_cases i <;> simp [exps,h1] <;> omega
  · have h1' : f 1 = 1 := by omega
    refine ⟨Sum.inr ⟨f 0,by omega⟩,?_⟩
    funext i; fin_cases i <;> simp [exps,h1']

lemma divisor_closed {E q : ℕ} (hq : q.Prime) (h3 : 3 < q) (j : Label E)
    (d : ℕ) (hd : d ∣ modulus (bases q) (exps j)) (h1 : 1 < d) :
    ∃ k : Label E, modulus (bases q) (exps k) = d := by
  obtain ⟨f,hf,hfd⟩ := divisor_pattern (bases q) (bases_prime hq) (bases_injective h3) _ d hd
  have hf0 : f ≠ fun _ => 0 := by
    intro hz
    rw [hz] at hfd
    simp [modulus] at hfd
    omega
  obtain ⟨k,hk⟩ := exps_complete f (hf.trans (exps_bound j)) hf0
  exact ⟨k, hk ▸ hfd⟩

/-- Every depth has a genuine odd arithmetic partial realization, with all
nontrivial divisor patterns and private integers. No covering is asserted. -/
theorem arithmetic_family (E q : ℕ) (hq : q.Prime) (h3 : 3 < q) (hE : E+1 < q) :
    ∃ (a z : Label E → ℤ) (v : ℤ),
      (∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target j i) ∧
      (∀ j k, (modulus (bases q) (exps k) : ℤ) ∣ z j-a k ↔ k = j) ∧
      (∀ k, ¬ (modulus (bases q) (exps k) : ℤ) ∣ v-a k) := by
  exact realize_partial_family (bases q) (bases_prime hq) (bases_injective h3)
    (caps E) exps exps_bound target witness (hole E)
    (private_coordinates hE) (hole_coordinates hE)

lemma moduli_injective (E q : ℕ) (hq : q.Prime) (h3 : 3 < q) :
    Function.Injective (fun j : Label E => modulus (bases q) (exps j)) :=
  (modulus_injective (bases q) (bases_prime hq) (bases_injective h3)).comp
    (exps_injective E)

lemma moduli_odd_gt_one {E q : ℕ} (hq : q.Prime) (h3 : 3 < q) (j : Label E) :
    1 < modulus (bases q) (exps j) ∧ Odd (modulus (bases q) (exps j)) := by
  have hqo : Odd q := hq.odd_of_ne_two (by omega)
  have h3o : Odd (3:ℕ) := by decide
  cases j with
  | inl j =>
    simp only [modulus,Fin.prod_univ_two,bases,exps,Matrix.cons_val_zero,
      Matrix.cons_val_one,pow_zero,mul_one]
    exact ⟨Nat.one_lt_pow (by omega) (by omega), h3o.pow⟩
  | inr j =>
    simp only [modulus,Fin.prod_univ_two,bases,exps,Matrix.cons_val_zero,
      Matrix.cons_val_one,pow_one]
    constructor
    · have hpow : 1 ≤ 3^j.val := Nat.one_le_pow _ _ (by omega)
      nlinarith
    · exact (h3o.pow).mul hqo

/-- Delete exactly the pure ternary comb. -/
def pure (E j : ℕ) : Finset (ZMod (3^E)) :=
  cylinder 3 E (j+1) (exitValue 3 (j+1) 1)
def good (E : ℕ) : Finset (ZMod (3^E)) :=
  Finset.univ \ (Finset.range E).biUnion (pure E)
noncomputable def active (E : ℕ) (x : ZMod (3^E)) : Finset ℕ :=
  (Finset.range E).filter (fun j => x ∈ cylinder 3 E (j+1) 1)
noncomputable def rootCount (E : ℕ) (x : ZMod (3^E)) : ℕ := 1+(active E x).card

lemma pure_pairwise (E : ℕ) :
    (↑(Finset.range E) : Set ℕ).PairwiseDisjoint (pure E) := by
  intro j _ k _ hjk
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (mem_cylinder 3 E (j+1) _ x).mp hx
  have hy' := (mem_cylinder 3 E (k+1) _ x).mp hy
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hx' hy'
  have hh : (3:ℤ)^min (j+1) (k+1) ∣ exitValue 3 (j+1) 1-exitValue 3 (k+1) 1 := by
    convert dvd_sub ((pow_dvd_pow (3:ℤ) (min_le_right _ _)).trans hy')
      ((pow_dvd_pow (3:ℤ) (min_le_left _ _)).trans hx') using 1 <;> ring
  have he := (exit_congruent_iff (by omega : 0 < (3:ℕ)) (by omega : 0 < j+1)
    (by omega : 0 < k+1) (by omega : 0 < (1:ℕ)) (by omega : 0 < (1:ℕ))
    (by omega : 1 < (3:ℕ)) (by omega : 1 < (3:ℕ))).mp hh
  exact hjk (by omega)

lemma geometric_third (E : ℕ) : geometricMass (1/3:ℚ) E = (1-(1/3:ℚ)^E)/2 := by
  induction E with
  | zero => simp [geometricMass]
  | succ E ih =>
    have he : geometricMass (1/3:ℚ) (E+1) = geometricMass (1/3:ℚ) E+(1/3:ℚ)^(E+1) := by
      simp [geometricMass,Finset.sum_range_succ]
    rw [he,ih,pow_succ]; ring

lemma good_card (E : ℕ) : ((good E).card:ℚ) =
    Fintype.card (ZMod (3^E)) * (1+(1/3:ℚ)^E)/2 := by
  have hh := pure_union_card (1/3:ℚ) E (pure E) (pure_pairwise E) (by
    intro j hj
    simpa [pure] using cylinder_card 3 E (j+1) (by omega) (exitValue 3 (j+1) 1))
  rw [geometric_third] at hh
  have hc := Finset.card_sdiff_add_card_eq_card
    (Finset.subset_univ ((Finset.range E).biUnion (pure E)))
  have hc' : ((good E).card:ℚ) + ((Finset.range E).biUnion (pure E)).card =
      Fintype.card (ZMod (3^E)) := by exact_mod_cast hc
  linarith

lemma nested_good {E a : ℕ} (ha : 0 < a) : cylinder 3 E a 1 ⊆ good E := by
  intro x hx
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  intro hy
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hy
  have hx' := (mem_cylinder 3 E a 1 x).mp hx
  have hj' := (mem_cylinder 3 E (j+1) (exitValue 3 (j+1) 1) x).mp hj
  simp only [Nat.cast_pow,Nat.cast_ofNat] at hx' hj'
  have h1 : (3:ℤ) ∣ (x.val:ℤ)-1 :=
    (show (3:ℤ) ∣ (3:ℤ)^a by simpa using (pow_dvd_pow (3:ℤ) (show 1 ≤ a by omega))).trans hx'
  have h2 : (3:ℤ) ∣ (x.val:ℤ)-exitValue 3 (j+1) 1 :=
    (show (3:ℤ) ∣ (3:ℤ)^(j+1) by simpa using (pow_dvd_pow (3:ℤ) (show 1 ≤ j+1 by omega))).trans hj'
  apply one_not_exit (j+1) (by omega)
  convert dvd_sub h2 h1 using 1 <;> ring

lemma cylinder_nested {E a b : ℕ} (hab : a ≤ b) :
    cylinder 3 E b 1 ⊆ cylinder 3 E a 1 := by
  intro x hx
  rw [mem_cylinder] at hx ⊢
  have hd : ((3^a:ℕ):ℤ) ∣ ((3^b:ℕ):ℤ) := by exact_mod_cast pow_dvd_pow 3 hab
  exact hd.trans hx

lemma root_tail {E a : ℕ} (ha : 0 < a) (haE : a ≤ E) (x : ZMod (3^E)) :
    a+1 ≤ rootCount E x ↔ x ∈ cylinder 3 E a 1 := by
  constructor
  · intro h
    by_contra hx
    have hs : active E x ⊆ Finset.range (a-1) := by
      intro j hj
      obtain ⟨_,hj⟩ := Finset.mem_filter.mp hj
      apply Finset.mem_range.mpr
      by_contra hn
      exact hx (cylinder_nested (by omega : a ≤ j+1) hj)
    have hc := Finset.card_le_card hs
    rw [Finset.card_range] at hc
    dsimp [rootCount] at h
    omega
  · intro hx
    have hs : Finset.range a ⊆ active E x := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_range.mpr (by omega),cylinder_nested (by omega) hx⟩
    have hc := Finset.card_le_card hs
    rw [Finset.card_range] at hc
    dsimp [rootCount]
    omega

/-- Equality, at every positive depth, in the finite-cap geometric root law.
The law concerns uniform conditioning on the pure-class complement. -/
theorem root_tail_probability {E a : ℕ} (ha : 0 < a) (haE : a ≤ E) :
    (((good E).filter (fun x => a+1 ≤ rootCount E x)).card:ℚ) / (good E).card =
      (2/(1+(1/3:ℚ)^E))*(1/3:ℚ)^a := by
  have he : (good E).filter (fun x => a+1 ≤ rootCount E x) = cylinder 3 E a 1 := by
    ext x
    simp only [Finset.mem_filter, root_tail ha haE]
    exact and_iff_right_of_imp (fun hx => nested_good ha hx)
  rw [he,good_card,cylinder_card 3 E a haE]
  have hcard : (Fintype.card (ZMod (3^E)):ℚ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos : 0 < Fintype.card (ZMod (3^E))))
  have hden : 1+(1/3:ℚ)^E ≠ 0 := by positivity
  norm_num only [inv_eq_one_div]
  field_simp

lemma cylinder_congr {E e : ℕ} (he : e ≤ E) (a b : ℤ)
    (hab : (3:ℤ)^E ∣ a-b) : cylinder 3 E e a = cylinder 3 E e b := by
  ext x
  simp only [mem_cylinder,Nat.cast_pow,Nat.cast_ofNat]
  have hh := (pow_dvd_pow (3:ℤ) he).trans hab
  constructor
  · intro h
    convert dvd_add h hh using 1 <;> ring
  · intro h
    convert dvd_sub h hh using 1 <;> ring

noncomputable def arithmeticGood {E : ℕ} (a : Label E → ℤ) : Finset (ZMod (3^E)) :=
  Finset.univ \ Finset.univ.biUnion
    (fun j : Fin E => cylinder 3 E (j.val+1) (a (Sum.inl j)))
noncomputable def arithmeticCount {E : ℕ} (a : Label E → ℤ) (x : ZMod (3^E)) : ℕ :=
  ∑ j : Fin (E+1), if x ∈ cylinder 3 E j.val (a (Sum.inr j)) then 1 else 0

lemma arithmeticGood_eq {E q : ℕ} (a : Label E → ℤ)
    (ha : ∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target j i) :
    arithmeticGood a = good E := by
  have hh (j : Fin E) : cylinder 3 E (j.val+1) (a (Sum.inl j)) = pure E j.val := by
    apply cylinder_congr (by omega)
    simpa [bases,caps,target] using ha (Sum.inl j) 0
  ext x
  simp only [arithmeticGood,good,Finset.mem_sdiff,Finset.mem_univ,true_and,
    Finset.mem_biUnion,hh]
  simp only [Fin.exists_iff,Finset.mem_range, exists_prop]

lemma arithmeticCount_eq {E q : ℕ} (a : Label E → ℤ)
    (ha : ∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target j i) (x : ZMod (3^E)) :
    arithmeticCount a x = rootCount E x := by
  have hh (j : Fin (E+1)) : cylinder 3 E j.val (a (Sum.inr j)) = cylinder 3 E j.val 1 := by
    apply cylinder_congr (by omega)
    simpa [bases,caps,target] using ha (Sum.inr j) 0
  simp only [arithmeticCount,hh]
  rw [Fin.sum_univ_succ]
  have hz : x ∈ cylinder 3 E 0 1 := by rw [mem_cylinder]; simp
  simp only [Fin.val_zero,if_pos hz,Fin.val_succ,rootCount]
  congr 1
  rw [Fin.sum_univ_eq_sum_range (fun j => if x ∈ cylinder 3 E (j+1) 1 then (1:ℕ) else 0)]
  exact Finset.sum_boole _ _

/-- The exact root law is a law for the actual integer residues produced by
CRT, not just a separately chosen collection of abstract cylinders. -/
theorem arithmetic_root_law {E q : ℕ} (a : Label E → ℤ)
    (ha : ∀ j i, (bases q i : ℤ)^caps E i ∣ a j-target j i)
    (t : ℕ) (ht : 0 < t) (htE : t ≤ E) :
    (((arithmeticGood a).filter (fun x => t+1 ≤ arithmeticCount a x)).card:ℚ) /
        (arithmeticGood a).card = (2/(1+(1/3:ℚ)^E))*(1/3:ℚ)^t := by
  simp only [arithmeticGood_eq a ha,arithmeticCount_eq a ha]
  exact root_tail_probability ht htE

/-- All depths occur in actual partial odd arithmetic families attaining the
root marginal, with private points and a hole. -/
theorem exists_arithmetic_sharpness (E : ℕ) :
    ∃ (q : ℕ) (a z : Label E → ℤ) (v : ℤ),
      q.Prime ∧ 3 < q ∧ E+1 < q ∧
      Function.Injective (fun j : Label E => modulus (bases q) (exps j)) ∧
      (∀ j : Label E, 1 < modulus (bases q) (exps j) ∧ Odd (modulus (bases q) (exps j))) ∧
      (∀ j : Label E, ∀ d : ℕ, d ∣ modulus (bases q) (exps j) → 1 < d →
        ∃ k : Label E, modulus (bases q) (exps k) = d) ∧
      (∀ j k, (modulus (bases q) (exps k) : ℤ) ∣ z j-a k ↔ k = j) ∧
      (∀ k, ¬ (modulus (bases q) (exps k) : ℤ) ∣ v-a k) ∧
      (∀ t, 0 < t → t ≤ E →
        (((arithmeticGood a).filter (fun x => t+1 ≤ arithmeticCount a x)).card:ℚ) /
          (arithmeticGood a).card = (2/(1+(1/3:ℚ)^E))*(1/3:ℚ)^t) := by
  obtain ⟨q,hqbound,hq⟩ := Nat.exists_infinite_primes (E+5)
  have h3 : 3 < q := by omega
  have hE : E+1 < q := by omega
  obtain ⟨a,z,v,ha,hz,hv⟩ := arithmetic_family E q hq h3 hE
  exact ⟨q,a,z,v,hq,h3,hE,moduli_injective E q hq h3,
    moduli_odd_gt_one hq h3,divisor_closed hq h3,hz,hv,arithmetic_root_law a ha⟩

#print axioms exists_arithmetic_sharpness
#print axioms arithmetic_root_law
#print axioms root_tail_probability
#print axioms moduli_odd_gt_one
#print axioms arithmetic_family
#print axioms divisor_closed
end Erdos7RootMarginalSharpness
