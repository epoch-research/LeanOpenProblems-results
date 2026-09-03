import Submission.FormalGaussianSidon

/-!
Progression-free alphabets do not repair Gaussian-polynomial specialization.
This auxiliary counterexample is not a disproof of Erdős 773.
-/
namespace Erdos773.PrimeAPFreeAlphabetCarry
open Finset Polynomial FormalGaussianSidon
noncomputable section
set_option maxHeartbeats 2000000

def base (t : ℤ) : ℤ := 1452*t+509

def offset : Fin 9 → ℤ := ![1,9,11,18,33,34,56,60,66]
def slope : Fin 9 → ℤ := ![0,40,66,40,66,132,132,181,181]
def letter (t : ℤ) (i : Fin 9) : ℤ := slope i*t+offset i
def alphabet (t : ℤ) : Finset ℤ := univ.image (letter t)

def low (t : ℤ) : Fin 4 → ℤ := ![66*t+33,132*t+34,66*t+11,132*t+56]
def high (t : ℤ) : Fin 4 → ℤ := ![40*t+9,181*t+66,40*t+18,181*t+60]
def parameter (t : ℤ) (j : Fin 4) : ℤ[X] :=
  1+C (low t j)*X+C (high t j)*X^2

def value (t : ℤ) (j : Fin 4) : ℤ := (encoding 3 (parameter t j)).eval (base t)

lemma offset_injective : Function.Injective offset := by decide +kernel

lemma offset_ap_free : ThreeAPFree (univ.image offset : Set ℤ) := by decide +kernel

lemma offset_bounds (i : Fin 9) : 1 ≤ offset i ∧ offset i ≤ 66 := by
  fin_cases i <;> norm_num [offset]

lemma alphabet_ap_free (t : ℤ) (ht : 133 ≤ t) : ThreeAPFree (alphabet t : Set ℤ) := by
  intro a ha b hb c hc he
  simp only [mem_coe,alphabet] at ha hb hc
  obtain ⟨i,_,rfl⟩ := mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := mem_image.mp hb
  obtain ⟨k,_,rfl⟩ := mem_image.mp hc
  have hi := offset_bounds i
  have hj := offset_bounds j
  have hk := offset_bounds k
  have hm := congrArg (fun x : ℤ => x%t) he
  have hi0 : 0 ≤ offset i+offset k := by omega
  have hi1 : offset i+offset k<t := by omega
  have hj0 : 0 ≤ offset j+offset j := by omega
  have hj1 : offset j+offset j<t := by omega
  have hr : offset i+offset k=offset j+offset j := by
    have hm' : (offset i+offset k)%t=(offset j+offset j)%t := by
      simpa [letter, Int.add_emod, Int.mul_emod] using hm
    simpa only [Int.emod_eq_of_lt hi0 hi1,Int.emod_eq_of_lt hj0 hj1] using hm'
  have hmem (l : Fin 9) : offset l ∈ (univ.image offset : Set ℤ) :=
    mem_image.mpr ⟨l,mem_univ _,rfl⟩
  have hij := offset_ap_free (hmem i) (hmem j) (hmem k) hr
  exact congrArg (letter t) (offset_injective hij)


lemma letter_positive (t : ℤ) (ht : 0≤t) (i : Fin 9) : 0<letter t i := by
  fin_cases i <;> dsimp [letter,slope,offset] <;> omega

lemma letter_no_doubling (t : ℤ) (ht : 133≤t) (i j : Fin 9) :
    letter t i≠2*letter t j := by
  fin_cases i <;> fin_cases j <;> dsimp [letter,slope,offset] <;> omega

def digitAlphabet (t : ℤ) : Finset ℤ := insert 1 ((insert 0 (alphabet t)).image (6*·))

lemma zero_alphabet_ap_free (t : ℤ) (ht : 133≤t) :
    ThreeAPFree ((insert 0 (alphabet t) : Finset ℤ) : Set ℤ) := by
  intro a ha b hb c hc he
  simp only [mem_coe,mem_insert,alphabet] at ha hb hc
  rcases ha with rfl|ha <;> rcases hb with rfl|hb <;> rcases hc with rfl|hc
  all_goals first | rfl | omega | skip
  · obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    obtain ⟨k,_,rfl⟩ := mem_image.mp hc
    exact (letter_no_doubling t ht k j (by omega)).elim
  · obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨k,_,rfl⟩ := mem_image.mp hc
    have hi := letter_positive t (by omega) i
    have hk := letter_positive t (by omega) k
    omega
  · obtain ⟨i,_,rfl⟩ := mem_image.mp ha
    obtain ⟨j,_,rfl⟩ := mem_image.mp hb
    exact (letter_no_doubling t ht i j (by omega)).elim
  · exact alphabet_ap_free t ht ha hb hc he

lemma digit_alphabet_ap_free (t : ℤ) (ht : 133≤t) :
    ThreeAPFree (digitAlphabet t : Set ℤ) := by
  intro a ha b hb c hc he
  simp only [digitAlphabet,mem_coe,mem_insert,mem_image] at ha hb hc
  rcases ha with rfl|⟨a,ha,rfl⟩ <;>
    rcases hb with rfl|⟨b,hb,rfl⟩ <;> rcases hc with rfl|⟨c,hc,rfl⟩
  all_goals first | rfl | omega | skip
  have hh : a+c=b+b := by omega
  have hab := zero_alphabet_ap_free t ht (mem_insert.mpr ha) (mem_insert.mpr hb)
    (mem_insert.mpr hc) hh
  omega


/-- The ten positive actual digit values, with the leading digit included. -/
def digitOffset : Fin 10 → ℤ := ![1,6,54,66,108,198,204,336,360,396]
def digitSlope : Fin 10 → ℤ := ![0,0,240,396,240,396,792,792,1086,1086]
def positiveDigit (t : ℤ) (i : Fin 10) : ℤ := digitSlope i*t+digitOffset i

def determinant (i j k : Fin 10) : ℤ :=
  (digitSlope i-digitSlope j)*(digitOffset k-digitOffset j)-
    (digitSlope k-digitSlope j)*(digitOffset i-digitOffset j)

lemma determinant_nonzero : ∀ i j k : Fin 10,
    i≠j → i≠k → j≠k → determinant i j k≠0 := by decide +kernel

lemma digitOffset_bounds (i : Fin 10) : 1≤digitOffset i ∧ digitOffset i≤396 := by
  fin_cases i <;> norm_num [digitOffset]

/-- Even forbidding every short weighted three-term average is insufficient.
The bound is quantitative: all positive weights at most K are excluded when
792*K<t. The ten digits are not asserted to form a large alphabet. -/
theorem no_bounded_weighted_average (t K u v : ℤ) (_hK : 1≤K)
    (ht : 792*K<t) (hu : 0<u) (huK : u≤K) (hv : 0<v) (hvK : v≤K)
    (i j k : Fin 10)
    (he : u*positiveDigit t i+v*positiveDigit t k=(u+v)*positiveDigit t j) :
    positiveDigit t i=positiveDigit t j := by
  have hi := digitOffset_bounds i
  have hj := digitOffset_bounds j
  have hk := digitOffset_bounds k
  have hleft : 0≤u*digitOffset i+v*digitOffset k :=
    add_nonneg (mul_nonneg hu.le (by omega)) (mul_nonneg hv.le (by omega))
  have hright : 0≤(u+v)*digitOffset j :=
    mul_nonneg (by omega) (by omega)
  have hule := mul_le_mul_of_nonneg_left hi.2 hu.le
  have hvle := mul_le_mul_of_nonneg_left hk.2 hv.le
  have huj := mul_le_mul_of_nonneg_left hj.2 (show 0≤u+v by omega)
  have hleftlt : u*digitOffset i+v*digitOffset k<t := by nlinarith
  have hrightlt : (u+v)*digitOffset j<t := by nlinarith
  have hmod := congrArg (fun z : ℤ => z%t) he
  have hoff : u*digitOffset i+v*digitOffset k=(u+v)*digitOffset j := by
    have hh : (u*digitOffset i+v*digitOffset k)%t=((u+v)*digitOffset j)%t := by
      simpa [positiveDigit,Int.add_emod,Int.mul_emod] using hmod
    simpa only [Int.emod_eq_of_lt hleft hleftlt,
      Int.emod_eq_of_lt hright hrightlt] using hh
  have ht0 : t≠0 := by omega
  have hsl : u*digitSlope i+v*digitSlope k=(u+v)*digitSlope j := by
    have hh : t*(u*digitSlope i+v*digitSlope k-(u+v)*digitSlope j)=0 := by
      dsimp only [positiveDigit] at he
      linear_combination he-hoff
    exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left ht0)
  have hdet : determinant i j k=0 := by
    have hh : u*determinant i j k=0 := by
      dsimp only [determinant]
      linear_combination (digitOffset k-digitOffset j)*hsl-
        (digitSlope k-digitSlope j)*hoff
    exact (mul_eq_zero.mp hh).resolve_left hu.ne'
  by_cases hij : i=j
  · exact congrArg (positiveDigit t) hij
  by_cases hik : i=k
  · subst k
    apply mul_left_cancel₀ (show u+v≠0 by omega)
    linear_combination he
  by_cases hjk : j=k
  · subst k
    apply mul_left_cancel₀ hu.ne'
    linear_combination he
  exact (determinant_nonzero i j k hij hik hjk hdet).elim

lemma admissible (t : ℤ) (j : Fin 4) : Admissible 3 (parameter t j) := by
  fin_cases j <;> constructor
  all_goals first
    | (dsimp [parameter]; compute_degree <;> norm_num)
    | norm_num [parameter]

lemma coefficient_formula (t : ℤ) (j : Fin 4) (n : ℕ) :
    (encoding 3 (parameter t j)).coeff n =
      (if n=3 then 1 else 0)+6*((if n=0 then 1 else 0)+
        low t j*(if 1=n then 1 else 0)+high t j*(if n=2 then 1 else 0)) := by
  simp only [encoding,parameter,coeff_add,coeff_X_pow,coeff_C_mul,coeff_one,coeff_X]

/-- An explicit index for each of the four positive coefficients. -/
def coefficientIndex (j n : Fin 4) : Fin 10 :=
  ![1, (![5,6,3,7] : Fin 4 → Fin 10) j,
    (![2,9,4,8] : Fin 4 → Fin 10) j, 0] n

lemma coefficient_positiveDigit (t : ℤ) (j n : Fin 4) :
    (encoding 3 (parameter t j)).coeff n =
      positiveDigit t (coefficientIndex j n) := by
  fin_cases j <;> fin_cases n <;>
    norm_num [coefficient_formula, coefficientIndex, positiveDigit,
      digitSlope, digitOffset, low, high] <;> dsimp <;> ring

def positiveAlphabet (t : ℤ) : Finset ℤ := univ.image (positiveDigit t)

lemma coefficient_mem_positiveAlphabet (t : ℤ) (j : Fin 4) (n : ℕ) (hn : n≤3) :
    (encoding 3 (parameter t j)).coeff n ∈ positiveAlphabet t := by
  let k : Fin 4 := ⟨n, by omega⟩
  have he := coefficient_positiveDigit t j k
  exact mem_image.mpr ⟨coefficientIndex j k, mem_univ _, he.symm⟩

/-- Weighted-average freeness of the actual positive alphabet used by the roots. -/
theorem positiveAlphabet_weighted_free (t K : ℤ) (hK : 1≤K) (ht : 792*K<t)
    (u v : ℤ) (hu : 0<u) (huK : u≤K) (hv : 0<v) (hvK : v≤K)
    (a b c : ℤ) (ha : a∈positiveAlphabet t) (hb : b∈positiveAlphabet t)
    (hc : c∈positiveAlphabet t) (he : u*a+v*c=(u+v)*b) : a=b := by
  obtain ⟨i,_,rfl⟩ := mem_image.mp ha
  obtain ⟨j,_,rfl⟩ := mem_image.mp hb
  obtain ⟨k,_,rfl⟩ := mem_image.mp hc
  exact no_bounded_weighted_average t K u v hK ht hu huK hv hvK i j k he

lemma parameter_letters (t : ℤ) (j : Fin 4) :
    1∈alphabet t ∧ low t j∈alphabet t ∧ high t j∈alphabet t := by
  have hm (i : Fin 9) : letter t i∈alphabet t := mem_image.mpr ⟨i,mem_univ _,rfl⟩
  refine ⟨by simpa [letter,slope,offset] using hm 0,?_,?_⟩
  · fin_cases j
    · simpa [low,letter,slope,offset] using hm 4
    · simpa [low,letter,slope,offset] using hm 5
    · simpa [low,letter,slope,offset] using hm 2
    · simpa [low,letter,slope,offset] using hm 6
  · fin_cases j
    · simpa [high,letter,slope,offset] using hm 1
    · simpa [high,letter,slope,offset] using hm 8
    · simpa [high,letter,slope,offset] using hm 3
    · simpa [high,letter,slope,offset] using hm 7

lemma digit_bounds (t : ℤ) (ht : 0≤t) (j : Fin 4) :
    0<6*low t j ∧ 6*low t j<base t ∧
      0<6*high t j ∧ 6*high t j<base t := by
  fin_cases j <;> dsimp [low,high,base] <;> omega


lemma canonical_ap_free_digits (t : ℤ) (ht : 133≤t) (j : Fin 4) :
    ThreeAPFree (digitAlphabet t : Set ℤ) ∧
    (encoding 3 (parameter t j)).coeff 0=6 ∧
    (encoding 3 (parameter t j)).coeff 3=1 ∧
    ∀ n≤3, (encoding 3 (parameter t j)).coeff n∈digitAlphabet t ∧
      0≤(encoding 3 (parameter t j)).coeff n ∧
      (encoding 3 (parameter t j)).coeff n<base t := by
  obtain ⟨h1,hl,hh⟩ := parameter_letters t j
  obtain ⟨hl0,hlB,hh0,hhB⟩ := digit_bounds t (by omega) j
  have hB : 6<base t := by dsimp [base]; omega
  refine ⟨digit_alphabet_ap_free t ht,?_,?_,?_⟩
  · norm_num [coefficient_formula]
  · norm_num [coefficient_formula]
  · intro n hn
    have hm {x : ℤ} (hx : x∈alphabet t) : 6*x∈digitAlphabet t :=
      mem_insert_of_mem (mem_image.mpr ⟨x,mem_insert_of_mem hx,rfl⟩)
    interval_cases n
    · norm_num only [coefficient_formula]
      simp only [ite_true,ite_false,mul_zero,mul_one,zero_add,add_zero] 
      exact ⟨by simpa using hm h1,by omega,by omega⟩
    · norm_num only [coefficient_formula]
      simp only [ite_true,ite_false,mul_zero,mul_one,zero_add,add_zero]
      exact ⟨hm hl,by omega,hlB⟩
    · norm_num only [coefficient_formula]
      simp only [ite_true,ite_false,mul_zero,mul_one,zero_add,add_zero]
      exact ⟨hm hh,by omega,hhB⟩
    · norm_num only [coefficient_formula]
      simp only [ite_true,ite_false,mul_zero,add_zero]
      exact ⟨mem_insert_self _ _,by omega,by omega⟩

lemma norm_difference (t : ℤ) :
    (encoding 3 (parameter t 0))^2+(encoding 3 (parameter t 1))^2-
      (encoding 3 (parameter t 2))^2-(encoding 3 (parameter t 3))^2 =
        36*X^2*(C (base t)-X)*(X^2-4*X-2) := by
  dsimp [encoding,parameter,low,high,base]
  simp only [map_add,map_mul,map_ofNat]
  ring

lemma collision (t : ℤ) : value t 0^2+value t 1^2=value t 2^2+value t 3^2 := by
  have hh := congrArg (Polynomial.eval (base t)) (norm_difference t)
  simp only [eval_sub,eval_add,eval_pow,eval_mul,eval_X,eval_C,eval_ofNat,
    sub_self,mul_zero,zero_mul] at hh
  change value t 0^2+value t 1^2-value t 2^2-value t 3^2=0 at hh
  omega

lemma value_formula (t : ℤ) (j : Fin 4) :
    value t j=(base t)^3+6*(1+low t j*base t+high t j*(base t)^2) := by
  simp only [value,encoding,parameter,eval_add,eval_pow,eval_X,eval_mul,eval_C,eval_one]

lemma positive (t : ℤ) (ht : 0≤t) (j : Fin 4) : 0<value t j := by
  have hB : 0<base t := by dsimp [base]; omega
  obtain ⟨hl,_,hh,_⟩ := digit_bounds t ht j
  have hl' : 0<low t j := by omega
  have hh' : 0<high t j := by omega
  rw [value_formula]
  positivity

lemma ordered_values (t : ℤ) (ht : 0≤t) :
    value t 0<value t 2 ∧ value t 2<value t 3 ∧ value t 3<value t 1 := by
  have hB : 509≤base t := by dsimp [base]; omega
  have h1 : value t 2-value t 0=6*base t*(9*base t-22) := by
    simp only [value_formula]; dsimp [low,high]; ring
  have h2 : value t 3-value t 2=
      6*base t*((141*t+42)*base t+(66*t+45)) := by
    simp only [value_formula]; dsimp [low,high]; ring
  have h3 : value t 1-value t 3=6*base t*(6*base t-22) := by
    simp only [value_formula]; dsimp [low,high]; ring
  have h9 : 0<9*base t-22 := by omega
  have h6 : 0<6*base t-22 := by omega
  have h1' : 0<value t 2-value t 0 := by rw [h1]; positivity
  have h2' : 0<value t 3-value t 2 := by rw [h2]; positivity
  have h3' : 0<value t 1-value t 3 := by rw [h3]; positivity
  omega

lemma value_injective (t : ℤ) (ht : 0≤t) : Function.Injective (value t) := by
  have hh := ordered_values t ht
  intro i j he
  fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at he ⊢ <;> first | rfl | omega

lemma formal_square_sidon (t : ℤ) :
    IsSidon ((univ.image (fun j : Fin 4 => (encoding 3 (parameter t j))^2)) : Set ℤ[X]) := by
  apply Set.IsSidon.subset (formal_sidon 3)
  intro f hf
  simp only [mem_coe] at hf
  obtain ⟨j,_,rfl⟩ := mem_image.mp hf
  exact ⟨parameter t j,admissible t j,rfl⟩

theorem specialization_not_sidon (t : ℤ) (ht : 0≤t) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => value t j^2)) : Set ℤ) := by
  intro hs
  have hm (j : Fin 4) : value t j^2∈univ.image (fun j : Fin 4 => value t j^2) :=
    mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have ho := ordered_values t ht
  have h02 : value t 0^2<value t 2^2 :=
    (sq_lt_sq₀ (positive t ht 0).le (positive t ht 2).le).mpr ho.1
  have h03 : value t 0^2<value t 3^2 :=
    (sq_lt_sq₀ (positive t ht 0).le (positive t ht 3).le).mpr (ho.1.trans ho.2.1)
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (collision t) with h | h <;> omega


def naturalValue (t : ℤ) (j : Fin 4) : ℕ := (value t j).toNat

lemma naturalValue_cast (t : ℤ) (ht : 0≤t) (j : Fin 4) :
    (naturalValue t j : ℤ)=value t j := Int.toNat_of_nonneg (positive t ht j).le

lemma natural_collision (t : ℤ) (ht : 0≤t) :
    naturalValue t 0^2+naturalValue t 1^2=
      naturalValue t 2^2+naturalValue t 3^2 := by
  have hh := collision t
  simp only [← naturalValue_cast t ht] at hh
  exact_mod_cast hh

theorem natural_specialization_not_sidon (t : ℤ) (ht : 0≤t) :
    ¬IsSidon ((univ.image (fun j : Fin 4 => naturalValue t j^2)) : Set ℕ) := by
  intro hs
  have hm (j : Fin 4) : naturalValue t j^2∈univ.image (fun j : Fin 4 => naturalValue t j^2) :=
    mem_image.mpr ⟨j,mem_univ _,rfl⟩
  have ho := ordered_values t ht
  have h02 : value t 0^2<value t 2^2 :=
    (sq_lt_sq₀ (positive t ht 0).le (positive t ht 2).le).mpr ho.1
  have h03 : value t 0^2<value t 3^2 :=
    (sq_lt_sq₀ (positive t ht 0).le (positive t ht 3).le).mpr (ho.1.trans ho.2.1)
  have h02' : naturalValue t 0^2<naturalValue t 2^2 := by
    exact_mod_cast (by simpa only [naturalValue_cast t ht,Int.natCast_pow] using h02 :
      (naturalValue t 0:ℤ)^2<(naturalValue t 2:ℤ)^2)
  have h03' : naturalValue t 0^2<naturalValue t 3^2 := by
    exact_mod_cast (by simpa only [naturalValue_cast t ht,Int.natCast_pow] using h03 :
      (naturalValue t 0:ℤ)^2<(naturalValue t 3:ℤ)^2)
  rcases hs _ (hm 0) _ (hm 2) _ (hm 1) _ (hm 3) (natural_collision t ht) with h | h <;> omega

lemma arbitrarily_large_prime (M : ℕ) :
    ∃ t : ℕ, 133≤t ∧ M<1452*t+509 ∧ Nat.Prime (1452*t+509) := by
  obtain ⟨p,hp,hprime,hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max M 194000) (by norm_num : (1452:ℕ)≠0)
    (show Nat.Coprime 509 1452 by norm_num)
  have hrem : p%1452=509 := by simpa only [Nat.ModEq] using hmod
  have he : 1452*(p/1452)+509=p := by omega
  refine ⟨p/1452,by omega,?_,?_⟩
  · rw [he]; exact (le_max_left _ _).trans_lt hp
  · rwa [he]

theorem arbitrarily_large_prime_obstruction (M : ℕ) :
    ∃ t : ℕ, 133≤t ∧ M<1452*t+509 ∧ Nat.Prime (1452*t+509) ∧
      ThreeAPFree (alphabet (t:ℤ) : Set ℤ) ∧
        ¬IsSidon ((univ.image (fun j : Fin 4 => value (t:ℤ) j^2)) : Set ℤ) := by
  obtain ⟨t,ht,hM,hp⟩ := arbitrarily_large_prime M
  exact ⟨t,ht,hM,hp,alphabet_ap_free t (by exact_mod_cast ht),
    specialization_not_sidon t (by positivity)⟩

/-- For each fixed weight bound, arbitrarily large prime bases still admit
four distinct colliding roots whose positive canonical digits all lie in a
single weighted-average-free alphabet. This is not a Sidon-subset upper bound. -/
theorem arbitrarily_large_prime_weighted_obstruction (K M : ℕ) (hK : 1≤K) :
    ∃ t : ℕ, 133≤t ∧ M<1452*t+509 ∧ Nat.Prime (1452*t+509) ∧
      (∀ u v : ℤ, 0<u → u≤K → 0<v → v≤K →
        ∀ a∈positiveAlphabet t, ∀ b∈positiveAlphabet t, ∀ c∈positiveAlphabet t,
          u*a+v*c=(u+v)*b → a=b) ∧
      (∀ j : Fin 4, ∀ n≤3,
        (encoding 3 (parameter t j)).coeff n ∈ positiveAlphabet t ∧
        0≤(encoding 3 (parameter t j)).coeff n ∧
        (encoding 3 (parameter t j)).coeff n<base t) ∧
      ¬IsSidon ((univ.image (fun j : Fin 4 => naturalValue (t:ℤ) j^2)) : Set ℕ) := by
  obtain ⟨t,ht,hM,hp⟩ := arbitrarily_large_prime (max M (1452*(792*K)+509))
  have hMK : 1452*(792*K)+509<1452*t+509 :=
    (le_max_right _ _).trans_lt hM
  have hlarge : 792*K<t := by omega
  have htZ : (133:ℤ)≤t := by exact_mod_cast ht
  refine ⟨t,ht,(le_max_left _ _).trans_lt hM,hp,?_,?_,
    natural_specialization_not_sidon t (by positivity)⟩
  · intro u v hu huK hv hvK a ha b hb c hc he
    exact positiveAlphabet_weighted_free t K (by exact_mod_cast hK)
      (by exact_mod_cast hlarge) u v hu huK hv hvK a b c ha hb hc he
  · intro j n hn
    have hh := (canonical_ap_free_digits t htZ j).2.2.2 n hn
    exact ⟨coefficient_mem_positiveAlphabet t j n hn, hh.2⟩

#print axioms coefficient_positiveDigit
#print axioms positiveAlphabet_weighted_free
#print axioms arbitrarily_large_prime_weighted_obstruction
#print axioms no_bounded_weighted_average
#print axioms canonical_ap_free_digits
#print axioms natural_specialization_not_sidon
#print axioms alphabet_ap_free
#print axioms norm_difference
#print axioms value_injective
#print axioms formal_square_sidon
#print axioms specialization_not_sidon
#print axioms arbitrarily_large_prime_obstruction
end
end Erdos773.PrimeAPFreeAlphabetCarry
