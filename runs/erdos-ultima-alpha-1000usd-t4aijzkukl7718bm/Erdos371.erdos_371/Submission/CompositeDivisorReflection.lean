import Submission.SmallPrimeReflection

/-! Composite-divisor reflection and exact marked balance for the actual
largest-prime-factor comparisons. The marked multiplicities and prefix
boundary are retained. No unweighted asymptotic cancellation is asserted. -/
namespace Erdos371
open Finset

/-- The smaller prescribed divisor need not be prime. -/
lemma small_divisor_prime_pair_rise (a p m : ℕ) (hp : p.Prime)
    (ha : 0<a) (hap : a<p) (hm : 0 < m) (hsize : m<a*p)
    (ham : a∣m) (hpm : p∣m+1) :
    Nat.maxPrimeFac m<p ∧ Nat.maxPrimeFac (m+1)=p := by
  have hk : 0 < m/a := Nat.div_pos (Nat.le_of_dvd hm ham) ha
  have hkp : m/a<p := (Nat.div_lt_iff_lt_mul ha).mpr (by nlinarith)
  have hmfac : Nat.maxPrimeFac m = max (Nat.maxPrimeFac a) (Nat.maxPrimeFac (m/a)) := by
    conv_lhs => rw [← Nat.mul_div_cancel' ham]
    rw [Nat.maxPrimeFac_mul ha.ne' hk.ne']
  have hj : 0<(m+1)/p := Nat.div_pos (Nat.le_of_dvd (by omega) hpm) hp.pos
  have hja : (m+1)/p≤a := by
    have hle : m+1≤a*p := by omega
    simpa only [Nat.mul_div_cancel a hp.pos] using Nat.div_le_div_right (c := p) hle
  have hjp : Nat.maxPrimeFac ((m+1)/p)<p := Nat.maxPrimeFac_le.trans_lt (hja.trans_lt hap)
  constructor
  · rw [hmfac]
    exact max_lt (Nat.maxPrimeFac_le.trans_lt hap) (Nat.maxPrimeFac_le.trans_lt hkp)
  · calc
      _ = Nat.maxPrimeFac (p*((m+1)/p)) := congrArg Nat.maxPrimeFac (Nat.mul_div_cancel' hpm).symm
      _ = p := by rw [Nat.maxPrimeFac_mul hp.ne_zero hj.ne',hp.maxPrimeFac_eq_self,max_eq_left hjp.le]

lemma small_divisor_prime_pair_fall (a p m : ℕ) (hp : p.Prime)
    (ha : 0<a) (hap : a<p) (hm : 0 < m) (hsize : m<a*p)
    (hpm : p∣m) (ham : a∣m+1) :
    Nat.maxPrimeFac m=p ∧ Nat.maxPrimeFac (m+1)<p := by
  have hstrict : m+1<a*p := by
    by_contra h
    have he : m+1=a*p := by omega
    have hd : p∣1 := (Nat.dvd_add_iff_right hpm).mpr (by rw [he]; exact Nat.dvd_mul_left p a)
    exact hp.not_dvd_one hd
  have hk : 0 < m/p := Nat.div_pos (Nat.le_of_dvd hm hpm) hp.pos
  have hka : m/p<a := (Nat.div_lt_iff_lt_mul hp.pos).mpr (by nlinarith)
  have hkp : Nat.maxPrimeFac (m/p)<p := Nat.maxPrimeFac_le.trans_lt (hka.trans hap)
  have hj : 0<(m+1)/a := Nat.div_pos (Nat.le_of_dvd (by omega) ham) ha
  have hjp : (m+1)/a<p := (Nat.div_lt_iff_lt_mul ha).mpr (by nlinarith)
  constructor
  · calc
      _ = Nat.maxPrimeFac (p*(m/p)) := congrArg Nat.maxPrimeFac (Nat.mul_div_cancel' hpm).symm
      _ = p := by rw [Nat.maxPrimeFac_mul hp.ne_zero hk.ne',hp.maxPrimeFac_eq_self,max_eq_left hkp.le]
  · calc
      _ = max (Nat.maxPrimeFac a) (Nat.maxPrimeFac ((m+1)/a)) := by
        conv_lhs => rw [← Nat.mul_div_cancel' ham]
        rw [Nat.maxPrimeFac_mul ha.ne' hj.ne']
      _ < p := max_lt (Nat.maxPrimeFac_le.trans_lt hap) (Nat.maxPrimeFac_le.trans_lt hjp)

/-- Composite marked reflections reverse actual comparisons, without
assuming primality of the smaller divisor. -/
theorem composite_divisor_reflection_rise (n a p : ℕ) (hp : p.Prime)
    (ha : 1<a) (hap : a<p) (han : a∣n) (hpn : p∣n+1) :
    Nat.maxPrimeFac (divisorReflection n a p)=p ∧
      Nat.maxPrimeFac (divisorReflection n a p+1)<p := by
  have hb := divisorReflection_bounds n a p ha hp.one_lt han hpn
  have hc := divisor_pair_coprime n a p han hpn
  apply small_divisor_prime_pair_fall a p _ hp (by omega) hap (by omega) hb.2
  · rw [divisorReflection_eq_root n a p ha hp.one_lt han hpn]
    exact adjacentRoot_dvd_left _ _ _
  · rw [divisorReflection_eq_root n a p ha hp.one_lt han hpn]
    exact adjacentRoot_dvd_right _ _ _ (by omega)

lemma composite_divisor_reflection_fall (n a p : ℕ) (hp : p.Prime)
    (ha : 1<a) (hap : a<p) (hpn : p∣n) (han : a∣n+1) :
    Nat.maxPrimeFac (divisorReflection n a p)<p ∧
      Nat.maxPrimeFac (divisorReflection n a p+1)=p := by
  have hb := divisorReflection_bounds n p a hp.one_lt ha hpn han
  have hr : divisorReflection n a p=divisorReflection n p a := by
    simp only [divisorReflection,Nat.mul_comm]
  rw [hr]
  apply small_divisor_prime_pair_rise a p _ hp (by omega) hap (by omega)
    (by simpa only [Nat.mul_comm] using hb.2)
  · rw [divisorReflection_eq_root n p a hp.one_lt ha hpn han]
    exact adjacentRoot_dvd_left _ _ _
  · rw [divisorReflection_eq_root n p a hp.one_lt ha hpn han]
    exact adjacentRoot_dvd_right _ _ _ hp.pos

/-- Any divisor between one and the winning prime gives a sign-reversing
reflection. This is not a statement about its input or output distribution. -/
theorem composite_losing_divisor_reflection (n a : ℕ) (hn : 1<n)
    (ha : 1<a) (hap : a<primeWinner n) (had : a∣losingNumber n) :
    factorSign (divisorReflection n a (primeWinner n))= -factorSign n ∧
      primeWinner (divisorReflection n a (primeWinner n))=primeWinner n := by
  by_cases h : Nat.maxPrimeFac n<Nat.maxPrimeFac (n+1)
  · have hw : primeWinner n=Nat.maxPrimeFac (n+1) := max_eq_right h.le
    rw [hw] at hap ⊢
    have hd : a∣n := by simpa only [losingNumber,if_pos h] using had
    have hr := composite_divisor_reflection_rise n a (Nat.maxPrimeFac (n+1))
      (Nat.prime_maxPrimeFac_of_one_lt (n+1) (by omega)) ha hap hd Nat.maxPrimeFac_dvd
    constructor
    · simp only [factorSign,predicateSign,hr.1,if_neg hr.2.not_gt,if_pos h]
    · simp only [primeWinner,hr.1,max_eq_left hr.2.le]
  · have hw : primeWinner n=Nat.maxPrimeFac n := max_eq_left (not_lt.mp h)
    rw [hw] at hap ⊢
    have hd : a∣n+1 := by simpa only [losingNumber,if_neg h] using had
    have hr := composite_divisor_reflection_fall n a (Nat.maxPrimeFac n)
      (Nat.prime_maxPrimeFac_of_one_lt n hn) ha hap Nat.maxPrimeFac_dvd hd
    constructor
    · simp only [factorSign,predicateSign,hr.2,if_pos hr.1,if_neg h,neg_neg]
    · simp only [primeWinner,hr.2,max_eq_right hr.1.le]

/-- Each mark records both factors of a smaller-prime-factor neighbour.
The first factor is retained by reflection. -/
def riseDivisorMarks (p : ℕ) : Finset (ℕ×ℕ) :=
  ((Ico 2 p).product (Ico 1 p)).filter (fun ab => p∣ab.1*ab.2+1)

def fallDivisorMarks (p : ℕ) : Finset (ℕ×ℕ) :=
  ((Ico 2 p).product (Ico 1 p)).filter (fun ab => p∣ab.1*ab.2-1)

def reflectDivisorMark (p : ℕ) (ab : ℕ×ℕ) : ℕ×ℕ := (ab.1,p-ab.2)

lemma reflectDivisorMark_rise_mem (p : ℕ) (ab : ℕ×ℕ)
    (hab : ab∈riseDivisorMarks p) : reflectDivisorMark p ab∈fallDivisorMarks p := by
  change (ab.1,p-ab.2) ∈ fallDivisorMarks p
  obtain ⟨hab,hd⟩ := mem_filter.mp hab
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨ha,ha'⟩ := mem_Ico.mp ha
  obtain ⟨hb,hb'⟩ := mem_Ico.mp hb
  have hc : 1≤p-ab.2 := by omega
  have hprod : 1≤ab.1*(p-ab.2) := by nlinarith
  have he : ab.1*(p-ab.2)-1+(ab.1*ab.2+1)=ab.1*p := by
    have hsub := Nat.sub_add_cancel hb'.le
    have hsub' := Nat.sub_add_cancel hprod
    nlinarith
  have hd' : p∣ab.1*(p-ab.2)-1 := (Nat.dvd_add_iff_left hd).mpr (by rw [he]; exact Nat.dvd_mul_left p _)
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ico.mpr ⟨ha,ha'⟩,mem_Ico.mpr ⟨hc,by omega⟩⟩,hd'⟩

lemma reflectDivisorMark_fall_mem (p : ℕ) (ab : ℕ×ℕ)
    (hab : ab∈fallDivisorMarks p) : reflectDivisorMark p ab∈riseDivisorMarks p := by
  change (ab.1,p-ab.2) ∈ riseDivisorMarks p
  obtain ⟨hab,hd⟩ := mem_filter.mp hab
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨ha,ha'⟩ := mem_Ico.mp ha
  obtain ⟨hb,hb'⟩ := mem_Ico.mp hb
  have hprod : 1≤ab.1*ab.2 := by nlinarith
  have he : ab.1*(p-ab.2)+1+(ab.1*ab.2-1)=ab.1*p := by
    have hsub := Nat.sub_add_cancel hb'.le
    have hsub' := Nat.sub_add_cancel hprod
    nlinarith
  have hd' : p∣ab.1*(p-ab.2)+1 := (Nat.dvd_add_iff_left hd).mpr (by rw [he]; exact Nat.dvd_mul_left p _)
  exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_Ico.mpr ⟨ha,ha'⟩,
    mem_Ico.mpr ⟨by omega,by omega⟩⟩,hd'⟩

lemma reflectDivisorMark_twice (p : ℕ) (ab : ℕ×ℕ) (hb : ab.2≤p) :
    reflectDivisorMark p (reflectDivisorMark p ab)=ab := by
  ext <;> simp [reflectDivisorMark,Nat.sub_sub_self hb]

/-- Transport with the mark retained is a bijection. This does not say that
the corresponding map on unmarked natural indices is injective. -/
lemma sum_fallDivisorMarks (p : ℕ) (f : ℕ×ℕ → ℝ) :
    (∑ ab ∈ fallDivisorMarks p, f ab) =
      ∑ ab ∈ riseDivisorMarks p, f (reflectDivisorMark p ab) := by
  symm
  apply sum_bij (fun ab _ => reflectDivisorMark p ab)
  · exact fun ab hab => reflectDivisorMark_rise_mem p ab hab
  · intro ab hab cd hcd he
    have hb : ab.2≤p := by have := (mem_Ico.mp (mem_product.mp (mem_filter.mp hab).1).2).2; omega
    have hd : cd.2≤p := by have := (mem_Ico.mp (mem_product.mp (mem_filter.mp hcd).1).2).2; omega
    simpa only [reflectDivisorMark_twice p ab hb,reflectDivisorMark_twice p cd hd] using
      congrArg (reflectDivisorMark p) he
  · intro ab hab
    have hb : ab.2≤p := by have := (mem_Ico.mp (mem_product.mp (mem_filter.mp hab).1).2).2; omega
    exact ⟨reflectDivisorMark p ab,reflectDivisorMark_fall_mem p ab hab,reflectDivisorMark_twice p ab hb⟩
  · intro ab hab; rfl

lemma riseDivisorMarks_actual_sign (p : ℕ) (hp : p.Prime) (ab : ℕ×ℕ)
    (hab : ab∈riseDivisorMarks p) : factorSign (ab.1*ab.2)=1 ∧ primeWinner (ab.1*ab.2)=p := by
  obtain ⟨hab,hd⟩ := mem_filter.mp hab
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨ha,ha'⟩ := mem_Ico.mp ha
  obtain ⟨hb,hb'⟩ := mem_Ico.mp hb
  have h := small_divisor_prime_pair_rise ab.1 p (ab.1*ab.2) hp (by omega) ha'
    (by positivity) (by nlinarith) (Nat.dvd_mul_right _ _) hd
  simp [factorSign,predicateSign,primeWinner,h.2,h.1,max_eq_right h.1.le]

lemma fallDivisorMarks_actual_sign (p : ℕ) (hp : p.Prime) (ab : ℕ×ℕ)
    (hab : ab∈fallDivisorMarks p) : factorSign (ab.1*ab.2-1)= -1 ∧ primeWinner (ab.1*ab.2-1)=p := by
  obtain ⟨hab,hd⟩ := mem_filter.mp hab
  obtain ⟨ha,hb⟩ := mem_product.mp hab
  obtain ⟨ha,ha'⟩ := mem_Ico.mp ha
  obtain ⟨hb,hb'⟩ := mem_Ico.mp hb
  have hab2 : 2≤ab.1*ab.2 := by nlinarith
  have he : ab.1*ab.2-1+1=ab.1*ab.2 := Nat.sub_add_cancel (by omega)
  have h := small_divisor_prime_pair_fall ab.1 p (ab.1*ab.2-1) hp (by omega) ha'
    (by omega) (by have := Nat.sub_le (ab.1*ab.2) 1; nlinarith) hd
    (by rw [he]; exact Nat.dvd_mul_right _ _)
  simp [factorSign,predicateSign,primeWinner,h.1,h.2.not_gt,max_eq_left h.2.le]

lemma riseDivisorMarks_reflection_index (p : ℕ) (ab : ℕ×ℕ)
    (hab : ab∈riseDivisorMarks p) :
    divisorReflection (ab.1*ab.2) ab.1 p=ab.1*(p-ab.2)-1 := by
  have ha := (mem_Ico.mp (mem_product.mp (mem_filter.mp hab).1).1).1
  have hb := (mem_Ico.mp (mem_product.mp (mem_filter.mp hab).1).2).2
  have hsize : ab.1*ab.2<ab.1*p := Nat.mul_lt_mul_of_pos_left hb (by omega)
  unfold divisorReflection
  rw [Nat.mod_eq_of_lt hsize,Nat.mul_sub_left_distrib]
  omega

/-- Exact balance for actual comparisons with divisor multiplicity and an
arbitrary weight on the divisor retained by reflection. -/
theorem marked_divisor_comparison_balance (p : ℕ) (hp : p.Prime) (w : ℕ → ℝ) :
    (∑ ab ∈ riseDivisorMarks p, w ab.1*factorSign (ab.1*ab.2)) +
      (∑ ab ∈ fallDivisorMarks p, w ab.1*factorSign (ab.1*ab.2-1)) = 0 := by
  rw [sum_fallDivisorMarks]
  rw [← sum_add_distrib]
  apply sum_eq_zero
  intro ab hab
  rw [(riseDivisorMarks_actual_sign p hp ab hab).1,
    (fallDivisorMarks_actual_sign p hp _ (reflectDivisorMark_rise_mem p ab hab)).1]
  simp [reflectDivisorMark]

/-- Prefix truncation leaves exactly the reflected boundary terms. No bound
making these terms negligible is asserted. -/
theorem marked_divisor_prefix_boundary (p N : ℕ) (w : ℕ → ℝ) :
    (∑ ab ∈ riseDivisorMarks p, if ab.1*ab.2<N then w ab.1 else 0) -
      (∑ ab ∈ fallDivisorMarks p, if ab.1*ab.2≤N then w ab.1 else 0) =
    ∑ ab ∈ riseDivisorMarks p,
      ((if ab.1*ab.2<N then w ab.1 else 0) -
        (if ab.1*(p-ab.2)≤N then w ab.1 else 0)) := by
  rw [sum_fallDivisorMarks,← sum_sub_distrib]
  rfl

#print axioms composite_losing_divisor_reflection
#print axioms riseDivisorMarks_reflection_index
#print axioms composite_divisor_reflection_rise
#print axioms marked_divisor_comparison_balance
#print axioms marked_divisor_prefix_boundary
end Erdos371
