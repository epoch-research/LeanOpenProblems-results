import Submission.BalancedSmoothFactorization

/-! Packing integers with prime factors below p into a bounded number of
factors below p. This is a coverage result, not a signed-count estimate. -/
namespace Erdos371

lemma exists_large_block_divisor (m p : ℕ) (hp : 2 ≤ p) (hpm : p ≤ m)
    (hmp : Nat.maxPrimeFac m < p) :
    ∃ a : ℕ, a ∣ m ∧ 2 ≤ a ∧ a < p ∧ p ≤ a^2 := by
  let k := (p-1).sqrt
  have hk : 1 ≤ k := by
    apply Nat.le_sqrt.mpr
    omega
  have hksq : k*k < p := by
    have h := Nat.sqrt_le (p-1)
    change k*k ≤ p-1 at h
    omega
  have hnext : p ≤ (k+1)^2 := by
    have h := Nat.lt_succ_sqrt (p-1)
    change p-1 < (k+1)*(k+1) at h
    have hsub : p-1+1 = p := Nat.sub_add_cancel (by omega)
    nlinarith
  have hkm : k < m := by nlinarith
  have hsq (a : ℕ) (hka : k < a) : p ≤ a^2 :=
    hnext.trans (Nat.pow_le_pow_left (by omega) 2)
  by_cases hq : k < Nat.maxPrimeFac m
  · have hpq := Nat.prime_maxPrimeFac_of_one_lt m (by omega)
    exact ⟨Nat.maxPrimeFac m,Nat.maxPrimeFac_dvd,hpq.two_le,hmp,hsq _ hq⟩
  · obtain ⟨a,had,hka,ha⟩ := exists_divisor_above_le_mul_maxPrimeFac m k hk hkm
    have hap : a < p := (ha.trans (Nat.mul_le_mul_left k (not_lt.mp hq))).trans_lt hksq
    exact ⟨a,had,by omega,hap,hsq a hka⟩

/-- All blocks except a final remainder have square at least p. -/
theorem smooth_factor_packing (p : ℕ) : ∀ m : ℕ, 0 < m → Nat.maxPrimeFac m < p →
    ∃ (L : List ℕ) (b : ℕ), L.prod*b = m ∧ 1 ≤ b ∧ b < p ∧
      ∀ a ∈ L, 2 ≤ a ∧ a < p ∧ p ≤ a^2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm hmp
    by_cases hsmall : m < p
    · exact ⟨[],m,by simp,hm,hsmall,by simp⟩
    have hp : 2 ≤ p := by
      by_cases hm1 : m = 1
      · subst m
        simpa using hmp
      · have hq := (Nat.prime_maxPrimeFac_of_one_lt m (by omega)).two_le
        omega
    obtain ⟨a,had,ha,hap,hasq⟩ := exists_large_block_divisor m p hp (by omega) hmp
    have ha0 : 0 < a := by omega
    have hquot : 0 < m/a := Nat.div_pos (Nat.le_of_dvd hm had) ha0
    have hlt : m/a < m := Nat.div_lt_self hm (by omega)
    have he : a*(m/a) = m := Nat.mul_div_cancel' had
    have hqmax : Nat.maxPrimeFac (m/a) ≤ Nat.maxPrimeFac m := by
      calc
        _ ≤ max (Nat.maxPrimeFac a) (Nat.maxPrimeFac (m/a)) := le_max_right _ _
        _ = Nat.maxPrimeFac (a*(m/a)) := (Nat.maxPrimeFac_mul ha0.ne' hquot.ne').symm
        _ = _ := congrArg Nat.maxPrimeFac he
    obtain ⟨L,b,hprod,hb,hbp,hL⟩ := ih (m/a) hlt hquot (hqmax.trans_lt hmp)
    refine ⟨a::L,b,?_,hb,hbp,?_⟩
    · simp only [List.prod_cons,mul_assoc,hprod,he]
    · intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ⟨ha,hap,hasq⟩
      · exact hL c hc

lemma list_length_power_le_prod_square (p : ℕ) (L : List ℕ)
    (hL : ∀ a ∈ L, p ≤ a^2) : p^L.length ≤ L.prod^2 := by
  induction L with
  | nil => simp
  | cons a L ih =>
    have ha := hL a (by simp)
    have hs := ih (fun b hb => hL b (by simp [hb]))
    simp only [List.length_cons,List.prod_cons]
    calc
      p^(L.length+1) = p*p^L.length := by rw [pow_succ,Nat.mul_comm]
      _ ≤ a^2*L.prod^2 := Nat.mul_le_mul ha hs
      _ = (a*L.prod)^2 := (mul_pow _ _ _).symm

/-- A power-size condition gives a bounded-length representation. Ones are
allowed so that representations can later be padded to an exact length. -/
theorem exists_bounded_factor_list (m p K : ℕ) (hm : 0 < m)
    (hmp : Nat.maxPrimeFac m < p) (hsize : m^2 < p^K) :
    ∃ L : List ℕ, L.prod = m ∧ L.length ≤ K ∧ ∀ a ∈ L, 1 ≤ a ∧ a < p := by
  obtain ⟨L,b,he,hb,hbp,hL⟩ := smooth_factor_packing p m hm hmp
  have hp : 1 < p := hb.trans_lt hbp
  have hpow := list_length_power_le_prod_square p L (fun a ha => (hL a ha).2.2)
  have hprod : L.prod ≤ m := by nlinarith
  have hlen : L.length < K := (Nat.pow_lt_pow_iff_right hp).mp
    ((hpow.trans (Nat.pow_le_pow_left hprod 2)).trans_lt hsize)
  refine ⟨L++[b],?_,?_,?_⟩
  · simpa only [List.prod_append,List.prod_singleton] using he
  · simp only [List.length_append,List.length_singleton]
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨by have := (hL a ha).1; omega,(hL a ha).2.1⟩
    · have hab : a = b := List.mem_singleton.mp ha
      subst a
      exact ⟨hb,hbp⟩

/-- An exact-length representation, obtained by padding with ones. -/
theorem exists_exact_factor_list (m p K : ℕ) (hm : 0 < m)
    (hmp : Nat.maxPrimeFac m < p) (hsize : m^2 < p^K) :
    ∃ L : List ℕ, L.prod = m ∧ L.length = K ∧ ∀ a ∈ L, 1 ≤ a ∧ a < p := by
  obtain ⟨L,he,hLK,hL⟩ := exists_bounded_factor_list m p K hm hmp hsize
  have hp : 1 < p := by
    by_cases hm1 : m = 1
    · simpa only [hm1,Nat.maxPrimeFac_one] using hmp
    · have hq := (Nat.prime_maxPrimeFac_of_one_lt m (by omega)).two_le
      omega
  refine ⟨List.replicate (K-L.length) 1 ++ L,?_,?_,?_⟩
  · simp only [List.prod_append,List.prod_replicate,one_pow,one_mul,he]
  · simp only [List.length_append,List.length_replicate]
    omega
  · intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · have ha1 : a = 1 := (List.mem_replicate.mp ha).2
      subst a
      exact ⟨le_rfl,hp⟩
    · exact hL a ha

#print axioms exists_large_block_divisor
#print axioms smooth_factor_packing
#print axioms exists_bounded_factor_list
#print axioms exists_exact_factor_list
end Erdos371
