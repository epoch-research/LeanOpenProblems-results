import FormalConjecturesUtil

/-! Binary exponent separation for a prospective trace obstruction.
This file does not claim an extremal-graph result. -/
namespace Erdos713SuzukiTraceExponentSeparation
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

lemma two_pow_mod_eight (n : ℕ) :
    2^n % 8 = if n = 0 then 1 else if n = 1 then 2 else if n = 2 then 4 else 0 := by
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  rcases n with _ | n
  · norm_num
  have he : n+1+1+1 = 3+n := by omega
  rw [he, pow_add]
  simp [show 3+n ≠ 1 by omega, show 3+n ≠ 2 by omega]

lemma pow_seven_ne (a k : ℕ) : 2^k ≠ 7*2^a := by
  intro h
  have h₁ : 2^(a+2) < 2^k := by rw [h,pow_add]; norm_num; nlinarith [Nat.two_pow_pos a]
  have h₂ : 2^k < 2^(a+3) := by rw [h,pow_add]; norm_num; nlinarith [Nat.two_pow_pos a]
  have h₃ : a+2 < k := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h₁
  have h₄ : k < a+3 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h₂
  omega

lemma isolated_negative_zero (r i l j k : ℕ) (hr : 4 ≤ r)
    (hd : i+r=l ∨ l+r=i ∨ i+(r-1)=l ∨ l+(r-1)=i)
    (h : 2^j+2^k = 3+3*2^r+2^i+2^l) :
    i=0 ∨ l=0 := by
  have hp : 8 ≤ 2^r := (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ r))
  have hi := Nat.two_pow_pos i
  have hl := Nat.two_pow_pos l
  have hm := congrArg (fun n : ℕ => n % 8) h
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,two_pow_mod_eight] at hm
  split_ifs at hm <;> first | omega | (norm_num at hm <;> subst_vars <;> norm_num at h <;> omega)

lemma positive_indices (r l j k : ℕ) (hr : 4 ≤ r) (hl : 3 ≤ l)
    (h : 2^j+2^k = 3+3*2^r+2^0+2^l) :
    (j=2 ∧ 3 ≤ k) ∨ (k=2 ∧ 3 ≤ j) := by
  have hp : 8 ≤ 2^r := (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (by omega : 3 ≤ r))
  have hlpos := Nat.two_pow_pos l
  have hm := congrArg (fun n : ℕ => n % 8) h
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,two_pow_mod_eight] at hm
  split_ifs at hm <;> first | omega | (norm_num at hm <;> subst_vars <;> norm_num at h <;> omega)

lemma positive_large_index (r l k : ℕ) (hr : 4 ≤ r) (hl : l=r ∨ l=r-1)
    (h : 2^2+2^k = 3+3*2^r+2^0+2^l) : l=r ∧ k=r+2 := by
  rcases hl with hl | hl
  · subst l
    constructor
    · rfl
    · have he : 2^k = 2^(r+2) := by rw [pow_add]; norm_num at h ⊢; omega
      exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he
  · subst l
    have hr' : r = (r-1)+1 := by omega
    have he : 2^k = 7*2^(r-1) := by
      conv_lhs at h => rw [show (2:ℕ)^2=4 by decide]
      conv_rhs at h => rw [show (2:ℕ)^0=1 by decide]
      have hp : 2^r = 2^(r-1)*2 := by conv_lhs => rw [hr']; rw [pow_succ]
      rw [hp] at h
      omega
    exact (pow_seven_ne (r-1) k he).elim

lemma two_positive_two_negative (r i l j k : ℕ) (hr : 4 ≤ r)
    (hd : i+r=l ∨ l+r=i ∨ i+(r-1)=l ∨ l+(r-1)=i)
    (h : 2^j+2^k = 3+3*2^r+2^i+2^l) :
    ((i=0 ∧ l=r) ∨ (l=0 ∧ i=r)) ∧
      ((j=2 ∧ k=r+2) ∨ (k=2 ∧ j=r+2)) := by
  have aux (l j k : ℕ) (hl : l=r ∨ l=r-1)
      (he : 2^j+2^k = 3+3*2^r+2^0+2^l) :
      l=r ∧ ((j=2 ∧ k=r+2) ∨ (k=2 ∧ j=r+2)) := by
    have hl3 : 3 ≤ l := by omega
    rcases positive_indices r l j k hr hl3 he with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · obtain ⟨hlr,hk⟩ := positive_large_index r l k hr hl he
      exact ⟨hlr,Or.inl ⟨rfl,hk⟩⟩
    · have he' : 2^2+2^j = 3+3*2^r+2^0+2^l := by omega
      obtain ⟨hlr,hj⟩ := positive_large_index r l j hr hl he'
      exact ⟨hlr,Or.inr ⟨rfl,hj⟩⟩
  rcases isolated_negative_zero r i l j k hr hd h with rfl | rfl
  · have hl : l=r ∨ l=r-1 := by omega
    obtain ⟨hlr,hjk⟩ := aux l j k hl h
    exact ⟨Or.inl ⟨rfl,hlr⟩,hjk⟩
  · have hi : i=r ∨ i=r-1 := by omega
    have he : 2^j+2^k = 3+3*2^r+2^0+2^i := by omega
    obtain ⟨hir,hjk⟩ := aux i j k hi he
    exact ⟨Or.inr ⟨rfl,hir⟩,hjk⟩

lemma negative_total_bound (r i l : ℕ) (hr : 4 ≤ r)
    (hi : i < 2*r-1) (hl : l < 2*r-1)
    (hd : i+r=l ∨ l+r=i ∨ i+(r-1)=l ∨ l+(r-1)=i) :
    3+3*2^r+2^i+2^l < 2^(2*r-1)-1 := by
  have hp : 8 ≤ 2^(r-1) := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ r-1)
  have hpR : 2^r = 2^(r-1)*2 := by
    conv_lhs => rw [show r=(r-1)+1 by omega]
    rw [pow_succ]
  have hpM : 2^(2*r-1) = (2^(r-1))^2*2 := by
    rw [← pow_mul, ← pow_succ]
    congr 1
    omega
  have hpH : 2^(2*r-2) = (2^(r-1))^2 := by
    rw [← pow_mul]
    congr 1
    omega
  have hSmall : i ≤ r-1 ∨ l ≤ r-1 := by omega
  have hSum : 2^i+2^l ≤ 2^(2*r-2)+2^(r-1) := by
    rcases hSmall with hs | hs
    · have h₁ : 2^i ≤ 2^(r-1) := Nat.pow_le_pow_right (by decide) hs
      have h₂ : 2^l ≤ 2^(2*r-2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
    · have h₁ : 2^l ≤ 2^(r-1) := Nat.pow_le_pow_right (by decide) hs
      have h₂ : 2^i ≤ 2^(2*r-2) := Nat.pow_le_pow_right (by decide) (by omega)
      omega
  rw [hpR,hpM]
  rw [hpH] at hSum
  have : 3+3*(2^(r-1)*2)+2^i+2^l+1 < (2^(r-1))^2*2 := by nlinarith
  omega

lemma two_positive_modular (r i l j k : ℕ) (hr : 4 ≤ r)
    (hi : i < 2*r-1) (hl : l < 2*r-1)
    (hj : j < 2*r-1) (hk : k < 2*r-1)
    (hd : i+r=l ∨ l+r=i ∨ i+(r-1)=l ∨ l+(r-1)=i)
    (h : Nat.ModEq (2^(2*r-1)-1) (2^j+2^k) (3+3*2^r+2^i+2^l)) :
    ((i=0 ∧ l=r) ∨ (l=0 ∧ i=r)) ∧
      ((j=2 ∧ k=r+2) ∨ (k=2 ∧ j=r+2)) := by
  have hB := negative_total_bound r i l hr hi hl hd
  have hj' : 2^j ≤ 2^(2*r-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk' : 2^k ≤ 2^(2*r-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hQ : 2^(2*r-1) = 2^(2*r-2)*2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hpos := Nat.two_pow_pos r
  have hipos := Nat.two_pow_pos i
  have hlpos := Nat.two_pow_pos l
  have hsumpos := Nat.two_pow_pos j
  have hkpos := Nat.two_pow_pos k
  have he : 2^j+2^k = 3+3*2^r+2^i+2^l := by
    apply h.eq_of_abs_lt
    rw [abs_lt]
    constructor <;> omega
  exact two_positive_two_negative r i l j k hr hd he

lemma shifted_index (r i : ℕ) (hr : 4 ≤ r) (hi : i < 2*r-1) :
    i+r=(i+r)%(2*r-1) ∨ (i+r)%(2*r-1)+(r-1)=i := by
  by_cases h : i+r < 2*r-1
  · exact Or.inl (Nat.mod_eq_of_lt h).symm
  · have he : (i+r)%(2*r-1) = i+r-(2*r-1) := by
      rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]
    rw [he]
    omega

/-- Exactly one negative index and two ordered positive pairs can
contribute to the coefficient with exponent `3+3*2^r`. -/
lemma unique_coefficient (r i j k : ℕ) (hr : 4 ≤ r)
    (hi : i < 2*r-1) (hj : j < 2*r-1) (hk : k < 2*r-1) :
    Nat.ModEq (2^(2*r-1)-1) (2^j+2^k)
      (3+3*2^r+2^i+2^((i+r)%(2*r-1))) ↔
    i=0 ∧ ((j=2 ∧ k=r+2) ∨ (k=2 ∧ j=r+2)) := by
  constructor
  · intro h
    have hl : (i+r)%(2*r-1) < 2*r-1 := Nat.mod_lt _ (by omega)
    have hd : i+r=(i+r)%(2*r-1) ∨ (i+r)%(2*r-1)+r=i ∨
        i+(r-1)=(i+r)%(2*r-1) ∨ (i+r)%(2*r-1)+(r-1)=i := by
      rcases shifted_index r i hr hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    obtain ⟨hneg,hpos⟩ := two_positive_modular r i ((i+r)%(2*r-1)) j k hr hi hl hj hk hd h
    refine ⟨?_,hpos⟩
    rcases hneg with h | ⟨hl0,hir⟩
    · exact h.1
    · subst i
      have hrr : (r+r)%(2*r-1)=1 := by
        rw [Nat.mod_eq_sub_mod (by omega)]
        have : r+r-(2*r-1)=1 := by omega
        rw [this,Nat.mod_eq_of_lt (by omega)]
      omega
  · rintro ⟨rfl,hpos⟩
    have hmod : (0+r)%(2*r-1)=r := by rw [zero_add,Nat.mod_eq_of_lt (by omega)]
    rw [hmod]
    rcases hpos with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals
      apply congrArg (fun n : ℕ => n % (2^(2*r-1)-1))
      simp only [pow_add,pow_zero]
      norm_num
      omega

lemma no_single_with_negative (r i j : ℕ) (hr : 4 ≤ r)
    (hi : i < 2*r-1) (hj : j < 2*r-1) :
    ¬ Nat.ModEq (2^(2*r-1)-1) (2^j)
      (3+3*2^r+2^i+2^((i+r)%(2*r-1))) := by
  intro h
  by_cases hj0 : j=0
  · subst j
    have hl := Nat.mod_lt (i+r) (by omega : 0 < 2*r-1)
    have hd : i+r=(i+r)%(2*r-1) ∨ (i+r)%(2*r-1)+r=i ∨
        i+(r-1)=(i+r)%(2*r-1) ∨ (i+r)%(2*r-1)+(r-1)=i := by
      rcases shifted_index r i hr hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inr h))
    have hB := negative_total_bound r i ((i+r)%(2*r-1)) hr hi hl hd
    have hp := Nat.two_pow_pos r
    have hip := Nat.two_pow_pos i
    have hlp := Nat.two_pow_pos ((i+r)%(2*r-1))
    have he := h.eq_of_lt_of_lt (by simpa using (show 1 < 2^(2*r-1)-1 by omega)) hB
    norm_num at he
    omega
  · have he : 2^j = 2^(j-1)+2^(j-1) := by
      conv_lhs => rw [show j=(j-1)+1 by omega]
      rw [pow_succ]
      omega
    rw [he] at h
    have hc := (unique_coefficient r i (j-1) (j-1) hr hi (by omega) (by omega)).mp h
    omega

lemma no_two_without_negative (r j k : ℕ) (hr : 4 ≤ r)
    (hj : j < 2*r-1) (hk : k < 2*r-1) :
    ¬ Nat.ModEq (2^(2*r-1)-1) (2^j+2^k) (3+3*2^r) := by
  intro h
  have hB := negative_total_bound r 0 r hr (by omega) (by omega) (Or.inl (by omega))
  have hp : 8 ≤ 2^r := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 3 ≤ r)
  have hj' : 2^j ≤ 2^(2*r-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hk' : 2^k ≤ 2^(2*r-2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hQ : 2^(2*r-1) = 2^(2*r-2)*2 := by
    rw [← pow_succ]
    congr 1
    omega
  have hjp := Nat.two_pow_pos j
  have hkp := Nat.two_pow_pos k
  have he : 2^j+2^k = 3+3*2^r := by
    apply h.eq_of_abs_lt
    rw [abs_lt]
    constructor <;> omega
  have hm := congrArg (fun n : ℕ => n % 8) he
  simp only [Nat.add_mod,Nat.mul_mod,Nat.mod_mod,two_pow_mod_eight] at hm
  split_ifs at hm <;> first | omega |
    (norm_num at hm <;> subst_vars <;> norm_num at he)

lemma no_single_without_negative (r j : ℕ) (hr : 4 ≤ r)
    (hj : j < 2*r-1) :
    ¬ Nat.ModEq (2^(2*r-1)-1) (2^j) (3+3*2^r) := by
  intro h
  by_cases hj0 : j=0
  · subst j
    have hB := negative_total_bound r 0 r hr (by omega) (by omega) (Or.inl (by omega))
    have hp := Nat.two_pow_pos r
    have he := h.eq_of_lt_of_lt (by simpa using (show 1 < 2^(2*r-1)-1 by omega)) (by omega)
    norm_num at he
    omega
  · have he : 2^j = 2^(j-1)+2^(j-1) := by
      conv_lhs => rw [show j=(j-1)+1 by omega]
      rw [pow_succ]
      omega
    rw [he] at h
    exact no_two_without_negative r (j-1) (j-1) hr (by omega) (by omega) h

end Erdos713SuzukiTraceExponentSeparation
