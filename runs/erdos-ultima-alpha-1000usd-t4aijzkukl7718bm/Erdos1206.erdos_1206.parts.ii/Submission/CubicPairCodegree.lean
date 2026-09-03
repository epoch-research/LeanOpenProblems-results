import Submission.DivisorPowerBound

/-! Divisor bounds for sums and differences of two cubes, and hence for
completions of a fixed pair in a cubic collision. No linear total collision
bound is asserted. -/
namespace Erdos1206.CubicPairCodegree
open Finset

private lemma fixed_sum_injective {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (hs : a+b=c+d) (he : a^3+b^3=c^3+d^3) : a=c ∧ b=d := by
  have hsZ : (a:ℤ)+b=c+d := by exact_mod_cast hs
  have heZ : (a:ℤ)^3+b^3=c^3+d^3 := by exact_mod_cast he
  have hd : (d:ℤ)=a+b-c := by omega
  have hf : (3:ℤ)*((a:ℤ)-c)*((a:ℤ)-d)*((a:ℤ)+b)=0 := by
    rw [hd] at heZ ⊢
    linear_combination heZ
  have hs0 : (a:ℤ)+b≠0 := by omega
  have hh := (mul_eq_zero.mp hf).resolve_right hs0
  have hh' : (a:ℤ)=c ∨ (a:ℤ)=d := by
    rcases mul_eq_zero.mp hh with h | h
    · exact Or.inl (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left (by norm_num)))
    · exact Or.inr (sub_eq_zero.mp h)
  rcases hh' with h | h
  · have h' : a=c := by exact_mod_cast h
    exact ⟨h',by omega⟩
  · omega

private lemma fixed_gap_injective {a b c d : ℕ} (hab : a < b) (hcd : c < d)
    (hg : b-a=d-c) (he : b^3+c^3=a^3+d^3) : a=c ∧ b=d := by
  let h : ℤ := (b:ℤ)-a
  have hh : 0<h := by dsimp [h]; omega
  have hb : (b:ℤ)=a+h := by dsimp [h]; ring
  have hd : (d:ℤ)=c+h := by dsimp [h]; omega
  have heZ : (b:ℤ)^3+c^3=a^3+d^3 := by exact_mod_cast he
  have hf : (3:ℤ)*h*((a:ℤ)-c)*((a:ℤ)+c+h)=0 := by
    rw [hb,hd] at heZ
    linear_combination heZ
  have hz : (3:ℤ)*h≠0 := by positivity
  have hs : (a:ℤ)+c+h≠0 := by omega
  have haZ := sub_eq_zero.mp ((mul_eq_zero.mp ((mul_eq_zero.mp hf).resolve_right hs)).resolve_left hz)
  have ha : a=c := by exact_mod_cast haZ
  exact ⟨ha,by omega⟩

def sumPairs (N s : ℕ) : Finset (ℕ×ℕ) :=
  ((range N) ×ˢ (range N)).filter (fun p => p.1 < p.2 ∧ p.1^3+p.2^3=s)

def diffPairs (N s : ℕ) : Finset (ℕ×ℕ) :=
  ((range N) ×ˢ (range N)).filter (fun p => p.1 < p.2 ∧ p.2^3=p.1^3+s)

lemma mem_sumPairs {N s a b : ℕ} : (a,b) ∈ sumPairs N s ↔
    a < N ∧ b < N ∧ a < b ∧ a^3+b^3=s := by
  simp [sumPairs,and_assoc]

lemma mem_diffPairs {N s a b : ℕ} : (a,b) ∈ diffPairs N s ↔
    a < N ∧ b < N ∧ a < b ∧ b^3=a^3+s := by
  simp [diffPairs,and_assoc]

/-- A fixed root sum determines an unordered cubic-sum representation. -/
theorem sumPairs_card_le (N s : ℕ) (hs : 0 < s) :
    (sumPairs N s).card ≤ s.divisors.card := by
  apply card_le_card_of_injOn (fun p : ℕ×ℕ => p.1+p.2)
  · rintro ⟨a,b⟩ hp
    obtain ⟨_,_,_,he⟩ := mem_sumPairs.mp hp
    apply Nat.mem_divisors.mpr
    refine ⟨?_,hs.ne'⟩
    rw [←he]
    exact Odd.nat_add_dvd_pow_add_pow a b (by decide : Odd 3)
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd heq
    obtain ⟨_,_,hab',he⟩ := mem_sumPairs.mp hab
    obtain ⟨_,_,hcd',he'⟩ := mem_sumPairs.mp hcd
    obtain ⟨h₁,h₂⟩ := fixed_sum_injective hab' hcd' heq (he.trans he'.symm)
    simp [h₁,h₂]

/-- A fixed positive root gap determines a cubic-difference representation. -/
theorem diffPairs_card_le (N s : ℕ) (hs : 0 < s) :
    (diffPairs N s).card ≤ s.divisors.card := by
  apply card_le_card_of_injOn (fun p : ℕ×ℕ => p.2-p.1)
  · rintro ⟨a,b⟩ hp
    obtain ⟨_,_,_,he⟩ := mem_diffPairs.mp hp
    apply Nat.mem_divisors.mpr
    refine ⟨?_,hs.ne'⟩
    have hd := Nat.sub_dvd_pow_sub_pow b a 3
    rwa [he,Nat.add_sub_cancel_left] at hd
  · rintro ⟨a,b⟩ hab ⟨c,d⟩ hcd heq
    obtain ⟨_,_,hab',he⟩ := mem_diffPairs.mp hab
    obtain ⟨_,_,hcd',he'⟩ := mem_diffPairs.mp hcd
    obtain ⟨h₁,h₂⟩ := fixed_gap_injective hab' hcd' heq (by omega)
    simp [h₁,h₂]

/-- For `x<y` and `a<b`, a nontrivial pairing of the four cube values is
one of these two possibilities. Including trivial completions only enlarges
this set and is harmless for its upper bound. -/
def completions (N x y : ℕ) : Finset (ℕ×ℕ) :=
  sumPairs N (x^3+y^3) ∪ diffPairs N (y^3-x^3)

theorem completions_card_le {x y : ℕ} (hxy : x < y) (N : ℕ) :
    (completions N x y).card ≤ (x^3+y^3).divisors.card+(y^3-x^3).divisors.card := by
  have hs : 0 < x^3+y^3 := by
    have hy0 : 0 < y := by omega
    positivity
  have hd : 0 < y^3-x^3 := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hxy (by decide : 3≠0))
  exact card_union_le _ _ |>.trans (Nat.add_le_add (sumPairs_card_le N _ hs) (diffPairs_card_le N _ hd))

def codegreeConstant : ℕ := 2*(2*DivisorPowerBound.constant 12+1)

/-- In a prefix of length `t^12`, pair-completion counts are at most a
constant times `t^3`, i.e. the fourth root of the prefix length. -/
theorem completions_card_le_power {x y t : ℕ} (hxy : x < y) (hy : y < t^12) :
    (completions (t^12) x y).card ≤ codegreeConstant*t^3 := by
  have hx3 : x^3 ≤ t^36 := by
    have h := Nat.pow_le_pow_left (hxy.trans hy).le 3
    simpa only [←pow_mul] using h
  have hy3 : y^3 ≤ t^36 := by
    have h := Nat.pow_le_pow_left hy.le 3
    simpa only [←pow_mul] using h
  have hs : 0 < x^3+y^3 := by
    have hy0 : 0 < y := by omega
    positivity
  have hd : 0 < y^3-x^3 := Nat.sub_pos_of_lt (Nat.pow_lt_pow_left hxy (by decide : 3≠0))
  have h₁ := DivisorPowerBound.card_divisors_le_at_power_cutoff hs (by omega : x^3+y^3 ≤ 2*t^36)
  have h₂ := DivisorPowerBound.card_divisors_le_at_power_cutoff hd (by omega : y^3-x^3 ≤ 2*t^36)
  have h := (completions_card_le hxy (t^12)).trans (Nat.add_le_add h₁ h₂)
  change _ ≤ 2*(2*DivisorPowerBound.constant 12+1)*t^3
  rw [Nat.mul_assoc,two_mul]
  exact h

#print axioms sumPairs_card_le
#print axioms diffPairs_card_le
#print axioms completions_card_le_power
end Erdos1206.CubicPairCodegree
