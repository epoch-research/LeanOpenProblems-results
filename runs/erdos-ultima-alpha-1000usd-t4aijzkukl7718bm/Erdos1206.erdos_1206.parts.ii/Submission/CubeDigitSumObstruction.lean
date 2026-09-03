import Submission.DigitSumObstruction

/-! A uniform obstruction to colorings by the digit sum of the cube.
This does not rule out arbitrary root sets of positive density. -/
namespace Erdos1206.CubeDigitSumObstruction

lemma digit_sum_block {b k x : ℕ} (hb : 1 < b) (hx : x < b^k) (y : ℕ) :
    (b.digits (x+b^k*y)).sum = (b.digits x).sum+(b.digits y).sum := by
  let L := Nat.digitsAppend b k x
  let H := b.digits y
  have hlen : L.length=k := Nat.length_digitsAppend hb k hx
  have hL : ∀ d ∈ L, d < b := fun d hd => Nat.lt_of_mem_digitsAppend hb k d hd
  have hH : ∀ d ∈ H, d < b := fun d hd => Nat.digits_lt_base hb hd
  have hLH : ∀ d ∈ L++H, d < b := by
    intro d hd
    exact (List.mem_append.mp hd).elim (hL d) (hH d)
  have hval : Nat.ofDigits b (L++H)=x+b^k*y := by
    rw [Nat.ofDigits_append,hlen]
    simp [L,H,Nat.digitsAppend,Nat.ofDigits_append_replicate_zero,Nat.ofDigits_digits]
  rw [←hval,Nat.sum_digits_ofDigits_eq_sum hb
    (l := (L++H).length) ⟨rfl,hLH⟩,List.sum_append]
  simp [L,H,Nat.digitsAppend]

lemma digit_sum_complement {b k m : ℕ} (hb : 1 < b)
    (hm : 0 < m) (hmb : m ≤ b^k) :
    (b.digits (b^k-m)).sum+(b.digits (m-1)).sum=(b-1)*k := by
  have hB : 0 < b^k := pow_pos (by omega) _
  have hlt : b^k-m < b^k := by omega
  have hval : m*(b^k-1)=(b^k-m)+b^k*(m-1) := by
    have h₁ : b^k-1+1=b^k := by omega
    have h₂ : m-1+1=m := by omega
    have h₃ : b^k-m+m=b^k := by omega
    nlinarith
  have hh := DigitSumObstruction.digit_sum_mul_pow_sub_one hb hm hmb
  rwa [hval,digit_sum_block hb hlt] at hh

/-- The four radix blocks occur in complementary pairs. -/
lemma cube_block_identity {B m : ℕ} (hm : 0 < m) (hBm : 3*m ≤ B) :
    m*(B-1)^3=(B-m)+B*((3*m-1)+B*((B-3*m)+B*(m-1))) := by
  have h₁ : 1 ≤ B := by omega
  have h₂ : m ≤ B := by omega
  have h₃ : 1 ≤ m := by omega
  have h₄ : 1 ≤ 3*m := by omega
  zify [h₁,h₂,h₃,h₄,hBm]
  ring

/-- Multiplication by a cubed block of maximal digits gives a constant digit
sum whenever the coefficient fits with room for the factor three. -/
theorem digit_sum_mul_pow_sub_one_cube {b k m : ℕ} (hb : 1 < b)
    (hm : 0 < m) (hmb : 3*m ≤ b^k) :
    (b.digits (m*(b^k-1)^3)).sum=2*((b-1)*k) := by
  have h₁ : b^k-m < b^k := by omega
  have h₂ : 3*m-1 < b^k := by omega
  have h₃ : b^k-3*m < b^k := by omega
  rw [cube_block_identity hm hmb,digit_sum_block hb h₁,
    digit_sum_block hb h₂,digit_sum_block hb h₃]
  have hc₁ := digit_sum_complement hb hm (show m ≤ b^k by omega)
  have hc₂ := digit_sum_complement hb (show 0 < 3*m by omega) hmb
  omega

theorem cube_digit_sum_fiber_not_sidon {b k : ℕ} (hb : 1 < b)
    (hk : 5184 ≤ b^k) :
    ¬ IsSidon ((fun n : ℕ => n^3) ''
      {n | (b.digits (n^3)).sum=2*((b-1)*k)}) := by
  intro hs
  let q := b^k-1
  have hq : 0 < q := by dsimp [q]; omega
  have hm (m : ℕ) (hm0 : 0 < m) (hm12 : m ≤ 12) :
      m*q ∈ {n : ℕ | (b.digits (n^3)).sum=2*((b-1)*k)} := by
    have hc : 3*m^3 ≤ b^k := by
      have hp := Nat.pow_le_pow_left hm12 3
      norm_num at hp
      omega
    simpa only [Set.mem_setOf_eq,mul_pow,q] using
      digit_sum_mul_pow_sub_one_cube hb (pow_pos hm0 3) hc
  have he : (1*q)^3+(12*q)^3=(9*q)^3+(10*q)^3 := by ring
  have hh := hs _ ⟨1*q,hm 1 (by omega) (by omega),rfl⟩
    _ ⟨9*q,hm 9 (by omega) (by omega),rfl⟩
    _ ⟨12*q,hm 12 (by omega) (by omega),rfl⟩
    _ ⟨10*q,hm 10 (by omega) (by omega),rfl⟩ he
  have h19 : (1*q)^3 < (9*q)^3 := Nat.pow_lt_pow_left (by omega) (by decide)
  have h110 : (1*q)^3 < (10*q)^3 := Nat.pow_lt_pow_left (by omega) (by decide)
  dsimp only at hh
  rcases hh with hh | hh <;> omega

/-- This applies to any function of the cube's digit sum, not merely reduction
modulo a fixed number of colors. -/
theorem no_cube_digit_sum_coloring {ι : Type*} (f : ℕ → ι) {b : ℕ} (hb : 1 < b) :
    ¬ (∀ i, IsSidon ((fun n : ℕ => n^3) ''
      {n | f (b.digits (n^3)).sum=i})) := by
  intro h
  have hk : 5184 ≤ b^13 := by
    have hh := Nat.pow_le_pow_left (show 2 ≤ b by omega) 13
    norm_num at hh
    omega
  apply cube_digit_sum_fiber_not_sidon hb hk
  apply Set.IsSidon.subset (h (f (2*((b-1)*13))))
  rintro _ ⟨n,hn,rfl⟩
  exact ⟨n,congrArg f hn,rfl⟩

#print axioms digit_sum_mul_pow_sub_one_cube
#print axioms cube_digit_sum_fiber_not_sidon
#print axioms no_cube_digit_sum_coloring
end Erdos1206.CubeDigitSumObstruction
