import FormalConjecturesUtil

/-!
Cubic Sidonness on finite arithmetic progressions, and explicit collisions in
infinite residue classes. These results do not settle the density conjecture.
-/

namespace Erdos1206.CubeArithmeticProgressions
open scoped Classical

private lemma unordered_eq_of_sum_and_cube_sum {a b c d : ℕ}
    (hs : a+b=c+d) (he : a^3+b^3=c^3+d^3) :
    (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  by_cases hz : a+b=0
  · left; omega
  have hp : a*b=c*d := by
    have hi : 3*(a+b)*(a*b)+(a^3+b^3)=(a+b)^3 := by ring
    have hj : 3*(c+d)*(c*d)+(c^3+d^3)=(c+d)^3 := by ring
    rw [hs,he] at hi
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3*(c+d))
      (Nat.add_right_cancel (hi.trans hj.symm))
  have hsZ : (a : ℤ)+b=c+d := by exact_mod_cast hs
  have hpZ : (a : ℤ)*b=c*d := by exact_mod_cast hp
  have hf : ((a : ℤ)-c)*((a : ℤ)-d)=0 := by nlinarith
  rcases mul_eq_zero.mp hf with hh | hh
  · left; constructor <;> omega
  · right; constructor <;> omega

/-- Large reduced step alone makes a finite progression's cubes Sidon.
In particular there is no length-only criterion forcing a cubic collision in
an arbitrary arithmetic progression. -/
theorem cubes_sidon_of_large_coprime_step (u step L : ℕ)
    (hcop : Nat.Coprime step u) (hstep : 6*L < step) :
    IsSidon ((fun i : ℕ => (u+step*i)^3) '' Set.Icc 0 L) := by
  rintro _ ⟨i,hi,rfl⟩ _ ⟨k,hk,rfl⟩ _ ⟨j,hj,rfl⟩ _ ⟨l,hl,rfl⟩ he
  have hstep0 : 0 < step := by omega
  let F : ℕ → ℕ := fun x => 3*u^2*x+step*(3*u*x^2+step*x^3)
  have hF (x : ℕ) : (u+step*x)^3=u^3+step*F x := by dsimp [F]; ring
  simp only [hF] at he
  have hsumF : F i+F j=F k+F l := by nlinarith
  have hmod : u^2*(3*(i+j)) ≡ u^2*(3*(k+l)) [MOD step] := by
    have hfmod (x : ℕ) : F x ≡ 3*u^2*x [MOD step] := by
      dsimp [F]
      simp [Nat.ModEq, Nat.add_mod, Nat.mul_mod]
    have hh := (hfmod i).add (hfmod j)
    have hh' := (hfmod k).add (hfmod l)
    rw [hsumF] at hh
    convert hh.symm.trans hh' using 1 <;> ring
  have hcancel : 3*(i+j) ≡ 3*(k+l) [MOD step] :=
    Nat.ModEq.cancel_left_of_coprime (hcop.pow_right 2) hmod
  have hiL := hi.2
  have hjL := hj.2
  have hkL := hk.2
  have hlL := hl.2
  have hlt1 : 3*(i+j)<step := by omega
  have hlt2 : 3*(k+l)<step := by omega
  have hsum : i+j=k+l := by
    change (3*(i+j)) % step=(3*(k+l)) % step at hcancel
    rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hcancel
    omega
  have hsroots : (u+step*i)+(u+step*j)=(u+step*k)+(u+step*l) := by
    nlinarith
  have he' : (u+step*i)^3+(u+step*j)^3=(u+step*k)^3+(u+step*l)^3 := by
    simpa only [hF] using he
  rcases unordered_eq_of_sum_and_cube_sum hsroots he' with hh | hh
  · exact Or.inl ⟨congrArg (fun n : ℕ => n^3) hh.1,
      congrArg (fun n : ℕ => n^3) hh.2⟩
  · exact Or.inr ⟨congrArg (fun n : ℕ => n^3) hh.1,
      congrArg (fun n : ℕ => n^3) hh.2⟩

/-- Four homogeneous cubic forms; all are congruent to `z^3` modulo `q`. -/
def A (q z : ℕ) := z^3+7*q*z^2+15*q^2*z+6*q^3
def B (q z : ℕ) := z^3+8*q*z^2+24*q^2*z+27*q^3
def C (q z : ℕ) := z^3+10*q*z^2+36*q^2*z+45*q^3
def D (q z : ℕ) := z^3+11*q*z^2+39*q^2*z+48*q^3

lemma identity (q z : ℕ) : (A q z)^3+(D q z)^3=(B q z)^3+(C q z)^3 := by
  dsimp [A,B,C,D]
  ring

lemma ordered {q z : ℕ} (hq : 0<q) :
    0<A q z ∧ A q z<B q z ∧ B q z<C q z ∧ C q z<D q z := by
  have hq3 : 0<q^3 := pow_pos hq _
  dsimp [A,B,C,D]
  constructor
  · positivity
  constructor
  · nlinarith
  constructor <;> nlinarith

lemma congruences (q z : ℕ) :
    A q z ≡ z^3 [MOD q] ∧ B q z ≡ z^3 [MOD q] ∧
    C q z ≡ z^3 [MOD q] ∧ D q z ≡ z^3 [MOD q] := by
  simp [A,B,C,D,Nat.ModEq,Nat.add_mod,Nat.mul_mod,Nat.pow_mod]


lemma band_bound {q z K : ℕ} (hqz : q≤z) (hlarge : 70*K*q≤z) :
    K*D q z ≤ (K+1)*A q z := by
  have h1 : q^2*z ≤ q*z^2 := by
    have hh := Nat.mul_le_mul_left (q*z) hqz
    nlinarith only [hh]
  have h2 : q^3 ≤ q*z^2 := by
    have hh := Nat.mul_le_mul_left q (Nat.pow_le_pow_left hqz 2)
    nlinarith only [hh]
  have hg : D q z ≤ A q z+70*q*z^2 := by
    dsimp [A,D]
    nlinarith only [h1,h2]
  have hh := Nat.mul_le_mul_left K hg
  have hj := Nat.mul_le_mul_right (z^2) hlarge
  have hz : z^3 ≤ A q z := by dsimp [A]; omega
  nlinarith only [hh,hj,hz]

/-- An explicit strict cubic collision exists arbitrarily far out in every
residue class. Its four roots can be confined to an arbitrarily narrow
multiplicative band. -/
theorem narrow_collision_in_residue_class (q r K M : ℕ) (hq : 0<q) :
    ∃ a b c d : ℕ, M<a ∧ a<b ∧ b<c ∧ c<d ∧
      a^3+d^3=b^3+c^3 ∧ K*d≤(K+1)*a ∧
      a ≡ r [MOD q] ∧ b ≡ r [MOD q] ∧
      c ≡ r [MOD q] ∧ d ≡ r [MOD q] := by
  let z := q*(70*K+M+1)+1
  let s := q+r
  have hs : 0<s := by dsimp [s]; omega
  have hqz : q≤z := by dsimp [z]; nlinarith
  have hlarge : 70*K*q≤z := by dsimp [z]; nlinarith
  have hzM : M<z := by dsimp [z]; nlinarith
  have hz0 : 1≤z := by dsimp [z]; omega
  have hzA : z≤A q z := (le_self_pow hz0 (by decide : 3≠0)).trans (by
    dsimp [A]; omega)
  have hAs : A q z≤s*A q z := Nat.le_mul_of_pos_left _ hs
  obtain ⟨ha,hab,hbc,hcd⟩ := ordered (z := z) hq
  have hcong := congruences q z
  have hzc : z ≡ 1 [MOD q] := by dsimp [z]; simp [Nat.ModEq]
  have hsc : s ≡ r [MOD q] := by dsimp [s]; simp [Nat.ModEq]
  have hz3 : z^3 ≡ 1 [MOD q] := by simpa using hzc.pow 3
  refine ⟨s*A q z,s*B q z,s*C q z,s*D q z,
    hzM.trans_le (hzA.trans hAs),Nat.mul_lt_mul_of_pos_left hab hs,
    Nat.mul_lt_mul_of_pos_left hbc hs,Nat.mul_lt_mul_of_pos_left hcd hs,?_,?_,
    ?_,?_,?_,?_⟩
  · simpa only [mul_pow,← mul_add] using
      congrArg (fun n : ℕ => s^3*n) (identity q z)
  · have hh := Nat.mul_le_mul_left s (band_bound hqz hlarge)
    nlinarith only [hh]
  · simpa using hsc.mul (hcong.1.trans hz3)
  · simpa using hsc.mul (hcong.2.1.trans hz3)
  · simpa using hsc.mul (hcong.2.2.1.trans hz3)
  · simpa using hsc.mul (hcong.2.2.2.trans hz3)

/-- No cube-Sidon root set can contain a tail of an infinite residue class. -/
theorem no_residue_class_tail {S : Set ℕ}
    (hS : IsSidon ((fun n : ℕ => n^3) '' S))
    (q r M : ℕ) (hq : 0<q) :
    ¬ ∀ n : ℕ, M<n → n ≡ r [MOD q] → n∈S := by
  intro h
  obtain ⟨a,b,c,d,ha,hab,hbc,hcd,he,_,hc1,hc2,hc3,hc4⟩ :=
    narrow_collision_in_residue_class q r 0 M hq
  have hh := hS _ ⟨a,h a ha hc1,rfl⟩ _ ⟨b,h b (by omega) hc2,rfl⟩
    _ ⟨d,h d (by omega) hc4,rfl⟩ _ ⟨c,h c (by omega) hc3,rfl⟩ he
  rcases hh with hh | hh
  · have heq : a=b := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega
  · have heq : a=c := Nat.pow_left_injective (by decide : 3≠0) hh.1
    omega

#print axioms narrow_collision_in_residue_class
#print axioms no_residue_class_tail

#print axioms cubes_sidon_of_large_coprime_step
#print axioms identity

end Erdos1206.CubeArithmeticProgressions
