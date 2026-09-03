import Submission.LosingProductSidon

/-! Actual collisions outside the short-cofactor range. Only the displayed
sum is assumed prime; no infinite prime-values assertion is used. -/
namespace Erdos371

lemma shifted_product_collision_factorizations (a b c d p : ℕ)
    (hs : p = a+b+c+d) (hd : c*d = a*b+1) :
    a*p+1 = (a+c)*(a+d) ∧ b*p+1 = (b+c)*(b+d) ∧
    c*p = (a+c)*(b+c)+1 ∧ d*p = (a+d)*(b+d)+1 := by
  subst p
  constructor
  · nlinarith [hd]
  constructor
  · nlinarith [hd]
  constructor <;> nlinarith [hd]

private lemma product_maxPrimeFac_lt (u v p : ℕ) (hu : 0<u) (hv : 0<v)
    (hup : u<p) (hvp : v<p) : Nat.maxPrimeFac (u*v)<p := by
  rw [Nat.maxPrimeFac_mul hu.ne' hv.ne']
  exact max_lt (Nat.maxPrimeFac_le.trans_lt hup) (Nat.maxPrimeFac_le.trans_lt hvp)

private lemma cofactor_maxPrimeFac (k p : ℕ) (hk : 0<k) (hkp : k<p)
    (hp : p.Prime) : Nat.maxPrimeFac (k*p)=p := by
  rw [Nat.maxPrimeFac_mul hk.ne' hp.ne_zero,hp.maxPrimeFac_eq_self]
  exact max_eq_right (Nat.maxPrimeFac_le.trans hkp.le)

/-- The four affine losing integers are all genuinely p-smooth, because the
factorizations split each into two positive factors below p. -/
theorem shifted_product_collision_data (a b c d p : ℕ)
    (ha : 0<a) (hb : 0<b) (hc : 0<c) (hd : 0<d)
    (hs : p = a+b+c+d) (hdet : c*d = a*b+1) (hp : p.Prime) :
    primeWinner (a*p)=p ∧ primeWinner (b*p)=p ∧
    primeWinner (c*p-1)=p ∧ primeWinner (d*p-1)=p ∧
    losingNumber (a*p)*losingNumber (b*p) =
      losingNumber (c*p-1)*losingNumber (d*p-1) ∧
    losingProductIndex (a*p) (b*p) = losingProductIndex (c*p-1) (d*p-1) := by
  obtain ⟨hf₁,hf₂,hf₃,hf₄⟩ := shifted_product_collision_factorizations a b c d p hs hdet
  have hcp : 0<c*p := mul_pos hc hp.pos
  have hdp : 0<d*p := mul_pos hd hp.pos
  have hce : c*p-1+1=c*p := Nat.sub_add_cancel hcp
  have hde : d*p-1+1=d*p := Nat.sub_add_cancel hdp
  have hf₃' : c*p-1=(a+c)*(b+c) := by omega
  have hf₄' : d*p-1=(a+d)*(b+d) := by omega
  have hA : Nat.maxPrimeFac (a*p+1)<p := by
    rw [hf₁]
    exact product_maxPrimeFac_lt _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hB : Nat.maxPrimeFac (b*p+1)<p := by
    rw [hf₂]
    exact product_maxPrimeFac_lt _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hC : Nat.maxPrimeFac (c*p-1)<p := by
    rw [hf₃']
    exact product_maxPrimeFac_lt _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hD : Nat.maxPrimeFac (d*p-1)<p := by
    rw [hf₄']
    exact product_maxPrimeFac_lt _ _ _ (by omega) (by omega) (by omega) (by omega)
  have hwA := cofactor_maxPrimeFac a p ha (by omega) hp
  have hwB := cofactor_maxPrimeFac b p hb (by omega) hp
  have hwC := cofactor_maxPrimeFac c p hc (by omega) hp
  have hwD := cofactor_maxPrimeFac d p hd (by omega) hp
  have hnA : ¬Nat.maxPrimeFac (a*p)<Nat.maxPrimeFac (a*p+1) := by omega
  have hnB : ¬Nat.maxPrimeFac (b*p)<Nat.maxPrimeFac (b*p+1) := by omega
  have hrC : Nat.maxPrimeFac (c*p-1)<Nat.maxPrimeFac (c*p-1+1) := by
    simpa only [hce,hwC] using hC
  have hrD : Nat.maxPrimeFac (d*p-1)<Nat.maxPrimeFac (d*p-1+1) := by
    simpa only [hde,hwD] using hD
  have hprod : (a*p+1)*(b*p+1)=(c*p-1)*(d*p-1) := by
    rw [hf₁,hf₂,hf₃',hf₄']
    ring
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · simp only [primeWinner,hwA,max_eq_left hA.le]
  · simp only [primeWinner,hwB,max_eq_left hB.le]
  · simp only [primeWinner,hce,hwC,max_eq_right hC.le]
  · simp only [primeWinner,hde,hwD,max_eq_right hD.le]
  · simpa only [losingNumber,if_neg hnA,if_neg hnB,if_pos hrC,if_pos hrD] using hprod
  · simp only [losingProductIndex,hnA,hnB,hrC,hrD,iff_self,if_true,
      losingNumber,if_false,hprod]

/-- A small explicit nontrivial collision. In particular, merely requiring
2N<p^2 would not justify the short-cofactor fibre bound. -/
lemma losing_product_collision_eleven :
    primeWinner 11=11 ∧ primeWinner 55=11 ∧
    primeWinner 21=11 ∧ primeWinner 32=11 ∧
    losingProductIndex 11 55=671 ∧ losingProductIndex 21 32=671 ∧
    2*56<(11 : ℕ)^2 := by
  decide +kernel

/-- The constant in 4N<p^2 cannot simply be replaced by 3.98.
This is a finite obstruction to that auxiliary claim, not to Erdős 371. -/
theorem losing_product_collision_near_four :
    ∃ p N n m a b : ℕ, p.Prime ∧ 398*N < 100*p^2 ∧
      1 < n ∧ n < N ∧ 1 < m ∧ m < N ∧ 1 < a ∧ a < N ∧ 1 < b ∧ b < N ∧
      primeWinner n=p ∧ primeWinner m=p ∧ primeWinner a=p ∧ primeWinner b=p ∧
      losingProductIndex n m=losingProductIndex a b ∧ n ≠ m ∧ a ≠ b ∧ n ≠ a ∧ n ≠ b := by
  let p : ℕ := 4063447
  let A : ℕ := 1010807
  let B : ℕ := 1020917
  let C : ℕ := 1010908
  let D : ℕ := 1020815
  have hp : p.Prime := by norm_num [p]
  have hh := shifted_product_collision_data A B C D p
    (by norm_num [A]) (by norm_num [B]) (by norm_num [C]) (by norm_num [D])
    (by norm_num [p,A,B,C,D]) (by norm_num [A,B,C,D]) hp
  refine ⟨p,B*p+1,A*p,B*p,C*p-1,D*p-1,hp,?_,?_,?_,?_,?_,?_,?_,?_,?_,
    hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,hh.2.2.2.2.2,?_,?_,?_,?_⟩ <;>
    norm_num [p,A,B,C,D]

#print axioms shifted_product_collision_factorizations
#print axioms shifted_product_collision_data
#print axioms losing_product_collision_eleven
#print axioms losing_product_collision_near_four
end Erdos371
