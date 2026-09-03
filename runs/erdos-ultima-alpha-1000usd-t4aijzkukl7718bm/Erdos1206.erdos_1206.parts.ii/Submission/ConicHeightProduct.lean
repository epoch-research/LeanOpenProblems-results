import FormalConjecturesUtil

/-!
A uniform product-height bound for the three rational conic parameters of a
strict positive cubic collision. This is an arithmetic bound, not a proof of
the positive-density cube-Sidon conjecture.
-/
namespace Erdos1206.ConicHeightProduct

/-- The difference between the two sums of roots. -/
def defect (a b c d : ℕ) : ℕ := b+c-(a+d)

/-- Heights of the three reduced ratios. In an ordered collision the displayed
numerator in each ratio is the larger of its two coordinates. -/
def heights (a b c d : ℕ) : Fin 3 → ℕ :=
  ![(b+c) / Nat.gcd (a+d) (b+c),
    (b-a) / Nat.gcd (b-a) (d-c),
    (c-a) / Nat.gcd (c-a) (d-b)]

lemma root_sum_lt {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) : a+d < b+c := by
  have ha : (0:ℤ) ≤ a := Int.natCast_nonneg a
  have hb : (0:ℤ) < b := by omega
  have hc : (0:ℤ) < c := by omega
  have hd : (0:ℤ) < d := by omega
  have habZ : (a:ℤ)<b := by exact_mod_cast hab
  have hbcZ : (b:ℤ)<c := by exact_mod_cast hbc
  have hcdZ : (c:ℤ)<d := by exact_mod_cast hcd
  have heZ : (a:ℤ)^3+d^3=b^3+c^3 := by exact_mod_cast he
  have hfac : ((b:ℤ)-a)*((a:ℤ)^2+a*b+b^2) =
      ((d:ℤ)-c)*((c:ℤ)^2+c*d+d^2) := by
    linear_combination -heZ
  have hQ : (a:ℤ)^2+a*b+b^2 < (c:ℤ)^2+c*d+d^2 := by
    have h₁ : (a:ℤ)^2 < (c:ℤ)^2 := (sq_lt_sq₀ ha hc.le).mpr (habZ.trans hbcZ)
    have h₂ : (b:ℤ)^2 < (d:ℤ)^2 := (sq_lt_sq₀ hb.le hd.le).mpr (hbcZ.trans hcdZ)
    have h₃ : (a:ℤ)*b ≤ (c:ℤ)*d := mul_le_mul (habZ.trans hbcZ).le
      (hbcZ.trans hcdZ).le hb.le hc.le
    linarith
  by_contra hn
  have hg : (b:ℤ)-a ≤ (d:ℤ)-c := by omega
  have hmul := mul_lt_mul_of_pos_left hQ (sub_pos.mpr habZ)
  have hmul' := mul_le_mul_of_nonneg_right hg
    (show (0:ℤ) ≤ (c:ℤ)^2+c*d+d^2 by positivity)
  linarith

lemma defect_pos {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) : 0 < defect a b c d := by
  exact Nat.sub_pos_of_lt (root_sum_lt hab hbc hcd he)

lemma defect_lt {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d) :
    defect a b c d < d := by
  dsimp [defect]
  omega

lemma three_dvd_defect {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) : 3 ∣ defect a b c d := by
  have hsum := (root_sum_lt hab hbc hcd he).le
  have he3 := congrArg (fun n : ℕ => (n : ZMod 3)) he
  simp only [Nat.cast_add,Nat.cast_pow,ZMod.pow_card] at he3
  apply (ZMod.natCast_eq_zero_iff _ 3).mp
  simp only [defect,Nat.cast_sub hsum,Nat.cast_add]
  exact sub_eq_zero.mpr he3.symm

/-- A factorization exposing the product of the three unreduced conic heights. -/
lemma product_identity {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) :
    3*((b-a)*(c-a)*(b+c)) =
      defect a b c d * (3*d^2+3*d*defect a b c d+(defect a b c d)^2) := by
  have hsum := (root_sum_lt hab hbc hcd he).le
  have heZ : (a:ℤ)^3+d^3=b^3+c^3 := by exact_mod_cast he
  apply Int.ofNat.inj
  change ((3*((b-a)*(c-a)*(b+c)) : ℕ) : ℤ) =
    ((defect a b c d * (3*d^2+3*d*defect a b c d+(defect a b c d)^2) : ℕ) : ℤ)
  simp only [Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat,
    Nat.cast_sub hab.le,Nat.cast_sub (hab.trans hbc).le]
  have hk : ((defect a b c d : ℕ):ℤ) = (b:ℤ)+c-a-d := by
    simp only [defect,Nat.cast_sub hsum,Nat.cast_add]
    ring
  rw [hk]
  linear_combination heZ

/-- The factor three in the preceding identity cancels integrally, since
all cubic collisions have root-sum defect divisible by three. -/
lemma defect_dvd_product {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) : defect a b c d ∣ (b-a)*(c-a)*(b+c) := by
  obtain ⟨j,hj⟩ := three_dvd_defect hab hbc hcd he
  have hh := product_identity hab hbc hcd he
  rw [hj] at hh ⊢
  refine ⟨d^2+3*d*j+3*j^2, ?_⟩
  nlinarith only [hh]

lemma dvd_gcd_product {k x y z : ℕ} (h : k ∣ x*y*z) :
    k ∣ Nat.gcd k x * Nat.gcd k y * Nat.gcd k z := by
  have h₁ : k ∣ Nat.gcd k (x*y) * Nat.gcd k z :=
    Nat.dvd_gcd_mul_gcd_iff_dvd_mul.mpr h
  exact h₁.trans (Nat.mul_dvd_mul_right
    (gcd_mul_dvd_mul_gcd k x y) (Nat.gcd k z))

#print axioms root_sum_lt
#print axioms product_identity
#print axioms defect_dvd_product

/-- The three gcds by which the conic parameters are reduced. -/
def denominatorProduct (a b c d : ℕ) : ℕ :=
  Nat.gcd (a+d) (b+c) * Nat.gcd (b-a) (d-c) * Nat.gcd (c-a) (d-b)

lemma gcd_defect {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d)
    (he : a^3+d^3=b^3+c^3) :
    Nat.gcd (defect a b c d) (b+c) = Nat.gcd (a+d) (b+c) ∧
    Nat.gcd (defect a b c d) (b-a) = Nat.gcd (b-a) (d-c) ∧
    Nat.gcd (defect a b c d) (c-a) = Nat.gcd (c-a) (d-b) := by
  have hsum := root_sum_lt hab hbc hcd he
  have h₁ : defect a b c d = (b-a)-(d-c) := by dsimp [defect]; omega
  have h₂ : defect a b c d = (c-a)-(d-b) := by dsimp [defect]; omega
  refine ⟨?_,?_,?_⟩
  · exact Nat.gcd_self_sub_left hsum.le
  · rw [h₁,Nat.gcd_self_sub_left (by omega : d-c ≤ b-a),Nat.gcd_comm]
  · rw [h₂,Nat.gcd_self_sub_left (by omega : d-b ≤ c-a),Nat.gcd_comm]

lemma denominatorProduct_pos {a b c d : ℕ} (hab : a<b) (hbc : b<c) (hcd : c<d) :
    0 < denominatorProduct a b c d := by
  have h₀ : 0 < Nat.gcd (a+d) (b+c) := Nat.gcd_pos_of_pos_left _ (by omega)
  have h₁ : 0 < Nat.gcd (b-a) (d-c) := Nat.gcd_pos_of_pos_left _ (by omega)
  have h₂ : 0 < Nat.gcd (c-a) (d-b) := Nat.gcd_pos_of_pos_left _ (by omega)
  exact Nat.mul_pos (Nat.mul_pos h₀ h₁) h₂

/-- No primitivity hypothesis is needed for this lower bound on the combined
cancellation in the three conic parameters. -/
theorem defect_dvd_denominatorProduct {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    defect a b c d ∣ denominatorProduct a b c d := by
  have h := defect_dvd_product hab hbc hcd he
  have h' : defect a b c d ∣ (b+c)*(b-a)*(c-a) := by
    simpa only [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using h
  have hh := dvd_gcd_product h'
  obtain ⟨h₀,h₁,h₂⟩ := gcd_defect hab hbc hcd he
  simpa only [h₀,h₁,h₂,denominatorProduct] using hh

lemma heights_mul_denominator (a b c d : ℕ) :
    (heights a b c d 0 * heights a b c d 1 * heights a b c d 2) *
      denominatorProduct a b c d = (b+c)*(b-a)*(c-a) := by
  change ((b+c)/Nat.gcd (a+d) (b+c) * ((b-a)/Nat.gcd (b-a) (d-c)) *
    ((c-a)/Nat.gcd (c-a) (d-b))) *
      (Nat.gcd (a+d) (b+c)*Nat.gcd (b-a) (d-c)*Nat.gcd (c-a) (d-b)) = _
  calc
    _ = (((b+c)/Nat.gcd (a+d) (b+c))*Nat.gcd (a+d) (b+c)) *
      (((b-a)/Nat.gcd (b-a) (d-c))*Nat.gcd (b-a) (d-c)) *
      (((c-a)/Nat.gcd (c-a) (d-b))*Nat.gcd (c-a) (d-b)) := by ring
    _ = _ := by rw [Nat.div_mul_cancel (Nat.gcd_dvd_right (a+d) (b+c)),
      Nat.div_mul_cancel (Nat.gcd_dvd_left (b-a) (d-c)),
      Nat.div_mul_cancel (Nat.gcd_dvd_left (c-a) (d-b))]

/-- The product of all three reduced conic heights is at most `7*d²/3`.
In particular this is uniform in the original parametrization and its gcd. -/
theorem heights_product_bound {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    3*(heights a b c d 0 * heights a b c d 1 * heights a b c d 2) ≤ 7*d^2 := by
  let k := defect a b c d
  let G := denominatorProduct a b c d
  let H := heights a b c d 0 * heights a b c d 1 * heights a b c d 2
  have hk : 0 < k := defect_pos hab hbc hcd he
  have hkd : k ≤ d := (defect_lt hab hbc hcd).le
  have hG : 0 < G := denominatorProduct_pos hab hbc hcd
  have hkG : k ≤ G := Nat.le_of_dvd hG (defect_dvd_denominatorProduct hab hbc hcd he)
  have hQ : 3*d^2+3*d*k+k^2 ≤ 7*d^2 := by
    have h₁ := Nat.mul_le_mul_left d hkd
    have h₂ := Nat.pow_le_pow_left hkd 2
    nlinarith
  have hprod : H*G = (b-a)*(c-a)*(b+c) := by
    simpa only [H,G,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using
      heights_mul_denominator a b c d
  have hid : 3*H*G = k*(3*d^2+3*d*k+k^2) := by
    rw [Nat.mul_assoc,hprod]
    exact product_identity hab hbc hcd he
  change 3*H ≤ 7*d^2
  apply Nat.le_of_mul_le_mul_left (c := k) (hc := hk)
  calc
    k*(3*H) = 3*H*k := by ring
    _ ≤ 3*H*G := Nat.mul_le_mul_left _ hkG
    _ = k*(3*d^2+3*d*k+k^2) := hid
    _ ≤ k*(7*d^2) := Nat.mul_le_mul_left k hQ

/-- At least one of the three rational conic parameters has height of order
`d^(2/3)`. This is stated without real powers. -/
theorem exists_small_height {a b c d : ℕ}
    (hab : a<b) (hbc : b<c) (hcd : c<d) (he : a^3+d^3=b^3+c^3) :
    ∃ i : Fin 3, 3*(heights a b c d i)^3 ≤ 7*d^2 := by
  obtain ⟨i,_,hi⟩ := Finset.exists_min_image Finset.univ
    (heights a b c d) Finset.univ_nonempty
  have h₀ := hi 0 (Finset.mem_univ _)
  have h₁ := hi 1 (Finset.mem_univ _)
  have h₂ := hi 2 (Finset.mem_univ _)
  have hp := Nat.mul_le_mul (Nat.mul_le_mul h₀ h₁) h₂
  have hp' : (heights a b c d i)^3 ≤
      heights a b c d 0 * heights a b c d 1 * heights a b c d 2 := by
    simpa only [pow_succ,pow_zero,mul_one,one_mul] using hp
  exact ⟨i,(Nat.mul_le_mul_left 3 hp').trans (heights_product_bound hab hbc hcd he)⟩

#print axioms defect_dvd_denominatorProduct
#print axioms heights_product_bound
#print axioms exists_small_height


#print axioms dvd_gcd_product
end Erdos1206.ConicHeightProduct
