import Submission.PrimeMomentCollisions

/-!
An obstruction to a blanket joint root/square digit-moment criterion.
This does not settle Erdos 773 and does not assert that every moment class
is bad, or that a large Sidon subclass cannot be selected.
-/
namespace Erdos773.JointPrimeDigitMoments
open Finset Filter PrimeColorCollisions PrimeMomentCollisions
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Root moments and square moments, with sufficient lengths for both words. -/
def moments (L n j : ℕ) : ℕ × ℕ :=
  (binaryDigitMoment L n j, binaryDigitMoment (2*L) (n^2) j)

lemma square_bit_bound {L n : ℕ} (hn : n < 2^L) : n^2 < 2^(2*L) := by
  calc
    _ < (2^L)^2 := Nat.pow_lt_pow_left hn (by decide : (2 : ℕ) ≠ 0)
    _ = _ := by rw [← pow_mul, Nat.mul_comm L 2]

private lemma digit_moment_bound {L k j : ℕ} (hL : 1 ≤ L) (hj : j < k) (n : ℕ) :
    binaryDigitMoment L n j ≤ L^k := by
  calc
    _ ≤ ∑ _i ∈ range L, L^j := by
      apply sum_le_sum
      intro i hi
      dsimp
      split_ifs
      · exact Nat.pow_le_pow_left (mem_range.mp hi).le j
      · exact Nat.zero_le _
    _ = L^(j+1) := by simp [pow_succ, mul_comm]
    _ ≤ L^k := Nat.pow_le_pow_right hL (by omega)

private lemma moment_bounds {L k j : ℕ} (hL : 2 ≤ L) (hj : j < k) (n : ℕ) :
    (moments L n j).1 ≤ L^(2*k) ∧ (moments L n j).2 ≤ L^(2*k) := by
  have hsq : 2*L ≤ L^2 := by nlinarith
  have hs : (2*L)^k ≤ L^(2*k) := by
    calc
      _ ≤ (L^2)^k := Nat.pow_le_pow_left hsq k
      _ = _ := by rw [← pow_mul]
  constructor
  · exact (digit_moment_bound (by omega) hj n).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  · exact (digit_moment_bound (by omega : 1 ≤ 2*L) hj (n^2)).trans hs

private def Color (L k : ℕ) :=
  (Fin k → Fin (L^(2*k)+1)) × (Fin k → Fin (L^(2*k)+1))

private instance (L k : ℕ) : Fintype (Color L k) := inferInstanceAs
  (Fintype ((Fin k → Fin (L^(2*k)+1)) × (Fin k → Fin (L^(2*k)+1))))

private def color (L k : ℕ) (hL : 2 ≤ L) (n : ℕ) : Color L k :=
  (fun j => ⟨(moments L n j.val).1,
      Nat.lt_succ_of_le (moment_bounds hL j.isLt n).1⟩,
   fun j => ⟨(moments L n j.val).2,
      Nat.lt_succ_of_le (moment_bounds hL j.isLt n).2⟩)

private lemma color_card (L k : ℕ) (hL : 2 ≤ L) :
    Fintype.card (Color L k) ≤ L^(2*k*(2*k+1)) := by
  change (Fintype.card
    ((Fin k → Fin (L^(2*k)+1)) × (Fin k → Fin (L^(2*k)+1)))) ≤ _
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  have h1 : 1 ≤ L^(2*k) := Nat.one_le_pow _ _ (by omega)
  have hh : L^(2*k)+1 ≤ L^(2*k+1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ = (L^(2*k)+1)^(2*k) := by simp only [two_mul, pow_add]
    _ ≤ (L^(2*k+1))^(2*k) := Nat.pow_le_pow_left hh _
    _ = _ := by rw [← pow_mul, Nat.mul_comm (2*k+1) (2*k)]

/-- Four distinct primes below 2^L with equal square sums and matching joint
moments. The square moments use 2L bits, not merely the low L bits. -/
def PrimeJointMomentCollision (L k : ℕ) : Prop :=
  ∃ a b c d : ℕ,
    a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧
    5 ≤ a ∧ 5 ≤ b ∧ 5 ≤ c ∧ 5 ≤ d ∧
    a < 2^L ∧ b < 2^L ∧ c < 2^L ∧ d < 2^L ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    a^2+b^2=c^2+d^2 ∧
    (∀ j < k, moments L a j = moments L b j ∧
      moments L a j = moments L c j ∧ moments L a j = moments L d j)

private lemma of_color_collision (m k : ℕ) (hm : 1 ≤ m)
    (h : FourCollision (sievePrimes (2^m)) (color (m+1) k (by omega))) :
    PrimeJointMomentCollision (m+1) k := by
  obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hac,had,hbc,hbd,hcd,he,hfab,hfac,hfad⟩ := h
  have hprime {p : ℕ} (hp : p ∈ sievePrimes (2^m)) :
      p.Prime ∧ 5 ≤ p ∧ p < 2^(m+1) := by
    obtain ⟨hp,hpprime,h5⟩ := mem_filter.mp hp
    have hp' := mem_range.mp hp
    have hle : p ≤ 2^(m+1) := by rw [pow_succ']; omega
    have hne : p ≠ 2^(m+1) := by
      intro hh
      rw [hh] at hpprime
      have hpow := hpprime.eq_one_of_pow
      omega
    exact ⟨hpprime,h5,lt_of_le_of_ne hle hne⟩
  have ha' := hprime ha
  have hb' := hprime hb
  have hc' := hprime hc
  have hd' := hprime hd
  refine ⟨a,b,c,d,ha'.1,hb'.1,hc'.1,hd'.1,
    ha'.2.1,hb'.2.1,hc'.2.1,hd'.2.1,ha'.2.2,hb'.2.2,hc'.2.2,hd'.2.2,
    hab,hac,had,hbc,hbd,hcd,he,?_⟩
  intro j hj
  have hmom {x y : ℕ}
      (hxy : color (m+1) k (by omega) x = color (m+1) k (by omega) y) :
      moments (m+1) x j = moments (m+1) y j := by
    apply Prod.ext
    · exact congrArg (fun z : Color (m+1) k => (z.1 ⟨j,hj⟩).val) hxy
    · exact congrArg (fun z : Color (m+1) k => (z.2 ⟨j,hj⟩).val) hxy
  exact ⟨hmom hfab,hmom hfac,hmom hfad⟩

private lemma of_color_collision_length (m L k : ℕ) (hm : 1 ≤ m) (hml : m+1=L)
    (h : FourCollision (sievePrimes (2^m)) (color L k (by omega))) :
    PrimeJointMomentCollision L k := by
  subst L
  exact of_color_collision m k hm h

/-- Every fixed number of joint moments admits prime-root collisions at every
sufficiently large bit length. This is not an assertion about every fiber. -/
theorem eventually_joint_prime_collisions (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, PrimeJointMomentCollision (m+1) k := by
  filter_upwards [eventually_prime_color_collision (2*k*(2*k+1)),
    eventually_ge_atTop 1] with m hc hm
  apply of_color_collision m k hm
  exact hc _ (color_card _ _ (by omega)) _

/-- The joint root/square moments still collide at an explicit
O(k^2 log^2(k+1)) bit length. All four roots are distinct primes. -/
theorem joint_prime_collision_quadratic_log (k : ℕ) :
    PrimeJointMomentCollision (2 ^ 22 * (k+1) ^ 2 * ((k+1).log2+1) ^ 2) k := by
  let ell : ℕ := (k+1).log2+1
  let L : ℕ := 2 ^ 22 * (k+1) ^ 2 * ell ^ 2
  let m : ℕ := L - 1
  let q : ℕ := 2*k*(2*k+1)
  let κ := Color L k
  have hell : 1 ≤ ell := by dsimp [ell]; omega
  have hKsq : 1 ≤ (k+1)^2 := Nat.one_le_pow _ _ (by omega)
  have helsq : 1 ≤ ell^2 := Nat.one_le_pow _ _ hell
  have hLlarge : 896 ≤ L := by
    have hh : 2^22*1*1 ≤ L := Nat.mul_le_mul (Nat.mul_le_mul_left _ hKsq) helsq
    norm_num at hh
    omega
  have hm : 895 ≤ m := by dsimp [m]; omega
  have hml : m+1 = L := by dsimp [m]; omega
  have hmlR : (m : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hml
  let f : ℕ → κ := color L k (by omega)
  have hcard : (Fintype.card κ : ℝ) ≤ (L : ℝ) ^ q := by
    exact_mod_cast color_card L k (by omega)
  let K : ℝ := (k : ℝ) + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hKpos : 0 < K := by linarith only [hK]
  have hel : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have helpos : (0 : ℝ) < ell := by linarith only [hel]
  have hLR : (L : ℝ) = 2^22 * K^2 * (ell : ℝ)^2 := by dsimp [L,K]; push_cast; ring
  have hLpos : (0 : ℝ) < L := by rw [hLR]; positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hl2lo : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith only [hh]
  have hl2hi : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog128 : Real.log 128 ≤ 7 := by
    have hh : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    linarith only [hh,hl2hi]
  have hKpow : k+1 ≤ 2^ell :=
    ((Nat.log2_lt (by omega : k+1 ≠ 0)).mp (by dsimp [ell]; omega)).le
  have hKpowR : K ≤ (2 : ℝ)^ell := by dsimp [K]; exact_mod_cast hKpow
  have hlogK : Real.log K ≤ ell := by
    have hh := Real.log_le_log hKpos hKpowR
    rw [Real.log_pow] at hh
    have ht := mul_le_mul_of_nonneg_left hl2hi helpos.le
    linarith only [hh,ht]
  have hlogell : Real.log (ell : ℝ) ≤ ell := by
    have hh := Real.log_le_sub_one_of_pos helpos
    linarith only [hh]
  have hlogL : Real.log (L : ℝ) ≤ 26 * ell := by
    have he : Real.log (L : ℝ) = 22 * Real.log 2 + 2 * Real.log K + 2 * Real.log (ell : ℝ) := by
      rw [hLR, Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by positivity)]
      simp only [Real.log_pow, Nat.cast_ofNat]
    linarith only [he,hl2hi,hlogK,hlogell,hel]
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  let x : ℝ := L * Real.log 2
  have hx : 1 < x := by
    have hL896 : (896 : ℝ) ≤ L := by exact_mod_cast hLlarge
    dsimp [x]
    nlinarith only [hL896,hl2lo]
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogxle : Real.log x ≤ 26 * ell := by
    apply le_trans _ hlogL
    apply Real.log_le_log (by linarith only [hx] : 0 < x)
    dsimp [x]
    nlinarith only [hl2hi,hLpos]
  have hq : ((q+1 : ℕ) : ℝ) ≤ 4*K^2 := by
    dsimp [q,K]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  have hKE : 1 ≤ K^2 * (ell : ℝ) := by
    have hh : 1 ≤ K^2 := one_le_pow₀ hK
    nlinarith only [hh,hel]
  have hnum : Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) ≤
      111 * K^2 * ell := by
    have hh := mul_le_mul hq hlogL hlogL0 (by positivity : (0 : ℝ) ≤ 4*K^2)
    nlinarith only [hh,hlog128,hKE]
  have hden : 512 * Real.log x ≤ 13312 * ell := by linarith only [hlogxle]
  have hprod : (Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ)) *
      (512 * Real.log x) < x := by
    calc
      _ ≤ (111 * K^2 * ell) * (13312 * ell) :=
        mul_le_mul hnum hden (by positivity) (by positivity)
      _ < (L : ℝ) / 2 := by
        rw [hLR]
        nlinarith only [mul_pos (sq_pos_of_pos hKpos) (sq_pos_of_pos helpos)]
      _ ≤ x := by
        dsimp [x]
        nlinarith only [hl2lo,hLpos]
  have hgap : Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) <
      x / (512 * Real.log x) := (lt_div_iff₀ (by positivity)).mpr hprod
  have hcost : 128 * (Fintype.card κ : ℝ) * L *
      Real.exp (-x / (512 * Real.log x)) < 1 := by
    calc
      _ ≤ 128 * (L : ℝ)^q * L * Real.exp (-x / (512 * Real.log x)) := by gcongr
      _ = Real.exp (Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) -
          x / (512 * Real.log x)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 128), Real.exp_nat_mul,
          Real.exp_log hLpos, pow_succ]
        rw [neg_div]
        ring
      _ < 1 := by rw [Real.exp_lt_one_iff]; linarith only [hgap]
  have hcol := prime_color_collision_of_entropy m hm κ f (by rw [hmlR]; exact hcost)
  exact of_color_collision_length m L k (by omega) hml hcol


/-- The prime-root class specified by all the joint moments of a reference root.
No Sidonness or density property is built into this definition. -/
def primeJointClass (L k a : ℕ) : Set ℕ :=
  {n | n.Prime ∧ 5 ≤ n ∧ n < 2^L ∧
    ∀ j < k, moments L n j = moments L a j}

/-- A joint-moment collision really gives a non-Sidon square-value class.
This does not say that every class is non-Sidon. -/
theorem collision_class_not_sidon {L k : ℕ} (h : PrimeJointMomentCollision L k) :
    ∃ a : ℕ, ¬ IsSidon ((fun n : ℕ => n^2) '' primeJointClass L k a) := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd,ha5,hb5,hc5,hd5,haL,hbL,hcL,hdL,
    hab,hac,had,hbc,hbd,hcd,he,hmom⟩ := h
  have haS : a^2 ∈ (fun n : ℕ => n^2) '' primeJointClass L k a :=
    ⟨a,⟨ha,ha5,haL,fun _ _ => rfl⟩,rfl⟩
  have hbS : b^2 ∈ (fun n : ℕ => n^2) '' primeJointClass L k a :=
    ⟨b,⟨hb,hb5,hbL,fun j hj => (hmom j hj).1.symm⟩,rfl⟩
  have hcS : c^2 ∈ (fun n : ℕ => n^2) '' primeJointClass L k a :=
    ⟨c,⟨hc,hc5,hcL,fun j hj => (hmom j hj).2.1.symm⟩,rfl⟩
  have hdS : d^2 ∈ (fun n : ℕ => n^2) '' primeJointClass L k a :=
    ⟨d,⟨hd,hd5,hdL,fun j hj => (hmom j hj).2.2.symm⟩,rfl⟩
  refine ⟨a,fun hs => ?_⟩
  rcases hs _ haS _ hcS _ hbS _ hdS he with hh | hh
  · exact hac (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh.1)
  · exact had (Nat.pow_left_injective (by decide : (2 : ℕ) ≠ 0) hh.1)

/-- Explicit obstruction to the blanket rule that fixing these joint moments,
even among prime roots, makes the entire square-value class Sidon. -/
theorem joint_prime_class_obstruction (k : ℕ) :
    ∃ a : ℕ, ¬ IsSidon ((fun n : ℕ => n^2) ''
      primeJointClass (2^22 * (k+1)^2 * ((k+1).log2+1)^2) k a) :=
  collision_class_not_sidon (joint_prime_collision_quadratic_log k)

/-- For fixed k, bad prime-root classes persist at every sufficiently large
length; a finite small-base accident is not being used as an asymptotic claim. -/
theorem eventually_joint_class_obstruction (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∃ a : ℕ,
      ¬ IsSidon ((fun n : ℕ => n^2) '' primeJointClass (m+1) k a) := by
  filter_upwards [eventually_joint_prime_collisions k] with m hm
  exact collision_class_not_sidon hm


#print axioms collision_class_not_sidon
#print axioms joint_prime_class_obstruction
#print axioms eventually_joint_class_obstruction
#print axioms square_bit_bound
#print axioms eventually_joint_prime_collisions
#print axioms joint_prime_collision_quadratic_log
end Erdos773.JointPrimeDigitMoments
