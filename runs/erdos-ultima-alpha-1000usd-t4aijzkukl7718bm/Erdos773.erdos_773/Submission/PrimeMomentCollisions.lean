import Submission.PrimeColorCollisions

/-!
Prime roots with any prescribed finite number of matching binary digit moments
still admit nontrivial equal square sums. This is an obstruction to a blanket
selection criterion, not a disproof of Erdos 773.
-/
namespace Erdos773.PrimeMomentCollisions
open Finset Filter PrimeColorCollisions
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- The j-th positional moment of the first L binary digits. -/
def binaryDigitMoment (L n j : ℕ) : ℕ :=
  ∑ i ∈ range L, if n.testBit i then i ^ j else 0

private lemma moment_bound {L k j : ℕ} (hL : 1 ≤ L) (hj : j < k) (n : ℕ) :
    binaryDigitMoment L n j ≤ L ^ k := by
  calc
    _ ≤ ∑ _i ∈ range L, L ^ j := by
      apply sum_le_sum
      intro i hi
      dsimp
      split_ifs
      · exact Nat.pow_le_pow_left (mem_range.mp hi).le j
      · exact Nat.zero_le _
    _ = L ^ (j+1) := by simp [pow_succ, mul_comm]
    _ ≤ L ^ k := Nat.pow_le_pow_right hL (by omega)

private def momentColor (L k : ℕ) (hL : 1 ≤ L) (n : ℕ) : Fin k → Fin (L ^ k + 1) :=
  fun j => ⟨binaryDigitMoment L n j.val, Nat.lt_succ_of_le (moment_bound hL j.isLt n)⟩

private lemma color_card (L k : ℕ) (hL : 2 ≤ L) :
    Fintype.card (Fin k → Fin (L ^ k + 1)) ≤ L ^ (k * (k+1)) := by
  simp only [Fintype.card_fun, Fintype.card_fin]
  have hp : 1 ≤ L ^ k := Nat.one_le_pow _ _ (by omega)
  have hh : L ^ k + 1 ≤ L ^ (k+1) := by
    rw [pow_succ]
    nlinarith
  calc
    _ ≤ (L ^ (k+1)) ^ k := Nat.pow_le_pow_left hh k
    _ = _ := by rw [← pow_mul, Nat.mul_comm (k+1) k]

/-- Distinct prime roots with matching binary moments. All listed bits account
for the whole root, because each root is strictly below 2^L. -/
def PrimeMomentCollision (L k : ℕ) : Prop :=
  ∃ a b c d : ℕ,
    a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧
    5 ≤ a ∧ 5 ≤ b ∧ 5 ≤ c ∧ 5 ≤ d ∧
    a < 2 ^ L ∧ b < 2 ^ L ∧ c < 2 ^ L ∧ d < 2 ^ L ∧
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 ∧
    (∀ j < k, binaryDigitMoment L a j = binaryDigitMoment L b j ∧
      binaryDigitMoment L a j = binaryDigitMoment L c j ∧
      binaryDigitMoment L a j = binaryDigitMoment L d j)

private lemma of_color_collision (m k : ℕ) (hm : 1 ≤ m)
    (h : FourCollision (sievePrimes (2 ^ m)) (momentColor (m+1) k (by omega))) :
    PrimeMomentCollision (m+1) k := by
  let κ := Fin k → Fin ((m+1)^k+1)
  let f : ℕ → κ := momentColor (m+1) k (by omega)
  obtain ⟨a,ha,b,hb,c,hc',d,hd,hab,hac,had,hbc,hbd,hcd,he,hfab,hfac,hfad⟩ := h
  have hprime {p : ℕ} (hp : p ∈ sievePrimes (2 ^ m)) :
      p.Prime ∧ 5 ≤ p ∧ p < 2 ^ (m+1) := by
    obtain ⟨hp, hprime, h5⟩ := mem_filter.mp hp
    have hp' := mem_range.mp hp
    have hle : p ≤ 2 ^ (m+1) := by rw [pow_succ']; omega
    have hne : p ≠ 2 ^ (m+1) := by
      intro hh
      rw [hh] at hprime
      have heq := hprime.eq_one_of_pow
      omega
    exact ⟨hprime, h5, lt_of_le_of_ne hle hne⟩
  have ha' := hprime ha
  have hb' := hprime hb
  have hc'' := hprime hc'
  have hd' := hprime hd
  refine ⟨a,b,c,d,ha'.1,hb'.1,hc''.1,hd'.1,ha'.2.1,hb'.2.1,hc''.2.1,hd'.2.1,
    ha'.2.2,hb'.2.2,hc''.2.2,hd'.2.2,hab,hac,had,hbc,hbd,hcd,he,?_⟩
  intro j hj
  have hmom {x y : ℕ} (hxy : f x = f y) :
      binaryDigitMoment (m+1) x j = binaryDigitMoment (m+1) y j := by
    exact congrArg (fun z : κ => (z ⟨j,hj⟩).val) hxy
  exact ⟨hmom hfab, hmom hfac, hmom hfad⟩

private lemma of_color_collision_length (m L k : ℕ) (hm : 1 ≤ m) (hml : m+1 = L)
    (h : FourCollision (sievePrimes (2 ^ m)) (momentColor L k (by omega))) :
    PrimeMomentCollision L k := by
  subst L
  exact of_color_collision m k hm h

/-- For every fixed number k of moments, prime-root collisions with all those
moments equal occur at every sufficiently large available bit length. -/
theorem eventually_prime_moment_collisions (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, PrimeMomentCollision (m+1) k := by
  filter_upwards [eventually_prime_color_collision (k * (k+1)), eventually_ge_atTop 1]
    with m hcolor hm
  apply of_color_collision m k hm
  exact hcolor _ (color_card _ _ (by omega)) _

/-- In particular these counterexamples have pairwise coprime roots, unlike
common-multiplier constructions. -/
theorem exists_pairwise_coprime_prime_moment_collision (k : ℕ) :
    ∃ L a b c d : ℕ,
      a.Prime ∧ b.Prime ∧ c.Prime ∧ d.Prime ∧
      a.Coprime b ∧ a.Coprime c ∧ a.Coprime d ∧
      b.Coprime c ∧ b.Coprime d ∧ c.Coprime d ∧
      a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a < 2 ^ L ∧ b < 2 ^ L ∧ c < 2 ^ L ∧ d < 2 ^ L ∧
      a ^ 2 + b ^ 2 = c ^ 2 + d ^ 2 ∧
      (∀ j < k, binaryDigitMoment L a j = binaryDigitMoment L b j ∧
        binaryDigitMoment L a j = binaryDigitMoment L c j ∧
        binaryDigitMoment L a j = binaryDigitMoment L d j) := by
  obtain ⟨m, hm⟩ := (eventually_prime_moment_collisions k).exists
  obtain ⟨a,b,c,d,ha,hb,hc,hd,_,_,_,_,haL,hbL,hcL,hdL,hab,hac,had,hbc,hbd,hcd,he,hmom⟩ := hm
  have cp {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) : p.Coprime q := by
    exact (hp.coprime_iff_not_dvd).mpr (by
      intro h
      exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).mp h))
  exact ⟨m+1,a,b,c,d,ha,hb,hc,hd,cp ha hb hab,cp ha hc hac,cp ha hd had,
    cp hb hc hbc,cp hb hd hbd,cp hc hd hcd,hab,hac,had,hbc,hbd,hcd,
    haL,hbL,hcL,hdL,he,hmom⟩


/-- A quantitative prime-root obstruction: quartic word length suffices for
any prescribed number of matching moments. This is not a Sidon construction. -/
theorem prime_moment_collision_quartic (k : ℕ) :
    PrimeMomentCollision ((256 * (k+1)) ^ 4) k := by
  let t : ℕ := 256 * (k+1)
  let L : ℕ := t ^ 4
  let m : ℕ := L - 1
  let q : ℕ := k * (k+1)
  let κ := Fin k → Fin (L ^ k + 1)
  have ht : 256 ≤ t := by dsimp [t]; omega
  have hLlarge : 896 ≤ L := by
    have hh := Nat.pow_le_pow_left ht 4
    norm_num at hh
    dsimp [L]
    omega
  have hm : 895 ≤ m := by dsimp [m]; omega
  have hml : m+1 = L := by dsimp [m]; omega
  have hmlR : (m : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hml
  let f : ℕ → κ := momentColor L k (by omega)
  have hcard : (Fintype.card κ : ℝ) ≤ (L : ℝ) ^ q := by
    exact_mod_cast color_card L k (by omega)
  let Y : ℝ := (k : ℝ) + 1
  have hY : 1 ≤ Y := by dsimp [Y]; linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hYpos : 0 < Y := by linarith
  have hY3 : 1 ≤ Y ^ 3 := one_le_pow₀ hY
  have htR : (t : ℝ) = 256 * Y := by dsimp [t,Y]; push_cast; ring
  have hLR : (L : ℝ) = (256 * Y) ^ 4 := by dsimp [L]; rw [Nat.cast_pow, htR]
  have htpos : (0 : ℝ) < t := by rw [htR]; positivity
  have hLpos : (0 : ℝ) < L := by rw [hLR]; positivity
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (show 1 ≤ L by omega)
  have hl2lo : (1/2 : ℝ) ≤ Real.log 2 := by
    have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh ⊢
    linarith
  have hl2hi : Real.log 2 ≤ 1 := by
    have hh := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hh
    exact hh
  have hlog128 : Real.log 128 ≤ 7 := by
    have hh : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]
      norm_num
    linarith
  have hlogL : Real.log (L : ℝ) ≤ 4 * t := by
    have hh := Real.log_le_sub_one_of_pos htpos
    have he : Real.log (L : ℝ) = 4 * Real.log (t : ℝ) := by
      dsimp [L]
      rw [Nat.cast_pow, Real.log_pow]
      norm_num
    linarith
  have hlogL0 : 0 ≤ Real.log (L : ℝ) := Real.log_nonneg hL1
  let x : ℝ := L * Real.log 2
  have hx : 1 < x := by
    have hL896 : (896 : ℝ) ≤ L := by exact_mod_cast hLlarge
    dsimp [x]
    nlinarith only [hL896, hl2lo]
  have hlogx : 0 < Real.log x := Real.log_pos hx
  have hlogxle : Real.log x ≤ 4 * t := by
    apply le_trans _ hlogL
    apply Real.log_le_log (by linarith : 0 < x)
    dsimp [x]
    nlinarith only [hl2hi, hLpos]
  have hq : ((q+1 : ℕ) : ℝ) ≤ Y ^ 2 := by
    dsimp [q,Y]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  have hnum : Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) ≤ 1031 * Y ^ 3 := by
    have hh := mul_le_mul hq hlogL hlogL0 (sq_nonneg Y)
    rw [htR] at hh
    nlinarith only [hh, hlog128, hY3]
  have hden : 512 * Real.log x ≤ 2048 * t := by linarith
  have hprod : (Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ)) *
      (512 * Real.log x) < x := by
    calc
      _ ≤ (1031 * Y ^ 3) * (2048 * t) :=
        mul_le_mul hnum hden (by positivity) (by positivity)
      _ < (L : ℝ) / 2 := by
        rw [htR, hLR]
        nlinarith only [pow_pos hYpos 4]
      _ ≤ x := by
        dsimp [x]
        nlinarith only [hl2lo, hLpos]
  have hgap : Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) <
      x / (512 * Real.log x) := (lt_div_iff₀ (by positivity)).mpr hprod
  have hcost : 128 * (Fintype.card κ : ℝ) * L *
      Real.exp (-x / (512 * Real.log x)) < 1 := by
    calc
      _ ≤ 128 * (L : ℝ) ^ q * L * Real.exp (-x / (512 * Real.log x)) := by
        gcongr
      _ = Real.exp (Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) -
          x / (512 * Real.log x)) := by
        rw [sub_eq_add_neg, Real.exp_add, Real.exp_add,
          Real.exp_log (by norm_num : (0 : ℝ) < 128), Real.exp_nat_mul,
          Real.exp_log hLpos, pow_succ]
        rw [neg_div]
        ring
      _ < 1 := by rw [Real.exp_lt_one_iff]; linarith only [hgap]
  have hcol := prime_color_collision_of_entropy m hm κ f (by
    rw [hmlR]
    exact hcost)
  exact of_color_collision_length m L k (by omega) hml hcol


/-- Prime-root collisions already exist with O(k^2 log^2(k+1)) bits while the
first k binary digit moments agree. All four roots are distinct primes. -/
theorem prime_moment_collision_quadratic_log (k : ℕ) :
    PrimeMomentCollision (2 ^ 20 * (k+1) ^ 2 * ((k+1).log2+1) ^ 2) k := by
  let ell : ℕ := (k+1).log2+1
  let L : ℕ := 2 ^ 20 * (k+1) ^ 2 * ell ^ 2
  let m : ℕ := L - 1
  let q : ℕ := k * (k+1)
  let κ := Fin k → Fin (L ^ k + 1)
  have hell : 1 ≤ ell := by dsimp [ell]; omega
  have hKsq : 1 ≤ (k+1)^2 := Nat.one_le_pow _ _ (by omega)
  have helsq : 1 ≤ ell^2 := Nat.one_le_pow _ _ hell
  have hLlarge : 896 ≤ L := by
    have hh : 2^20*1*1 ≤ L := Nat.mul_le_mul (Nat.mul_le_mul_left _ hKsq) helsq
    norm_num at hh
    omega
  have hm : 895 ≤ m := by dsimp [m]; omega
  have hml : m+1 = L := by dsimp [m]; omega
  have hmlR : (m : ℝ) + 1 = (L : ℝ) := by exact_mod_cast hml
  let f : ℕ → κ := momentColor L k (by omega)
  have hcard : (Fintype.card κ : ℝ) ≤ (L : ℝ) ^ q := by
    exact_mod_cast color_card L k (by omega)
  let K : ℝ := (k : ℝ) + 1
  have hK : 1 ≤ K := by dsimp [K]; linarith only [Nat.cast_nonneg (α := ℝ) k]
  have hKpos : 0 < K := by linarith only [hK]
  have hel : (1 : ℝ) ≤ ell := by exact_mod_cast hell
  have helpos : (0 : ℝ) < ell := by linarith only [hel]
  have hLR : (L : ℝ) = 2^20 * K^2 * (ell : ℝ)^2 := by dsimp [L,K]; push_cast; ring
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
  have hlogL : Real.log (L : ℝ) ≤ 24 * ell := by
    have he : Real.log (L : ℝ) = 20 * Real.log 2 + 2 * Real.log K + 2 * Real.log (ell : ℝ) := by
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
  have hlogxle : Real.log x ≤ 24 * ell := by
    apply le_trans _ hlogL
    apply Real.log_le_log (by linarith only [hx] : 0 < x)
    dsimp [x]
    nlinarith only [hl2hi,hLpos]
  have hq : ((q+1 : ℕ) : ℝ) ≤ K^2 := by
    dsimp [q,K]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) k]
  have hKE : 1 ≤ K^2 * (ell : ℝ) := by
    have hh : 1 ≤ K^2 := one_le_pow₀ hK
    nlinarith only [hh,hel]
  have hnum : Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ) ≤
      31 * K^2 * ell := by
    have hh := mul_le_mul hq hlogL hlogL0 (sq_nonneg K)
    nlinarith only [hh,hlog128,hKE]
  have hden : 512 * Real.log x ≤ 12288 * ell := by linarith only [hlogxle]
  have hprod : (Real.log 128 + ((q+1 : ℕ) : ℝ) * Real.log (L : ℝ)) *
      (512 * Real.log x) < x := by
    calc
      _ ≤ (31 * K^2 * ell) * (12288 * ell) :=
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

#print axioms prime_moment_collision_quadratic_log

#print axioms prime_moment_collision_quartic

#print axioms eventually_prime_moment_collisions
#print axioms exists_pairwise_coprime_prime_moment_collision
end Erdos773.PrimeMomentCollisions
