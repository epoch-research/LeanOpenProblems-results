import FormalConjecturesUtil

/-!
A stronger interval bound and a Pell family near its square-root scale.
These auxiliary results do not settle the positive-density conjecture.
-/

namespace Erdos1206

private lemma cube_mod_six (n : ℕ) : n ^ 3 % 6 = n % 6 := by
  have h : n % 6 = 0 ∨ n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
  rcases h with h | h | h | h | h | h <;> simp [Nat.pow_mod, h]

private lemma cube_sum_lt_of_sum_gap_six (a b c d L : ℤ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hspread : (a - b) ^ 2 ≤ L ^ 2)
    (hsize : L ^ 2 ≤ 6 * (a + b) + 36)
    (hgap : a + b + 6 ≤ c + d) :
    a ^ 3 + b ^ 3 < c ^ 3 + d ^ 3 := by
  have hpow : (a + b + 6) ^ 3 ≤ (c + d) ^ 3 :=
    pow_le_pow_left₀ (by omega) hgap 3
  have hspread' := mul_le_mul_of_nonneg_left hspread
    (show (0 : ℤ) ≤ 3 * (a + b) by omega)
  have hsize' := mul_le_mul_of_nonneg_left hsize
    (show (0 : ℤ) ≤ 3 * (a + b) by omega)
  have hnonneg := mul_nonneg (show (0 : ℤ) ≤ 3 * (c + d) by omega)
    (sq_nonneg (c - d))
  nlinarith only [hpow, hspread', hsize', hnonneg]

lemma cubes_sidon_on_short_interval_twelve (L M : ℕ)
    (hsize : L ^ 2 ≤ 12 * M + 36) :
    IsSidon ((fun a : ℕ => a ^ 3) '' Set.Icc M (M + L)) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩ _ ⟨b, hb, rfl⟩ _ ⟨d, hd, rfl⟩ heq
  have hmod : (a + b) % 6 = (c + d) % 6 := by
    have hh := congrArg (fun n : ℕ => n % 6) heq
    simpa only [Nat.add_mod, cube_mod_six, Nat.mod_mod] using hh
  have hint (x y : ℕ) (hx : x ∈ Set.Icc M (M + L))
      (hy : y ∈ Set.Icc M (M + L)) :
      ((x : ℤ) - y) ^ 2 ≤ (L : ℤ) ^ 2 ∧
        (L : ℤ) ^ 2 ≤ 6 * ((x : ℤ) + y) + 36 := by
    have hx₁ : (M : ℤ) ≤ x := by exact_mod_cast hx.1
    have hy₁ : (M : ℤ) ≤ y := by exact_mod_cast hy.1
    have hx₂ : (x : ℤ) ≤ M + L := by exact_mod_cast hx.2
    have hy₂ : (y : ℤ) ≤ M + L := by exact_mod_cast hy.2
    have hsizeZ : (L : ℤ) ^ 2 ≤ 12 * M + 36 := by exact_mod_cast hsize
    have h₁ : 0 ≤ (L : ℤ) - ((x : ℤ) - y) := by omega
    have h₂ : 0 ≤ (L : ℤ) + ((x : ℤ) - y) := by omega
    constructor
    · nlinarith [mul_nonneg h₁ h₂]
    · omega
  have heqZ : (a : ℤ) ^ 3 + (b : ℤ) ^ 3 = (c : ℤ) ^ 3 + (d : ℤ) ^ 3 := by
    exact_mod_cast heq
  have hsum : a + b = c + d := by
    rcases lt_trichotomy (a + b) (c + d) with hlt | he | hgt
    · have hgap : (a : ℤ) + b + 6 ≤ c + d := by omega
      obtain ⟨hspread, hsize'⟩ := hint a b ha hb
      have h := cube_sum_lt_of_sum_gap_six a b c d L
        (by omega) (by omega) hspread hsize' hgap
      omega
    · exact he
    · have hgap : (c : ℤ) + d + 6 ≤ a + b := by omega
      obtain ⟨hspread, hsize'⟩ := hint c d hc hd
      have h := cube_sum_lt_of_sum_gap_six c d a b L
        (by omega) (by omega) hspread hsize' hgap
      omega
  by_cases hzero : a + b = 0
  · have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    have hc0 : c = 0 := by omega
    have hd0 : d = 0 := by omega
    simp [ha0, hb0, hc0, hd0]
  have hprod : a * b = c * d := by
    have hid : 3 * (a + b) * (a * b) + (a ^ 3 + b ^ 3) = (a + b) ^ 3 := by ring
    have hid' : 3 * (c + d) * (c * d) + (c ^ 3 + d ^ 3) = (c + d) ^ 3 := by ring
    rw [hsum, heq] at hid
    have hh : 3 * (c + d) * (a * b) = 3 * (c + d) * (c * d) :=
      Nat.add_right_cancel (hid.trans hid'.symm)
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3 * (c + d)) hh
  have hsumZ : (a : ℤ) + b = c + d := by exact_mod_cast hsum
  have hprodZ : (a : ℤ) * b = (c : ℤ) * d := by exact_mod_cast hprod
  have hfactor : ((a : ℤ) - c) * ((a : ℤ) - d) = 0 := by nlinarith
  rcases mul_eq_zero.mp hfactor with h | h
  · have hac : a = c := by omega
    have hbd : b = d := by omega
    exact Or.inl ⟨congrArg (fun n : ℕ => n ^ 3) hac, congrArg (fun n : ℕ => n ^ 3) hbd⟩
  · have had : a = d := by omega
    have hbc : b = c := by omega
    exact Or.inr ⟨congrArg (fun n : ℕ => n ^ 3) had, congrArg (fun n : ℕ => n ^ 3) hbc⟩


/-- Unequal root-pair sums force a stronger spread bound. -/
private lemma cube_pair_spread_bound (a b c d k : ℤ)
    (hS : 0 < a+b) (hk : 1 ≤ k) (hs : c+d = a+b+6*k)
    (he : a^3+b^3=c^3+d^3) : 19*(a+b) < 3*(a-b)^2 := by
  let S := a+b
  let s := 6*k
  let D := a-b
  let E := c-d
  let r := 2*(c*d-a*b)-9*k*S-36*k^2
  have hs6 : 6 ≤ s := by dsimp [s]; omega
  have hs0 : 0 < s := by omega
  have hS0 : 0 < S := hS
  have hs' : c+d=S+s := hs
  have hid₁ : S^3+3*S*D^2=4*(a^3+b^3) := by dsimp [S,D]; ring
  have hid₂ : (c+d)^3+3*(c+d)*E^2=4*(c^3+d^3) := by dsimp [E]; ring
  rw [hs'] at hid₂
  have hbasic : S^3+3*S*D^2=(S+s)^3+3*(S+s)*E^2 := by omega
  have hrid : 2*r=D^2-E^2-s^2-s*S := by
    have hsq := congrArg (fun n : ℤ => n^2) hs'
    dsimp [r,D,E,s,S] at *
    nlinarith only [hsq]
  have heq : 6*r*S=3*s*E^2+s^3 := by
    nlinarith only [hbasic, congrArg (fun n : ℤ => n*S) hrid]
  have hE : 0 ≤ 3*s*E^2 := mul_nonneg (by omega) (sq_nonneg _)
  have hs3 : 0 < s^3 := pow_pos hs0 _
  have hrS : 0 < r*S := by nlinarith only [heq,hE,hs3]
  have hr0 : 0 < r := (mul_pos_iff_of_pos_right hS0).mp hrS
  have hr : 1 ≤ r := hr0
  have hcoef : 19*s ≤ 3*(s^2+2*r) := by
    have hh := mul_nonneg (show 0 ≤ s-6 by omega) (show 0 ≤ 3*s-1 by omega)
    nlinarith
  have hcoefS := mul_le_mul_of_nonneg_right hcoef hS0.le
  have hlast : 0 < 6*s*r := mul_pos (by omega) hr0
  have heq' : 3*s*D^2=3*(s^2+2*r)*S+2*s^3+6*s*r := by
    nlinarith only [heq, congrArg (fun n : ℤ => 3*s*n) hrid]
  have hh : (19*S)*s < (3*D^2)*s := by
    nlinarith only [hcoefS,heq',hs3,hlast]
  exact (mul_lt_mul_iff_left₀ hs0).mp (by nlinarith only [hh])

/-- The asymptotically sharp uniform short-interval constant is `38/3`.
The strict lower-order gap allows the weak inequality in this statement. -/
lemma cubes_sidon_on_short_interval_sharp (L M : ℕ)
    (hsize : 3*L^2 ≤ 38*M) :
    IsSidon ((fun a : ℕ => a^3) '' Set.Icc M (M+L)) := by
  by_cases hM : M=0
  · subst M
    have hL : L=0 := by nlinarith
    subst L
    simp [IsSidon]
  rintro _ ⟨a,ha,rfl⟩ _ ⟨c,hc,rfl⟩ _ ⟨b,hb,rfl⟩ _ ⟨d,hd,rfl⟩ he
  have haM := ha.1
  have hbM := hb.1
  have hcM := hc.1
  have hdM := hd.1
  have hmod : (a+b)%6=(c+d)%6 := by
    have hh := congrArg (fun n : ℕ => n%6) he
    simpa only [Nat.add_mod,cube_mod_six,Nat.mod_mod] using hh
  have heZ : (a : ℤ)^3+b^3=c^3+d^3 := by exact_mod_cast he
  have hspread (x y : ℕ) (hx : x ∈ Set.Icc M (M+L))
      (hy : y ∈ Set.Icc M (M+L)) : ((x : ℤ)-y)^2 ≤ (L : ℤ)^2 := by
    have hx₁ : (M : ℤ) ≤ x := by exact_mod_cast hx.1
    have hy₁ : (M : ℤ) ≤ y := by exact_mod_cast hy.1
    have hx₂ : (x : ℤ) ≤ M+L := by exact_mod_cast hx.2
    have hy₂ : (y : ℤ) ≤ M+L := by exact_mod_cast hy.2
    have hh := mul_nonneg (show 0 ≤ (L : ℤ)-((x : ℤ)-y) by omega)
      (show 0 ≤ (L : ℤ)+((x : ℤ)-y) by omega)
    nlinarith
  have hsizeZ : 3*(L : ℤ)^2 ≤ 38*M := by exact_mod_cast hsize
  have hsum : a+b=c+d := by
    rcases lt_trichotomy (a+b) (c+d) with hlt | heq | hgt
    · let k := (c+d-(a+b))/6
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hs : (c : ℤ)+d=(a : ℤ)+b+6*k := by dsimp [k]; omega
      have hh := cube_pair_spread_bound a b c d k (by omega) (by exact_mod_cast hk) hs heZ
      have haZ : (M : ℤ) ≤ a := by exact_mod_cast ha.1
      have hbZ : (M : ℤ) ≤ b := by exact_mod_cast hb.1
      nlinarith only [hh,hspread a b ha hb,hsizeZ,haZ,hbZ]
    · exact heq
    · let k := (a+b-(c+d))/6
      have hk : 1 ≤ k := by dsimp [k]; omega
      have hs : (a : ℤ)+b=(c : ℤ)+d+6*k := by dsimp [k]; omega
      have hh := cube_pair_spread_bound c d a b k (by omega) (by exact_mod_cast hk) hs heZ.symm
      have hcZ : (M : ℤ) ≤ c := by exact_mod_cast hc.1
      have hdZ : (M : ℤ) ≤ d := by exact_mod_cast hd.1
      nlinarith only [hh,hspread c d hc hd,hsizeZ,hcZ,hdZ]
  have hp : a*b=c*d := by
    have h₁ : 3*(a+b)*(a*b)+(a^3+b^3)=(a+b)^3 := by ring
    have h₂ : 3*(c+d)*(c*d)+(c^3+d^3)=(c+d)^3 := by ring
    rw [hsum,he] at h₁
    exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 3*(c+d))
      (Nat.add_right_cancel (h₁.trans h₂.symm))
  have hsumZ : (a : ℤ)+b=c+d := by exact_mod_cast hsum
  have hpZ : (a : ℤ)*b=c*d := by exact_mod_cast hp
  have hf : ((a : ℤ)-c)*(a-d)=0 := by nlinarith
  rcases mul_eq_zero.mp hf with hh | hh
  · have hac : a=c := by omega
    have hbd : b=d := by omega
    simp [hac,hbd]
  · have had : a=d := by omega
    have hbc : b=c := by omega
    simp [had,hbc]


namespace NearDiagonalCubes

/-- A Pell equation in coordinates for which all four roots are integral. -/
def PellPair (p q : ℕ) : Prop := p^2+p = 19*q^2+19*q+68

lemma pell_step {p q : ℕ} (h : PellPair p q) :
    PellPair (170*p+741*q+455) (39*p+170*q+104) := by
  dsimp [PellPair] at h ⊢
  nlinarith only [h]

lemma pell_large (N : ℕ) : ∃ p q : ℕ, PellPair p q ∧ N ≤ q ∧ 2 ≤ q := by
  induction N with
  | zero => exact ⟨13,2,by norm_num [PellPair],by omega,by omega⟩
  | succ N ih =>
    rcases ih with ⟨p,q,h,hN,hq⟩
    exact ⟨170*p+741*q+455,39*p+170*q+104,pell_step h,by omega,by omega⟩

lemma pell_linear_bound {p q : ℕ} (h : PellPair p q) (hq : 2 ≤ q) : p ≤ 6*q+3 := by
  dsimp [PellPair] at h
  by_contra! hlt
  have hsq := Nat.pow_le_pow_left hlt 2
  nlinarith

/-- Four explicitly defined roots, with pair-sum difference exactly six. -/
def a (p q : ℕ) : ℕ := 6*q^2+6*q+19-p
def b (q : ℕ) : ℕ := 6*q^2+5*q+22
def c (q : ℕ) : ℕ := 6*q^2+7*q+23
def d (p q : ℕ) : ℕ := 6*q^2+6*q+20+p

lemma roots_identity {p q : ℕ} (h : PellPair p q) (hq : 2 ≤ q) :
    a p q ^ 3 + d p q ^ 3 = b q ^ 3 + c q ^ 3 := by
  have hp := pell_linear_bound h hq
  have hsub : a p q + p = 6*q^2+6*q+19 := by dsimp [a]; omega
  have hZ : (p : ℤ)^2+p = 19*(q : ℤ)^2+19*q+68 := by exact_mod_cast h
  have haZ : (a p q : ℤ) = 6*(q : ℤ)^2+6*q+19-p := by
    have hh : (a p q : ℤ) + p = 6*(q : ℤ)^2+6*q+19 := by exact_mod_cast hsub
    omega
  have hid : ((6*(q : ℤ)^2+6*q+19-p)^3 + (6*q^2+6*q+20+p)^3 -
      (6*q^2+5*q+22)^3 - (6*q^2+7*q+23)^3) =
      (36*q^2+36*q+117)*(p^2+p-19*q^2-19*q-68) := by ring
  have hz : (p : ℤ)^2+p-19*q^2-19*q-68 = 0 := by omega
  rw [hz, mul_zero] at hid
  have he : (a p q : ℤ)^3+(d p q : ℤ)^3=(b q : ℤ)^3+(c q : ℤ)^3 := by
    simp only [b,c,d,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow]
    rw [haZ]
    omega
  exact_mod_cast he

lemma roots_ordered {p q : ℕ} (h : PellPair p q) (hq : 2 ≤ q) :
    0 < a p q ∧ a p q < b q ∧ b q < c q ∧ c q < d p q := by
  have hp := pell_linear_bound h hq
  have hpq : q+3 < p := by
    dsimp [PellPair] at h
    by_contra! hlt
    have hsq := Nat.pow_le_pow_left hlt 2
    nlinarith
  dsimp [a,b,c,d]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

lemma roots_small_span {p q : ℕ} (h : PellPair p q) (hq : 40 ≤ q) :
    d p q = a p q + (2*p+1) ∧ (2*p+1)^2 ≤ 13*a p q := by
  have hp := pell_linear_bound h (by omega)
  have hsub : a p q + p = 6*q^2+6*q+19 := by dsimp [a]; omega
  constructor
  · dsimp [d]; omega
  · dsimp [PellPair] at h
    have hs : (2*p+1)^2 = 76*q^2+76*q+273 := by nlinarith only [h]
    rw [hs]
    nlinarith

/-- There are arbitrarily far intervals with a nontrivial cubic collision
and squared width at most thirteen times their starting point. -/
theorem arbitrarily_far_collisions (N : ℕ) :
    ∃ M L a b c d : ℕ, N ≤ M ∧ 0 < M ∧ L^2 ≤ 13*M ∧
      M ≤ a ∧ a < b ∧ b < c ∧ c < d ∧ d ≤ M+L ∧
      a^3+d^3=b^3+c^3 := by
  rcases pell_large (max N 40) with ⟨p,q,h,hN,hq⟩
  have hq40 : 40 ≤ q := le_trans (le_max_right _ _) hN
  have hqN : N ≤ q := le_trans (le_max_left _ _) hN
  have ho := roots_ordered h hq
  have hspan := roots_small_span h hq40
  refine ⟨a p q,2*p+1,a p q,b q,c q,d p q,?_,ho.1,hspan.2,le_rfl,
    ho.2.1,ho.2.2.1,ho.2.2.2,le_of_eq hspan.1,roots_identity h hq⟩
  have hp := pell_linear_bound h hq
  have hsub : a p q + p = 6*q^2+6*q+19 := by dsimp [a]; omega
  nlinarith


/-- Every strictly larger constant fails arbitrarily far out. Together with
`cubes_sidon_on_short_interval_sharp`, this proves asymptotic sharpness. -/
theorem interval_constant_sharp (C : ℝ) (hC : 38/3 < C) (N : ℕ) :
    ∃ M L : ℕ, N ≤ M ∧ 0 < M ∧ (L : ℝ)^2 ≤ C*M ∧
      ¬ IsSidon ((fun a : ℕ => a^3) '' Set.Icc M (M+L)) := by
  let ε := C-38/3
  have hε : 0 < ε := sub_pos.mpr hC
  obtain ⟨K,hK⟩ := exists_nat_gt (500/ε)
  rcases pell_large (max (max N 40) K) with ⟨p,q,h,hlarge,hq⟩
  have hqN : N ≤ q := by omega
  have hqK : K ≤ q := by omega
  have hq40 : 40 ≤ q := by omega
  let M := a p q
  let L := 2*p+1
  have hp := pell_linear_bound h hq
  have hsub : M+p=6*q^2+6*q+19 := by dsimp [M,a]; omega
  have hMquad : q^2 ≤ M := by nlinarith
  have ho := roots_ordered h hq
  have hspan := (roots_small_span h hq40).1
  have hMN : N ≤ M := by nlinarith
  have hMq : 0 < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1 : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
  have hqK' : (K : ℝ) ≤ q := by exact_mod_cast hqK
  have hepsq : 500 < ε*(q : ℝ) := by
    have hh := (div_lt_iff₀ hε).mp (hK.trans_le hqK')
    nlinarith only [hh]
  have hepsqq := mul_lt_mul_of_pos_right hepsq hMq
  have hquadR : (q : ℝ)^2 ≤ M := by exact_mod_cast hMquad
  have hepsM := mul_le_mul_of_nonneg_left hquadR (show 0 ≤ 3*ε by positivity)
  have hpR : (p : ℝ) ≤ 6*q+3 := by exact_mod_cast hp
  have htail : 38*(p : ℝ)+97 ≤ 3*ε*M := by
    nlinarith only [hepsqq,hepsM,hpR,hq1]
  have hexact : 3*L^2=38*M+38*p+97 := by
    dsimp [L]
    dsimp [PellPair] at h
    nlinarith only [h,hsub]
  have hexactR : 3*(L : ℝ)^2=38*M+38*p+97 := by exact_mod_cast hexact
  refine ⟨M,L,hMN,ho.1,?_,?_⟩
  · dsimp [ε] at htail
    nlinarith only [htail,hexactR]
  · intro hs
    have ha : a p q ∈ Set.Icc M (M+L) := by dsimp [M,L]; constructor <;> omega
    have hb : b q ∈ Set.Icc M (M+L) := by dsimp [M,L]; constructor <;> omega
    have hc : c q ∈ Set.Icc M (M+L) := by dsimp [M,L]; constructor <;> omega
    have hd : d p q ∈ Set.Icc M (M+L) := by dsimp [M,L]; constructor <;> omega
    have hh := hs _ ⟨a p q,ha,rfl⟩ _ ⟨b q,hb,rfl⟩
      _ ⟨d p q,hd,rfl⟩ _ ⟨c q,hc,rfl⟩ (roots_identity h hq)
    rcases hh with hh | hh
    · have he := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
      omega
    · have he := Nat.pow_left_injective (by decide : 3 ≠ 0) hh.1
      omega

end NearDiagonalCubes

#print axioms cubes_sidon_on_short_interval_twelve
#print axioms cubes_sidon_on_short_interval_sharp
#print axioms NearDiagonalCubes.interval_constant_sharp
#print axioms NearDiagonalCubes.arbitrarily_far_collisions

end Erdos1206
