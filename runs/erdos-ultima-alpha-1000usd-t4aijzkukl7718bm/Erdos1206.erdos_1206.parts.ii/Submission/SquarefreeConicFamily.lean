import Submission.QuadraticSquarefreeSieve

/-! A conic family surviving a simultaneous square-divisor sieve.
The density here concerns parameters, not a cube-Sidon root set. -/
set_option maxHeartbeats 2000000

namespace Erdos1206.SquarefreeConicFamily
open Finset Filter QuadraticSquarefreeSieve
open scoped Classical Topology

def a : Fin 4 → ℕ := ![29,263,571,589]
def b : Fin 4 → ℕ := ![1160,19880,41884,43324]
def c : Fin 4 → ℕ := ![3419,374777,769417,797983]
def F (i : Fin 4) (t u : ℕ) : ℕ := quad (a i) (b i) (c i) t u

noncomputable def K : ℕ := Classical.choose (show ∃ n : ℕ, 1000000000 ≤ n from ⟨1000000000,le_rfl⟩)

lemma K_large : 1000000000 ≤ K := Classical.choose_spec (show ∃ n : ℕ, 1000000000 ≤ n from ⟨1000000000,le_rfl⟩)
@[irreducible] noncomputable def M : ℕ := sieveModulus K

noncomputable def roots (i : Fin 4) (x : ℕ × ℕ) : ℕ := F i (M*x.1) (M*x.2+1)

def Good (x : ℕ × ℕ) : Prop := ∀ i, Squarefree (roots i x)

noncomputable def good (N : ℕ) : Finset (ℕ × ℕ) := (range N ×ˢ range N).filter Good

lemma identity (t u : ℕ) : (F 0 t u)^3+(F 3 t u)^3=(F 1 t u)^3+(F 2 t u)^3 := by
  dsimp [F,quad,a,b,c]
  ring

lemma ordered (t u : ℕ) (hu : 0<u) :
    0<F 0 t u ∧ F 0 t u<F 1 t u ∧ F 1 t u<F 2 t u ∧ F 2 t u<F 3 t u := by
  have hu2 : 0<u^2 := pow_pos hu 2
  dsimp [F,quad,a,b,c]
  constructor
  · positivity
  constructor <;> (try constructor) <;> nlinarith

lemma coefficient_bounds (i : Fin 4) :
    0<a i ∧ a i≤K ∧ Squarefree (a i) ∧ a i+b i+c i≤1000000 := by
  have hK := K_large
  fin_cases i <;> norm_num [a,b,c]
  all_goals constructor
  all_goals first | omega | decide +kernel

lemma discriminant_bounds (i : Fin 4) :
    discriminant (a i) (b i) (c i) ≠ 0 ∧
      (discriminant (a i) (b i) (c i)).natAbs≤K := by
  have hK := K_large
  fin_cases i <;> norm_num [a,b,c,discriminant]
  all_goals omega

lemma good_eventually_large : ∀ᶠ N : ℕ in atTop, (N:ℝ)^2/2 ≤ (good N).card := by
  have hh := factorial_progression_sieve (by decide : 0<4) a b c K 1000000
    (by have := K_large; omega)
    (fun i => ⟨(coefficient_bounds i).1,(coefficient_bounds i).2.1,(coefficient_bounds i).2.2.1⟩)
    discriminant_bounds (fun i => (coefficient_bounds i).2.2.2)
  have hg (N : ℕ) : good N=goodPairs a b c M N := by
    ext x
    simp only [good,goodPairs,mem_filter,Good,roots,F]
  simp_rw [hg,M]
  exact hh

lemma modulus_pos : 0<M := by rw [M]; exact sieveModulus_pos K

lemma roots_pos (i : Fin 4) (x : ℕ × ℕ) : 0<roots i x := by
  have ha := (coefficient_bounds i).1
  dsimp [roots,F,quad]
  positivity

lemma roots_height (N : ℕ) (hN : 0<N) (i : Fin 4) {x : ℕ × ℕ}
    (hx : x∈range N ×ˢ range N) : roots i x≤(1000000*(M+1)*N)^2 :=
  (quad_size_bound (a i) (b i) (c i) M N 1000000 (coefficient_bounds i).1
    (coefficient_bounds i).2.2.2 hN hx).2

lemma F_injective {t u t' u' : ℕ}
    (h0 : F 0 t u=F 0 t' u') (h1 : F 1 t u=F 1 t' u')
    (h2 : F 2 t u=F 2 t' u') : t=t' ∧ u=u' := by
  have ht : t^2=t'^2 := by
    dsimp [F,quad,a,b,c] at h0 h1 h2
    nlinarith only [h0,h1,h2]
  have hu : u^2=u'^2 := by
    dsimp [F,quad,a,b,c] at h0 h1 h2
    nlinarith only [h0,h1,h2]
  exact ⟨Nat.pow_left_injective (by decide : 2 ≠ 0) ht,
    Nat.pow_left_injective (by decide : 2 ≠ 0) hu⟩

lemma roots_injective : Function.Injective (fun x => (roots 0 x,roots 1 x,roots 2 x,roots 3 x)) := by
  intro x y he
  have h0 := congrArg (fun z : ℕ × ℕ × ℕ × ℕ => z.1) he
  have h1 := congrArg (fun z : ℕ × ℕ × ℕ × ℕ => z.2.1) he
  have h2 := congrArg (fun z : ℕ × ℕ × ℕ × ℕ => z.2.2.1) he
  obtain ⟨ht,hu⟩ := F_injective h0 h1 h2
  apply Prod.ext
  · exact Nat.eq_of_mul_eq_mul_left modulus_pos ht
  · exact Nat.eq_of_mul_eq_mul_left modulus_pos (Nat.add_right_cancel hu)

lemma small_prime_divides_modulus {p : ℕ} (hp : p.Prime) (hpK : p≤K) : p∣M := by
  rw [M,sieveModulus]
  exact (Nat.dvd_factorial hp.pos hpK).trans (dvd_pow_self _ (by decide : 2 ≠ 0))

lemma root_modulus_reduction {p : ℕ} (hpM : p∣M) (i : Fin 4) (x : ℕ × ℕ) :
    (roots i x : ZMod p)=(a i : ZMod p) := by
  have hm := (CharP.cast_eq_zero_iff (ZMod p) p M).mpr hpM
  simp only [roots,F,quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one,hm,
    zero_mul,zero_add,one_pow,mul_one,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero]

lemma root_coprime_six (i : Fin 4) (x : ℕ × ℕ) : Nat.Coprime (roots i x) 6 := by
  apply Nat.coprime_of_dvd
  intro p hp hpn hp6
  have hpK : p≤K := (Nat.le_of_dvd (by decide : 0<6) hp6).trans (by have := K_large; omega)
  have hroot := (CharP.cast_eq_zero_iff (ZMod p) p (roots i x)).mpr hpn
  rw [root_modulus_reduction (small_prime_divides_modulus hp hpK)] at hroot
  have hpa := (CharP.cast_eq_zero_iff (ZMod p) p (a i)).mp hroot
  have hcop : Nat.Coprime (a i) 6 := by fin_cases i <;> norm_num [a]
  exact hp.not_dvd_one (by simpa [hcop.gcd_eq_one] using Nat.dvd_gcd hpa hp6)

lemma primitive {x : ℕ × ℕ} (hx : Good x) :
    Nat.gcd (Nat.gcd (roots 0 x) (roots 1 x)) (Nat.gcd (roots 2 x) (roots 3 x))=1 := by
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpg
  haveI : Fact p.Prime := ⟨hp⟩
  have hp0 : p∣roots 0 x := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hpg).1).1
  have hp1 : p∣roots 1 x := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hpg).1).2
  have hp2 : p∣roots 2 x := (Nat.dvd_gcd_iff.mp (Nat.dvd_gcd_iff.mp hpg).2).1
  have h0 := (CharP.cast_eq_zero_iff (ZMod p) p (roots 0 x)).mpr hp0
  have h1 := (CharP.cast_eq_zero_iff (ZMod p) p (roots 1 x)).mpr hp1
  have h2 := (CharP.cast_eq_zero_iff (ZMod p) p (roots 2 x)).mpr hp2
  by_cases hpk : p≤K
  · rw [root_modulus_reduction (small_prime_divides_modulus hp hpk)] at h0 h1
    have hpa := (CharP.cast_eq_zero_iff (ZMod p) p (a 0)).mp h0
    have hpb := (CharP.cast_eq_zero_iff (ZMod p) p (a 1)).mp h1
    have hh := Nat.dvd_gcd hpa hpb
    norm_num [a] at hh
    exact hp.ne_one hh
  · have hn : (721465056 : ZMod p) ≠ 0 := by
      intro h
      have hh := (CharP.cast_eq_zero_iff (ZMod p) p 721465056).mp h
      have hle := Nat.le_of_dvd (by decide : 0<721465056) hh
      have hbound : 721465056≤K := by have := K_large; omega
      omega
    simp only [roots,F,quad,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one] at h0 h1 h2
    norm_num [a,b,c] at h0 h1 h2
    change (571 : ZMod p)*(M*x.2+1)^2+41884*(M*x.1)*(M*x.2+1)+769417*(M*x.1)^2=0 at h2
    have ht2 : (721465056 : ZMod p)*(M*x.1)^2=0 := by
      linear_combination -335988*h0-552276*h1+271440*h2
    have hu2 : (721465056 : ZMod p)*(M*x.2+1)^2=0 := by
      linear_combination -401149908*h0-749322324*h1+366771600*h2
    have ht0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp ht2).resolve_left hn)
    have hu0 := (pow_eq_zero_iff (by decide : 2 ≠ 0)).mp ((mul_eq_zero.mp hu2).resolve_left hn)
    have hpt : p∣M*x.1 := (CharP.cast_eq_zero_iff (ZMod p) p _).mp (by simpa only [Nat.cast_mul] using ht0)
    have hpu : p∣M*x.2+1 := (CharP.cast_eq_zero_iff (ZMod p) p _).mp (by simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hu0)
    have hdv : p^2∣roots 0 x := by
      dsimp only [roots,F,quad]
      apply dvd_add
      · apply dvd_add
        · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpu 2) _
        · have hh := mul_dvd_mul hpt hpu
          simpa only [pow_two,mul_assoc] using dvd_mul_of_dvd_right hh (b 0)
      · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hpt 2) _
    exact (Nat.squarefree_iff_prime_squarefree.mp (hx 0) p hp) (by simpa only [pow_two] using hdv)

noncomputable def weight (x : ℕ × ℕ) : ℝ := if Good x then 1/(roots 3 x) else 0

/-- The simultaneously squarefree primitive family has divergent reciprocal
height mass. This is a collision-counting statement, not an independence bound. -/
theorem weight_not_summable : ¬ Summable weight := by
  intro hs
  let H : ℕ := 1000000*(M+1)
  have hH : (0:ℝ)<H := by dsimp [H]; positivity
  have hε : (0:ℝ)<1/(4*(H:ℝ)^2) := by positivity
  obtain ⟨S,hS⟩ := summable_iff_vanishing_norm.mp hs _ hε
  obtain ⟨N,hNg,hNS⟩ := (good_eventually_large.and
    (eventually_ge_atTop (4*S.card+1))).exists
  have hN : 0<N := by omega
  have hNR : (0:ℝ)<N := by exact_mod_cast hN
  have hNSR : 4*(S.card:ℝ)+1≤N := by exact_mod_cast hNS
  let T := good N \ S
  have hTc : (N:ℝ)^2/4 ≤ T.card := by
    have hh : ((good N).card:ℝ)≤T.card+S.card := by
      exact_mod_cast (card_le_card_sdiff_add_card (s := good N) (t := S))
    nlinarith [show (0:ℝ)≤(N:ℝ)^2 by positivity]
  have hper : ∀ x∈T, 1/((H:ℝ)^2*(N:ℝ)^2)≤weight x := by
    intro x hx
    have hxg := (mem_sdiff.mp hx).1
    have hxG : Good x := (mem_filter.mp hxg).2
    have hxN := (mem_filter.mp hxg).1
    have hrootR : (0:ℝ)<roots 3 x := by exact_mod_cast roots_pos 3 x
    have hrootbound : (roots 3 x:ℝ)≤(H:ℝ)^2*(N:ℝ)^2 := by
      have hh := roots_height N hN 3 hxN
      change roots 3 x≤(H*N)^2 at hh
      exact_mod_cast (by simpa only [mul_pow] using hh : roots 3 x≤H^2*N^2)
    rw [weight,if_pos hxG]
    exact one_div_le_one_div_of_le hrootR hrootbound
  have hsum := sum_le_sum hper
  have hTsum : (T.card:ℝ)*(1/((H:ℝ)^2*(N:ℝ)^2))≤∑x∈T,weight x := by
    simpa only [sum_const,nsmul_eq_mul] using hsum
  have hlow : 1/(4*(H:ℝ)^2)≤∑x∈T,weight x := by
    calc
      1/(4*(H:ℝ)^2) = ((N:ℝ)^2/4)/((H:ℝ)^2*(N:ℝ)^2) := by
        field_simp
      _ ≤ (T.card:ℝ)/((H:ℝ)^2*(N:ℝ)^2) := div_le_div_of_nonneg_right hTc (by positivity)
      _ ≤ ∑x∈T,weight x := by simpa only [mul_one_div] using hTsum
  have htail := hS T sdiff_disjoint
  have habs : (∑x∈T,weight x) ≤ ‖∑x∈T,weight x‖ := by simpa only [Real.norm_eq_abs] using le_abs_self (∑x∈T,weight x)
  linarith

abbrev Index := {x : ℕ × ℕ // Good x}

lemma index_weight_not_summable : ¬ Summable (fun x : Index => (1:ℝ)/(roots 3 x.val)) := by
  intro hs
  apply weight_not_summable
  have hh := (summable_subtype_iff_indicator (s := {x | Good x})
    (f := fun x => (1:ℝ)/(roots 3 x))).mp hs
  simpa only [weight,Set.indicator,Set.mem_setOf_eq] using hh

abbrev Collision := {v : Fin 4 → ℕ //
  0<v 0 ∧ v 0<v 1 ∧ v 1<v 2 ∧ v 2<v 3 ∧
  (v 0)^3+(v 3)^3=(v 1)^3+(v 2)^3 ∧
  Nat.gcd (Nat.gcd (v 0) (v 1)) (Nat.gcd (v 2) (v 3))=1 ∧
  ∀i, Squarefree (v i) ∧ Nat.Coprime (v i) 6}

noncomputable def collision (x : Index) : Collision :=
  ⟨fun i => roots i x.val,
    (ordered (M*x.val.1) (M*x.val.2+1) (by omega)).1,
    (ordered (M*x.val.1) (M*x.val.2+1) (by omega)).2.1,
    (ordered (M*x.val.1) (M*x.val.2+1) (by omega)).2.2.1,
    (ordered (M*x.val.1) (M*x.val.2+1) (by omega)).2.2.2,
    identity _ _,primitive x.property,fun i => ⟨x.property i,root_coprime_six i x.val⟩⟩

lemma collision_injective : Function.Injective collision := by
  intro x y he
  apply Subtype.ext
  apply roots_injective
  have hv := congrArg Subtype.val he
  have h0 := congrFun hv 0
  have h1 := congrFun hv 1
  have h2 := congrFun hv 2
  have h3 := congrFun hv 3
  exact Prod.ext h0 (Prod.ext h1 (Prod.ext h2 h3))

theorem squarefree_coprime_six_primitive_mass_diverges :
    ¬ Summable (fun e : Collision => (1:ℝ)/(e.val 3)) := by
  intro hs
  have hh := hs.comp_injective collision_injective
  apply index_weight_not_summable
  simpa only [Function.comp_def,collision] using hh

theorem exists_large_squarefree_primitive_mass (C : ℝ) :
    ∃ E : Finset Collision, C < ∑e∈E,(1:ℝ)/(e.val 3) := by
  by_contra hn
  push_neg at hn
  exact squarefree_coprime_six_primitive_mass_diverges
    (summable_of_sum_le (fun e => by positivity) hn)

#print axioms weight_not_summable
#print axioms squarefree_coprime_six_primitive_mass_diverges
#print axioms exists_large_squarefree_primitive_mass
end Erdos1206.SquarefreeConicFamily
