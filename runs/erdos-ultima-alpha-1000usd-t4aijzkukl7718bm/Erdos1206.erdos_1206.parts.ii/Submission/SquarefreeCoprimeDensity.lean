import FormalConjecturesUtil

/-! A quantitative density bound for squarefree integers coprime to a fixed
integer. This is an auxiliary sieve estimate, not a settlement of Erdős 1206. -/

namespace Erdos1206.SquarefreeCoprimeDensity
open Finset Filter
open scoped Classical Topology
set_option maxHeartbeats 1000000

noncomputable def copCount (h N : ℕ) : ℕ :=
  ((range N).filter (fun n => h.Coprime n)).card

lemma copCount_mono (h : ℕ) : Monotone (copCount h) := by
  intro a b hab
  exact card_le_card (filter_subset_filter _ (range_mono hab))

lemma copCount_mul (h k : ℕ) : copCount h (k*h) = k*h.totient := by
  have he (N : ℕ) : copCount h N = Nat.count (fun n => h.Coprime n) N :=
    (Nat.count_eq_card_filter_range _ _).symm
  induction k with
  | zero => simp [copCount]
  | succ k ih =>
    rw [Nat.succ_mul, he, Nat.count_add, ← he, ih]
    have hh : (fun n => h.Coprime (k*h+n)) = (fun n => h.Coprime n) := by
      funext n
      apply propext
      simpa only [add_comm] using Nat.coprime_add_mul_right_right h n k
    simp only [Nat.count_eq_card_filter_range, hh] 
    change k*h.totient+h.totient=(k+1)*h.totient
    ring

noncomputable def copRate (h : ℕ) : ℝ := (h.totient : ℝ)/h

lemma copRate_nonneg (h : ℕ) : 0 ≤ copRate h := by dsimp [copRate]; positivity
lemma copRate_le_one {h : ℕ} (hh : 0<h) : copRate h ≤ 1 := by
  dsimp [copRate]
  exact (div_le_one (by exact_mod_cast hh)).mpr (by exact_mod_cast Nat.totient_le h)

lemma copCount_bounds {h : ℕ} (hh : 0<h) (N : ℕ) :
    copRate h*N-h ≤ (copCount h N : ℝ) ∧
      (copCount h N : ℝ) ≤ copRate h*N+h := by
  have hlo := copCount_mono h (Nat.div_mul_le_self N h)
  have hhi := copCount_mono h (Nat.lt_mul_div_succ N hh).le
  rw [copCount_mul] at hlo
  rw [mul_comm h, copCount_mul] at hhi
  have hloR : ((N/h : ℕ):ℝ)*h.totient ≤ copCount h N := by exact_mod_cast hlo
  have hhiR : (copCount h N : ℝ) ≤ (((N/h : ℕ):ℝ)+1)*h.totient := by exact_mod_cast hhi
  have hfloor : (N : ℝ) < (h : ℝ)*(((N/h : ℕ):ℝ)+1) := by
    exact_mod_cast Nat.lt_mul_div_succ N hh
  have hfloor' : (((N/h : ℕ):ℝ))*(h : ℝ) ≤ N := by
    exact_mod_cast Nat.div_mul_le_self N h
  have hrate : copRate h*(h : ℝ)=h.totient := by
    dsimp [copRate]
    exact div_mul_cancel₀ _ (by exact_mod_cast hh.ne')
  have ht : (h.totient : ℝ) ≤ h := by exact_mod_cast Nat.totient_le h
  have h₁ := mul_le_mul_of_nonneg_left hfloor.le (copRate_nonneg h)
  have h₂ := mul_le_mul_of_nonneg_left hfloor' (copRate_nonneg h)
  constructor <;> nlinarith [hrate]

lemma reciprocal_square_sum (T : ℕ) :
    (∑ k ∈ Icc 2 T, (1:ℝ)/(k:ℝ)^2) ≤ 3/4 := by
  have hs : Icc 2 T ⊆ insert 2 (Ioc 2 (max 2 T)) := by
    intro k hk
    obtain ⟨hk₁,hk₂⟩ := mem_Icc.mp hk
    by_cases he : k=2
    · simp [he]
    · exact mem_insert_of_mem (mem_Ioc.mpr ⟨by omega,hk₂.trans (le_max_right _ _)⟩)
  have hsum := sum_le_sum_of_subset_of_nonneg hs
    (fun k _ _ => by positivity : ∀ k ∈ insert 2 (Ioc 2 (max 2 T)),
      k ∉ Icc 2 T → 0 ≤ (1:ℝ)/(k:ℝ)^2)
  rw [sum_insert (by simp)] at hsum
  have ht := sum_Ioc_inv_sq_le_sub (α := ℝ) (by decide : (2:ℕ) ≠ 0) (le_max_left 2 T)
  simp only [← one_div] at ht
  norm_num only [Nat.cast_ofNat] at hsum ht
  have hz : (0:ℝ) ≤ 1/(max 2 T : ℕ) := by positivity
  linarith

noncomputable def sfCount (h N : ℕ) : ℕ :=
  ((range N).filter (fun n => Squarefree n ∧ h.Coprime n)).card

private lemma square_multiple_copCount (h N k : ℕ) :
    ((range N).filter (fun n => h.Coprime n ∧ k^2 ∣ n)).card ≤
      copCount h (N/k^2+1) := by
  dsimp only [copCount]
  apply card_le_card_of_injOn (fun n => n/k^2)
  · intro n hn
    change n ∈ (range N).filter (fun n => h.Coprime n ∧ k^2 ∣ n) at hn
    have hn' := mem_filter.mp hn
    change n/k^2 ∈ (range (N/k^2+1)).filter (fun n => h.Coprime n)
    apply mem_filter.mpr
    constructor
    · apply mem_range.mpr
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (mem_range.mp hn'.1).le)
    · apply hn'.2.1.of_dvd_right
      exact Nat.div_dvd_of_dvd hn'.2.2
  · intro a ha b hb hab
    change a ∈ (range N).filter (fun n => h.Coprime n ∧ k^2 ∣ n) at ha
    change b ∈ (range N).filter (fun n => h.Coprime n ∧ k^2 ∣ n) at hb
    have ha' := (mem_filter.mp ha).2.2
    have hb' := (mem_filter.mp hb).2.2
    have hma := Nat.div_mul_cancel ha'
    have hmb := Nat.div_mul_cancel hb'
    dsimp only at hab
    rw [hab] at hma
    exact hma.symm.trans hmb

lemma sfCount_lower {h : ℕ} (hh : 0<h) (N : ℕ) :
    copRate h*N/4 ≤ (sfCount h N : ℝ)+(h+1)*(N.sqrt+1) := by
  let C := (range N).filter (fun n => h.Coprime n)
  let G := (range N).filter (fun n => Squarefree n ∧ h.Coprime n)
  let B (k : ℕ) := (range N).filter (fun n => h.Coprime n ∧ k^2 ∣ n)
  let U := (Icc 2 N.sqrt).biUnion B
  have hsub : C ⊆ G ∪ ({0} ∪ U) := by
    intro n hn
    have hn' := mem_filter.mp hn
    by_cases hsf : Squarefree n
    · exact mem_union_left _ (mem_filter.mpr ⟨hn'.1,hsf,hn'.2⟩)
    · apply mem_union_right
      by_cases hn0 : n=0
      · simp [hn0]
      · apply mem_union_right
        have hnot : ¬ ∀ p : ℕ, p.Prime → ¬ p*p ∣ n := by
          simpa only [← Nat.squarefree_iff_prime_squarefree] using hsf
        push_neg at hnot
        obtain ⟨p,hp,hpd⟩ := hnot
        have hpN : p ≤ N.sqrt := Nat.le_sqrt.mpr
          ((Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpd).trans (mem_range.mp hn'.1).le)
        exact mem_biUnion.mpr ⟨p,mem_Icc.mpr ⟨hp.two_le,hpN⟩,
          mem_filter.mpr ⟨hn'.1,hn'.2,by simpa [pow_two] using hpd⟩⟩
  have hcount : copCount h N ≤ sfCount h N+1+∑ k ∈ Icc 2 N.sqrt, (B k).card := by
    have hc := card_le_card hsub
    have hu : U.card ≤ ∑ k ∈ Icc 2 N.sqrt, (B k).card := card_biUnion_le
    have hg := card_union_le G ({0} ∪ U)
    have hz := card_union_le ({0} : Finset ℕ) U
    simp only [card_singleton] at hz
    change copCount h N ≤ _ at hc
    change _ ≤ sfCount h N+_ at hg
    omega
  have hterm (k : ℕ) (hk : k ∈ Icc 2 N.sqrt) :
      ((B k).card : ℝ) ≤ copRate h*N/(k:ℝ)^2+h+1 := by
    have hc : ((B k).card : ℝ) ≤ copCount h (N/k^2+1) := by
      exact_mod_cast square_multiple_copCount h N k
    have hd := (copCount_bounds hh (N/k^2+1)).2
    have hf : (((N/k^2 : ℕ):ℝ)) ≤ (N:ℝ)/(k:ℝ)^2 := by
      have hf : (((N/k^2 : ℕ):ℝ)) ≤ (N:ℝ)/((k^2:ℕ):ℝ) := Nat.cast_div_le
      simpa only [Nat.cast_pow] using hf
    have hm := mul_le_mul_of_nonneg_left hf (copRate_nonneg h)
    simp only [Nat.cast_add,Nat.cast_one] at hd
    have hr := copRate_le_one hh
    nlinarith [show copRate h*((N:ℝ)/(k:ℝ)^2)=copRate h*N/(k:ℝ)^2 by ring]
  have hsum := sum_le_sum hterm
  have he : (∑ k ∈ Icc 2 N.sqrt, (copRate h*N/(k:ℝ)^2+(h:ℝ)+1)) =
      copRate h*N*(∑ k ∈ Icc 2 N.sqrt, (1:ℝ)/(k:ℝ)^2)+
        ((Icc 2 N.sqrt).card : ℝ)*(h+1) := by
    calc
      _ = ∑ k ∈ Icc 2 N.sqrt, (copRate h*N*((1:ℝ)/(k:ℝ)^2)+((h:ℝ)+1)) := by
        apply sum_congr rfl
        intro k hk
        ring
      _ = _ := by rw [sum_add_distrib, ← mul_sum]; simp; ring
  rw [he] at hsum
  have hcard : ((Icc 2 N.sqrt).card : ℝ) ≤ N.sqrt := by
    exact_mod_cast (show (Icc 2 N.sqrt).card ≤ N.sqrt by simp only [Nat.card_Icc]; omega)
  have hrec := mul_le_mul_of_nonneg_left (reciprocal_square_sum N.sqrt)
    (mul_nonneg (copRate_nonneg h) (Nat.cast_nonneg N))
  have hcard' := mul_le_mul_of_nonneg_right hcard (show (0:ℝ) ≤ h+1 by positivity)
  have hcountR : (copCount h N : ℝ) ≤ sfCount h N+1+
      ∑ k ∈ Icc 2 N.sqrt, ((B k).card : ℝ) := by exact_mod_cast hcount
  have hlo := (copCount_bounds hh N).1
  nlinarith

/-- A uniform quantitative loss for the coprimality constraint. -/
theorem lowerDensity_bound (h : ℕ) (hh : 0<h) :
    (h.totient : ℝ)/(4*h) ≤
      ({n : ℕ | Squarefree n ∧ h.Coprime n} : Set ℕ).lowerDensity := by
  let A : Set ℕ := {n : ℕ | Squarefree n ∧ h.Coprime n}
  have hvalue : (h.totient : ℝ)/(4*h)=copRate h/4 := by dsimp [copRate]; ring
  rw [hvalue]
  apply le_of_forall_lt_imp_le_of_dense
  intro c hc
  let ε := copRate h/4-c
  have hε : 0<ε := by dsimp [ε]; linarith
  obtain ⟨L,hL⟩ := exists_nat_gt (2*((h:ℝ)+1)/ε+1)
  have hL0 : 0<L := by
    have : (0:ℝ) ≤ 2*((h:ℝ)+1)/ε := by positivity
    exact_mod_cast (by linarith : (0:ℝ)<L)
  have hevent : ∀ᶠ N : ℕ in atTop, c ≤ A.partialDensity Set.univ N := by
    filter_upwards [eventually_ge_atTop (L^2)] with N hN
    have hsL : L ≤ N.sqrt := Nat.le_sqrt'.mpr hN
    have hs0 : 0<N.sqrt := lt_of_lt_of_le hL0 hsL
    have hN0 : 0<N := Nat.sqrt_pos.mp hs0
    have hsLr : (L:ℝ) ≤ N.sqrt := by exact_mod_cast hsL
    have hs1 : (1:ℝ) ≤ N.sqrt := by exact_mod_cast hs0
    have hs2 : (N.sqrt : ℝ)^2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
    have hlarge : 2*((h:ℝ)+1) < ε*(N.sqrt : ℝ) := by
      have hl := (div_lt_iff₀ hε).mp (show 2*((h:ℝ)+1)/ε < (N.sqrt:ℝ) by linarith)
      nlinarith
    have hmul := mul_le_mul_of_nonneg_left hs2 hε.le
    have hmul' := mul_lt_mul_of_pos_right hlarge (show (0:ℝ)<N.sqrt by exact_mod_cast hs0)
    have herror : ((h:ℝ)+1)*(N.sqrt+1) ≤ ε*N := by nlinarith
    have hcN : c*N ≤ sfCount h N := by
      have hh := sfCount_lower hh N
      dsimp [ε] at herror
      nlinarith
    have hcard : (A ∩ Set.Iio N).ncard=sfCount h N := by
      have heq : A ∩ Set.Iio N = ((range N).filter (fun n => Squarefree n ∧ h.Coprime n) : Finset ℕ) := by
        ext n
        simp [A,and_comm]
      rw [heq,Set.ncard_coe_finset]
      rfl
    simp only [Set.partialDensity,Set.inter_univ,Set.univ_inter,Nat.ncard_Iio,hcard]
    exact (le_div_iff₀ (by exact_mod_cast hN0 : (0:ℝ)<N)).mpr hcN
  exact le_liminf_of_le
    (isCoboundedUnder_ge_of_le atTop (fun N => Set.partialDensity_le_one A Set.univ N)) hevent

#print axioms lowerDensity_bound
end Erdos1206.SquarefreeCoprimeDensity
