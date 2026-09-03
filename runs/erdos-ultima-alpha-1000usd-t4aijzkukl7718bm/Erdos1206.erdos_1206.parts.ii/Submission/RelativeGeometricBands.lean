import Submission.WeightedPathSelection
import Submission.Compactness

/-! Geometric-bin extraction inside an arbitrary positive-density source.
Unlike an intersection with one fixed periodic band set, this preserves
positive LOWER density without any invariance assumption on the source. -/
namespace Erdos1206.RelativeGeometricBands
open Finset WeightedPathSelection
open scoped Classical

noncomputable def bin (q : ℝ) (S : Set ℕ) (k : ℕ) : Finset ℕ :=
  (range ⌈q^(k+1)⌉₊).filter (fun n => 0 < n ∧ n∈S ∧ q^k  ≤  (n:ℝ))

lemma mem_bin (q : ℝ) (S : Set ℕ) (k n : ℕ) :
    n ∈ bin q S k ↔ 0 < n ∧ n∈S ∧ q^k  ≤  (n:ℝ) ∧ (n:ℝ)  <  q^(k+1) := by
  simp only [bin,mem_filter,mem_range,Nat.lt_ceil]
  tauto

lemma bin_disjoint {q : ℝ} (hq : 1 < q) (S : Set ℕ) {i j : ℕ} (hij : i≠j) :
    Disjoint (bin q S i) (bin q S j) := by
  apply disjoint_left.mpr
  intro n hn hm
  obtain ⟨_,_,hi₁,hi₂⟩ := (mem_bin _ _ _ _).mp hn
  obtain ⟨_,_,hj₁,hj₂⟩ := (mem_bin _ _ _ _).mp hm
  rcases lt_or_gt_of_ne hij with h | h
  · have hp := pow_le_pow_right₀ hq.le (show i+1  ≤  j by omega)
    linarith
  · have hp := pow_le_pow_right₀ hq.le (show j+1  ≤  i by omega)
    linarith

lemma sum_bin_card {q : ℝ} (hq : 1 < q) (S : Set ℕ) (J : Finset ℕ) :
    (∑ j ∈ J, (bin q S j).card) = (J.biUnion (bin q S)).card := by
  symm
  apply card_biUnion
  intro i _ j _ hij
  exact bin_disjoint hq S hij

lemma exists_bin_index {q : ℝ} (hq : 1 < q) :
    ∃ index : ℕ → ℕ, ∀ n, 0 < n → q^(index n)  ≤  (n:ℝ) ∧ (n:ℝ) < q^(index n+1) := by
  have hex (n : ℕ) : ∃ k : ℕ, q^k  ≤  max 1 (n:ℝ) ∧ max 1 (n:ℝ) < q^(k+1) :=
    exists_nat_pow_near (le_max_left _ _) hq
  choose index hi using hex
  refine ⟨index,fun n hn => ?_⟩
  have hnR : (1:ℝ)  ≤  n := by exact_mod_cast hn
  simpa only [max_eq_right hnR] using hi n

lemma bin_index_mono {q : ℝ} (hq : 1 < q) {index : ℕ → ℕ}
    (hi : ∀ n, 0 < n → q^(index n)  ≤  (n:ℝ) ∧ (n:ℝ) < q^(index n+1))
    {n m : ℕ} (hn : 0 < n) (hnm : n ≤ m) : index n  ≤  index m := by
  by_contra hh
  have hp := pow_le_pow_right₀ hq.le (show index m+1  ≤  index n by omega)
  have hnR : (n:ℝ)  ≤  m := by exact_mod_cast hnm
  have h₁ := hi n hn
  have h₂ := hi m (hn.trans_le hnm)
  linarith

lemma prefix_card_le_weight {q : ℝ} (hq : 1 < q) {S : Set ℕ}
    (hpos : ∀ n∈S, 0 < n) {index : ℕ → ℕ}
    (hi : ∀ n, 0 < n → q^(index n)  ≤  (n:ℝ) ∧ (n:ℝ) < q^(index n+1))
    (N : ℕ) :
    (S ∩ Set.Iio N).ncard  ≤  ∑ k ∈ range (index N+1), (bin q S k).card := by
  rw [sum_bin_card hq]
  have hsub : S ∩ Set.Iio N ⊆ ((range (index N+1)).biUnion (bin q S) : Set ℕ) := by
    intro n hn
    have hn0 := hpos n hn.1
    apply mem_biUnion.mpr
    refine ⟨index n,mem_range.mpr (by have := bin_index_mono hq hi hn0 hn.2.le; omega),?_⟩
    exact (mem_bin _ _ _ _).mpr ⟨hn0,hn.1,hi n hn0⟩
  simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub

lemma lowerDensity_pos_of_scaled_prefix {S T : Set ℕ} (hS : 0 < S.lowerDensity)
    {C D : ℕ} (hC : 0 < C) (hD : 0 < D)
    (hc : ∀ N, (S ∩ Set.Iio N).ncard  ≤  D*(T ∩ Set.Iio (C*N)).ncard) :
    0 < T.lowerDensity := by
  obtain ⟨δ,hδ,E,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  have hCR : (0:ℝ) < C := by exact_mod_cast hC
  have hDR : (0:ℝ) < D := by exact_mod_cast hD
  apply positive_lowerDensity_of_prefix_bound (δ := δ/((C:ℝ)*D))
    (C := ((C:ℝ)*E+δ*C)/((C:ℝ)*D)) (by positivity)
  intro M
  have hmono : (T ∩ Set.Iio (C*(M/C))).ncard  ≤  (T ∩ Set.Iio M).ncard :=
    Set.ncard_le_ncard (fun n hn => ⟨hn.1,hn.2.trans_le (Nat.mul_div_le M C)⟩)
  have hcount : ((S ∩ Set.Iio (M/C)).ncard:ℝ)  ≤  (D:ℝ)*(T ∩ Set.Iio M).ncard := by
    exact_mod_cast (hc (M/C)).trans (Nat.mul_le_mul_left D hmono)
  have hfloor : (M:ℝ)  ≤  (C:ℝ)*((M/C:ℕ):ℝ)+C := by
    exact_mod_cast (Nat.lt_mul_div_succ M hC).le
  have h₁ := mul_le_mul_of_nonneg_left (hpre (M/C)) hCR.le
  have h₂ := mul_le_mul_of_nonneg_left hcount hCR.le
  have h₃ := mul_le_mul_of_nonneg_left hfloor hδ.le
  have hh : δ*M  ≤  ((C:ℝ)*D)*(T ∩ Set.Iio M).ncard+((C:ℝ)*E+δ*C) := by
    nlinarith only [h₁,h₂,h₃]
  calc
    _ = δ*M/((C:ℝ)*D) := by ring
    _  ≤  (((C:ℝ)*D)*(T ∩ Set.Iio M).ncard+((C:ℝ)*E+δ*C))/((C:ℝ)*D) :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

/-- A positive-density subset of any positive-density source can be confined
to geometrically separated bins. The quantitative loss is finite and depends
only on the bin width and separation radius, not on the source. -/
theorem exists_positive_bin_subset {q : ℝ} (hq : 1 < q) (R : ℕ) {S : Set ℕ}
    (hS : 0 < S.lowerDensity) (hpos : ∀ n∈S, 0 < n) :
    ∃ T : Set ℕ, T ⊆ S ∧ 0 < T.lowerDensity ∧
      ∃ I : Set ℕ, Separated R I ∧ ∀ n∈T, ∃ k∈I, n∈bin q S k := by
  obtain ⟨index,hi⟩ := exists_bin_index hq
  let w : ℕ → ℕ := fun k => (bin q S k).card
  obtain ⟨I,hI,hdom⟩ := exists_selection R w
  let T : Set ℕ := {n | ∃ k∈I, n∈bin q S k}
  have hTS : T ⊆ S := by
    rintro n ⟨k,hk,hn⟩
    exact ((mem_bin _ _ _ _).mp hn).2.1
  let C : ℕ := ⌈q^(R+1)⌉₊
  have hC : 0 < C := Nat.ceil_pos.mpr (pow_pos (by linarith) _)
  have hcount (N : ℕ) :
      (S ∩ Set.Iio N).ncard  ≤  (2*R+1)*(T ∩ Set.Iio (C*N)).ncard := by
    by_cases hn : N=0
    · subst N
      simp
    have hN : 0 < N := Nat.pos_of_ne_zero hn
    have hwi : (∑ j ∈ range (index N+R+1), if j∈I then w j else 0)  ≤ 
        (T ∩ Set.Iio (C*N)).ncard := by
      rw [←sum_filter]
      change (∑ j ∈ (range (index N+R+1)).filter (fun j => j∈I), (bin q S j).card)  ≤  _
      rw [sum_bin_card hq]
      rw [←Set.ncard_coe_finset]
      refine Set.ncard_le_ncard ?_ ((Set.finite_Iio _).subset Set.inter_subset_right)

      intro n hn
      obtain ⟨j,hj,hnj⟩ := mem_biUnion.mp hn
      have hj' := mem_filter.mp hj
      obtain ⟨_,_,_,hnup⟩ := (mem_bin _ _ _ _).mp hnj
      refine ⟨⟨j,hj'.2,hnj⟩,?_⟩
      have hjN : j+1  ≤  index N+R+1 := mem_range.mp hj'.1
      have hp := pow_le_pow_right₀ hq.le hjN
      have hcR : q^(R+1)  ≤  (C:ℝ) := Nat.le_ceil _
      have hb : q^(index N+R+1)  ≤  (C:ℝ)*N := by
        calc
          _ = q^(index N)*q^(R+1) := by rw [←pow_add]; congr 1
          _  ≤  (N:ℝ)*C := mul_le_mul (hi N hN).1 hcR (by positivity) (Nat.cast_nonneg N)
          _ = _ := by ring
      have hnR : (n:ℝ) < (C:ℝ)*N := hnup.trans_le (hp.trans hb)
      exact_mod_cast hnR
    calc
      _  ≤  ∑ k ∈ range (index N+1), w k := prefix_card_le_weight hq hpos hi N
      _  ≤  (2*R+1)*∑ j ∈ range (index N+R+1), if j∈I then w j else 0 := prefix_domination hdom _
      _  ≤  _ := Nat.mul_le_mul_left _ hwi
  exact ⟨T,hTS,lowerDensity_pos_of_scaled_prefix hS hC (by omega) hcount,I,hI,fun _ hn => hn⟩

/-- Avoiding a fixed compact interval of nontrivial real ratios preserves
positive lower density inside any source of positive integers. -/
theorem exists_ratio_separated_subset {q B : ℝ} (hq : 1 < q) (hB : 1 ≤ B)
    {S : Set ℕ} (hS : 0 < S.lowerDensity) (hpos : ∀ n∈S, 0 < n) :
    ∃ T : Set ℕ, T ⊆ S ∧ 0 < T.lowerDensity ∧
      ∀ x∈T, ∀ y∈T, x ≤ y → (y:ℝ) ≤ B*x → (y:ℝ) < q*x := by
  obtain ⟨r,_,hr⟩ := exists_nat_pow_near hB hq
  let R := r+1
  have hR : B < q^R := hr
  obtain ⟨T,hTS,hTd,I,hI,hbins⟩ := exists_positive_bin_subset hq R hS hpos
  refine ⟨T,hTS,hTd,?_⟩
  intro x hx y hy hxy hyB
  obtain ⟨i,hi,hxi⟩ := hbins x hx
  obtain ⟨j,hj,hyj⟩ := hbins y hy
  obtain ⟨_,_,hxlo,hxup⟩ := (mem_bin _ _ _ _).mp hxi
  obtain ⟨_,_,hylo,hyup⟩ := (mem_bin _ _ _ _).mp hyj
  have hq0 : 0 < q := by linarith
  have hxyR : (x:ℝ) ≤ y := by exact_mod_cast hxy
  have hij : i ≤ j := by
    by_contra hh
    have hp := pow_le_pow_right₀ hq.le (show j+1 ≤ i by omega)
    linarith
  have hjR : j ≤ i+R := by
    by_contra hh
    have hp := pow_le_pow_right₀ hq.le (show i+R+1 ≤ j by omega)
    have hxB := mul_lt_mul_of_pos_left hxup (show 0 < B by linarith)
    have hBR := mul_lt_mul_of_pos_right hR (pow_pos hq0 (i+1))
    have he : q^R*q^(i+1)=q^(i+R+1) := by rw [←pow_add]; congr 1; omega
    rw [he] at hBR
    linarith
  have heq := hI i hi j hj (by omega) hjR
  rw [←heq] at hyup
  calc
    (y:ℝ) < q^(i+1) := hyup
    _ = q*q^i := by rw [pow_succ]; ring
    _  ≤  q*x := mul_le_mul_of_nonneg_left hxlo hq0.le

#print axioms exists_positive_bin_subset
#print axioms exists_ratio_separated_subset
end Erdos1206.RelativeGeometricBands
