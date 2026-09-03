import Submission.Compactness

/-! Any positive-lower-density source has a positive-lower-density subset
avoiding a fixed bounded set of nontrivial rational ratios. -/
namespace Erdos1206.FiniteRatioSource
open Finset
open scoped Classical

def Separated (H : ℕ) (A : Set ℕ) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ a ∈ Set.Icc 1 H, ∀ b ∈ Set.Icc 1 H,
    a*x=b*y → x=y

lemma exists_maximal_separated (H : ℕ) (S : Set ℕ) :
    ∃ A : Set ℕ, Maximal (fun A => A ⊆ S ∧ Separated H A) A := by
  apply zorn_subset {A : Set ℕ | A ⊆ S ∧ Separated H A}
  intro C hC hchain
  refine ⟨⋃₀ C,⟨?_,?_⟩,fun B hB => Set.subset_sUnion_of_mem hB⟩
  · rintro x ⟨B,hB,hx⟩
    exact (hC hB).1 hx
  · rintro x ⟨B,hB,hx⟩ y ⟨D,hD,hy⟩ a ha b hb he
    rcases hchain.total hB hD with hBD | hDB
    · exact (hC hD).2 x (hBD hx) y hy a ha b hb he
    · exact (hC hB).2 x hx y (hDB hy) a ha b hb he

lemma maximal_dominates {H : ℕ} (hH : 0 < H) {S A : Set ℕ}
    (hA : Maximal (fun A => A ⊆ S ∧ Separated H A) A) :
    ∀ n ∈ S, ∃ a ∈ Set.Icc 1 H, ∃ b ∈ Set.Icc 1 H, ∃ v ∈ A, a*n=b*v := by
  intro n hn
  by_cases hna : n ∈ A
  · exact ⟨1,⟨le_rfl,hH⟩,1,⟨le_rfl,hH⟩,n,hna,rfl⟩
  by_contra hnot
  have hsep : Separated H (insert n A) := by
    intro x hx y hy a ha b hb he
    rcases Set.mem_insert_iff.mp hx with hxE | hxA <;>
      rcases Set.mem_insert_iff.mp hy with hyE | hyA
    · exact hxE.trans hyE.symm
    · rw [hxE] at he
      exact (hnot ⟨a,ha,b,hb,y,hyA,he⟩).elim
    · rw [hyE] at he
      exact (hnot ⟨b,hb,a,ha,x,hxA,he.symm⟩).elim
    · exact hA.1.2 x hxA y hyA a ha b hb he
  have hsub : insert n A ⊆ S := Set.insert_subset hn hA.1.1
  exact hna ((hA.2 ⟨hsub,hsep⟩ (Set.subset_insert _ _)) (Set.mem_insert n A))

lemma positive_density_of_ratio_domination {H : ℕ} (hH : 0 < H) {S A : Set ℕ}
    (hS : 0 < S.lowerDensity)
    (hcover : ∀ n ∈ S, ∃ a ∈ Set.Icc 1 H, ∃ b ∈ Set.Icc 1 H, ∃ v ∈ A, a*n=b*v) :
    0 < A.lowerDensity := by
  have hex (n : ℕ) : ∃ a b v : ℕ, a ∈ Set.Icc 1 H ∧ b ∈ Set.Icc 1 H ∧
      (n ∈ S → v ∈ A ∧ a*n=b*v) := by
    by_cases hn : n ∈ S
    · obtain ⟨a,ha,b,hb,v,hv,he⟩ := hcover n hn
      exact ⟨a,b,v,ha,hb,fun _ => ⟨hv,he⟩⟩
    · exact ⟨1,1,0,⟨le_rfl,hH⟩,⟨le_rfl,hH⟩,fun hh => (hn hh).elim⟩
  choose a b v ha hb hv using hex
  have hcount (M : ℕ) : (S ∩ Set.Iio (M/H)).ncard ≤ H*H*(A ∩ Set.Iio M).ncard := by
    let f : ℕ → ℕ × ℕ × ℕ := fun n => (a n,b n,v n)
    have hmap : ∀ n ∈ S ∩ Set.Iio (M/H),
        f n ∈ Set.Icc 1 H ×ˢ Set.Icc 1 H ×ˢ (A ∩ Set.Iio M) := by
      intro n hn
      have hnS := hn.1
      have hnM : n < M/H := hn.2
      obtain ⟨hnv,he⟩ := hv n hnS
      refine ⟨ha n,hb n,hnv,?_⟩
      have hvle : v n ≤ b n*v n := by nlinarith [(hb n).1]
      have hvH : v n ≤ H*n := hvle.trans (he ▸ Nat.mul_le_mul_right n (ha n).2)
      have hlt := Nat.mul_lt_mul_of_pos_left hnM hH
      exact hvH.trans_lt (hlt.trans_le (Nat.mul_div_le M H))
    have hinj : Set.InjOn f (S ∩ Set.Iio (M/H)) := by
      intro n hn m hm he
      have hea : a n=a m := congrArg Prod.fst he
      have heb : b n=b m := congrArg (fun z : ℕ × ℕ × ℕ => z.2.1) he
      have hev : v n=v m := congrArg (fun z : ℕ × ℕ × ℕ => z.2.2) he
      have h₁ := (hv n hn.1).2
      have h₂ := (hv m hm.1).2
      rw [←hea,←heb,←hev] at h₂
      exact Nat.eq_of_mul_eq_mul_left (ha n).1 (h₁.trans h₂.symm)
    have hc := Set.ncard_le_ncard_of_injOn f hmap hinj
    have hI : (Set.Icc 1 H).ncard=H := by
      rw [←Finset.coe_Icc,Set.ncard_coe_finset,Nat.card_Icc]
      omega
    simpa only [Set.ncard_prod,hI,mul_assoc] using hc
  obtain ⟨δ,hδ,C,hpre⟩ := prefix_bound_of_positive_lowerDensity hS
  have hHR : (0:ℝ) < H := by exact_mod_cast hH
  apply positive_lowerDensity_of_prefix_bound (δ := δ/(H:ℝ)^3)
    (C := ((H:ℝ)*C+δ*H)/(H:ℝ)^3) (by positivity)
  intro M
  have hc : ((S ∩ Set.Iio (M/H)).ncard:ℝ) ≤ (H:ℝ)*H*(A ∩ Set.Iio M).ncard := by
    exact_mod_cast hcount M
  have hd : (M:ℝ) ≤ (H:ℝ)*((M/H:ℕ):ℝ)+H := by
    have hh := (Nat.lt_mul_div_succ M hH).le
    exact_mod_cast hh
  have h₁ := mul_le_mul_of_nonneg_left (hpre (M/H)) hHR.le
  have h₂ := mul_le_mul_of_nonneg_left hc hHR.le
  have h₃ := mul_le_mul_of_nonneg_left hd hδ.le
  have hh : δ*M ≤ (H:ℝ)^3*(A ∩ Set.Iio M).ncard+((H:ℝ)*C+δ*H) := by
    nlinarith only [h₁,h₂,h₃]
  calc
    _ = δ*M/(H:ℝ)^3 := by ring
    _ ≤ ((H:ℝ)^3*(A ∩ Set.Iio M).ncard+((H:ℝ)*C+δ*H))/(H:ℝ)^3 :=
      div_le_div_of_nonneg_right hh (by positivity)
    _ = _ := by field_simp

/-- Finite ratio exclusions preserve positive LOWER density inside an arbitrary
source; no multiplicative invariance of the source is assumed. -/
theorem exists_positive_separated {S : Set ℕ} (hS : 0 < S.lowerDensity) {H : ℕ} (hH : 0 < H) :
    ∃ A : Set ℕ, A ⊆ S ∧ 0 < A.lowerDensity ∧ Separated H A := by
  obtain ⟨A,hA⟩ := exists_maximal_separated H S
  exact ⟨A,hA.1.1,positive_density_of_ratio_domination hH hS (maximal_dominates hH hA),hA.1.2⟩

lemma Separated.not_dilate_pair {H : ℕ} {A : Set ℕ} (hA : Separated H A)
    {a b k : ℕ} (ha : 0 < a) (haH : a ≤ H) (hb : 0 < b) (hbH : b ≤ H)
    (hab : a ≠ b) (hk : 0 < k) : ¬ (k*a ∈ A ∧ k*b ∈ A) := by
  rintro ⟨hka,hkb⟩
  have hh := hA (k*a) hka (k*b) hkb b ⟨hb,hbH⟩ a ⟨ha,haH⟩ (by ring)
  exact hab (Nat.eq_of_mul_eq_mul_left hk hh)

#print axioms exists_maximal_separated
#print axioms positive_density_of_ratio_domination
#print axioms exists_positive_separated
end Erdos1206.FiniteRatioSource
