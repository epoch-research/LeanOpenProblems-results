import Submission.TwoLinearSelberg

/-! A product-cutoff Selberg sieve retaining the density of an enforced
arithmetic progression. This is a finite unsigned upper bound. -/
namespace Erdos371.FiniteSieve
open Finset

lemma selbergMass_reciprocal_le_product {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hr : ∀ i ∈ S, 0 < (R i).card ∧ (R i).card < s i) (Z : ℝ) (hZ : 1 < Z)
    (hm : (∑ i ∈ S, Real.log (s i)*((R i).card : ℝ)/(s i)) ≤ Real.log Z/2) :
    1/selbergMass s R (productSieveFamily S s Z) ≤
      2*∏ i ∈ S, (1-((R i).card : ℝ)/(s i)) := by
  let G := selbergMass s R (productSieveFamily S s Z)
  let A := ∏ i ∈ S, (1-((R i).card : ℝ)/(s i))
  let W := ∏ i ∈ S, (1+((R i).card : ℝ)/((s i : ℝ)-(R i).card))
  have hG : 0 < G := selbergMass_pos s R _ (productSieveFamily_empty S s Z hZ.le)
    (fun T hT i hi => hr i (((mem_productSieveFamily S s Z T).mp hT).1 hi))
  have hs0 (i : ι) (hi : i ∈ S) : (0 : ℝ) < s i := by
    exact_mod_cast (lt_trans (hr i hi).1 (hr i hi).2)
  have hA : 0 ≤ A := by
    apply prod_nonneg
    intro i hi
    exact sub_nonneg.mpr ((div_le_one (hs0 i hi)).mpr (by exact_mod_cast (hr i hi).2.le))
  have hWA : W*A=1 := by
    dsimp only [W,A]
    rw [← prod_mul_distrib]
    apply prod_eq_one
    intro i hi
    have hp : (s i : ℝ)-(R i).card ≠ 0 := (sub_pos.mpr (by exact_mod_cast (hr i hi).2)).ne'
    have hq := (hs0 i hi).ne'
    field_simp
    ring
  have hlower : W/2 ≤ G := selbergMass_product_lower S s R hr Z hZ hm
  have hmul := mul_le_mul_of_nonneg_right hlower hA
  apply (div_le_iff₀ hG).mpr
  nlinarith

lemma residue_selberg_product_upper_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (s : ι → ℕ) (R : ι → Finset ℕ)
    (hs : ∀ i ∈ S, s i ≠ 0)
    (hc : (↑S : Set ι).Pairwise (Function.onFun Nat.Coprime s))
    (hR : ∀ i ∈ S, R i ⊆ range (s i))
    (hr : ∀ i ∈ S, 0 < (R i).card ∧ (R i).card < s i)
    (Z : ℝ) (hZ : 1 < Z)
    (hm : (∑ i ∈ S, Real.log (s i)*((R i).card : ℝ)/(s i)) ≤ Real.log Z/2) (N : ℕ) :
    (avoidanceCount (range N) (fun i n => n%s i ∈ R i) S : ℝ) ≤
      2*N*(∏ i ∈ S, (1-((R i).card : ℝ)/(s i)))+2*Z^4 := by
  have hb := quadratic_residue_sieve S s R hs hc hR hr (productSieveFamily S s Z)
    (fun T hT => ((mem_productSieveFamily S s Z T).mp hT).1)
    (productSieveFamily_empty S s Z hZ.le) Z (by linarith)
    (fun T hT => ((mem_productSieveFamily S s Z T).mp hT).2) N
  have he := mul_le_mul_of_nonneg_left (selbergMass_reciprocal_le_product S s R hr Z hZ hm)
    (Nat.cast_nonneg (α := ℝ) N)
  have he' : N/selbergMass s R (productSieveFamily S s Z) ≤
      2*N*(∏ i ∈ S, (1-((R i).card : ℝ)/(s i))) := by
    convert he using 1 <;> ring
  exact hb.trans (add_le_add he' le_rfl)

/-- Enforce one residue class modulo M and sieve at coprime moduli in S.
The factor 1/M is retained exactly, rather than replaced by exp(-1).
The local weighted logarithmic mass of S must fit inside log(Z)/2. -/
theorem residue_selberg_progression_bound (S : Finset ℕ) (R : ℕ → Finset ℕ)
    (M r N : ℕ) (hM : 0 < M) (hrM : r < M)
    (hMS : M ∉ S) (hcopM : ∀ p ∈ S, M.Coprime p)
    (hs : ∀ p ∈ S, p ≠ 0)
    (hc : (↑S : Set ℕ).Pairwise (Function.onFun Nat.Coprime id))
    (hR : ∀ p ∈ S, R p ⊆ range p)
    (hr : ∀ p ∈ S, 0 < (R p).card ∧ (R p).card < p)
    (Z : ℝ) (hZ : 1 < Z)
    (hm : (∑ p ∈ S, Real.log p*((R p).card : ℝ)/p) ≤ Real.log Z/2) :
    (((range N).filter (fun n => n%M=r ∧ ∀ p ∈ S, n%p ∉ R p)).card : ℝ) ≤
      2*N/M*Real.exp (-(∑ p ∈ S, ((R p).card : ℝ)/p))+
        2*(M : ℝ)^8*Z^4 := by
  classical
  have hprod : (∏ p ∈ S, (1-((R p).card : ℝ)/p)) ≤
      Real.exp (-(∑ p ∈ S, ((R p).card : ℝ)/p)) := by
    rw [← sum_neg_distrib,Real.exp_sum]
    apply prod_le_prod
    · intro p hp
      exact sub_nonneg.mpr ((div_le_one (by exact_mod_cast (Nat.pos_of_ne_zero (hs p hp)))).mpr
        (by exact_mod_cast (hr p hp).2.le))
    · intro p hp
      simpa only [neg_div,neg_add_eq_sub] using
        Real.add_one_le_exp (-((R p).card : ℝ)/(p : ℝ))
  by_cases hM1 : M = 1
  · subst M
    have hr0 : r = 0 := by omega
    subst r
    have hh := residue_selberg_upper_bound S id R hs hc hR hr Z hZ hm N
    convert hh using 1 <;> simp [avoidanceCount,Nat.mod_one]
    congr 1
    ext n
    simp
  have hM2 : 1 < M := by omega
  let T := insert M S
  let R' : ℕ → Finset ℕ := fun p => if p=M then (range M).erase r else R p
  have hrmem : r ∈ range M := mem_range.mpr hrM
  have hR'M : R' M = (range M).erase r := by simp [R']
  have hR'S (p : ℕ) (hp : p ∈ S) : R' p = R p := by
    have hne : p ≠ M := by intro he; subst p; exact hMS hp
    simp [R',hne]
  have hcard : (R' M).card=M-1 := by rw [hR'M,card_erase_of_mem hrmem,card_range]
  have hcardR : ((R' M).card : ℝ)=(M : ℝ)-1 := by rw [hcard]; exact_mod_cast Nat.cast_sub (by omega : 1 ≤ M)
  have hsT : ∀ p ∈ T, p ≠ 0 := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · omega
    · exact hs p hp
  have hcT : (↑T : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := by
    intro p hp q hq hpq
    have hpS : p=M ∨ p ∈ S := by simpa only [T,Finset.mem_coe,mem_insert] using hp
    have hqS : q=M ∨ q ∈ S := by simpa only [T,Finset.mem_coe,mem_insert] using hq
    rcases hpS with hpM | hpS
    · subst p
      exact hcopM q (hqS.resolve_left hpq.symm)
    · rcases hqS with hqM | hqS
      · subst q
        exact (hcopM p hpS).symm
      · exact hc hpS hqS hpq
  have hRT : ∀ p ∈ T, R' p ⊆ range p := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · rw [hR'M]
      exact erase_subset _ _
    · rw [hR'S p hp]
      exact hR p hp
  have hrT : ∀ p ∈ T, 0 < (R' p).card ∧ (R' p).card < p := by
    intro p hp
    rcases mem_insert.mp hp with rfl | hp
    · rw [hcard]
      omega
    · rw [hR'S p hp]
      exact hr p hp
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hMge : (1 : ℝ) ≤ M := by exact_mod_cast (by omega : 1 ≤ M)
  have hW : (1 : ℝ) < (M : ℝ)^2*Z := by
    have hh : (1 : ℝ) ≤ (M : ℝ)^2 := one_le_pow₀ hMge
    nlinarith
  have hmT : (∑ p ∈ T, Real.log p*((R' p).card : ℝ)/p) ≤
      Real.log ((M : ℝ)^2*Z)/2 := by
    rw [show T=insert M S from rfl,sum_insert hMS,hcardR]
    have hsumeq : (∑ p ∈ S, Real.log p*((R' p).card : ℝ)/p) =
        ∑ p ∈ S, Real.log p*((R p).card : ℝ)/p := by
      apply sum_congr rfl
      intro p hp
      rw [hR'S p hp]
    rw [hsumeq,Real.log_mul (by positivity) (by linarith : Z ≠ 0),Real.log_pow]
    have hterm : Real.log M*((M : ℝ)-1)/M ≤ Real.log M := by
      apply (div_le_iff₀ hMr).mpr
      have hh := Real.log_nonneg hMge
      nlinarith
    norm_num
    linarith
  have hh := residue_selberg_product_upper_bound T id R' hsT hcT hRT hrT
    ((M : ℝ)^2*Z) hW hmT N
  have hcount : avoidanceCount (range N) (fun p n => n%p ∈ R' p) T =
      ((range N).filter (fun n => n%M=r ∧ ∀ p ∈ S, n%p ∉ R p)).card := by
    unfold avoidanceCount
    congr 1
    ext n
    simp only [mem_filter]
    apply and_congr_right
    intro hn
    constructor
    · intro h
      have hnot := h M (mem_insert_self M S)
      rw [hR'M,mem_erase,mem_range] at hnot
      have heq : n%M=r := by have := Nat.mod_lt n hM; omega
      refine ⟨heq,?_⟩
      intro p hp
      simpa only [hR'S p hp] using h p (mem_insert_of_mem hp)
    · rintro ⟨heq,h⟩ p hp
      rcases mem_insert.mp hp with rfl | hp
      · rw [hR'M,heq]
        simp
      · rw [hR'S p hp]
        exact h p hp
  have hprodT : (∏ p ∈ T, (1-((R' p).card : ℝ)/p)) =
      (1/(M : ℝ))*(∏ p ∈ S, (1-((R p).card : ℝ)/p)) := by
    rw [show T=insert M S from rfl,prod_insert hMS,hcardR]
    have he : 1-((M : ℝ)-1)/M=1/M := by field_simp; ring
    rw [he]
    congr 1
    apply prod_congr rfl
    intro p hp
    rw [hR'S p hp]
  simp only [id_eq] at hh
  rw [hcount,hprodT,mul_pow,← pow_mul] at hh
  have he := mul_le_mul_of_nonneg_left hprod (show (0 : ℝ) ≤ 2*N/M by positivity)
  calc
    _ ≤ 2*N*((1/(M : ℝ))*(∏ p ∈ S, (1-((R p).card : ℝ)/p)))+
        2*((M : ℝ)^8*Z^4) := hh
    _ ≤ _ := by
      convert add_le_add_right he (2*(M : ℝ)^8*Z^4) using 1 <;> ring

#print axioms residue_selberg_progression_bound
end Erdos371.FiniteSieve
