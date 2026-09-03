import Submission.CarryExplore

/-! A plane-group sum gives at most four ordinary integer sums under the
standard two-digit radix encoding. Includes natural translations. -/
namespace Erdos66RadixPlaneSumSupport
open AdditiveCombinatorics Erdos66Carry
open scoped Classical
set_option maxHeartbeats 1800000

variable (m : ℕ) [NeZero m]

lemma value_carry (x y : ZMod m) :
    ∃ c : Fin 2, x.val+y.val = (x+y).val+m*c.val := by
  by_cases h : m ≤ x.val+y.val
  · refine ⟨⟨1,by decide⟩,?_⟩
    simpa only [mul_one] using ZMod.val_add_val_of_le h
  · refine ⟨⟨0,by decide⟩,?_⟩
    simp only [mul_zero,add_zero,ZMod.val_add_of_lt (by omega : x.val+y.val < m)]

lemma plane_carries (x y : ZMod m × ZMod m) :
    ∃ c : Fin 2 × Fin 2,
      digitEncode m x+digitEncode m y = digitEncode m (x+y)+m*c.1.val+m^2*c.2.val := by
  obtain ⟨a,ha⟩ := value_carry m x.1 y.1
  obtain ⟨b,hb⟩ := value_carry m x.2 y.2
  refine ⟨(a,b),?_⟩
  dsimp [digitEncode]
  nlinarith

/-- Every represented integer sum from a graph indexed by `S` lies in a
set of at most four times as many values as its plane-group sum support. -/
lemma lifted_sum_support_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ZMod m × ZMod m) (T : Finset (ZMod m × ZMod m))
    (hT : ∀ x ∈ S, ∀ y ∈ S, f x+f y ∈ T) (a : ℕ) :
    ((S.product S).image (fun p ↦ (a+digitEncode m (f p.1))+(a+digitEncode m (f p.2)))).card ≤ 4*T.card := by
  let Q := (T.product (Finset.univ : Finset (Fin 2 × Fin 2))).image
    (fun p ↦ 2*a+digitEncode m p.1+m*p.2.1.val+m^2*p.2.2.val)
  have hsub : (S.product S).image (fun p ↦ (a+digitEncode m (f p.1))+(a+digitEncode m (f p.2))) ⊆ Q := by
    intro n hn
    obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
    obtain ⟨c,hc⟩ := plane_carries m (f x) (f y)
    apply Finset.mem_image.mpr
    refine ⟨(f x+f y,c),Finset.mem_product.mpr ⟨hT x hx y hy,Finset.mem_univ _⟩,?_⟩
    dsimp only
    omega
  have hc := (Finset.card_le_card hsub).trans (Finset.card_image_le (s := T.product Finset.univ))
  simpa only [Finset.product_eq_sprod,Finset.card_product,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
    show 2*2=4 by decide,Nat.mul_comm] using hc

/-- General mass-versus-support estimate, applied directly to the input
pairs. Injectivity is needed only for their actual natural encodings. -/
lemma encoded_pair_mass_bound {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℕ) (hf : Set.InjOn f (S : Set ι)) (A : Set ℕ)
    (hA : ∀ x ∈ S, f x ∈ A) (V : ℝ) (hV : 0 ≤ V)
    (hcap : ∀ x ∈ S, ∀ y ∈ S, (sumRep A (f x+f y) : ℝ) ≤ V)
    (L : ℕ) (hL : ((S.product S).image (fun p ↦ f p.1+f p.2)).card ≤ L) :
    (S.card : ℝ)^2 ≤ L*V := by
  let σ : ι × ι → ℕ := fun p ↦ f p.1+f p.2
  let T := (S.product S).image σ
  have hfiber (n : ℕ) : (((S.product S).filter (fun p ↦ σ p=n)).card : ℝ) ≤ sumRep A n := by
    have hh : ((S.product S).filter (fun p ↦ σ p=n)).card ≤ sumRep A n := by
      rw [sumRep_def]
      apply Finset.card_le_card_of_injOn (fun p : ι × ι ↦ (f p.1,f p.2))
      · intro p hp
        change p ∈ (S.product S).filter (fun p ↦ σ p=n) at hp
        obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
        obtain ⟨hx,hy⟩ := Finset.mem_product.mp hp
        change (f p.1,f p.2) ∈ (Finset.antidiagonal n).filter (fun z ↦ z.1 ∈ A ∧ z.2 ∈ A)
        exact Finset.mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr he,hA _ hx,hA _ hy⟩
      · intro p hp r hr he
        have hp' := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
        have hr' := Finset.mem_product.mp (Finset.mem_filter.mp hr).1
        exact Prod.ext (hf hp'.1 hr'.1 (congrArg Prod.fst he)) (hf hp'.2 hr'.2 (congrArg Prod.snd he))
    exact_mod_cast hh
  have hmass : (S.card : ℝ)^2 = ∑ n ∈ T, (((S.product S).filter (fun p ↦ σ p=n)).card : ℝ) := by
    have hh := Finset.card_eq_sum_card_image σ (S.product S)
    simp only [Finset.product_eq_sprod,Finset.card_product] at hh
    have hh' : (S.card : ℝ)*S.card = ∑ n ∈ T, (((S.product S).filter (fun p ↦ σ p=n)).card : ℝ) := by
      exact_mod_cast hh
    simpa only [pow_two] using hh'
  rw [hmass]
  calc
    _ ≤ ∑ _n ∈ T, V := by
      apply Finset.sum_le_sum
      intro n hn
      obtain ⟨⟨x,y⟩,hxy,rfl⟩ := Finset.mem_image.mp hn
      obtain ⟨hx,hy⟩ := Finset.mem_product.mp hxy
      exact (hfiber _).trans (hcap x hx y hy)
    _ = (T.card : ℝ)*V := by simp only [Finset.sum_const,nsmul_eq_mul]
    _ ≤ L*V := mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hV

end Erdos66RadixPlaneSumSupport
