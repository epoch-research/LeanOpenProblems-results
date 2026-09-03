import Submission.QuadraticUnitResidues
import Submission.QuadraticPrimeTail
import Submission.PositiveLocalProducts

/-! Summable forbidden prime sets do not exhaust locally admissible quadratic
parameter families. This is only an obstruction to prime-multiple avoidance. -/
namespace Erdos1206.QuadraticPrimeAvoidance
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticUnitResidues
  QuadraticPrimeTail PrimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

lemma product_lower {a b c : Fin 4 → ℤ}
    (hQ : ∀ i, Anisotropic (a i) (b i) (c i))
    (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    (hloc : ∀ p∈B, ∃ z : ZMod p × ZMod p,
      ∀ i, evalMod (a i) (b i) (c i) z ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ B →
      δ ≤ ∏p∈S, localDensity (units a b c) p := by
  let f : ℕ → ℝ := fun p => if p∈B then localDensity (units a b c) p else 1
  have hf (p : ℕ) : 0 < f p ∧ f p ≤ 1 := by
    by_cases hp : p∈B
    · exact ⟨by simpa [f,hp] using (density_bounds hQ (hB p hp) (hloc p hp)).1,
        by simpa [f,hp] using (density_bounds hQ (hB p hp) (hloc p hp)).2.1⟩
    · simp [f,hp]
  have hsum : Summable (fun p => 1-f p) := by
    apply Summable.of_nonneg_of_le (fun p => sub_nonneg.mpr (hf p).2) _
      (hs.mul_left (boundConstant a b c:ℝ))
    intro p
    by_cases hp : p∈B
    · simpa only [f,if_pos hp,mul_one_div] using
        (density_bounds hQ (hB p hp) (hloc p hp)).2.2
    · simp [f,hp]
  obtain ⟨δ,hδ,hprod⟩ := PositiveLocalProducts.uniform_product_lower f hf hsum
  refine ⟨δ,hδ,fun S hS => ?_⟩
  calc
    δ ≤ ∏p∈S,f p := hprod S
    _ = ∏p∈S,localDensity (units a b c) p := by
      apply prod_congr rfl
      intro p hp
      exact if_pos (hS hp)

lemma tail_mono {a b c : ℤ} {B : Set ℕ} {H K N : ℕ} (hHK : H ≤ K) :
    badTail a b c B K N ⊆ badTail a b c B H N := by
  intro x hx
  obtain ⟨hbox,hne,p,hp,hK,hdiv⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hbox,hne,p,hp,lt_of_le_of_lt hHK hK,hdiv⟩

/-- There is a positive first parameter avoiding every forbidden prime in
all four forms. Local admissibility is required at each forbidden prime. -/
theorem exists_avoiding {a b c : Fin 4 → ℤ}
    (hQ : ∀ i, Anisotropic (a i) (b i) (c i))
    (B : Set ℕ) (hB : ∀ p∈B, p.Prime)
    (hs : Summable (fun p : ℕ => if p∈B then (1:ℝ)/p else 0))
    (hloc : ∀ p∈B, ∃ z : ZMod p × ZMod p,
      ∀ i, evalMod (a i) (b i) (c i) z ≠ 0) :
    ∃ x y : ℕ, 0 < x ∧ ∀ i p, p∈B →
      ¬ (p:ℤ) ∣ form (a i) (b i) (c i) ((x:ℤ),(y:ℤ)) := by
  obtain ⟨δ,hδ,hprod⟩ := product_lower hQ B hB hs hloc
  have hε : 0 < δ/16 := by positivity
  choose H hH using fun i => uniform_prime_tail (hQ i) B hB hs hε
  let K := (univ : Finset (Fin 4)).sup H
  have htail (i : Fin 4) (N : ℕ) :
      ((badTail (a i) (b i) (c i) B K N).card:ℝ) ≤ δ/16*(N:ℝ)^2 := by
    exact (show ((badTail (a i) (b i) (c i) B K N).card:ℝ) ≤
      (badTail (a i) (b i) (c i) B (H i) N).card by
        exact_mod_cast card_le_card (tail_mono (le_sup (f := H) (mem_univ i)))).trans (hH i N)
  let S := (range (K+1)).filter (fun p => p∈B)
  have hSB : (↑S : Set ℕ) ⊆ B := by
    intro p hp
    exact (mem_filter.mp (show p∈S from hp)).2
  have hS : ∀ p∈S, p.Prime := fun p hp => hB p (hSB hp)
  let d : ℝ := ∏p∈S,(p:ℝ)
  have hd : 0 ≤ d := prod_nonneg (fun p _ => Nat.cast_nonneg p)
  obtain ⟨N,hN⟩ := exists_nat_gt ((4*(1+3*d))/δ+d+1)
  have hN0 : (0:ℝ) < N := lt_trans (by positivity) hN
  have hdN : d ≤ (N:ℝ) := by
    have hh : 0 ≤ 4*(1+3*d)/δ := by positivity
    linarith
  have hδN : 4*(1+3*d) < δ*(N:ℝ) := by
    have hh : 4*(1+3*d)/δ < (N:ℝ) := by linarith
    exact (div_lt_iff₀ hδ).mp hh |>.trans_eq (mul_comm _ _)
  let T := ((range N) ×ˢ (range N)).filter (fun x =>
    ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p)) ∈ units a b c p)
  have hcount : δ*(N:ℝ)^2 ≤ (T.card:ℝ)+3*(N:ℝ)*d := by
    have he := (abs_le.mp (joint_box_discrepancy S hS (units a b c) N)).1
    have hp := mul_le_mul_of_nonneg_left (hprod S hSB) (sq_nonneg (N:ℝ))
    have hd2 := mul_le_mul_of_nonneg_left hdN hd
    change -(2*(N:ℝ)*d+d^2) ≤ (T.card:ℝ)-(N:ℝ)^2*∏p∈S,localDensity (units a b c) p at he
    nlinarith only [he,hp,hd2]
  by_contra! hnone
  let lift : ℕ × ℕ → Vec := fun x => ((x.1:ℤ),(x.2:ℤ))
  have hinj : Function.Injective lift := by
    intro x y h
    apply Prod.ext
    · exact Int.ofNat.inj (congrArg Prod.fst h)
    · exact Int.ofNat.inj (congrArg Prod.snd h)
  let W (i : Fin 4) := badTail (a i) (b i) (c i) B K N
  let axis := ({(0:ℤ)} : Finset ℤ) ×ˢ ((range N).image (fun n : ℕ => (n:ℤ)))
  have hcover : T.image lift ⊆ axis ∪ univ.biUnion W := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    obtain ⟨hxbox,hxhead⟩ := mem_filter.mp hx
    obtain ⟨hx1,hx2⟩ := mem_product.mp hxbox
    by_cases hx0 : x.1=0
    · apply mem_union_left
      exact mem_product.mpr ⟨by simp [lift,hx0],mem_image.mpr ⟨x.2,hx2,rfl⟩⟩
    · obtain ⟨i,p,hp,hdiv⟩ := hnone x.1 x.2 (Nat.pos_of_ne_zero hx0)
      have hpK : K < p := by
        by_contra! hpK
        have hpS : p∈S := mem_filter.mpr ⟨mem_range.mpr (by omega),hp⟩
        have hu := (mem_units (hB p hp) _).mp (hxhead p hpS) i
        apply hu
        have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hdiv
        simpa only [evalMod,form,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast] using hz
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨i,mem_univ _,mem_filter.mpr ⟨?_,?_,p,hp,hpK,hdiv⟩⟩
      · apply mem_box_iff.mpr
        dsimp [ht,lift]
        rw [abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
        exact max_le (by exact_mod_cast (mem_range.mp hx1).le)
          (by exact_mod_cast (mem_range.mp hx2).le)
      · intro he
        have hzero := congrArg Prod.fst he
        apply hx0
        exact Int.ofNat.inj hzero
  have hc : T.card ≤ N+∑i,(W i).card := by
    calc
      T.card = (T.image lift).card := (card_image_of_injective _ hinj).symm
      _ ≤ (axis ∪ univ.biUnion W).card := card_le_card hcover
      _ ≤ axis.card+(univ.biUnion W).card := card_union_le _ _
      _ ≤ N+∑i,(W i).card := by
        apply Nat.add_le_add _ card_biUnion_le
        simp only [axis,card_product,card_singleton,one_mul]
        exact (card_image_le).trans_eq (card_range N)
  have hsum : (∑i,((W i).card:ℝ)) ≤ δ/4*(N:ℝ)^2 := by
    calc
      _ ≤ ∑i : Fin 4, δ/16*(N:ℝ)^2 := sum_le_sum (fun i _ => htail i N)
      _ = _ := by simp; ring
  have hcR : (T.card:ℝ) ≤ (N:ℝ)+∑i,((W i).card:ℝ) := by exact_mod_cast hc
  have hmul := mul_lt_mul_of_pos_right hδN hN0
  nlinarith only [hcount,hcR,hsum,hmul, mul_nonneg hδ.le (sq_nonneg (N:ℝ))]

#print axioms product_lower
#print axioms exists_avoiding
end Erdos1206.QuadraticPrimeAvoidance
