import Submission.ApproximateFisher
import Submission.PureCommonMoments

/-! A robust obstruction to almost zero-or-three common-neighbor models.
This is a necessary condition, not a solution of the balanced Zarankiewicz problem. -/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 6000000
namespace Erdos714RobustPureFour
open Erdos714Packing
variable {B V : Type*} [Fintype B] [Fintype V]

def count (S : B → Finset V) (T : Finset V) : ℕ := (blocksContaining S T).card

def tupleCommon (S : B → Finset V) {I : Type*} [Fintype I] (f : I → V) : Finset B :=
  univ.filter (fun b => ∀ i, f i ∈ S b)

omit [Fintype V] in
@[simp] lemma mem_tupleCommon (S : B → Finset V) {I : Type*} [Fintype I]
    (f : I → V) (b : B) : b ∈ tupleCommon S f ↔ ∀ i, f i ∈ S b := by
  simp [tupleCommon]

lemma tupleCommon_eq (S : B → Finset V) {I : Type*} [Fintype I] (f : I → V) :
    tupleCommon S f = blocksContaining S (univ.image f) := by
  ext b
  simp only [mem_tupleCommon,mem_blocksContaining]
  constructor
  · intro h v hv
    obtain ⟨i,_,rfl⟩ := mem_image.mp hv
    exact h i
  · intro h i
    exact h (mem_image.mpr ⟨i,mem_univ _,rfl⟩)

/-- Rectangles with repetitions on one side and no repetitions on the other. -/
def mixedRectangleEquiv (S : B → Finset V) (k t : ℕ) :
    (Σ f : Fin k → V, Fin t ↪ tupleCommon S f) ≃
      (Σ g : Fin t ↪ B, Fin k → common S g) where
  toFun p :=
    ⟨⟨fun j => (p.2 j).val, fun i j h => p.2.injective (Subtype.ext h)⟩,
      fun i => ⟨p.1 i, by
        rw [mem_common]
        intro j
        exact (mem_tupleCommon S p.1 _).mp (p.2 j).property i⟩⟩
  invFun p :=
    ⟨fun i => (p.2 i).val,
      ⟨fun j => ⟨p.1 j, by
        rw [mem_tupleCommon]
        intro i
        exact (mem_common S p.1 _).mp (p.2 i).property j⟩,
       fun i j h => p.1.injective (congrArg Subtype.val h)⟩⟩
  left_inv p := by rcases p with ⟨f,g⟩; rfl
  right_inv p := by rcases p with ⟨f,g⟩; rfl

lemma mixed_rectangle_count (S : B → Finset V) (k t : ℕ) :
    (∑ f : Fin k → V, (tupleCommon S f).card.descFactorial t) =
      ∑ g : Fin t ↪ B, (common S g).card^k := by
  have h := Fintype.card_congr (mixedRectangleEquiv S k t)
  simpa only [Fintype.card_sigma,Fintype.card_embedding_eq,Fintype.card_fin,
    Fintype.card_fun,Fintype.card_coe] using h

lemma sum_tuple_succ {M : Type*} [AddCommMonoid M] (n : ℕ)
    (f : (Fin (n+1) → V) → M) :
    (∑ t, f t) = ∑ a, ∑ t : Fin n → V, f (Fin.cons a t) := by
  have h := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (n+1) => V))
    (fun p => f (Fin.cons p.1 p.2)) f (fun _ => rfl)
  simpa only [Fintype.sum_prod_type] using h.symm

lemma sum_tuple_three {M : Type*} [AddCommMonoid M]
    (f : (Fin 3 → V) → M) :
    (∑ t, f t) = ∑ a, ∑ b, ∑ c, f ![a,b,c] := by
  rw [sum_tuple_succ]
  apply sum_congr rfl
  intro a _
  rw [sum_tuple_succ]
  apply sum_congr rfl
  intro b _
  rw [sum_tuple_succ]
  apply sum_congr rfl
  intro c _
  simp only [Fintype.sum_unique]
  congr 1

lemma tupleCommon_three (S : B → Finset V) (a b c : V) :
    (tupleCommon S ![a,b,c]).card = count S {a,b,c} := by
  unfold count
  congr 1
  ext d
  simp [mem_tupleCommon,mem_blocksContaining,Fin.forall_fin_succ,insert_subset_iff]

lemma triple_fourth_factorial (S : B → Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ a, ∑ b, ∑ c, (count S {a,b,c}).descFactorial 4) ≤
      27*(Fintype.card B)^4 := by
  have h := mixed_rectangle_count S 3 4
  rw [sum_tuple_three] at h
  simp_rw [tupleCommon_three] at h
  rw [h]
  calc
    _ ≤ ∑ _g : Fin 4 ↪ B, 27 := by
      apply sum_le_sum
      intro g _
      have hg := (free_iff_common_card S (by decide : 0 < 4)).mp hfree g
      have hh := Nat.pow_le_pow_left (show (common S g).card ≤ 3 by omega) 3
      exact hh
    _ = 27*(Fintype.card B).descFactorial 4 := by simp [Nat.mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)

lemma cubic_fourth_moment {I : Type*} [Fintype I] (a : I → ℕ) :
    (∑ i, a i^3)^4 ≤ Fintype.card I*(∑ i, a i^4)^3 := by
  have h1 := sum_mul_sq_le_sq_mul_sq (univ : Finset I) a (fun i => a i^2)
  have h2 := sum_mul_sq_le_sq_mul_sq (univ : Finset I) (fun _ => (1 : ℕ))
    (fun i => a i^2)
  have he (i : I) : a i*(a i)^2 = a i^3 := by ring
  have he' (i : I) : ((a i)^2)^2 = a i^4 := by ring
  simp only [he,he',one_mul,one_pow,sum_const,card_univ,smul_eq_mul,mul_one] at h1 h2
  calc
    _ = ((∑ i, a i^3)^2)^2 := by ring
    _ ≤ ((∑ i, a i^2)*(∑ i, a i^4))^2 := Nat.pow_le_pow_left h1 2
    _ = (∑ i, a i^2)^2*(∑ i, a i^4)^2 := by ring
    _ ≤ (Fintype.card I*(∑ i, a i^4))*(∑ i, a i^4)^2 := Nat.mul_le_mul_right _ h2
    _ = _ := by ring

def thirdMoment (S : B → Finset V) : ℕ := ∑ a, ∑ b, ∑ c, count S {a,b,c}^3

/-- No pointwise degree or codegree hypothesis is used. -/
theorem third_moment_bound (S : B → Finset V) (q : ℕ) (hq : 1 ≤ q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    thirdMoment S ≤ 216*q^15 := by
  let a : (V × V × V) → ℕ := fun p => count S {p.1,p.2.1,p.2.2}-3
  have hn : Fintype.card (V × V × V) ≤ q^12 := by
    simp only [Fintype.card_prod]
    calc
      _ ≤ (q^4)*((q^4)*(q^4)) := Nat.mul_le_mul hV (Nat.mul_le_mul hV hV)
      _ = _ := by ring
  have hfour : (∑ p, a p^4) ≤ 27*q^16 := by
    have hf := triple_fourth_factorial S hfree
    calc
      _ ≤ ∑ p : V × V × V, (count S {p.1,p.2.1,p.2.2}).descFactorial 4 := by
        apply sum_le_sum
        intro p _
        simpa only [a,show 4-1=3 from rfl] using
          Nat.pow_sub_le_descFactorial (count S {p.1,p.2.1,p.2.2}) 4
      _ ≤ 27*(Fintype.card B)^4 := by simpa only [Fintype.sum_prod_type] using hf
      _ ≤ 27*(q^4)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hB 4)
      _ = _ := by ring
  have hc : (∑ p, a p^3) ≤ 27*q^15 := by
    apply (Nat.pow_le_pow_iff_left (by decide : 4 ≠ 0)).mp
    calc
      _ ≤ Fintype.card (V × V × V)*(∑ p, a p^4)^3 := cubic_fourth_moment a
      _ ≤ q^12*(27*q^16)^3 := Nat.mul_le_mul hn (Nat.pow_le_pow_left hfour 3)
      _ ≤ (27*q^15)^4 := by ring_nf; omega
  have hd (p : V × V × V) : count S {p.1,p.2.1,p.2.2}^3 ≤ 4*a p^3+108 := by
    have hh : count S {p.1,p.2.1,p.2.2} ≤ a p+3 := by dsimp [a]; omega
    have ha := add_pow_le (Nat.zero_le (a p)) (Nat.zero_le 3) 3
    calc
      _ ≤ (a p+3)^3 := Nat.pow_le_pow_left hh 3
      _ ≤ _ := by norm_num at ha; nlinarith
  calc
    thirdMoment S = ∑ p : V × V × V, count S {p.1,p.2.1,p.2.2}^3 := by
      simp only [thirdMoment,Fintype.sum_prod_type]
    _ ≤ ∑ p, (4*a p^3+108) := sum_le_sum (fun p _ => hd p)
    _ = 4*(∑ p, a p^3)+108*Fintype.card (V × V × V) := by
      simp [sum_add_distrib,← mul_sum,Nat.mul_comm]
    _ ≤ 4*(27*q^15)+108*q^12 := Nat.add_le_add (Nat.mul_le_mul_left _ hc)
      (Nat.mul_le_mul_left _ hn)
    _ ≤ 216*q^15 := by
      have hp : q^12 ≤ q^15 := pow_le_pow_right' hq (by decide)
      omega

/-- A union bound over the six possible equality pairs in a four-tuple.
The weight depends only on the set of entries. -/
lemma repeated_four_bound (F : Finset V → ℝ) (hF : ∀ T, 0 ≤ F T) :
    (∑ a, ∑ b, ∑ c, ∑ d,
      if ({a,b,c,d} : Finset V).card < 4 then F {a,b,c,d} else 0) ≤
      6*∑ a, ∑ b, ∑ c, F {a,b,c} := by
  have hpoint (a b c d : V) :
      (if ({a,b,c,d} : Finset V).card < 4 then F {a,b,c,d} else 0) ≤
      (if a=b then F {a,b,c,d} else 0) +
      (if a=c then F {a,b,c,d} else 0) +
      (if a=d then F {a,b,c,d} else 0) +
      (if b=c then F {a,b,c,d} else 0) +
      (if b=d then F {a,b,c,d} else 0) +
      (if c=d then F {a,b,c,d} else 0) := by
    have he : ({a,b,c,d} : Finset V).card < 4 →
        a=b ∨ a=c ∨ a=d ∨ b=c ∨ b=d ∨ c=d := by
      intro hc
      by_contra hn
      push_neg at hn
      have ha : a ∉ ({b,c,d} : Finset V) := by simp [hn.1,hn.2.1,hn.2.2.1]
      have hb : b ∉ ({c,d} : Finset V) := by simp [hn.2.2.2.1,hn.2.2.2.2.1]
      have hc' : c ∉ ({d} : Finset V) := by simp [hn.2.2.2.2.2]
      simp [card_insert_of_notMem,ha,hb,hc'] at hc
    have hnon := hF {a,b,c,d}
    split_ifs <;> (try tauto) <;> linarith
  have he₂ (a b c : V) : ({a,b,a,c} : Finset V) = {a,b,c} := by
    ext x; simp; tauto
  have he₃ (a b c : V) : ({a,b,c,a} : Finset V) = {a,b,c} := by
    ext x; simp; tauto
  have he₅ (a b c : V) : ({a,b,c,b} : Finset V) = {a,b,c} := by
    ext x; simp; tauto
  have h₁ : (∑ a, ∑ b, ∑ c, ∑ d,
      if a=b then F {a,b,c,d} else 0) = ∑ a, ∑ b, ∑ c, F {a,b,c} := by
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true,insert_idem]
  have h₂ : (∑ a, ∑ b, ∑ c, ∑ d,
      if a=c then F {a,b,c,d} else 0) = ∑ a, ∑ b, ∑ c, F {a,b,c} := by
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true,he₂]
  have h₃ : (∑ a, ∑ b, ∑ c, ∑ d,
      if a=d then F {a,b,c,d} else 0) = ∑ a, ∑ b, ∑ c, F {a,b,c} := by
    simp only [sum_ite_eq,mem_univ,ite_true,he₃]
  have h₄ : (∑ a, ∑ b, ∑ c, ∑ d,
      if b=c then F {a,b,c,d} else 0) = ∑ a, ∑ b, ∑ c, F {a,b,c} := by
    simp only [sum_ite_irrel,sum_const_zero,sum_ite_eq,mem_univ,ite_true,insert_idem]
  have h₅ : (∑ a, ∑ b, ∑ c, ∑ d,
      if b=d then F {a,b,c,d} else 0) = ∑ a, ∑ b, ∑ c, F {a,b,c} := by
    simp only [sum_ite_eq,mem_univ,ite_true,he₅]
  have h₆ : (∑ a, ∑ b, ∑ c, ∑ d,
      if c=d then F {a,b,c,d} else 0) = ∑ a, ∑ b, ∑ c, F {a,b,c} := by
    simp only [sum_ite_eq,mem_univ,ite_true,pair_eq_singleton]
  calc
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d,
      ((if a=b then F {a,b,c,d} else 0) +
      (if a=c then F {a,b,c,d} else 0) +
      (if a=d then F {a,b,c,d} else 0) +
      (if b=c then F {a,b,c,d} else 0) +
      (if b=d then F {a,b,c,d} else 0) +
      (if c=d then F {a,b,c,d} else 0)) :=
        sum_le_sum (fun a _ => sum_le_sum (fun b _ =>
          sum_le_sum (fun c _ => sum_le_sum (fun d _ => hpoint a b c d))))
    _ = _ := by simp only [sum_add_distrib,h₁,h₂,h₃,h₄,h₅,h₆]; ring

def pairBlocks (S : B → Finset V) (b : B) : Finset (V × V) := (S b) ×ˢ (S b)

def secondMoment (S : B → Finset V) : ℕ := ∑ a, ∑ b, count S {a,b}^2
def pairTotal (S : B → Finset V) : ℕ := ∑ a, ∑ b, count S {a,b}

def impurity (S : B → Finset V) : ℕ := ∑ a, ∑ b, ∑ c, ∑ d,
  if ({a,b,c,d} : Finset V).card=4 ∧ (count S {a,b,c,d}=1 ∨ count S {a,b,c,d}=2)
  then 1 else 0

def fourthNorm (S : B → Finset V) : ℝ := ∑ a, ∑ b, ∑ c, ∑ d,
  (count S {a,b,c,d} : ℝ)*((count S {a,b,c,d} : ℝ)-3)^2

lemma pair_replication (S : B → Finset V) (p : V × V) :
    Erdos714ApproximateFisher.replication (pairBlocks S) p = count S {p.1,p.2} := by
  unfold Erdos714ApproximateFisher.replication count
  congr 1
  ext b
  simp [pairBlocks,mem_blocksContaining,insert_subset_iff]

lemma pair_coverage (S : B → Finset V) (p q : V × V) :
    Erdos714ApproximateFisher.coverage (pairBlocks S) p q =
      count S {p.1,p.2,q.1,q.2} := by
  unfold Erdos714ApproximateFisher.coverage count
  congr 1
  ext b
  simp [pairBlocks,mem_blocksContaining,insert_subset_iff,and_assoc]

/-- The rank certificate summed over all column neighborhoods. -/
theorem pair_rank_bound (S : B → Finset V) :
    ((secondMoment S : ℝ)-3*(pairTotal S : ℝ))^2 ≤
      (Fintype.card B : ℝ)*(Fintype.card B+1 : ℝ)*fourthNorm S := by
  have h := Erdos714ApproximateFisher.localized_defect_bound (pairBlocks S) 3
  simp_rw [pair_replication,pair_coverage] at h
  simp only [Nat.cast_ofNat,Fintype.sum_prod_type] at h
  have ht : (∑ a, ∑ b, (count S {a,b} : ℝ)*((count S {a,b} : ℝ)-3)) =
      ((secondMoment S : ℝ)-3*(pairTotal S : ℝ)) := by
    simp only [secondMoment,pairTotal,Nat.cast_sum,Nat.cast_pow,mul_sub,
      ← pow_two,sum_sub_distrib,← sum_mul]
    ring
  rw [ht] at h
  exact h

lemma count_le_three (S : B → Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (T : Finset V) (hT : T.card=4) : count S T ≤ 3 := by
  have h := (isPacking_iff_common_card S (by decide : 0 < 4)).mpr
    ((free_iff_common_card S (by decide : 0 < 4)).mp hfree) T hT
  exact Nat.le_of_lt_succ h

lemma defect_cubic_bound (n : ℕ) : (n : ℝ)*((n : ℝ)-3)^2 ≤ 4*(n : ℝ)^3 := by
  by_cases hn : n=0
  · simp [hn]
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hs : ((n : ℝ)-3)^2 ≤ 4*(n : ℝ)^2 := by nlinarith [sq_nonneg ((n : ℝ)-1)]
  nlinarith [mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ n)]

/-- All repeated four-tuples are charged to the third homomorphism moment. -/
theorem fourth_norm_bound (S : B → Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    fourthNorm S ≤ 4*(impurity S : ℝ)+24*(thirdMoment S : ℝ) := by
  let F : Finset V → ℝ := fun T => (count S T : ℝ)^3
  have hp (a b c d : V) :
      (count S {a,b,c,d} : ℝ)*((count S {a,b,c,d} : ℝ)-3)^2 ≤
      4*(if ({a,b,c,d} : Finset V).card=4 ∧
        (count S {a,b,c,d}=1 ∨ count S {a,b,c,d}=2) then (1:ℝ) else 0) +
      4*(if ({a,b,c,d} : Finset V).card<4 then F {a,b,c,d} else 0) := by
    by_cases hT : ({a,b,c,d} : Finset V).card=4
    · have hn := count_le_three S hfree {a,b,c,d} hT
      interval_cases hk : count S {a,b,c,d} <;> norm_num [hT,hk]
    · have hcard : ({a,b,c,d} : Finset V).card≤4 := by
        have h₁ := card_insert_le a ({b,c,d} : Finset V)
        have h₂ := card_insert_le b ({c,d} : Finset V)
        have h₃ := card_insert_le c ({d} : Finset V)
        simp only [card_singleton] at h₃
        omega
      have ht : ({a,b,c,d} : Finset V).card<4 := by omega
      simpa only [hT,false_and,ite_false,ht,ite_true,mul_zero,zero_add,F]
        using defect_cubic_bound (count S {a,b,c,d})
  have hr := repeated_four_bound F (by intro T; dsimp [F]; positivity)
  have hh := sum_le_sum (s := univ) (fun a _ => sum_le_sum (s := univ) (fun b _ =>
    sum_le_sum (s := univ) (fun c _ => sum_le_sum (s := univ) (fun d _ => hp a b c d))))
  have hZ : (∑ a, ∑ b, ∑ c, ∑ d,
      if ({a,b,c,d} : Finset V).card=4 ∧
        (count S {a,b,c,d}=1 ∨ count S {a,b,c,d}=2) then (1:ℝ) else 0) =
      (impurity S : ℝ) := by simp only [impurity,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  have h3 : (∑ a, ∑ b, ∑ c, F {a,b,c}) = (thirdMoment S : ℝ) := by
    simp only [thirdMoment,F,Nat.cast_sum,Nat.cast_pow]
  simp only [sum_add_distrib,← mul_sum,hZ] at hh
  rw [h3] at hr
  dsimp only [fourthNorm]
  linarith

lemma pair_total_eq (S : B → Finset V) : pairTotal S = ∑ b, (S b).card^2 := by
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun b (p : V × V) => p ∈ pairBlocks S b)
    (s := (univ : Finset B)) (t := (univ : Finset (V × V)))
  have hl (b : B) : (univ.filter (fun p => p ∈ pairBlocks S b)).card = (S b).card^2 := by
    have he : univ.filter (fun p => p ∈ pairBlocks S b) = pairBlocks S b := by ext p; simp
    rw [he]
    simp only [pairBlocks,card_product,pow_two]
  have hr (p : V × V) : (univ.filter (fun b => p ∈ pairBlocks S b)).card = count S {p.1,p.2} := by
    unfold count
    congr 1
    ext b
    simp [mem_blocksContaining,pairBlocks,insert_subset_iff]
  simp only [bipartiteAbove,bipartiteBelow,hl,hr,Fintype.sum_prod_type] at h
  exact h.symm

lemma second_moment_lower (S : B → Finset V) :
    (∑ b, (S b).card)^4 ≤ (Fintype.card B)^2*(Fintype.card V)^2*secondMoment S := by
  have h1 := sum_mul_sq_le_sq_mul_sq (univ : Finset B) (fun _ => (1 : ℕ))
    (fun b => (S b).card)
  have h2 := sum_mul_sq_le_sq_mul_sq (univ : Finset (V × V)) (fun _ => (1 : ℕ))
    (fun p => count S {p.1,p.2})
  simp only [one_mul,one_pow,sum_const,card_univ,smul_eq_mul,mul_one] at h1 h2
  rw [← pair_total_eq S] at h1
  have h2' : (pairTotal S)^2 ≤ (Fintype.card V)^2*secondMoment S := by
    simpa only [pairTotal,secondMoment,Fintype.sum_prod_type,Fintype.card_prod,pow_two] using h2
  calc
    _ = ((∑ b, (S b).card)^2)^2 := by ring
    _ ≤ (Fintype.card B*pairTotal S)^2 := Nat.pow_le_pow_left h1 2
    _ = (Fintype.card B)^2*(pairTotal S)^2 := by ring
    _ ≤ (Fintype.card B)^2*((Fintype.card V)^2*secondMoment S) := Nat.mul_le_mul_left _ h2'
    _ = _ := by ring

lemma pair_total_bound (S : B → Finset V) (q : ℕ) (hq : 1 ≤ q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    pairTotal S ≤ 24*q^10 := by
  let a : B → ℕ := fun b => (S b).card-3
  have hfour : (∑ b, a b^4) ≤ 3*q^16 := by
    calc
      _ ≤ ∑ b, (S b).card.descFactorial 4 := by
        apply sum_le_sum
        intro b _
        exact Nat.pow_sub_le_descFactorial (S b).card 4
      _ ≤ 3*(Fintype.card V).descFactorial 4 := Erdos714Unbalanced.star_bound S (by decide) hfree
      _ ≤ 3*(Fintype.card V)^4 := Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow _ _)
      _ ≤ 3*(q^4)^4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hV 4)
      _ = _ := by ring
  have hs : (∑ b, a b^2) ≤ 3*q^10 := by
    have hh := sum_mul_sq_le_sq_mul_sq (univ : Finset B) (fun _ => (1 : ℕ))
      (fun b => a b^2)
    have he (b : B) : (a b^2)^2 = a b^4 := by ring
    simp only [one_mul,one_pow,sum_const,card_univ,smul_eq_mul,mul_one,he] at hh
    apply (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp
    calc
      _ ≤ Fintype.card B*(∑ b, a b^4) := hh
      _ ≤ q^4*(3*q^16) := Nat.mul_le_mul hB hfour
      _ ≤ (3*q^10)^2 := by ring_nf; omega
  have hd (b : B) : (S b).card^2 ≤ 2*a b^2+18 := by
    have hh : (S b).card ≤ a b+3 := by dsimp [a]; omega
    have ha := add_pow_le (Nat.zero_le (a b)) (Nat.zero_le 3) 2
    calc
      _ ≤ (a b+3)^2 := Nat.pow_le_pow_left hh 2
      _ ≤ _ := by norm_num at ha; nlinarith
  rw [pair_total_eq]
  calc
    _ ≤ ∑ b, (2*a b^2+18) := sum_le_sum (fun b _ => hd b)
    _ = 2*(∑ b, a b^2)+18*Fintype.card B := by
      simp [sum_add_distrib,← mul_sum,Nat.mul_comm]
    _ ≤ 2*(3*q^10)+18*q^4 := Nat.add_le_add (Nat.mul_le_mul_left _ hs)
      (Nat.mul_le_mul_left _ hB)
    _ ≤ 24*q^10 := by
      have hp : q^4 ≤ q^10 := pow_le_pow_right' hq (by decide)
      omega

/-- Every critical-density K44-free system has a positive-density number
of ordered four-tuples with one or two common neighbors. In particular,
no pointwise degree or codegree regularity is assumed. -/
theorem critical_impurity (S : B → Finset V) (q C : ℕ)
    (hC : 1 ≤ C) (hq : 82944*C^8 ≤ q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*(∑ b, (S b).card)) :
    q^16 ≤ 64*C^8*impurity S := by
  have hq0 : 1 ≤ q := by
    have hc8 : 1 ≤ C^8 := one_le_pow₀ hC
    omega
  have hC4 : 0 < C^4 := by positivity
  have hc28 : C^2 ≤ C^8 := pow_le_pow_right' hC (by decide)
  have h12 : 12*C^2 ≤ q := by omega
  have h144 : 144*C^4 ≤ q^2 := by
    have hh := Nat.pow_le_pow_left h12 2
    nlinarith
  have hK : q^12 ≤ C^4*secondMoment S := by
    have hh : q^16*q^12 ≤ q^16*(C^4*secondMoment S) := by
      calc
        _ = (q^7)^4 := by ring
        _ ≤ (C*(∑ b, (S b).card))^4 := Nat.pow_le_pow_left he 4
        _ = C^4*(∑ b, (S b).card)^4 := by ring
        _ ≤ C^4*((Fintype.card B)^2*(Fintype.card V)^2*secondMoment S) :=
          Nat.mul_le_mul_left _ (second_moment_lower S)
        _ ≤ C^4*((q^4)^2*(q^4)^2*secondMoment S) := by gcongr
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hD := pair_total_bound S q hq0 hB hV hfree
  have hoff : 6*C^4*pairTotal S ≤ q^12 := by
    calc
      _ ≤ 6*C^4*(24*q^10) := Nat.mul_le_mul_left _ hD
      _ = q^10*(144*C^4) := by ring
      _ ≤ q^10*q^2 := Nat.mul_le_mul_left _ h144
      _ = _ := by ring
  have hKD : 3*pairTotal S ≤ secondMoment S := by
    have hh : C^4*(6*pairTotal S) ≤ C^4*secondMoment S := by
      calc
        _ = 6*C^4*pairTotal S := by ring
        _ ≤ q^12 := hoff
        _ ≤ _ := hK
    have h := Nat.le_of_mul_le_mul_left hh hC4
    omega
  have hsub := Nat.sub_add_cancel hKD
  have htrace : q^12 ≤ 2*C^4*(secondMoment S-3*pairTotal S) := by nlinarith
  have hR : (secondMoment S-3*pairTotal S)^2 ≤
      Fintype.card B*(Fintype.card B+1)*(4*impurity S+24*thirdMoment S) := by
    have hh := (pair_rank_bound S).trans
      (mul_le_mul_of_nonneg_left (fourth_norm_bound S hfree) (by positivity))
    have hh' : (((secondMoment S-3*pairTotal S)^2 : ℕ) : ℝ) ≤
        ((Fintype.card B*(Fintype.card B+1)*(4*impurity S+24*thirdMoment S) : ℕ) : ℝ) := by
      simpa only [Nat.cast_pow,Nat.cast_sub hKD,Nat.cast_mul,Nat.cast_ofNat,
        Nat.cast_add,Nat.cast_one] using hh
    exact_mod_cast hh'
  have hcoef : Fintype.card B*(Fintype.card B+1) ≤ 2*q^8 := by
    have hq4 : 1 ≤ q^4 := one_le_pow₀ hq0
    calc
      _ ≤ q^4*(2*q^4) := Nat.mul_le_mul hB (by omega)
      _ = _ := by ring
  have h3 := third_moment_bound S q hq0 hB hV hfree
  have hR' : (secondMoment S-3*pairTotal S)^2 ≤ 2*q^8*(4*impurity S+5184*q^15) := by
    calc
      _ ≤ Fintype.card B*(Fintype.card B+1)*(4*impurity S+24*thirdMoment S) := hR
      _ ≤ 2*q^8*(4*impurity S+24*(216*q^15)) := by gcongr
      _ = _ := by ring
  have hmain : q^16 ≤ 32*C^8*impurity S+41472*C^8*q^15 := by
    have hh : q^8*q^16 ≤ q^8*(32*C^8*impurity S+41472*C^8*q^15) := by
      calc
        _ = (q^12)^2 := by ring
        _ ≤ (2*C^4*(secondMoment S-3*pairTotal S))^2 := Nat.pow_le_pow_left htrace 2
        _ = 4*C^8*(secondMoment S-3*pairTotal S)^2 := by ring
        _ ≤ 4*C^8*(2*q^8*(4*impurity S+5184*q^15)) := Nat.mul_le_mul_left _ hR'
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hh (by positivity)
  have hoff' : 82944*C^8*q^15 ≤ q^16 := by
    calc
      _ ≤ q*q^15 := Nat.mul_le_mul_right _ hq
      _ = _ := by ring
  nlinarith

abbrev Quad (V : Type*) := V × V × V × V

def quadSet (p : Quad V) : Finset V := {p.1,p.2.1,p.2.2.1,p.2.2.2}

def impureQuads (S : B → Finset V) : Finset (Quad V) :=
  univ.filter (fun p => (quadSet p).card=4 ∧
    (count S (quadSet p)=1 ∨ count S (quadSet p)=2))

lemma impurity_eq_card (S : B → Finset V) : impurity S = (impureQuads S).card := by
  calc
    impurity S = ∑ p : Quad V, if (quadSet p).card=4 ∧
        (count S (quadSet p)=1 ∨ count S (quadSet p)=2) then 1 else 0 := by
      simp only [impurity,quadSet,Fintype.sum_prod_type]
    _ = _ := sum_boole _ _

/-- Almost-purity with at most D q^15 exceptional ordered tuples is
incompatible with unbounded critical parameters. -/
theorem exceptional_budget (S : B → Finset V) (q C D : ℕ)
    (hC : 1 ≤ C) (hq : 82944*C^8 ≤ q)
    (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : q^7 ≤ C*(∑ b, (S b).card))
    (X : Finset (Quad V)) (hX : X.card ≤ D*q^15)
    (hgood : ∀ p, (quadSet p).card=4 → p ∉ X →
      count S (quadSet p)=0 ∨ count S (quadSet p)=3) :
    q ≤ 64*C^8*D := by
  have hsub : impureQuads S ⊆ X := by
    intro p hp
    have hh := (mem_filter.mp hp).2
    by_contra hn
    have h := hgood p hh.1 hn
    omega
  have hZ : impurity S ≤ D*q^15 := by
    rw [impurity_eq_card]
    exact (card_le_card hsub).trans hX
  have hc := critical_impurity S q C hC hq hB hV hfree he
  have hh : q^15*q ≤ q^15*(64*C^8*D) := by
    calc
      _ = q^16 := by ring
      _ ≤ 64*C^8*impurity S := hc
      _ ≤ 64*C^8*(D*q^15) := Nat.mul_le_mul_left _ hZ
      _ = _ := by ring
  have hq0 : 0 < q := by
    have hc8 : 1 ≤ C^8 := one_le_pow₀ hC
    omega
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

def quadEquiv : Quad V ≃ (Fin 4 → V) where
  toFun p := ![p.1,p.2.1,p.2.2.1,p.2.2.2]
  invFun f := (f 0,f 1,f 2,f 3)
  left_inv _ := rfl
  right_inv f := by ext i; fin_cases i <;> rfl

variable {F : Type*} [Field F] [Fintype F]

def quadEncoding (e : V ↪ (Fin 4 → F)) : Quad V ↪ (Fin 16 → F) where
  toFun p j := e (quadEquiv p ((finProdFinEquiv (m := 4) (n := 4)).symm j).1) ((finProdFinEquiv (m := 4) (n := 4)).symm j).2
  inj' := by
    intro p q h
    apply quadEquiv.injective
    funext i
    apply e.injective
    funext k
    have hh := congrFun h (finProdFinEquiv (i,k))
    simpa only [Equiv.symm_apply_apply] using hh

/-- A nonzero polynomial exceptional set is allowed; no codegree bounds
are needed. The encoding lists all sixteen coordinates of the four rows. -/
theorem polynomial_pure_budget (S : B → Finset V) (C : ℕ)
    (hC : 1 ≤ C) (hq : 82944*C^8 ≤ Fintype.card F)
    (hB : Fintype.card B ≤ Fintype.card F^4)
    (e : V ↪ (Fin 4 → F))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : Fintype.card F^7 ≤ C*(∑ b, (S b).card))
    (P : MvPolynomial (Fin 16) F) (hP : P ≠ 0)
    (hgood : ∀ p, (quadSet p).card=4 →
      MvPolynomial.eval (quadEncoding e p) P ≠ 0 →
      count S (quadSet p)=0 ∨ count S (quadSet p)=3) :
    Fintype.card F ≤ 64*C^8*P.totalDegree := by
  have hV : Fintype.card V ≤ Fintype.card F^4 := by
    simpa only [Fintype.card_fun,Fintype.card_fin] using
      Fintype.card_le_of_injective _ e.injective
  apply exceptional_budget S (Fintype.card F) C P.totalDegree hC hq hB hV hfree he
    (univ.filter (fun p => MvPolynomial.eval (quadEncoding e p) P=0))
    (Erdos714PolynomialExceptionalDensity.encoded_zero_card 16 (by decide)
      (quadEncoding e) P hP)
  intro p hp hn
  apply hgood p hp
  simpa using hn

/-- The noncube sparse-sextic model is excluded even when it holds only
outside a bounded-degree polynomial exceptional set. Equality with the
full root set is still essential. -/
theorem exceptional_sparse_sextic_budget (S : B → Finset V) (C : ℕ)
    (hC : 1 ≤ C) (hq : 82944*C^8 ≤ Fintype.card F)
    (hB : Fintype.card B ≤ Fintype.card F^4)
    (e : V ↪ (Fin 4 → F))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (he : Fintype.card F^7 ≤ C*(∑ b, (S b).card))
    (P : MvPolynomial (Fin 16) F) (hP : P ≠ 0)
    (a b : Quad V → F) (ζ : F) (hζ : IsPrimitiveRoot ζ 3)
    (hb : ∀ p, ¬ ∃ z : F, z^3=b p)
    (hmodel : ∀ p, (quadSet p).card=4 →
      MvPolynomial.eval (quadEncoding e p) P ≠ 0 →
      count S (quadSet p) = (Erdos714PowerQuadraticRoots.solutions 3 (a p) (b p)).card) :
    Fintype.card F ≤ 64*C^8*P.totalDegree := by
  apply polynomial_pure_budget S C hC hq hB e hfree he P hP
  intro p hp hn
  rw [hmodel p hp hn]
  exact Erdos714PowerQuadraticRoots.solution_card_zero_or_k
    3 (by decide) (a p) (b p) ζ (hb p) hζ

#print axioms third_moment_bound
#print axioms repeated_four_bound
#print axioms pair_rank_bound
#print axioms fourth_norm_bound
#print axioms second_moment_lower
#print axioms critical_impurity
#print axioms exceptional_budget
#print axioms polynomial_pure_budget
#print axioms exceptional_sparse_sextic_budget
end Erdos714RobustPureFour
