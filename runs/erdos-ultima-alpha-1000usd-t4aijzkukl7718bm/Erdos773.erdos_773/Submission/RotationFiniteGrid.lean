import Submission.QuadraticRotationSpecialization

/-!
Quantitative finite specialization using Schwartz--Zippel. This supplies a
polynomial height bound for the finite rotation model, not an improvement
of the asymptotic square-Sidon lower exponent.
-/
namespace Erdos773.QuadraticRotationTrade
open Finset Fintype MvPolynomial
set_option maxHeartbeats 2500000
noncomputable section

lemma exists_grid_nonzero {n : ℕ} {p : MvPolynomial (Fin n) ℚ}
    (hp : p ≠ 0) (S : Finset ℚ) (hS : p.totalDegree < S.card) :
    ∃ x : Fin n → ℚ, (∀ i, x i ∈ S) ∧ eval x p ≠ 0 := by
  classical
  by_contra hn
  push_neg at hn
  have he : {x ∈ piFinset (fun _ : Fin n => S) | eval x p=0} =
      piFinset (fun _ : Fin n => S) := by
    apply filter_eq_self.mpr
    intro x hx
    exact hn x (by simpa using hx)
  have hb := schwartz_zippel_totalDegree hp S
  rw [he,card_piFinset] at hb
  have hpos : (0:ℚ≥0) < S.card := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le _) hS)
  have hne : (#S : ℚ≥0)^n ≠ 0 := pow_ne_zero _ hpos.ne'
  simp only [prod_const,card_univ,Fintype.card_fin,Nat.cast_pow] at hb
  rw [div_self hne] at hb
  have hh := (one_le_div hpos).mp hb
  have hlt : (p.totalDegree : ℚ≥0) < S.card := by exact_mod_cast hS
  exact (not_le_of_gt hlt) hh

lemma avoid_integer_grid {n d L : ℕ} (P : Finset (MvPolynomial (Fin n) ℚ))
    (hP : ∀ p ∈ P, p ≠ 0 ∧ p.totalDegree ≤ d) (hL : d*P.card < L) :
    ∃ x : Fin n → ℕ, (∀ i, 3*L+1 ≤ x i ∧ x i ≤ 4*L) ∧
      ∀ p ∈ P, eval (fun i => (x i : ℚ)) p ≠ 0 := by
  classical
  let p := ∏ f ∈ P, f
  have hp : p ≠ 0 := prod_ne_zero_iff.mpr (fun f hf => (hP f hf).1)
  have hd : p.totalDegree ≤ d*P.card := by
    apply (totalDegree_finset_prod P id).trans
    calc
      (∑ f ∈ P, f.totalDegree) ≤ ∑ _f ∈ P, d := sum_le_sum (fun f hf => (hP f hf).2)
      _ = d*P.card := by simp [Nat.mul_comm]
  let S : Finset ℚ := (Icc (3*L+1) (4*L)).image (fun a : ℕ => (a:ℚ))
  have hcard : S.card=L := by
    rw [card_image_of_injective _ Nat.cast_injective]
    simp only [Nat.card_Icc]
    omega
  obtain ⟨x,hx,hpn⟩ := exists_grid_nonzero hp S (by rw [hcard]; exact hd.trans_lt hL)
  have hh (i : Fin n) : ∃ a : ℕ, a ∈ Icc (3*L+1) (4*L) ∧ (a:ℚ)=x i := mem_image.mp (hx i)
  choose y hy he using hh
  refine ⟨y,fun i => mem_Icc.mp (hy i),?_⟩
  have hsum : ∀ f ∈ P, eval x f ≠ 0 := by
    simpa only [p,map_prod,prod_ne_zero_iff] using hpn
  intro f hf
  simpa only [he] using hsum f hf

/-- The formal roots are in bijection with all ordered pairs of core indices. -/
def rootKey {n : ℕ} : Root n → Fin n × Fin n
  | .core a => (a,a)
  | .plus e => e.val
  | .minus e => (e.val.2,e.val.1)

lemma rootKey_bijective (n : ℕ) : Function.Bijective (rootKey (n := n)) := by
  constructor
  · intro u v h
    cases u with
    | core a =>
      cases v with
      | core b => simp only [rootKey,Prod.mk.injEq] at h; simp [h.1]
      | plus e =>
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        exact (e.property.ne (h₁.symm.trans h₂)).elim
      | minus e =>
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        exact (e.property.ne (h₂.symm.trans h₁)).elim
    | plus e =>
      cases v with
      | core a =>
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        exact (e.property.ne (h₁.trans h₂.symm)).elim
      | plus f => exact congrArg Root.plus (Subtype.ext h)
      | minus f => exact (edge_swap_impossible e f ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩).elim
    | minus e =>
      cases v with
      | core a =>
        have h₁ := congrArg Prod.fst h
        have h₂ := congrArg Prod.snd h
        exact (e.property.ne (h₂.trans h₁.symm)).elim
      | plus f => exact (edge_swap_impossible e f ⟨congrArg Prod.snd h,congrArg Prod.fst h⟩).elim
      | minus f => exact congrArg Root.minus (Subtype.ext (Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)))
  · rintro ⟨a,b⟩
    rcases lt_trichotomy a b with h | rfl | h
    · exact ⟨.plus ⟨(a,b),h⟩,rfl⟩
    · exact ⟨.core a,rfl⟩
    · exact ⟨.minus ⟨(b,a),h⟩,rfl⟩

lemma root_card (n : ℕ) : Fintype.card (Root n)=n^2 := by
  have hh := Fintype.card_congr (Equiv.ofBijective rootKey (rootKey_bijective n))
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_two] using hh

lemma poly_degree {n : ℕ} (u : Root n) : (poly u).totalDegree ≤ 1 := by
  have hmul (c : ℚ) (a : Fin n) : (C c*X a).totalDegree ≤ 1 := by
    simpa using totalDegree_mul (C c) (X a : MvPolynomial (Fin n) ℚ)
  cases u with
  | core a => exact hmul 5 a
  | plus e => exact (totalDegree_add _ _).trans (max_le (hmul 3 _) (hmul 4 _))
  | minus e => exact (totalDegree_sub _ _).trans (max_le (hmul 4 _) (hmul 3 _))

lemma value_degree {n : ℕ} (u : Root n) : (value u).totalDegree ≤ 2 :=
  (totalDegree_pow (poly u) 2).trans (by have h := poly_degree u; omega)

lemma pair_difference_degree {n : ℕ} (a b c d : Root n) :
    (value a+value b-(value c+value d)).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  exact max_le ((totalDegree_add _ _).trans (max_le (value_degree _) (value_degree _)))
    ((totalDegree_add _ _).trans (max_le (value_degree _) (value_degree _)))

lemma bounded_pair_specialization (n : ℕ) :
    ∃ x : Fin n → ℕ, (∀ i, 3*(2*n^8+1)+1 ≤ x i ∧ x i ≤ 4*(2*n^8+1)) ∧
      ∀ a b c d : Root n,
        eval (fun i => (x i:ℚ)) (value a+value b)=eval (fun i => (x i:ℚ)) (value c+value d) ↔
          value a+value b=value c+value d := by
  classical
  let diff (t : Root n × Root n × Root n × Root n) := value t.1+value t.2.1-(value t.2.2.1+value t.2.2.2)
  let P := (univ.image diff).erase 0
  have hcard : P.card ≤ n^8 := by
    apply card_erase_le.trans (card_image_le.trans ?_)
    simp only [card_univ,Fintype.card_prod,root_card]
    exact le_of_eq (by ring)
  have hP : ∀ p ∈ P, p ≠ 0 ∧ p.totalDegree ≤ 2 := by
    intro p hp
    obtain ⟨hn,hm⟩ := mem_erase.mp hp
    obtain ⟨t,_,rfl⟩ := mem_image.mp hm
    exact ⟨hn,pair_difference_degree _ _ _ _⟩
  obtain ⟨x,hx,havoid⟩ := avoid_integer_grid P hP (show 2*P.card < 2*n^8+1 by omega)
  refine ⟨x,hx,fun a b c d => ⟨?_,fun h => congrArg (eval _) h⟩⟩
  intro h
  by_contra hn
  have hm : diff (a,b,c,d) ∈ P :=
    mem_erase.mpr ⟨sub_ne_zero.mpr hn,mem_image.mpr ⟨(a,b,c,d),mem_univ _,rfl⟩⟩
  apply havoid _ hm
  simp only [diff,map_sub,h,sub_self]

def natRoot {n : ℕ} (x : Fin n → ℕ) : Root n → ℕ
  | .core a => 5*x a
  | .plus e => 3*x e.val.1+4*x e.val.2
  | .minus e => 4*x e.val.1-3*x e.val.2

lemma natRoot_positive_bounded {n L : ℕ} {x : Fin n → ℕ}
    (hx : ∀ i, 3*L+1 ≤ x i ∧ x i ≤ 4*L) (u : Root n) :
    0 < natRoot x u ∧ natRoot x u ≤ 28*L := by
  cases u with
  | core a => dsimp [natRoot]; constructor <;> nlinarith [(hx a).1,(hx a).2]
  | plus e => dsimp [natRoot]; constructor <;> nlinarith [(hx e.val.1).1,(hx e.val.1).2,(hx e.val.2).1,(hx e.val.2).2]
  | minus e =>
    dsimp [natRoot]
    constructor
    · apply Nat.sub_pos_of_lt
      nlinarith [(hx e.val.1).1,(hx e.val.2).2]
    · exact (Nat.sub_le _ _).trans (by nlinarith [(hx e.val.1).2])

lemma eval_natRoot {n L : ℕ} {x : Fin n → ℕ}
    (hx : ∀ i, 3*L+1 ≤ x i ∧ x i ≤ 4*L) (u : Root n) :
    eval (fun i => (x i:ℚ)) (poly u)=(natRoot x u:ℚ) := by
  cases u with
  | core a => simp [poly,natRoot]
  | plus e => simp [poly,natRoot]
  | minus e =>
    have hle : 3*x e.val.2 ≤ 4*x e.val.1 := by nlinarith [(hx e.val.1).1,(hx e.val.2).2]
    simp [poly,natRoot,Nat.cast_sub hle]

/-- A quantitative, relation-preserving model on exactly n^2 formal roots.
    Its height is polynomial, but its 1/4 scale is below existing lower bounds. -/
theorem bounded_integer_model (n : ℕ) :
    ∃ f : Root n → ℕ, (∀ u, 0 < f u ∧ f u ≤ 56*n^8+28) ∧ Function.Injective f ∧
      ∀ u v w z, f u^2+f v^2=f w^2+f z^2 ↔ value u+value v=value w+value z := by
  obtain ⟨x,hx,hpair⟩ := bounded_pair_specialization n
  let f := natRoot x
  have heval (u v : Root n) :
      eval (fun i => (x i:ℚ)) (value u+value v)=((f u^2+f v^2 : ℕ):ℚ) := by
    simp only [map_add,value,map_pow,eval_natRoot hx,Nat.cast_add,Nat.cast_pow,f]
  have hequiv (u v w z : Root n) :
      f u^2+f v^2=f w^2+f z^2 ↔ value u+value v=value w+value z := by
    rw [← hpair,heval,heval]
    exact Nat.cast_inj.symm
  refine ⟨f,?_,?_,hequiv⟩
  · intro u
    obtain ⟨hpos,hbound⟩ := natRoot_positive_bounded hx u
    exact ⟨hpos,hbound.trans_eq (by ring)⟩
  · intro u v huv
    have hh := (hequiv u u v v).mp (by rw [huv])
    apply value_injective
    apply mul_left_cancel₀ (show (2 : MvPolynomial (Fin n) ℚ) ≠ 0 by norm_num)
    simpa only [two_mul] using hh

/-- The elementary packing lower limit on the height of an injective model.
    It does not assert the stronger height estimate needed by the conjecture. -/
lemma model_height_lower {n N : ℕ} {f : Root n → ℕ} (hinj : Function.Injective f)
    (hbound : ∀ u, 0 < f u ∧ f u ≤ N) : n^2 ≤ N := by
  classical
  have hs : univ.image f ⊆ Icc 1 N := by
    intro a ha
    obtain ⟨u,_,rfl⟩ := mem_image.mp ha
    exact mem_Icc.mpr ⟨(hbound u).1,(hbound u).2⟩
  have hh := card_le_card hs
  simpa only [card_image_of_injective _ hinj,card_univ,root_card,Nat.card_Icc,Nat.add_sub_cancel] using hh

#print axioms bounded_integer_model
#print axioms model_height_lower
#print axioms exists_grid_nonzero
#print axioms avoid_integer_grid
#print axioms root_card
#print axioms bounded_pair_specialization
end
end Erdos773.QuadraticRotationTrade
