import Submission.PolynomialGraphPeakExplore

/-! Thinning a polynomial graph over a square modulus cannot preserve most of
its points under a small representation cap. This remains a restricted result. -/
namespace Erdos66PolynomialGraphSubset
open AdditiveCombinatorics Polynomial Erdos66PolynomialGraphPeak
open scoped Classical Topology
set_option maxHeartbeats 2400000

variable {H : ℕ} [NeZero H]

noncomputable def input (a i : Fin H) : ZMod (H^2) :=
  ((a.val+H*i.val:ℕ):ZMod (H^2))

lemma input_nat_lt (a i : Fin H) : a.val+H*i.val<H^2 := by
  have ha := a.isLt
  have hi := i.isLt
  have hH := NeZero.pos H
  nlinarith

lemma input_val (a i : Fin H) : (input a i).val=a.val+H*i.val := by
  simp only [input,ZMod.val_natCast,Nat.mod_eq_of_lt (input_nat_lt a i)]

lemma input_injective (a : Fin H) : Function.Injective (input a) := by
  intro i j he
  have hh := congrArg ZMod.val he
  rw [input_val,input_val] at hh
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left (NeZero.pos H) (Nat.add_left_cancel hh))

lemma eval_input (P : Polynomial (ZMod (H^2))) (a i : Fin H) :
    P.eval (input a i)=P.eval (a.val:ZMod (H^2))+
      P.derivative.eval (a.val:ZMod (H^2))*(H:ZMod (H^2))*(i.val:ZMod (H^2)) := by
  have hz : ((H:ZMod (H^2))*(i.val:ZMod (H^2)))^2=0 := by
    rw [mul_pow,square_increment_zero,zero_mul]
  have he := P.eval_add_of_sq_eq_zero (a.val:ZMod (H^2))
    ((H:ZMod (H^2))*(i.val:ZMod (H^2))) hz
  simpa only [input,Nat.cast_add,Nat.cast_mul,mul_assoc] using he

noncomputable def residueSum (P : Polynomial (ZMod (H^2))) (a : Fin H) (u : ℕ) :
    ZMod (H^2) := 2*P.eval (a.val:ZMod (H^2))+
      P.derivative.eval (a.val:ZMod (H^2))*(H:ZMod (H^2))*(u:ZMod (H^2))

lemma eval_input_sum (P : Polynomial (ZMod (H^2))) (a i j : Fin H) :
    P.eval (input a i)+P.eval (input a j)=residueSum P a (i.val+j.val) := by
  rw [eval_input,eval_input]
  simp only [residueSum,Nat.cast_add]
  ring

noncomputable def target (P : Polynomial (ZMod (H^2))) (a : Fin H)
    (p : Fin (2*H) × Bool) : ℕ :=
  2*a.val+H*p.1.val+H^2*((residueSum P a p.1.val).val+if p.2 then H^2 else 0)

lemma graph_sum_mem_targets (P : Polynomial (ZMod (H^2))) (a i j : Fin H) :
    graphEncode P.eval (input a i)+graphEncode P.eval (input a j)∈
      Finset.univ.image (target P a) := by
  letI : NeZero (H^2) := ⟨by have := NeZero.pos H; positivity⟩
  let u : Fin (2*H) := ⟨i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩
  have hs := nat_sum_two_lifts (P.eval (input a i)) (P.eval (input a j))
    (residueSum P a (i.val+j.val)) (eval_input_sum P a i j)
  have he : graphEncode P.eval (input a i)+graphEncode P.eval (input a j)=
      2*a.val+H*(i.val+j.val)+H^2*((P.eval (input a i)).val+(P.eval (input a j)).val) := by
    simp only [graphEncode,input_val]
    ring
  rcases hs with hs | hs
  · refine Finset.mem_image.mpr ⟨(u,false),Finset.mem_univ _,?_⟩
    simp only [target,Bool.false_eq_true,↓reduceIte,add_zero,u]
    rw [he,hs]
  · refine Finset.mem_image.mpr ⟨(u,true),Finset.mem_univ _,?_⟩
    simp only [target,↓reduceIte,u]
    rw [he,hs]

/-- Every subset of one input residue class has at most 4H distinct
ordinary sums, regardless of the polynomial's degree. -/
lemma local_sumset_card_le (P : Polynomial (ZMod (H^2))) (a : Fin H)
    (S : Finset (Fin H)) :
    ((S.product S).image (fun p ↦
      graphEncode P.eval (input a p.1)+graphEncode P.eval (input a p.2))).card≤4*H := by
  have hs : (S.product S).image (fun p ↦
      graphEncode P.eval (input a p.1)+graphEncode P.eval (input a p.2))⊆
      Finset.univ.image (target P a) := by
    intro n hn
    obtain ⟨⟨i,j⟩,hij,rfl⟩ := Finset.mem_image.mp hn
    exact graph_sum_mem_targets P a i j
  have hh := (Finset.card_le_card hs).trans (Finset.card_image_le (s := Finset.univ))
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hh
  omega

lemma local_card_sq_le_cap (P : Polynomial (ZMod (H^2))) (a : Fin H)
    (S : Finset (Fin H)) (A : Set ℕ) (B : ℕ)
    (hSA : ∀ i∈S, graphEncode P.eval (input a i)∈A)
    (hcap : ∀ n : ℕ, n<2*H^4 → sumRep A n≤B) :
    S.card^2≤4*H*B := by
  letI : NeZero (H^2) := ⟨by have := NeZero.pos H; positivity⟩
  let f : Fin H × Fin H → ℕ := fun p ↦
    graphEncode P.eval (input a p.1)+graphEncode P.eval (input a p.2)
  have hbound (n : ℕ) (hn : n∈(S.product S).image f) :
      ((S.product S).filter (fun p ↦ f p=n)).card≤B := by
    have hnlt : n<2*H^4 := by
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn
      have h₁ := graphEncode_lt P.eval (input a p.1)
      have h₂ := graphEncode_lt P.eval (input a p.2)
      dsimp [f]
      have he : (H^2)^2=H^4 := by ring
      rw [he] at h₁ h₂
      omega
    apply (le_trans ?_ (hcap n hnlt))
    rw [sumRep_def]
    apply Finset.card_le_card_of_injOn (fun p ↦
      (graphEncode P.eval (input a p.1),graphEncode P.eval (input a p.2)))
    · intro p hp
      change p∈(S.product S).filter (fun p ↦ f p=n) at hp
      obtain ⟨hp,he⟩ := Finset.mem_filter.mp hp
      obtain ⟨hi,hj⟩ := Finset.mem_product.mp hp
      change (graphEncode P.eval (input a p.1),graphEncode P.eval (input a p.2))∈
        (Finset.antidiagonal n).filter (fun q : ℕ×ℕ ↦ q.1∈A ∧ q.2∈A)
      simp only [Finset.mem_filter,Finset.mem_antidiagonal]
      exact ⟨he,hSA _ hi,hSA _ hj⟩
    · intro p hp q hq he
      apply Prod.ext
      · exact input_injective a (graphEncode_injective P.eval (congrArg Prod.fst he))
      · exact input_injective a (graphEncode_injective P.eval (congrArg Prod.snd he))
  have hh := Finset.card_le_mul_card_image (f := f) (S.product S) B hbound
  have hcard := local_sumset_card_le P a S
  change ((S.product S).image f).card≤4*H at hcard
  simp only [Finset.product_eq_sprod,Finset.card_product] at hh hcard
  nlinarith [Nat.mul_le_mul_left B hcard]

/-- Summing over input residue classes shows that an arbitrary retained
part of a polynomial graph has at most sqrt(4 H^3 B) points under a cap B. -/
theorem retained_graph_card_bound (P : Polynomial (ZMod (H^2)))
    (U : Fin H → Finset (Fin H)) (A : Set ℕ) (B : ℕ)
    (hUA : ∀ a i, i∈U a → graphEncode P.eval (input a i)∈A)
    (hcap : ∀ n : ℕ, n<2*H^4 → sumRep A n≤B) :
    (∑ a, (U a).card)^2≤4*H^3*B := by
  have hlocal (a : Fin H) : (U a).card^2≤4*H*B :=
    local_card_sq_le_cap P a (U a) A B (hUA a) hcap
  have hsum : (∑ a, (U a).card^2)≤H*(4*H*B) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦ hlocal a)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hh
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin H))
    (fun _ ↦ (1:ℕ)) (fun a ↦ (U a).card)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,mul_one] at hCS
  have hh := hCS.trans (Nat.mul_le_mul_left H hsum)
  nlinarith only [hh]

lemma input_grid_bijective : Function.Bijective
    (fun p : Fin H × Fin H ↦ input p.1 p.2) := by
  letI : NeZero (H^2) := ⟨by have := NeZero.pos H; positivity⟩
  constructor
  · intro p q he
    have hh := congrArg ZMod.val he
    rw [input_val,input_val] at hh
    have hmod := congrArg (fun n : ℕ ↦ n%H) hh
    simp only [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt p.1.isLt,
      Nat.mod_eq_of_lt q.1.isLt] at hmod
    have ha : p.1=q.1 := Fin.ext hmod
    have hi : p.2=q.2 := by
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_left (NeZero.pos H) (by omega)
    exact Prod.ext ha hi
  · intro x
    let a : Fin H := ⟨x.val%H,Nat.mod_lt _ (NeZero.pos H)⟩
    let i : Fin H := ⟨x.val/H,(Nat.div_lt_iff_lt_mul (NeZero.pos H)).mpr
      (by simpa only [pow_two] using ZMod.val_lt x)⟩
    refine ⟨(a,i),?_⟩
    apply ZMod.val_injective (H^2)
    rw [input_val]
    exact Nat.mod_add_div x.val H

noncomputable def inputEquiv : (Fin H × Fin H) ≃ ZMod (H^2) :=
  Equiv.ofBijective _ input_grid_bijective

noncomputable def retainedInputs (P : Polynomial (ZMod (H^2))) (A : Set ℕ) :
    Finset (ZMod (H^2)) := by
  letI : NeZero (H^2) := ⟨by have := NeZero.pos H; positivity⟩
  exact Finset.univ.filter (fun x ↦ graphEncode P.eval x∈A)

lemma retainedInputs_card (P : Polynomial (ZMod (H^2))) (A : Set ℕ) :
    (retainedInputs P A).card=
      ∑ a : Fin H, (Finset.univ.filter (fun i : Fin H ↦ graphEncode P.eval (input a i)∈A)).card := by
  letI : NeZero (H^2) := ⟨by have := NeZero.pos H; positivity⟩
  simp only [retainedInputs,Finset.card_filter]
  rw [←Fintype.sum_prod_type (fun p : Fin H × Fin H ↦
    if graphEncode P.eval (input p.1 p.2)∈A then (1:ℕ) else 0)]
  symm
  exact Fintype.sum_equiv inputEquiv _ _ (fun p ↦ rfl)

/-- This is a bound for all points of A lying on one graph, not merely for
an input family already known to be complete in a residue class. -/
theorem retainedInputs_card_sq_le_cap (P : Polynomial (ZMod (H^2)))
    (A : Set ℕ) (B : ℕ) (hcap : ∀ n : ℕ, n<2*H^4 → sumRep A n≤B) :
    (retainedInputs P A).card^2≤4*H^3*B := by
  rw [retainedInputs_card]
  apply retained_graph_card_bound P _ A B
  · intro a i hi
    exact (Finset.mem_filter.mp hi).2
  · exact hcap

/-- A logarithmic representation envelope forces the retained portion of
any polynomial graph to be small, uniformly in the polynomial and its degree. -/
theorem retainedInputs_log_envelope (P : Polynomial (ZMod (H^2)))
    (A : Set ℕ) (K C : ℝ) (hK : 0≤K) (hC : 0≤C)
    (hu : ∀ n : ℕ, (sumRep A n:ℝ)≤K+C*Real.log ((n:ℝ)+2)) :
    ((retainedInputs P A).card:ℝ)^2≤
      4*(H:ℝ)^3*(K+C*Real.log (2*(H:ℝ)^4+2)+1) := by
  let R := K+C*Real.log (2*(H:ℝ)^4+2)
  have hR : 0≤R := by
    have hl : 0≤Real.log (2*(H:ℝ)^4+2) := Real.log_nonneg (by nlinarith [pow_nonneg (Nat.cast_nonneg (α := ℝ) H) 4])
    dsimp [R]
    positivity
  let B := ⌈R⌉₊
  have hcap (n : ℕ) (hn : n<2*H^4) : sumRep A n≤B := by
    have hn' : (n:ℝ)+2≤2*(H:ℝ)^4+2 := by exact_mod_cast (by omega : n+2≤2*H^4+2)
    have hl := Real.log_le_log (by positivity : (0:ℝ)<(n:ℝ)+2) hn'
    have hh : (sumRep A n:ℝ)≤R := (hu n).trans (by
      dsimp [R]
      linarith [mul_le_mul_of_nonneg_left hl hC])
    exact_mod_cast hh.trans (Nat.le_ceil R)
  have hh : ((retainedInputs P A).card:ℝ)^2≤4*(H:ℝ)^3*(B:ℝ) := by
    exact_mod_cast retainedInputs_card_sq_le_cap P A B hcap
  have hb : (B:ℝ)≤R+1 := (Nat.ceil_lt_add_one hR).le
  exact hh.trans (mul_le_mul_of_nonneg_left hb (by positivity))

end Erdos66PolynomialGraphSubset
