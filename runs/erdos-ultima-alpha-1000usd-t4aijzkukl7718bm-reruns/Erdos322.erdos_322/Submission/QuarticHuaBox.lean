import Submission.FiniteCollisionEnergy
import Submission.QuarticDifferenceFibers
import Submission.BinaryNormBound

/-! An unrestricted eighth-power Weyl-sum / quartic second-moment bound
in a finite root box, proved by finite differencing and divisor estimates. -/
namespace Erdos322Research.QuarticHuaBox

open Finset FiniteCollisionEnergy QuarticDifferenceFibers
open scoped Classical
set_option Elab.async false

abbrev Pair (B : ℕ) := Fin B × Fin B
abbrev Quad (B : ℕ) := Pair B × Pair B

def pairValue {B : ℕ} (p : Pair B) : ℕ := (p.1 : ℕ)^4+(p.2 : ℕ)^4

def quadValue {B : ℕ} (p : Quad B) : ℕ := pairValue p.1+pairValue p.2

def signedValue {B : ℕ} (p : Quad B) : ℤ :=
  (pairValue p.1 : ℤ)+(p.2.1 : ℤ)^4-(p.2.2 : ℤ)^4

noncomputable def pairEnergy (B : ℕ) : ℕ := energy Finset.univ (@pairValue B)
noncomputable def boxEnergy (B : ℕ) : ℕ := energy Finset.univ (@quadValue B)

def swapLast {B : ℕ} (p : Quad B × Quad B) : Quad B × Quad B :=
  ((p.1.1,(p.1.2.1,p.2.2.2)),(p.2.1,(p.2.2.1,p.1.2.2)))

lemma swapLast_injective (B : ℕ) : Function.Injective (@swapLast B) := by
  apply Function.Involutive.injective
  rintro ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩
  rfl

lemma signed_energy_eq (B : ℕ) : energy Finset.univ (@signedValue B)=boxEnergy B := by
  unfold boxEnergy energy
  apply le_antisymm
  · apply Finset.card_le_card_of_injOn swapLast
    · intro p hp
      simp only [Finset.mem_coe,mem_filter,mem_product,mem_univ,true_and] at hp ⊢
      dsimp [swapLast,signedValue,quadValue,pairValue] at hp ⊢
      zify
      omega
    · exact (swapLast_injective B).injOn
  · apply Finset.card_le_card_of_injOn swapLast
    · intro p hp
      simp only [Finset.mem_coe,mem_filter,mem_product,mem_univ,true_and] at hp ⊢
      dsimp [swapLast,signedValue,quadValue,pairValue] at hp ⊢
      zify at hp
      omega
    · exact (swapLast_injective B).injOn

def differenceLabel {B : ℕ} (p : Quad B) : Fin (2*B+1) :=
  ⟨(p.2.1 : ℕ)+B-(p.2.2 : ℕ),by have := p.2.1.isLt; omega⟩

lemma differenceLabel_eq_iff {B : ℕ} (p q : Quad B) :
    differenceLabel p=differenceLabel q ↔
      (p.2.1 : ℤ)-(p.2.2 : ℤ)=(q.2.1 : ℤ)-(q.2.2 : ℤ) := by
  rw [Fin.ext_iff]
  dsimp [differenceLabel]
  have := p.2.2.isLt
  have := q.2.2.isLt
  omega

noncomputable def alignedFiber (B : ℕ) (D : ℤ) : Finset (Fin 4 → Fin B) :=
  Finset.univ.filter (fun a => aligned (fun i => (a i : ℕ)) ∧
    difference (fun i => (a i : ℕ))=D)

lemma alignedFiber_nonzero_bound (B : ℕ) (D : ℤ) (hD : D ≠ 0) :
    (alignedFiber B D).card ≤ 4*D.natAbs.divisors.card^2 := by
  let f : (Fin 4 → Fin B) → (Fin 4 → ℕ) := fun a i => a i
  have hf : Function.Injective f := by
    intro a b hab
    funext i
    exact Fin.ext (congrFun hab i)
  have hb := nonzero_fiber_bound D hD ((alignedFiber B D).image f) (by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hb).2)
  simpa only [Finset.card_image_of_injective _ hf] using hb

lemma alignedFiber_zero_bound (B : ℕ) : (alignedFiber B 0).card ≤ 2*B^2 := by
  let f : Pair B → (Fin 4 → Fin B) := fun p => ![p.1,p.1,p.2,p.2]
  let g : Pair B → (Fin 4 → Fin B) := fun p => ![p.1,p.2,p.1,p.2]
  have hs : alignedFiber B 0 ⊆ (Finset.univ.image f) ∪ (Finset.univ.image g) := by
    intro a ha
    obtain ⟨hal,hD⟩ := (Finset.mem_filter.mp ha).2
    rcases (zero_difference_iff _ hal).mp hD with ⟨h0,h2⟩ | ⟨h0,h1⟩
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨(a 0,a 2),Finset.mem_univ _,?_⟩
      have he0 : a 0=a 1 := Fin.ext h0
      have he2 : a 2=a 3 := Fin.ext h2
      funext i
      fin_cases i <;> simp [f,he0,he2]
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨(a 0,a 1),Finset.mem_univ _,?_⟩
      have he0 : a 0=a 2 := Fin.ext h0
      have he1 : a 1=a 3 := Fin.ext h1
      funext i
      fin_cases i <;> simp [g,he0,he1]
  calc
    (alignedFiber B 0).card ≤ ((Finset.univ.image f) ∪ (Finset.univ.image g)).card :=
      Finset.card_le_card hs
    _ ≤ (Finset.univ.image f).card+(Finset.univ.image g).card := Finset.card_union_le _ _
    _ ≤ (Finset.univ : Finset (Pair B)).card+(Finset.univ : Finset (Pair B)).card :=
      Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le)
    _ = 2*B^2 := by simp [Pair,pow_two]; omega

lemma pairValue_le (B : ℕ) (p : Pair B) : pairValue p ≤ 2*B^4 := by
  have h1 := Nat.pow_le_pow_left p.1.isLt.le 4
  have h2 := Nat.pow_le_pow_left p.2.isLt.le 4
  dsimp [pairValue]
  omega

lemma pair_difference_abs_le (B : ℕ) (p q : Pair B) :
    ((pairValue q : ℤ)-(pairValue p : ℤ)).natAbs ≤ 2*B^4 := by
  have hp := pairValue_le B p
  have hq := pairValue_le B q
  rw [← Int.ofNat_le,Int.natCast_natAbs,abs_le]
  constructor <;> omega


def baseTuple {B : ℕ} (p : Pair B × Pair B) : Fin 4 → Fin B :=
  ![p.1.1,p.1.2,p.2.1,p.2.2]

lemma baseTuple_injective (B : ℕ) : Function.Injective (@baseTuple B) := by
  intro a b hab
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  have h3 := congrFun hab 3
  exact Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3)

noncomputable def labelledEnergy (B : ℕ) : ℕ :=
  energy Finset.univ (fun a : Quad B => (signedValue a,differenceLabel a))

lemma labelled_energy_le_fibers (B : ℕ) :
    labelledEnergy B ≤ ∑ p : Pair B × Pair B,
      (alignedFiber B ((pairValue p.2 : ℤ)-(pairValue p.1 : ℤ))).card := by
  let S : Finset (Quad B × Quad B) := (Finset.univ ×ˢ Finset.univ).filter
    (fun p => (signedValue p.1,differenceLabel p.1)=
      (signedValue p.2,differenceLabel p.2))
  unfold labelledEnergy
  rw [energy_def]
  change S.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ)
    (f := fun p : Quad B × Quad B => (p.1.1,p.2.1))
    (fun p _ => Finset.mem_univ _)]
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.card_le_card_of_injOn (fun p => baseTuple (p.1.2,p.2.2))
  · intro p hp
    simp only [Finset.mem_coe,Finset.mem_filter,Finset.mem_product,
      Finset.mem_univ,true_and,S,Prod.mk.injEq] at hp
    obtain ⟨⟨hv,hl⟩,hr1,hr2⟩ := hp
    have hal := (differenceLabel_eq_iff p.1 p.2).mp hl
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_⟩
    · simpa only [aligned,baseTuple,Matrix.cons_val_zero,Matrix.cons_val_one,
        Matrix.cons_val_two,Matrix.cons_val_three] using hal
    · dsimp [difference,baseTuple]
      dsimp [signedValue] at hv
      omega
  · intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hp : (a.1.1,a.2.1)=(b.1.1,b.2.1) := ha'.trans hb'.symm
    have hv := baseTuple_injective B hab
    have hp0 := congrArg Prod.fst hp
    have hp1 := congrArg Prod.snd hp
    have hv0 := congrArg Prod.fst hv
    have hv1 := congrArg Prod.snd hv
    exact Prod.ext (Prod.ext hp0 hv0) (Prod.ext hp1 hv1)


/-- Purely finite differencing estimate; `M` controls the binary and the
nonzero aligned-difference fibers. -/
theorem box_energy_bound (B M : ℕ) (hB : 0 < B)
    (hpair : ∀ n : ℕ, (Finset.univ.filter
      (fun p : Pair B => pairValue p=n)).card ≤ M)
    (hdiff : ∀ D : ℤ, D ≠ 0 → D.natAbs ≤ 2*B^4 →
      (alignedFiber B D).card ≤ M) :
    boxEnergy B ≤ 9*B^5*M := by
  have hE2 : pairEnergy B ≤ B^2*M := by
    simpa only [pairEnergy,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
      ← pow_two] using energy_le_card_mul_max_fiber Finset.univ (@pairValue B) M (by
      intro n
      convert hpair n using 1
      congr 1
      ext p
      simp only [Finset.mem_filter])
  have hC : labelledEnergy B ≤ 2*B^2*pairEnergy B+B^4*M := by
    have hb := labelled_energy_le_fibers B
    have hterm (p : Pair B × Pair B) :
        (alignedFiber B ((pairValue p.2 : ℤ)-(pairValue p.1 : ℤ))).card ≤
          (if pairValue p.1=pairValue p.2 then 2*B^2 else 0)+M := by
      by_cases hp : pairValue p.1=pairValue p.2
      · rw [hp,sub_self,if_pos rfl]
        exact (alignedFiber_zero_bound B).trans (Nat.le_add_right _ _)
      · rw [if_neg hp,zero_add]
        apply hdiff _ (by
          apply sub_ne_zero.mpr
          intro he
          exact hp (Nat.cast_injective he.symm))
        exact pair_difference_abs_le B p.1 p.2
    have hs := Finset.sum_le_sum (s := Finset.univ) (fun p _ => hterm p)
    apply hb.trans
    refine hs.trans_eq ?_
    rw [Finset.sum_add_distrib,← Finset.sum_filter,Finset.sum_const,Finset.sum_const]
    have he : (Finset.univ.filter
        (fun p : Pair B × Pair B => pairValue p.1=pairValue p.2)).card=pairEnergy B := by
      unfold pairEnergy
      rw [energy_def,Finset.univ_product_univ]
    rw [he]
    simp only [nsmul_eq_mul,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Nat.cast_id]
    ring
  have hcauchy := energy_le_label_card_mul Finset.univ (@signedValue B) (@differenceLabel B)
  rw [signed_energy_eq] at hcauchy
  simp only [Fintype.card_fin] at hcauchy
  change boxEnergy B ≤ (2*B+1)*labelledEnergy B at hcauchy
  have h1 : 2*B+1 ≤ 3*B := by omega
  calc
    boxEnergy B ≤ (2*B+1)*labelledEnergy B := hcauchy
    _ ≤ (3*B)*(2*B^2*pairEnergy B+B^4*M) := Nat.mul_le_mul h1 hC
    _ ≤ (3*B)*(2*B^2*(B^2*M)+B^4*M) := by gcongr
    _ = 9*B^5*M := by ring

lemma pair_fiber_le_binary (B n : ℕ) :
    (Finset.univ.filter (fun p : Pair B => pairValue p=n)).card ≤
      (binaryNormSolutions 1 n).card := by
  apply Finset.card_le_card_of_injOn
    (fun p : Pair B => ((p.1 : ℕ)^2,(p.2 : ℕ)^2))
  · intro p hp
    apply (mem_binaryNormSolutions (by decide : 0 < 1) _).mpr
    have h := (Finset.mem_filter.mp hp).2
    simpa only [pairValue,one_mul,← pow_mul] using h
  · intro p hp q hq he
    have h0 := congrArg Prod.fst he
    have h1 := congrArg Prod.snd he
    exact Prod.ext (Fin.ext (Nat.pow_left_injective (by decide : 2 ≠ 0) h0))
      (Fin.ext (Nat.pow_left_injective (by decide : 2 ≠ 0) h1))

lemma divisor_square_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ C > (0 : ℝ), ∀ N n : ℕ, 0 < n → n ≤ N →
      4*(n.divisors.card : ℝ)^2 ≤ C*(N+1 : ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := divisor_count_subpolynomial (ε/2) (by linarith)
  refine ⟨4*C^2,by positivity,?_⟩
  intro N n hn hnN
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hp : ((n : ℝ)^(ε/2))^2=(n : ℝ)^ε := by
    rw [pow_two,← Real.rpow_add hnr]
    congr 1
    ring
  calc
    4*(n.divisors.card : ℝ)^2 ≤ 4*(C*(n : ℝ)^(ε/2))^2 := by
      gcongr
      exact hdiv n hn
    _ = (4*C^2)*(n : ℝ)^ε := by rw [mul_pow,hp]; ring
    _ ≤ (4*C^2)*(N+1 : ℝ)^ε := by
      gcongr
      exact_mod_cast (show n ≤ N+1 by omega)

/-- An analytic form of the finite differencing bound. -/
theorem box_energy_subpolynomial_loss (ε : ℝ) (hε : 0 < ε) :
    ∃ K > (0 : ℝ), ∀ B : ℕ, 0 < B →
      (boxEnergy B : ℝ) ≤ K*(B : ℝ)^5*(2*(B : ℝ)^4+1)^ε := by
  obtain ⟨C,hC,hdiv⟩ := divisor_square_uniform ε hε
  obtain ⟨A,hA,hbin⟩ := binary_norm_subpolynomial_general_up_to
    (by decide : 0 < 1) ε hε
  let L := max A C
  have hL : 0 < L := hA.trans_le (le_max_left _ _)
  refine ⟨9*(L+1),by positivity,?_⟩
  intro B hB
  let P : ℝ := (2*(B : ℝ)^4+1)^ε
  have hP : 1 ≤ P := Real.one_le_rpow (by have := pow_nonneg (Nat.cast_nonneg B : (0 : ℝ) ≤ B) 4; linarith) hε.le
  let M : ℕ := ⌈L*P⌉₊
  have hceil : L*P ≤ (M : ℝ) := Nat.le_ceil _
  have hM : (M : ℝ) ≤ (L+1)*P := by
    have hlt := Nat.ceil_lt_add_one (show 0 ≤ L*P by positivity)
    change (M : ℝ) < L*P+1 at hlt
    nlinarith
  have hpair (n : ℕ) :
      (Finset.univ.filter (fun p : Pair B => pairValue p=n)).card ≤ M := by
    by_cases hn : n ≤ 2*B^4
    · have hb := hbin (2*B^4) n hn
      push_cast at hb
      have hi : ((Finset.univ.filter (fun p : Pair B => pairValue p=n)).card : ℝ) ≤
          (binaryNormSolutions 1 n).card := by exact_mod_cast pair_fiber_le_binary B n
      apply (Nat.cast_le (α := ℝ)).mp
      calc
        _ ≤ A*P := hi.trans hb
        _ ≤ L*P := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
        _ ≤ M := hceil
    · have hempty : (Finset.univ.filter (fun p : Pair B => pairValue p=n))=∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p hp he
        exact hn (he ▸ pairValue_le B p)
      simp only [hempty,Finset.card_empty,Nat.zero_le]
  have hdiff (D : ℤ) (hD : D ≠ 0) (hDB : D.natAbs ≤ 2*B^4) :
      (alignedFiber B D).card ≤ M := by
    have hb := hdiv (2*B^4) D.natAbs (Int.natAbs_pos.mpr hD) hDB
    push_cast at hb
    apply (Nat.cast_le (α := ℝ)).mp
    calc
      ((alignedFiber B D).card : ℝ) ≤ 4*(D.natAbs.divisors.card : ℝ)^2 := by
        exact_mod_cast alignedFiber_nonzero_bound B D hD
      _ ≤ C*P := hb
      _ ≤ L*P := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
      _ ≤ M := hceil
  have hf : (boxEnergy B : ℝ) ≤ 9*(B : ℝ)^5*M := by
    exact_mod_cast box_energy_bound B M hB hpair hdiff
  calc
    (boxEnergy B : ℝ) ≤ 9*(B : ℝ)^5*M := hf
    _ ≤ 9*(B : ℝ)^5*((L+1)*P) := by gcongr
    _ = 9*(L+1)*(B : ℝ)^5*(2*(B : ℝ)^4+1)^ε := by ring

end Erdos322Research.QuarticHuaBox
