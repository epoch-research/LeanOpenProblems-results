import FormalConjecturesUtil
import Submission.C8CosetOctagon
import Submission.C8CentralSuzukiBasic

/-! A nondegenerate twisted-central word supplies an injective coset octagon. -/
open SimpleGraph
namespace Erdos713C8CentralSuzukiCosets
open Erdos713C8MixedSuzukiMatrices Erdos713C8CentralSuzukiMatrices
variable {F G : Type*} [Field F] [CharP F 2] [Group G]
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

omit [CharP F 2] in
lemma corners (σ : F →+* F) (a b c d : F) :
    (Z σ a*O σ b) 0 3=σ b ∧
    (O σ a*Z σ b) 3 0=σ b ∧
    (Z σ a*O σ b*Z σ c) 0 3=σ b ∧
    (O σ a*Z σ b*O σ c) 3 0=σ b ∧
    (O σ a*Z σ b*O σ c) 1 0=a*σ b ∧
    (Z σ a*O σ b*Z σ c) 2 1=a*σ b*c ∧
    (Z σ a*O σ b*Z σ c*O σ d) 1 0=b*σ c := by
  simp [Z,O,X,Matrix.mul_apply,Fin.sum_univ_succ]

lemma four_injective {T : Type*} (a b c d : T)
    (h01 : a ≠ b) (h02 : a ≠ c) (h03 : a ≠ d)
    (h12 : b ≠ c) (h13 : b ≠ d) (h23 : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → T) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> first | rfl | (
    dsimp at he
    first | exact (h01 he).elim | exact (h01 he.symm).elim | exact (h02 he).elim | exact (h02 he.symm).elim | exact (h03 he).elim | exact (h03 he.symm).elim | exact (h12 he).elim | exact (h12 he.symm).elim | exact (h13 he).elim | exact (h13 he.symm).elim | exact (h23 he).elim | exact (h23 he.symm).elim)

omit [CharP F 2] in
lemma coset_ne_entry (ρ : G →* Mat F) (S : Subgroup G) (i j : Fin 4)
    (hS : ∀ x ∈ S, ρ x i j=0) (a b : G) (hne : ρ (a⁻¹*b) i j ≠ 0) :
    (a : G ⧸ S) ≠ (b : G ⧸ S) :=
  fun h => hne (hS _ (QuotientGroup.eq.mp h))

/-- All seven nonzero parameters are explicit hypotheses. The word
identity alone would not suffice to guarantee an injective octagon. -/
theorem contains_word (σ : F →+* F) (ρ : G →* Mat F) (hρ : Function.Injective ρ)
    (H K : Subgroup G)
    (hH03 : ∀ x ∈ H, ρ x 0 3=0) (hH10 : ∀ x ∈ H, ρ x 1 0=0)
    (hK30 : ∀ x ∈ K, ρ x 3 0=0) (hK21 : ∀ x ∈ K, ρ x 2 1=0)
    (z o : F → G) (hz : ∀ a, ρ (z a)=Z σ a) (ho : ∀ a, ρ (o a)=O σ a)
    (hzH : ∀ a, z a ∈ H) (hoK : ∀ a, o a ∈ K)
    (b c d e f g h : F) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0)
    (he : e ≠ 0) (hf : f ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0)
    (hword : z 1*o b*z c*o d*z h=o e*z f*o g) :
    cycleGraph 8 ⊑ Erdos713C8CosetOctagon.graph H K := by
  have hzsq : ∀ a, z a*z a=1 := by
    intro a; apply hρ
    simpa only [map_mul,map_one,hz] using Z_sq σ a
  have hosq : ∀ a, o a*o a=1 := by
    intro a; apply hρ
    simpa only [map_mul,map_one,ho] using O_sq σ a
  have hzi : ∀ a, (z a)⁻¹=z a := fun a => inv_eq_of_mul_eq_one_right (hzsq a)
  have hoi : ∀ a, (o a)⁻¹=o a := fun a => inv_eq_of_mul_eq_one_right (hosq a)
  let u := z 1*o b
  let v := u*z c
  let w := v*o d
  let t := o e*z f
  have hword' : w*z h=t*o g := hword
  have hw : w=t*o g*z h := by
    apply mul_right_cancel (b := z h)
    simpa only [mul_assoc,hzsq,mul_one] using hword'
  have ht : t=v*o d*z h*o g := by
    apply mul_right_cancel (b := o g)
    simpa only [w,mul_assoc,hosq,mul_one] using hword'.symm
  have hw_inv : w⁻¹*o e=z h*o g*z f := by
    rw [hw]
    simp only [t,mul_inv_rev,hzi,hoi,mul_assoc,hosq,mul_one]
  have hv_inv : v⁻¹*t=o d*z h*o g := by
    rw [ht]
    simp only [mul_assoc,inv_mul_cancel_left]
  have hσnz : ∀ a : F, a ≠ 0 → σ a ≠ 0 := fun a ha => (map_ne_zero σ).mpr ha
  let p : Fin 4 → G ⧸ H := ![((1 : G) : G ⧸ H),(u : G ⧸ H),(w : G ⧸ H),(o e : G ⧸ H)]
  let l : Fin 4 → G ⧸ K := ![(z 1 : G ⧸ K),(v : G ⧸ K),(t : G ⧸ K),((1 : G) : G ⧸ K)]
  have hp : Function.Injective p := by
    apply four_injective
    · apply coset_ne_entry ρ H 0 3 hH03
      simpa only [inv_one,one_mul,u,map_mul,hz,ho,(corners σ 1 b 0 0).1] using hσnz b hb
    · apply coset_ne_entry ρ H 1 0 hH10
      simpa only [inv_one,one_mul,w,v,u,map_mul,hz,ho,(corners σ 1 b c d).2.2.2.2.2.2] using mul_ne_zero hb (hσnz c hc)
    · apply coset_ne_entry ρ H 0 3 hH03
      simpa [inv_one,one_mul,ho,O] using hσnz e he
    · apply coset_ne_entry ρ H 0 3 hH03
      have hr : u⁻¹*w=z c*o d := by dsimp [w,v]; group
      simpa only [hr,map_mul,hz,ho,(corners σ c d 0 0).1] using hσnz d hd
    · apply coset_ne_entry ρ H 1 0 hH10
      simpa only [u,mul_inv_rev,hoi,hzi,map_mul,hz,ho,(corners σ b 1 e 0).2.2.2.2.1,map_one,mul_one] using hb
    · apply coset_ne_entry ρ H 0 3 hH03
      simpa only [hw_inv,map_mul,hz,ho,(corners σ h g f 0).2.2.1] using hσnz g hg
  have hl : Function.Injective l := by
    apply four_injective
    · apply coset_ne_entry ρ K 3 0 hK30
      have hr : (z 1)⁻¹*v=o b*z c := by dsimp [v,u]; group
      simpa only [hr,map_mul,hz,ho,(corners σ b c 0 0).2.1] using hσnz c hc
    · apply coset_ne_entry ρ K 2 1 hK21
      simpa only [t,hzi,map_mul,hz,ho,← mul_assoc,(corners σ 1 e f 0).2.2.2.2.2.1,one_mul] using mul_ne_zero (hσnz e he) hf
    · apply coset_ne_entry ρ K 3 0 hK30
      simp [mul_one,hzi,hz,Z,X]
    · apply coset_ne_entry ρ K 3 0 hK30
      simpa only [hv_inv,map_mul,hz,ho,(corners σ d h g 0).2.2.2.1] using hσnz h hh
    · apply coset_ne_entry ρ K 2 1 hK21
      simpa only [v,u,mul_one,mul_inv_rev,hoi,hzi,map_mul,hz,ho,← mul_assoc,(corners σ c b 1 0).2.2.2.2.2.1,mul_one] using mul_ne_zero hc (hσnz b hb)
    · apply coset_ne_entry ρ K 3 0 hK30
      simpa [t,mul_one,mul_inv_rev,hoi,hzi,map_mul,hz,ho,Z,O,X,Matrix.mul_apply,Fin.sum_univ_succ] using hσnz f hf
  apply Erdos713C8CosetOctagon.contains_of_octagon H K p l hp hl
  · intro i
    fin_cases i
    · refine ⟨z 1,?_,rfl⟩
      simpa only [one_mul] using QuotientGroup.mk_mul_of_mem (1 : G) (hzH 1)
    · exact ⟨v,QuotientGroup.mk_mul_of_mem u (hzH c),rfl⟩
    · refine ⟨w*z h,QuotientGroup.mk_mul_of_mem w (hzH h),?_⟩
      change (w*z h : G ⧸ K)=(t : G ⧸ K)
      have hw' : w*z h=t*o g := hword
      rw [hw']
      exact QuotientGroup.mk_mul_of_mem t (hoK g)
    · refine ⟨o e,rfl,?_⟩
      simpa only [one_mul] using QuotientGroup.mk_mul_of_mem (1 : G) (hoK e)
  · intro i
    fin_cases i
    · exact ⟨u,rfl,QuotientGroup.mk_mul_of_mem (z 1) (hoK b)⟩
    · exact ⟨w,rfl,QuotientGroup.mk_mul_of_mem v (hoK d)⟩
    · exact ⟨t,QuotientGroup.mk_mul_of_mem (o e) (hzH f),rfl⟩
    · exact ⟨1,rfl,rfl⟩

end Erdos713C8CentralSuzukiCosets
