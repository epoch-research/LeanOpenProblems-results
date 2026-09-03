import Submission.SubsystemClosure

/-!
A bounded palette of possible third points is still too restrictive for a
critical K44-free graph. This does not assert that arbitrary graphs admit
such palettes, nor that arbitrary edge thinnings preserve completion.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714CompletionPalettes
open Erdos714Packing Erdos714SubsystemClosure
variable {B V : Type*} [Fintype B] [Fintype V]

def Completes (S : B → Finset V) (P : V → V → Finset V) : Prop :=
  ∀ x y : V, x ≠ y → x ∉ P x y ∧ y ∉ P x y ∧
    ∀ b : B, x ∈ S b → y ∈ S b → (P x y ∩ S b).Nonempty

lemma four_bound (S : B → Finset V)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (T : Finset V) (hT : T.card=4) : (blocksContaining S T).card ≤ 3 := by
  have h := (isPacking_iff_common_card S (by decide : 0 < 4)).mpr
    ((free_iff_common_card S (by decide)).mp hfree) T hT
  omega

lemma generic_triple (S : B → Finset V) (P : V → V → Finset V)
    (hP : Completes S P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) (hz : z ∉ P x y) :
    (blocksContaining S {x,y,z}).card ≤ 3*(P x y).card := by
  have hsub : blocksContaining S {x,y,z} ⊆
      (P x y).biUnion (fun w => blocksContaining S {x,y,z,w}) := by
    intro b hb
    have hm := (mem_blocksContaining S _ _).mp hb
    obtain ⟨w,hw⟩ := (hP x y hxy).2.2 b (hm (by simp)) (hm (by simp))
    refine mem_biUnion.mpr ⟨w,(mem_inter.mp hw).1,?_⟩
    apply (mem_blocksContaining S _ _).mpr
    simp only [insert_subset_iff,singleton_subset_iff]
    exact ⟨hm (by simp),hm (by simp),hm (by simp),(mem_inter.mp hw).2⟩
  have hc (w : V) (hw : w ∈ P x y) : (blocksContaining S {x,y,z,w}).card ≤ 3 := by
    apply four_bound S hfree
    have hxw : x ≠ w := fun h => (hP x y hxy).1 (h ▸ hw)
    have hyw : y ≠ w := fun h => (hP x y hxy).2.1 (h ▸ hw)
    have hzw : z ≠ w := fun h => hz (h ▸ hw)
    simp [hxy,hxz,hyz,hxw,hyw,hzw]
  calc
    _ ≤ ((P x y).biUnion (fun w => blocksContaining S {x,y,z,w})).card := card_le_card hsub
    _ ≤ ∑ w ∈ P x y, (blocksContaining S {x,y,z,w}).card := card_biUnion_le
    _ ≤ ∑ _w ∈ P x y, 3 := sum_le_sum hc
    _ = _ := by simp [mul_comm]

lemma pointwise (S : B → Finset V) (P : V → V → Finset V) (K : ℕ)
    (hK : ∀ x y, (P x y).card ≤ K) (hP : Completes S P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (x y z : V) :
    (blocksContaining S {x,y,z}).card ≤ 3*K +
      (if x=y then Fintype.card B else 0) +
      (if x=z then Fintype.card B else 0) +
      (if y=z then Fintype.card B else 0) +
      (if z ∈ P x y then Fintype.card B else 0) := by
  have hc : (blocksContaining S {x,y,z}).card ≤ Fintype.card B := card_le_univ _
  by_cases hxy : x=y
  · simp only [if_pos hxy]; omega
  by_cases hxz : x=z
  · simp only [if_pos hxz]; omega
  by_cases hyz : y=z
  · simp only [if_pos hyz]; omega
  by_cases hz : z ∈ P x y
  · simp only [if_pos hz]; omega
  simp only [if_neg hxy,if_neg hxz,if_neg hyz,if_neg hz,add_zero]
  exact (generic_triple S P hP hfree x y z hxy hxz hyz hz).trans (Nat.mul_le_mul_left _ (hK x y))

lemma degree_cube_bound (S : B → Finset V) (P : V → V → Finset V) (K : ℕ)
    (hK : ∀ x y, (P x y).card ≤ K) (hP : Completes S P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ b, (S b).card^3) ≤
      3*K*(Fintype.card V)^3+(K+3)*Fintype.card B*(Fintype.card V)^2 := by
  rw [degree_cube_identity]
  have h := sum_le_sum (s := (univ : Finset V)) (fun x _ =>
    sum_le_sum (s := (univ : Finset V)) (fun y _ =>
      sum_le_sum (s := (univ : Finset V)) (fun z _ => pointwise S P K hK hP hfree x y z)))
  have hxy : (∑ x : V, ∑ y : V, ∑ _z : V, if x=y then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by
    simp [sum_ite_irrel,pow_two,mul_comm,mul_left_comm]
  have hxz : (∑ x : V, ∑ _y : V, ∑ z : V, if x=z then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by simp [pow_two,mul_comm,mul_left_comm]
  have hyz : (∑ _x : V, ∑ y : V, ∑ z : V, if y=z then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by simp [pow_two,mul_comm,mul_left_comm]
  have hp : (∑ x : V, ∑ y : V, ∑ z : V, if z ∈ P x y then Fintype.card B else 0) ≤
      K*Fintype.card B*(Fintype.card V)^2 := by
    calc
      _ = ∑ x, ∑ y, (P x y).card*Fintype.card B := by
        apply sum_congr rfl
        intro x _
        apply sum_congr rfl
        intro y _
        rw [← sum_filter]
        simp
      _ ≤ ∑ _x : V, ∑ _y : V, K*Fintype.card B :=
        sum_le_sum (fun x _ => sum_le_sum (fun y _ => Nat.mul_le_mul_right _ (hK x y)))
      _ = _ := by simp [pow_two,mul_comm,mul_left_comm]
  simp only [sum_add_distrib,hxy,hxz,hyz] at h
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at h
  nlinarith

/-- A fixed number of completion choices does not repair the subsystem route. -/
theorem balanced_bound (S : B → Finset V) (P : V → V → Finset V) (K : ℕ)
    (hK : ∀ x y, (P x y).card ≤ K) (hP : Completes S P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (N : ℕ) (hB : Fintype.card B ≤ N) (hV : Fintype.card V ≤ N) :
    (∑ b, (S b).card)^3 ≤ (4*K+3)*N^5 := by
  calc
    _ ≤ (Fintype.card B)^2*∑ b, (S b).card^3 := cubic_holder _
    _ ≤ (Fintype.card B)^2*(3*K*(Fintype.card V)^3+
        (K+3)*Fintype.card B*(Fintype.card V)^2) :=
      Nat.mul_le_mul_left _ (degree_cube_bound S P K hK hP hfree)
    _ ≤ N^2*(3*K*N^3+(K+3)*N*N^2) := by gcongr
    _ = _ := by ring

/-- At critical scale the palette size must grow at least linearly in q. -/
theorem critical_budget (S : B → Finset V) (P : V → V → Finset V) (K : ℕ)
    (hK : ∀ x y, (P x y).card ≤ K) (hP : Completes S P)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (q C : ℕ) (hq : 0 < q) (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (he : q^7 ≤ C*(∑ b, (S b).card)) : q ≤ (4*K+3)*C^3 := by
  have hh : q^20*q ≤ q^20*((4*K+3)*C^3) := by
    calc
      _ = (q^7)^3 := by ring
      _ ≤ (C*(∑ b, (S b).card))^3 := Nat.pow_le_pow_left he 3
      _ = C^3*(∑ b, (S b).card)^3 := by ring
      _ ≤ C^3*((4*K+3)*(q^4)^5) := Nat.mul_le_mul_left _
        (balanced_bound S P K hK hP hfree _ hB hV)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

#print axioms generic_triple
#print axioms degree_cube_bound
#print axioms balanced_bound
#print axioms critical_budget
end Erdos714CompletionPalettes
