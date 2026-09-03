import Submission.ExceptionalQuinticCounts

/-!
A global binary closure law imposes a subcritical bound on K44-free incidence
systems. This includes closed subsystems of arbitrary Steiner triple systems,
not just linear ones. It does not impose any closure on arbitrary graphs and
therefore does not settle Erdős 714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 4000000
namespace Erdos714SubsystemClosure
open Erdos714Packing
variable {B V : Type*} [Fintype B] [Fintype V]

/-- A closure point for each distinct pair, shared by every indexed block
containing the pair. The point cannot be either endpoint. -/
def PairCompletion (S : B → Finset V) : Prop :=
  ∀ x y : V, x ≠ y → ∃ z : V, z ≠ x ∧ z ≠ y ∧
    ∀ b : B, x ∈ S b → y ∈ S b → z ∈ S b

lemma noncollinear_common (S : B → Finset V) (op : V → V → V)
    (hleft : ∀ x y, x ≠ y → op x y ≠ x)
    (hright : ∀ x y, x ≠ y → op x y ≠ y)
    (hclosed : ∀ b x y, x ∈ S b → y ∈ S b → op x y ∈ S b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (x y z : V) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hz : z ≠ op x y) : (blocksContaining S {x,y,z}).card ≤ 3 := by
  by_contra hn
  obtain ⟨f,hf⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin 4) (s := blocksContaining S {x,y,z}) (by simp; omega)
  have hmem (i : Fin 4) : {x,y,z} ⊆ S (f i) :=
    (mem_blocksContaining S _ _).mp (hf ⟨i,rfl⟩)
  have hx (i : Fin 4) : x ∈ S (f i) := hmem i (by simp)
  have hy (i : Fin 4) : y ∈ S (f i) := hmem i (by simp)
  have hzz (i : Fin 4) : z ∈ S (f i) := hmem i (by simp)
  have hw (i : Fin 4) : op x y ∈ S (f i) := hclosed (f i) x y (hx i) (hy i)
  have hsub : {x,y,z,op x y} ⊆ common S f := by
    simp only [insert_subset_iff,singleton_subset_iff,mem_common]
    exact ⟨hx,hy,hzz,hw⟩
  have hc : ({x,y,z,op x y} : Finset V).card=4 := by
    simp [hxy,hxz,hyz,hz,
      Ne.symm (hleft x y hxy),Ne.symm (hright x y hxy)]
  have hlo := card_le_card hsub
  have hhi := (free_iff_common_card S (by decide : 0 < 4)).mp hfree f
  omega

/-- Repetitions and the one designated closure point account for all exceptional
ordered triples. Each exception has at most two free point coordinates. -/
lemma triple_pointwise (S : B → Finset V) (op : V → V → V)
    (hleft : ∀ x y, x ≠ y → op x y ≠ x)
    (hright : ∀ x y, x ≠ y → op x y ≠ y)
    (hclosed : ∀ b x y, x ∈ S b → y ∈ S b → op x y ∈ S b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (x y z : V) :
    (blocksContaining S {x,y,z}).card ≤ 3 +
      (if x=y then Fintype.card B else 0) +
      (if x=z then Fintype.card B else 0) +
      (if y=z then Fintype.card B else 0) +
      (if z=op x y then Fintype.card B else 0) := by
  have hc : (blocksContaining S {x,y,z}).card ≤ Fintype.card B := card_le_univ _
  by_cases hxy : x=y
  · simp only [if_pos hxy]; omega
  by_cases hxz : x=z
  · simp only [if_pos hxz]; omega
  by_cases hyz : y=z
  · simp only [if_pos hyz]; omega
  by_cases hz : z=op x y
  · simp only [if_pos hz]; omega
  simp only [if_neg hxy,if_neg hxz,if_neg hyz,if_neg hz,add_zero]
  exact noncollinear_common S op hleft hright hclosed hfree x y z hxy hxz hyz hz

lemma degree_cube_identity (S : B → Finset V) :
    (∑ b, (S b).card^3) = ∑ x, ∑ y, ∑ z, (blocksContaining S {x,y,z}).card := by
  let T (b : B) : Finset (V × V × V) := S b ×ˢ (S b ×ˢ S b)
  have h := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun b p => p ∈ T b) (s := (univ : Finset B)) (t := (univ : Finset (V × V × V)))
  have hT (b : B) : (univ.filter (fun p => p ∈ T b)).card=(S b).card^3 := by
    have he : univ.filter (fun p => p ∈ T b)=T b := by ext p; simp
    rw [he]
    simp only [T,card_product]
    ring
  have hd (p : V × V × V) :
      (univ.filter (fun b => p ∈ T b)).card=(blocksContaining S {p.1,p.2.1,p.2.2}).card := by
    congr 1
    ext b
    simp [T,mem_blocksContaining,insert_subset_iff]
  simp only [bipartiteAbove,bipartiteBelow,hT,hd,Fintype.sum_prod_type] at h
  exact h

/-- No degree regularity or linearity of the closure operation is assumed. -/
theorem degree_cube_bound (S : B → Finset V) (op : V → V → V)
    (hleft : ∀ x y, x ≠ y → op x y ≠ x)
    (hright : ∀ x y, x ≠ y → op x y ≠ y)
    (hclosed : ∀ b x y, x ∈ S b → y ∈ S b → op x y ∈ S b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ b, (S b).card^3) ≤ 3*(Fintype.card V)^3+4*Fintype.card B*(Fintype.card V)^2 := by
  rw [degree_cube_identity]
  have h := sum_le_sum (s := (univ : Finset V)) (fun x _ =>
    sum_le_sum (s := (univ : Finset V)) (fun y _ =>
      sum_le_sum (s := (univ : Finset V)) (fun z _ =>
        triple_pointwise S op hleft hright hclosed hfree x y z)))
  have hxy : (∑ x : V, ∑ y : V, ∑ _z : V, if x=y then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by
    simp [sum_ite_irrel,pow_two,mul_comm,mul_left_comm]
  have hxz : (∑ x : V, ∑ _y : V, ∑ z : V, if x=z then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by
    simp [pow_two,mul_comm,mul_left_comm]
  have hyz : (∑ _x : V, ∑ y : V, ∑ z : V, if y=z then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by
    simp [pow_two,mul_comm,mul_left_comm]
  have hop : (∑ x : V, ∑ y : V, ∑ z : V, if z=op x y then Fintype.card B else 0) =
      Fintype.card B*(Fintype.card V)^2 := by
    simp [pow_two,mul_comm,mul_left_comm]
  simp only [sum_add_distrib,hxy,hxz,hyz,hop] at h
  simp only [sum_const,card_univ,nsmul_eq_mul,Nat.cast_id] at h
  convert h using 1; ring

lemma cubic_holder (a : B → ℕ) : (∑ b, a b)^3 ≤ (Fintype.card B)^2*∑ b, a b^3 := by
  have h := pow_sum_le_card_mul_sum_pow (s := (univ : Finset B)) (f := a)
    (by intros; omega) 2
  simpa using h

/-- A genuinely subcritical bound for every K44-free system with one common
binary closure law. This is not asserted for arbitrary edge thinnings. -/
theorem edge_cube_bound (S : B → Finset V) (op : V → V → V)
    (hleft : ∀ x y, x ≠ y → op x y ≠ x)
    (hright : ∀ x y, x ≠ y → op x y ≠ y)
    (hclosed : ∀ b x y, x ∈ S b → y ∈ S b → op x y ∈ S b)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ b, (S b).card)^3 ≤ (Fintype.card B)^2*
      (3*(Fintype.card V)^3+4*Fintype.card B*(Fintype.card V)^2) :=
  (cubic_holder _).trans (Nat.mul_le_mul_left _
    (degree_cube_bound S op hleft hright hclosed hfree))

theorem pair_completion_bound (S : B → Finset V) (hcomp : PairCompletion S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ b, (S b).card)^3 ≤ (Fintype.card B)^2*
      (3*(Fintype.card V)^3+4*Fintype.card B*(Fintype.card V)^2) := by
  let op (x y : V) := if h : x=y then x else Classical.choose (hcomp x y h)
  apply edge_cube_bound S op ?_ ?_ ?_ hfree
  · intro x y hxy
    simp only [op,dif_neg hxy]
    exact (Classical.choose_spec (hcomp x y hxy)).1
  · intro x y hxy
    simp only [op,dif_neg hxy]
    exact (Classical.choose_spec (hcomp x y hxy)).2.1
  · intro b x y hx hy
    dsimp only [op]
    split_ifs with hxy
    · exact hx
    · exact (Classical.choose_spec (hcomp x y hxy)).2.2 b hx hy

/-- Balanced form: e cubed is at most seven times the fifth power of the
vertex budget of one part. -/
theorem balanced_bound (S : B → Finset V) (hcomp : PairCompletion S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (N : ℕ) (hB : Fintype.card B ≤ N) (hV : Fintype.card V ≤ N) :
    (∑ b, (S b).card)^3 ≤ 7*N^5 := by
  calc
    _ ≤ (Fintype.card B)^2*(3*(Fintype.card V)^3+4*Fintype.card B*(Fintype.card V)^2) :=
      pair_completion_bound S hcomp hfree
    _ ≤ N^2*(3*N^3+4*N*N^2) := by gcongr
    _ = _ := by ring

theorem critical_budget (S : B → Finset V) (hcomp : PairCompletion S)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (q C : ℕ) (hq : 0 < q) (hB : Fintype.card B ≤ q^4) (hV : Fintype.card V ≤ q^4)
    (he : q^7 ≤ C*(∑ b, (S b).card)) : q ≤ 7*C^3 := by
  have hh : q^20*q ≤ q^20*(7*C^3) := by
    calc
      _ = (q^7)^3 := by ring
      _ ≤ (C*(∑ b, (S b).card))^3 := Nat.pow_le_pow_left he 3
      _ = C^3*(∑ b, (S b).card)^3 := by ring
      _ ≤ C^3*(7*(q^4)^5) := Nat.mul_le_mul_left _ (balanced_bound S hcomp hfree _ hB hV)
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

section Quintic
open Erdos714ExceptionalCounts
variable {F : Type*} [Field F] [CharP F 3] [Finite F]

/-- Closure under the third point of every root triple through two distinct
points of T, phrased without an arbitrary choice of a quasigroup operation. -/
def QuinticClosed (T : Finset F) : Prop := ∀ a b x y : F,
  x ≠ y → x ∈ T → y ∈ T → x ∈ roots a b → y ∈ roots a b → roots a b ⊆ T

omit [Fintype B] in
lemma quintic_pair_completion (S : B → Finset F) (hns : ¬ IsSquare (-1 : F))
    (hclosed : ∀ b, QuinticClosed (S b)) : PairCompletion S := by
  intro x y hxy
  obtain ⟨a,b,hx,hy⟩ := two_root_parameters x y hxy
  obtain ⟨z,hzx,hzy,hz⟩ := third_root a b x y hxy
    ((mem_roots a b x).mp hx) ((mem_roots a b y).mp hy) hns
  exact ⟨z,hzx,hzy,fun j hxj hyj =>
    hclosed j a b x y hxy hxj hyj hx hy ((mem_roots a b z).mpr hz)⟩

variable [Fintype F]

/-- Nonlinear Steiner subsystems do not furnish the desired large-block
packing merely by being closed under the exceptional-quintic operation. -/
theorem quintic_subsystem_bound (S : B → Finset F) (hns : ¬ IsSquare (-1 : F))
    (hclosed : ∀ b, QuinticClosed (S b))
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    (∑ b, (S b).card)^3 ≤ (Fintype.card B)^2*
      (3*(Fintype.card F)^3+4*Fintype.card B*(Fintype.card F)^2) :=
  pair_completion_bound S (quintic_pair_completion S hns hclosed) hfree

end Quintic

#print axioms noncollinear_common
#print axioms edge_cube_bound
#print axioms pair_completion_bound
#print axioms balanced_bound
#print axioms critical_budget
#print axioms quintic_subsystem_bound
end Erdos714SubsystemClosure
