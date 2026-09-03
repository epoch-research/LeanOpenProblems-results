import Submission.BlowupThinning
import Submission.AffineThreeSeed

/-! Endpoint-dependent relabellings do not amplify the ternary affine seed.
This is a uniform construction obstruction, not a disproof of Erdős 714. -/
noncomputable section
open Classical Finset SimpleGraph Matrix
set_option maxHeartbeats 3000000
set_option maxRecDepth 2000
namespace Erdos714RelabelledSeed
open Erdos714Packing
abbrev F := ZMod 3
abbrev P := Erdos714AffineThree.Point F

def rel (a b : P) : Prop := a.2+b.2=a.1 ⬝ᵥ b.1
lemma rel_symm (a b : P) : rel a b ↔ rel b a := by
  simp only [rel,add_comm,dotProduct_comm]

def columnEquiv (b : P) : {a : P // rel a b} ≃ (Fin 3 → F) where
  toFun a := a.val.1
  invFun x := ⟨(x,x ⬝ᵥ b.1-b.2),by simp [rel]⟩
  left_inv a := by
    apply Subtype.ext
    change (a.val.1,a.val.1 ⬝ᵥ b.1-b.2)=a.val
    refine Prod.ext rfl ?_
    have h := a.property
    change a.val.1 ⬝ᵥ b.1-b.2=a.val.2
    dsimp [rel] at h
    linear_combination -h
  right_inv _ := rfl

lemma permuted_column_card (e : P ≃ P) (b : P) :
    (univ.filter (fun a : P => rel (e a) b)).card=27 := by
  let q : {a : P // rel (e a) b} ≃ {a : P // rel a b} :=
    Equiv.subtypeEquiv e (fun _ => Iff.rfl)
  have h := Fintype.card_congr (q.trans (columnEquiv b))
  simpa only [Fintype.card_subtype,Fintype.card_fun,Fintype.card_fin,ZMod.card] using h

lemma permuted_row_card (e : P ≃ P) (a : P) :
    (univ.filter (fun b : P => rel a (e b))).card=27 := by
  simpa only [rel_symm a] using permuted_column_card e a

def base (x : P) : Finset P := univ.filter (rel x)
lemma base_card (x : P) : (base x).card=27 := by
  exact permuted_row_card (Equiv.refl P) x


/-- The base factor is genuinely K44-free. -/
theorem base_free :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence base) := by
  rw [free_iff_no_rectangle _ (by decide)]
  intro f g h
  apply Erdos714AffineThree.no_rectangle (F := F) (r := 4)
    (by norm_num [F]) f g f.injective g.injective
  intro i j
  exact (mem_filter.mp (h i j)).2

/-- Every individual relabelled local factor is also K44-free. -/
theorem local_free (e f : P ≃ P) :
    (completeBipartiteGraph (Fin 4) (Fin 4)).Free
      (incidence fun a => univ.filter (fun b => rel (e a) (f b))) := by
  rw [free_iff_no_rectangle _ (by decide)]
  intro u v h
  apply (free_iff_no_rectangle _ (by decide)).mp base_free
    (u.trans e.toEmbedding) (v.trans f.toEmbedding)
  intro i j
  simpa [base] using h i j

/-- Both endpoint relabellings may depend arbitrarily on the entire base edge. -/
def lifted (L R : P → P → (P ≃ P)) (p : P × P) : Finset (P × P) :=
  univ.filter (fun z => z.1 ∈ base p.1 ∧ rel (L p.1 z.1 p.2) (R p.1 z.1 z.2))

lemma column_degree (L R : P → P → (P ≃ P)) (x y : P) (hy : y ∈ base x) (b : P) :
    (univ.filter (fun a : P => (y,b) ∈ lifted L R (x,a))).card=27 := by
  simpa [lifted,hy] using permuted_column_card (L x y) (R x y b)

/-- Every such full lift contains K44, despite allowing unrelated edge relabellings. -/
theorem not_free (L R : P → P → (P ≃ P)) :
    ¬ (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence (lifted L R)) := by
  intro hf
  let x : P := (0,0)
  have hP : Fintype.card P=81 := by norm_num [P,Erdos714AffineThree.Point,F]
  have h := Erdos714Blowup.ternary_seed_degree_bound base (lifted L R)
    hf hP hP x (by
      intro y hy b
      convert column_degree L R x y hy b using 1
      apply congrArg Finset.card
      ext a
      simp only [mem_filter,mem_univ,true_and])
  rw [base_card] at h
  omega

lemma lifted_degree (L R : P → P → (P ≃ P)) (p : P × P) :
    (lifted L R p).card=729 := by
  have h : (lifted L R p).card = ∑ y ∈ base p.1,
      (univ.filter (fun b : P => rel (L p.1 y p.2) (R p.1 y b))).card := by
    simp only [lifted,card_eq_sum_ones,sum_filter]
    rw [Fintype.sum_prod_type]
    simp only [ite_and]
    let f : P → ℕ := fun y => ∑ b : P,
      if rel (L p.1 y p.2) (R p.1 y b) then 1 else 0
    trans ∑ y : P, if y ∈ base p.1 then f y else 0
    · apply sum_congr rfl
      intro y _
      by_cases hy : y ∈ base p.1 <;> simp [hy,f]
    · have he : (univ.filter (fun y : P => y ∈ base p.1))=base p.1 := by
        ext y
        simp
      rw [← sum_filter,he]
  rw [h]
  simp only [permuted_row_card,sum_const,nsmul_eq_mul,Nat.cast_id,base_card]
  norm_num

/-- Actual undirected edge count, independent of all relabellings. -/
theorem edge_count (L R : P → P → (P ≃ P)) :
    (incidence (lifted L R)).edgeFinset.card=4782969 := by
  rw [incidence_edges]
  simp only [lifted_degree,sum_const,card_univ,nsmul_eq_mul,Nat.cast_id]
  norm_num [P,Erdos714AffineThree.Point,F]

theorem vertex_count : Fintype.card ((P × P) ⊕ (P × P))=13122 := by
  norm_num [P,Erdos714AffineThree.Point,F]

end Erdos714RelabelledSeed
#print axioms Erdos714RelabelledSeed.permuted_column_card
#print axioms Erdos714RelabelledSeed.not_free
#print axioms Erdos714RelabelledSeed.edge_count
#print axioms Erdos714RelabelledSeed.vertex_count

#print axioms Erdos714RelabelledSeed.base_free
#print axioms Erdos714RelabelledSeed.local_free
