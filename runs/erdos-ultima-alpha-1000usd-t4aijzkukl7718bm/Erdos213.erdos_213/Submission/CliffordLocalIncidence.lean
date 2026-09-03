import Submission.CliffordCircle

/-! The geometric odd-neighborhood wrapper for arbitrary finite Clifford
masks. Rationality and completeness of any arithmetic edge rule are separate. -/
namespace Erdos213.CliffordLocalIncidence
open EuclideanGeometry CliffordCircle
noncomputable section

variable {ι : Type*} [DecidableEq ι]

def factorProduct (h : ℂ) (u : ι → ℂ) (S : Finset ι) : ℂ :=
  ∏ i ∈ S, (1+h*u i)

def vertex (h : ℂ) (u : ι → ℂ) (S : Finset ι) : ℂ :=
  evenPoint h (factorProduct h u S) (S.card/2)

def center (h : ℂ) (u : ι → ℂ) (S : Finset ι) : ℂ :=
  oddCenter h (factorProduct h u S) (S.card/2)

def radius (h : ℝ) (u : ι → ℂ) (S : Finset ι) : ℝ :=
  ‖factorProduct h u S‖ / |1-h^2|^(S.card/2)

lemma inserted_incidence (h : ℝ) (u : ι → ℂ) (S : Finset ι) (i : ι)
    (hh : h≠0) (hd : 1-h^2≠0) (hs : Odd S.card) (hi : i∉S) (hu : ‖u i‖=1) :
    dist (vertex h u (insert i S)) (center h u S) = radius h u S := by
  have hc : (insert i S).card/2=S.card/2+1 := by
    rw [Finset.card_insert_of_notMem hi]
    obtain ⟨k,hk⟩ := hs
    omega
  have hp : factorProduct h u (insert i S)=factorProduct h u S*(1+(h : ℂ)*u i) := by
    simp [factorProduct,Finset.prod_insert hi,mul_comm]
  simp only [vertex,center,radius,hc,hp]
  exact added_neighbor_dist h _ _ hh hd hu

lemma erased_incidence (h : ℝ) (u : ι → ℂ) (S : Finset ι) (i : ι)
    (hh : h≠0) (hd : 1-h^2≠0) (hs : Odd S.card) (hi : i∈S) (hu : ‖u i‖=1)
    (hf : 1+(h : ℂ)*u i≠0) :
    dist (vertex h u (S.erase i)) (center h u S) = radius h u S := by
  have hc : (S.erase i).card/2=S.card/2 := by
    rw [Finset.card_erase_of_mem hi]
    obtain ⟨k,hk⟩ := hs
    omega
  have hp : factorProduct h u (S.erase i)=factorProduct h u S/(1+(h : ℂ)*u i) := by
    apply (eq_div_iff hf).mpr
    exact Finset.prod_erase_mul S (fun i => 1+(h : ℂ)*u i) hi
  simp only [vertex,center,radius,hc,hp]
  exact removed_neighbor_dist h _ _ hh hd hu hf

lemma factor_ne_zero (h : ℝ) (u : ℂ) (hd : 1-h^2≠0) (hu : ‖u‖=1) :
    1+(h : ℂ)*u≠0 := by
  intro he
  have hm : (h : ℂ)*u=-1 := by linear_combination he
  have hn := congrArg (fun z : ℂ => ‖z‖) hm
  simp only [norm_mul,hu,mul_one,norm_neg,norm_one,Complex.norm_real,
    Real.norm_eq_abs] at hn
  have hsq : h^2=1 := by
    rw [← sq_abs,hn]
    norm_num
  exact hd (by simp [hsq])

/-- Every one-bit neighbor of any odd mask is on its prescribed circle. -/
theorem odd_neighborhood_cospherical (h : ℝ) (u : ι → ℂ) (S : Finset ι)
    (hh : h≠0) (hd : 1-h^2≠0) (hs : Odd S.card)
    (hu : ∀ i, ‖u i‖=1) :
    Cospherical (Set.range (fun i =>
      vertex h u (if i∈S then S.erase i else insert i S))) := by
  refine ⟨center h u S,radius h u S,?_⟩
  rintro p ⟨i,rfl⟩
  by_cases hi : i∈S
  · simp only [hi,ite_true]
    exact erased_incidence h u S i hh hd hs hi (hu i) (factor_ne_zero h (u i) hd (hu i))
  · simp only [hi,ite_false]
    exact inserted_incidence h u S i hh hd hs hi (hu i)

#print axioms inserted_incidence
#print axioms erased_incidence
#print axioms odd_neighborhood_cospherical
end
end Erdos213.CliffordLocalIncidence
