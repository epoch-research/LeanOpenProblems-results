import FormalConjecturesUtil

/-! Elementary preservation of irreducibility under coprime-degree base change. -/
noncomputable section
open Polynomial IntermediateField
namespace Erdos714CoprimeBaseChange
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- A monic irreducible polynomial remains irreducible after an extension
whose degree is coprime to its degree. -/
theorem irreducible_map (p : F[X]) (hp : Irreducible p) (hm : p.Monic)
    (hcop : p.natDegree.Coprime (Module.finrank F K)) :
    Irreducible (p.map (algebraMap F K)) := by
  let P := p.map (algebraMap F K)
  have hPm : P.Monic := hm.map _
  have hPd : P.natDegree = p.natDegree := natDegree_map _
  have hPu : ¬ IsUnit P := by
    intro h
    have hd := natDegree_eq_zero_of_isUnit h
    rw [hPd] at hd
    exact hp.natDegree_pos.ne' hd
  obtain ⟨g,hgm,hgi,hgd⟩ := P.exists_monic_irreducible_factor hPu
  letI : Fact (Irreducible g) := ⟨hgi⟩
  let L := AdjoinRoot g
  let pb := AdjoinRoot.powerBasis hgi.ne_zero
  letI : FiniteDimensional K L := pb.finite
  letI : FiniteDimensional F L := Module.Finite.trans K L
  let theta : L := AdjoinRoot.root g
  have hgzero : aeval theta g = 0 := by
    exact (AdjoinRoot.aeval_eq g).trans (AdjoinRoot.mk_self (f := g))
  have hpzeroK : aeval theta P = 0 := by
    rcases hgd with ⟨s,hs⟩
    rw [hs,map_mul,hgzero,zero_mul]
  have hpzero : aeval theta p = 0 := by
    simpa only [P, aeval_map_algebraMap] using hpzeroK
  have hmin : p = minpoly F theta := minpoly.eq_of_irreducible_of_monic hp hpzero hm
  have htheta : IsIntegral F theta := ⟨p,hm,hpzero⟩
  have hdiv : p.natDegree ∣ Module.finrank F L := by
    rw [hmin, ← IntermediateField.adjoin.finrank htheta]
    exact ⟨Module.finrank F⟮theta⟯ L, (Module.finrank_mul_finrank F F⟮theta⟯ L).symm⟩
  have hdL : Module.finrank K L = g.natDegree := pb.finrank
  rw [← Module.finrank_mul_finrank F K L, hdL] at hdiv
  have hdiv' := hcop.dvd_of_dvd_mul_left hdiv
  have hle : g.natDegree ≤ p.natDegree := hPd ▸ natDegree_le_of_dvd hgd hPm.ne_zero
  have hge : p.natDegree ≤ g.natDegree := Nat.le_of_dvd hgi.natDegree_pos hdiv'
  have heq : P = g := eq_of_monic_of_dvd_of_natDegree_le hgm hPm hgd (by omega)
  change Irreducible P
  rw [heq]
  exact hgi

#print axioms irreducible_map
end Erdos714CoprimeBaseChange
