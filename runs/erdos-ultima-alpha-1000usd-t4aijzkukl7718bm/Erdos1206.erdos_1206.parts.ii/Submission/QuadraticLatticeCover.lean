import Submission.QuadraticPrimeDivisibility

/-! Finite root-lattice covers, and their combination at coprime moduli. -/
namespace Erdos1206.QuadraticLatticeCover
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticPrimeDivisibility
open scoped Classical
set_option maxHeartbeats 2000000

def Covers (a b c : ℤ) (N d : ℕ) (I : Finset (Finset Vec)) : Prop :=
  points a b c N d ⊆ I.biUnion id ∧
    ∀ S∈I, S ⊆ QuadraticLatticeLines.box N ∧
      ∀ x∈S, ∀ y∈S, (d:ℤ) ∣ form a b c (x-y)

lemma covers_prime {a b c : ℤ} (N p : ℕ) (hp : p.Prime) (hpa : ¬(p:ℤ)∣a) :
    ∃ I : Finset (Finset Vec), I.card ≤ 3 ∧ Covers a b c N p I := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hane : (a:ZMod p) ≠ 0 := fun hz => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
  let Z := (QuadraticLatticeLines.box N).filter
    (fun x => (x.1:ZMod p)=0 ∧ (x.2:ZMod p)=0)
  let R (r : ZMod p) := (QuadraticLatticeLines.box N).filter
    (fun x => (x.1:ZMod p)=r*(x.2:ZMod p))
  let T := (univ : Finset (ZMod p)).filter
    (fun r => (a:ZMod p)*r^2+(b:ZMod p)*r+c=0)
  let I := insert Z (T.image R)
  have hT : T.card ≤ 2 := QuadraticLocalAdmissibility.roots_card hp _ _ _ (Or.inl hane)
  have hI : I.card ≤ 3 := (card_insert_le _ _).trans (by have := card_image_le (s := T) (f := R); omega)
  refine ⟨I,hI,?_,?_⟩
  · intro x hx
    obtain ⟨hxbox,_,hxdvd⟩ := mem_filter.mp hx
    have he : (a:ZMod p)*(x.1:ZMod p)^2+(b:ZMod p)*(x.1:ZMod p)*(x.2:ZMod p)+
        (c:ZMod p)*(x.2:ZMod p)^2=0 := by
      simpa only [form,Int.cast_add,Int.cast_mul,Int.cast_pow] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hxdvd
    apply mem_biUnion.mpr
    by_cases hy : (x.2:ZMod p)=0
    · have hxpow : (x.1:ZMod p)^2=0 := by
        simp only [hy,mul_zero,zero_pow (by decide : 2≠0),add_zero] at he
        exact (mul_eq_zero.mp he).resolve_left hane
      refine ⟨Z,mem_insert_self _ _,?_⟩
      exact mem_filter.mpr ⟨hxbox,eq_zero_of_pow_eq_zero hxpow,hy⟩
    · let r : ZMod p := (x.1:ZMod p)/(x.2:ZMod p)
      have hr : (a:ZMod p)*r^2+(b:ZMod p)*r+c=0 := by
        dsimp only [r]
        field_simp [hy]
        linear_combination he
      have hxr : (x.1:ZMod p)=r*(x.2:ZMod p) := (div_mul_cancel₀ _ hy).symm
      exact ⟨R r,mem_insert_of_mem (mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,hr⟩,rfl⟩),
        mem_filter.mpr ⟨hxbox,hxr⟩⟩
  · intro S hS
    rcases mem_insert.mp hS with rfl | hS
    · refine ⟨filter_subset _ _,fun x hx y hy => ?_⟩
      exact zero_lattice_difference (mem_filter.mp hx).2 (mem_filter.mp hy).2
    · obtain ⟨r,hr,rfl⟩ := mem_image.mp hS
      refine ⟨filter_subset _ _,fun x hx y hy => ?_⟩
      exact root_lattice_difference (mem_filter.mp hr).2 (mem_filter.mp hx).2 (mem_filter.mp hy).2

lemma covers_coprime_mul {a b c : ℤ} {N m n : ℕ} {I J : Finset (Finset Vec)}
    (hI : Covers a b c N m I) (hJ : Covers a b c N n J) (hcop : m.Coprime n) :
    ∃ K : Finset (Finset Vec), K.card ≤ I.card*J.card ∧ Covers a b c N (m*n) K := by
  let K := (I ×ˢ J).image (fun s => s.1 ∩ s.2)
  refine ⟨K,card_image_le.trans_eq (card_product I J),?_,?_⟩
  · intro x hx
    obtain ⟨hxbox,hx0,hdiv⟩ := mem_filter.mp hx
    have hm : (m:ℤ) ∣ form a b c x := (show (m:ℤ) ∣ ((m*n:ℕ):ℤ) by exact_mod_cast dvd_mul_right m n).trans hdiv
    have hn : (n:ℤ) ∣ form a b c x := (show (n:ℤ) ∣ ((m*n:ℕ):ℤ) by exact_mod_cast dvd_mul_left n m).trans hdiv
    obtain ⟨S,hS,hxS⟩ := mem_biUnion.mp (hI.1 (mem_filter.mpr ⟨hxbox,hx0,hm⟩))
    obtain ⟨T,hT,hxT⟩ := mem_biUnion.mp (hJ.1 (mem_filter.mpr ⟨hxbox,hx0,hn⟩))
    exact mem_biUnion.mpr ⟨S∩T,mem_image.mpr ⟨(S,T),mem_product.mpr ⟨hS,hT⟩,rfl⟩,
      mem_inter.mpr ⟨hxS,hxT⟩⟩
  · intro U hU
    obtain ⟨⟨S,T⟩,hST,rfl⟩ := mem_image.mp hU
    obtain ⟨hS,hT⟩ := mem_product.mp hST
    refine ⟨fun x hx => (hI.2 S hS).1 (mem_inter.mp hx).1,fun x hx y hy => ?_⟩
    have hm := (hI.2 S hS).2 x (mem_inter.mp hx).1 y (mem_inter.mp hy).1
    have hn := (hJ.2 T hT).2 x (mem_inter.mp hx).2 y (mem_inter.mp hy).2
    have hh := (Nat.isCoprime_iff_coprime.mpr hcop).mul_dvd hm hn
    simpa only [Nat.cast_mul] using hh

/-- A cover by L root lattices has a uniform O(L*N^2/d) divisibility count. -/
theorem cover_mass_bound {a b c : ℤ} (hQ : Anisotropic a b c)
    {N d L : ℕ} (hd : 0 < d) {I : Finset (Finset Vec)}
    (hIcard : I.card ≤ L) (hI : Covers a b c N d I) :
    d*(points a b c N d).card ≤ 16*mass a b c*L*N^2 := by
  by_cases hsize : d ≤ mass a b c*N^2
  · have hlocal (S : Finset Vec) (hS : S∈I) : d*S.card ≤ 16*mass a b c*N^2 :=
      root_lattice_mass_bound hQ S N d hd hsize (hI.2 S hS).1 (hI.2 S hS).2
    calc
      _ ≤ d*(∑S∈I,S.card) := Nat.mul_le_mul_left d ((card_le_card hI.1).trans card_biUnion_le)
      _ = ∑S∈I,d*S.card := mul_sum _ _ _
      _ ≤ ∑S∈I,16*mass a b c*N^2 := sum_le_sum hlocal
      _ = I.card*(16*mass a b c*N^2) := by simp
      _ ≤ L*(16*mass a b c*N^2) := Nat.mul_le_mul_right _ hIcard
      _ = _ := by ring
  · have he : points a b c N d=∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hsize (prime_le_height hQ hx)
    rw [he,card_empty,mul_zero]
    omega

#print axioms covers_coprime_mul
#print axioms cover_mass_bound
end Erdos1206.QuadraticLatticeCover
