import Submission.QuadraticLatticeCover

/-! Root-lattice covers modulo a prime square, including the zero residue lattice. -/
namespace Erdos1206.QuadraticSquareLatticeCover
open Finset QuadraticLatticeLines QuadraticRootLattice QuadraticPrimeDivisibility
  QuadraticLatticeCover
open scoped Classical
set_option maxHeartbeats 2000000

lemma zero_lattice_square_difference {p : ℕ} {a b c : ℤ} {x y : Vec}
    (hx : (x.1:ZMod p)=0 ∧ (x.2:ZMod p)=0)
    (hy : (y.1:ZMod p)=0 ∧ (y.2:ZMod p)=0) :
    ((p^2:ℕ):ℤ) ∣ form a b c (x-y) := by
  have h1 : (p:ℤ) ∣ x.1-y.1 := dvd_sub
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx.1)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hy.1)
  have h2 : (p:ℤ) ∣ x.2-y.2 := dvd_sub
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hx.2)
    ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hy.2)
  obtain ⟨u,hu⟩ := h1
  obtain ⟨v,hv⟩ := h2
  refine ⟨form a b c (u,v),?_⟩
  simp only [form,Prod.fst_sub,Prod.snd_sub,Nat.cast_pow,hu,hv]
  ring

lemma covers_prime_square {a b c : ℤ} (N p : ℕ) (hp : p.Prime)
    (hpa : (a:ZMod p) ≠ 0) (hD : (b:ZMod p)^2-4*a*c ≠ 0) :
    ∃ I : Finset (Finset Vec), I.card ≤ 3 ∧ Covers a b c N (p^2) I := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let Z := (QuadraticLatticeLines.box N).filter
    (fun x => (x.1:ZMod p)=0 ∧ (x.2:ZMod p)=0)
  let R (r : ZMod (p^2)) := (QuadraticLatticeLines.box N).filter
    (fun x => (x.1:ZMod (p^2))=r*(x.2:ZMod (p^2)))
  let T := (univ : Finset (ZMod (p^2))).filter
    (fun r => (a:ZMod (p^2))*r^2+(b:ZMod (p^2))*r+c=0)
  let I := insert Z (T.image R)
  have hT : T.card ≤ 2 := QuadraticSquarefreeSieve.quadratic_roots_card hp a b c
    (by simpa only [map_intCast] using hpa)
    (by simpa only [map_sub,map_mul,map_pow,map_ofNat,map_intCast] using hD)
  have hI : I.card ≤ 3 := (card_insert_le _ _).trans (by have := card_image_le (s := T) (f := R); omega)
  refine ⟨I,hI,?_,?_⟩
  · intro x hx
    obtain ⟨hxbox,_,hxdvd⟩ := mem_filter.mp hx
    have he2 : (a:ZMod (p^2))*(x.1:ZMod (p^2))^2+
        (b:ZMod (p^2))*(x.1:ZMod (p^2))*(x.2:ZMod (p^2))+
        (c:ZMod (p^2))*(x.2:ZMod (p^2))^2=0 := by
      simpa only [form,Int.cast_add,Int.cast_mul,Int.cast_pow] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ (p^2)).mpr hxdvd
    have he : (a:ZMod p)*(x.1:ZMod p)^2+(b:ZMod p)*(x.1:ZMod p)*(x.2:ZMod p)+
        (c:ZMod p)*(x.2:ZMod p)^2=0 := by
      have hd : (p:ℤ) ∣ form a b c x :=
        (show (p:ℤ) ∣ ((p^2:ℕ):ℤ) by exact_mod_cast dvd_pow_self p (by decide : 2≠0)).trans hxdvd
      simpa only [form,Int.cast_add,Int.cast_mul,Int.cast_pow] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd
    apply mem_biUnion.mpr
    by_cases hy : (x.2:ZMod p)=0
    · have hxpow : (x.1:ZMod p)^2=0 := by
        simp only [hy,mul_zero,zero_pow (by decide : 2≠0),add_zero] at he
        exact (mul_eq_zero.mp he).resolve_left hpa
      refine ⟨Z,mem_insert_self _ _,?_⟩
      exact mem_filter.mpr ⟨hxbox,eq_zero_of_pow_eq_zero hxpow,hy⟩
    · have hyunit : IsUnit (x.2:ZMod (p^2)) :=
        QuadraticSquarefreeSieve.unit_of_reduction_ne_zero hp _ (by simpa only [map_intCast] using hy)
      obtain ⟨u,hu⟩ := hyunit
      let r : ZMod (p^2) := (x.1:ZMod (p^2))*(↑(u⁻¹):ZMod (p^2))
      have hxr : (x.1:ZMod (p^2))=r*(x.2:ZMod (p^2)) := by
        rw [←hu]
        simp only [r,mul_assoc,Units.inv_mul,mul_one]
      have hr : (a:ZMod (p^2))*r^2+(b:ZMod (p^2))*r+c=0 := by
        have hh : ((a:ZMod (p^2))*r^2+(b:ZMod (p^2))*r+c)*(x.2:ZMod (p^2))^2=0 := by
          rw [hxr] at he2
          linear_combination he2
        have hunit : IsUnit (x.2:ZMod (p^2)) := ⟨u,hu⟩
        exact (hunit.pow 2).mul_left_eq_zero.mp hh
      exact ⟨R r,mem_insert_of_mem (mem_image.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,hr⟩,rfl⟩),
        mem_filter.mpr ⟨hxbox,hxr⟩⟩
  · intro S hS
    rcases mem_insert.mp hS with rfl | hS
    · refine ⟨filter_subset _ _,fun x hx y hy => ?_⟩
      exact zero_lattice_square_difference (mem_filter.mp hx).2 (mem_filter.mp hy).2
    · obtain ⟨r,hr,rfl⟩ := mem_image.mp hS
      refine ⟨filter_subset _ _,fun x hx y hy => ?_⟩
      exact root_lattice_difference (mem_filter.mp hr).2 (mem_filter.mp hx).2 (mem_filter.mp hy).2

#print axioms covers_prime_square
end Erdos1206.QuadraticSquareLatticeCover
