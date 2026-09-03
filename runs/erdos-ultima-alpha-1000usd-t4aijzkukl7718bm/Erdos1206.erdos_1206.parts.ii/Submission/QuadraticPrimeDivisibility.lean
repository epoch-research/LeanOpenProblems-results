import Submission.QuadraticRootLattice

/-!
Uniform prime-divisibility bounds in a two-dimensional parameter box.
These fixed-form estimates do not settle the cube-Sidon density conjecture.
-/
namespace Erdos1206.QuadraticPrimeDivisibility
open Finset QuadraticLatticeLines QuadraticRootLattice
open scoped Classical
set_option maxHeartbeats 1000000

noncomputable def points (a b c : ℤ) (N p : ℕ) : Finset Vec :=
  (QuadraticLatticeLines.box N).filter (fun x => x ≠ 0 ∧ (p:ℤ) ∣ form a b c x)

lemma prime_le_height {a b c : ℤ} (hQ : Anisotropic a b c)
    {N p : ℕ} {x : Vec} (hx : x ∈ points a b c N p) :
    p ≤ mass a b c*N^2 := by
  obtain ⟨hbox,hx,hdiv⟩ := mem_filter.mp hx
  have hh := mem_box_iff.mp hbox
  have hsq := pow_le_pow_left₀ (ht_nonneg x) hh 2
  have hmul := mul_le_mul_of_nonneg_left hsq (show (0:ℤ) ≤ mass a b c by positivity)
  have hlo := divisor_lower (hQ x hx) hdiv
  have hhi := form_abs_le a b c x
  have hpZ : (p:ℤ) ≤ (mass a b c:ℤ)*(N:ℤ)^2 := by linarith
  exact_mod_cast hpZ

lemma zero_lattice_difference {p : ℕ} {a b c : ℤ} {x y : Vec}
    (hx : (x.1:ZMod p)=0 ∧ (x.2:ZMod p)=0)
    (hy : (y.1:ZMod p)=0 ∧ (y.2:ZMod p)=0) :
    (p:ℤ) ∣ form a b c (x-y) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp only [form,Prod.fst_sub,Prod.snd_sub,Int.cast_add,Int.cast_mul,
    Int.cast_pow,Int.cast_sub,hx.1,hx.2,hy.1,hy.2,sub_self,zero_pow (by decide : 2 ≠ 0),
    mul_zero,add_zero]

lemma root_lattice_difference {p : ℕ} {a b c : ℤ} {r : ZMod p} {x y : Vec}
    (hr : (a:ZMod p)*r^2+(b:ZMod p)*r+c=0)
    (hx : (x.1:ZMod p)=r*(x.2:ZMod p))
    (hy : (y.1:ZMod p)=r*(y.2:ZMod p)) :
    (p:ℤ) ∣ form a b c (x-y) := by
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  simp only [form,Prod.fst_sub,Prod.snd_sub,Int.cast_add,Int.cast_mul,
    Int.cast_pow,Int.cast_sub,hx,hy]
  linear_combination ((x.2:ZMod p)-(y.2:ZMod p))^2*hr

/-- Every nonzero value divisible by a prime is counted with probability
O(1/p), uniformly in the box size. Irreducibility is represented by the
absence of nonzero integral zeros; positive definiteness is not required. -/
theorem prime_divisibility_bound {a b c : ℤ} (hQ : Anisotropic a b c)
    (N p : ℕ) (hp : p.Prime) :
    p*(points a b c N p).card ≤ 48*mass a b c*N^2 := by
  by_cases hsize : p ≤ mass a b c*N^2
  · have hN : 0 < N := by
      by_contra hn
      have hz : N=0 := by omega
      simp only [hz,zero_pow (by decide : 2 ≠ 0),mul_zero] at hsize
      exact hp.ne_zero (by omega)
    have ha : a ≠ 0 := by
      have hh := hQ (1,0) (by decide)
      simpa only [form,one_pow,mul_one,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero] using hh
    by_cases hpa : (p:ℤ) ∣ a
    · have hpZ := divisor_lower ha hpa
      have hpm : p ≤ mass a b c := by
        have hpmZ : (p:ℤ) ≤ (mass a b c:ℤ) := by
          simp only [mass,Nat.cast_add,Int.natCast_natAbs,Nat.cast_one]
          have := abs_nonneg b
          have := abs_nonneg c
          omega
        exact_mod_cast hpmZ
      have hc : (points a b c N p).card ≤ 9*N^2 := by
        have hh := card_le_card (filter_subset (fun x : Vec => x ≠ 0 ∧
          (p:ℤ) ∣ form a b c x) (QuadraticLatticeLines.box N))
        rw [card_box] at hh
        change (points a b c N p).card ≤ (2*N+1)^2 at hh
        nlinarith
      have hh := Nat.mul_le_mul hpm hc
      nlinarith
    · haveI : Fact p.Prime := ⟨hp⟩
      have hane : (a:ZMod p) ≠ 0 := by
        intro hz
        exact hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp hz)
      let Z := (QuadraticLatticeLines.box N).filter
        (fun x => (x.1:ZMod p)=0 ∧ (x.2:ZMod p)=0)
      let R (r : ZMod p) := (QuadraticLatticeLines.box N).filter
        (fun x => (x.1:ZMod p)=r*(x.2:ZMod p))
      let T := (univ : Finset (ZMod p)).filter
        (fun r => (a:ZMod p)*r^2+(b:ZMod p)*r+c=0)
      have hT : T.card ≤ 2 := QuadraticLocalAdmissibility.roots_card hp _ _ _ (Or.inl hane)
      have hZ : p*Z.card ≤ 16*mass a b c*N^2 := by
        apply root_lattice_mass_bound hQ Z N p hp.pos hsize (filter_subset _ _)
        intro x hx y hy
        exact zero_lattice_difference (mem_filter.mp hx).2 (mem_filter.mp hy).2
      have hR : ∀ r∈T, p*(R r).card ≤ 16*mass a b c*N^2 := by
        intro r hr
        apply root_lattice_mass_bound hQ (R r) N p hp.pos hsize (filter_subset _ _)
        intro x hx y hy
        exact root_lattice_difference (mem_filter.mp hr).2
          (mem_filter.mp hx).2 (mem_filter.mp hy).2
      have hcover : points a b c N p ⊆ Z ∪ T.biUnion R := by
        intro x hx
        obtain ⟨hxbox,hxne,hxdvd⟩ := mem_filter.mp hx
        have he : (a:ZMod p)*(x.1:ZMod p)^2+
            (b:ZMod p)*(x.1:ZMod p)*(x.2:ZMod p)+
            (c:ZMod p)*(x.2:ZMod p)^2=0 := by
          have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hxdvd
          simpa only [form,Int.cast_add,Int.cast_mul,Int.cast_pow] using hh
        by_cases hy : (x.2:ZMod p)=0
        · have hxpow : (x.1:ZMod p)^2=0 := by
            simp only [hy,mul_zero,zero_pow (by decide : 2 ≠ 0),add_zero] at he
            exact (mul_eq_zero.mp he).resolve_left hane
          have hxzero : (x.1:ZMod p)=0 := eq_zero_of_pow_eq_zero hxpow
          exact mem_union_left _ (mem_filter.mpr ⟨hxbox,hxzero,hy⟩)
        · let r : ZMod p := (x.1:ZMod p)/(x.2:ZMod p)
          have hr : (a:ZMod p)*r^2+(b:ZMod p)*r+c=0 := by
            dsimp only [r]
            field_simp [hy]
            linear_combination he
          have hxr : (x.1:ZMod p)=r*(x.2:ZMod p) := (div_mul_cancel₀ _ hy).symm
          exact mem_union_right _ (mem_biUnion.mpr ⟨r,mem_filter.mpr ⟨mem_univ _,hr⟩,
            mem_filter.mpr ⟨hxbox,hxr⟩⟩)
      have hc : (points a b c N p).card ≤ Z.card+∑r∈T,(R r).card :=
        (card_le_card hcover).trans ((card_union_le _ _).trans
          (Nat.add_le_add_left card_biUnion_le Z.card))
      have hsum : p*(∑r∈T,(R r).card) ≤ 2*(16*mass a b c*N^2) := by
        calc
          _ = ∑r∈T,p*(R r).card := mul_sum _ _ _
          _ ≤ ∑r∈T,16*mass a b c*N^2 := sum_le_sum hR
          _ = T.card*(16*mass a b c*N^2) := by simp
          _ ≤ 2*(16*mass a b c*N^2) := Nat.mul_le_mul_right _ hT
      have hh := Nat.mul_le_mul_left p hc
      nlinarith
  · have he : points a b c N p = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact hsize (prime_le_height hQ hx)
    rw [he,card_empty,mul_zero]
    omega

#print axioms prime_divisibility_bound
end Erdos1206.QuadraticPrimeDivisibility
