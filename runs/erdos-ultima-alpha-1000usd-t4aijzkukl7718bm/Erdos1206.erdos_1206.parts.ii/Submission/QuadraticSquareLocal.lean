import Submission.QuadraticNaturalPrime
import Submission.PeriodicParameterSieve

/-! Local factors for simultaneous squarefreeness and forbidden prime divisors. -/
namespace Erdos1206.QuadraticSquareLocal
open Finset QuadraticSquarefreeSieve AffineQuadraticSquarefreeSieve
  QuadraticRootLattice CoprimeBoxCRT
open scoped Classical
set_option maxHeartbeats 2000000

def test (a b c : Fin 4 → ℕ) (B : Set ℕ) (p : ℕ) (x : ℕ × ℕ) : Prop :=
  ∀ i, ¬ p^2∣quad (a i) (b i) (c i) x.1 x.2 ∧
    (p∈B → ¬ p∣quad (a i) (b i) (c i) x.1 x.2)

lemma test_mod (a b c : Fin 4 → ℕ) (B : Set ℕ) (p : ℕ) (x : ℕ × ℕ) :
    test a b c B p (x.1%(p^2),x.2%(p^2)) ↔ test a b c B p x := by
  have he (i : Fin 4) := quad_modEq (a i) (b i) (c i)
    (Nat.mod_modEq x.1 (p^2)) (Nat.mod_modEq x.2 (p^2))
  simp only [test,(he _).dvd_iff dvd_rfl,(he _).dvd_iff (dvd_pow_self p (by decide : 2≠0))]

noncomputable def residues (a b c : Fin 4 → ℕ) (B : Set ℕ) (p : ℕ) :
    Finset (ZMod (p^2) × ZMod (p^2)) :=
  if hp : p.Prime then
    letI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
    univ.filter (fun z => test a b c B p (z.1.val,z.2.val))
  else ∅

lemma mem_residues_nat (a b c : Fin 4 → ℕ) (B : Set ℕ) {p : ℕ} (hp : p.Prime)
    (x : ℕ × ℕ) :
    ((x.1:ZMod (p^2)),(x.2:ZMod (p^2)))∈residues a b c B p ↔ test a b c B p x := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  simp only [residues,dif_pos hp,mem_filter,mem_univ,true_and,ZMod.val_natCast]
  exact test_mod a b c B p x

lemma residues_card (a b c : Fin 4 → ℕ) (B : Set ℕ) {p : ℕ} (hp : p.Prime) :
    (residues a b c B p).card = ((range (p^2) ×ˢ range (p^2)).filter (test a b c B p)).card := by
  haveI : NeZero (p^2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  apply Nat.le_antisymm
  · apply card_le_card_of_injOn (fun z : ZMod (p^2) × ZMod (p^2) => (z.1.val,z.2.val))
    · intro z hz
      change z ∈ residues a b c B p at hz
      simp only [residues,dif_pos hp,mem_filter,mem_univ,true_and] at hz
      exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr z.1.val_lt,mem_range.mpr z.2.val_lt⟩,hz⟩
    · intro x hx y hy h
      exact Prod.ext (ZMod.val_injective _ (congrArg Prod.fst h))
        (ZMod.val_injective _ (congrArg Prod.snd h))
  · apply card_le_card_of_injOn (fun x : ℕ × ℕ => ((x.1:ZMod (p^2)),(x.2:ZMod (p^2))))
    · intro x hx
      exact (mem_residues_nat a b c B hp x).mpr (mem_filter.mp hx).2
    · intro x hx y hy h
      obtain ⟨hx1,hx2⟩ := mem_product.mp (mem_filter.mp hx).1
      obtain ⟨hy1,hy2⟩ := mem_product.mp (mem_filter.mp hy).1
      have h1 := congrArg (fun z : ZMod (p^2) × ZMod (p^2) => z.1.val) h
      have h2 := congrArg (fun z : ZMod (p^2) × ZMod (p^2) => z.2.val) h
      dsimp only at h1 h2
      rw [ZMod.val_cast_of_lt (mem_range.mp hx1),ZMod.val_cast_of_lt (mem_range.mp hy1)] at h1
      rw [ZMod.val_cast_of_lt (mem_range.mp hx2),ZMod.val_cast_of_lt (mem_range.mp hy2)] at h2
      exact Prod.ext h1 h2

def squareConstant (a b c : ℕ) : ℕ := (a+((b:ℤ)^2-4*a*c).natAbs+1)^2+8

def primeConstant (a b c : ℕ) : ℕ := 48*mass c b a+1

lemma square_box_bound (a b c p : ℕ) (ha : 0 < a)
    (hdisc : (b:ℤ)^2-4*a*c ≠ 0) (hp : p.Prime) :
    ((((range (p^2) ×ˢ range (p^2)).filter
      (fun x => p^2∣quad a b c x.1 x.2)).card):ℝ) ≤ (squareConstant a b c:ℝ)*(p:ℝ)^2 := by
  let T := (range (p^2) ×ˢ range (p^2)).filter (fun x => p^2∣quad a b c x.1 x.2)
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  by_cases hlarge : a+((b:ℤ)^2-4*a*c).natAbs < p
  · obtain ⟨ha',hd'⟩ := QuadraticSquareTail.regular_of_large a b c ha hdisc hlarge
    have hh := AffineQuadraticSquarefreeSieve.bad_prime_pairs_count hp a b c 1 0 0 (p^2)
      (by simp) ha' hd'
    simp only [one_mul,add_zero,Nat.cast_pow] at hh
    have he : 3*((p:ℝ)^2)^2/(p:ℝ)^2+4*(p:ℝ)^2+1=7*(p:ℝ)^2+1 := by field_simp; ring
    rw [he] at hh
    have hC : (8:ℝ) ≤ squareConstant a b c := by
      exact_mod_cast (show 8 ≤ squareConstant a b c by dsimp [squareConstant]; omega)
    have hp1 : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hm := mul_le_mul_of_nonneg_right hC (sq_nonneg (p:ℝ))
    nlinarith only [hh,hm,hp1]
  · have hpC : p^2 ≤ squareConstant a b c := by
      dsimp [squareConstant]
      have hpA : p ≤ a+((b:ℤ)^2-4*a*c).natAbs := by omega
      have hh := Nat.pow_le_pow_left hpA 2
      nlinarith
    have hh : T.card ≤ p^2*p^2 := by
      simpa only [card_product,card_range] using card_le_card (filter_subset (fun x => p^2∣quad a b c x.1 x.2) (range (p^2) ×ˢ range (p^2)))
    have hbound := hh.trans (Nat.mul_le_mul_right (p^2) hpC)
    exact_mod_cast hbound

lemma prime_square_box_bound (a b c p : ℕ) (hQ : Anisotropic c b a) (hp : p.Prime) :
    ((((range (p^2) ×ˢ range (p^2)).filter
      (fun x => p∣quad a b c x.1 x.2)).card):ℝ) ≤ (primeConstant a b c:ℝ)*(p:ℝ)^3 := by
  have hh := QuadraticNaturalPrime.prime_box_bound a b c (p^2) p hQ hp
  rw [Nat.cast_pow] at hh
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have he : 48*(mass c b a:ℝ)*((p:ℝ)^2)^2/p=48*(mass c b a:ℝ)*(p:ℝ)^3 := by field_simp
  rw [he] at hh
  have hp1 : (1:ℝ) ≤ (p:ℝ)^3 := one_le_pow₀ (by exact_mod_cast hp.one_le)
  simp only [primeConstant,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  nlinarith only [hh,hp1]

def squareMass (a b c : Fin 4 → ℕ) : ℕ := ∑i,squareConstant (a i) (b i) (c i)
def primeMass (a b c : Fin 4 → ℕ) : ℕ := ∑i,primeConstant (a i) (b i) (c i)

lemma density_bounds (a b c : Fin 4 → ℕ) (B : Set ℕ)
    (ha : ∀ i, 0 < a i) (hQ : ∀ i, Anisotropic (c i) (b i) (a i))
    (hdisc : ∀ i, (b i:ℤ)^2-4*(a i)*(c i) ≠ 0) {p : ℕ} (hp : p.Prime)
    (hloc : ∃ x : ℕ × ℕ, ∀ i, ¬p∣quad (a i) (b i) (c i) x.1 x.2) :
    0 < localDensity (fun p => p^2) (residues a b c B) p ∧
      localDensity (fun p => p^2) (residues a b c B) p ≤ 1 ∧
      1-localDensity (fun p => p^2) (residues a b c B) p ≤
        (squareMass a b c:ℝ)/(p:ℝ)^2 + if p∈B then (primeMass a b c:ℝ)/p else 0 := by
  let U := range (p^2) ×ˢ range (p^2)
  let Bad := U.filter (fun x => ¬test a b c B p x)
  let V (i : Fin 4) := U.filter (fun x => p^2∣quad (a i) (b i) (c i) x.1 x.2)
  let W (i : Fin 4) := U.filter (fun x => p∈B ∧ p∣quad (a i) (b i) (c i) x.1 x.2)
  have hcover : Bad ⊆ univ.biUnion (fun i => V i ∪ W i) := by
    intro x hx
    obtain ⟨hxU,hbad⟩ := mem_filter.mp hx
    simp only [test,not_forall] at hbad
    obtain ⟨i,hi⟩ := hbad
    apply mem_biUnion.mpr
    refine ⟨i,mem_univ _,?_⟩
    by_cases hv : p^2∣quad (a i) (b i) (c i) x.1 x.2
    · exact mem_union_left _ (mem_filter.mpr ⟨hxU,hv⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hxU,by simpa only [_root_.not_imp,not_not] using (not_and.mp hi) hv⟩)
  have hW (i : Fin 4) : ((W i).card:ℝ) ≤
      if p∈B then (primeConstant (a i) (b i) (c i):ℝ)*(p:ℝ)^3 else 0 := by
    by_cases hpB : p∈B
    · simp only [W,hpB,true_and,if_pos]
      exact prime_square_box_bound _ _ _ p (hQ i) hp
    · simp [W,hpB]
  have hbad : (Bad.card:ℝ) ≤ (squareMass a b c:ℝ)*(p:ℝ)^2+
      if p∈B then (primeMass a b c:ℝ)*(p:ℝ)^3 else 0 := by
    have hc := (card_le_card hcover).trans card_biUnion_le
    have hcR : (Bad.card:ℝ) ≤ ∑i,((V i ∪ W i).card:ℝ) := by exact_mod_cast hc
    calc
      _ ≤ ∑i,((V i ∪ W i).card:ℝ) := hcR
      _ ≤ ∑i,(((V i).card:ℝ)+(W i).card) := sum_le_sum (fun i _ => by exact_mod_cast card_union_le (V i) (W i))
      _ ≤ ∑i,((squareConstant (a i) (b i) (c i):ℝ)*(p:ℝ)^2+
          if p∈B then (primeConstant (a i) (b i) (c i):ℝ)*(p:ℝ)^3 else 0) :=
        sum_le_sum (fun i _ => add_le_add (square_box_bound _ _ _ p (ha i) (hdisc i) hp) (hW i))
      _ = _ := by
        by_cases hpB : p∈B <;>
          simp [squareMass,primeMass,Nat.cast_sum,sum_add_distrib,sum_mul,hpB]
  have hpart : (residues a b c B p).card+Bad.card=(p^2)^2 := by
    rw [residues_card a b c B hp]
    have hh := card_filter_add_card_filter_not (s := U) (test a b c B p)
    simpa only [Bad,U,card_product,card_range,pow_two] using hh
  have hpos : 0 < (residues a b c B p).card := by
    obtain ⟨x,hx⟩ := hloc
    apply card_pos.mpr
    refine ⟨((x.1:ZMod (p^2)),(x.2:ZMod (p^2))),(mem_residues_nat a b c B hp x).mpr ?_⟩
    intro i
    exact ⟨fun hd => hx i ((dvd_pow_self p (by decide : 2≠0)).trans hd),fun _ => hx i⟩
  have hpR : (0:ℝ) < p := by exact_mod_cast hp.pos
  have hposR : (0:ℝ) < (residues a b c B p).card := by exact_mod_cast hpos
  have hpartR : ((residues a b c B p).card:ℝ)+Bad.card=((p:ℝ)^2)^2 := by exact_mod_cast hpart
  have hbad0 : (0:ℝ) ≤ Bad.card := Nat.cast_nonneg _
  simp only [localDensity,Nat.cast_pow]
  refine ⟨div_pos hposR (by positivity),?_,?_⟩
  · exact (div_le_one (by positivity)).mpr (by linarith)
  · have he : 1-((residues a b c B p).card:ℝ)/((p:ℝ)^2)^2=
        (Bad.card:ℝ)/((p:ℝ)^2)^2 := by
      apply (eq_div_iff (by positivity)).mpr
      field_simp
      linarith
    rw [he]
    apply (div_le_iff₀ (by positivity)).mpr
    by_cases hpB : p∈B <;> simp only [hpB,if_true,if_false] at hbad ⊢
    all_goals field_simp; nlinarith only [hbad]

#print axioms density_bounds
end Erdos1206.QuadraticSquareLocal
