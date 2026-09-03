import Submission.PrimeLoserCollisionPatterns
import Submission.CofactorTripleSummation

/-! A uniform dimension-three sieve bound for actual prime-loser collisions.
The estimate is useful at a boundary scale and does not assert bulk cancellation. -/
namespace Erdos371
open Finset FiniteSieve

lemma primeLoserCollisionFiber_sieve_bound (B N k l a b X z : ℕ) (e d : ℤ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hk : k ∈ Icc 1 X) (hl : l ∈ Icc 1 X)
    (ha : a ∈ Icc 1 X) (hb : b ∈ Icc 1 X)
    (he : e.natAbs=1) (hd : d.natAbs=1) :
    ((primeLoserCollisionFiber B N k l a b e d).card : ℝ) ≤
      2*Real.exp 3*Real.exp (3*primeHarmonic (3+2*X^2))*(N/(max k l)+1 : ℕ)/
        ((a.lcm b : ℕ)*(Real.log (z+1 : ℝ))^3)+
      2*((a.lcm b : ℕ) : ℝ)^8*(z+1 : ℝ)^96 := by
  classical
  by_cases hnon : (primeLoserCollisionFiber B N k l a b e d).Nonempty
  · obtain ⟨nm,hnm⟩ := hnon
    obtain ⟨hnm,hk',hl',ha',hb',he',hd'⟩ := mem_filter.mp hnm
    have hdet := primeLoserCollisions_det_ne_zero B N nm.1 nm.2 hB hnm
    rw [hk',hl',he',hd'] at hdet
    exact ((Nat.cast_le (α := ℝ)).mpr (primeLoserCollisionFiber_card_le_pattern B N k l a b z e d
      hB hzB (mem_Icc.mp hk).1)).trans
        (threePrimePatternSet_sieve_bound _ k l a b X z e d hk hl ha hb hz he hd hdet)
  · rw [not_nonempty_iff_eq_empty.mp hnon,card_empty,Nat.cast_zero]
    have hlog : 0 ≤ Real.log (z+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
    positivity

abbrev CollisionCoordinates := ℕ × ℕ × ℕ × ℕ × ℤ × ℤ

def collisionCoordinates (nm : ℕ × ℕ) : CollisionCoordinates :=
  (loserIncidenceCofactor nm.1,loserIncidenceCofactor nm.2,
    winnerIncidenceCofactor nm.1,winnerIncidenceCofactor nm.2,
      incidenceShift nm.1,incidenceShift nm.2)

def collisionCoordinateBox (X : ℕ) : Finset CollisionCoordinates :=
  Icc 1 X ×ˢ (Icc 1 X ×ˢ (Icc 1 X ×ˢ (Icc 1 X ×ˢ
    (({1,-1} : Finset ℤ) ×ˢ ({1,-1} : Finset ℤ)))))

lemma collisionCoordinates_mapsTo (B N X : ℕ) (hB : 1 ≤ B) (hX : N/(B+1) ≤ X) :
    ∀ nm ∈ primeLoserCollisions B N, collisionCoordinates nm ∈ collisionCoordinateBox X := by
  intro nm hnm
  obtain ⟨hnm,_⟩ := mem_filter.mp hnm
  obtain ⟨hn,hm,_⟩ := mem_offDiag.mp hnm
  have hd₁ := loserIncidence_cofactor_bounds B N nm.1 hB hn
  have hd₂ := loserIncidence_cofactor_bounds B N nm.2 hB hm
  have hsub : Icc 1 (N/(B+1)) ⊆ Icc 1 X := Icc_subset_Icc_right hX
  have hs (n : ℕ) : incidenceShift n ∈ ({1,-1} : Finset ℤ) := by
    simpa only [mem_insert,mem_singleton] using incidenceShift_cases n
  exact mem_product.mpr ⟨hsub hd₁.1,mem_product.mpr ⟨hsub hd₂.1,
    mem_product.mpr ⟨hsub hd₁.2,mem_product.mpr ⟨hsub hd₂.2,
      mem_product.mpr ⟨hs nm.1,hs nm.2⟩⟩⟩⟩⟩

lemma collisionCoordinates_fiber (B N : ℕ) (t : CollisionCoordinates) :
    (primeLoserCollisions B N).filter (fun nm => collisionCoordinates nm=t) =
      primeLoserCollisionFiber B N t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2 := by
  rcases t with ⟨k,l,a,b,e,d⟩
  ext nm
  simp only [primeLoserCollisionFiber,mem_filter,collisionCoordinates,Prod.mk.injEq]

lemma primeLoserCollisions_card_fiber_sum (B N X : ℕ) (hB : 1 ≤ B) (hX : N/(B+1) ≤ X) :
    ((primeLoserCollisions B N).card : ℝ) =
      ∑ t ∈ collisionCoordinateBox X,
        ((primeLoserCollisionFiber B N t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2).card : ℝ) := by
  have hh := card_eq_sum_card_fiberwise (f := collisionCoordinates) (s := primeLoserCollisions B N)
    (t := collisionCoordinateBox X) (fun nm hnm => collisionCoordinates_mapsTo B N X hB hX nm hnm)
  simp_rw [collisionCoordinates_fiber] at hh
  exact_mod_cast hh

lemma primeLoserCollisionFiber_simple_bound (B N k l a b X z : ℕ) (e d : ℤ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B) (hXN : X ≤ N)
    (hk : k ∈ Icc 1 X) (hl : l ∈ Icc 1 X)
    (ha : a ∈ Icc 1 X) (hb : b ∈ Icc 1 X)
    (he : e.natAbs=1) (hd : d.natAbs=1) :
    ((primeLoserCollisionFiber B N k l a b e d).card : ℝ) ≤
      (4*Real.exp 3*Real.exp (3*primeHarmonic (3+2*X^2))*N/(Real.log (z+1 : ℝ))^3)*
        ((1 : ℝ)/(max k l : ℕ))*((1 : ℝ)/(a.lcm b))+
          2*(X : ℝ)^16*(z+1 : ℝ)^96 := by
  have hmax0 : 0 < max k l := lt_max_of_lt_left (mem_Icc.mp hk).1
  have hmaxN : max k l ≤ N := (max_le (mem_Icc.mp hk).2 (mem_Icc.mp hl).2).trans hXN
  have hmaxR : (0 : ℝ)<(max k l : ℕ) := by exact_mod_cast hmax0
  have hT : ((N/(max k l)+1 : ℕ) : ℝ) ≤ 2*(N : ℝ)/(max k l : ℕ) := by
    have hf := Nat.cast_div_le (α := ℝ) (m := N) (n := max k l)
    have hh : (1 : ℝ) ≤ (N : ℝ)/(max k l : ℕ) :=
      (le_div_iff₀ hmaxR).mpr (by exact_mod_cast (by simpa using hmaxN))
    simp only [Nat.cast_add,Nat.cast_one,mul_div_assoc]
    linarith
  have hlcm : a.lcm b ≤ X^2 := (Nat.lcm_le_mul (mem_Icc.mp ha).1 (mem_Icc.mp hb).1).trans
    (by nlinarith [Nat.mul_le_mul (mem_Icc.mp ha).2 (mem_Icc.mp hb).2])
  have hlcmR : ((a.lcm b : ℕ) : ℝ)^8 ≤ (X : ℝ)^16 := by
    have hh : ((a.lcm b : ℕ) : ℝ) ≤ (X : ℝ)^2 := by exact_mod_cast hlcm
    simpa only [← pow_mul,Nat.reduceMul] using pow_le_pow_left₀ (Nat.cast_nonneg _) hh 8
  have hlog : 0 ≤ Real.log (z+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hC : 0 ≤ 2*Real.exp 3*Real.exp (3*primeHarmonic (3+2*X^2)) := by positivity
  have hmain := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hT hC)
    (show 0 ≤ ((a.lcm b : ℕ) : ℝ)*(Real.log (z+1 : ℝ))^3 by positivity)
  have herr := mul_le_mul_of_nonneg_right hlcmR (show (0 : ℝ) ≤ 2*(z+1 : ℝ)^96 by positivity)
  apply (primeLoserCollisionFiber_sieve_bound B N k l a b X z e d hB hz hzB hk hl ha hb he hd).trans
  apply add_le_add
  · convert hmain using 1; simp only [div_eq_mul_inv,mul_inv_rev]; ring
  · nlinarith

/-- A finite, uniform upper bound obtained by sieving three distinct prime
values and summing their actual cofactor fibers. -/
theorem primeLoserCollisions_sieve_bound (B N X z : ℕ)
    (hB : 1 ≤ B) (hz : 1 ≤ z) (hzB : z ≤ B)
    (hX : N/(B+1) ≤ X) (hXN : X ≤ N) :
    ((primeLoserCollisions B N).card : ℝ) ≤
      32*Real.exp 3*Real.exp (3*primeHarmonic (3+2*X^2))*N*X*(harmonic X : ℝ)^3/
        (Real.log (z+1 : ℝ))^3+8*(X : ℝ)^20*(z+1 : ℝ)^96 := by
  let C : ℝ := 4*Real.exp 3*Real.exp (3*primeHarmonic (3+2*X^2))*N/(Real.log (z+1 : ℝ))^3
  let E : ℝ := 2*(X : ℝ)^16*(z+1 : ℝ)^96
  let A : ℝ := ∑ k ∈ Icc 1 X, ∑ l ∈ Icc 1 X, (1 : ℝ)/(max k l : ℕ)
  let L : ℝ := ∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, (1 : ℝ)/(a.lcm b)
  have hlog : 0 ≤ Real.log (z+1 : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hpoint (t : CollisionCoordinates) (ht : t ∈ collisionCoordinateBox X) :
      ((primeLoserCollisionFiber B N t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2).card : ℝ) ≤
        C*((1 : ℝ)/(max t.1 t.2.1 : ℕ))*((1 : ℝ)/(t.2.2.1.lcm t.2.2.2.1))+E := by
    obtain ⟨hk,hl,ha,hb,he,hd⟩ := by
      simpa only [collisionCoordinateBox,mem_product] using ht
    have hes : t.2.2.2.2.1.natAbs=1 := by
      rcases mem_insert.mp he with he | he
      · rw [he]; norm_num
      · rw [mem_singleton.mp he]; norm_num
    have hds : t.2.2.2.2.2.natAbs=1 := by
      rcases mem_insert.mp hd with hd | hd
      · rw [hd]; norm_num
      · rw [mem_singleton.mp hd]; norm_num
    exact primeLoserCollisionFiber_simple_bound B N _ _ _ _ X z _ _ hB hz hzB hXN hk hl ha hb hes hds
  rw [primeLoserCollisions_card_fiber_sum B N X hB hX]
  apply (sum_le_sum hpoint).trans
  have heval : (∑ t ∈ collisionCoordinateBox X,
      (C*((1 : ℝ)/(max t.1 t.2.1 : ℕ))*((1 : ℝ)/(t.2.2.1.lcm t.2.2.2.1))+E)) =
        4*C*A*L+4*(X : ℝ)^4*E := by
    simp only [collisionCoordinateBox,sum_product,sum_const,card_product,Nat.cast_mul,
      show ({1,-1} : Finset ℤ).card=2 from by decide,Nat.card_Icc,Nat.add_sub_cancel,
      nsmul_eq_mul,Nat.cast_ofNat,sum_add_distrib,← mul_sum,← sum_mul]
    dsimp [A,L]
    ring
  rw [heval]
  have hA := sum_reciprocal_max_le X
  have hL' := sum_reciprocal_lcm_le_harmonic_cube X
  have hAL : A*L ≤ (2*X : ℝ)*(harmonic X : ℝ)^3 :=
    mul_le_mul hA hL' hL (by positivity)
  have hmain := mul_le_mul_of_nonneg_left hAL (show 0 ≤ 4*C by positivity)
  convert add_le_add_right hmain (4*(X : ℝ)^4*E) using 1 <;> dsimp only [C,E] <;> ring

#print axioms primeLoserCollisionFiber_simple_bound
#print axioms primeLoserCollisions_sieve_bound
end Erdos371
