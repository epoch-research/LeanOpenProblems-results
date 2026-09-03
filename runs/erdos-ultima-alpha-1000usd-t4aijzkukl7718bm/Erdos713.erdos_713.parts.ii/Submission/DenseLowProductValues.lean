import FormalConjecturesUtil

/-! A dense subset of an odd-order abelian group cannot have too many
product values with at most two representations. Auxiliary finite counting. -/
open Finset
open scoped Pointwise
namespace Erdos713DenseLowProductValues
variable {W : Type*} [CommGroup W] [DecidableEq W]
set_option maxHeartbeats 2000000

def corr (A : Finset W) (x : W) : ℕ := (A ∩ x • A).card

lemma sum_corr [Fintype W] (A : Finset W) : ∑ x : W, corr A x = A.card^2 := by
  simp only [corr,card_inter_smul,Finset.convolution]
  rw [sum_card_fiberwise_eq_card_filter]
  simp [card_product,pow_two]

lemma inv_mem_difference {A : Finset W} {x : W} (hx : x ∈ A*A⁻¹) : x⁻¹ ∈ A*A⁻¹ := by
  obtain ⟨a,ha,z,hz,rfl⟩ := mem_mul.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_inv.mp hz
  exact mem_mul.mpr ⟨b,hb,a⁻¹,mem_inv.mpr ⟨a,ha,rfl⟩,by group⟩

lemma corr_lower_difference (A : Finset W) {x : W} (hx : x ∈ A*A⁻¹) :
    2*A.card ≤ corr A x+(A*A⁻¹).card := by
  obtain ⟨a,ha,z,hz,rfl⟩ := mem_mul.mp hx
  obtain ⟨b,hb,rfl⟩ := mem_inv.mp hz
  have hsub (a : W) (ha : a ∈ A) : a⁻¹ • A ⊆ A*A⁻¹ := by
    intro y hy
    obtain ⟨c,hc,rfl⟩ := mem_smul_finset.mp hy
    exact mem_mul.mpr ⟨c,hc,a⁻¹,mem_inv.mpr ⟨a,ha,rfl⟩,by simp [mul_comm]⟩
  have hu := card_le_card (union_subset (hsub a ha) (hsub b hb))
  have he := card_inter_add_card_union (a⁻¹ • A) (b⁻¹ • A)
  rw [card_smul_finset,card_smul_finset,card_smul_inter_smul] at he
  simp only [inv_inv,← card_inter_smul,corr] at he ⊢
  omega

lemma small_difference_mul_closed (A : Finset W) (h : 2*(A*A⁻¹).card < 3*A.card)
    {x y : W} (hx : x ∈ A*A⁻¹) (hy : y ∈ A*A⁻¹) : x*y ∈ A*A⁻¹ := by
  have hx' := corr_lower_difference A hx
  have hy' := corr_lower_difference A (inv_mem_difference hy)
  have hu : ((A ∩ x • A) ∪ (A ∩ y⁻¹ • A)).card ≤ A.card :=
    card_le_card (union_subset inter_subset_left inter_subset_left)
  have he := card_inter_add_card_union (A ∩ x • A) (A ∩ y⁻¹ • A)
  have hp : 0 < ((A ∩ x • A) ∩ (A ∩ y⁻¹ • A)).card := by
    dsimp only [corr] at hx' hy'
    omega
  obtain ⟨z,hz⟩ := card_pos.mp hp
  obtain ⟨u,hu,huz⟩ := mem_smul_finset.mp (mem_inter.mp (mem_inter.mp hz).1).2
  obtain ⟨v,hv,hvz⟩ := mem_smul_finset.mp (mem_inter.mp (mem_inter.mp hz).2).2
  change x*u=z at huz
  change y⁻¹*v=z at hvz
  have hv' : v = y*(x*u) := by
    calc
      v = y*(y⁻¹*v) := by simp
      _ = _ := by rw [hvz,← huz]
  apply mem_mul.mpr
  refine ⟨v,hv,u⁻¹,mem_inv.mpr ⟨u,hu,rfl⟩,?_⟩
  rw [hv']
  simp [mul_assoc,mul_comm]

/-- The elementary small-difference version of the three-halves lemma. -/
def differenceSubgroup (A : Finset W) (h : 2*(A*A⁻¹).card < 3*A.card) : Subgroup W where
  carrier := ↑(A*A⁻¹)
  one_mem' := by
    have hp : 0 < A.card := by omega
    obtain ⟨a,ha⟩ := card_pos.mp hp
    exact mem_mul.mpr ⟨a,ha,a⁻¹,mem_inv.mpr ⟨a,ha,rfl⟩,mul_inv_cancel a⟩
  inv_mem' := inv_mem_difference
  mul_mem' := small_difference_mul_closed A h

omit [DecidableEq W] in
lemma dense_odd_subgroup_top [Fintype W] (hodd : Odd (Fintype.card W))
    (H : Subgroup W) (hh : Fintype.card W < 3*Nat.card H) : H = ⊤ := by
  have hi : Odd H.index := Odd.of_dvd_nat (by simpa using hodd) H.index_dvd_card
  have hmul := H.card_mul_index
  rw [Nat.card_eq_fintype_card (α := W)] at hmul
  have hpos : 0 < Fintype.card W := Fintype.card_pos
  apply Subgroup.index_eq_one.mp
  obtain ⟨j,hj⟩ := hi
  by_contra hn
  have hthree : 3 ≤ H.index := by omega
  have hx := Nat.mul_le_mul_left (Nat.card H) hthree
  nlinarith

lemma near_complements [Fintype W] (R : Finset W) (a b : W)
    (ha : (R ∩ a • R⁻¹).card ≤ 2) (hb : (R ∩ b • R⁻¹).card ≤ 2) :
    3*R.card ≤ (a • R⁻¹ ∩ b • R⁻¹).card+Fintype.card W+4 := by
  let A := a • R⁻¹
  let B := b • R⁻¹
  have hA : A.card = R.card := by simp [A]
  have hB : B.card = R.card := by simp [B]
  have he := card_inter_add_card_union A B
  have he' := card_inter_add_card_union (A ∪ B) R
  have hh : ((A ∪ B) ∩ R).card ≤ 4 := by
    rw [union_inter_distrib_right]
    have hc := card_union_le (A ∩ R) (B ∩ R)
    have ha' : (A ∩ R).card ≤ 2 := by simpa only [A,inter_comm] using ha
    have hb' : (B ∩ R).card ≤ 2 := by simpa only [B,inter_comm] using hb
    omega
  have hu := ((A ∪ B) ∪ R).card_le_univ
  change 3*R.card ≤ (A ∩ B).card+Fintype.card W+4
  omega

private lemma numerical_small {d r b N : ℕ} (hd : 20 ≤ d) (hdr : d ≤ r)
    (hrN : 2*r ≤ N+2) (hNd : N ≤ 2*d+1)
    (hb : b*r ≤ r^2+5*b) : 2*b < 3*d := by
  have hr : r ≤ d+1 := by omega
  by_contra hnot
  have hbd : 3*d ≤ 2*b := by omega
  zify at hd hdr hr hbd hb
  have h1 : 0 ≤ (2*(b : ℤ)-3*d)*(r-5) := mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ ((r : ℤ)-d)*(3*d) := mul_nonneg (by omega) (by positivity)
  have h3 : 0 ≤ ((d : ℤ)-20)*(d+1) := mul_nonneg (by omega) (by positivity)
  have h4 : (r : ℤ)^2 ≤ (d+1)^2 := by nlinarith
  nlinarith

private lemma numerical_impossible {d r N : ℕ} (hd : 20 ≤ d) (hdr : d ≤ r)
    (hrN : 2*r ≤ N+2) (he : N*r ≤ r^2+5*N) : False := by
  zify at hd hdr hrN he
  have h1 : 0 ≤ ((N : ℤ)-2*r+2)*(r-5) := mul_nonneg (by omega) (by omega)
  have h2 : 0 ≤ ((r : ℤ)-20)*(r+8) := mul_nonneg (by omega) (by positivity)
  nlinarith

/-- There cannot be at least twenty near-half-size low-product values
when the ambient group has odd order. -/
theorem impossible [Fintype W] (R D : Finset W) (hodd : Odd (Fintype.card W))
    (hd : 20 ≤ D.card) (hdr : D.card ≤ R.card)
    (hN : Fintype.card W ≤ 2*D.card+1)
    (hlo : ∀ d ∈ D, (R ∩ d • R⁻¹).card ≤ 2) : False := by
  obtain ⟨d,hdD⟩ := card_pos.mp (show 0 < D.card by omega)
  have hrN : 2*R.card ≤ Fintype.card W+2 := by
    have he := card_inter_add_card_union R (d • R⁻¹)
    have hu := (R ∪ d • R⁻¹).card_le_univ
    have hh := hlo d hdD
    simp only [card_smul_finset,card_inv] at he
    omega
  let B := D*D⁻¹
  have hc : ∀ x ∈ B, R.card ≤ corr R⁻¹ x+5 := by
    intro x hx
    obtain ⟨a,ha,z,hz,rfl⟩ := mem_mul.mp hx
    obtain ⟨b,hb,rfl⟩ := mem_inv.mp hz
    have hh := near_complements R b a (hlo b hb) (hlo a ha)
    rw [card_smul_inter_smul,← card_inter_smul] at hh
    change 3*R.card ≤ corr R⁻¹ (b⁻¹*a)+Fintype.card W+4 at hh
    rw [mul_comm b⁻¹ a] at hh
    omega
  have he : B.card*R.card ≤ R.card^2+5*B.card := by
    have hs := sum_le_sum (s := B) hc
    have hu := sum_le_sum_of_subset_of_nonneg (f := corr R⁻¹) (s := B) (t := Finset.univ)
      (Finset.subset_univ _) (fun x _ _ => Nat.zero_le (corr R⁻¹ x))
    rw [sum_corr,card_inv] at hu
    simp only [sum_add_distrib,sum_const,Nat.nsmul_eq_mul] at hs
    nlinarith
  have hsmall := numerical_small hd hdr hrN hN he
  let H := differenceSubgroup D hsmall
  have hHcard : Nat.card H = B.card := by
    change Nat.card {x : W // x ∈ B} = B.card
    simp only [Nat.card_eq_fintype_card,Fintype.card_coe]
  have hDB : D.card ≤ B.card := by
    have hsub : d⁻¹ • D ⊆ B := by
      intro x hx
      obtain ⟨a,ha,rfl⟩ := mem_smul_finset.mp hx
      exact mem_mul.mpr ⟨a,ha,d⁻¹,mem_inv.mpr ⟨d,hdD,rfl⟩,by simp [mul_comm]⟩
    simpa only [card_smul_finset] using card_le_card hsub
  have htop : H = ⊤ := dense_odd_subgroup_top hodd H (by rw [hHcard]; omega)
  have hBN : B.card = Fintype.card W := by
    rw [← hHcard,htop]
    simp
  rw [hBN] at he
  exact numerical_impossible hd hdr hrN he

#print axioms differenceSubgroup
#print axioms impossible
end Erdos713DenseLowProductValues
