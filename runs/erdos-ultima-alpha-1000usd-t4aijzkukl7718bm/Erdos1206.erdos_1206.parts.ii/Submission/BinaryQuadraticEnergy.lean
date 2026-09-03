import Submission.QuadraticLatticeLines

/-! An equal-value energy estimate for a nondegenerate binary quadratic form.
This is a counting tool, not a solution of Erdős 1206. -/
namespace Erdos1206.BinaryQuadraticEnergy
open Finset QuadraticLatticeLines
open scoped Classical

def energy (a b c : ℤ) (N : ℕ) : Finset (Vec × Vec) :=
  ((box N) ×ˢ (box N)).filter (fun p => form a b c p.1=form a b c p.2)

def directions (j : ℕ) : Finset Vec :=
  (box (2^(j+1))).filter (fun v => Int.gcd v.1 v.2=1 ∧ (2:ℤ)^j ≤ ht v)

def line (a b c : ℤ) (N : ℕ) (v : Vec) (g : ℕ) : Finset Vec :=
  (box N).filter (fun x => leftCoeff a b v*x.1+rightCoeff b c v*x.2=(g:ℤ)*form a b c v)

def pairs (a b c : ℤ) (N : ℕ) (v : Vec) (g : ℕ) : Finset (Vec × Vec) :=
  (line a b c N v g).image (fun x => (x,x-(g:ℤ) • v))

def shell (a b c : ℤ) (k j : ℕ) : Finset (Vec × Vec) :=
  (directions j).biUnion (fun v => (Icc 1 (2^(k+1-j))).biUnion (fun g => pairs a b c (2^k) v g))

lemma ht_smul {g : ℤ} (hg : 0 ≤ g) (v : Vec) : ht (g • v)=g*ht v := by
  simp only [ht,Prod.smul_fst,Prod.smul_snd,smul_eq_mul,abs_mul,abs_of_nonneg hg,
    mul_max_of_nonneg _ _ hg]

lemma ht_sub_le (x y : Vec) : ht (x-y) ≤ ht x+ht y := by
  apply max_le
  · exact (abs_sub _ _).trans (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact (abs_sub _ _).trans (add_le_add (le_max_right _ _) (le_max_right _ _))

lemma equal_form_line {a b c : ℤ} {x y v : Vec} {g : ℕ} (hg : 0 < g)
    (hxy : x-y=(g:ℤ) • v) (he : form a b c x=form a b c y) :
    leftCoeff a b v*x.1+rightCoeff b c v*x.2=(g:ℤ)*form a b c v := by
  have hy : y=x-(g:ℤ) • v := by rw [← hxy]; abel
  rw [hy] at he
  have hid : (g:ℤ)*(leftCoeff a b v*x.1+rightCoeff b c v*x.2-(g:ℤ)*form a b c v)=0 := by
    dsimp [form,leftCoeff,rightCoeff] at *
    linear_combination he
  have hgZ : (g:ℤ) ≠ 0 := by exact_mod_cast hg.ne'
  have hh := (mul_eq_zero.mp hid).resolve_left hgZ
  omega

lemma dyadic_decomposition {k : ℕ} {x y : Vec}
    (hx : x∈box (2^k)) (hy : y∈box (2^k)) (hne : x ≠ y) :
    ∃ j∈range (k+2), ∃ v∈directions j, ∃ g : ℕ, g∈Icc 1 (2^(k+1-j)) ∧
      x-y=(g:ℤ) • v := by
  let w := x-y
  have hw : w ≠ 0 := sub_ne_zero.mpr hne
  have hwp : 0 < Int.gcd w.1 w.2 := by
    by_contra h
    have hz : Int.gcd w.1 w.2=0 := by omega
    obtain ⟨h1,h2⟩ := Int.gcd_eq_zero_iff.mp hz
    exact hw (Prod.ext h1 h2)
  obtain ⟨g,u,v,hg,hcop,hu,hv⟩ := Int.exists_gcd_one' hwp
  let z : Vec := (u,v)
  have hwz : w=(g:ℤ) • z := by
    apply Prod.ext
    · simpa only [z,Prod.smul_fst,smul_eq_mul,mul_comm] using hu
    · simpa only [z,Prod.smul_snd,smul_eq_mul,mul_comm] using hv
  have hz0 : z ≠ 0 := by intro hz; have hh := hwz; rw [hz,smul_zero] at hh; exact hw hh
  have hzp := ht_pos hz0
  have hht : (g:ℤ)*ht z ≤ 2*(2:ℤ)^k := by
    rw [← ht_smul (by positivity),← hwz]
    have h1 := mem_box_iff.mp hx
    have h2 := mem_box_iff.mp hy
    have hh := ht_sub_le x y
    dsimp only [w]
    push_cast at h1 h2
    omega
  have hg1 : (1:ℤ) ≤ g := by exact_mod_cast hg
  have hzbound : ht z ≤ (2:ℤ)^(k+1) := by
    rw [pow_succ]
    nlinarith
  let H := (ht z).toNat
  have hHcast : (H:ℤ)=ht z := Int.toNat_of_nonneg (ht_nonneg z)
  have hHp : 0 < H := by omega
  have hHb : H ≤ 2^(k+1) := by exact_mod_cast (show (H:ℤ) ≤ (2:ℤ)^(k+1) by omega)
  let j := Nat.log 2 H
  have hj : j ≤ k+1 := by
    have hh := Nat.log_mono_right (b := 2) hHb
    simpa only [Nat.log_pow (by decide : 1<2)] using hh
  have hjlo : (2:ℤ)^j ≤ ht z := by
    have hh := Nat.pow_log_le_self 2 hHp.ne'
    rw [← hHcast]
    exact_mod_cast (show (2:ℕ)^j ≤ H from hh)
  have hjhi : ht z < (2:ℤ)^(j+1) := by
    have hh := Nat.lt_pow_succ_log_self (by decide : 1<2) H
    have hhr : (H:ℤ)<(2:ℤ)^(j+1) := by exact_mod_cast hh
    omega
  have hpow : (2:ℤ)^j*2^(k+1-j)=2^(k+1) := by
    rw [← pow_add,Nat.add_sub_of_le hj]
  have hgb : g ≤ 2^(k+1-j) := by
    have hh := mul_le_mul_of_nonneg_left hjlo (show (0:ℤ)≤g by positivity)
    have hh' : (g:ℤ)*(2:ℤ)^j ≤ (2:ℤ)^(k+1) := by rw [pow_succ]; nlinarith
    rw [← hpow] at hh'
    have hres : (g:ℤ) ≤ (2:ℤ)^(k+1-j) := by
      exact (mul_le_mul_iff_left₀ (by positivity : (0:ℤ)<2^j)).mp (by simpa [mul_comm] using hh')
    exact_mod_cast hres
  refine ⟨j,mem_range.mpr (by omega),z,mem_filter.mpr ⟨?_,hcop,hjlo⟩,
    g,mem_Icc.mpr ⟨hg,hgb⟩,hwz⟩
  exact mem_box_iff.mpr (by exact_mod_cast hjhi.le)

lemma energy_cover (a b c : ℤ) (k : ℕ) :
    energy a b c (2^k) ⊆ ((box (2^k)).image (fun x => (x,x))) ∪
      (range (k+2)).biUnion (shell a b c k) := by
  intro p hp
  obtain ⟨hpB,he⟩ := mem_filter.mp hp
  obtain ⟨hx,hy⟩ := mem_product.mp hpB
  by_cases hxy : p.1=p.2
  · exact mem_union_left _ (mem_image.mpr ⟨p.1,hx,Prod.ext rfl hxy⟩)
  · obtain ⟨j,hj,v,hv,g,hg,hvg⟩ := dyadic_decomposition hx hy hxy
    apply mem_union_right
    apply mem_biUnion.mpr
    refine ⟨j,hj,mem_biUnion.mpr ⟨v,hv,mem_biUnion.mpr ⟨g,hg,?_⟩⟩⟩
    apply mem_image.mpr
    refine ⟨p.1,mem_filter.mpr ⟨hx,equal_form_line (mem_Icc.mp hg).1 hvg he⟩,?_⟩
    apply Prod.ext
    · rfl
    · dsimp
      rw [← hvg]
      abel


def coeffBound (a b c : ℤ) : ℕ := (constant a b c).toNat

lemma coeffBound_cast (a b c : ℤ) : (coeffBound a b c:ℤ)=constant a b c :=
  Int.toNat_of_nonneg (constant_pos a b c).le

lemma direction_card_bound (j : ℕ) : (directions j).card ≤ 25*(2^j)^2 := by
  have hh := card_filter_le (box (2^(j+1)))
    (fun v => Int.gcd v.1 v.2=1 ∧ (2:ℤ)^j≤ht v)
  rw [card_box] at hh
  change (directions j).card ≤ (2*2^(j+1)+1)^2 at hh
  have hp : 1 ≤ (2:ℕ)^j := Nat.one_le_pow _ _ (by decide)
  have hle : 2*2^(j+1)+1 ≤ 5*2^j := by rw [pow_succ]; omega
  have hh' := Nat.pow_le_pow_left hle 2
  nlinarith

lemma pairs_card_bound {a b c : ℤ} (hd : 4*a*c-b^2 ≠ 0)
    {k j : ℕ} (hj : j ≤ k+1) {v : Vec} (hv : v∈directions j) (g : ℕ) :
    (pairs a b c (2^k) v g).card ≤ coeffBound a b c*2^(k+1-j)+1 := by
  obtain ⟨_,hcop,hheight⟩ := mem_filter.mp hv
  have hpow : (2:ℤ)^j*2^(k+1-j)=2^(k+1) := by
    rw [← pow_add,Nat.add_sub_of_le hj]
  have hbound : 2*constant a b c*(2^k:ℕ) ≤
      ((coeffBound a b c*2^(k+1-j):ℕ):ℤ)*(2:ℤ)^j := by
    push_cast
    rw [coeffBound_cast]
    calc
      2*constant a b c*2^k = constant a b c*2^(k+1) := by rw [pow_succ]; ring
      _ ≤ _ := by rw [← hpow]; exact le_of_eq (by ring)
  have hh := affine_line_card hd v hcop (2^k) (coeffBound a b c*2^(k+1-j))
    (2^j) ((g:ℤ)*form a b c v) (by positivity) hheight hbound
  exact card_image_le.trans hh

lemma shell_card_bound {a b c : ℤ} (hd : 4*a*c-b^2 ≠ 0)
    {k j : ℕ} (hj : j ≤ k+1) :
    (shell a b c k j).card ≤ 100*(coeffBound a b c+1)*(2^k)^2 := by
  let G := 2^(k+1-j)
  let C := coeffBound a b c
  have hG : 1 ≤ G := Nat.one_le_pow _ _ (by decide)
  have hpow : (2:ℕ)^j*G=2^(k+1) := by
    dsimp [G]
    rw [← pow_add,Nat.add_sub_of_le hj]
  have hper (v : Vec) (hv : v∈directions j) :
      ((Icc 1 G).biUnion (fun g => pairs a b c (2^k) v g)).card ≤ G*(C*G+1) := by
    calc
      _ ≤ ∑ g∈Icc 1 G, (pairs a b c (2^k) v g).card := card_biUnion_le
      _ ≤ ∑ _g∈Icc 1 G, (C*G+1) := sum_le_sum (fun g _ => pairs_card_bound hd hj hv g)
      _ = _ := by simp
  have hGb : G*(C*G+1) ≤ (C+1)*G^2 := by nlinarith
  have heq : 25*(2^j)^2*((C+1)*G^2)=100*(C+1)*(2^k)^2 := by
    calc
      _ = 25*(C+1)*(2^j*G)^2 := by ring
      _ = _ := by rw [hpow,pow_succ]; ring
  calc
    (shell a b c k j).card ≤ ∑ v∈directions j,
        ((Icc 1 G).biUnion (fun g => pairs a b c (2^k) v g)).card := card_biUnion_le
    _ ≤ ∑ _v∈directions j, G*(C*G+1) := sum_le_sum hper
    _ = (directions j).card*(G*(C*G+1)) := by simp
    _ ≤ (25*(2^j)^2)*((C+1)*G^2) := Nat.mul_le_mul (direction_card_bound j) hGb
    _ = _ := heq

/-- The logarithmic loss is explicit on dyadic boxes: the number of pairs of
integer vectors having equal quadratic value is O((k+1) * 4^k). -/
theorem energy_dyadic_bound {a b c : ℤ} (hd : 4*a*c-b^2 ≠ 0) (k : ℕ) :
    (energy a b c (2^k)).card ≤
      (100*(coeffBound a b c+1)+9)*(k+2)*(2^k)^2 := by
  have hp : 1 ≤ (2:ℕ)^k := Nat.one_le_pow _ _ (by decide)
  have hdiag : ((box (2^k)).image (fun x => (x,x))).card ≤ 9*(2^k)^2 := by
    calc
      _ ≤ (box (2^k)).card := card_image_le
      _ = (2*2^k+1)^2 := card_box _
      _ ≤ (3*2^k)^2 := Nat.pow_le_pow_left (by omega) 2
      _ = _ := by ring
  have hshell : ((range (k+2)).biUnion (shell a b c k)).card ≤
      (k+2)*(100*(coeffBound a b c+1)*(2^k)^2) := by
    calc
      _ ≤ ∑ j∈range (k+2), (shell a b c k j).card := card_biUnion_le
      _ ≤ ∑ _j∈range (k+2), 100*(coeffBound a b c+1)*(2^k)^2 := by
        apply sum_le_sum
        intro j hj
        exact shell_card_bound hd (by have := mem_range.mp hj; omega)
      _ = _ := by simp
  have hcover := (card_le_card (energy_cover a b c k)).trans (card_union_le _ _)
  have hmul : 9*(2^k)^2 ≤ 9*(k+2)*(2^k)^2 := by
    nlinarith [show (0:ℕ) ≤ 9*k*(2^k)^2 from Nat.zero_le _]
  nlinarith

#print axioms energy_dyadic_bound
end Erdos1206.BinaryQuadraticEnergy
