import FormalConjecturesUtil

/-!
Divisor bounds for exact product-degenerate four-edge configurations.
Fixing two entries leaves only a divisor-bounded number of completions,
except for the explicitly excluded equal-ratio case. These are finite
arithmetic bounds, not a bound on the full signed prime-label energy.
-/
namespace Erdos371
open Finset
set_option autoImplicit false

/-- A product of two consecutive-number ratios has a divisor factorization.
The factors in the natural-number subtraction are strictly positive. -/
lemma consecutive_product_factorization (L R c d : ℕ)
    (hR : 0 < R) (hLR : R < L) (_hc : 0 < c) (_hd : 0 < d)
    (he : L*c*d = R*(c+1)*(d+1)) :
    R < (L-R)*c ∧ R < (L-R)*d ∧
      ((L-R)*c-R)*((L-R)*d-R) = L*R := by
  let A := L-R
  have hA : 0 < A := Nat.sub_pos_of_lt hLR
  have hAL : A+R=L := Nat.sub_add_cancel hLR.le
  have he' : A*c*d = R*(c+d+1) := by
    rw [← hAL] at he
    nlinarith [he]
  have hxc : R < A*c := by
    by_contra h
    have hm := Nat.mul_le_mul_right d (le_of_not_gt h)
    nlinarith
  have hxd : R < A*d := by
    by_contra h
    have hm := Nat.mul_le_mul_right c (le_of_not_gt h)
    nlinarith
  refine ⟨hxc,hxd,?_⟩
  change (A*c-R)*(A*d-R)=L*R
  have hx : A*c-R+R=A*c := Nat.sub_add_cancel hxc.le
  have hy : A*d-R+R=A*d := Nat.sub_add_cancel hxd.le
  have hxy : (A*c-R+R)*(A*d-R+R)=A*(A*c*d) := by
    rw [hx,hy]
    ring
  rw [he'] at hxy
  have hs : (A*c-R)+(A*d-R)+2*R=A*(c+d) := by nlinarith
  have hsR := congrArg (fun x : ℕ => R*x) hs
  nlinarith

/-- The completion bound is uniform over every finite set of positive pairs;
no upper endpoint is needed in the divisor majorant. -/
theorem consecutive_product_fibre_card_le (L R : ℕ) (hR : 0 < R) (hLR : R < L)
    (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2 ∧ L*z.1*z.2=R*(z.1+1)*(z.2+1)) :
    S.card ≤ (L*R).divisors.card := by
  let A := L-R
  have hA : 0 < A := Nat.sub_pos_of_lt hLR
  have hLR0 : L*R ≠ 0 := mul_ne_zero (by omega) hR.ne'
  have hf (z : ℕ × ℕ) (hz : z ∈ S) :
      R < A*z.1 ∧ R < A*z.2 ∧ (A*z.1-R)*(A*z.2-R)=L*R :=
    consecutive_product_factorization L R z.1 z.2 hR hLR (hS z hz).1
      (hS z hz).2.1 (hS z hz).2.2
  apply card_le_card_of_injOn (fun z : ℕ × ℕ => A*z.1-R)
  · intro z hz
    exact Nat.mem_divisors.mpr ⟨⟨A*z.2-R,(hf z hz).2.2.symm⟩,hLR0⟩
  · intro z hz w hw he
    dsimp only at he
    have hzc : A*z.1-R+R=A*z.1 := Nat.sub_add_cancel (hf z hz).1.le
    have hwc : A*w.1-R+R=A*w.1 := Nat.sub_add_cancel (hf w hw).1.le
    have hc : z.1=w.1 := by
      apply Nat.eq_of_mul_eq_mul_left hA
      omega
    have hx : 0 < A*z.1-R := Nat.sub_pos_of_lt (hf z hz).1
    have hdsub : A*z.2-R=A*w.2-R := by
      apply Nat.eq_of_mul_eq_mul_left hx
      rw [(hf z hz).2.2,he,(hf w hw).2.2]
    have hzd : A*z.2-R+R=A*z.2 := Nat.sub_add_cancel (hf z hz).2.1.le
    have hwd : A*w.2-R+R=A*w.2 := Nat.sub_add_cancel (hf w hw).2.1.le
    have hd : z.2=w.2 := by
      apply Nat.eq_of_mul_eq_mul_left hA
      omega
    exact Prod.ext hc hd

/-- A quotient of consecutive-number ratios has a similar factorization. -/
lemma consecutive_quotient_factorization (L R c d : ℕ)
    (hR : 0 < R) (hLR : R < L) (_hc : 0 < c) (hd : 0 < d)
    (he : L*(c+1)*d = R*c*(d+1)) :
    (L-R)*d < R ∧ ((L-R)*c+L)*(R-(L-R)*d)=L*R := by
  let A := L-R
  have hAL : A+R=L := Nat.sub_add_cancel hLR.le
  have he' : A*c*d+L*d=R*c := by
    rw [← hAL] at he ⊢
    nlinarith [he]
  have hsmall : A*d < R := by
    by_contra h
    have hm := Nat.mul_le_mul_right c (le_of_not_gt h)
    nlinarith
  refine ⟨hsmall,?_⟩
  change (A*c+L)*(R-A*d)=L*R
  have hs : R-A*d+A*d=R := Nat.sub_add_cancel hsmall.le
  have hs' := congrArg (fun x : ℕ => (A*c+L)*x) hs
  have heA := congrArg (fun x : ℕ => A*x) he'
  nlinarith

theorem consecutive_quotient_fibre_card_le_of_lt (L R : ℕ)
    (hR : 0 < R) (hLR : R < L) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2 ∧ L*(z.1+1)*z.2=R*z.1*(z.2+1)) :
    S.card ≤ (L*R).divisors.card := by
  let A := L-R
  have hA : 0 < A := Nat.sub_pos_of_lt hLR
  have hL : 0 < L := hR.trans hLR
  have hLR0 : L*R ≠ 0 := mul_ne_zero hL.ne' hR.ne'
  have hf (z : ℕ × ℕ) (hz : z ∈ S) :
      A*z.2 < R ∧ (A*z.1+L)*(R-A*z.2)=L*R :=
    consecutive_quotient_factorization L R z.1 z.2 hR hLR (hS z hz).1
      (hS z hz).2.1 (hS z hz).2.2
  apply card_le_card_of_injOn (fun z : ℕ × ℕ => A*z.1+L)
  · intro z hz
    exact Nat.mem_divisors.mpr ⟨⟨R-A*z.2,(hf z hz).2.symm⟩,hLR0⟩
  · intro z hz w hw he
    dsimp only at he
    have hc : z.1=w.1 := by
      apply Nat.eq_of_mul_eq_mul_left hA
      omega
    have hx : 0 < A*z.1+L := by positivity
    have hdsub : R-A*z.2=R-A*w.2 := by
      apply Nat.eq_of_mul_eq_mul_left hx
      rw [(hf z hz).2,he,(hf w hw).2]
    have hzd : R-A*z.2+A*z.2=R := Nat.sub_add_cancel (hf z hz).1.le
    have hwd : R-A*w.2+A*w.2=R := Nat.sub_add_cancel (hf w hw).1.le
    have hd : z.2=w.2 := by
      apply Nat.eq_of_mul_eq_mul_left hA
      omega
    exact Prod.ext hc hd

/-- Either strict ordering of the two fixed products gives the same bound.
The equal-product case is essential and is not included. -/
theorem consecutive_quotient_fibre_card_le (L R : ℕ)
    (hL : 0 < L) (hR : 0 < R) (hne : L ≠ R) (S : Finset (ℕ × ℕ))
    (hS : ∀ z ∈ S, 0 < z.1 ∧ 0 < z.2 ∧ L*(z.1+1)*z.2=R*z.1*(z.2+1)) :
    S.card ≤ (L*R).divisors.card := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · let T := S.image Prod.swap
    have hc : T.card=S.card := card_image_of_injective _ Prod.swap_injective
    have hT (z : ℕ × ℕ) (hz : z ∈ T) :
        0 < z.1 ∧ 0 < z.2 ∧ R*(z.1+1)*z.2=L*z.1*(z.2+1) := by
      obtain ⟨w,hw,rfl⟩ := mem_image.mp hz
      obtain ⟨h1,h2,he⟩ := hS w hw
      refine ⟨h2,h1,?_⟩
      dsimp only [Prod.swap]
      nlinarith [he]
    have h := consecutive_quotient_fibre_card_le_of_lt R L hL hlt T hT
    rwa [hc,Nat.mul_comm R L] at h
  · exact consecutive_quotient_fibre_card_le_of_lt L R hR hgt S hS

/-- Two forward and two backward consecutive-number ratios. -/
theorem balanced_four_product_completions (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*(b+1)*z.1*z.2=a*b*(z.1+1)*(z.2+1)).card ≤
        (a*b*(a+1)*(b+1)).divisors.card := by
  have h := consecutive_product_fibre_card_le ((a+1)*(b+1)) (a*b) (by positivity)
    (by nlinarith) (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*(b+1)*z.1*z.2=a*b*(z.1+1)*(z.2+1)) (by
        intro z hz
        obtain ⟨hz,he⟩ := mem_filter.mp hz
        obtain ⟨hc,hd⟩ := mem_product.mp hz
        exact ⟨(mem_Icc.mp hc).1,(mem_Icc.mp hd).1,he⟩)
  convert h using 2
  congr 1
  ring

/-- Alternating traversal directions. The equality a=b would allow every
completion c=d; this genuine diagonal degeneracy is excluded explicitly. -/
theorem alternating_four_product_completions (a b N : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*b*(z.1+1)*z.2=a*(b+1)*z.1*(z.2+1)).card ≤
        (a*b*(a+1)*(b+1)).divisors.card := by
  have h := consecutive_quotient_fibre_card_le ((a+1)*b) (a*(b+1))
    (by positivity) (by positivity) (by intro he; apply hab; nlinarith)
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*b*(z.1+1)*z.2=a*(b+1)*z.1*(z.2+1)) (by
        intro z hz
        obtain ⟨hz,he⟩ := mem_filter.mp hz
        obtain ⟨hc,hd⟩ := mem_product.mp hz
        exact ⟨(mem_Icc.mp hc).1,(mem_Icc.mp hd).1,he⟩)
  convert h using 2
  congr 1
  ring


/-- Three forward ratios and one backward ratio give the same divisor
budget after fixing the first two forward entries. -/
theorem three_forward_product_completions (a b N : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*(b+1)*(z.1+1)*z.2=a*b*z.1*(z.2+1)).card ≤
        (a*b*(a+1)*(b+1)).divisors.card := by
  have h := consecutive_quotient_fibre_card_le_of_lt ((a+1)*(b+1)) (a*b)
    (by positivity) (by nlinarith)
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*(b+1)*(z.1+1)*z.2=a*b*z.1*(z.2+1)) (by
        intro z hz
        obtain ⟨hz,he⟩ := mem_filter.mp hz
        obtain ⟨hc,hd⟩ := mem_product.mp hz
        exact ⟨(mem_Icc.mp hc).1,(mem_Icc.mp hd).1,he⟩)
  convert h using 2
  congr 1
  ring

lemma alternating_equal_ratio_iff (a c d : ℕ) (ha : 0 < a) :
    (a+1)*a*(c+1)*d=a*(a+1)*c*(d+1) ↔ c=d := by
  constructor
  · intro he
    have hA : 0 < a*(a+1) := by positivity
    have he' : a*(a+1)*((c+1)*d)=a*(a+1)*(c*(d+1)) := by
      convert he using 1 <;> ring
    have hh := Nat.eq_of_mul_eq_mul_left hA he'
    nlinarith
  · rintro rfl
    ring

/-- The omitted equal-ratio case has exactly N completions in the box, not
an endpoint-independent divisor bound. -/
theorem alternating_equal_ratio_completions (a N : ℕ) (ha : 0 < a) :
    (((Icc 1 N) ×ˢ (Icc 1 N)).filter fun z : ℕ × ℕ =>
      (a+1)*a*(z.1+1)*z.2=a*(a+1)*z.1*(z.2+1)).card=N := by
  simp_rw [alternating_equal_ratio_iff a _ _ ha]
  have he : ((Icc 1 N) ×ˢ (Icc 1 N)).filter (fun z : ℕ × ℕ => z.1=z.2) =
      (Icc 1 N).diag := by
    ext z
    simp only [mem_filter,mem_product,mem_diag]
    aesop
  rw [he,diag_card]
  simp

#print axioms consecutive_product_fibre_card_le
#print axioms consecutive_quotient_fibre_card_le
#print axioms balanced_four_product_completions
#print axioms alternating_four_product_completions
#print axioms three_forward_product_completions
#print axioms alternating_equal_ratio_completions
end Erdos371
