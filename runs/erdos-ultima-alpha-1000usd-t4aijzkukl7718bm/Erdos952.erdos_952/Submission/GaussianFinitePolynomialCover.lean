import Submission.GaussianPolynomialShortEdges
import Submission.GaussianPathLargerSieve

/-! Uniform finite-segment bounds for finite unions of nonlinear Gaussian
polynomial images. The bounds are independent of the polynomial coefficients.
No inverse-sieve theorem classifying prime paths by such images is asserted. -/
namespace Erdos952Investigation.GaussianFinitePolynomialCover
open GaussianPolynomialImageObstruction GaussianPolynomialShortEdges GaussianPathLargerSieve
open scoped BigOperators Classical
set_option maxHeartbeats 0
noncomputable section

lemma norm_forward_displacement_le_on_segment (x : ℕ → GaussianInt) (C : ℤ) (L : ℕ)
    (hs : ∀ n < L, (x (n+1)-x n).norm ≤ C) (i h : ℕ) (hih : i+h ≤ L) :
    (x (i+h)-x i).norm ≤ C*(h : ℤ)^2 := by
  have he := Finset.sum_range_sub (fun j => x (i+j)) h
  simp only [Nat.add_zero] at he
  have hh := norm_sum_le_card_mul_sum_norm (Finset.range h)
    (fun j => x (i+(j+1))-x (i+j))
  rw [he,Finset.card_range] at hh
  have hb : (∑ j ∈ Finset.range h, (x (i+(j+1))-x (i+j)).norm) ≤ (h : ℤ)*C := by
    calc
      _ ≤ ∑ _j ∈ Finset.range h, C := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' : j < h := Finset.mem_range.mp hj
        simpa only [Nat.add_assoc] using hs (i+j) (by omega)
      _ = _ := by simp
  calc
    _ ≤ (h : ℤ)*(∑ j ∈ Finset.range h, (x (i+(j+1))-x (i+j)).norm) := hh
    _ ≤ (h : ℤ)*((h : ℤ)*C) := mul_le_mul_of_nonneg_left hb (Int.natCast_nonneg h)
    _ = _ := by ring

lemma norm_displacement_le_on_segment (x : ℕ → GaussianInt) (C : ℤ) (L : ℕ)
    (hs : ∀ n < L, (x (n+1)-x n).norm ≤ C) (i j : ℕ) (hi : i ≤ L) (hj : j ≤ L) :
    (x i-x j).norm ≤ C*((i : ℤ)-(j : ℤ))^2 := by
  rcases le_total i j with hij | hji
  · calc
      _ = (x j-x i).norm := norm_sub_swap _ _
      _ ≤ C*((j-i : ℕ) : ℤ)^2 := by
        have hh := norm_forward_displacement_le_on_segment x C L hs i (j-i) (by omega)
        simpa only [Nat.add_sub_of_le hij] using hh
      _ = _ := by rw [Nat.cast_sub hij]; ring
  · calc
      _ ≤ C*((i-j : ℕ) : ℤ)^2 := by
        have hh := norm_forward_displacement_le_on_segment x C L hs j (i-j) (by omega)
        simpa only [Nat.add_sub_of_le hji] using hh
      _ = _ := by rw [Nat.cast_sub hji]

lemma norm_block_difference_le (x : ℕ → GaussianInt) (C : ℤ) (hC : 0 ≤ C) (L : ℕ)
    (hs : ∀ n < L, (x (n+1)-x n).norm ≤ C) (N K i j : ℕ)
    (hi : i ≤ K) (hj : j ≤ K) (hb : N+K ≤ L) :
    (x (N+j)-x (N+i)).norm ≤ C*(K : ℤ)^2 := by
  have hh := norm_displacement_le_on_segment x C L hs (N+j) (N+i) (by omega) (by omega)
  have hm : -((K : ℤ)) ≤ ((N+j : ℕ) : ℤ)-((N+i : ℕ) : ℤ) ∧
      ((N+j : ℕ) : ℤ)-((N+i : ℕ) : ℤ) ≤ K := by omega
  have hsq : (((N+j : ℕ) : ℤ)-((N+i : ℕ) : ℤ))^2 ≤ (K : ℤ)^2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm.2) (sub_nonneg.mpr hm.1)]
  exact hh.trans (mul_le_mul_of_nonneg_left hsq hC)

lemma block_index_div (K b : ℕ) (i : Fin (K+1)) :
    (b*(K+1)+i.val)/(K+1) = b := by
  rw [Nat.mul_comm b, Nat.mul_add_div (by omega),Nat.div_eq_of_lt i.isLt,Nat.add_zero]

/-- In a block longer than the number of polynomial images, two vertices
must belong to the same image. Their bounded separation puts one vertex
in the finite close-pair certificate. -/
lemma block_hits_certificate {J : Type*} [Fintype J]
    (P : J → Polynomial GaussianInt) (hP : ∀ j, 2 ≤ (P j).natDegree)
    (x : ℕ → GaussianInt) (C : ℤ) (hC : 0 ≤ C) (L : ℕ)
    (hx : Set.InjOn x (Set.Iic L))
    (hp : ∀ n ≤ L, ∃ j, x n ∈ Set.range (P j).eval)
    (hs : ∀ n < L, (x (n+1)-x n).norm ≤ C)
    (N : ℕ) (hN : N+Fintype.card J ≤ L) :
    ∃ i : Fin (Fintype.card J+1),
      x (N+i.val) ∈ familyCertificate P (C*(Fintype.card J : ℤ)^2) := by
  have hm (i : Fin (Fintype.card J+1)) : ∃ j, x (N+i.val) ∈ Set.range (P j).eval :=
    hp (N+i.val) (by omega)
  choose c hc using hm
  have hn : ¬ Function.Injective c := by
    intro hi
    have hh := Fintype.card_le_of_injective c hi
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨i,j,hij,hne⟩ := Function.not_injective_iff.mp hn
  refine ⟨i,?_⟩
  apply mem_familyCertificate P hP _ (c i) _ _ (hc i)
  · simpa only [hij] using hc j
  · intro he
    apply hne
    apply Fin.ext
    have hh := hx (by change N+i.val ≤ L; omega) (by change N+j.val ≤ L; omega) he
    omega
  · exact norm_block_difference_le x C hC L hs N (Fintype.card J) i.val j.val
      (by omega) (by omega) hN

/-- Uniformity includes the coefficients: only the degree bound, number of
images and squared jump bound affect M. This is a finite-union result, not
an inference from separate no-ray statements for the individual images. -/
theorem uniform_polynomial_cover_segment_bound {J : Type*} [Fintype J]
    (d : ℕ) (C : ℤ) : ∃ M : ℕ,
    ∀ P : J → Polynomial GaussianInt,
      (∀ j, 2 ≤ (P j).natDegree ∧ (P j).natDegree ≤ d) →
    ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, ∃ j, x n ∈ Set.range (P j).eval) →
      (∀ n < L, (x (n+1)-x n).norm ≤ C) → L < M := by
  let K := Fintype.card J
  let C' := max C 0
  let B := C'*(K : ℤ)^2
  let Q := K*((ball B).card^2*d)
  refine ⟨(Q+1)*(K+1),?_⟩
  intro P hP x L hx hp hs
  by_contra! hlong
  let E := familyCertificate P B
  have hE : E.card ≤ Q := familyCertificate_card_le P d (fun j => (hP j).2) B
  have hs' (n : ℕ) (hn : n < L) : (x (n+1)-x n).norm ≤ C' :=
    (hs n hn).trans (le_max_left _ _)
  have hindex (b : Fin (E.card+1)) (i : Fin (K+1)) : b.val*(K+1)+i.val ≤ L := by
    have hmul := Nat.mul_le_mul_right (K+1) (show b.val+1 ≤ Q+1 by omega)
    nlinarith [i.isLt]
  have hblock (b : Fin (E.card+1)) :
      ∃ i : Fin (K+1), x (b.val*(K+1)+i.val) ∈ E := by
    apply block_hits_certificate P (fun j => (hP j).1) x C' (le_max_right _ _) L hx hp hs'
    exact hindex b (Fin.last K)
  choose a ha using hblock
  let f : Fin (E.card+1) → E := fun b => ⟨x (b.val*(K+1)+(a b).val),ha b⟩
  have hf : Function.Injective f := by
    intro b c he
    have he' : x (b.val*(K+1)+(a b).val) = x (c.val*(K+1)+(a c).val) :=
      congrArg Subtype.val he
    have hidx := hx (hindex b (a b)) (hindex c (a c)) he'
    have hd := congrArg (fun n => n/(K+1)) hidx
    dsimp only at hd
    rw [block_index_div,block_index_div] at hd
    exact Fin.ext hd
  have hcard := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin,Fintype.card_coe] at hcard
  omega

/-- The same coefficient-independent bound applies to finite unions of
fixed-width neighborhoods: offsets are absorbed into the constant terms. -/
theorem uniform_polynomial_neighborhood_cover_segment_bound {J : Type*} [Fintype J]
    (d : ℕ) (B C : ℤ) : ∃ M : ℕ,
    ∀ P : J → Polynomial GaussianInt,
      (∀ j, 2 ≤ (P j).natDegree ∧ (P j).natDegree ≤ d) →
    ∀ x : ℕ → GaussianInt, ∀ L : ℕ,
      Set.InjOn x (Set.Iic L) →
      (∀ n ≤ L, ∃ j u, (x n-(P j).eval u).norm ≤ B) →
      (∀ n < L, (x (n+1)-x n).norm ≤ C) → L < M := by
  let T := {t : GaussianInt // t.norm ≤ B}
  letI : Fintype T := (norm_sublevel_finite B).fintype
  obtain ⟨M,hM⟩ := uniform_polynomial_cover_segment_bound (J := J × T) d C
  refine ⟨M,?_⟩
  intro P hP x L hx hp hs
  let Q : J × T → Polynomial GaussianInt := fun j => P j.1+Polynomial.C j.2.val
  have hQ (j : J × T) : 2 ≤ (Q j).natDegree ∧ (Q j).natDegree ≤ d := by
    simpa only [Q,Polynomial.natDegree_add_C] using hP j.1
  apply hM Q hQ x L hx _ hs
  intro n hn
  obtain ⟨j,u,hu⟩ := hp n hn
  refine ⟨(j,⟨x n-(P j).eval u,hu⟩),u,?_⟩
  simp only [Q,Polynomial.eval_add,Polynomial.eval_C]
  abel

/-- No injective bounded-step path can lie in any finite union of fixed-width
nonlinear polynomial neighborhoods. The statement is independent of primes. -/
theorem no_injective_polynomial_neighborhood_cover {J : Type*} [Fintype J]
    (P : J → Polynomial GaussianInt) (hP : ∀ j, 2 ≤ (P j).natDegree)
    (B C : ℤ) (x : ℕ → GaussianInt) (hx : Function.Injective x)
    (hs : ∀ n, (x (n+1)-x n).norm ≤ C) :
    ¬ ∀ n, ∃ j u, (x n-(P j).eval u).norm ≤ B := by
  intro hp
  let d := (Finset.univ : Finset J).sup (fun j => (P j).natDegree)
  obtain ⟨M,hM⟩ := uniform_polynomial_neighborhood_cover_segment_bound (J := J) d B C
  have hh := hM P (fun j => ⟨hP j,Finset.le_sup (f := fun j => (P j).natDegree) (Finset.mem_univ j)⟩) x M hx.injOn
    (fun n _ => hp n) (fun n _ => hs n)
  omega

#print axioms uniform_polynomial_neighborhood_cover_segment_bound
#print axioms no_injective_polynomial_neighborhood_cover
#print axioms norm_displacement_le_on_segment
#print axioms block_hits_certificate
#print axioms uniform_polynomial_cover_segment_bound
end
end Erdos952Investigation.GaussianFinitePolynomialCover
