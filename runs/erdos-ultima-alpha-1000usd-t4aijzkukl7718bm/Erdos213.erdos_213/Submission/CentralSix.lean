import FormalConjecturesUtil

/-!
# Erdős Problem 213

*Reference:* [erdosproblems.com/213](https://www.erdosproblems.com/213)
-/

open EuclideanGeometry

namespace Erdos213

/--
The predicate (on $n$) that there exist $n$ points in $\mathbb{R}^2$,
no three on a line and no four on a circle,
such that all pairwise distances are integers.
-/
def Erdos213For (n : ℕ) : Prop := ∃ S : Set ℝ², S.Finite ∧ S.ncard = n ∧
    NonTrilinear S ∧
    (∀ Q : Set ℝ², Q ⊆ S ∧ Q.ncard = 4 → ¬ EuclideanGeometry.Cospherical Q) ∧
    (S.Pairwise fun p₁ p₂ => dist p₁ p₂ ∈ Set.range Int.cast)

lemma Erdos213For.mono {m n : ℕ} (h : Erdos213For n) (hmn : m ≤ n) :
    Erdos213For m := by
  rcases h with ⟨S, hfin, hcard, htri, hcirc, hdist⟩
  obtain ⟨T, hTS, hTcard⟩ := Set.exists_subset_card_eq (hcard ▸ hmn)
  exact ⟨T, hfin.subset hTS, hTcard, htri.mono hTS,
    fun Q hQ => hcirc Q ⟨hQ.1.trans hTS, hQ.2⟩, hdist.mono hTS⟩

private lemma collinear_det_zero {a b c : ℝ²} (h : Collinear ℝ {a, b, c}) :
    (b 0 - a 0) * (c 1 - a 1) - (b 1 - a 1) * (c 0 - a 0) = 0 := by
  obtain ⟨v, hv⟩ := (collinear_iff_of_mem (by simp : a ∈ ({a,b,c} : Set ℝ²))).mp h
  obtain ⟨r, hr⟩ := hv b (by simp)
  obtain ⟨s, hs⟩ := hv c (by simp)
  subst b c
  simp
  ring

private lemma p4_dist_sq (a b : ℝ²) :
    dist a b ^ 2 = (a 0 - b 0)^2 + (a 1 - b 1)^2 := by
  simp [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq]

private def det3 {R : Type*} [CommRing R] (a b c d e f g h i : R) : R :=
  a*(e*i-f*h) - b*(d*i-f*g) + c*(d*h-e*g)

private noncomputable def latticePoint (D : ℕ) (x y : ℤ) : ℝ² := !₂[(x : ℝ), (y : ℝ)*Real.sqrt D]

private def latticeNorm (D : ℕ) (x y x' y' : ℤ) : ℤ :=
  (x-x')^2 + (D : ℤ)*(y-y')^2

private def latticeTriangle (x y : Fin n → ℤ) (i j k : Fin n) : ℤ :=
  (x j-x i)*(y k-y i) - (y j-y i)*(x k-x i)

private def latticeCircle (D : ℕ) (x y : Fin n → ℤ) (i j k l : Fin n) : ℤ :=
  det3 (x j-x i) (y j-y i) (latticeNorm D (x i) (y i) (x j) (y j))
    (x k-x i) (y k-y i) (latticeNorm D (x i) (y i) (x k) (y k))
    (x l-x i) (y l-y i) (latticeNorm D (x i) (y i) (x l) (y l))

private lemma latticePoint_dist_sq (D : ℕ) (x y x' y' : ℤ) :
    dist (latticePoint D x y) (latticePoint D x' y')^2 = (latticeNorm D x y x' y' : ℝ) := by
  rw [p4_dist_sq]
  simp only [latticePoint, PiLp.toLp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    latticeNorm]
  push_cast
  linear_combination ((y : ℝ)-y')^2 * (Real.sq_sqrt (show 0 ≤ (D : ℝ) by positivity))

private lemma lattice_not_collinear {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k : Fin n} (ht : latticeTriangle x y i j k ≠ 0) :
    ¬Collinear ℝ {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k)} := by
  intro h
  have hz := collinear_det_zero h
  have hz' : (latticeTriangle x y i j k : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeTriangle]
    ring
  have hn : (latticeTriangle x y i j k : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma cospherical_det_zero {a b c d : ℝ²} (h : Cospherical {a,b,c,d}) :
    det3 (b 0-a 0) (b 1-a 1) (dist a b^2)
      (c 0-a 0) (c 1-a 1) (dist a c^2)
      (d 0-a 0) (d 1-a 1) (dist a d^2) = 0 := by
  obtain ⟨o,r,h⟩ := h
  have ha := congrArg (fun z : ℝ => z^2) (h a (by simp))
  have hb := congrArg (fun z : ℝ => z^2) (h b (by simp))
  have hc := congrArg (fun z : ℝ => z^2) (h c (by simp))
  have hd := congrArg (fun z : ℝ => z^2) (h d (by simp))
  simp only [p4_dist_sq] at ha hb hc hd ⊢
  unfold det3
  linear_combination
    ((c 0-a 0)*(d 1-a 1)-(d 0-a 0)*(c 1-a 1)) * (hb-ha) +
    ((d 0-a 0)*(b 1-a 1)-(b 0-a 0)*(d 1-a 1)) * (hc-ha) +
    ((b 0-a 0)*(c 1-a 1)-(c 0-a 0)*(b 1-a 1)) * (hd-ha)

private lemma lattice_not_cospherical {D : ℕ} (hD : 0 < D) {x y : Fin n → ℤ}
    {i j k l : Fin n} (ht : latticeCircle D x y i j k l ≠ 0) :
    ¬Cospherical {latticePoint D (x i) (y i), latticePoint D (x j) (y j),
      latticePoint D (x k) (y k), latticePoint D (x l) (y l)} := by
  intro h
  have hz := cospherical_det_zero h
  simp only [latticePoint_dist_sq] at hz
  have hz' : (latticeCircle D x y i j k l : ℝ) * Real.sqrt D = 0 := by
    convert hz using 1
    simp [latticePoint, latticeCircle, det3]
    ring
  have hn : (latticeCircle D x y i j k l : ℝ) ≠ 0 := by exact_mod_cast ht
  exact (mul_ne_zero hn (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hD))) hz'

private lemma integral_configuration_certificate (D n : ℕ) (hD : 0 < D)
    (x y : Fin n → ℤ) (d : Fin n → Fin n → ℕ)
    (hinj : Function.Injective x)
    (htri : ∀ i j k, i ≠ j → j ≠ k → i ≠ k → latticeTriangle x y i j k ≠ 0)
    (hcirc : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      latticeCircle D x y i j k l ≠ 0)
    (hdist : ∀ i j, latticeNorm D (x i) (y i) (x j) (y j) = (d i j : ℤ)^2) :
    Erdos213For n := by
  let p : Fin n → ℝ² := fun i => latticePoint D (x i) (y i)
  have hp : Function.Injective p := by
    intro i j hij
    apply hinj
    have he := congrArg (fun z : ℝ² => z 0) hij
    change (x i : ℝ) = (x j : ℝ) at he
    exact_mod_cast he
  refine ⟨Set.range p, Set.finite_range _, ?_, ?_, ?_, ?_⟩
  · rw [Set.ncard_range_of_injective hp]
    simp
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ ⟨k,rfl⟩ hij hjk hik
    exact lattice_not_collinear hD (htri i j k (fun he => hij (he ▸ rfl))
      (fun he => hjk (he ▸ rfl)) (fun he => hik (he ▸ rfl)))
  · intro Q hQ hcos
    obtain ⟨a,b,c,e,hab,hac,hae,hbc,hbe,hce,hset⟩ := Set.ncard_eq_four.mp hQ.2
    subst Q
    obtain ⟨i,rfl⟩ := hQ.1 (by simp : a ∈ ({a,b,c,e} : Set ℝ²))
    obtain ⟨j,rfl⟩ := hQ.1 (by simp : b ∈ ({p i,b,c,e} : Set ℝ²))
    obtain ⟨k,rfl⟩ := hQ.1 (by simp : c ∈ ({p i,p j,c,e} : Set ℝ²))
    obtain ⟨l,rfl⟩ := hQ.1 (by simp : e ∈ ({p i,p j,p k,e} : Set ℝ²))
    exact lattice_not_cospherical hD (hcirc i j k l
      (fun he => hab (he ▸ rfl)) (fun he => hac (he ▸ rfl))
      (fun he => hae (he ▸ rfl)) (fun he => hbc (he ▸ rfl))
      (fun he => hbe (he ▸ rfl)) (fun he => hce (he ▸ rfl))) hcos
  · rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _
    refine ⟨(d i j : ℤ), ?_⟩
    have he := latticePoint_dist_sq D (x i) (y i) (x j) (y j)
    rw [hdist] at he
    push_cast at he ⊢
    change (d i j : ℝ) = dist (latticePoint D (x i) (y i)) (latticePoint D (x j) (y j))
    nlinarith [dist_nonneg (x := latticePoint D (x i) (y i)) (y := latticePoint D (x j) (y j)),
      Nat.cast_nonneg (α := ℝ) (d i j)]

/- A distinct centrally symmetric six-point certificate. The three
representative vectors do not have any signed zero-sum relation. This is an
auxiliary construction, not a proof of the arbitrary-cardinality conjecture. -/
private def x77 : Fin 6 → ℤ := ![1040,-1040,156,-156,190,-190]
private def y77 : Fin 6 → ℤ := ![0,0,78,-78,-75,75]
private def d77 : Fin 6 → Fin 6 → ℕ := !![0,2080,1118,1378,1075,1395;
    2080,0,1378,1118,1395,1075;
    1118,1378,0,1404,1343,347;
    1378,1118,1404,0,347,1343;
    1075,1395,1343,347,0,1370;
    1395,1075,347,1343,1370,0]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma erdos213For_six_characteristic_seventyseven : Erdos213For 6 := by
  apply integral_configuration_certificate 77 6 (by norm_num) x77 y77 d77
  · decide
  · decide
  · decide
  · decide

lemma central77_no_signed_zero_sum : ∀ s : Fin 3 → Bool,
    (if s 0 then 1040 else -1040) + (if s 1 then 156 else -156) +
      (if s 2 then 190 else -190) ≠ (0 : ℤ) := by decide

#print axioms erdos213For_six_characteristic_seventyseven
#print axioms central77_no_signed_zero_sum

end Erdos213
