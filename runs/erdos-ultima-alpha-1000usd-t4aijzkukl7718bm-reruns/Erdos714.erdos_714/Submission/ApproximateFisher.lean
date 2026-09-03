import FormalConjecturesUtil

/-! A rank-sensitive defect bound for approximate pair coverage. No
application to arbitrary critical K44-free graphs is asserted here. -/
noncomputable section
open Classical Finset Matrix Unitary
set_option maxHeartbeats 4000000
namespace Erdos714ApproximateFisher
variable {V : Type*} [Fintype V]

lemma trace_square_eigenvalues (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    (A*A).trace=∑ i, (hA.eigenvalues i)^2 := by
  have he : A*A=conjStarAlgAut ℝ _ hA.eigenvectorUnitary
      (diagonal hA.eigenvalues*diagonal hA.eigenvalues) := by
    rw [map_mul]
    have hs := hA.spectral_theorem
    simp only [Function.comp_def,RCLike.ofReal_real_eq_id,id_eq] at hs
    rw [←hs]
  rw [he,conjStarAlgAut_apply,trace_mul_cycle,coe_star_mul_self,one_mul,
    diagonal_mul_diagonal,trace_diagonal]
  simp [pow_two]

/-- Cauchy--Schwarz over the nonzero eigenvalues uses rank, not the
ambient dimension. Negative eigenvalues are permitted. -/
lemma trace_rank_bound (A : Matrix V V ℝ) (hA : A.IsHermitian) :
    A.trace^2 ≤ (A.rank : ℝ)*(∑ i, ∑ j, (A i j)^2) := by
  let s : Finset V := univ.filter (fun i => hA.eigenvalues i ≠ 0)
  have hs : (∑ i ∈ s, hA.eigenvalues i)=∑ i, hA.eigenvalues i := by
    apply sum_subset (subset_univ s)
    intro i _ hi
    have he : hA.eigenvalues i=0 := by simpa [s] using hi
    exact he
  have hs2 : (∑ i ∈ s, (hA.eigenvalues i)^2)=∑ i, (hA.eigenvalues i)^2 := by
    apply sum_subset (subset_univ s)
    intro i _ hi
    have he : hA.eigenvalues i=0 := by simpa [s] using hi
    simp [he]
  have hr : A.rank=s.card := by
    rw [hA.rank_eq_card_non_zero_eigs]
    simp [s,Fintype.card_subtype]
  have hf : (A*A).trace=∑ i, ∑ j, (A i j)^2 := by
    unfold trace
    apply sum_congr rfl
    intro i _
    change (∑ j, A i j * A j i) = ∑ j, A i j ^ 2
    apply sum_congr rfl
    intro j _
    have hij : A j i=A i j := by
      have h := congrArg (fun M : Matrix V V ℝ => M i j) hA.eq
      simpa only [conjTranspose_apply,star_trivial] using h
    rw [hij,pow_two]
  have hc := sum_mul_sq_le_sq_mul_sq s (fun _ => (1 : ℝ)) hA.eigenvalues
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one] at hc
  have ht : A.trace = ∑ i, hA.eigenvalues i := by
    simpa using hA.trace_eq_sum_eigenvalues
  rw [hs,hs2,←ht,←trace_square_eigenvalues A hA,hf,←hr] at hc
  exact hc

variable {B : Type*} [Fintype B]
def coverage (S : B → Finset V) (v w : V) : ℕ :=
  (univ.filter (fun b => v ∈ S b ∧ w ∈ S b)).card
def replication (S : B → Finset V) (v : V) : ℕ :=
  (univ.filter (fun b => v ∈ S b)).card

def defectMatrix (S : B → Finset V) (l : ℕ) : Matrix V V ℝ :=
  fun v w => (coverage S v w : ℝ)-l

omit [Fintype V] in
lemma defectMatrix_hermitian (S : B → Finset V) (l : ℕ) :
    (defectMatrix S l).IsHermitian := by
  ext v w
  simp only [conjTranspose_apply,star_trivial,defectMatrix]
  have hc : coverage S w v = coverage S v w := by
    unfold coverage
    congr 1
    ext b
    simp [and_comm]
  rw [hc]

lemma defectMatrix_rank (S : B → Finset V) (l : ℕ) :
    (defectMatrix S l).rank ≤ Fintype.card B+1 := by
  let L : Matrix V (Option B) ℝ := fun v b =>
    b.elim (-(l : ℝ)) (fun b => if v ∈ S b then 1 else 0)
  let R : Matrix (Option B) V ℝ := fun b v =>
    b.elim 1 (fun b => if v ∈ S b then 1 else 0)
  have he : defectMatrix S l=L*R := by
    ext v w
    simp only [Matrix.mul_apply,Fintype.sum_option,L,R,Option.elim_none,
      Option.elim_some,mul_one,defectMatrix]
    have ht (b : B) : (if v ∈ S b then (1:ℝ) else 0)*(if w ∈ S b then 1 else 0)=
        if v ∈ S b ∧ w ∈ S b then 1 else 0 := by split_ifs <;> simp_all
    simp_rw [ht]
    simp only [coverage,sum_boole]
    ring
  rw [he]
  exact (rank_mul_le_left L R).trans (by simpa using rank_le_card_width L)

/-- Exact defect inequality, allowing arbitrary replication numbers and
arbitrary block sizes. It does not assume uniformity or proper blocks. -/
theorem squared_defect_bound (S : B → Finset V) (l : ℕ) :
    (∑ v, ((replication S v : ℝ)-l))^2 ≤
      (Fintype.card B+1 : ℝ)*
        (∑ v, ∑ w, ((coverage S v w : ℝ)-l)^2) := by
  have h := trace_rank_bound (defectMatrix S l) (defectMatrix_hermitian S l)
  have hr : ((defectMatrix S l).rank : ℝ) ≤ (Fintype.card B+1 : ℝ) := by
    exact_mod_cast defectMatrix_rank S l
  have ht : (defectMatrix S l).trace=∑ v, ((replication S v : ℝ)-l) := by
    simp [trace,defectMatrix,coverage,replication]
  rw [ht] at h
  exact h.trans (mul_le_mul_of_nonneg_right hr (by positivity))

/-- Localizing the defect inequality to every block and summing gives a
second rank-sensitive constraint. No uniformity or coverage assumptions
are needed. -/
theorem localized_defect_bound (S : B → Finset V) (l : ℕ) :
    (∑ v, (replication S v : ℝ)*((replication S v : ℝ)-l))^2 ≤
      (Fintype.card B : ℝ)*(Fintype.card B+1 : ℝ)*
        (∑ v, ∑ w, (coverage S v w : ℝ)*((coverage S v w : ℝ)-l)^2) := by
  let t : B → ℝ := fun b => ∑ v ∈ S b, ((replication S v : ℝ)-l)
  let d : B → ℝ := fun b => ∑ v ∈ S b, ∑ w ∈ S b,
    ((coverage S v w : ℝ)-l)^2
  have hlocal (b : B) : (t b)^2 ≤ (Fintype.card B+1 : ℝ)*d b := by
    let S' : B → Finset (S b) := fun c => univ.filter (fun v => v.val ∈ S c)
    have hr (v : S b) : replication S' v = replication S v.val := by
      simp [replication,S']
    have hc (v w : S b) : coverage S' v w = coverage S v.val w.val := by
      simp [coverage,S']
    have h := squared_defect_bound S' l
    simp_rw [hr,hc] at h
    have hsum (f : V → ℝ) : (∑ v : S b, f v.val) = ∑ v ∈ S b, f v :=
      (sum_subtype (S b) (fun _ => Iff.rfl) f).symm
    have hdouble : (∑ v : S b, ∑ w : S b,
        ((coverage S v.val w.val : ℝ)-l)^2) = d b := by
      rw [hsum (fun v => ∑ w : S b, ((coverage S v w.val : ℝ)-l)^2)]
      apply sum_congr rfl
      intro v _
      exact hsum (fun w => ((coverage S v w : ℝ)-l)^2)
    rw [hsum (fun v => ((replication S v : ℝ)-l)),hdouble] at h
    exact h
  have hs (s : Finset V) (f : V → ℝ) :
      (∑ v ∈ s, f v) = ∑ v, if v ∈ s then f v else 0 := by
    simp [sum_ite_mem]
  have hi (p : B → Prop) [DecidablePred p] (z : ℝ) :
      (∑ b, if p b then z else 0) = (univ.filter p).card*z := by
    rw [← sum_filter]
    simp
  have hts (b : B) : t b = ∑ v,
      if v ∈ S b then ((replication S v : ℝ)-l) else 0 :=
    hs (S b) (fun v => ((replication S v : ℝ)-l))
  have hds (b : B) : d b = ∑ v, ∑ w,
      if v ∈ S b ∧ w ∈ S b then ((coverage S v w : ℝ)-l)^2 else 0 := by
    dsimp only [d]
    rw [hs (S b) (fun v => ∑ w ∈ S b, ((coverage S v w : ℝ)-l)^2)]
    apply sum_congr rfl
    intro v _
    by_cases hv : v ∈ S b
    · simp only [hv,ite_true,true_and]
      exact hs (S b) (fun w => ((coverage S v w : ℝ)-l)^2)
    · simp [hv]
  have ht : (∑ b, t b) = ∑ v, (replication S v : ℝ)*((replication S v : ℝ)-l) := by
    simp_rw [hts]
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    exact hi (fun b => v ∈ S b) ((replication S v : ℝ)-l)
  have hd : (∑ b, d b) = ∑ v, ∑ w,
      (coverage S v w : ℝ)*((coverage S v w : ℝ)-l)^2 := by
    simp_rw [hds]
    rw [sum_comm]
    apply sum_congr rfl
    intro v _
    rw [sum_comm]
    apply sum_congr rfl
    intro w _
    exact hi (fun b => v ∈ S b ∧ w ∈ S b) (((coverage S v w : ℝ)-l)^2)
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset B) (fun _ => (1 : ℝ)) t
  simp only [one_mul,one_pow,sum_const,nsmul_eq_mul,mul_one,card_univ] at hc
  rw [ht] at hc
  calc
    _ ≤ (Fintype.card B : ℝ)*∑ b, (t b)^2 := hc
    _ ≤ (Fintype.card B : ℝ)*∑ b, (Fintype.card B+1 : ℝ)*d b :=
      mul_le_mul_of_nonneg_left (sum_le_sum (fun b _ => hlocal b)) (by positivity)
    _ = _ := by rw [← mul_sum,hd,mul_assoc]

#print axioms trace_rank_bound
#print axioms squared_defect_bound
#print axioms localized_defect_bound
end Erdos714ApproximateFisher
