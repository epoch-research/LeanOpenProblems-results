import Submission.SemilinearBothModel

/-! Transport of the refined semilinear graph through odd-degree extensions.
This concerns an auxiliary construction, not a universal extremal upper bound. -/

open Matrix Polynomial SimpleGraph Erdos714BothModel
noncomputable section
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace Erdos714BothTransport

variable {K L : Type*} [Field K] [Field L] [CharP K 2] [CharP L 2]

lemma elliptic_iff_irreducible (A : M (K := K)) : elliptic A ↔ Irreducible A.charpoly := by
  have hn : A.charpoly.natDegree = 2 := by simp [Matrix.charpoly_natDegree_eq_dim]
  rw [Polynomial.irreducible_iff_roots_eq_zero_of_degree_le_three
    (by omega : 2 ≤ A.charpoly.natDegree) (by omega : A.charpoly.natDegree ≤ 3)]
  rw [Multiset.eq_zero_iff_forall_notMem]
  simp only [Polynomial.mem_roots A.charpoly_monic.ne_zero]
  simp only [Polynomial.IsRoot, Matrix.charpoly_fin_two, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  have hsub : ∀ a b : K, a-b = a+b := fun a b => by rw [sub_eq_add_neg, CharTwo.neg_eq]
  simp only [hsub]
  rfl

omit [CharP K 2] [CharP L 2] in
lemma trace_map_two (α : K →+* L) (A : M (K := K)) : (A.map α).trace = α A.trace := by
  simp [Matrix.trace_fin_two]

omit [CharP K 2] [CharP L 2] in
lemma det_map_two (α : K →+* L) (A : M (K := K)) : (A.map α).det = α A.det := by
  simp [Matrix.det_fin_two]

omit [CharP L 2] in
lemma elliptic_map_odd [Algebra K L] (hodd : Odd (Module.finrank K L))
    (A : M (K := K)) (hA : elliptic A) : elliptic (A.map (algebraMap K L)) := by
  intro x hx
  have hroot : Polynomial.aeval x A.charpoly = 0 := by
    rw [Matrix.charpoly_fin_two]
    simpa [Polynomial.aeval_def, trace_map_two, det_map_two,
      sub_eq_add_neg, CharTwo.neg_eq] using hx
  have hp := (elliptic_iff_irreducible A).mp hA
  have hmin := minpoly.eq_of_irreducible_of_monic hp hroot A.charpoly_monic
  have hxI : IsIntegral K x := ⟨A.charpoly, A.charpoly_monic, hroot⟩
  have hrank : Module.finrank K (IntermediateField.adjoin K {x}) = 2 := by
    rw [IntermediateField.adjoin.finrank hxI, ← hmin, Matrix.charpoly_natDegree_eq_dim]
    rfl
  apply hodd.not_two_dvd_nat
  refine ⟨Module.finrank (IntermediateField.adjoin K {x}) L, ?_⟩
  rw [← Module.finrank_mul_finrank K (IntermediateField.adjoin K {x}) L, hrank]

/-- Ordered products along an arbitrary map; no commutativity is assumed. -/
def orbitNorm {G : Type*} [Monoid G] (f : G → G) : ℕ → G → G
  | 0, _ => 1
  | n+1, a => a * orbitNorm f n (f a)

lemma orbitNorm_add {G : Type*} [Monoid G] (f : G → G) (n m : ℕ) (a : G) :
    orbitNorm f (n+m) a = orbitNorm f n a * orbitNorm f m (f^[n] a) := by
  induction n generalizing a with
  | zero => simp [orbitNorm]
  | succ n ih =>
    rw [Nat.succ_add]
    change a * orbitNorm f (n+m) (f a) =
      (a * orbitNorm f n (f a)) * orbitNorm f m (f^[n+1] a)
    rw [ih, mul_assoc, Function.iterate_succ_apply]

lemma orbitNorm_mul_of_period {G : Type*} [Monoid G] (f : G → G) (n m : ℕ) (a : G)
    (hn : orbitNorm f n a = 1) (hp : f^[n] a = a) : orbitNorm f (n*m) a = 1 := by
  induction m with
  | zero => simp [orbitNorm]
  | succ m ih =>
    rw [Nat.mul_succ, Nat.add_comm, orbitNorm_add, hn, hp, one_mul, ih]

omit [CharP K 2] in
lemma source_norm (n : ℕ) (A : M (K := K)) :
    orbitNorm sigmaM n A = semilinearNorm n A := by
  induction n generalizing A with
  | zero => rfl
  | succ n ih => exact congrArg (A * ·) (ih (sigmaM A))

def theta (d : ℕ) (A : M (K := K)) : M (K := K) := A.map (fun x => x^d)

omit [CharP K 2] in
lemma theta_iterate (d n : ℕ) (A : M (K := K)) :
    (theta d)^[n] A = A.map (fun x => x^(d^n)) := by
  induction n with
  | zero => ext i j; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    ext i j
    simp only [theta, Matrix.map_apply, pow_succ, pow_mul]

omit [CharP K 2] in
lemma pow512_iter (hK : ∀ x : K, x^512 = x) (n : ℕ) (x : K) : x^(512^n) = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_mul, ih, hK]

omit [CharP K 2] in
lemma sigmaM_period (hK : ∀ x : K, x^512 = x) (A : M (K := K)) :
    sigmaM^[9] A = A := by
  change (theta 32)^[9] A = A
  rw [theta_iterate]
  ext i j
  change (A i j)^(32^9) = A i j
  rw [show (32 : ℕ)^9 = 512^5 by norm_num]
  exact pow512_iter hK 5 _

omit [CharP K 2] [CharP L 2] in
lemma theta_map (α : K →+* L) (d : ℕ)
    (hd : ∀ x : K, (α x)^d = α (x^32)) (A : M (K := K)) :
    theta d (A.map α) = (sigmaM A).map α := by
  ext i j
  exact hd (A i j)

omit [CharP K 2] [CharP L 2] in
lemma orbitNorm_map (α : K →+* L) (d : ℕ)
    (hd : ∀ x : K, (α x)^d = α (x^32)) (n : ℕ) (A : M (K := K)) :
    orbitNorm (theta d) n (A.map α) = (semilinearNorm n A).map α := by
  induction n generalizing A with
  | zero => simpa only [orbitNorm, semilinearNorm] using (α.mapMatrix.map_one).symm
  | succ n ih =>
    change A.map α * orbitNorm (theta d) n (theta d (A.map α)) =
      (A * semilinearNorm n (sigmaM A)).map α
    rw [theta_map α d hd, ih, Matrix.map_mul]

/-- The actual Tits-power relation and the full k-step norm guard. -/
def GoodAt (k : ℕ) (A : M (K := K)) : Prop :=
  (A * theta (2^((k+1)/2)) A).trace = 1 ∧ elliptic A ∧
    orbitNorm (theta (2^((k+1)/2))) k A = 1 ∧
      elliptic (A * theta (2^((k+1)/2)) A)

def graphAt (k : ℕ) : SimpleGraph (U (K := K) ⊕ U (K := K)) where
  Adj
    | Sum.inl g, Sum.inr h => GoodAt k ((↑g⁻¹ : M (K := K)) * (↑h : M (K := K)))
    | Sum.inr h, Sum.inl g => GoodAt k ((↑g⁻¹ : M (K := K)) * (↑h : M (K := K)))
    | _, _ => False
  symm := by intro a b; cases a <;> cases b <;> simp
  loopless := by intro a; cases a <;> simp

omit [CharP K 2] [CharP L 2] in
lemma tits_power_restrict (hK : ∀ x : K, x^512 = x) (α : K →+* L)
    (m : ℕ) (hm : Odd m) (x : K) : (α x)^(2^((9*m+1)/2)) = α (x^32) := by
  obtain ⟨j, hj⟩ := hm
  have hhalf : (9*m+1)/2 = 9*j+5 := by omega
  rw [hhalf]
  have hexp : (2 : ℕ)^(9*j+5) = 512^j*32 := by rw [pow_add, pow_mul]; norm_num
  rw [hexp, ← map_pow, pow_mul, pow512_iter hK]

omit [CharP L 2] in
lemma good_map [Algebra K L] (hK : ∀ x : K, x^512 = x) (m : ℕ) (hm : Odd m)
    (hodd : Odd (Module.finrank K L)) (A : M (K := K)) (hA : Good A) :
    GoodAt (9*m) (A.map (algebraMap K L)) := by
  let α := algebraMap K L
  have hd := tits_power_restrict hK α m hm
  have hprod : A.map α * theta (2^((9*m+1)/2)) (A.map α) =
      (A * sigmaM A).map α := by rw [theta_map α _ hd, Matrix.map_mul]
  refine ⟨?_, elliptic_map_odd hodd A hA.2.1, ?_, ?_⟩
  · change (A.map α * theta (2^((9*m+1)/2)) (A.map α)).trace = 1
    rw [hprod, trace_map_two, hA.1, map_one]
  · change orbitNorm (theta (2^((9*m+1)/2))) (9*m) (A.map α) = 1
    rw [orbitNorm_map α _ hd, ← source_norm]
    rw [orbitNorm_mul_of_period sigmaM 9 m A
      (by rw [source_norm]; exact hA.2.2.1) (sigmaM_period hK A)]
    exact α.mapMatrix.map_one
  · change elliptic (A.map α * theta (2^((9*m+1)/2)) (A.map α))
    rw [hprod]
    exact elliptic_map_odd hodd _ hA.2.2.2

omit [CharP L 2] in
lemma graph_map [Algebra K L] (hK : ∀ x : K, x^512 = x) (m : ℕ) (hm : Odd m)
    (hodd : Odd (Module.finrank K L)) : graph (K := K) ⊑ graphAt (K := L) (9*m) := by
  let f : U (K := K) →* U (K := L) := Matrix.GeneralLinearGroup.map (algebraMap K L)
  have hf : Function.Injective f := by
    intro a b h
    apply Units.ext
    apply Matrix.map_injective (algebraMap K L).injective
    exact congrArg (fun g : U (K := L) => (↑g : M (K := L))) h
  refine ⟨⟨⟨Sum.map f f, ?_⟩, Sum.map_injective.mpr ⟨hf, hf⟩⟩⟩
  intro a b hab
  cases a with
  | inl a => cases b with
    | inl b => exact hab.elim
    | inr b =>
      change GoodAt (9*m) ((↑(f a)⁻¹ : M (K := L)) * (↑(f b) : M (K := L)))
      have hh := good_map hK m hm hodd _ hab
      simpa only [Matrix.map_mul] using hh
  | inr a => cases b with
    | inl b =>
      change GoodAt (9*m) ((↑(f b)⁻¹ : M (K := L)) * (↑(f a) : M (K := L)))
      have hh := good_map hK m hm hodd _ hab
      simpa only [Matrix.map_mul] using hh
    | inr b => exact hab.elim

#print axioms elliptic_iff_irreducible
#print axioms elliptic_map_odd
#print axioms good_map
#print axioms graph_map
end Erdos714BothTransport
