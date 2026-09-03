import Submission.ArithmeticReduction

/-! A sufficient construction criterion: replace exceptional classes by
refinements at a fresh prime-power level, then enlarge them using a distinct
assignment of cofactor divisors. No such assignment for a covering witness
is asserted in this module. -/
namespace Erdos7DivisorRepair
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- Split one congruence class into any positive number of equal refinements. -/
theorem split_class (m q : ℕ) (hq : 0 < q) (a x : ℤ)
    (hx : (m : ℤ) ∣ x-a) :
    ∃ t : Fin q, ((m*q : ℕ) : ℤ) ∣ x-(a+(m : ℤ)*t.val) := by
  obtain ⟨k,hk⟩ := hx
  let t : Fin q := ⟨k.natMod q, Int.natMod_lt hq.ne'⟩
  have ht : (t.val : ℤ) = k % q := by
    exact Int.toNat_of_nonneg (Int.emod_nonneg k (by exact_mod_cast hq.ne'))
  refine ⟨t, ⟨k/(q : ℤ), ?_⟩⟩
  have he := Int.emod_add_mul_ediv k (q : ℤ)
  rw [Nat.cast_mul, ht]
  calc
    x-(a+(m : ℤ)*(k % q)) = (x-a)-(m : ℤ)*(k % q) := by ring
    _ = (m : ℤ)*k-(m : ℤ)*(k % q) := by rw [hk]
    _ = ((m : ℤ)*q)*(k/q) := by nlinarith [he]

lemma refinement_modulus (p R a d : ℕ) (ha : a ≤ R) :
    (p^a*d)*p^(R-a) = p^R*d := by
  calc
    _ = (p^a*p^(R-a))*d := by ring
    _ = p^R*d := by rw [← pow_add, Nat.add_sub_of_le ha]

/-- Every exceptional class is covered after the divisor enlargement. -/
theorem repair_one (p R a d : ℕ) (hp : 0 < p) (ha : a ≤ R)
    (e : Fin (p^(R-a)) → ℕ) (he : ∀ t, e t ∣ d) (b x : ℤ)
    (hx : ((p^a*d : ℕ) : ℤ) ∣ x-b) :
    ∃ t, ((p^R*e t : ℕ) : ℤ) ∣ x-(b+((p^a*d : ℕ) : ℤ)*t.val) := by
  obtain ⟨t,ht⟩ := split_class (p^a*d) (p^(R-a)) (pow_pos hp _) b x hx
  refine ⟨t, ?_⟩
  have hd : p^R*e t ∣ (p^a*d)*p^(R-a) := by
    rw [refinement_modulus p R a d ha]
    exact Nat.mul_dvd_mul_left _ (he t)
  exact (show ((p^R*e t : ℕ) : ℤ) ∣ (((p^a*d)*p^(R-a) : ℕ) : ℤ) by exact_mod_cast hd).trans ht

/-- The actual repaired class system, including its distinctness and oddness.
The global divisor injection is essential: reusing a divisor for two pieces
would give repeated new moduli and would not prove the conjecture. -/
theorem repair_cover {I J : Type} [Fintype I] [Fintype J]
    (m : I → ℕ) (b : I → ℤ) (hm : Function.Injective m)
    (hmo : ∀ i, 1 < m i ∧ Odd (m i))
    (p R : ℕ) (hp : 1 < p) (hpo : Odd p) (hR : 0 < R)
    (a d : J → ℕ) (c : J → ℤ) (ha : ∀ j, a j ≤ R)
    (hd : ∀ j, Odd (d j)) (hnew : ∀ i, ¬ p^R ∣ m i)
    (e : (j : J) × Fin (p^(R-a j)) → ℕ)
    (hei : Function.Injective e) (hed : ∀ j t, e ⟨j,t⟩ ∣ d j)
    (hc : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-b i) ∨
      (∃ j, ((p^(a j)*d j : ℕ) : ℤ) ∣ x-c j)) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  classical
  let K := (j : J) × Fin (p^(R-a j))
  let n : I ⊕ K → ℕ := Sum.elim m (fun k => p^R*e k)
  let r : I ⊕ K → ℤ := Sum.elim b
    (fun k => c k.1 + ((p^(a k.1)*d k.1 : ℕ) : ℤ)*k.2.val)
  have hn : Function.Injective n := by
    intro u v huv
    cases u with
    | inl i =>
      cases v with
      | inl j => exact congrArg Sum.inl (hm huv)
      | inr k =>
        exact False.elim (hnew i (by
          change m i = p^R*e k at huv
          rw [huv]
          exact dvd_mul_right _ _))
    | inr k =>
      cases v with
      | inl i =>
        exact False.elim (hnew i (by
          change p^R*e k = m i at huv
          rw [← huv]
          exact dvd_mul_right _ _))
      | inr l =>
        apply congrArg Sum.inr
        apply hei
        exact Nat.mul_left_cancel (pow_pos (by omega) R) huv
  have hno (u : I ⊕ K) : 1 < n u ∧ Odd (n u) := by
    cases u with
    | inl i => exact hmo i
    | inr k =>
      have heo : Odd (e k) := (hd k.1).of_dvd_nat (hed k.1 k.2)
      have hep : 0 < e k := heo.pos
      have hpow : 1 < p^R := Nat.one_lt_pow hR.ne' hp
      exact ⟨hpow.trans_le (Nat.le_mul_of_pos_right _ hep), hpo.pow.mul heo⟩
  have hcover (x : ℤ) : ∃ u, (n u : ℤ) ∣ x-r u := by
    rcases hc x with ⟨i,hi⟩ | ⟨j,hj⟩
    · exact ⟨Sum.inl i, hi⟩
    · obtain ⟨t,ht⟩ := repair_one p R (a j) (d j) (by omega) (ha j)
        (fun t => e ⟨j,t⟩) (hed j) (c j) x hj
      exact ⟨Sum.inr ⟨j,t⟩, ht⟩
  exact Erdos7Reduction.arithmetic_formulation.mpr
    ⟨I ⊕ K, inferInstance, n, r, hn, hno, hcover⟩


/-- Hall's condition on the cofactor-divisor lists suffices for the repair.
This is a finite combinatorial hypothesis, not asserted automatically. -/
theorem repair_cover_of_hall {I J : Type} [Fintype I] [Fintype J]
    (m : I → ℕ) (b : I → ℤ) (hm : Function.Injective m)
    (hmo : ∀ i, 1 < m i ∧ Odd (m i))
    (p R : ℕ) (hp : 1 < p) (hpo : Odd p) (hR : 0 < R)
    (a d : J → ℕ) (c : J → ℤ) (ha : ∀ j, a j ≤ R)
    (hd : ∀ j, Odd (d j)) (hnew : ∀ i, ¬ p^R ∣ m i)
    (hHall : ∀ s : Finset ((j : J) × Fin (p^(R-a j))),
      s.card ≤ (s.biUnion (fun k => (d k.1).divisors)).card)
    (hc : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-b i) ∨
      (∃ j, ((p^(a j)*d j : ℕ) : ℤ) ∣ x-c j)) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  classical
  obtain ⟨e,hei,he⟩ := (Finset.all_card_le_biUnion_card_iff_exists_injective
    (fun k : (j : J) × Fin (p^(R-a j)) => (d k.1).divisors)).mp hHall
  exact repair_cover m b hm hmo p R hp hpo hR a d c ha hd hnew
    e hei (fun j t => (Nat.mem_divisors.mp (he ⟨j,t⟩)).1) hc

/-- One extra75-class can be replaced by the three new moduli9,45,225,
provided no kept modulus is divisible by9. This remains conditional on a
near-cover; no such near-cover is supplied here. -/
theorem one_extra_seventyfive {I : Type} [Fintype I]
    (m : I → ℕ) (b : I → ℤ) (hm : Function.Injective m)
    (hmo : ∀ i, 1 < m i ∧ Odd (m i)) (hno9 : ∀ i, ¬ 9 ∣ m i)
    (c : ℤ) (hc : ∀ x : ℤ, (∃ i, (m i : ℤ) ∣ x-b i) ∨ 75 ∣ x-c) :
    ∃ C : StrictCoveringSystem ℤ, ∀ i,
      ¬ C.moduli i ≤ Ideal.span {2} ∧ C.moduli i ≠ ⊤ := by
  let e : (_ : Unit) × Fin (3^(2-1)) → ℕ := fun k => (![1,5,25] : Fin 3 → ℕ) k.2
  have hei : Function.Injective e := by decide +kernel
  have hed : ∀ j t, e ⟨j,t⟩ ∣ (25 : ℕ) := by decide +kernel
  apply repair_cover m b hm hmo 3 2 (by norm_num) (by decide) (by norm_num)
    (fun _ : Unit => 1) (fun _ : Unit => 25) (fun _ : Unit => c)
    (by intro; norm_num) (by intro; change Odd (25 : ℕ); decide) hno9 e hei hed
  intro x
  rcases hc x with h | h
  · exact Or.inl h
  · exact Or.inr ⟨(), by simpa using h⟩

#print axioms repair_cover_of_hall
#print axioms one_extra_seventyfive

#print axioms split_class
#print axioms repair_one
#print axioms repair_cover
end Erdos7DivisorRepair
