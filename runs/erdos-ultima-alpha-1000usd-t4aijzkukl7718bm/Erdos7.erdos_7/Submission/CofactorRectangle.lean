import Submission.CofactorChain

/-! Two-coordinate cofactor capacity for actual arithmetic residue classes.
This is a necessary condition, not a solution of the odd covering problem.
No claim that coordinate compression preserves this constraint is made. -/
namespace Erdos7CofactorRectangle
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1500000

/-- Symmetric-chain label in an exponent rectangle. -/
def chainKey (B u v : ℕ) : ℕ := min u (B-v)

lemma key_bounds (A B u v : ℕ) (hu : u ≤ A) (hv : v ≤ B) :
    chainKey B u v ≤ min A B ∧ chainKey B u v ≤ u ∧
      v + chainKey B u v ≤ B := by
  simp only [chainKey]
  omega

lemma key_corner (B u v : ℕ) (hv : v ≤ B) :
    u = chainKey B u v ∨ v + chainKey B u v = B := by
  simp only [chainKey]
  omega

lemma chain_order {B u v u' v' : ℕ} (hv : v ≤ B) (hv' : v' ≤ B)
    (hk : chainKey B u v = chainKey B u' v') (hs : u+v ≤ u'+v') :
    u ≤ u' ∧ v ≤ v' := by
  have h := key_corner B u v hv
  have h' := key_corner B u' v' hv'
  have hb := key_bounds u B u v le_rfl hv
  have hb' := key_bounds u' B u' v' le_rfl hv'
  omega

lemma chain_rank_injective {B u v u' v' : ℕ} (hv : v ≤ B) (hv' : v' ≤ B)
    (hk : chainKey B u v = chainKey B u' v') (hs : u+v = u'+v') :
    u = u' ∧ v = v' := by
  have h := chain_order hv hv' hk hs.le
  have h' := chain_order hv' hv hk.symm hs.ge
  omega

/-- Cardinality bound from a chain decomposition, with a separate residue
capacity for each chain and an injection into its rank interval. -/
theorem active_card_bound {I : Type*} (S : Finset I)
    (A B q p r : ℕ) (hq : 0 < q) (u v : I → ℕ) (a : I → ℤ)
    (hu : ∀ i ∈ S, u i ≤ A) (hv : ∀ i ∈ S, v i ≤ B)
    (hinj : Set.InjOn (fun i => (u i, v i)) (S : Set I))
    (hcop : ∀ i ∈ S, Nat.Coprime q (p^(u i) * r^(v i)))
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      p^(u i)*r^(v i) ∣ p^(u j)*r^(v j) →
      ¬ ((q*(p^(u i)*r^(v i)) : ℕ) : ℤ) ∣ a j-a i)
    (x : ℤ) :
    (S.filter (fun i => ((p^(u i)*r^(v i) : ℕ) : ℤ) ∣ x-a i)).card ≤
      ∑ k ∈ Finset.range (min A B + 1), min q (A+B+1-2*k) := by
  classical
  let T := S.filter (fun i => ((p^(u i)*r^(v i) : ℕ) : ℤ) ∣ x-a i)
  let key := fun i => chainKey B (u i) (v i)
  have hgroup (k : ℕ) (hk : k ∈ Finset.range (min A B+1)) :
      (T.filter (fun i => key i=k)).card ≤ min q (A+B+1-2*k) := by
    let G := T.filter (fun i => key i=k)
    have hmem (i : G) : i.val ∈ S :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).1
    have hkey (i : G) : chainKey B (u i.val) (v i.val) = k :=
      (Finset.mem_filter.mp i.property).2
    have hqbound : G.card ≤ q := by
      have hh := Erdos7CofactorChain.card_le q hq
        (fun i : G => p^(u i.val)*r^(v i.val)) (fun i : G => a i.val)
        (fun i => hcop i.val (hmem i)) (by
          intro i j
          rcases le_total (u i.val+v i.val) (u j.val+v j.val) with h | h
          · have ho := chain_order (hv i.val (hmem i)) (hv j.val (hmem j))
              ((hkey i).trans (hkey j).symm) h
            exact Or.inl (Nat.mul_dvd_mul (pow_dvd_pow p ho.1) (pow_dvd_pow r ho.2))
          · have ho := chain_order (hv j.val (hmem j)) (hv i.val (hmem i))
              ((hkey j).trans (hkey i).symm) h
            exact Or.inr (Nat.mul_dvd_mul (pow_dvd_pow p ho.1) (pow_dvd_pow r ho.2)))
        (by
          intro i j hij hd
          exact hsep i.val (hmem i) j.val (hmem j)
            (fun heq => hij (Subtype.ext heq)) hd)
        x (fun i => (Finset.mem_filter.mp (Finset.mem_filter.mp i.property).1).2)
      simpa only [Fintype.card_coe] using hh
    have hrange (i : G) : u i.val+v i.val-k < A+B+1-2*k := by
      have hb := key_bounds A B (u i.val) (v i.val)
        (hu i.val (hmem i)) (hv i.val (hmem i))
      have hku : k ≤ u i.val := (hkey i) ▸ hb.2.1
      have hkv : v i.val+k ≤ B := (hkey i) ▸ hb.2.2
      have hui := hu i.val (hmem i)
      omega
    let f : G → Fin (A+B+1-2*k) := fun i => ⟨u i.val+v i.val-k, hrange i⟩
    have hfinj : Function.Injective f := by
      intro i j heq
      have hf : u i.val+v i.val-k = u j.val+v j.val-k := congrArg Fin.val heq
      have hbi := key_bounds A B (u i.val) (v i.val)
        (hu i.val (hmem i)) (hv i.val (hmem i))
      have hbj := key_bounds A B (u j.val) (v j.val)
        (hu j.val (hmem j)) (hv j.val (hmem j))
      have hki : k ≤ u i.val := (hkey i) ▸ hbi.2.1
      have hkj : k ≤ u j.val := (hkey j) ▸ hbj.2.1
      have hs : u i.val+v i.val = u j.val+v j.val := by omega
      have he := chain_rank_injective (hv i.val (hmem i)) (hv j.val (hmem j))
        ((hkey i).trans (hkey j).symm) hs
      apply Subtype.ext
      exact hinj (hmem i) (hmem j) (Prod.ext he.1 he.2)
    have hlbound : G.card ≤ A+B+1-2*k := by
      have hh := Fintype.card_le_of_injective f hfinj
      simpa only [Fintype.card_coe, Fintype.card_fin] using hh
    exact le_min hqbound hlbound
  change T.card ≤ _
  rw [Finset.card_eq_sum_card_fiberwise (s := T)
    (t := Finset.range (min A B+1)) (f := key) (by
      intro i hi
      have hm := (Finset.mem_filter.mp hi).1
      have hb := key_bounds A B (u i) (v i) (hu i hm) (hv i hm)
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le hb.1))]
  exact Finset.sum_le_sum hgroup

/-- Application to any selected two-prime rectangle inside an actual
irredundant arithmetic cover. -/
theorem irredundant_cover_bound {I : Type*} [Fintype I]
    (m : I → ℕ) (a : I → ℤ)
    (hpriv : ∀ i, ∃ x : ℤ, ∀ j, j ≠ i → ¬ (m j : ℤ) ∣ x-a j)
    (hc : ∀ x : ℤ, ∃ i, (m i : ℤ) ∣ x-a i)
    (S : Finset I) (A B q p r : ℕ) (hq : 0 < q) (u v : I → ℕ)
    (hu : ∀ i ∈ S, u i ≤ A) (hv : ∀ i ∈ S, v i ≤ B)
    (hinj : Set.InjOn m (S : Set I))
    (hfac : ∀ i ∈ S, m i = q*(p^(u i)*r^(v i)))
    (hcop : ∀ i ∈ S, Nat.Coprime q (p^(u i)*r^(v i))) (x : ℤ) :
    (S.filter (fun i => ((p^(u i)*r^(v i) : ℕ) : ℤ) ∣ x-a i)).card ≤
      ∑ k ∈ Finset.range (min A B+1), min q (A+B+1-2*k) := by
  apply active_card_bound S A B q p r hq u v a hu hv ?_ hcop ?_ x
  · intro i hi j hj heq
    apply hinj hi hj
    rw [hfac i hi, hfac j hj]
    have he1 := congrArg Prod.fst heq
    have he2 := congrArg Prod.snd heq
    dsimp only at he1 he2
    rw [he1, he2]
  · intro i hi j hj hij hd
    have hmd : m i ∣ m j := by
      rw [hfac i hi, hfac j hj]
      exact Nat.mul_dvd_mul_left q hd
    have hh := Erdos7Reduction.residue_not_congruent_of_proper_modulus_divisor
      m a hpriv hc hij hmd
    simpa only [hfac i hi] using hh

lemma small_cap_values :
    (∑ k ∈ Finset.range (min 3 3+1), min 7 (3+3+1-2*k)) = 16 ∧
    (∑ k ∈ Finset.range (min 4 4+1), min 7 (4+4+1-2*k)) = 23 ∧
    (∑ k ∈ Finset.range (min 4 4+1), min 5 (4+4+1-2*k)) = 19 := by
  decide +kernel

#print axioms irredundant_cover_bound
#print axioms active_card_bound
end Erdos7CofactorRectangle
