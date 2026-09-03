import Submission.ArithmeticReduction

/-! Support-sensitive exponent compression. These comparison lemmas are
auxiliary and do not settle the unrestricted odd covering problem. -/
namespace Erdos7SupportCompression
open scoped BigOperators
open Erdos7Distortion Erdos7CompressionSieve
set_option maxHeartbeats 4000000

/-- Multiplicity after truncating one exponent at `a` and erasing it. -/
def pushMultiplicity (w : ℕ → ℕ) (a r : ℕ) : ℕ := w r + a * w (r + 1)

@[simp] lemma pushMultiplicity_zero (w : ℕ → ℕ) : pushMultiplicity w 0 = w := by
  funext r
  simp [pushMultiplicity]

lemma support_update_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (i : ι) (hf : f i = 0) (b : ℕ) (hb : b ≠ 0) :
    (expSupport (Function.update f i b)).card = (expSupport f).card + 1 := by
  have he : expSupport (Function.update f i b) = insert i (expSupport f) := by
    ext j
    by_cases hj : j = i <;> simp [hj, hb, Function.update_of_ne]
  rw [he, Finset.card_insert_of_notMem]
  simp [hf]

/-- Exact support-size accounting avoids the uniform `(a+1)*M` bound. -/
lemma erase_support_multiplicity {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (K : Finset κ) (e : κ → ι → ℕ) (w : ℕ → ℕ)
    (hw : ∀ f, (K.filter (fun k => e k = f)).card ≤ w (expSupport f).card)
    (i : ι) (a : ℕ) (f : ι → ℕ) :
    ((K.filter (fun k => e k i ≤ a)).filter
      (fun k => Function.update (e k) i 0 = f)).card ≤
      pushMultiplicity w a (expSupport f).card := by
  classical
  by_cases hf : f i = 0
  · rw [Erdos7KilledSieve.erase_exponent_card K e i a f hf]
    calc
      _ ≤ ∑ b ∈ Finset.range (a + 1), w (expSupport (Function.update f i b)).card :=
        Finset.sum_le_sum (fun b _ => hw _)
      _ = w (expSupport f).card + a * w ((expSupport f).card + 1) := by
        rw [Finset.sum_range_succ']
        simp only [← hf, Function.update_eq_self]
        have hh : (∑ b ∈ Finset.range a,
            w (expSupport (Function.update f i (b + 1))).card) =
            a * w ((expSupport f).card + 1) := by
          simp only [support_update_positive f i hf _ (Nat.succ_ne_zero _),
            Finset.sum_const, Finset.card_range, smul_eq_mul]
        rw [hh]
        omega
      _ = _ := rfl
  · have he : ((K.filter (fun k => e k i ≤ a)).filter
        (fun k => Function.update (e k) i 0 = f)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro k hk
      have hh := congrFun (Finset.mem_filter.mp hk).2 i
      exact hf (by simpa only [Function.update_self] using hh.symm)
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

/-- A finite envelope retaining multiplicities as a function of support size. -/
def supportEnvelope {n : ℕ} (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (φ : ℚ → ℚ) : ℕ → (ℕ → ℕ) → ℚ
  | 0, w => φ (w 0)
  | t + 1, w => if h : t < n then
      (1 - q ⟨t,h⟩ 0) * supportEnvelope E q φ t w +
      ∑ g ∈ Finset.range (E ⟨t,h⟩), (q ⟨t,h⟩ g - q ⟨t,h⟩ (g + 1)) *
        supportEnvelope E q φ t (pushMultiplicity w (g + 1))
    else supportEnvelope E q φ t w

theorem tower_support_convex_bound {n : ℕ} {κ : Type*}
    (A : Fin n → Type*) [∀ i, Fintype (A i)] [∀ i, Nonempty (A i)] [∀ i, DecidableEq (A i)]
    (B : Fin n → Finset (∀ i, A i)) (c : Fin n → ℚ)
    (E : Fin n → ℕ) (q : Fin n → ℕ → ℚ)
    (hc : ∀ i, 1 ≤ c i) (hq1 : ∀ i, q i 0 ≤ 1)
    (hqdec : ∀ i g, g<E i → q i (g+1) ≤ q i g) (hqE : ∀ i, q i (E i)=0)
    (φ : ℚ → ℚ) (hφ : ConvexOn ℚ Set.univ φ) (hmono : Monotone φ)
    (t : ℕ) (ht : t≤n) (w : ℕ → ℕ) (K : Finset κ)
    (e : κ → Fin n → ℕ) (X : κ → ∀ i, Finset (A i))
    (he : ∀ k∈K, ∀ i, e k i ≤ E i)
    (hS : ∀ k∈K, ∀ i∈expSupport (e k), i.val<t)
    (hX : ∀ k∈K, ∀ i∈expSupport (e k), c i*fraction (X k i) ≤ q i (e k i-1))
    (hM : ∀ f, (K.filter (fun k => e k=f)).card ≤ w (expSupport f).card) :
    (∑ x, towerWeights A B c t x * φ (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x)) ≤
      supportEnvelope E q φ t w := by
  classical
  induction t generalizing w K e with
  | zero =>
    have hz (k : κ) (hk : k∈K) : e k = fun _ => 0 := by
      funext i
      by_contra hi
      have hh := hS k hk i (mem_expSupport _ _ |>.mpr hi)
      omega
    have hcard : K.card ≤ w 0 := by
      have hh := hM (fun _ => 0)
      have heq : K.filter (fun k => e k=fun _ => 0)=K := Finset.filter_true_of_mem hz
      simpa [heq, expSupport] using hh
    have hsupport (k : κ) (hk : k∈K) : expSupport (e k)=∅ := by simp [hz k hk,expSupport]
    have hvalue (x : ∀ i, A i) : (∑ k∈K, boxIndicator A (expSupport (e k)) (X k) x) = (K.card:ℚ) := by
      calc
        _ = ∑ _k∈K, (1:ℚ) := Finset.sum_congr rfl (fun k hk => by rw [hsupport k hk,boxIndicator_empty])
        _ = _ := by simp
    simp_rw [hvalue]
    rw [← Finset.sum_mul,towerWeights_total A B c hc 0,one_mul]
    exact hmono (by exact_mod_cast hcard)
  | succ t ih =>
    let i : Fin n := ⟨t,by omega⟩
    let e' (k : κ) := Function.update (e k) i 0
    let K' (a : ℕ) := K.filter (fun k => e k i ≤ a)
    have he' (k : κ) (hk : k∈K) (j : Fin n) : e' k j ≤ E j := by
      by_cases hj : j=i
      · subst j; simp [e']
      · simpa only [e',Function.update_of_ne hj] using he k hk j
    have hS' (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) : j.val<t := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      have hh := hS k hk j (Finset.mem_erase.mp hj).2
      have hne : j.val≠t := by intro heq; exact hjne (Fin.ext heq)
      omega
    have hX' (k : κ) (hk : k∈K) (j : Fin n) (hj : j∈expSupport (e' k)) :
        c j*fraction (X k j) ≤ q j (e' k j-1) := by
      rw [expSupport_update_zero] at hj
      have hjne := (Finset.mem_erase.mp hj).1
      simpa only [e',Function.update_of_ne hjne] using hX k hk j (Finset.mem_erase.mp hj).2
    have hbound (a : ℕ) :
        (∑ x, towerWeights A B c t x*φ (∑ k∈K' a, boxIndicator A (expSupport (e' k)) (X k) x)) ≤
          supportEnvelope E q φ t (pushMultiplicity w a) :=
      ih (by omega) (pushMultiplicity w a) (K' a) e'
        (fun k hk => he' k (Finset.mem_filter.mp hk).1)
        (fun k hk => hS' k (Finset.mem_filter.mp hk).1)
        (fun k hk => hX' k (Finset.mem_filter.mp hk).1)
        (erase_support_multiplicity K e w hM i a)
    have hstep := resample_exponent_compression A i (towerWeights A B c t)
      (towerWeights_nonneg A B c hc t) (B i) (c i) (hc i) φ hφ hmono K e X (E i) (q i)
      (fun k hk => he k hk i) (fun k hk hi => hX k hk i ((mem_expSupport _ _).mpr hi)) (hqE i)
    have hrec : towerWeights A B c (t+1) = resample A i (towerWeights A B c t) (B i) (c i) :=
      towerWeights_succ A B c i
    rw [hrec]
    apply hstep.trans
    have h0 := mul_le_mul_of_nonneg_left (hbound 0) (sub_nonneg.mpr (hq1 i))
    have hsum := Finset.sum_le_sum (fun g (hg : g∈Finset.range (E i)) =>
      mul_le_mul_of_nonneg_left (hbound (g+1)) (sub_nonneg.mpr (hqdec i g (Finset.mem_range.mp hg))))
    have hh := add_le_add h0 hsum
    simpa only [pushMultiplicity_zero,Nat.zero_add,Nat.one_mul,Nat.add_assoc,supportEnvelope,show t<n by omega,
      ↓reduceDIte,e',K',i] using hh


#print axioms erase_support_multiplicity
#print axioms tower_support_convex_bound
end Erdos7SupportCompression
