import FormalConjecturesUtil

/-!
# Erdős Problem 241

*References:*
- [erdosproblems.com/30](https://www.erdosproblems.com/30)
- [erdosproblems.com/241](https://www.erdosproblems.com/241)
- [BoCh62] Bose, R. C. and Chowla, S., Theorems in the additive theory of numbers. Comment. Math.
  Helv. (1962/63), 141-147.
- [Gr01] Green, Ben, The number of squares and {$B_h[g]$} sets. Acta Arith. (2001), 365-390.
- [Gu04] Guy, Richard K., Unsolved problems in number theory. (2004), xviii+437.
-/

open Filter Finset
open scoped Asymptotics



open Polynomial

namespace BoseConstruction

lemma prod_inj {K L : Type*} [Field K] [Field L] [Algebra K L]
    (pb : PowerBasis K L) (s t : Multiset K)
    (hs : s.card = pb.dim) (ht : t.card = pb.dim)
    (he : (s.map (fun a ↦ pb.gen - algebraMap K L a)).prod =
      (t.map (fun a ↦ pb.gen - algebraMap K L a)).prod) : s = t := by
  classical
  let P : K[X] := (s.map (fun a ↦ X - C a)).prod
  let Q : K[X] := (t.map (fun a ↦ X - C a)).prod
  have hP : P.Monic := monic_multisetProd_X_sub_C s
  have hQ : Q.Monic := monic_multisetProd_X_sub_C t
  have hPd : P.degree = pb.dim := by
    rw [degree_eq_natDegree hP.ne_zero]
    simpa [P, natDegree_multiset_prod_X_sub_C_eq_card] using congrArg (fun n : ℕ ↦ (n : WithBot ℕ)) hs
  have hQd : Q.degree = pb.dim := by
    rw [degree_eq_natDegree hQ.ne_zero]
    simpa [Q, natDegree_multiset_prod_X_sub_C_eq_card] using congrArg (fun n : ℕ ↦ (n : WithBot ℕ)) ht
  have hv : aeval pb.gen (P - Q) = 0 := by
    simp only [map_sub, sub_eq_zero]
    simpa [P, Q, map_multiset_prod, Multiset.map_map, Function.comp_def] using he
  have hpq : P = Q := by
    by_contra h
    have hlow := pb.dim_le_degree_of_root (sub_ne_zero.mpr h) hv
    have hupp := degree_sub_lt (hPd.trans hQd.symm) hP.ne_zero
      (hP.leadingCoeff.trans hQ.leadingCoeff.symm)
    rw [hPd] at hupp
    exact (not_lt_of_ge hlow) hupp
  have hr := congrArg Polynomial.roots hpq
  simpa [P, Q] using hr

lemma gen_sub_ne_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    (pb : PowerBasis K L) (hd : 1 < pb.dim) (a : K) :
    pb.gen - algebraMap K L a ≠ 0 := by
  intro he
  have hb := pb.dim_le_natDegree_of_root (X_sub_C_ne_zero a)
    (show aeval pb.gen (X - C a) = 0 by simpa using he)
  simp only [natDegree_X_sub_C] at hb
  omega




lemma exists_code {K L : Type*} [Field K] [Field L] [Algebra K L] [Finite L]
    (pb : PowerBasis K L) (hd : 1 < pb.dim) :
    ∃ code : K → ℕ, Function.Injective code ∧
      (∀ a, 1 ≤ code a ∧ code a ≤ Nat.card Lˣ) ∧
      (∀ s t : Multiset K, s.card = pb.dim → t.card = pb.dim →
        (s.map code).sum = (t.map code).sum → s = t) := by
  classical
  let M := Nat.card Lˣ
  haveI : NeZero M := ⟨Nat.card_pos.ne'⟩
  let u : K → Lˣ := fun a ↦ Units.mk0 _ (gen_sub_ne_zero pb hd a)
  let e : Multiplicative (ZMod M) ≃* Lˣ := zmodCyclicMulEquiv inferInstance
  let log : K → ZMod M := fun a ↦ Multiplicative.toAdd (e.symm (u a))
  let code : K → ℕ := fun a ↦ (log a).val + 1
  have he (a : K) : e (Multiplicative.ofAdd (log a)) = u a := e.apply_symm_apply _
  have hlog : Function.Injective log := by
    intro a b h
    have hh := congrArg (fun z ↦ ((e (Multiplicative.ofAdd z)) : L)) h
    simp only [he] at hh
    change pb.gen - algebraMap K L a = pb.gen - algebraMap K L b at hh
    exact (algebraMap K L).injective (sub_right_inj.mp hh)
  have hcode : Function.Injective code := by
    intro a b h
    apply hlog
    apply ZMod.val_injective M
    exact Nat.add_right_cancel h
  refine ⟨code, hcode, ?_, ?_⟩
  · intro a
    have hh := ZMod.val_lt (log a)
    exact ⟨by simp [code], by dsimp [code]; omega⟩
  · intro s t hs ht hsum
    have sumcode (m : Multiset K) :
        ((m.map code).sum : ZMod M) = (m.map log).sum + (m.card : ZMod M) := by
      induction m using Multiset.induction_on with
      | empty => simp
      | @cons a m ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons,
          Nat.cast_add, Nat.cast_one, ih]
        simp [code, add_assoc, add_left_comm, add_comm]
    have hl : (s.map log).sum = (t.map log).sum := by
      have hh := congrArg (fun n : ℕ ↦ (n : ZMod M)) hsum
      dsimp only at hh
      rw [sumcode, sumcode, hs, ht] at hh
      exact add_right_cancel hh
    have prodlog (m : Multiset K) :
        e (Multiplicative.ofAdd (m.map log).sum) = (m.map u).prod := by
      induction m using Multiset.induction_on with
      | empty => simp
      | @cons a m ih =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.prod_cons,
          ofAdd_add, map_mul, he, ih]
    have hp : (s.map u).prod = (t.map u).prod := by rw [← prodlog, ← prodlog, hl]
    apply prod_inj pb s t hs ht
    have hv := congrArg (Units.coeHom L) hp
    simpa [u, map_multiset_prod, Multiset.map_map, Function.comp_def] using hv



lemma exists_set_of_code {K : Type*} [Fintype K] [Nonempty K] (N r : ℕ)
    (code : K → ℕ) (hi : Function.Injective code)
    (hb : ∀ a, 1 ≤ code a ∧ code a ≤ N)
    (hs : ∀ s t : Multiset K, s.card = r → t.card = r →
      (s.map code).sum = (t.map code).sum → s = t) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ A.card = Fintype.card K ∧
      ∀ m₁ m₂ : Multiset ℕ,
        m₁.card = r → m₂.card = r →
        (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
        m₁.sum = m₂.sum → m₁ = m₂ := by
  classical
  let A := Finset.univ.image code
  let decode := Function.invFun code
  have hinv (a : K) : decode (code a) = a := Function.leftInverse_invFun hi a
  have hmap (m : Multiset ℕ) (hm : ∀ x ∈ m, x ∈ A) :
      (m.map decode).map code = m := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id m]
    apply Multiset.map_congr rfl
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hm x hx)
    exact congrArg code (hinv a)
  refine ⟨A, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_Icc.mpr (hb a)
  · exact (Finset.card_image_of_injective _ hi).trans (Finset.card_univ)
  · intro m₁ m₂ h₁ h₂ hm₁ hm₂ heq
    have h := hs (m₁.map decode) (m₂.map decode) (by simpa using h₁) (by simpa using h₂)
      (by simpa [hmap m₁ hm₁, hmap m₂ hm₂] using heq)
    have he := congrArg (Multiset.map code) h
    simpa [hmap m₁ hm₁, hmap m₂ hm₂] using he

lemma bose_chowla_sets (p : ℕ) [Fact p.Prime] :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 (p^3 - 1) ∧ A.card = p ∧
      ∀ m₁ m₂ : Multiset ℕ,
        m₁.card = 3 → m₂.card = 3 →
        (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
        m₁.sum = m₂.sum → m₁ = m₂ := by
  let pb := Field.powerBasisOfFiniteOfSeparable (ZMod p) (GaloisField p 3)
  have hd : pb.dim = 3 := pb.finrank.symm.trans (GaloisField.finrank p (by decide))
  have hM : Nat.card (GaloisField p 3)ˣ = p^3 - 1 := by
    rw [Nat.card_units, GaloisField.card p 3 (by decide)]
  obtain ⟨code, hi, hb, hs⟩ := exists_code pb (by omega)
  rw [hd] at hs
  rw [hM] at hb
  simpa using exists_set_of_code (p^3 - 1) 3 code hi hb hs

end BoseConstruction

namespace Erdos241

/--
Let $f(N)$ be the maximum size of $A\subseteq \{1,\ldots,N\}$ such that the sums $a+b+c$ with
$a,b,c\in A$ are all distinct (aside from the trivial coincidences).

Formalization note: this is generalized to allow for different $r$.
-/
noncomputable def f (N r : ℕ) : ℕ :=
  open scoped Classical in
  letI candidates := (Icc 1 N).powerset.filter (fun A ↦
    ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂)
  candidates.sup card


lemma f_le (N r : ℕ) : f N r ≤ N := by
  classical
  unfold f
  apply Finset.sup_le
  intro A hA
  have hsub : A ⊆ Icc 1 N := mem_powerset.mp (mem_filter.mp hA).1
  simpa using Finset.card_le_card hsub

lemma f_monotone (r : ℕ) : Monotone (fun N ↦ f N r) := by
  classical
  intro N M hNM
  unfold f
  apply Finset.sup_mono
  intro A hA
  rcases mem_filter.mp hA with ⟨hA, hP⟩
  apply mem_filter.mpr
  refine ⟨mem_powerset.mpr ?_, hP⟩
  intro x hx
  have hxN := mem_Icc.mp (mem_powerset.mp hA hx)
  exact mem_Icc.mpr ⟨hxN.1, hxN.2.trans hNM⟩

lemma target_iff_ratio :
    ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3))) ↔
    Tendsto (fun N : ℕ ↦ (f N 3 : ℝ) / (N : ℝ) ^ ((1 : ℝ) / 3))
      atTop (nhds 1) := by
  apply Asymptotics.isEquivalent_iff_tendsto_one
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact ne_of_gt (Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _)



lemma admissible_counting_bound (N r : ℕ) (A : Finset ℕ)
    (hAN : A ⊆ Icc 1 N)
    (hA : ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = r → m₂.card = r →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂) :
    (A.card + r - 1).choose r ≤ r * N + 1 := by
  classical
  let val : Sym A r → Multiset ℕ := fun m ↦ m.val.map Subtype.val
  have hc (m : Sym A r) : (val m).card = r := by
    simp [val]
  have hm (m : Sym A r) : ∀ x ∈ val m, x ∈ A := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact y.property
  have hu (m : Sym A r) : (val m).sum ≤ r * N := by
    calc
      (val m).sum ≤ (val m).card • N :=
        Multiset.sum_le_card_nsmul _ _ (fun x hx ↦ (mem_Icc.mp (hAN (hm m x hx))).2)
      _ = r * N := by simp [hc]
  let g : Sym A r → Fin (r * N + 1) := fun m ↦ ⟨(val m).sum, Nat.lt_succ_of_le (hu m)⟩
  have hg : Function.Injective g := by
    intro m₁ m₂ heq
    apply Subtype.ext
    apply Multiset.map_injective (f := Subtype.val) Subtype.val_injective
    apply hA (val m₁) (val m₂) (hc m₁) (hc m₂) (hm m₁) (hm m₂)
    exact congrArg Fin.val heq
  have hcard := Fintype.card_le_of_injective g hg
  simpa [Sym.card_sym_eq_choose, Fintype.card_coe] using hcard



lemma f_counting_bound (N : ℕ) : (f N 3 + 2).choose 3 ≤ 3 * N + 1 := by
  classical
  unfold f
  apply Finset.sup_induction (p := fun k : ℕ ↦ (k + 2).choose 3 ≤ 3 * N + 1)
  · norm_num
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa [sup_eq_right.mpr h] using hb
    · simpa [sup_eq_left.mpr h] using ha
  · intro A hA
    rcases mem_filter.mp hA with ⟨hsub, hA⟩
    simpa using admissible_counting_bound N 3 A (mem_powerset.mp hsub) hA

lemma f_cube_bound (N : ℕ) : (f N 3)^3 ≤ 18 * N + 6 := by
  have hb := f_counting_bound N
  have heq := Nat.ascFactorial_eq_factorial_mul_choose' (f N 3) 3
  norm_num [Nat.ascFactorial_succ, Nat.factorial] at heq
  nlinarith [Nat.zero_le ((f N 3)^2)]



lemma signed_counting_bound (N : ℕ) (A : Finset ℕ)
    (hAN : A ⊆ Icc 1 N)
    (hA : ∀ m₁ m₂ : Multiset ℕ,
      m₁.card = 3 → m₂.card = 3 →
      (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
      m₁.sum = m₂.sum → m₁ = m₂) :
    A.card * A.card.choose 2 ≤ 3 * N + 1 := by
  classical
  let D := (c : A) × Sym ↥(A.erase c.val) 2
  let val (c : A) (m : Sym ↥(A.erase c.val) 2) : Multiset ℕ :=
    m.val.map Subtype.val
  have hc (c : A) (m : Sym ↥(A.erase c.val) 2) : (val c m).card = 2 := by
    simp [val]
  have hm (c : A) (m : Sym ↥(A.erase c.val) 2) : ∀ x ∈ val c m, x ∈ A.erase c.val := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
    exact y.property
  have hu (c : A) (m : Sym ↥(A.erase c.val) 2) : (val c m).sum ≤ 2 * N := by
    calc
      (val c m).sum ≤ (val c m).card • N :=
        Multiset.sum_le_card_nsmul _ _ (fun x hx ↦
          (mem_Icc.mp (hAN (mem_of_mem_erase (hm c m x hx)))).2)
      _ = 2 * N := by simp [hc]
  let g : D → Fin (3 * N + 1) := fun ⟨c, m⟩ ↦
    ⟨(val c m).sum + N - c.val, by have := hu c m; omega⟩
  have hg : Function.Injective g := by
    rintro ⟨c, m⟩ ⟨d, n⟩ heq
    have hs := congrArg Fin.val heq
    change (val c m).sum + N - c.val = (val d n).sum + N - d.val at hs
    have hce : c.val ≤ N := (mem_Icc.mp (hAN c.property)).2
    have hde : d.val ≤ N := (mem_Icc.mp (hAN d.property)).2
    have hs' : d.val + (val c m).sum = c.val + (val d n).sum := by omega
    have he := hA (d.val ::ₘ val c m) (c.val ::ₘ val d n)
      (by simp [hc]) (by simp [hc])
      (by intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact d.property
          · exact mem_of_mem_erase (hm c m x hx))
      (by intro x hx; rcases Multiset.mem_cons.mp hx with rfl | hx
          · exact c.property
          · exact mem_of_mem_erase (hm d n x hx))
      (by simpa using hs')
    have hcd : c = d := by
      apply Subtype.ext
      have hmem : c.val ∈ d.val ::ₘ val c m := by
        rw [he]
        exact Multiset.mem_cons_self _ _
      rcases Multiset.mem_cons.mp hmem with h | h
      · exact h
      · exact False.elim ((mem_erase.mp (hm c m c.val h)).1 rfl)
    subst d
    have hmn : m = n := by
      apply Sym.ext
      apply Multiset.map_injective (f := Subtype.val) Subtype.val_injective
      exact Multiset.cons_inj_right c.val |>.mp he
    subst n
    rfl
  have hcard := Fintype.card_le_of_injective g hg
  have hsize (c : A) : Fintype.card (Sym ↥(A.erase c.val) 2) = A.card.choose 2 := by
    rw [Sym.card_sym_eq_choose, Fintype.card_coe, card_erase_of_mem c.property]
    have hp : 0 < A.card := card_pos.mpr ⟨c.val, c.property⟩
    congr 1
    omega
  change Fintype.card ((c : A) × Sym ↥(A.erase c.val) 2) ≤ _ at hcard
  rw [Fintype.card_sigma] at hcard
  simp_rw [hsize] at hcard
  simpa using hcard



lemma f_signed_counting_bound (N : ℕ) : f N 3 * (f N 3).choose 2 ≤ 3 * N + 1 := by
  classical
  unfold f
  apply Finset.sup_induction (p := fun k : ℕ ↦ k * k.choose 2 ≤ 3 * N + 1)
  · norm_num
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa [sup_eq_right.mpr h] using hb
    · simpa [sup_eq_left.mpr h] using ha
  · intro A hA
    rcases mem_filter.mp hA with ⟨hsub, hA⟩
    exact signed_counting_bound N A (mem_powerset.mp hsub) hA

lemma f_cube_bound_improved (N : ℕ) : (f N 3)^3 ≤ 6 * N + (f N 3)^2 + 2 := by
  have hb : (f N 3 : ℝ) * ((f N 3).choose 2 : ℝ) ≤ 3 * N + 1 := by
    exact_mod_cast f_signed_counting_bound N
  have heq := Nat.cast_choose_two (K := ℝ) (f N 3)
  have hg : (f N 3 : ℝ)^3 ≤ 6 * N + (f N 3 : ℝ)^2 + 2 := by
    nlinarith
  exact_mod_cast hg



lemma f_bose_chowla (p : ℕ) [Fact p.Prime] : p ≤ f (p^3 - 1) 3 := by
  classical
  obtain ⟨A, hAN, hcard, hA⟩ := BoseConstruction.bose_chowla_sets p
  conv_lhs => rw [← hcard]
  unfold f
  apply Finset.le_sup
  exact mem_filter.mpr ⟨mem_powerset.mpr hAN, hA⟩

lemma f_bose_lower_bound (n : ℕ) : n ≤ f (8 * n^3) 3 := by
  by_cases hn : n = 0
  · simp [hn]
  obtain ⟨p, hp, hnp, hpn⟩ := Nat.bertrand n hn
  haveI : Fact p.Prime := ⟨hp⟩
  apply hnp.le.trans
  apply (f_bose_chowla p).trans
  apply f_monotone
  have hpow := Nat.pow_le_pow_left hpn 3
  nlinarith [Nat.sub_le (p^3) 1]



lemma f_reverse_cube_bound (N : ℕ) (hN : 8 ≤ N) : N ≤ 64 * (f N 3)^3 := by
  let n := Nat.nthRoot 3 (N / 8)
  have hn : 1 ≤ n := (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr (by simp; omega)
  have hs : n^3 ≤ N / 8 := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hsmall : 8 * n^3 ≤ N := by omega
  have hf : n ≤ f N 3 := (f_bose_lower_bound n).trans (f_monotone 3 hsmall)
  have hl : N / 8 < (n + 1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hlarge : N < 8 * (n + 1)^3 := by omega
  have hpow := Nat.pow_le_pow_left (show n + 1 ≤ 2 * n by omega) 3
  have hpow' := Nat.pow_le_pow_left hf 3
  nlinarith

lemma f_cuberoot_bounds :
    ∀ᶠ N : ℕ in atTop,
      (f N 3 : ℝ) ≤ 3 * (N : ℝ)^((1 : ℝ) / 3) ∧
      (N : ℝ)^((1 : ℝ) / 3) ≤ 4 * (f N 3 : ℝ) := by
  filter_upwards [eventually_ge_atTop 8] with N hN
  have hpos : (0 : ℝ) ≤ (N : ℝ)^((1 : ℝ) / 3) := Real.rpow_nonneg (by positivity) _
  have hr : ((N : ℝ)^((1 : ℝ) / 3))^3 = N := by
    simpa [one_div] using Real.rpow_inv_natCast_pow (x := (N : ℝ)) (n := 3)
      (by positivity) (by decide)
  constructor
  · apply (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp
    rw [mul_pow, hr]
    have hb : (f N 3 : ℝ)^3 ≤ 18 * N + 6 := by exact_mod_cast f_cube_bound N
    have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
    norm_num
    linarith
  · apply (pow_le_pow_iff_left₀ hpos (by positivity) (by decide : 3 ≠ 0)).mp
    rw [mul_pow, hr]
    norm_num
    exact_mod_cast f_reverse_cube_bound N hN

lemma f_isTheta :
    (fun N : ℕ ↦ (f N 3 : ℝ)) =Θ[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ) / 3)) := by
  constructor
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨3, f_cuberoot_bounds.mono ?_⟩
    intro N hN
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN.1
  · apply Asymptotics.isBigO_iff.mpr
    refine ⟨4, f_cuberoot_bounds.mono ?_⟩
    intro N hN
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)] using hN.2



lemma f_cube_ratio_eventually_lt (c : ℝ) (hc : 6 < c) :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3 / N < c := by
  let R : ℕ → ℝ := fun N ↦ (N : ℝ)^((1 : ℝ) / 3)
  have hRt : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hHt : Tendsto (fun N : ℕ ↦ 6 + 9 / R N + 2 / (N : ℝ)) atTop (nhds 6) := by
    simpa using ((tendsto_const_nhds (x := (6 : ℝ))).add (hRt.const_div_atTop 9)).add
      (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
  filter_upwards [eventually_ge_atTop 8, f_cuberoot_bounds,
    hHt.eventually_lt_const hc] with N hN hbound hH
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R N := Real.rpow_pos_of_pos hNp _
  have hr : (R N)^3 = N := by
    simpa [R, one_div] using Real.rpow_inv_natCast_pow (x := (N : ℝ)) (n := 3)
      hNp.le (by decide)
  have hs : (f N 3 : ℝ)^2 ≤ 9 * (R N)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ f N 3) hbound.1 2
    norm_num [mul_pow] at hh
    exact hh
  have hf : (f N 3 : ℝ)^3 ≤ 6 * N + (f N 3 : ℝ)^2 + 2 := by
    exact_mod_cast f_cube_bound_improved N
  apply lt_of_le_of_lt _ hH
  apply (div_le_iff₀ hNp).mpr
  have hh : (6 + 9 / R N + 2 / (N : ℝ)) * N = 6 * N + 9 * (R N)^2 + 2 := by
    rw [← hr]
    field_simp
  rw [hh]
  linarith

lemma f_cube_ratio_frequently_ge_one :
    ∃ᶠ N : ℕ in atTop, 1 ≤ (f N 3 : ℝ)^3 / N := by
  apply frequently_atTop.mpr
  intro K
  obtain ⟨p, hKp, hp⟩ := Nat.exists_infinite_primes K
  haveI : Fact p.Prime := ⟨hp⟩
  have hpow : p ≤ p^3 := Nat.le_pow (by decide)
  refine ⟨p^3, hKp.trans hpow, ?_⟩
  have hf : p ≤ f (p^3) 3 := (f_bose_chowla p).trans (f_monotone 3 (Nat.sub_le _ _))
  have hfp : p^3 ≤ (f (p^3) 3)^3 := Nat.pow_le_pow_left hf 3
  have hpp : (0 : ℝ) < (p^3 : ℕ) := by exact_mod_cast pow_pos hp.pos 3
  apply (le_div_iff₀ hpp).mpr
  simpa using (show ((p^3 : ℕ) : ℝ) ≤ (f (p^3) 3 : ℝ)^3 by exact_mod_cast hfp)


namespace B3Aux

def Good (A : Finset ℕ) : Prop :=
  ∀ m₁ m₂ : Multiset ℕ, m₁.card = 3 → m₂.card = 3 →
    (∀ x ∈ m₁, x ∈ A) → (∀ x ∈ m₂, x ∈ A) →
    m₁.sum = m₂.sum → m₁ = m₂

lemma sum_two_inj {A : Finset ℕ} (hA : Good A) (s t : Multiset ℕ)
    (hs : s.card = 2) (ht : t.card = 2)
    (hsm : ∀ x ∈ s, x ∈ A) (htm : ∀ x ∈ t, x ∈ A)
    (he : s.sum = t.sum) : s = t := by
  obtain ⟨a, ha⟩ := Multiset.card_pos_iff_exists_mem.mp (by omega : 0 < s.card)
  apply Multiset.cons_inj_right a |>.mp
  apply hA (a ::ₘ s) (a ::ₘ t) (by simp [hs]) (by simp [ht])
  · simpa using And.intro (hsm a ha) hsm
  · simpa using And.intro (hsm a ha) htm
  · simp [he]

noncomputable def pairSums (A : Finset ℕ) : Finset ℕ :=
  (A.powersetCard 2).image (fun P ↦ ∑ a ∈ P, a)

lemma pair_sum_inj {A : Finset ℕ} (hA : Good A) :
    Set.InjOn (fun P : Finset ℕ ↦ ∑ a ∈ P, a) (A.powersetCard 2) := by
  intro P hP Q hQ he
  rcases mem_powersetCard.mp hP with ⟨hPA, hPc⟩
  rcases mem_powersetCard.mp hQ with ⟨hQA, hQc⟩
  apply Finset.val_injective
  exact sum_two_inj hA P.val Q.val hPc hQc hPA hQA (by simpa only [Finset.sum_val, id_eq] using he)

lemma card_pairSums {A : Finset ℕ} (hA : Good A) : (pairSums A).card = A.card.choose 2 := by
  rw [pairSums, card_image_of_injOn (pair_sum_inj hA), card_powersetCard]

lemma mem_pairSums_iff {A : Finset ℕ} {s : ℕ} :
    s ∈ pairSums A ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ s = a + b := by
  classical
  constructor
  · intro h
    obtain ⟨P, hP, rfl⟩ := mem_image.mp h
    rcases mem_powersetCard.mp hP with ⟨hPA, hPc⟩
    obtain ⟨a, b, hab, rfl⟩ := card_eq_two.mp hPc
    refine ⟨a, hPA (by simp), b, hPA (by simp), hab, ?_⟩
    simp [hab]
  · rintro ⟨a, ha, b, hb, hab, rfl⟩
    apply mem_image.mpr
    refine ⟨{a,b}, mem_powersetCard.mpr ⟨?_, ?_⟩, ?_⟩
    · exact insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩
    · simp [hab]
    · simp [hab]

lemma three_sum_mem {A : Finset ℕ} (hA : Good A)
    {a b c d e f : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A)
    (hd : d ∈ A) (he : e ∈ A) (hf : f ∈ A)
    (hs : a + b + c = d + e + f) : a = d ∨ a = e ∨ a = f := by
  have hh := hA {a,b,c} {d,e,f} (by simp) (by simp)
    (by simp [ha,hb,hc]) (by simp [hd,he,hf]) (by simpa [add_assoc] using hs)
  have hm : a ∈ ({d,e,f} : Multiset ℕ) := hh ▸ (by simp : a ∈ ({a,b,c} : Multiset ℕ))
  simpa using hm



noncomputable def shiftReps (A : Finset ℕ) (i j : ℕ) : Finset (ℕ × ℕ) :=
  ((pairSums A) ×ˢ (pairSums A)).filter (fun r ↦ r.1 + i = r.2 + j)

lemma shiftReps_mem {A : Finset ℕ} {i j : ℕ} {r : ℕ × ℕ} :
    r ∈ shiftReps A i j ↔ r.1 ∈ pairSums A ∧ r.2 ∈ pairSums A ∧ r.1 + i = r.2 + j := by
  simp [shiftReps, and_assoc]

lemma other_summand_unique {A : Finset ℕ} (hA : Good A) {i j a b b' t t' : ℕ}
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a + i ≠ b + j)
    (ha : a ∈ A) (hb : b ∈ A) (hb' : b' ∈ A)
    (ht : t ∈ pairSums A) (ht' : t' ∈ pairSums A)
    (he : a + b + i = t + j) (he' : a + b' + i = t' + j) : b = b' := by
  obtain ⟨c, hc, d, hd, hcd, rfl⟩ := mem_pairSums_iff.mp ht
  obtain ⟨e, heA, f, hf, hef, rfl⟩ := mem_pairSums_iff.mp ht'
  have hs : b + e + f = b' + c + d := by omega
  rcases three_sum_mem hA hb heA hf hb' hc hd hs with h | h | h
  · exact h
  · exfalso
    apply hNo a ha d hd
    omega
  · exfalso
    apply hNo a ha c hc
    omega

lemma shiftReps_bound_good {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a + i ≠ b + j) :
    2 * (shiftReps A i j).card ≤ A.card := by
  classical
  let R := shiftReps A i j
  have hR (r : R) : r.val.1 ∈ pairSums A ∧ r.val.2 ∈ pairSums A ∧
      r.val.1 + i = r.val.2 + j := shiftReps_mem.mp r.property
  have hex (r : R) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ r.val.1 = a + b :=
    mem_pairSums_iff.mp (hR r).1
  choose a ha b hb hab hs using hex
  let P (r : R) : Finset ℕ := {a r, b r}
  have hPc (r : R) : (P r).card = 2 := by simp [P, hab r]
  have hPA (r : R) : P r ⊆ A :=
    insert_subset_iff.mpr ⟨ha r, singleton_subset_iff.mpr (hb r)⟩
  have hPs (r : R) {x : ℕ} (hx : x ∈ P r) : ∃ y ∈ A, r.val.1 = x + y := by
    simp only [P, mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨b r, hb r, hs r⟩
    · exact ⟨a r, ha r, by simpa [add_comm] using hs r⟩
  have hdis : (↑(univ : Finset R) : Set R).PairwiseDisjoint P := by
    intro r hr r' hr' hne
    apply disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y, hy, hxy⟩ := hPs r hx
    obtain ⟨y', hy', hxy'⟩ := hPs r' hx'
    have her := (hR r).2.2
    have her' := (hR r').2.2
    have hyy' : y = y' := other_summand_unique hA hNo (hPA r hx) hy hy'
      (hR r).2.1 (hR r').2.1 (by omega) (by omega)
    apply hne
    apply Subtype.ext
    apply Prod.ext
    · omega
    · have he := (hR r).2.2
      have he' := (hR r').2.2
      omega
  have hu : (univ.biUnion P : Finset ℕ) ⊆ A := by
    intro x hx
    obtain ⟨r, hr, hxr⟩ := mem_biUnion.mp hx
    exact hPA r hxr
  have hh := card_le_card hu
  rw [card_biUnion hdis] at hh
  simp_rw [hPc] at hh
  simpa [R, mul_comm] using hh

lemma shiftReps_bound_bad {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hij : i ≠ j) {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a + i = b + j) :
    (shiftReps A i j).card ≤ A.card := by
  have hab' : a ≠ b := by omega
  have hex (r : ℕ × ℕ) (hr : r ∈ shiftReps A i j) :
      ∃ z ∈ A, r.1 = a + z ∧ r.2 = b + z := by
    rcases shiftReps_mem.mp hr with ⟨hs, ht, heq⟩
    obtain ⟨c, hc, d, hd, hcd, hcds⟩ := mem_pairSums_iff.mp hs
    obtain ⟨e, he, f, hf, hef, heft⟩ := mem_pairSums_iff.mp ht
    have hh : a + e + f = b + c + d := by omega
    rcases three_sum_mem hA ha he hf hb hc hd hh with h | h | h
    · exact (hab' h).elim
    · exact ⟨d, hd, by omega, by omega⟩
    · exact ⟨c, hc, by omega, by omega⟩
  apply card_le_card_of_injOn (fun r : ℕ × ℕ ↦ r.1 - a)
  · intro r hr
    obtain ⟨z, hz, he, he'⟩ := hex r hr
    simpa [he] using hz
  · intro r hr r' hr' hh
    dsimp only at hh
    obtain ⟨z, hz, he, he'⟩ := hex r hr
    obtain ⟨w, hw, hf, hf'⟩ := hex r' hr'
    apply Prod.ext <;> omega



lemma shiftReps_self (A : Finset ℕ) (i : ℕ) :
    (shiftReps A i i).card = (pairSums A).card := by
  have h : shiftReps A i i = (pairSums A).diag := by
    ext ⟨x,y⟩
    simp only [shiftReps_mem, mem_diag]
    aesop
  rw [h, diag_card]

lemma energy_eq_shift (A T : Finset ℕ) :
    addEnergy (pairSums A) T = ∑ ij ∈ T ×ˢ T, (shiftReps A ij.1 ij.2).card := by
  rw [addEnergy_comm, addEnergy]
  simp only [shiftReps, card_eq_sum_ones, sum_filter, sum_product, add_comm]

noncomputable def badShifts (A T : Finset ℕ) : Finset (ℕ × ℕ) :=
  (T ×ˢ T).filter (fun ij ↦ ∃ a ∈ A, ∃ b ∈ A, a + ij.1 = b + ij.2)

lemma card_badShifts (A T : Finset ℕ) : (badShifts A T).card ≤ A.card^2 * T.card := by
  classical
  have hsub : badShifts A T ⊆ ((A ×ˢ A) ×ˢ T).image
      (fun p : (ℕ × ℕ) × ℕ ↦ (p.2, p.1.1 + p.2 - p.1.2)) := by
    intro ij hij
    rcases mem_filter.mp hij with ⟨hijT, a, ha, b, hb, heq⟩
    apply mem_image.mpr
    refine ⟨((a,b),ij.1), ?_, ?_⟩
    · exact mem_product.mpr ⟨mem_product.mpr ⟨ha,hb⟩, (mem_product.mp hijT).1⟩
    · apply Prod.ext <;> dsimp
      omega
  calc
    _ ≤ (((A ×ˢ A) ×ˢ T).image
        (fun p : (ℕ × ℕ) × ℕ ↦ (p.2, p.1.1 + p.2 - p.1.2))).card := card_le_card hsub
    _ ≤ ((A ×ˢ A) ×ˢ T).card := card_image_le
    _ = _ := by simp [card_product, pow_two]

lemma energy_bound {A : Finset ℕ} (hA : Good A) (T : Finset ℕ) :
    2 * addEnergy (pairSums A) T ≤
      A.card * T.card^2 + 2 * (pairSums A).card * T.card + 2 * A.card^3 * T.card := by
  classical
  have hpoint (ij : ℕ × ℕ) :
      2 * (shiftReps A ij.1 ij.2).card ≤ A.card +
        (if ij.1 = ij.2 then 2 * (pairSums A).card else 0) +
        (if ∃ a ∈ A, ∃ b ∈ A, a + ij.1 = b + ij.2 then 2 * A.card else 0) := by
    by_cases hij : ij.1 = ij.2
    · simp only [hij, shiftReps_self, if_true]
      omega
    · simp only [hij, if_false, add_zero]
      split_ifs with h
      · obtain ⟨a, ha, b, hb, hab⟩ := h
        have hh := shiftReps_bound_bad hA ij.1 ij.2 hij ha hb hab
        omega
      · have hh := shiftReps_bound_good hA ij.1 ij.2 (by simpa using h)
        exact hh
  have hsum := sum_le_sum (s := T ×ˢ T) (fun ij hij ↦ hpoint ij)
  have hdiag : (T ×ˢ T).filter (fun ij : ℕ × ℕ ↦ ij.1 = ij.2) = T.diag := by
    ext ⟨x,y⟩
    simp only [mem_filter, mem_product, mem_diag]
    aesop
  have hd : (∑ ij ∈ T ×ˢ T, if ij.1 = ij.2 then 2 * (pairSums A).card else 0) =
      2 * (pairSums A).card * T.card := by
    rw [← sum_filter, hdiag]
    simp [mul_comm]
  have hb : (∑ ij ∈ T ×ˢ T,
      if ∃ a ∈ A, ∃ b ∈ A, a + ij.1 = b + ij.2 then 2 * A.card else 0) =
      2 * A.card * (badShifts A T).card := by
    rw [← sum_filter]
    simp [badShifts, mul_comm]
  rw [← mul_sum, ← energy_eq_shift, sum_add_distrib, sum_add_distrib, hd, hb] at hsum
  simp only [sum_const, card_product, nsmul_eq_mul] at hsum
  have hbad := card_badShifts A T
  nlinarith



lemma cauchy_energy_bound {A : Finset ℕ} (hA : Good A) (N u : ℕ)
    (hAN : A ⊆ Icc 1 N) :
    2 * (A.card.choose 2)^2 * u^2 ≤ (2 * N + u) *
      (A.card * u^2 + 2 * A.card.choose 2 * u + 2 * A.card^3 * u) := by
  classical
  open scoped Pointwise in
  have hsumcard : (pairSums A + range u).card ≤ 2 * N + u := by
    apply (card_le_card (show pairSums A + range u ⊆ range (2 * N + u) from ?_)).trans
    · simp
    · intro x hx
      obtain ⟨s, hs, t, ht, rfl⟩ := mem_add.mp hx
      obtain ⟨a, ha, b, hb, hab, rfl⟩ := mem_pairSums_iff.mp hs
      have haN := (mem_Icc.mp (hAN ha)).2
      have hbN := (mem_Icc.mp (hAN hb)).2
      have htN := mem_range.mp ht
      exact mem_range.mpr (by omega)
  have hc := le_card_add_mul_addEnergy (pairSums A) (range u)
  have he := energy_bound hA (range u)
  simp only [card_range, card_pairSums hA] at hc he
  have hh := hc.trans (Nat.mul_le_mul_right _ hsumcard)
  have he' := Nat.mul_le_mul_left (2 * N + u) he
  nlinarith

end B3Aux

lemma f_cauchy_energy_bound (N u : ℕ) :
    2 * ((f N 3).choose 2)^2 * u^2 ≤ (2 * N + u) *
      (f N 3 * u^2 + 2 * (f N 3).choose 2 * u + 2 * (f N 3)^3 * u) := by
  classical
  unfold f
  apply Finset.sup_induction (p := fun n : ℕ ↦
    2 * (n.choose 2)^2 * u^2 ≤ (2 * N + u) *
      (n * u^2 + 2 * n.choose 2 * u + 2 * n^3 * u))
  · norm_num
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa [sup_eq_right.mpr h] using hb
    · simpa [sup_eq_left.mpr h] using ha
  · intro A hA
    rcases mem_filter.mp hA with ⟨hsub, hA⟩
    exact B3Aux.cauchy_energy_bound hA N u (mem_powerset.mp hsub)



lemma f_four_bound (N k : ℕ) (hk : 0 < k) :
    (k : ℝ) * (f N 3 : ℝ)^3 ≤ (4 * k + 12) * N +
      (2 * (k : ℝ)^2 + 8 * k) * (f N 3 : ℝ)^2 := by
  by_cases hn0 : f N 3 = 0
  · simp [hn0]
    positivity
  let n : ℝ := f N 3
  let m : ℝ := (f N 3).choose 2
  let u : ℝ := k * n^2
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast (show 1 ≤ f N 3 by omega)
  have hnpos : 0 < n := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : 0 < u := by dsimp [u]; positivity
  have heq : 2 * m = n * (n - 1) := by
    dsimp [m, n]
    rw [Nat.cast_choose_two]
    ring
  have hraw : 2 * m^2 * u^2 ≤ (2 * N + u) *
      (n * u^2 + 2 * m * u + 2 * n^3 * u) := by
    dsimp [m, n, u]
    exact_mod_cast f_cauchy_energy_bound N (k * (f N 3)^2)
  have hmc : 2 * m ≤ n^3 := by
    have hh := mul_le_mul_of_nonneg_right hn (sq_nonneg n)
    nlinarith
  have hmid : n * u^2 + 2 * m * u + 2 * n^3 * u ≤ n * u * n^2 * (k + 3) := by
    calc
      _ ≤ n * u^2 + 3 * n^3 * u := by nlinarith [mul_le_mul_of_nonneg_right hmc hu.le]
      _ = _ := by dsimp [u]; ring
  have he : 2 * m^2 * u^2 ≤ (2 * N + u) * (n * u * n^2 * (k + 3)) :=
    hraw.trans (mul_le_mul_of_nonneg_left hmid (by positivity))
  have h₁ : 2 * m^2 * u ≤ (2 * N + u) * n * n^2 * (k + 3) := by
    apply (mul_le_mul_iff_right₀ hu).mp
    calc
      _ = 2 * m^2 * u^2 := by ring
      _ ≤ _ := he
      _ = _ := by ring
  have h₂ : 2 * (k : ℝ) * m^2 ≤ (2 * N + u) * n * (k + 3) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hnpos 2)).mp
    convert h₁ using 1 <;> dsimp [u] <;> ring
  have heq₂ : 4 * m^2 = n^2 * (n - 1)^2 := by
    nlinarith only [congrArg (fun x : ℝ ↦ x^2) heq]
  have h₃ : (k : ℝ) * n * (n - 1)^2 ≤ 2 * (2 * N + u) * (k + 3) := by
    apply (mul_le_mul_iff_right₀ hnpos).mp
    calc
      _ = (k : ℝ) * (n^2 * (n - 1)^2) := by ring
      _ = (k : ℝ) * (4 * m^2) := by rw [heq₂]
      _ = 2 * (2 * (k : ℝ) * m^2) := by ring
      _ ≤ 2 * ((2 * N + u) * n * (k + 3)) := mul_le_mul_of_nonneg_left h₂ (by norm_num)
      _ = _ := by ring
  change (k : ℝ) * n^3 ≤ (4 * k + 12) * N + (2 * (k : ℝ)^2 + 8 * k) * n^2
  dsimp [u] at h₃
  nlinarith [mul_nonneg hkpos.le hnpos.le]



lemma f_square_ratio_tendsto_zero :
    Tendsto (fun N : ℕ ↦ (f N 3 : ℝ)^2 / N) atTop (nhds 0) := by
  have hRt : Tendsto (fun N : ℕ ↦ (N : ℝ)^((1 : ℝ) / 3)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity)) _ (hRt.const_div_atTop 9)
  filter_upwards [eventually_ge_atTop 8, f_cuberoot_bounds] with N hN hbound
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < (N : ℝ)^((1 : ℝ) / 3) := Real.rpow_pos_of_pos hNp _
  have hr : ((N : ℝ)^((1 : ℝ) / 3))^3 = N := by
    simpa [one_div] using Real.rpow_inv_natCast_pow (x := (N : ℝ)) (n := 3)
      hNp.le (by decide)
  apply (div_le_iff₀ hNp).mpr
  have he : (9 / (N : ℝ)^((1 : ℝ) / 3)) * N =
      9 * ((N : ℝ)^((1 : ℝ) / 3))^2 := by
    conv_lhs => rhs; rw [← hr]
    field_simp
  rw [he]
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ f N 3) hbound.1 2
  norm_num [mul_pow] at hh
  exact hh

lemma f_cube_ratio_eventually_lt_four (c : ℝ) (hc : 4 < c) :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3 / N < c := by
  obtain ⟨k, hk⟩ := exists_nat_gt (12 / (c - 4))
  have hkpos : (0 : ℝ) < k := (div_pos (by norm_num) (sub_pos.mpr hc)).trans hk
  have hk' : 0 < k := by exact_mod_cast hkpos
  have hlim : (4 * (k : ℝ) + 12) / k < c := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh := (div_lt_iff₀ (sub_pos.mpr hc)).mp hk
    nlinarith
  let a : ℝ := 4 * k + 12
  let b : ℝ := 2 * (k : ℝ)^2 + 8 * k
  have hHt : Tendsto (fun N : ℕ ↦ a / k + (b / k) * ((f N 3 : ℝ)^2 / N)) atTop (nhds (a / k)) := by
    simpa using (tendsto_const_nhds (x := a / (k : ℝ))).add
      ((tendsto_const_nhds (x := b / (k : ℝ))).mul f_square_ratio_tendsto_zero)
  filter_upwards [eventually_ge_atTop 1, hHt.eventually_lt_const hlim] with N hN hH
  apply lt_of_le_of_lt _ hH
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNp).mpr
  have he : (a / k + (b / k) * ((f N 3 : ℝ)^2 / N)) * N =
      (a * N + b * (f N 3 : ℝ)^2) / k := by
    field_simp
  rw [he]
  apply (le_div_iff₀ hkpos).mpr
  simpa [a, b, mul_comm] using f_four_bound N k hk'

/- A family showing why the pointwise pair-sum multiplicity estimate cannot
be improved asymptotically without using the diameter or other global information. -/

open Finset Polynomial

namespace SharpFamily

set_option maxHeartbeats 1000000

variable {ι α β G H J : Type*} [AddCommGroup G] [AddCommGroup H] [AddCommGroup J]

def SumUnique (code : ι → G) : Prop :=
  ∀ s t : Multiset ι, s.card = t.card → (s.map code).sum = (t.map code).sum → s = t

lemma sum_unique_of_separating [DecidableEq ι] (code : ι → G) (z : ℤ) (hz : z ≠ 0)
    (sep : ι → G →+ ℤ)
    (hsep : ∀ i j, sep i (code j) = if i = j then z else 0) : SumUnique code := by
  classical
  intro s t hc he
  apply Multiset.ext.mpr
  intro i
  have hm (m : Multiset ι) : sep i (m.map code).sum = (m.count i : ℤ) * z := by
    rw [map_multiset_sum, Multiset.map_map]
    have hh := Multiset.sum_map_eq_nsmul_single (m := m)
      (f := fun j ↦ sep i (code j)) i (by
        intro j hj hjm
        simp [hsep, Ne.symm hj])
    simpa [Function.comp_def, hsep, nsmul_eq_mul] using hh
  have hh := congrArg (sep i) he
  rw [hm s, hm t] at hh
  exact_mod_cast (mul_right_cancel₀ hz hh)

lemma exists_disjSum (m : Multiset (α ⊕ β)) :
    ∃ s : Multiset α, ∃ t : Multiset β, m = s.disjSum t := by
  induction m using Multiset.induction_on with
  | empty => exact ⟨0, 0, rfl⟩
  | @cons x m ih =>
    obtain ⟨s, t, rfl⟩ := ih
    cases x with
    | inl a => exact ⟨a ::ₘ s, t, by simp [Multiset.disjSum]⟩
    | inr b => exact ⟨s, b ::ₘ t, by simp [Multiset.disjSum]⟩

lemma sum_map_disjSum (l : α → G) (r : β → G) (s : Multiset α) (t : Multiset β) :
    ((s.disjSum t).map (Sum.elim l r)).sum = (s.map l).sum + (t.map r).sum := by
  simp [Multiset.map_disjSum]

lemma map_sum_zero (q : G →+ H) (f : ι → G) (hf : ∀ i, q (f i) = 0)
    (s : Multiset ι) : q (s.map f).sum = 0 := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [hf]

lemma map_sum_one (q : G →+ ℤ) (f : ι → G) (hf : ∀ i, q (f i) = 1)
    (s : Multiset ι) : q (s.map f).sum = s.card := by
  rw [map_multiset_sum, Multiset.map_map]
  simp [hf]

lemma union_three_unique
    (l : α → G) (r : β → G) (hl : SumUnique l) (hr : SumUnique r)
    (color : G →+ ℤ) (hcl : ∀ a, color (l a) = 0) (hcr : ∀ b, color (r b) = 1)
    (ql : G →+ H) (hql : Function.Injective (ql ∘ l)) (hqlr : ∀ b, ql (r b) = 0)
    (qr : G →+ J) (hqr : Function.Injective (qr ∘ r)) (hqrl : ∀ a, qr (l a) = 0)
    (s t : Multiset (α ⊕ β)) (hsc : s.card = 3) (htc : t.card = 3)
    (he : (s.map (Sum.elim l r)).sum = (t.map (Sum.elim l r)).sum) : s = t := by
  obtain ⟨sl, sr, rfl⟩ := exists_disjSum s
  obtain ⟨tl, tr, rfl⟩ := exists_disjSum t
  simp only [Multiset.card_disjSum] at hsc htc
  simp only [sum_map_disjSum] at he
  have hrc : sr.card = tr.card := by
    have hc := congrArg color he
    simp only [map_add, map_sum_zero color l hcl, map_sum_one color r hcr, zero_add] at hc
    exact_mod_cast hc
  have hlc : sl.card = tl.card := by omega
  have hle : sr.card ≤ 3 := by omega
  interval_cases h : sr.card
  · have hsr : sr = 0 := Multiset.card_eq_zero.mp h
    have htr : tr = 0 := Multiset.card_eq_zero.mp (by omega)
    subst sr tr
    simp only [Multiset.map_zero, Multiset.sum_zero, add_zero] at he
    rw [hl sl tl hlc he]
  · obtain ⟨b, rfl⟩ := Multiset.card_eq_one.mp h
    obtain ⟨b', rfl⟩ := Multiset.card_eq_one.mp (by simpa using hrc.symm)
    simp only [Multiset.map_singleton, Multiset.sum_singleton] at he
    have hb : b = b' := by
      apply hqr
      have hh := congrArg qr he
      simpa only [map_add, map_sum_zero qr l hqrl, zero_add, Function.comp_def] using hh
    subst b'
    have hlt := hl sl tl hlc (add_right_cancel he)
    rw [hlt]
  · have hsl : sl.card = 1 := by omega
    have htl : tl.card = 1 := by omega
    obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp hsl
    obtain ⟨a', rfl⟩ := Multiset.card_eq_one.mp htl
    simp only [Multiset.map_singleton, Multiset.sum_singleton] at he
    have ha : a = a' := by
      apply hql
      have hh := congrArg ql he
      simpa only [map_add, map_sum_zero ql r hqlr, add_zero, Function.comp_def] using hh
    subst a'
    have hrt := hr sr tr (by omega) (add_left_cancel he)
    rw [hrt]
  · have hsl : sl = 0 := Multiset.card_eq_zero.mp (by omega)
    have htl : tl = 0 := Multiset.card_eq_zero.mp (by omega)
    subst sl tl
    simp only [Multiset.map_zero, Multiset.sum_zero, zero_add] at he
    rw [hr sr tr (by omega) he]


section Polynomials

noncomputable def cf (n : ℕ) : ℤ[X] →+ ℤ := (lcoeff ℤ n).toAddMonoidHom

@[simp] lemma cf_apply (n : ℕ) (p : ℤ[X]) : cf n p = p.coeff n := rfl

noncomputable def left (k : ℕ) (i : Fin k) : ℤ[X] := X^(i.val + 1)

noncomputable def right (k : ℕ) (j : Fin (k+1)) : ℤ[X] :=
  X^(k+1) + C (j.val : ℤ) - X^(j.val % k + 1)

noncomputable def tag (k : ℕ) : ℤ[X] →+ ℤ :=
  cf 0 + (evalRingHom (1 : ℤ)).toAddMonoidHom.comp derivative.toAddMonoidHom - k • cf (k+1)

@[simp] lemma tag_apply (k : ℕ) (p : ℤ[X]) :
    tag k p = p.coeff 0 + p.derivative.eval 1 - k * p.coeff (k+1) := by
  simp [tag]

lemma color_left (k : ℕ) (i : Fin k) : cf (k+1) (left k i) = 0 := by
  simp [left, coeff_X_pow, show k ≠ i.val by omega]

lemma color_right (k : ℕ) (hk : 0 < k) (j : Fin (k+1)) :
    cf (k+1) (right k j) = 1 := by
  have hm : j.val % k < k := Nat.mod_lt _ hk
  simp [right, coeff_X_pow, show k ≠ j.val % k by omega]

lemma index_left (k : ℕ) (i : Fin k) : cf 0 (left k i) = 0 := by
  simp [left, coeff_X_pow]

lemma index_right (k : ℕ) (j : Fin (k+1)) : cf 0 (right k j) = j.val := by
  simp [right, coeff_X_pow]

lemma tag_left (k : ℕ) (i : Fin k) : tag k (left k i) = i.val + 1 := by
  simp [tag_apply, left, coeff_X_pow, show k ≠ i.val by omega]

lemma tag_right (k : ℕ) (hk : 0 < k) (j : Fin (k+1)) :
    tag k (right k j) = (j.val : ℤ) - (j.val % k : ℕ) := by
  have hc := color_right k hk j
  have hi := index_right k j
  rw [cf_apply] at hc hi
  rw [tag_apply, hc, hi]
  simp [right]
  ring

lemma left_sum_unique (k : ℕ) : SumUnique (left k) := by
  apply sum_unique_of_separating (left k) 1 (by decide) (fun i ↦ cf (i.val+1))
  intro i j
  simp [left, coeff_X_pow, Fin.ext_iff]

noncomputable def rightSep (k : ℕ) (j : Fin (k+1)) : ℤ[X] →+ ℤ :=
  if j.val = k then tag k
  else if j.val = 0 then -(k • cf 1) - tag k
  else -(k • cf (j.val+1))

lemma mod_index (k : ℕ) (_hk : 0 < k) (j : Fin (k+1)) :
    j.val % k = if j.val = k then 0 else j.val := by
  split_ifs with h
  · simp [h]
  · exact Nat.mod_eq_of_lt (by omega)

lemma tag_right' (k : ℕ) (hk : 0 < k) (j : Fin (k+1)) :
    tag k (right k j) = if j.val = k then (k : ℤ) else 0 := by
  rw [tag_right k hk, mod_index k hk]
  split_ifs with h <;> simp [h]

lemma right_sep_apply (k : ℕ) (hk : 0 < k) (i j : Fin (k+1)) :
    rightSep k i (right k j) = if i = j then (k : ℤ) else 0 := by
  have hj : j.val ≤ k := by omega
  by_cases hiK : i.val = k
  · simp only [rightSep, hiK, if_true, tag_right' k hk]
    have hiff : j.val = k ↔ i = j :=
      ⟨fun h ↦ Fin.ext (hiK.trans h.symm), fun h ↦ h ▸ hiK⟩
    simp only [hiff]
  · by_cases hi0 : i.val = 0
    · rw [rightSep, if_neg hiK, if_pos hi0]
      change -(k • (right k j).coeff 1) - tag k (right k j) = _
      rw [tag_right' k hk]
      have hc : (right k j).coeff 1 = -(if 0 = j.val % k then (1 : ℤ) else 0) := by
        simp [right, coeff_X_pow, hk.ne', eq_comm]
      rw [hc, mod_index k hk]
      by_cases hjK : j.val = k
      · simp [hjK, show i ≠ j by intro h; have := congrArg Fin.val h; omega]
      · simp only [hjK, if_false]
        by_cases hj0 : j.val = 0
        · have he : i = j := Fin.ext (hi0.trans hj0.symm)
          simp [hj0, he]
        · have he : i ≠ j := by intro h; have := congrArg Fin.val h; omega
          simp [Ne.symm hj0, he]
    · simp only [rightSep, hiK, if_false, hi0, AddMonoidHom.neg_apply]
      have hc : (right k j).coeff (i.val+1) =
          -(if i.val = j.val % k then (1 : ℤ) else 0) := by
        simp [right, coeff_X_pow, hiK]
      change -((k : ℕ) • (right k j).coeff (i.val+1)) = _
      rw [hc, mod_index k hk]
      by_cases hjK : j.val = k
      · simp [hjK, hi0, show i ≠ j by intro h; have := congrArg Fin.val h; omega]
      · simp only [hjK, if_false]
        simp [Fin.ext_iff]

lemma right_sum_unique (k : ℕ) (hk : 0 < k) : SumUnique (right k) := by
  exact sum_unique_of_separating (right k) k (by exact_mod_cast hk.ne')
    (rightSep k) (right_sep_apply k hk)


noncomputable def tagMod (k : ℕ) : ℤ[X] →+ ZMod k :=
  (Int.castAddHom (ZMod k)).comp (tag k)

lemma tagMod_left (k : ℕ) (i : Fin k) : tagMod k (left k i) = (i.val : ZMod k) + 1 := by
  change ((tag k (left k i) : ℤ) : ZMod k) = _
  rw [tag_left]
  simp

lemma tagMod_right (k : ℕ) (hk : 0 < k) (j : Fin (k+1)) : tagMod k (right k j) = 0 := by
  simp [tagMod, tag_right k hk]

lemma tagMod_left_injective (k : ℕ) : Function.Injective (tagMod k ∘ left k) := by
  intro i j h
  simp only [Function.comp_apply, tagMod_left, add_left_inj] at h
  have hh := (ZMod.natCast_eq_natCast_iff _ _ k).mp h
  apply Fin.ext
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] using hh

lemma index_right_injective (k : ℕ) : Function.Injective (cf 0 ∘ right k) := by
  intro i j h
  simp only [Function.comp_apply, index_right] at h
  apply Fin.ext
  exact_mod_cast h

noncomputable def polyCode (k : ℕ) : Fin k ⊕ Fin (k+1) → ℤ[X] := Sum.elim (left k) (right k)

lemma polyCode_three_unique (k : ℕ) (hk : 0 < k)
    (s t : Multiset (Fin k ⊕ Fin (k+1))) (hs : s.card = 3) (ht : t.card = 3)
    (he : (s.map (polyCode k)).sum = (t.map (polyCode k)).sum) : s = t := by
  exact union_three_unique (left k) (right k) (left_sum_unique k) (right_sum_unique k hk)
    (cf (k+1)) (color_left k) (color_right k hk)
    (tagMod k) (tagMod_left_injective k) (tagMod_right k hk)
    (cf 0) (index_right_injective k) (index_left k) s t hs ht he

lemma polyCode_injective (k : ℕ) (hk : 0 < k) : Function.Injective (polyCode k) := by
  intro a b he
  cases a with
  | inl a =>
    cases b with
    | inl b => exact congrArg Sum.inl (tagMod_left_injective k (congrArg (tagMod k) he))
    | inr b =>
      have hh := congrArg (cf (k+1)) he
      simp only [polyCode, Sum.elim_inl, Sum.elim_inr, color_left, color_right k hk] at hh
      norm_num at hh
  | inr a =>
    cases b with
    | inl b =>
      have hh := congrArg (cf (k+1)) he
      simp only [polyCode, Sum.elim_inl, Sum.elim_inr, color_left, color_right k hk] at hh
      norm_num at hh
    | inr b => exact congrArg Sum.inr (index_right_injective k (congrArg (cf 0) he))

lemma exists_eval_injOn (S : Finset ℤ[X]) :
    ∃ B : ℕ, 2 ≤ B ∧ Set.InjOn (Polynomial.eval (B : ℤ)) S := by
  classical
  let bad : Finset ℤ := (S ×ˢ S).biUnion (fun pq ↦ (pq.1 - pq.2).roots.toFinset)
  let B := bad.sup Int.toNat + 2
  refine ⟨B, by omega, ?_⟩
  intro p hp q hq he
  by_contra hpq
  have hroot : (B : ℤ) ∈ (p-q).roots := by
    rw [mem_roots (sub_ne_zero.mpr hpq)]
    simpa [Polynomial.IsRoot, eval_sub] using sub_eq_zero.mpr he
  have hbad : (B : ℤ) ∈ bad := by
    apply mem_biUnion.mpr
    exact ⟨(p,q), mem_product.mpr ⟨hp,hq⟩, by simpa using hroot⟩
  have hh := Finset.le_sup (f := Int.toNat) hbad
  simp only [Int.toNat_natCast] at hh
  dsimp [B] at hh
  omega

noncomputable def polyTotal (k : ℕ) (m : Sym (Fin k ⊕ Fin (k+1)) 3) : ℤ[X] :=
  (m.val.map (polyCode k)).sum

lemma exists_eval_total_injective (k : ℕ) (hk : 0 < k) :
    ∃ B : ℕ, 2 ≤ B ∧ Function.Injective (fun m : Sym (Fin k ⊕ Fin (k+1)) 3 ↦
      (polyTotal k m).eval (B : ℤ)) := by
  classical
  obtain ⟨B,hB,hI⟩ := exists_eval_injOn (univ.image (polyTotal k))
  refine ⟨B,hB,?_⟩
  intro s t he
  apply Subtype.ext
  apply polyCode_three_unique k hk s.val t.val s.property t.property
  exact hI (mem_image.mpr ⟨s, mem_univ _, rfl⟩) (mem_image.mpr ⟨t, mem_univ _, rfl⟩) he

lemma left_eval_pos (k B : ℕ) (hB : 2 ≤ B) (i : Fin k) :
    0 < (left k i).eval (B : ℤ) := by
  simp only [left, eval_X_pow]
  positivity

lemma right_eval_pos (k B : ℕ) (hk : 0 < k) (hB : 2 ≤ B) (j : Fin (k+1)) :
    0 < (right k j).eval (B : ℤ) := by
  have hb : (1 : ℤ) < B := by exact_mod_cast (show 1 < B by omega)
  have hp : (B : ℤ)^(j.val % k + 1) < (B : ℤ)^(k+1) :=
    pow_lt_pow_right₀ hb (by have := Nat.mod_lt j.val hk; omega)
  simp only [right, eval_sub, eval_add, eval_X_pow, eval_C]
  have hj : (0 : ℤ) ≤ j.val := by positivity
  omega

lemma polyCode_eval_pos (k B : ℕ) (hk : 0 < k) (hB : 2 ≤ B)
    (a : Fin k ⊕ Fin (k+1)) : 0 < (polyCode k a).eval (B : ℤ) := by
  cases a with
  | inl i => exact left_eval_pos k B hB i
  | inr j => exact right_eval_pos k B hk hB j


noncomputable def natCode (k B : ℕ) (a : Fin k ⊕ Fin (k+1)) : ℕ :=
  ((polyCode k a).eval (B : ℤ)).toNat

lemma natCode_cast (k B : ℕ) (hk : 0 < k) (hB : 2 ≤ B)
    (a : Fin k ⊕ Fin (k+1)) :
    (natCode k B a : ℤ) = (polyCode k a).eval (B : ℤ) :=
  Int.toNat_of_nonneg (polyCode_eval_pos k B hk hB a).le

lemma natTotal_cast (k B : ℕ) (hk : 0 < k) (hB : 2 ≤ B)
    (m : Sym (Fin k ⊕ Fin (k+1)) 3) :
    ((m.val.map (natCode k B)).sum : ℤ) = (polyTotal k m).eval (B : ℤ) := by
  have h₁ := map_multiset_sum (Nat.castAddMonoidHom ℤ) (m.val.map (natCode k B))
  have h₂ := map_multiset_sum (evalRingHom (B : ℤ)) (m.val.map (polyCode k))
  change _ = (evalRingHom (B : ℤ)) (m.val.map (polyCode k)).sum
  rw [h₂]
  change (Nat.castAddMonoidHom ℤ) (m.val.map (natCode k B)).sum = _
  rw [h₁, Multiset.map_map, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  exact natCode_cast k B hk hB a

lemma exists_natTotal_injective (k : ℕ) (hk : 0 < k) :
    ∃ B : ℕ, 2 ≤ B ∧ Function.Injective (fun m : Sym (Fin k ⊕ Fin (k+1)) 3 ↦
      (m.val.map (natCode k B)).sum) := by
  obtain ⟨B,hB,hi⟩ := exists_eval_total_injective k hk
  refine ⟨B,hB,?_⟩
  intro s t he
  apply hi
  have hh := congrArg (fun n : ℕ ↦ (n : ℤ)) he
  simpa only [natTotal_cast k B hk hB] using hh

lemma natCode_pair (k B : ℕ) (hk : 0 < k) (hB : 2 ≤ B) (j : Fin (k+1)) :
    natCode k B (.inl ⟨j.val % k, Nat.mod_lt _ hk⟩) + natCode k B (.inr j) =
      B^(k+1) + j.val := by
  apply Int.ofNat_inj.mp
  push_cast
  rw [natCode_cast k B hk hB, natCode_cast k B hk hB]
  simp only [polyCode, Sum.elim_inl, Sum.elim_inr, left, right,
    eval_X_pow, eval_sub, eval_add, eval_C]
  ring

end Polynomials

lemma injective_of_three_sum_injective {ι : Type*} (code : ι → ℕ)
    (hs : Function.Injective (fun m : Sym ι 3 ↦ (m.val.map code).sum)) :
    Function.Injective code := by
  intro a b he
  let s : Sym ι 3 := ⟨{a,a,a}, by simp⟩
  let t : Sym ι 3 := ⟨{b,b,b}, by simp⟩
  have hst : s = t := hs (by simp [s,t,he])
  have hm : a ∈ t.val := hst ▸ (by simp [s])
  simpa [t] using hm

lemma good_of_sym_injective {ι : Type*} [Fintype ι] [Nonempty ι]
    (code : ι → ℕ)
    (hs : Function.Injective (fun m : Sym ι 3 ↦ (m.val.map code).sum)) :
    Erdos241.B3Aux.Good (univ.image code) := by
  classical
  let decode : ℕ → ι := Function.invFun code
  have hmap (m : Multiset ℕ) (hm : ∀ x ∈ m, x ∈ univ.image code) :
      (m.map decode).map code = m := by
    rw [Multiset.map_map]
    conv_rhs => rw [← Multiset.map_id m]
    apply Multiset.map_congr rfl
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hm x hx)
    exact Function.apply_invFun_apply
  intro m₁ m₂ h₁ h₂ hm₁ hm₂ he
  let s : Sym ι 3 := ⟨m₁.map decode, by simpa using h₁⟩
  let t : Sym ι 3 := ⟨m₂.map decode, by simpa using h₂⟩
  have hst : s = t := hs (by simpa [s, t, hmap m₁ hm₁, hmap m₂ hm₂] using he)
  have hh := congrArg (fun m : Sym ι 3 ↦ m.val.map code) hst
  simpa only [s, t, hmap m₁ hm₁, hmap m₂ hm₂] using hh

open Erdos241.B3Aux

lemma family_exists (k : ℕ) (hk : 2 ≤ k) :
    ∃ A : Finset ℕ, Good A ∧ A.card = 2*k+1 ∧ (∀ a ∈ A, 0 < a) ∧
      (∀ a ∈ A, ∀ b ∈ A, a + 1 ≠ b) ∧
      (shiftReps A 1 0).card = k := by
  classical
  have hkpos : 0 < k := by omega
  obtain ⟨B,hB,hT⟩ := exists_natTotal_injective k hkpos
  let code := natCode k B
  have hi : Function.Injective code := injective_of_three_sum_injective code hT
  let A : Finset ℕ := univ.image code
  have hA : Good A := good_of_sym_injective code hT
  have hcard : A.card = 2*k+1 := by
    change (univ.image code).card = _
    rw [card_image_of_injective _ hi, card_univ, Fintype.card_sum]
    simp only [Fintype.card_fin]
    omega
  let L (j : Fin (k+1)) : ℕ := code (.inl ⟨j.val % k, Nat.mod_lt _ hkpos⟩)
  let R (j : Fin (k+1)) : ℕ := code (.inr j)
  have hL (j : Fin (k+1)) : L j ∈ A := mem_image.mpr ⟨_, mem_univ _, rfl⟩
  have hR (j : Fin (k+1)) : R j ∈ A := mem_image.mpr ⟨_, mem_univ _, rfl⟩
  have hLR (j : Fin (k+1)) : L j ≠ R j := by
    intro h
    cases hi h
  have hp (j : Fin (k+1)) : L j + R j = B^(k+1) + j.val :=
    natCode_pair k B hkpos hB j
  have hmem (j : Fin (k+1)) : B^(k+1) + j.val ∈ pairSums A := by
    exact mem_pairSums_iff.mpr ⟨L j,hL j,R j,hR j,hLR j,(hp j).symm⟩
  have hlower : k ≤ (shiftReps A 1 0).card := by
    have hh := card_le_card_of_injOn (s := range k) (t := shiftReps A 1 0)
      (fun i : ℕ ↦ (B^(k+1)+i, B^(k+1)+(i+1))) ?_ ?_
    · simpa only [card_range] using hh
    · intro i hi
      have hik : i < k := mem_range.mp hi
      apply shiftReps_mem.mpr
      exact ⟨hmem ⟨i,by omega⟩,hmem ⟨i+1,by omega⟩,by dsimp only; omega⟩
    · intro i hi j hj he
      have hh := congrArg Prod.fst he
      dsimp only at hh
      omega
  let j0 : Fin (k+1) := ⟨0,by omega⟩
  let j1 : Fin (k+1) := ⟨1,by omega⟩
  let j2 : Fin (k+1) := ⟨2,by omega⟩
  have hdis : ∀ x, (x = L j0 ∨ x = R j0) → (x = L j1 ∨ x = R j1) → False := by
    intro x hx hy
    have hmod : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
    rcases hx with h | h <;> rcases hy with h' | h'
    · have hh := hi (h.symm.trans h')
      have he := congrArg (Sum.elim Fin.val Fin.val) hh
      simp [j0, j1, hmod] at he
    · cases hi (h.symm.trans h')
    · cases hi (h.symm.trans h')
    · have hh := hi (h.symm.trans h')
      have he := congrArg (Sum.elim Fin.val Fin.val) hh
      simp [j0, j1] at he
  have hno : ∀ a ∈ A, ∀ b ∈ A, a + 1 ≠ b := by
    intro a ha b hb he
    have h0 := hp j0
    have h1 := hp j1
    have h2 := hp j2
    change L j0 + R j0 = B^(k+1)+0 at h0
    change L j1 + R j1 = B^(k+1)+1 at h1
    change L j2 + R j2 = B^(k+1)+2 at h2
    have hh0 := three_sum_mem hA ha (hL j1) (hR j1) hb (hL j0) (hR j0)
      (by omega : a + L j1 + R j1 = b + L j0 + R j0)
    have hh1 := three_sum_mem hA ha (hL j2) (hR j2) hb (hL j1) (hR j1)
      (by omega : a + L j2 + R j2 = b + L j1 + R j1)
    have hab : a ≠ b := by omega
    exact hdis a (hh0.resolve_left hab) (hh1.resolve_left hab)
  have hu := shiftReps_bound_good hA 1 0 (by simpa only [add_zero] using hno)
  rw [hcard] at hu
  have hpos : ∀ a ∈ A, 0 < a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := mem_image.mp ha
    have hp := polyCode_eval_pos k B hkpos hB i
    rw [← natCode_cast k B hkpos hB] at hp
    exact_mod_cast hp
  refine ⟨A,hA,hcard,hpos,hno,?_⟩
  omega

lemma pointwise_asymptotically_sharp (c : ℝ) (hc : 2 < c) (K : ℕ) :
    ∃ A : Finset ℕ, Good A ∧ K ≤ A.card ∧ (∀ a ∈ A, 0 < a) ∧
      (∀ a ∈ A, ∀ b ∈ A, a + 1 ≠ b) ∧
      (A.card : ℝ) < c * (shiftReps A 1 0).card := by
  obtain ⟨k,hk⟩ := exists_nat_gt (max (1 / (c-2)) (K+2 : ℝ))
  have hkK : (K+2 : ℝ) < k := (le_max_right _ _).trans_lt hk
  have hk' : K+2 < k := by exact_mod_cast hkK
  obtain ⟨A,hA,hcard,hpos,hno,hR⟩ := family_exists k (by omega)
  refine ⟨A,hA,by omega,hpos,hno,?_⟩
  rw [hcard,hR]
  have hh := (div_lt_iff₀ (sub_pos.mpr hc)).mp ((le_max_left _ _).trans_lt hk)
  push_cast
  nlinarith


end SharpFamily


lemma f_reverse_cube_bound_strong (N : ℕ) : N < 8 * (f N 3 + 1)^3 := by
  let n := Nat.nthRoot 3 (N / 8)
  have hs : n^3 ≤ N / 8 := Nat.pow_nthRoot_le (Or.inl (by decide))
  have hsmall : 8 * n^3 ≤ N := by omega
  have hf : n ≤ f N 3 := (f_bose_lower_bound n).trans (f_monotone 3 hsmall)
  have hl : N / 8 < (n+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) _
  have hlarge : N < 8 * (n+1)^3 := by omega
  have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right hf 1) 3
  exact hlarge.trans_le (Nat.mul_le_mul_left 8 hpow)

lemma f_cuberoot_lower_pointwise (N : ℕ) :
    (N : ℝ)^((1 : ℝ)/3) < 2 * ((f N 3 : ℝ) + 1) := by
  have hb : (N : ℝ) < 8 * ((f N 3 : ℝ) + 1)^3 := by
    exact_mod_cast f_reverse_cube_bound_strong N
  have hr : ((N : ℝ)^((1 : ℝ)/3))^3 = N := by
    simpa [one_div] using Real.rpow_inv_natCast_pow (x := (N : ℝ)) (n := 3)
      (by positivity) (by decide)
  apply (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by decide : 3 ≠ 0)).mp
  rw [mul_pow, hr]
  norm_num
  exact hb

lemma f_ratio_eventually_gt_half (c : ℝ) (hc : c < 1/2) :
    ∀ᶠ N : ℕ in atTop, c < (f N 3 : ℝ) / (N : ℝ)^((1 : ℝ)/3) := by
  let R : ℕ → ℝ := fun N ↦ (N : ℝ)^((1 : ℝ)/3)
  have hRt : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N ↦ (1 : ℝ)/2 - 1 / R N) atTop (nhds (1/2)) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)/2)).sub (hRt.const_div_atTop 1)
  filter_upwards [eventually_ge_atTop 1, ht.eventually_const_lt hc] with N hN hh
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R N := Real.rpow_pos_of_pos hNp _
  have hb := f_cuberoot_lower_pointwise N
  change R N < 2 * ((f N 3 : ℝ)+1) at hb
  apply hh.trans
  apply (lt_div_iff₀ hRp).mpr
  have he : ((1 : ℝ)/2 - 1 / R N) * R N = R N / 2 - 1 := by
    field_simp
  rw [he]
  linarith

/-- A short-prime-interval estimate suffices for the sharp asymptotic lower bound.
The prime-interval hypothesis is explicit and is not assumed elsewhere. -/
lemma f_ratio_lower_of_short_prime_intervals
    (hprime : ∀ c : ℝ, c < 1 → ∀ᶠ x : ℝ in atTop,
      ∃ p : ℕ, p.Prime ∧ c*x < p ∧ (p : ℝ) ≤ x)
    (c : ℝ) (hc : c < 1) :
    ∀ᶠ N : ℕ in atTop, c < (f N 3 : ℝ) / (N : ℝ)^((1 : ℝ)/3) := by
  let R : ℕ → ℝ := fun N ↦ (N : ℝ)^((1 : ℝ)/3)
  have hRt : Tendsto R atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/3)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hRt.eventually (hprime c hc)] with N hN hp
  obtain ⟨p,hp,hcp,hpR⟩ := hp
  haveI : Fact p.Prime := ⟨hp⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : 0 < R N := Real.rpow_pos_of_pos hNp _
  have hr : (R N)^3 = N := by
    simpa [R,one_div] using Real.rpow_inv_natCast_pow (x := (N : ℝ)) (n := 3)
      hNp.le (by decide)
  have hpower : p^3 ≤ N := by
    have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p) hpR 3
    rw [hr] at hh
    exact_mod_cast hh
  have hf : p ≤ f N 3 := (f_bose_chowla p).trans
    (f_monotone 3 ((Nat.sub_le (p^3) 1).trans hpower))
  apply (lt_div_iff₀ hRp).mpr
  exact hcp.trans_le (by exact_mod_cast hf)




/- A Fourier smoothing lemma for a Tauberian approach to short prime intervals. -/

open MeasureTheory Filter
open scoped FourierTransform RealInnerProductSpace

namespace TaubCore

lemma fourier_swap {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) :
    (∫ x : ℝ, (𝓕 f x) * g x) = ∫ x : ℝ, f x * (𝓕 g x) := by
  have hh := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner hf hg
  have hflip : (innerₗ ℝ).flip = innerₗ ℝ := by ext; rfl
  simpa only [hflip, smul_eq_mul] using hh

noncomputable def phase (t x : ℝ) : ℂ := Real.fourierChar (t*x)

lemma phase_continuous (t : ℝ) : Continuous (phase t) := by
  exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
    (continuous_const.mul continuous_id)

@[simp] lemma phase_norm (t x : ℝ) : ‖phase t x‖ = 1 := by simp [phase]

lemma fourier_translate (f : ℝ → ℂ) (t x : ℝ) :
    𝓕 (fun u ↦ f (u+t)) x = phase t x * 𝓕 f x := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ ℝ) f t) x
  change 𝓕 (fun u ↦ f (u+t)) x =
    (Real.fourierChar (x*t) : ℂ) * 𝓕 f x at hh
  simpa only [phase, mul_comm x t] using hh

lemma fourier_continuous {f : ℝ → ℂ} (hf : Integrable f) : Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hf

lemma translated_pairing {f ψ : ℝ → ℂ} (hf : Integrable f) (hψ : Integrable ψ) (t : ℝ) :
    (∫ x : ℝ, f (x+t) * (𝓕 ψ x)) =
      ∫ x : ℝ, phase t x * ((𝓕 f x) * ψ x) := by
  rw [← fourier_swap (hf.comp_add_right t) hψ]
  simp only [fourier_translate, mul_assoc]

/-- Bounded pointwise approximants with controlled Fourier limits admit a limiting
Fourier pairing. Compact Fourier support will supply the frequency-side bound in
applications; it is not needed explicitly in this general lemma. -/
lemma limit_pairing
    (F : ℕ → ℝ → ℂ) (f g ψ : ℝ → ℂ) (M C : ℝ)
    (hF : ∀ n, Integrable (F n))
    (hFb : ∀ n x, ‖F n x‖ ≤ M)
    (hFlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    (hgb : ∀ n x, ψ x ≠ 0 → ‖𝓕 (F n) x‖ ≤ C)
    (hglim : ∀ x, ψ x ≠ 0 → Tendsto (fun n ↦ 𝓕 (F n) x) atTop (nhds (g x)))
    (hψ : Integrable ψ) (hψF : Integrable (𝓕 ψ)) (t : ℝ) :
    (∫ x : ℝ, f (x+t) * 𝓕 ψ x) = ∫ x : ℝ, phase t x * (g x * ψ x) := by
  have hleft : Tendsto (fun n ↦ ∫ x : ℝ, F n (x+t) * 𝓕 ψ x)
      atTop (nhds (∫ x : ℝ, f (x+t) * 𝓕 ψ x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ M * ‖𝓕 ψ x‖)
    · intro n
      exact ((hF n).comp_add_right t).aestronglyMeasurable.mul hψF.aestronglyMeasurable
    · exact hψF.norm.const_mul M
    · intro n
      filter_upwards with x
      simpa only [norm_mul] using mul_le_mul_of_nonneg_right (hFb n (x+t)) (norm_nonneg _)
    · filter_upwards with x
      exact (hFlim (x+t)).mul_const _
  have hright : Tendsto (fun n ↦ ∫ x : ℝ, phase t x * ((𝓕 (F n) x) * ψ x))
      atTop (nhds (∫ x : ℝ, phase t x * (g x * ψ x))) := by
    apply tendsto_integral_of_dominated_convergence (fun x ↦ C * ‖ψ x‖)
    · intro n
      exact (phase_continuous t).aestronglyMeasurable.mul
        ((fourier_continuous (hF n)).aestronglyMeasurable.mul hψ.aestronglyMeasurable)
    · exact hψ.norm.const_mul C
    · intro n
      filter_upwards with x
      simp only [norm_mul, phase_norm, one_mul]
      by_cases hx : ψ x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right (hgb n x hx) (norm_nonneg _)
    · filter_upwards with x
      by_cases hx : ψ x = 0
      · simp only [hx, mul_zero]
        exact tendsto_const_nhds
      · exact ((hglim x hx).mul_const _).const_mul _
  have heq : (fun n ↦ ∫ x : ℝ, F n (x+t) * 𝓕 ψ x) =
      (fun n ↦ ∫ x : ℝ, phase t x * ((𝓕 (F n) x) * ψ x)) := by
    funext n
    exact translated_pairing (hF n) hψ t
  exact tendsto_nhds_unique (heq ▸ hleft) hright


lemma phase_pairing_eq_fourier (h : ℝ → ℂ) (t : ℝ) :
    (∫ x : ℝ, phase t x * h x) = 𝓕 h (-t) := by
  rw [Real.fourier_real_eq]
  apply integral_congr_ae
  filter_upwards with x
  simp [phase, Circle.smul_def, smul_eq_mul, mul_comm]

lemma smoothed_tendsto_zero
    (F : ℕ → ℝ → ℂ) (f g ψ : ℝ → ℂ) (M C : ℝ)
    (hF : ∀ n, Integrable (F n))
    (hFb : ∀ n x, ‖F n x‖ ≤ M)
    (hFlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    (hgb : ∀ n x, ψ x ≠ 0 → ‖𝓕 (F n) x‖ ≤ C)
    (hglim : ∀ x, ψ x ≠ 0 → Tendsto (fun n ↦ 𝓕 (F n) x) atTop (nhds (g x)))
    (hψ : Integrable ψ) (hψF : Integrable (𝓕 ψ)) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, f (x+t) * 𝓕 ψ x) atTop (nhds 0) := by
  have heq : (fun t : ℝ ↦ ∫ x : ℝ, f (x+t) * 𝓕 ψ x) =
      (fun t : ℝ ↦ 𝓕 (fun x ↦ g x * ψ x) (-t)) := by
    funext t
    rw [limit_pairing F f g ψ M C hF hFb hFlim hgb hglim hψ hψF t,
      phase_pairing_eq_fourier]
  rw [heq]
  exact (Real.zero_at_infty_fourier (fun x ↦ g x * ψ x)).comp
    (tendsto_neg_atTop_atBot.mono_right atBot_le_cocompact)


lemma continuous_boundary_smoothing
    (F : ℕ → ℝ → ℂ) (f ψ : ℝ → ℂ) (G : ℝ × ℝ → ℂ) (σ : ℕ → ℝ) (M : ℝ)
    (hF : ∀ n, Integrable (F n))
    (hFb : ∀ n x, ‖F n x‖ ≤ M)
    (hFlim : ∀ x, Tendsto (fun n ↦ F n x) atTop (nhds (f x)))
    (hG : Continuous G) (hσ : ∀ n, σ n ∈ Set.Icc (0 : ℝ) 1)
    (hσlim : Tendsto σ atTop (nhds 0))
    (hhat : ∀ n x, 𝓕 (F n) x = G (σ n,x))
    (hψ : Integrable ψ) (hψF : Integrable (𝓕 ψ)) (hψc : HasCompactSupport ψ) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, f (x+t) * 𝓕 ψ x) atTop (nhds 0) := by
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ tsupport ψ) := isCompact_Icc.prod hψc
  obtain ⟨C,hC⟩ := (hK.image hG.norm).bddAbove
  apply smoothed_tendsto_zero F f (fun x ↦ G (0,x)) ψ M C hF hFb hFlim _ _ hψ hψF
  · intro n x hx
    rw [hhat]
    apply hC
    apply Set.mem_image_of_mem
    exact ⟨hσ n, subset_tsupport ψ hx⟩
  · intro x hx
    simp only [hhat]
    exact hG.continuousAt.tendsto.comp (hσlim.prodMk_nhds tendsto_const_nhds)


noncomputable def damp (σ : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Set.Ici 0).indicator (fun x ↦ (Real.exp (-σ*x) : ℂ) * f x)

lemma damp_integrable (σ : ℝ) (hσ : 0 < σ) (f : ℝ → ℂ) (M : ℝ)
    (hf : AEStronglyMeasurable f volume) (hM : ∀ x, ‖f x‖ ≤ M) : Integrable (damp σ f) := by
  have he : IntegrableOn (fun x : ℝ ↦ (Real.exp (-σ*x) : ℂ)) (Set.Ici 0) := by
    apply (integrableOn_Ici_iff_integrableOn_Ioi).mpr
    exact (integrableOn_exp_mul_Ioi (neg_neg_of_pos hσ) 0).ofReal
  have hei : Integrable ((Set.Ici 0).indicator (fun x : ℝ ↦ (Real.exp (-σ*x) : ℂ))) :=
    (integrable_indicator_iff measurableSet_Ici).mpr he
  have heq : damp σ f = fun x ↦
      (Set.Ici 0).indicator (fun y : ℝ ↦ (Real.exp (-σ*y) : ℂ)) x * f x := by
    funext x
    exact Set.indicator_mul_left _ _ _
  rw [heq]
  exact hei.mul_bdd hf (Eventually.of_forall hM)

lemma damp_bound (σ : ℝ) (hσ : 0 ≤ σ) (f : ℝ → ℂ) (M : ℝ)
    (hM : ∀ x, ‖f x‖ ≤ M) (x : ℝ) : ‖damp σ f x‖ ≤ M := by
  have hM0 : 0 ≤ M := (norm_nonneg (f 0)).trans (hM 0)
  by_cases hx : 0 ≤ x
  · have he : Real.exp (-σ*x) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    calc
      _ = Real.exp (-σ*x) * ‖f x‖ := by
        simp only [damp, Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx), norm_mul, Complex.norm_real,
          Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * ‖f x‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ ≤ M := by simpa using hM x
  · simpa [damp,hx] using hM0

lemma damp_tendsto (σ : ℕ → ℝ) (hσ : Tendsto σ atTop (nhds 0)) (f : ℝ → ℂ)
    (hf : ∀ x, x < 0 → f x = 0) (x : ℝ) :
    Tendsto (fun n ↦ damp (σ n) f x) atTop (nhds (f x)) := by
  by_cases hx : 0 ≤ x
  · have he : Tendsto (fun n ↦ Real.exp (-σ n*x)) atTop (nhds 1) := by
      simpa only [neg_zero,zero_mul,Real.exp_zero,Function.comp_def] using
        Real.continuous_exp.continuousAt.tendsto.comp (hσ.neg.mul_const x)
    have he' : Tendsto (fun n ↦ (Real.exp (-σ n*x) : ℂ)) atTop (nhds 1) := by
      simpa only [Function.comp_def,Complex.ofReal_one] using
        Complex.continuous_ofReal.continuousAt.tendsto.comp he
    simpa [damp,hx] using he'.mul_const (f x)
  · simp only [damp, Set.indicator_of_notMem (show x ∉ Set.Ici 0 from hx), hf x (by linarith)]
    exact tendsto_const_nhds

noncomputable def laplace (f : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ x : ℝ in Set.Ici 0, Complex.exp (-s*x) * f x

lemma fourier_damp (f : ℝ → ℂ) (σ ξ : ℝ) :
    𝓕 (damp σ f) ξ = laplace f (σ + (2*Real.pi*ξ : ℝ)*Complex.I) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [damp, smul_eq_mul]
  simp_rw [← Set.indicator_mul_right (Set.Ici (0 : ℝ))
    (fun v : ℝ ↦ Complex.exp (↑(-2*Real.pi*v*ξ)*Complex.I))
    (fun x : ℝ ↦ (Real.exp (-σ*x) : ℂ) * f x)]
  rw [integral_indicator measurableSet_Ici]
  apply setIntegral_congr_fun measurableSet_Ici
  intro x hx
  dsimp only
  rw [← mul_assoc, Complex.ofReal_exp, ← Complex.exp_add]
  congr 2
  push_cast
  ring


/-- Continuous boundary values of a Laplace transform force band-limited smoothings
to vanish at infinity. This is the analytic smoothing step, not the full Tauberian theorem. -/
lemma laplace_boundary_smoothing
    (f ψ : ℝ → ℂ) (G : ℝ × ℝ → ℂ) (M : ℝ)
    (hf : AEStronglyMeasurable f volume) (hM : ∀ x, ‖f x‖ ≤ M)
    (hfzero : ∀ x, x < 0 → f x = 0)
    (hG : Continuous G)
    (hLap : ∀ σ : ℝ, 0 < σ → ∀ ξ : ℝ,
      laplace f (σ + (2*Real.pi*ξ : ℝ)*Complex.I) = G (σ,ξ))
    (hψ : Integrable ψ) (hψF : Integrable (𝓕 ψ)) (hψc : HasCompactSupport ψ) :
    Tendsto (fun t : ℝ ↦ ∫ x : ℝ, f (x+t) * 𝓕 ψ x) atTop (nhds 0) := by
  let σ : ℕ → ℝ := fun n ↦ 1 / (n+1 : ℝ)
  have hσpos (n : ℕ) : 0 < σ n := by dsimp [σ]; positivity
  have hσlim : Tendsto σ atTop (nhds 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hσ (n : ℕ) : σ n ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨(hσpos n).le,?_⟩
    dsimp [σ]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n+1)).mpr
    norm_num
  apply continuous_boundary_smoothing (fun n ↦ damp (σ n) f) f ψ G σ M
    (fun n ↦ damp_integrable (σ n) (hσpos n) f M hf hM)
    (fun n x ↦ damp_bound (σ n) (hσpos n).le f M hM x)
    (damp_tendsto σ hσlim f hfzero) hG hσ hσlim _ hψ hψF hψc
  intro n x
  rw [fourier_damp, hLap _ (hσpos n)]


end TaubCore


/- Positive band-limited smoothing kernels for the Tauberian argument. -/

open MeasureTheory Filter
open scoped FourierTransform Convolution

namespace TaubCore

set_option maxHeartbeats 1000000

lemma fourier_conj_reflect (f : ℝ → ℂ) (ξ : ℝ) :
    𝓕 (fun x ↦ starRingEnd ℂ (f (-x))) ξ = starRingEnd ℂ (𝓕 f ξ) := by
  simp only [Real.fourier_real_eq_integral_exp_smul, smul_eq_mul]
  rw [← integral_conj]
  rw [← integral_neg_eq_self (fun x : ℝ ↦
    Complex.exp (↑(-2*Real.pi*x*ξ)*Complex.I) * starRingEnd ℂ (f (-x))) volume]
  apply integral_congr_ae
  filter_upwards with x
  simp only [neg_neg, map_mul, ← Complex.exp_conj, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring_nf

noncomputable def kernelBump : ContDiffBump (0 : ℝ) := ⟨1,2,by norm_num,by norm_num⟩

noncomputable def kernelBase : SchwartzMap ℝ ℂ :=
  (kernelBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by rfl)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp kernelBump.contDiff)

@[simp] lemma kernelBase_apply (x : ℝ) : kernelBase x = (kernelBump x : ℂ) := rfl

lemma kernelBase_compact : HasCompactSupport (kernelBase : ℝ → ℂ) :=
  kernelBump.hasCompactSupport.comp_left (show Complex.ofReal 0 = 0 by rfl)

lemma kernelBase_zero : kernelBase 0 = 1 := by
  rw [kernelBase_apply, kernelBump.one_of_mem_closedBall (by simp [kernelBump])]
  rfl

lemma kernelBase_reflect (x : ℝ) : starRingEnd ℂ (kernelBase (-x)) = kernelBase x := by
  simp [kernelBump.neg]

lemma kernelBase_fourier_real (x : ℝ) :
    starRingEnd ℂ (𝓕 (kernelBase : ℝ → ℂ) x) = 𝓕 (kernelBase : ℝ → ℂ) x := by
  have hh := fourier_conj_reflect (kernelBase : ℝ → ℂ) x
  simpa only [kernelBase_reflect] using hh.symm

noncomputable def rawKernel : SchwartzMap ℝ ℂ :=
  SchwartzMap.convolution (ContinuousLinearMap.mul ℂ ℂ) kernelBase kernelBase

lemma rawKernel_compact : HasCompactSupport (rawKernel : ℝ → ℂ) := by
  have heq : (rawKernel : ℝ → ℂ) =
      (kernelBase : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℂ ℂ] (kernelBase : ℝ → ℂ) := by
    funext x
    exact SchwartzMap.convolution_apply _ _ _ x
  rw [heq]
  exact kernelBase_compact.convolution _ kernelBase_compact

lemma rawKernel_fourier (x : ℝ) :
    𝓕 (rawKernel : ℝ → ℂ) x = (‖𝓕 (kernelBase : ℝ → ℂ) x‖^2 : ℝ) := by
  rw [← SchwartzMap.fourier_coe]
  simp only [rawKernel, SchwartzMap.fourier_convolution, SchwartzMap.pairing_apply_apply,
    ContinuousLinearMap.mul_apply', SchwartzMap.fourier_coe]
  conv_lhs => rhs; rw [← kernelBase_fourier_real x]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

lemma rawKernel_mass_pos : 0 < ∫ x : ℝ, ‖𝓕 (kernelBase : ℝ → ℂ) x‖^2 := by
  rw [← SchwartzMap.fourier_coe, SchwartzMap.integral_norm_sq_fourier]
  apply (kernelBase.continuous.norm.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := 0)
  · exact kernelBase_compact.norm.comp_left (g := fun x : ℝ ↦ x^2) (by norm_num)
  · exact fun x ↦ sq_nonneg _
  · rw [kernelBase_zero]
    norm_num

lemma exists_positive_kernel :
    ∃ ψ : ℝ → ℂ, ∃ κ : ℝ → ℝ,
      Integrable ψ ∧ Integrable (𝓕 ψ) ∧ HasCompactSupport ψ ∧
      Continuous κ ∧ Integrable κ ∧ (∀ x, 0 ≤ κ x) ∧
      (∀ x, 𝓕 ψ x = (κ x : ℂ)) ∧ (∫ x : ℝ, κ x) = 1 := by
  let d : ℝ := ∫ x : ℝ, ‖𝓕 (kernelBase : ℝ → ℂ) x‖^2
  have hd : 0 < d := rawKernel_mass_pos
  let Ψ : SchwartzMap ℝ ℂ := (d⁻¹ : ℝ) • rawKernel
  let κ : ℝ → ℝ := fun x ↦ (𝓕 (Ψ : ℝ → ℂ) x).re
  have hval (x : ℝ) : 𝓕 (Ψ : ℝ → ℂ) x =
      (d⁻¹ * ‖𝓕 (kernelBase : ℝ → ℂ) x‖^2 : ℝ) := by
    rw [← SchwartzMap.fourier_coe]
    simp only [Ψ, FourierTransform.fourier_smul, SchwartzMap.smul_apply]
    rw [SchwartzMap.fourier_coe, rawKernel_fourier]
    simp only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv]
  have hκ (x : ℝ) : κ x = d⁻¹ * ‖𝓕 (kernelBase : ℝ → ℂ) x‖^2 := by
    simp only [κ, hval, Complex.ofReal_re]
  have hψc : HasCompactSupport (Ψ : ℝ → ℂ) := by
    exact rawKernel_compact.smul_left
  have hψFi : Integrable (𝓕 (Ψ : ℝ → ℂ)) := by
    rw [← SchwartzMap.fourier_coe]
    exact (𝓕 Ψ).integrable
  refine ⟨Ψ,κ,Ψ.integrable,hψFi,hψc,?_,hψFi.re,?_,?_,?_⟩
  · exact Complex.continuous_re.comp (fourier_continuous Ψ.integrable)
  · intro x
    rw [hκ]
    positivity
  · intro x
    rw [hval, hκ]
  · simp_rw [hκ]
    rw [integral_const_mul]
    change d⁻¹*d = 1
    exact inv_mul_cancel₀ hd.ne'


lemma fourier_modulate (ψ : ℝ → ℂ) (u x : ℝ) :
    𝓕 (fun ξ ↦ phase u ξ * ψ ξ) x = 𝓕 ψ (x-u) := by
  simp only [Real.fourier_real_eq, phase, Circle.smul_def, smul_eq_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
  congr 2
  ring_nf

lemma fourier_dilate (ψ : ℝ → ℂ) (a : ℝ) (ha : 0 < a) (x : ℝ) :
    𝓕 (fun ξ ↦ ψ (ξ/a)) x = (a : ℂ) * 𝓕 ψ (a*x) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  have he (ξ : ℝ) : -(ξ*x) = -((ξ/a)*(a*x)) := by field_simp
  simp_rw [he]
  rw [Measure.integral_comp_div (fun v : ℝ ↦ Real.fourierChar (-(v*(a*x))) • ψ v) a]
  simp only [abs_of_pos ha, Complex.real_smul]

lemma scaled_pairing (κ h : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (u : ℝ) :
    (∫ x : ℝ, a * κ (a*(x-u)) * h x) = ∫ y : ℝ, κ y * h (y/a+u) := by
  let F : ℝ → ℝ := fun y ↦ κ y * h (y/a+u)
  have he (x : ℝ) : a * κ (a*(x-u)) * h x = a * F (a*(x-u)) := by
    dsimp [F]
    rw [mul_div_cancel_left₀ (x-u) ha.ne']
    simp [mul_assoc]
  simp_rw [he]
  rw [integral_const_mul]
  have ht : (∫ x : ℝ, F (a*(x-u))) = ∫ x : ℝ, F (a*x) := by
    simpa only [sub_eq_add_neg] using integral_add_right_eq_self (fun x ↦ F (a*x)) (-u)
  rw [ht, Measure.integral_comp_mul_left, abs_of_pos (inv_pos.mpr ha)]
  change a * (a⁻¹ * ∫ y, F y) = _
  rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]

lemma scaled_mass (κ : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (u : ℝ) :
    (∫ x : ℝ, a * κ (a*(x-u))) = ∫ y : ℝ, κ y := by
  simpa only [mul_one] using scaled_pairing κ (fun _ ↦ 1) a ha u

lemma scaled_interval_mass (κ : ℝ → ℝ) (a : ℝ) (ha : 0 < a) (u l r : ℝ) :
    (∫ x : ℝ in Set.Ioo l r, a * κ (a*(x-u))) =
      ∫ y : ℝ, κ y * (Set.Ioo l r).indicator (fun _ ↦ (1 : ℝ)) (y/a+u) := by
  rw [← scaled_pairing κ ((Set.Ioo l r).indicator (fun _ ↦ (1 : ℝ))) a ha u]
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Set.Ioo l r <;> simp [hx]

lemma dilate_kernel (ψ : ℝ → ℂ) (κ : ℝ → ℝ)
    (hψ : Integrable ψ) (hψc : HasCompactSupport ψ)
    (hκc : Continuous κ) (hκi : Integrable κ) (hκpos : ∀ x, 0 ≤ κ x)
    (hFT : ∀ x, 𝓕 ψ x = (κ x : ℂ)) (hmass : (∫ x : ℝ, κ x) = 1)
    (a : ℝ) (ha : 0 < a) (u : ℝ) :
    let Ψ : ℝ → ℂ := fun ξ ↦ phase u ξ * ψ (ξ/a)
    let K : ℝ → ℝ := fun x ↦ a * κ (a*(x-u))
    Integrable Ψ ∧ Integrable (𝓕 Ψ) ∧ HasCompactSupport Ψ ∧
      Continuous K ∧ Integrable K ∧ (∀ x, 0 ≤ K x) ∧
      (∀ x, 𝓕 Ψ x = (K x : ℂ)) ∧ (∫ x : ℝ, K x) = 1 := by
  dsimp only
  have hki : Integrable (fun x : ℝ ↦ a * κ (a*(x-u))) := by
    simpa only [sub_eq_add_neg] using
      ((hκi.comp_mul_left' ha.ne').comp_add_right (-u)).const_mul a
  have hft (x : ℝ) : 𝓕 (fun ξ ↦ phase u ξ * ψ (ξ/a)) x =
      (a * κ (a*(x-u)) : ℝ) := by
    rw [fourier_modulate, fourier_dilate ψ a ha, hFT]
    simp only [Complex.ofReal_mul]
  refine ⟨?_,?_,?_,?_,hki,?_,hft,?_⟩
  · exact (hψ.comp_div ha.ne').bdd_mul (phase_continuous u).aestronglyMeasurable
      (Eventually.of_forall (fun x ↦ (phase_norm u x).le))
  · have heq := funext hft
    rw [heq]
    exact hki.ofReal
  · have hh : HasCompactSupport (fun ξ : ℝ ↦ ψ (ξ/a)) := by
      have hh := hψc.comp_homeomorph (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne'))
      change HasCompactSupport (fun ξ : ℝ ↦ ψ (ξ*a⁻¹)) at hh
      simpa only [div_eq_mul_inv] using hh
    exact hh.mul_left
  · fun_prop
  · intro x
    exact mul_nonneg ha.le (hκpos _)
  · rw [scaled_mass κ a ha,hmass]

/-- Dilations of a probability kernel concentrate in any interval containing their center. -/
lemma scaled_interval_mass_tendsto (κ : ℝ → ℝ)
    (hκc : Continuous κ) (hκi : Integrable κ) (hκpos : ∀ x, 0 ≤ κ x)
    (hmass : (∫ x : ℝ, κ x) = 1) (u l r : ℝ) (hlu : l < u) (hur : u < r) :
    Tendsto (fun n : ℕ ↦ ∫ x : ℝ in Set.Ioo l r,
      ((n : ℝ)+1) * κ (((n : ℝ)+1)*(x-u))) atTop (nhds 1) := by
  have heq (n : ℕ) := scaled_interval_mass κ ((n : ℝ)+1) (by positivity) u l r
  simp_rw [heq]
  conv_rhs => rw [← hmass]
  apply tendsto_integral_of_dominated_convergence κ
  · intro n
    apply (hκc.measurable.mul _).aestronglyMeasurable
    exact (measurable_const.indicator measurableSet_Ioo).comp (by fun_prop)
  · exact hκi
  · intro n
    filter_upwards with x
    by_cases hx : x / ((n : ℝ)+1) + u ∈ Set.Ioo l r
    · simp only [Set.indicator_of_mem hx, mul_one, Real.norm_eq_abs, abs_of_nonneg (hκpos x)]
      exact le_rfl
    · simp only [Set.indicator_of_notMem hx, mul_zero, norm_zero]
      exact hκpos x
  · filter_upwards with x
    have ht : Tendsto (fun n : ℕ ↦ x / ((n : ℝ)+1) + u) atTop (nhds u) := by
      have hh := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul x
      simpa only [mul_one_div, mul_zero, zero_add] using hh.add_const u
    have he := ht.eventually (isOpen_Ioo.mem_nhds (show u ∈ Set.Ioo l r from ⟨hlu,hur⟩))
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [Set.indicator_of_mem (show x / ((n : ℝ)+1) + u ∈ Set.Ioo l r from hn), mul_one]

/-- A nonnegative band-limited probability kernel can put arbitrarily much mass
inside any prescribed nonempty open interval. -/
lemma exists_concentrated_kernel (l r ε : ℝ) (hlr : l < r) (hε : 0 < ε) :
    ∃ ψ : ℝ → ℂ, ∃ κ : ℝ → ℝ,
      Integrable ψ ∧ Integrable (𝓕 ψ) ∧ HasCompactSupport ψ ∧
      Continuous κ ∧ Integrable κ ∧ (∀ x, 0 ≤ κ x) ∧
      (∀ x, 𝓕 ψ x = (κ x : ℂ)) ∧ (∫ x : ℝ, κ x) = 1 ∧
      1-ε < ∫ x : ℝ in Set.Ioo l r, κ x := by
  obtain ⟨ψ,κ,hψ,hψF,hψc,hκc,hκi,hκpos,hFT,hmass⟩ := exists_positive_kernel
  have ht := scaled_interval_mass_tendsto κ hκc hκi hκpos hmass ((l+r)/2) l r
    (by linarith) (by linarith)
  obtain ⟨n,hn⟩ := (ht.eventually (eventually_gt_nhds (show 1-ε < 1 by linarith))).exists
  have hd := dilate_kernel ψ κ hψ hψc hκc hκi hκpos hFT hmass
    ((n : ℝ)+1) (by positivity) ((l+r)/2)
  exact ⟨_,_,hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2.1,
    hd.2.2.2.2.2.1,hd.2.2.2.2.2.2.1,hd.2.2.2.2.2.2.2,hn⟩


end TaubCore


/- A monotonicity-based Tauberian passage from positive smoothings to pointwise limits. -/
open MeasureTheory Filter
open scoped FourierTransform
namespace TaubCore

lemma weighted_integrable (S κ : ℝ → ℝ) (M : ℝ)
    (hS : Measurable S) (hSb : ∀ x, ‖S x‖ ≤ M) (hκ : Integrable κ) (t : ℝ) :
    Integrable (fun x ↦ S (x+t) * κ x) := by
  exact hκ.bdd_mul (hS.comp (by fun_prop)).aestronglyMeasurable
    (Eventually.of_forall (fun x ↦ hSb (x+t)))

lemma weighted_local_lower (S κ : ℝ → ℝ) (s : Set ℝ) (c : ℝ)
    (hs : MeasurableSet s) (hSi : Integrable (fun x ↦ S x * κ x))
    (hκi : Integrable κ) (hκpos : ∀ x, 0 ≤ κ x) (hSpos : ∀ x, 0 ≤ S x)
    (hloc : ∀ x ∈ s, c ≤ S x) :
    c * (∫ x in s, κ x) ≤ ∫ x, S x * κ x := by
  rw [← integral_const_mul, ← integral_indicator hs]
  apply integral_mono_ae ((hκi.const_mul c).indicator hs) hSi
  filter_upwards with x
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx]
    exact mul_le_mul_of_nonneg_right (hloc x hx) (hκpos x)
  · rw [Set.indicator_of_notMem hx]
    exact mul_nonneg (hSpos x) (hκpos x)

lemma weighted_local_upper (S κ : ℝ → ℝ) (s : Set ℝ) (c M : ℝ)
    (hs : MeasurableSet s) (hSi : Integrable (fun x ↦ S x * κ x))
    (hκi : Integrable κ) (hκpos : ∀ x, 0 ≤ κ x) (hc : 0 ≤ c)
    (hSb : ∀ x, S x ≤ M) (hloc : ∀ x ∈ s, S x ≤ c)
    (hmass : (∫ x, κ x) = 1) :
    (∫ x, S x * κ x) ≤ c + M*(1-∫ x in s, κ x) := by
  have hb : (∫ x, S x * κ x) ≤
      ∫ x, c*κ x + M * sᶜ.indicator κ x := by
    apply integral_mono_ae hSi ((hκi.const_mul c).add ((hκi.indicator hs.compl).const_mul M))
    filter_upwards with x
    dsimp only [Pi.add_apply]
    by_cases hx : x ∈ s
    · simp only [Set.indicator_of_notMem (show x ∉ sᶜ from not_not_intro hx), mul_zero, add_zero]
      exact mul_le_mul_of_nonneg_right (hloc x hx) (hκpos x)
    · rw [Set.indicator_of_mem (show x ∈ sᶜ from hx)]
      have hh := mul_le_mul_of_nonneg_right (hSb x) (hκpos x)
      have hh' := mul_nonneg hc (hκpos x)
      linarith
  rw [integral_add (hκi.const_mul c) ((hκi.indicator hs.compl).const_mul M),
    integral_const_mul, integral_const_mul, integral_indicator hs.compl, hmass, mul_one] at hb
  have hh := integral_add_compl hs hκi
  rw [hmass] at hh
  have he : (∫ x in sᶜ, κ x) = 1-∫ x in s, κ x := by linarith
  rwa [he] at hb

/-- The only order hypothesis needed for the Tauberian step: the function cannot
decrease more quickly than the exponential rate. -/
def SlowDecrease (S : ℝ → ℝ) : Prop :=
  ∀ t u : ℝ, t ≤ u → S t ≤ Real.exp (u-t) * S u

lemma slow_forward (S : ℝ → ℝ) (hS : SlowDecrease S) (hpos : ∀ t, 0 ≤ S t)
    (t h x : ℝ) (hx : x ∈ Set.Ioo 0 h) :
    Real.exp (-h) * S t ≤ S (x+t) := by
  have hh := hS t (x+t) (by linarith [hx.1])
  have he : x+t-t = x := by ring
  rw [he] at hh
  have hh' := mul_le_mul_of_nonneg_left hh (Real.exp_pos (-x)).le
  have hc : Real.exp (-x) * (Real.exp x * S (x+t)) = S (x+t) := by
    rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
  rw [hc] at hh'
  exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hx.2])) (hpos t)).trans hh'

lemma slow_backward (S : ℝ → ℝ) (hS : SlowDecrease S) (hpos : ∀ t, 0 ≤ S t)
    (t h x : ℝ) (hx : x ∈ Set.Ioo (-h) 0) :
    S (x+t) ≤ Real.exp h * S t := by
  have hh := hS (x+t) t (by linarith [hx.2])
  have he : t-(x+t) = -x := by ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (Real.exp_le_exp.mpr (by linarith [hx.1])) (hpos t))

lemma positive_smoothing_tauberian
    (S : ℝ → ℝ) (M : ℝ)
    (hS : Measurable S) (hpos : ∀ t, 0 ≤ S t) (hSb : ∀ t, S t ≤ M)
    (hslow : SlowDecrease S)
    (hsmooth : ∀ (ψ : ℝ → ℂ) (κ : ℝ → ℝ),
      Integrable ψ → Integrable (𝓕 ψ) → HasCompactSupport ψ →
      Continuous κ → Integrable κ → (∀ x, 0 ≤ κ x) →
      (∀ x, 𝓕 ψ x = (κ x : ℂ)) → (∫ x, κ x) = 1 →
      Tendsto (fun t : ℝ ↦ ∫ x, S (x+t) * κ x) atTop (nhds 1)) :
    Tendsto S atTop (nhds 1) := by
  have hM : 0 ≤ M := (hpos 0).trans (hSb 0)
  have hnorm (t : ℝ) : ‖S t‖ ≤ M := by simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos t)] using hSb t
  apply tendsto_order.mpr
  constructor
  · intro a ha
    by_cases ha0 : a < 0
    · exact Eventually.of_forall (fun t ↦ ha0.trans_le (hpos t))
    have hat : 0 ≤ a := le_of_not_gt ha0
    have ht : Tendsto (fun h : ℝ ↦ Real.exp h * a + M*h) (nhds 0) (nhds a) := by
      convert ((Real.continuous_exp.tendsto 0).mul_const a).add (tendsto_id.const_mul M) using 1; simp
    obtain ⟨h,hh,hcond⟩ := (ht.eventually (eventually_lt_nhds ha)).exists_gt
    obtain ⟨ψ,κ,hψ,hψF,hψc,hκc,hκi,hκpos,hFT,hmass,hconc⟩ :=
      exists_concentrated_kernel (-h) 0 h (by linarith) hh
    have hsm := hsmooth ψ κ hψ hψF hψc hκc hκi hκpos hFT hmass
    filter_upwards [hsm.eventually (eventually_gt_nhds hcond)] with t ht
    have hb := weighted_local_upper (fun x ↦ S (x+t)) κ (Set.Ioo (-h) 0)
      (Real.exp h * S t) M measurableSet_Ioo (weighted_integrable S κ M hS hnorm hκi t)
      hκi hκpos (mul_nonneg (Real.exp_pos _).le (hpos t))
      (fun x ↦ hSb (x+t)) (fun x hx ↦ slow_backward S hslow hpos t h x hx) hmass
    have herr : M*(1-∫ x in Set.Ioo (-h) 0, κ x) ≤ M*h :=
      mul_le_mul_of_nonneg_left (by linarith) hM
    have he := Real.exp_pos h
    by_contra hnot
    have hat' : S t ≤ a := le_of_not_gt hnot
    have hmm := mul_le_mul_of_nonneg_left hat' he.le
    linarith
  · intro b hb
    have hb0 : 0 < b := by linarith
    have ht : Tendsto (fun h : ℝ ↦ Real.exp (-h) * (1-h) * b) (nhds 0) (nhds b) := by
      have hc : Continuous (fun h : ℝ ↦ Real.exp (-h) * (1-h) * b) := by fun_prop
      simpa using hc.tendsto 0
    have hnear := (ht.eventually (eventually_gt_nhds hb)).and
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))
    obtain ⟨h,hh,hcond,hh1⟩ := hnear.exists_gt
    obtain ⟨ψ,κ,hψ,hψF,hψc,hκc,hκi,hκpos,hFT,hmass,hconc⟩ :=
      exists_concentrated_kernel 0 h h hh hh
    have hsm := hsmooth ψ κ hψ hψF hψc hκc hκi hκpos hFT hmass
    filter_upwards [hsm.eventually (eventually_lt_nhds hcond)] with t ht
    have hl := weighted_local_lower (fun x ↦ S (x+t)) κ (Set.Ioo 0 h)
      (Real.exp (-h) * S t) measurableSet_Ioo (weighted_integrable S κ M hS hnorm hκi t)
      hκi hκpos (fun x ↦ hpos (x+t)) (fun x hx ↦ slow_forward S hslow hpos t h x hx)
    by_contra hnot
    have hbt : b ≤ S t := le_of_not_gt hnot
    have hmasspos : 0 ≤ ∫ x in Set.Ioo 0 h, κ x :=
      setIntegral_nonneg measurableSet_Ioo (fun x _ ↦ hκpos x)
    have he := Real.exp_pos (-h)
    have h1 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbt he.le) hmasspos
    have h2 := mul_le_mul_of_nonneg_left hconc.le (mul_nonneg he.le hb0.le)
    nlinarith

noncomputable def unitStep : ℝ → ℝ := (Set.Ici 0).indicator (fun _ ↦ 1)

lemma unitStep_measurable : Measurable unitStep := measurable_const.indicator measurableSet_Ici

lemma unitStep_nonneg (x : ℝ) : 0 ≤ unitStep x := by
  by_cases hx : 0 ≤ x <;> simp [unitStep, hx]

lemma unitStep_le_one (x : ℝ) : unitStep x ≤ 1 := by
  by_cases hx : 0 ≤ x <;> simp [unitStep, hx]

lemma unitStep_norm (x : ℝ) : ‖unitStep x‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs,abs_of_nonneg (unitStep_nonneg x)] using unitStep_le_one x

lemma unitStep_pairing_tendsto (κ : ℝ → ℝ) (hκi : Integrable κ) (hκpos : ∀ x, 0 ≤ κ x) :
    Tendsto (fun t : ℝ ↦ ∫ x, unitStep (x+t) * κ x) atTop (nhds (∫ x, κ x)) := by
  apply tendsto_integral_filter_of_dominated_convergence κ
  · exact Eventually.of_forall (fun t ↦
      (unitStep_measurable.comp (by fun_prop)).aestronglyMeasurable.mul hκi.aestronglyMeasurable)
  · apply Eventually.of_forall
    intro t
    filter_upwards with x
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (unitStep_nonneg _),
      Real.norm_eq_abs, abs_of_nonneg (hκpos x)]
    simpa using mul_le_mul_of_nonneg_right (unitStep_le_one (x+t)) (hκpos x)
  · exact hκi
  · filter_upwards with x
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (-x)] with t ht
    have he : unitStep (x+t) = 1 := by simp [unitStep, show 0 ≤ x+t by linarith]
    rw [he,one_mul]

/-- A bounded Wiener--Ikehara theorem in logarithmic coordinates. The Laplace
transform of `S - unitStep` has continuous boundary values, and `exp(t) * S(t)`
is nondecreasing, so `S` tends to one. -/
lemma laplace_boundary_tauberian
    (S : ℝ → ℝ) (G : ℝ × ℝ → ℂ) (M : ℝ)
    (hS : Measurable S) (hpos : ∀ t, 0 ≤ S t) (hSb : ∀ t, S t ≤ M)
    (hzero : ∀ t, t < 0 → S t = 0) (hslow : SlowDecrease S)
    (hG : Continuous G)
    (hLap : ∀ σ : ℝ, 0 < σ → ∀ ξ : ℝ,
      laplace (fun t ↦ ((S t - unitStep t : ℝ) : ℂ))
        (σ + (2*Real.pi*ξ : ℝ)*Complex.I) = G (σ,ξ)) :
    Tendsto S atTop (nhds 1) := by
  have hnorm (t : ℝ) : ‖S t‖ ≤ M := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hpos t)] using hSb t
  apply positive_smoothing_tauberian S M hS hpos hSb hslow
  intro ψ κ hψ hψF hψc hκc hκi hκpos hFT hmass
  have hf : AEStronglyMeasurable (fun t ↦ ((S t - unitStep t : ℝ) : ℂ)) volume :=
    (Complex.continuous_ofReal.measurable.comp (hS.sub unitStep_measurable)).aestronglyMeasurable
  have hfb (t : ℝ) : ‖((S t - unitStep t : ℝ) : ℂ)‖ ≤ M+1 := by
    rw [Complex.norm_real]
    exact (norm_sub_le _ _).trans (add_le_add (hnorm t) (unitStep_norm t))
  have hfz (t : ℝ) (ht : t < 0) : ((S t - unitStep t : ℝ) : ℂ) = 0 := by
    simp [hzero t ht,unitStep,not_le.mpr ht]
  have hs := laplace_boundary_smoothing _ ψ G (M+1) hf hfb hfz hG hLap hψ hψF hψc
  have he (t : ℝ) : (∫ x : ℝ, ((S (x+t)-unitStep (x+t) : ℝ) : ℂ) * 𝓕 ψ x) =
      ((∫ x : ℝ, (S (x+t)-unitStep (x+t)) * κ x : ℝ) : ℂ) := by
    simp_rw [hFT, ← Complex.ofReal_mul]
    exact integral_ofReal
  simp_rw [he] at hs
  have hs' : Tendsto (fun t : ℝ ↦ ∫ x : ℝ, (S (x+t)-unitStep (x+t))*κ x)
      atTop (nhds 0) := by
    simpa only [Function.comp_def,Complex.ofReal_re,Complex.zero_re] using
      Complex.continuous_re.continuousAt.tendsto.comp hs
  have hu := unitStep_pairing_tendsto κ hκi hκpos
  rw [hmass] at hu
  have hh := hs'.add hu
  simp only [zero_add] at hh
  apply hh.congr'
  apply Eventually.of_forall
  intro t
  simp_rw [sub_mul]
  rw [integral_sub (weighted_integrable S κ M hS hnorm hκi t)
    (weighted_integrable unitStep κ 1 unitStep_measurable unitStep_norm hκi t), sub_add_cancel]

end TaubCore


/- Prime asymptotics from the bounded Tauberian theorem. -/
open MeasureTheory Filter Finset
open scoped Asymptotics
namespace PrimeAsymptotic

noncomputable def S (t : ℝ) : ℝ := Real.exp (-t) * Chebyshev.psi (Real.exp t)

lemma S_measurable : Measurable S := by
  exact (Real.continuous_exp.comp continuous_neg).measurable.mul
    (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable)

lemma S_nonneg (t : ℝ) : 0 ≤ S t := mul_nonneg (Real.exp_pos _).le (Chebyshev.psi_nonneg _)

lemma S_bound (t : ℝ) : S t ≤ Real.log 4 + 4 := by
  have hh := mul_le_mul_of_nonneg_left
    (Chebyshev.psi_le_const_mul_self (Real.exp_pos t).le) (Real.exp_pos (-t)).le
  have he : Real.exp (-t) * ((Real.log 4+4) * Real.exp t) = Real.log 4+4 := by
    rw [mul_left_comm, ← Real.exp_add, neg_add_cancel, Real.exp_zero,mul_one]
  exact he ▸ hh

lemma S_zero (t : ℝ) (ht : t < 0) : S t = 0 := by
  have hh : Real.exp t < 2 := (Real.exp_lt_one_iff.mpr ht).trans (by norm_num)
  simp [S,Chebyshev.psi_eq_zero_of_lt_two hh]

lemma S_slow : TaubCore.SlowDecrease S := by
  intro t u htu
  have hh := mul_le_mul_of_nonneg_left
    (Chebyshev.psi_mono (Real.exp_le_exp.mpr htu)) (Real.exp_pos (-t)).le
  have he : Real.exp (u-t) * S u = Real.exp (-t) * Chebyshev.psi (Real.exp u) := by
    dsimp only [S]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rwa [he]

lemma psi_sum (x : ℝ) : Chebyshev.psi x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n := by
  rw [Chebyshev.psi]
  congr 1

lemma psi_bigO : (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k)
    =O[atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound (Real.log 4+4)
  apply Eventually.of_forall
  intro n
  have he : ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k = Chebyshev.psi (n : ℝ) := by
    rw [psi_sum,Nat.floor_natCast]
  rw [he,Real.rpow_one,Real.norm_eq_abs,abs_of_nonneg (Chebyshev.psi_nonneg _),
    Real.norm_eq_abs,abs_of_nonneg (Nat.cast_nonneg n)]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)

lemma exp_image_Ioi_zero : Real.exp '' Set.Ioi 0 = Set.Ioi 1 := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact Real.one_lt_exp_iff.mpr hx
  · intro hy
    exact ⟨Real.log y,Real.log_pos hy,Real.exp_log (by have hh : 1 < y := hy; linarith)⟩

lemma mellin_psi_eq_laplace (s : ℂ) :
    (∫ x : ℝ in Set.Ioi 1, (Chebyshev.psi x : ℂ) * (x : ℂ) ^ (-(1+s+1))) =
      TaubCore.laplace (fun t ↦ (S t : ℂ)) s := by
  rw [← exp_image_Ioi_zero, integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi (fun x _ ↦ (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn]
  rw [TaubCore.laplace, integral_Ici_eq_integral_Ioi]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only [abs_of_pos (Real.exp_pos _), Complex.real_smul, S,Complex.ofReal_mul]
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)),
    ← Complex.ofReal_log (Real.exp_pos t).le, Real.log_exp]
  simp only [Complex.ofReal_exp, Complex.ofReal_neg]
  calc
    Complex.exp (t : ℂ) * ((Chebyshev.psi (Real.exp t) : ℂ) *
        Complex.exp ((t : ℂ) * -(1+s+1))) =
      (Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * -(1+s+1))) *
        (Chebyshev.psi (Real.exp t) : ℂ) := by ring
    _ = (Complex.exp (-s*(t : ℂ)) * Complex.exp (-(t : ℂ))) *
        (Chebyshev.psi (Real.exp t) : ℂ) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      ring
    _ = _ := by ring

lemma laplace_S (s : ℂ) (hs : 0 < s.re) :
    TaubCore.laplace (fun t ↦ (S t : ℂ)) s =
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (1+s) / (1+s) := by
  have h1 : 1 < (1+s).re := by simp only [Complex.add_re,Complex.one_re]; linarith
  have hh := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
    (r := 1) (s := 1+s) (by norm_num) h1 psi_bigO (fun _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
  have he (x : ℝ) : (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (Chebyshev.psi x : ℂ) := by rw [psi_sum]; push_cast; rfl
  simp_rw [he] at hh
  rw [mellin_psi_eq_laplace] at hh
  rw [hh,mul_div_cancel_left₀]
  exact Complex.ne_zero_of_re_pos (by linarith : 0 < (1+s).re)

lemma laplace_integrable_bounded (f : ℝ → ℂ) (M : ℝ) (s : ℂ) (hs : 0 < s.re)
    (hf : Measurable f) (hb : ∀ t, ‖f t‖ ≤ M) :
    IntegrableOn (fun t : ℝ ↦ Complex.exp (-s*t) * f t) (Set.Ici 0) := by
  have he : IntegrableOn (fun t : ℝ ↦ Complex.exp (-s*t)) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs) 0)
  exact he.mul_bdd hf.aestronglyMeasurable (Eventually.of_forall hb)

lemma laplace_unitStep (s : ℂ) (hs : 0 < s.re) :
    TaubCore.laplace (fun t ↦ (TaubCore.unitStep t : ℂ)) s = 1/s := by
  rw [TaubCore.laplace]
  have he : (∫ t : ℝ in Set.Ici 0, Complex.exp (-s*t) * (TaubCore.unitStep t : ℂ)) =
      ∫ t : ℝ in Set.Ici 0, Complex.exp (-s*t) := by
    apply setIntegral_congr_fun measurableSet_Ici
    intro t ht
    simp [TaubCore.unitStep,ht]
  rw [he,integral_Ici_eq_integral_Ioi,
    integral_exp_mul_complex_Ioi (by simpa using neg_neg_of_pos hs)]
  simp

lemma laplace_S_sub_step (s : ℂ) (hs : 0 < s.re) :
    TaubCore.laplace (fun t ↦ ((S t-TaubCore.unitStep t : ℝ) : ℂ)) s =
      LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) (1+s) / (1+s) - 1/s := by
  have hS : Measurable (fun t ↦ (S t : ℂ)) := Complex.continuous_ofReal.measurable.comp S_measurable
  have hSi := laplace_integrable_bounded _ (Real.log 4+4) s hs hS (fun t ↦ by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (S_nonneg t)] using S_bound t)
  have hstep : Measurable (fun t ↦ (TaubCore.unitStep t : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp TaubCore.unitStep_measurable
  have hstepi := laplace_integrable_bounded _ 1 s hs hstep (fun t ↦ by
    simpa only [Complex.norm_real] using TaubCore.unitStep_norm t)
  simp only [TaubCore.laplace,Complex.ofReal_sub,mul_sub]
  rw [integral_sub hSi hstepi]
  exact congrArg₂ (·-·) (laplace_S s hs) (laplace_unitStep s hs)

noncomputable def regular (z : ℂ) : ℂ :=
  ArithmeticFunction.vonMangoldt.LFunctionResidueClassAux (1 : ZMod 1) z

lemma regular_continuous : ContinuousOn regular {z | 1 ≤ z.re} :=
  ArithmeticFunction.vonMangoldt.continuousOn_LFunctionResidueClassAux _

lemma regular_eq (z : ℂ) (hz : 1 < z.re) :
    regular z = LSeries (fun n ↦ (ArithmeticFunction.vonMangoldt n : ℂ)) z - 1/(z-1) := by
  have hh := ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux
    (a := (1 : ZMod 1)) isUnit_one hz
  have he (n : ℕ) : ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod 1) n =
      ArithmeticFunction.vonMangoldt n := by
    apply Set.indicator_of_mem
    exact Subsingleton.elim _ _
  simpa only [he,Nat.totient_one,Nat.cast_one,inv_one] using hh

noncomputable def boundaryPoint (p : ℝ × ℝ) : ℂ :=
  1 + (max p.1 0 : ℝ) + (2*Real.pi*p.2 : ℝ)*Complex.I

lemma boundaryPoint_continuous : Continuous boundaryPoint := by unfold boundaryPoint; fun_prop

lemma boundaryPoint_re (p : ℝ × ℝ) : (boundaryPoint p).re = 1 + max p.1 0 := by
  simp [boundaryPoint]

lemma boundaryPoint_re_ge (p : ℝ × ℝ) : 1 ≤ (boundaryPoint p).re := by
  rw [boundaryPoint_re]
  linarith [le_max_right p.1 (0 : ℝ)]

noncomputable def boundary (p : ℝ × ℝ) : ℂ := (regular (boundaryPoint p) - 1) / boundaryPoint p

lemma boundary_continuous : Continuous boundary := by
  apply Continuous.div
  · exact (regular_continuous.comp_continuous boundaryPoint_continuous boundaryPoint_re_ge).sub continuous_const
  · exact boundaryPoint_continuous
  · intro p
    exact Complex.ne_zero_of_re_pos (by linarith [boundaryPoint_re_ge p])

lemma laplace_boundary (σ : ℝ) (hσ : 0 < σ) (ξ : ℝ) :
    TaubCore.laplace (fun t ↦ ((S t - TaubCore.unitStep t : ℝ) : ℂ))
      (σ + (2*Real.pi*ξ : ℝ)*Complex.I) = boundary (σ,ξ) := by
  let s : ℂ := σ + (2*Real.pi*ξ : ℝ)*Complex.I
  have hs : 0 < s.re := by simpa [s] using hσ
  have he : boundaryPoint (σ,ξ) = 1+s := by simp [boundaryPoint,s,max_eq_left hσ.le,add_assoc]
  change TaubCore.laplace _ s = _
  rw [laplace_S_sub_step s hs]
  change _ = (regular (boundaryPoint (σ,ξ)) - 1) / boundaryPoint (σ,ξ)
  rw [he,regular_eq (1+s) (by simp only [Complex.add_re,Complex.one_re]; linarith)]
  have hs0 : s ≠ 0 := Complex.ne_zero_of_re_pos hs
  have hs1 : 1+s ≠ 0 := Complex.ne_zero_of_re_pos (by simp only [Complex.add_re,Complex.one_re]; linarith)
  have he' : 1+s-1 = s := by ring
  rw [he']
  field_simp; ring

lemma S_tendsto : Tendsto S atTop (nhds 1) :=
  TaubCore.laplace_boundary_tauberian S boundary (Real.log 4+4)
    S_measurable S_nonneg S_bound S_zero S_slow boundary_continuous laplace_boundary

/-- The prime number theorem in terms of Chebyshev's second function. -/
lemma psi_div_tendsto_one : Tendsto (fun x : ℝ ↦ Chebyshev.psi x / x) atTop (nhds 1) := by
  have hh := S_tendsto.comp Real.tendsto_log_atTop
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Function.comp_def,S,Real.exp_log hx,Real.exp_neg]
  ring

lemma psi_sub_theta_div_tendsto_zero :
    Tendsto (fun x : ℝ ↦ (Chebyshev.psi x-Chebyshev.theta x)/x) atTop (nhds 0) := by
  have hlim : Tendsto (fun x : ℝ ↦ 2 * (Real.log x / Real.sqrt x)) atTop (nhds 0) := by
    simpa only [mul_zero,Real.sqrt_eq_rpow] using
      ((isLittleO_log_rpow_atTop (r := (1 : ℝ)/2) (by norm_num)).tendsto_div_nhds_zero).const_mul 2
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x)) hx.le
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    have hh := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx
    rw [abs_of_nonneg (sub_nonneg.mpr (Chebyshev.theta_le_psi x))] at hh
    apply (div_le_div_of_nonneg_right hh hx0.le).trans_eq
    have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
    field_simp
    nlinarith [congrArg (fun y : ℝ ↦ y*Real.log x) (Real.sq_sqrt hx0.le)]

lemma theta_div_tendsto_one : Tendsto (fun x : ℝ ↦ Chebyshev.theta x/x) atTop (nhds 1) := by
  have hh := psi_div_tendsto_one.sub psi_sub_theta_div_tendsto_zero
  simpa only [sub_zero,sub_div,sub_sub_cancel] using hh

lemma exists_prime_of_theta_lt (a b : ℝ) (hab : a ≤ b) (hb : 0 ≤ b)
    (hθ : Chebyshev.theta a < Chebyshev.theta b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) ≤ b := by
  classical
  by_contra hn
  have he : ((Finset.Ioc 0 ⌊a⌋₊).filter Nat.Prime) = ((Finset.Ioc 0 ⌊b⌋₊).filter Nat.Prime) := by
    apply Finset.Subset.antisymm
    · intro p hp
      simp only [Finset.mem_filter,Finset.mem_Ioc] at hp ⊢
      exact ⟨⟨hp.1.1,hp.1.2.trans (Nat.floor_mono hab)⟩,hp.2⟩
    · intro p hp
      simp only [Finset.mem_filter,Finset.mem_Ioc] at hp ⊢
      have hpb : (p : ℝ) ≤ b := (Nat.cast_le.mpr hp.1.2).trans (Nat.floor_le hb)
      have hpa : (p : ℝ) ≤ a := le_of_not_gt (fun hpa ↦ hn ⟨p,hp.2,hpa,hpb⟩)
      exact ⟨⟨hp.1.1,Nat.le_floor hpa⟩,hp.2⟩
  have heθ : Chebyshev.theta a = Chebyshev.theta b := by unfold Chebyshev.theta; rw [he]
  exact (ne_of_lt hθ) heθ

/-- Every interval `(c*x, x]`, for fixed `c < 1`, contains a prime once `x` is large enough. -/
lemma short_prime_intervals (c : ℝ) (hc : c < 1) :
    ∀ᶠ x : ℝ in atTop, ∃ p : ℕ, p.Prime ∧ c*x < p ∧ (p : ℝ) ≤ x := by
  by_cases hc0 : 0 < c
  · have ht : Tendsto (fun x : ℝ ↦ Chebyshev.theta (c*x)/x) atTop (nhds c) := by
      have hh := (theta_div_tendsto_one.comp (tendsto_id.const_mul_atTop hc0)).mul_const c
      simp only [one_mul] at hh
      apply hh.congr'
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      dsimp only [Function.comp_def,id_eq]
      field_simp
    have hd := theta_div_tendsto_one.sub ht
    filter_upwards [hd.eventually (eventually_gt_nhds (sub_pos.mpr hc)),
      eventually_gt_atTop (0 : ℝ)] with x hθ hx
    apply exists_prime_of_theta_lt (c*x) x (by nlinarith) hx.le
    have hh : Chebyshev.theta (c*x)/x < Chebyshev.theta x/x := by linarith
    exact (div_lt_div_iff_of_pos_right hx).mp hh
  · filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    refine ⟨2,by decide,?_,hx⟩
    have hcx : c*x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hc0) (by linarith)
    norm_num
    linarith

end PrimeAsymptotic


/- The sharp Bose--Chowla asymptotic lower bound. -/
open Filter
lemma f_ratio_eventually_gt_one (c : ℝ) (hc : c < 1) :
    ∀ᶠ N : ℕ in atTop, c < (f N 3 : ℝ) / (N : ℝ)^((1 : ℝ)/3) :=
  f_ratio_lower_of_short_prime_intervals PrimeAsymptotic.short_prime_intervals c hc


lemma target_iff_sharp_upper :
    ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3))) ↔
      ∀ c : ℝ, 1 < c → ∀ᶠ N : ℕ in atTop,
        (f N 3 : ℝ)/(N : ℝ)^((1 : ℝ)/3) < c := by
  rw [target_iff_ratio,tendsto_order]
  exact ⟨fun h ↦ h.2, fun h ↦ ⟨f_ratio_eventually_gt_one,h⟩⟩


/- A global fourth-moment obstruction to a flat self-convolution. -/
open Finset Filter
namespace MomentBound

lemma centered_second {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, (x i-x j)^2) = 2 * Fintype.card ι * ∑ i, (x i)^2 := by
  have hi (i : ι) : (∑ j, (x i-x j)^2) = Fintype.card ι * (x i)^2 + ∑ j, (x j)^2 := by
    simp only [sub_sq,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,
      card_univ,hx,mul_zero,sub_zero]
  simp_rw [hi,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ]
  ring

lemma centered_fourth {ι : Type*} [Fintype ι] (x : ι → ℝ) (hx : ∑ i, x i = 0) :
    (∑ i, ∑ j, (x i-x j)^4) = 2 * Fintype.card ι * ∑ i, (x i)^4 + 6*(∑ i, (x i)^2)^2 := by
  have he (i j : ι) : (x i-x j)^4 =
      (x i)^4 - 4*(x i)^3*x j + 6*(x i)^2*(x j)^2 - 4*x i*(x j)^3 + (x j)^4 := by ring
  have hi (i : ι) : (∑ j, (x i-x j)^4) = Fintype.card ι * (x i)^4 +
      6*(x i)^2*(∑ j, (x j)^2) - 4*x i*(∑ j, (x j)^3) + ∑ j, (x j)^4 := by
    simp only [he,sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,
      card_univ,hx,mul_zero,sub_zero]
  simp only [hi,sum_add_distrib,sum_sub_distrib,← sum_mul,← mul_sum,
    sum_const,nsmul_eq_mul,card_univ,hx,mul_zero,zero_mul,sub_zero]
  ring

lemma fourth_moment {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    (2 : ℝ) * (∑ i, ∑ j, (b i-b j)^2)^2 ≤
      (Fintype.card ι : ℝ)^2 * ∑ i, ∑ j, (b i-b j)^4 := by
  by_cases hι : Fintype.card ι = 0
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hι
    simp
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast hι
  let c : ℝ := (∑ i, b i) / Fintype.card ι
  let x : ι → ℝ := fun i ↦ b i-c
  have hx : ∑ i, x i = 0 := by
    simp only [x,sum_sub_distrib,sum_const,nsmul_eq_mul,card_univ]
    dsimp only [c]
    rw [mul_div_cancel₀ _ hn, sub_self]
  have he (i j : ι) : b i-b j = x i-x j := by dsimp only [x]; ring
  simp_rw [he]
  rw [centered_second x hx,centered_fourth x hx]
  have hc := sum_mul_sq_le_sq_mul_sq (univ : Finset ι) (fun i ↦ (x i)^2) (fun _ ↦ (1 : ℝ))
  simp only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one,card_univ] at hc
  have hp (i : ι) : ((x i)^2)^2 = (x i)^4 := by ring
  simp_rw [hp] at hc
  have hh := mul_le_mul_of_nonneg_left hc (sq_nonneg (Fintype.card ι : ℝ))
  nlinarith only [hh]

lemma fourth_polynomial_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) (L : ℝ) :
    0 ≤ ∑ i, ∑ j, (9*(b i-b j)^4-12*L^2*(b i-b j)^2+2*L^4) := by
  by_cases hι : Fintype.card ι = 0
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hι
    simp
  have hn : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hι
  have hh := fourth_moment b
  have hsq := sq_nonneg (3*(∑ i, ∑ j, (b i-b j)^2) - L^2*(Fintype.card ι : ℝ)^2)
  simp only [sum_add_distrib,sum_sub_distrib,← mul_sum,sum_const,nsmul_eq_mul,card_univ]
  apply nonneg_of_mul_nonneg_left (b := (Fintype.card ι : ℝ)^2) _ (sq_pos_of_pos hn)
  nlinarith only [hh,hsq]

/-- The rational polynomial used in the weighted energy inequality. -/
noncomputable def weight (x : ℝ) : ℝ := (63*x^4-84*x^2+89)/75

lemma weight_pair_sum {ι : Type*} [Fintype ι] (b : ι → ℝ) :
    (Fintype.card ι : ℝ)^2 ≤ ∑ i, ∑ j, weight (b i-b j) := by
  have h := fourth_polynomial_nonneg b 1
  have he (x : ℝ) : weight x = 1 + (7/75)*(9*x^4-12*x^2+2) := by dsimp [weight]; ring
  simp_rw [he,sum_add_distrib,← mul_sum] 
  simp only [sum_const,nsmul_eq_mul,mul_one,card_univ]
  norm_num at h
  nlinarith only [h]

noncomputable def differenceCount {ι : Type*} [Fintype ι] (b : ι → ℤ) (d : ℤ) : ℝ :=
  ∑ i, ∑ j, if b i-b j = d then 1 else 0

lemma differenceCount_nonneg {ι : Type*} [Fintype ι] (b : ι → ℤ) (d : ℤ) :
    0 ≤ differenceCount b d := by unfold differenceCount; positivity

lemma sum_differenceCount_mul {ι : Type*} [Fintype ι] (b : ι → ℤ) (T : Finset ℤ)
    (hT : ∀ i j, b i-b j ∈ T) (w : ℤ → ℝ) :
    (∑ d ∈ T, differenceCount b d * w d) = ∑ i, ∑ j, w (b i-b j) := by
  classical
  simp only [differenceCount,sum_mul,ite_mul,one_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_ite_eq,if_pos (hT i j)]

lemma weighted_difference_energy {ι : Type*} [Fintype ι] (b : ι → ℤ) (T : Finset ℤ) (L : ℝ)
    (hT : ∀ i j, b i-b j ∈ T) :
    (Fintype.card ι : ℝ)^4 ≤
      (∑ d ∈ T, (differenceCount b d)^2) * (∑ d ∈ T, (weight ((d : ℝ)/L))^2) := by
  have hh := weight_pair_sum (fun i ↦ (b i : ℝ)/L)
  have he : (∑ d ∈ T, differenceCount b d * weight ((d : ℝ)/L)) =
      ∑ i, ∑ j, weight ((b i : ℝ)/L-(b j : ℝ)/L) := by
    rw [sum_differenceCount_mul b T hT]
    simp only [Int.cast_sub,sub_div]
  rw [← he] at hh
  have hs := pow_le_pow_left₀ (sq_nonneg (Fintype.card ι : ℝ)) hh 2
  have hc := sum_mul_sq_le_sq_mul_sq T (differenceCount b) (fun d ↦ weight ((d : ℝ)/L))
  have hp : ((Fintype.card ι : ℝ)^2)^2 = (Fintype.card ι : ℝ)^4 := by ring
  rw [hp] at hs
  exact hs.trans hc

lemma sum_symmetric_succ (F : ℤ → ℝ) (n : ℕ) :
    (∑ d ∈ Icc (-(n+1 : ℤ)) (n+1 : ℤ), F d) =
      F (-(n+1 : ℤ)) + F (n+1 : ℤ) + ∑ d ∈ Icc (-(n : ℤ)) n, F d := by
  have he : Icc (-(n+1 : ℤ)) (n+1 : ℤ) =
      insert (-(n+1 : ℤ)) (insert (n+1 : ℤ) (Icc (-(n : ℤ)) n)) := by
    ext d
    simp only [mem_Icc,mem_insert]
    omega
  rw [he,sum_insert (by simp; omega),sum_insert (by simp)]
  ring

lemma sum_symmetric_pow_zero (n : ℕ) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (d : ℝ)^0) = 2*(n : ℝ)+1 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    rw [sum_symmetric_succ,ih]
    ring

lemma sum_symmetric_pow_two (n : ℕ) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (d : ℝ)^2) = (2/3)*(n : ℝ)^3+n^2+n/3 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    rw [sum_symmetric_succ,ih]
    push_cast
    ring

lemma sum_symmetric_pow_four (n : ℕ) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (d : ℝ)^4) = (2/5)*(n : ℝ)^5+n^4+(2/3)*n^3-n/15 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    rw [sum_symmetric_succ,ih]
    push_cast
    ring

lemma sum_symmetric_pow_six (n : ℕ) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (d : ℝ)^6) = (2/7)*(n : ℝ)^7+n^6+n^5-n^3/3+n/21 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    rw [sum_symmetric_succ,ih]
    push_cast
    ring

lemma sum_symmetric_pow_eight (n : ℕ) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (d : ℝ)^8) =
      (2/9)*(n : ℝ)^9+n^8+(4/3)*n^7-(14/15)*n^5+(4/9)*n^3-n/15 := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    rw [sum_symmetric_succ,ih]
    push_cast
    ring

lemma weight_numerator_square_sum (n : ℕ) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (63*(d : ℝ)^4-84*(n : ℝ)^2*(d : ℝ)^2+89*(n : ℝ)^4)^2) =
      11040*(n : ℝ)^9+4624*n^8+1904*n^7-(6972/5)*n^5+1260*n^3-(1323/5)*n := by
  have he (d : ℤ) : (63*(d : ℝ)^4-84*(n : ℝ)^2*(d : ℝ)^2+89*(n : ℝ)^4)^2 =
      3969*(d : ℝ)^8-10584*(n : ℝ)^2*(d : ℝ)^6+18270*(n : ℝ)^4*(d : ℝ)^4
        -14952*(n : ℝ)^6*(d : ℝ)^2+7921*(n : ℝ)^8*(d : ℝ)^0 := by ring
  simp only [he,sum_add_distrib,sum_sub_distrib,← mul_sum]
  rw [sum_symmetric_pow_eight,sum_symmetric_pow_six,sum_symmetric_pow_four,
    sum_symmetric_pow_two,sum_symmetric_pow_zero]
  ring

lemma weight_square_sum_bound (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ Icc (-(n : ℤ)) n, (weight ((d : ℝ)/n))^2) ≤ (736/375)*(n : ℝ)+2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have he (d : ℤ) : (weight ((d : ℝ)/n))^2 =
      (63*(d : ℝ)^4-84*(n : ℝ)^2*(d : ℝ)^2+89*(n : ℝ)^4)^2 / (5625*(n : ℝ)^8) := by
    dsimp only [weight]
    field_simp; ring
  simp_rw [he]
  rw [← sum_div,weight_numerator_square_sum]
  apply (div_le_iff₀ (by positivity : 0 < 5625*(n : ℝ)^8)).mpr
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h7 : (n : ℝ)^7 ≤ (n : ℝ)^8 := pow_le_pow_right₀ hn1 (by omega)
  have h3 : (n : ℝ)^3 ≤ (n : ℝ)^8 := pow_le_pow_right₀ hn1 (by omega)
  nlinarith [pow_nonneg hn0.le 5,pow_nonneg hn0.le 8]

/-- The global moment improvement on the unweighted Cauchy bound. -/
lemma difference_energy_lower {ι : Type*} [Fintype ι] (b : ι → ℤ) (L : ℕ) (hL : 0 < L)
    (hb : ∀ i j, b i-b j ∈ Icc (-(L : ℤ)) L) :
    (Fintype.card ι : ℝ)^4 ≤
      ((736/375)*(L : ℝ)+2) * ∑ d ∈ Icc (-(L : ℤ)) L, (differenceCount b d)^2 := by
  have hh := weighted_difference_energy b (Icc (-(L : ℤ)) L) L hb
  have hc := mul_le_mul_of_nonneg_left (weight_square_sum_bound L hL)
    (show 0 ≤ ∑ d ∈ Icc (-(L : ℤ)) L, (differenceCount b d)^2 by positivity)
  exact hh.trans (by simpa only [mul_comm] using hc)

end MomentBound


/- Upper energy estimates after smoothing a B3 set. -/
open Finset
namespace MomentBound

noncomputable def quadEnergy {ι : Type*} [Fintype ι] (b : ι → ℤ) : ℝ :=
  ∑ i, ∑ j, ∑ k, ∑ l, if b i+b j = b k+b l then 1 else 0

lemma sum_four_rotate {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (F : ι → κ → τ → ℝ) : (∑ i, ∑ j, ∑ k, F i j k) = ∑ k, ∑ j, ∑ i, F i j k := by
  rw [sum_comm]
  simp_rw [sum_comm (f := fun i k ↦ F i _ k)]
  rw [sum_comm]

lemma difference_energy_eq {ι : Type*} [Fintype ι] (b : ι → ℤ) (T : Finset ℤ)
    (hT : ∀ i j, b i-b j ∈ T) :
    (∑ d ∈ T, (differenceCount b d)^2) = quadEnergy b := by
  simp only [pow_two]
  rw [sum_differenceCount_mul b T hT]
  unfold differenceCount quadEnergy
  apply sum_congr rfl
  intro i hi
  rw [sum_four_rotate]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro k hk
  apply sum_congr rfl
  intro l hl
  congr 1
  apply propext
  omega

lemma two_sum_permutation {A : Finset ℕ} (hA : B3Aux.Good A)
    (a b c d : A) (he : (a : ℕ)+b = c+d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  have hh := B3Aux.sum_two_inj hA ({(a : ℕ),(b : ℕ)} : Multiset ℕ) {(c : ℕ),(d : ℕ)}
    (by simp) (by simp) (by simp [a.property,b.property]) (by simp [c.property,d.property])
    (by simpa using he)
  have ha : (a : ℕ) = c ∨ (a : ℕ) = d := by
    have hm : (a : ℕ) ∈ ({(c : ℕ),(d : ℕ)} : Multiset ℕ) := hh ▸ (by simp)
    simpa using hm
  rcases ha with ha | ha
  · exact Or.inl ⟨Subtype.ext ha,Subtype.ext (by omega)⟩
  · exact Or.inr ⟨Subtype.ext ha,Subtype.ext (by omega)⟩

abbrev Quad (α : Type*) := (α × α) × (α × α)

noncomputable def offQuads (A : Finset ℕ) (i j : ℕ) : Finset (Quad A) :=
  univ.filter (fun p ↦ p.1.1 ≠ p.1.2 ∧ p.2.1 ≠ p.2.2 ∧
    (p.1.1 : ℕ)+p.1.2+i = p.2.1+p.2.2+j)

lemma offQuads_bound {A : Finset ℕ} (hA : B3Aux.Good A) (i j : ℕ) :
    (offQuads A i j).card ≤ 4*(B3Aux.shiftReps A i j).card := by
  classical
  let F : Quad A → ℕ × ℕ := fun p ↦ ((p.1.1 : ℕ)+p.1.2,(p.2.1 : ℕ)+p.2.2)
  refine card_le_mul_card_image_of_maps_to (f := F) (t := B3Aux.shiftReps A i j) ?_ 4 ?_
  · intro p hp
    have hp' := (mem_filter.mp hp).2
    apply B3Aux.shiftReps_mem.mpr
    refine ⟨?_,?_,hp'.2.2⟩
    · exact B3Aux.mem_pairSums_iff.mpr ⟨p.1.1,p.1.1.property,p.1.2,p.1.2.property,
        fun h ↦ hp'.1 (Subtype.ext h),rfl⟩
    · exact B3Aux.mem_pairSums_iff.mpr ⟨p.2.1,p.2.1.property,p.2.2,p.2.2.property,
        fun h ↦ hp'.2.1 (Subtype.ext h),rfl⟩
  · intro r hr
    by_cases hn : ((offQuads A i j).filter (fun p ↦ F p = r)).Nonempty
    · obtain ⟨p,hp⟩ := hn
      have hpr := (mem_filter.mp hp).2
      have hsub : ((offQuads A i j).filter (fun q ↦ F q = r)) ⊆
          ({p.1,p.1.swap} ×ˢ {p.2,p.2.swap}) := by
        intro q hq
        have hqr := (mem_filter.mp hq).2
        have he : F q = F p := hqr.trans hpr.symm
        have h1 := two_sum_permutation hA q.1.1 q.1.2 p.1.1 p.1.2 (congrArg Prod.fst he)
        have h2 := two_sum_permutation hA q.2.1 q.2.2 p.2.1 p.2.2 (congrArg Prod.snd he)
        apply mem_product.mpr
        constructor
        · rcases h1 with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · simp [Prod.ext h1 h2]
          · exact mem_insert_of_mem (mem_singleton.mpr (Prod.ext h1 h2))
        · rcases h2 with ⟨h1,h2⟩ | ⟨h1,h2⟩
          · simp [Prod.ext h1 h2]
          · exact mem_insert_of_mem (mem_singleton.mpr (Prod.ext h1 h2))
      have hh := card_le_card hsub
      have hc : (({p.1,p.1.swap} : Finset (A × A)) ×ˢ {p.2,p.2.swap}).card ≤ 4 := by
        rw [card_product]
        have h1 := card_le_two (a := p.1) (b := p.1.swap)
        have h2 := card_le_two (a := p.2) (b := p.2.swap)
        nlinarith
      exact hh.trans hc
    · simp only [not_nonempty_iff_eq_empty.mp hn,card_empty]
      omega

def leftShift {u : ℕ} (q : Quad (Fin u)) : ℕ := q.1.1 + q.1.2
def rightShift {u : ℕ} (q : Quad (Fin u)) : ℕ := q.2.1 + q.2.2

noncomputable def shiftFiber (u i j : ℕ) : Finset (Quad (Fin u)) :=
  univ.filter (fun q ↦ leftShift q+i = rightShift q+j)

lemma card_shiftFiber (u i j : ℕ) : (shiftFiber u i j).card ≤ u^3 := by
  let F : Quad (Fin u) → Fin u × Fin u × Fin u := fun q ↦ (q.1.1,q.1.2,q.2.1)
  have hh : (shiftFiber u i j).card ≤ (univ : Finset (Fin u × Fin u × Fin u)).card := by
    apply card_le_card_of_injOn F (fun _ _ ↦ mem_univ _)
    intro p hp q hq he
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    simp only [F,Prod.mk.injEq] at he
    rcases he with ⟨h1,h2,h3⟩
    apply Prod.ext (Prod.ext h1 h2)
    apply Prod.ext h3
    apply Fin.ext
    simp only [leftShift,rightShift,h1,h2,h3] at hp' hq'
    omega
  simpa [Fintype.card_prod,pow_succ,mul_assoc] using hh

noncomputable def badShiftQuads (A : Finset ℕ) (u : ℕ) : Finset (Quad (Fin u)) :=
  univ.filter (fun q ↦ ∃ a ∈ A, ∃ b ∈ A, a+leftShift q = b+rightShift q)

lemma card_badShiftQuads (A : Finset ℕ) (u : ℕ) :
    (badShiftQuads A u).card ≤ A.card^2*u^3 := by
  classical
  have hsub : badShiftQuads A u ⊆ A.biUnion (fun a ↦ A.biUnion (fun b ↦ shiftFiber u a b)) := by
    intro q hq
    obtain ⟨a,ha,b,hb,he⟩ := (mem_filter.mp hq).2
    exact mem_biUnion.mpr ⟨a,ha,mem_biUnion.mpr ⟨b,hb,mem_filter.mpr ⟨mem_univ _,by omega⟩⟩⟩
  calc
    _ ≤ (A.biUnion (fun a ↦ A.biUnion (fun b ↦ shiftFiber u a b))).card := card_le_card hsub
    _ ≤ ∑ a ∈ A, (A.biUnion (fun b ↦ shiftFiber u a b)).card := card_biUnion_le
    _ ≤ ∑ a ∈ A, ∑ b ∈ A, (shiftFiber u a b).card := sum_le_sum (fun _ _ ↦ card_biUnion_le)
    _ ≤ ∑ a ∈ A, ∑ b ∈ A, u^3 := sum_le_sum (fun a _ ↦ sum_le_sum (fun b _ ↦ card_shiftFiber u a b))
    _ = _ := by simp [pow_two,mul_assoc]

lemma sum_shiftReps_bound {A : Finset ℕ} (hA : B3Aux.Good A) (u : ℕ) :
    2*(∑ q : Quad (Fin u), (B3Aux.shiftReps A (leftShift q) (rightShift q)).card) ≤
      A.card*u^4 + 2*(A.card.choose 2)*u^3 + 2*A.card^3*u^3 := by
  classical
  have hp (q : Quad (Fin u)) :
      2*(B3Aux.shiftReps A (leftShift q) (rightShift q)).card ≤ A.card +
        (if leftShift q = rightShift q then 2*(B3Aux.pairSums A).card else 0) +
        (if ∃ a ∈ A, ∃ b ∈ A, a+leftShift q=b+rightShift q then 2*A.card else 0) := by
    by_cases he : leftShift q = rightShift q
    · simp only [he,B3Aux.shiftReps_self,if_true]
      omega
    · simp only [he,if_false,add_zero]
      split_ifs with h
      · obtain ⟨a,ha,b,hb,hab⟩ := h
        have hh := B3Aux.shiftReps_bound_bad hA _ _ he ha hb hab
        omega
      · exact B3Aux.shiftReps_bound_good hA _ _ (by simpa using h)
  have hh := sum_le_sum (s := (univ : Finset (Quad (Fin u)))) (fun q _ ↦ hp q)
  rw [← mul_sum,sum_add_distrib,sum_add_distrib] at hh
  have hd : (∑ q : Quad (Fin u), if leftShift q=rightShift q then 2*(B3Aux.pairSums A).card else 0) =
      2*(B3Aux.pairSums A).card*(shiftFiber u 0 0).card := by
    simp only [shiftFiber,add_zero,← sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
    ring
  have hb : (∑ q : Quad (Fin u),
      if ∃ a ∈ A, ∃ b ∈ A, a+leftShift q=b+rightShift q then 2*A.card else 0) =
      2*A.card*(badShiftQuads A u).card := by
    rw [← sum_filter]
    simp only [badShiftQuads,sum_const,nsmul_eq_mul,Nat.cast_id]
    ring
  rw [hd,hb,B3Aux.card_pairSums hA] at hh
  simp only [sum_const,nsmul_eq_mul,card_univ,Fintype.card_prod,Fintype.card_fin] at hh
  have hdiag := Nat.mul_le_mul_left (2*(A.card.choose 2)) (card_shiftFiber u 0 0)
  have hbad := Nat.mul_le_mul_left (2*A.card) (card_badShiftQuads A u)
  nlinarith

noncomputable def fullQuads (A : Finset ℕ) (u : ℕ) : Finset (Quad A × Quad (Fin u)) :=
  univ.filter (fun p ↦ (p.1.1.1 : ℕ)+p.1.1.2+leftShift p.2 =
    p.1.2.1+p.1.2.2+rightShift p.2)

noncomputable def offFullQuads (A : Finset ℕ) (u : ℕ) : Finset (Quad A × Quad (Fin u)) :=
  (fullQuads A u).filter (fun p ↦ p.1.1.1 ≠ p.1.1.2 ∧ p.1.2.1 ≠ p.1.2.2)

noncomputable def leftFullQuads (A : Finset ℕ) (u : ℕ) : Finset (Quad A × Quad (Fin u)) :=
  (fullQuads A u).filter (fun p ↦ p.1.1.1 = p.1.1.2)

noncomputable def rightFullQuads (A : Finset ℕ) (u : ℕ) : Finset (Quad A × Quad (Fin u)) :=
  (fullQuads A u).filter (fun p ↦ p.1.2.1 = p.1.2.2)

lemma card_offFullQuads (A : Finset ℕ) (u : ℕ) :
    (offFullQuads A u).card = ∑ q : Quad (Fin u), (offQuads A (leftShift q) (rightShift q)).card := by
  classical
  simp only [offFullQuads,fullQuads,filter_filter,card_eq_sum_ones,sum_filter]
  rw [Fintype.sum_prod_type,sum_comm]
  apply sum_congr rfl
  intro q hq
  simp only [offQuads,sum_filter]
  apply sum_congr rfl
  intro p hp
  congr 1
  apply propext
  tauto

lemma card_leftFullQuads (A : Finset ℕ) (u : ℕ) :
    (leftFullQuads A u).card ≤ A.card^3*u^3 := by
  classical
  let F : Quad A × Quad (Fin u) → (A × A × A) × (Fin u × Fin u × Fin u) := fun p ↦
    ((p.1.1.1,p.1.2.1,p.1.2.2),(p.2.1.1,p.2.1.2,p.2.2.1))
  have hh : (leftFullQuads A u).card ≤
      (univ : Finset ((A × A × A) × (Fin u × Fin u × Fin u))).card := by
    apply card_le_card_of_injOn F (fun _ _ ↦ mem_univ _)
    intro p hp q hq he
    have hpEq := (mem_filter.mp (mem_filter.mp hp).1).2
    have hqEq := (mem_filter.mp (mem_filter.mp hq).1).2
    have hpD := (mem_filter.mp hp).2
    have hqD := (mem_filter.mp hq).2
    simp only [F,Prod.mk.injEq] at he
    rcases he with ⟨⟨h1,h3,h4⟩,h5,h6,h7⟩
    have h2 : p.1.1.2 = q.1.1.2 := hpD.symm.trans (h1.trans hqD)
    apply Prod.ext (Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4))
    apply Prod.ext (Prod.ext h5 h6)
    apply Prod.ext h7
    apply Fin.ext
    simp only [leftShift,rightShift,h1,h2,h3,h4,h5,h6,h7] at hpEq hqEq
    omega
  simpa [Fintype.card_prod,pow_succ,mul_assoc] using hh

lemma card_rightFullQuads (A : Finset ℕ) (u : ℕ) :
    (rightFullQuads A u).card ≤ A.card^3*u^3 := by
  have hh : (rightFullQuads A u).card ≤ (leftFullQuads A u).card := by
    apply card_le_card_of_injOn (fun p : Quad A × Quad (Fin u) ↦ (p.1.swap,p.2.swap))
    · intro p hp
      have hpEq := (mem_filter.mp (mem_filter.mp hp).1).2
      have hpD := (mem_filter.mp hp).2
      apply mem_filter.mpr
      exact ⟨mem_filter.mpr ⟨mem_univ _,hpEq.symm⟩,hpD⟩
    · intro p hp q hq he
      exact Prod.ext (Prod.swap_injective (congrArg Prod.fst he))
        (Prod.swap_injective (congrArg Prod.snd he))
  exact hh.trans (card_leftFullQuads A u)

lemma card_fullQuads_bound {A : Finset ℕ} (hA : B3Aux.Good A) (u : ℕ) :
    (fullQuads A u).card ≤ 2*A.card*u^4+(4*(A.card.choose 2)+6*A.card^3)*u^3 := by
  classical
  have hsub : fullQuads A u ⊆ offFullQuads A u ∪ leftFullQuads A u ∪ rightFullQuads A u := by
    intro p hp
    by_cases h1 : p.1.1.1 = p.1.1.2
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp,h1⟩))
    by_cases h2 : p.1.2.1 = p.1.2.2
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,h2⟩)
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,h1,h2⟩))
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have hh' := card_union_le (offFullQuads A u) (leftFullQuads A u)
  have hl := card_leftFullQuads A u
  have hr := card_rightFullQuads A u
  have hoff : (offFullQuads A u).card ≤
      4*(∑ q : Quad (Fin u), (B3Aux.shiftReps A (leftShift q) (rightShift q)).card) := by
    rw [card_offFullQuads,mul_sum]
    exact sum_le_sum (fun q _ ↦ offQuads_bound hA _ _)
  have hs := sum_shiftReps_bound hA u
  nlinarith

def quadProdEquiv (α β : Type*) : Quad (α × β) ≃ Quad α × Quad β where
  toFun p := (((p.1.1.1,p.1.2.1),(p.2.1.1,p.2.2.1)),((p.1.1.2,p.1.2.2),(p.2.1.2,p.2.2.2)))
  invFun p := (((p.1.1.1,p.2.1.1),(p.1.1.2,p.2.1.2)),((p.1.2.1,p.2.2.1),(p.1.2.2,p.2.2.2)))
  left_inv _ := rfl
  right_inv _ := rfl

lemma quadEnergy_smooth_eq (A : Finset ℕ) (u : ℕ) :
    quadEnergy (fun p : A × Fin u ↦ ((p.1 : ℕ) + (p.2 : ℕ) : ℤ)) =
      ((fullQuads A u).card : ℝ) := by
  classical
  let F : Quad A × Quad (Fin u) → ℝ := fun p ↦
    if (p.1.1.1 : ℕ)+p.1.1.2+leftShift p.2 = p.1.2.1+p.1.2.2+rightShift p.2 then 1 else 0
  have hh := (quadProdEquiv A (Fin u)).sum_comp F
  have hl : quadEnergy (fun p : A × Fin u ↦ ((p.1 : ℕ) + (p.2 : ℕ) : ℤ)) =
      ∑ p : Quad (A × Fin u), F (quadProdEquiv A (Fin u) p) := by
    simp only [quadEnergy,Fintype.sum_prod_type]
    iterate 8 (apply sum_congr rfl; intro x hx)
    dsimp only [F,quadProdEquiv,Equiv.coe_fn_mk,leftShift,rightShift]
    congr 1
    apply propext
    omega
  rw [hl,hh]
  simp only [fullQuads,card_eq_sum_ones,sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,F]

lemma smooth_energy_bound {A : Finset ℕ} (hA : B3Aux.Good A) (u : ℕ) :
    quadEnergy (fun p : A × Fin u ↦ ((p.1 : ℕ) + (p.2 : ℕ) : ℤ)) ≤
      2*(A.card : ℝ)*(u : ℝ)^4+(4*((A.card.choose 2) : ℝ)+6*(A.card : ℝ)^3)*(u : ℝ)^3 := by
  rw [quadEnergy_smooth_eq]
  exact_mod_cast card_fullQuads_bound hA u

lemma moment_cauchy_bound {A : Finset ℕ} (hA : B3Aux.Good A) (N u : ℕ) (hu : 0 < u)
    (hAN : A ⊆ Icc 1 N) :
    ((A.card : ℝ)*(u : ℝ))^4 ≤ ((736/375)*(N+u : ℝ)+2) *
      (2*(A.card : ℝ)*(u : ℝ)^4+(4*((A.card.choose 2) : ℝ)+6*(A.card : ℝ)^3)*(u : ℝ)^3) := by
  let b : A × Fin u → ℤ := fun p ↦ (p.1 : ℕ) + (p.2 : ℕ)
  have hb (i j : A × Fin u) : b i-b j ∈ Icc (-(N+u : ℤ)) (N+u : ℤ) := by
    have hi := (mem_Icc.mp (hAN i.1.property)).2
    have hj := (mem_Icc.mp (hAN j.1.property)).2
    have hui := i.2.isLt
    have huj := j.2.isLt
    simp only [b,mem_Icc]
    omega
  have hh := difference_energy_lower b (N+u) (by omega) (by simpa only [Nat.cast_add] using hb)
  rw [difference_energy_eq b _ (by simpa only [Nat.cast_add] using hb)] at hh
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul,Nat.cast_add] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left (smooth_energy_bound hA u) (by positivity))

end MomentBound


/- A global-moment improvement on the asymptotic B3 upper bound. -/
open Finset Filter

lemma f_moment_cauchy_bound (N u : ℕ) (hu : 0 < u) :
    ((f N 3 : ℝ)*(u : ℝ))^4 ≤ ((736/375)*(N+u : ℝ)+2) *
      (2*(f N 3 : ℝ)*(u : ℝ)^4+(4*(((f N 3).choose 2) : ℝ)+6*(f N 3 : ℝ)^3)*(u : ℝ)^3) := by
  classical
  unfold f
  apply Finset.sup_induction (p := fun n : ℕ ↦
    ((n : ℝ)*(u : ℝ))^4 ≤ ((736/375)*(N+u : ℝ)+2) *
      (2*(n : ℝ)*(u : ℝ)^4+(4*((n.choose 2) : ℝ)+6*(n : ℝ)^3)*(u : ℝ)^3))
  · norm_num
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa [sup_eq_right.mpr h] using hb
    · simpa [sup_eq_left.mpr h] using ha
  · intro A hA
    rcases mem_filter.mp hA with ⟨hsub,hA⟩
    exact MomentBound.moment_cauchy_bound hA N u hu (mem_powerset.mp hsub)

lemma f_moment_bound (N k : ℕ) (hk : 0 < k) :
    (k : ℝ)*(f N 3 : ℝ)^3 ≤ ((2*k+10)*(736/375 : ℝ))*N +
      ((2*k+10)*((736/375 : ℝ)*k+2))*(f N 3 : ℝ)^2 := by
  by_cases hn0 : f N 3 = 0
  · simp [hn0]
    positivity
  let n : ℝ := f N 3
  let m : ℝ := (f N 3).choose 2
  let u : ℝ := k*n^2
  let D : ℝ := 736/375
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnpos : 0 < n := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : 0 < u := by dsimp [u]; positivity
  have hmc : m ≤ n^3 := by
    have hh : m ≤ n^2 := by dsimp [m,n]; exact_mod_cast Nat.choose_le_pow (f N 3) 2
    exact hh.trans (pow_le_pow_right₀ hn (by omega))
  have hraw : (n*u)^4 ≤ (D*(N+u)+2)*(2*n*u^4+(4*m+6*n^3)*u^3) := by
    have hu' : 0 < k*(f N 3)^2 := Nat.mul_pos hk (pow_pos (Nat.pos_of_ne_zero hn0) 2)
    simpa [n,m,u,D,Nat.cast_mul,Nat.cast_pow] using f_moment_cauchy_bound N (k*(f N 3)^2) hu'
  have hmid : 2*n*u^4+(4*m+6*n^3)*u^3 ≤ (2*k+10)*n^3*u^3 := by
    calc
      _ ≤ 2*n*u^4+10*n^3*u^3 := by nlinarith [mul_le_mul_of_nonneg_right hmc (pow_pos hu 3).le]
      _ = _ := by dsimp [u]; ring
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hmid (by dsimp [D]; positivity))
  have hmain : (k : ℝ)*n^3 ≤ (D*(N+u)+2)*(2*k+10) := by
    apply (mul_le_mul_iff_right₀ (mul_pos (pow_pos hnpos 3) (pow_pos hu 3))).mp
    calc
      _ = (n*u)^4 := by dsimp [u]; ring
      _ ≤ _ := hraw'
      _ = _ := by ring
  have hconst : 2 ≤ 2*n^2 := by nlinarith
  have hfin : D*(N+u)+2 ≤ D*N+(D*k+2)*n^2 := by dsimp [u,D]; nlinarith
  have hh := hmain.trans (mul_le_mul_of_nonneg_right hfin (by positivity))
  change (k : ℝ)*n^3 ≤ _
  dsimp [D] at hh
  nlinarith only [hh]

lemma f_cube_ratio_eventually_lt_moment_bound (c : ℝ) (hc : (1472 : ℝ)/375 < c) :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < c := by
  let D : ℝ := 736/375
  have hc' : 2*D < c := by dsimp [D]; linarith
  obtain ⟨k,hk⟩ := exists_nat_gt (10*D/(c-2*D))
  have hkpos : (0 : ℝ) < k := (div_pos (by dsimp [D]; norm_num) (sub_pos.mpr hc')).trans hk
  have hk' : 0 < k := by exact_mod_cast hkpos
  let a : ℝ := (2*k+10)*D
  let b : ℝ := (2*k+10)*(D*k+2)
  have hac : a/k < c := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh := (div_lt_iff₀ (sub_pos.mpr hc')).mp hk
    dsimp [a]
    nlinarith
  have ht : Tendsto (fun N : ℕ ↦ a/k+(b/k)*((f N 3 : ℝ)^2/N)) atTop (nhds (a/k)) := by
    simpa using (tendsto_const_nhds (x := a/(k : ℝ))).add
      (f_square_ratio_tendsto_zero.const_mul (b/k))
  filter_upwards [eventually_ge_atTop 1,ht.eventually_lt_const hac] with N hN hH
  apply lt_of_le_of_lt _ hH
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNp).mpr
  have he : (a/k+(b/k)*((f N 3 : ℝ)^2/N))*N = (a*N+b*(f N 3 : ℝ)^2)/k := by
    field_simp
  rw [he]
  apply (le_div_iff₀ hkpos).mpr
  simpa [a,b,D,mul_comm] using f_moment_bound N k hk'




/- Positive Fourier modes yield a stronger global energy inequality. -/
open Finset Filter
namespace CosineBound

lemma sin_half_step (x t : ℝ) :
    Real.sin (x+t/2) - Real.sin (x-t/2) = 2*Real.sin (t/2)*Real.cos x := by
  rw [Real.sin_add,Real.sin_sub]
  ring

lemma cos_grid_identity (n : ℕ) (t : ℝ) :
    Real.sin (t/2) * (∑ d ∈ Icc (-(n : ℤ)) n, Real.cos ((d : ℝ)*t)) =
      Real.sin (((n : ℝ)+1/2)*t) := by
  induction n with
  | zero => simp; congr 1; ring
  | succ n ih =>
    simp only [Nat.cast_add,Nat.cast_one]
    rw [MomentBound.sum_symmetric_succ]
    simp only [Int.cast_neg,Int.cast_add,Int.cast_natCast,Int.cast_one,neg_mul,Real.cos_neg]
    have hh := sin_half_step (((n : ℝ)+1)*t) t
    have he1 : ((n : ℝ)+1)*t+t/2 = ((n : ℝ)+1+1/2)*t := by ring
    have he2 : ((n : ℝ)+1)*t-t/2 = ((n : ℝ)+1/2)*t := by ring
    rw [he1,he2] at hh
    nlinarith only [ih,hh]

noncomputable def cosGrid (n : ℕ) (θ : ℝ) : ℝ :=
  (∑ d ∈ Icc (-(n : ℤ)) n, Real.cos (θ*((d : ℝ)/n))) / n

lemma cos_grid_tendsto (θ : ℝ) : Tendsto (fun n : ℕ ↦ cosGrid n θ) atTop (nhds (2*Real.sinc θ)) := by
  by_cases hθ : θ = 0
  · subst θ
    have he (n : ℕ) : cosGrid n 0 = (2*(n : ℝ)+1)/n := by
      have hh := MomentBound.sum_symmetric_pow_zero n
      simpa [cosGrid] using congrArg (fun x : ℝ ↦ x/n) hh
    simp_rw [he]
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).const_add 2
    simp only [Real.sinc_zero,mul_one,add_zero] at *
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  · let h : ℕ → ℝ := fun n ↦ θ/(2*(n : ℝ))
    have ht : Tendsto h atTop (nhds 0) := by
      simpa only [h,div_div] using tendsto_const_div_atTop_nhds_zero_nat (θ/2)
    have hsinc : Tendsto (fun n ↦ Real.sinc (h n)) atTop (nhds 1) := by
      simpa only [Function.comp_def,Real.sinc_zero] using Real.continuous_sinc.continuousAt.tendsto.comp ht
    have hsin : Tendsto (fun n ↦ Real.sin (θ+h n)) atTop (nhds (Real.sin θ)) := by
      simpa only [Function.comp_def,add_zero] using Real.continuous_sin.continuousAt.tendsto.comp (ht.const_add θ)
    have hden : θ/2 ≠ 0 := div_ne_zero hθ (by norm_num)
    have hr := hsin.div (hsinc.const_mul (θ/2)) (by simpa using hden)
    have hval : Real.sin θ / ((θ/2)*1) = 2*Real.sinc θ := by
      rw [Real.sinc_of_ne_zero hθ]
      field_simp
    rw [hval] at hr
    apply hr.congr'
    filter_upwards [eventually_ge_atTop 1,hsinc.eventually_ne (by norm_num : (1 : ℝ) ≠ 0)] with n hn hs
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    have hh0 : h n ≠ 0 := by dsimp [h]; exact div_ne_zero hθ (mul_ne_zero (by norm_num) hn0)
    have hSn : Real.sin (h n) ≠ 0 := by
      rw [Real.sinc_of_ne_zero hh0] at hs
      exact (div_ne_zero_iff.mp hs).1
    have hi := cos_grid_identity n (θ/n)
    have hf (d : ℤ) : (d : ℝ)*(θ/n) = θ*((d : ℝ)/n) := by ring
    simp_rw [hf] at hi
    have he1 : θ/(n : ℝ)/2 = h n := by dsimp [h]; ring
    have he2 : ((n : ℝ)+1/2)*(θ/n) = θ+h n := by dsimp [h]; field_simp
    rw [he1,he2] at hi
    change Real.sin (θ+h n) / ((θ/2)*Real.sinc (h n)) = _
    rw [← hi,Real.sinc_of_ne_zero hh0]
    dsimp only [h] at hSn
    dsimp only [cosGrid,h]
    field_simp [hSn]

lemma cos_pair_sum_nonneg {ι : Type*} [Fintype ι] (b : ι → ℝ) (θ : ℝ) :
    0 ≤ ∑ i, ∑ j, Real.cos (θ*(b i-b j)) := by
  have he (i j : ι) : θ*(b i-b j) = θ*b i-θ*b j := by ring
  simp only [he,Real.cos_sub,sum_add_distrib,← mul_sum,← sum_mul]
  nlinarith only [sq_nonneg (∑ i,Real.cos (θ*b i)),sq_nonneg (∑ i,Real.sin (θ*b i))]

noncomputable def grid (w : ℝ → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ Icc (-(n : ℤ)) n, w ((d : ℝ)/n))/n

lemma grid_add (w v : ℝ → ℝ) (n : ℕ) :
    grid (fun x ↦ w x+v x) n = grid w n+grid v n := by simp [grid,sum_add_distrib,add_div]

lemma grid_const_mul (a : ℝ) (w : ℝ → ℝ) (n : ℕ) :
    grid (fun x ↦ a*w x) n = a*grid w n := by simp [grid,← mul_sum,mul_div_assoc]

lemma grid_sum {ι : Type*} (T : Finset ι) (w : ι → ℝ → ℝ) (n : ℕ) :
    grid (fun x ↦ ∑ i ∈ T, w i x) n = ∑ i ∈ T, grid (w i) n := by
  simp only [grid]
  rw [sum_comm,sum_div]

lemma grid_one_tendsto : Tendsto (fun n : ℕ ↦ grid (fun _ ↦ 1) n) atTop (nhds 2) := by
  simpa [grid,cosGrid] using cos_grid_tendsto 0

lemma grid_cos_mul_tendsto (a b : ℝ) :
    Tendsto (fun n : ℕ ↦ grid (fun x ↦ Real.cos (a*x)*Real.cos (b*x)) n)
      atTop (nhds (Real.sinc (a-b)+Real.sinc (a+b))) := by
  have he : (fun x ↦ Real.cos (a*x)*Real.cos (b*x)) =
      (fun x ↦ (1/2)*(Real.cos ((a-b)*x)+Real.cos ((a+b)*x))) := by
    funext x
    simp only [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  simp only [he,grid_const_mul,grid_add]
  have hh := ((cos_grid_tendsto (a-b)).add (cos_grid_tendsto (a+b))).const_mul (1/2)
  convert hh using 1
  congr 1
  ring

noncomputable def cosineWeight {ι : Type*} (T : Finset ι) (c θ : ι → ℝ) (x : ℝ) : ℝ :=
  1+∑ i ∈ T, c i*Real.cos (θ i*x)

lemma cosineWeight_pair_sum {ι τ : Type*} [Fintype τ] (T : Finset ι) (c θ : ι → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) (b : τ → ℝ) :
    (Fintype.card τ : ℝ)^2 ≤ ∑ i, ∑ j, cosineWeight T c θ (b i-b j) := by
  have hh : 0 ≤ ∑ k ∈ T, c k*(∑ i, ∑ j, Real.cos (θ k*(b i-b j))) :=
    sum_nonneg (fun k hk ↦ mul_nonneg (hc k hk) (cos_pair_sum_nonneg b (θ k)))
  have he : (∑ i, ∑ j, cosineWeight T c θ (b i-b j)) = (Fintype.card τ : ℝ)^2 +
      ∑ k ∈ T, c k*(∑ i, ∑ j, Real.cos (θ k*(b i-b j))) := by
    simp only [cosineWeight,sum_add_distrib,sum_const,nsmul_eq_mul,card_univ,mul_one]
    simp_rw [sum_comm (s := (univ : Finset τ)) (t := T)]
    simp only [← mul_sum]
    ring
  rw [he]
  linarith

lemma cosineWeight_grid_tendsto {ι : Type*} (T : Finset ι) (c θ : ι → ℝ) :
    Tendsto (fun n : ℕ ↦ grid (fun x ↦ (cosineWeight T c θ x)^2) n) atTop
      (nhds (2+4*(∑ i ∈ T, c i*Real.sinc (θ i))+
        ∑ i ∈ T, ∑ j ∈ T, c i*c j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)))) := by
  have he : (fun x ↦ (cosineWeight T c θ x)^2) = (fun x ↦
      (1+2*(∑ i ∈ T, c i*Real.cos (θ i*x)))+
        ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x))) := by
    funext x
    dsimp only [cosineWeight]
    rw [add_sq]
    have hp : (∑ i ∈ T, c i*Real.cos (θ i*x))^2 =
        ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)) := by
      rw [pow_two,mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    rw [hp]
    ring
  simp only [he,grid_add,grid_const_mul,grid_sum]
  have h1 := (tendsto_finset_sum T (fun i hi ↦ (cos_grid_tendsto (θ i)).const_mul (c i))).const_mul 2
  have h2 := tendsto_finset_sum T (fun i hi ↦ tendsto_finset_sum T
    (fun j hj ↦ (grid_cos_mul_tendsto (θ i) (θ j)).const_mul (c i*c j)))
  have hh := (grid_one_tendsto.add h1).add h2
  have hsum : (∑ i ∈ T, c i*(2*Real.sinc (θ i))) = 2*∑ i ∈ T, c i*Real.sinc (θ i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum] at hh
  convert hh using 1
  congr 1
  ring

noncomputable def freq (j : ℕ) : ℝ := (4*(j : ℝ)+3)*Real.pi/2
noncomputable def coeff (j : ℕ) : ℝ := 4/((4*(j : ℝ)+3)*Real.pi)

lemma freq_pos (j : ℕ) : 0 < freq j := by dsimp [freq]; positivity
lemma coeff_pos (j : ℕ) : 0 < coeff j := by dsimp [coeff]; positivity

lemma sinc_freq (j : ℕ) : Real.sinc (freq j) = -(coeff j)/2 := by
  rw [Real.sinc_of_ne_zero (freq_pos j).ne']
  have he : freq j = (Real.pi/2+Real.pi) + (j : ℝ)*(2*Real.pi) := by dsimp [freq]; ring
  rw [he,Real.sin_add_nat_mul_two_pi,Real.sin_add_pi,Real.sin_pi_div_two]
  dsimp [coeff]
  field_simp; ring

lemma sinc_freq_sub (i j : ℕ) : Real.sinc (freq i-freq j) = if i=j then 1 else 0 := by
  by_cases hij : i=j
  · simp [hij]
  · have hne : freq i-freq j ≠ 0 := by
      have hp := Real.pi_pos
      dsimp only [freq]
      intro he
      have he' : (i : ℝ) = j := by nlinarith
      exact hij (Nat.cast_injective he')
    rw [if_neg hij,Real.sinc_of_ne_zero hne]
    have he : freq i-freq j = ((2*(i : ℤ)-2*(j : ℤ) : ℤ) : ℝ)*Real.pi := by
      dsimp [freq]
      push_cast
      ring
    rw [he,Real.sin_int_mul_pi,zero_div]

lemma sinc_freq_add (i j : ℕ) : Real.sinc (freq i+freq j) = 0 := by
  rw [Real.sinc_of_ne_zero (add_pos (freq_pos i) (freq_pos j)).ne']
  have he : freq i+freq j = ((2*i+2*j+3 : ℕ) : ℝ)*Real.pi := by
    dsimp [freq]
    push_cast
    ring
  rw [he,Real.sin_nat_mul_pi,zero_div]

lemma special_weight_grid_tendsto (T : Finset ℕ) :
    Tendsto (fun n : ℕ ↦ grid (fun x ↦ (cosineWeight T coeff freq x)^2) n) atTop
      (nhds (2-∑ i ∈ T, (coeff i)^2)) := by
  have hh := cosineWeight_grid_tendsto T coeff freq
  simp only [sinc_freq,sinc_freq_sub,sinc_freq_add,add_zero] at hh
  have he : (∑ i ∈ T, ∑ j ∈ T, coeff i*coeff j*(if i=j then 1 else 0)) = ∑ i ∈ T, (coeff i)^2 := by
    apply sum_congr rfl
    intro i hi
    simp only [mul_ite,mul_one,mul_zero,sum_ite_eq,if_pos hi,pow_two]
  rw [he] at hh
  convert hh using 1
  congr 1
  have he' : (∑ i ∈ T, coeff i*(-coeff i/2)) = -(1/2)*(∑ i ∈ T, (coeff i)^2) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [he']
  ring

end CosineBound


/- A finite positive-Fourier-mode upper bound for B3 sets. -/
open Finset Filter
namespace CosineBound

lemma cosine_energy_lower {ι : Type*} [Fintype ι] (b : ι → ℤ) (L : ℕ)
    (hb : ∀ i j, b i-b j ∈ Icc (-(L : ℤ)) L) (T : Finset ℕ) :
    (Fintype.card ι : ℝ)^4 ≤ MomentBound.quadEnergy b *
      (∑ d ∈ Icc (-(L : ℤ)) L, (cosineWeight T coeff freq ((d : ℝ)/L))^2) := by
  have hh := cosineWeight_pair_sum T coeff freq (fun i _ ↦ (coeff_pos i).le)
    (fun i ↦ (b i : ℝ)/L)
  have he : (∑ d ∈ Icc (-(L : ℤ)) L,
      MomentBound.differenceCount b d * cosineWeight T coeff freq ((d : ℝ)/L)) =
      ∑ i, ∑ j, cosineWeight T coeff freq ((b i : ℝ)/L-(b j : ℝ)/L) := by
    rw [MomentBound.sum_differenceCount_mul b _ hb]
    simp only [Int.cast_sub,sub_div]
  rw [← he] at hh
  have hs := pow_le_pow_left₀ (sq_nonneg (Fintype.card ι : ℝ)) hh 2
  have hc := sum_mul_sq_le_sq_mul_sq (Icc (-(L : ℤ)) L) (MomentBound.differenceCount b)
    (fun d ↦ cosineWeight T coeff freq ((d : ℝ)/L))
  rw [MomentBound.difference_energy_eq b _ hb] at hc
  have hp : ((Fintype.card ι : ℝ)^2)^2 = (Fintype.card ι : ℝ)^4 := by ring
  rw [hp] at hs
  exact hs.trans hc

lemma cosine_cauchy_bound {A : Finset ℕ} (hA : B3Aux.Good A) (N u : ℕ) (T : Finset ℕ) (C : ℝ)
    (hu : 0 < u) (hAN : A ⊆ Icc 1 N)
    (hgrid : grid (fun x ↦ (cosineWeight T coeff freq x)^2) (N+u) ≤ C) :
    ((A.card : ℝ)*(u : ℝ))^4 ≤ C*(N+u : ℝ) *
      (2*(A.card : ℝ)*(u : ℝ)^4+(4*((A.card.choose 2) : ℝ)+6*(A.card : ℝ)^3)*(u : ℝ)^3) := by
  let b : A × Fin u → ℤ := fun p ↦ (p.1 : ℕ) + (p.2 : ℕ)
  have hb (i j : A × Fin u) : b i-b j ∈ Icc (-(N+u : ℤ)) (N+u : ℤ) := by
    have hi := (mem_Icc.mp (hAN i.1.property)).2
    have hj := (mem_Icc.mp (hAN j.1.property)).2
    have hui := i.2.isLt
    have huj := j.2.isLt
    simp only [b,mem_Icc]
    omega
  have hh := cosine_energy_lower b (N+u) (by simpa only [Nat.cast_add] using hb) T
  have hNp : (0 : ℝ) < N+u := by exact_mod_cast (show 0 < N+u by omega)
  have hg := (div_le_iff₀ (by exact_mod_cast (show 0 < N+u by omega) : (0 : ℝ) < (N+u : ℕ))).mp hgrid
  change (∑ d ∈ Icc (-((N+u : ℕ) : ℤ)) (N+u : ℕ),
    (cosineWeight T coeff freq ((d : ℝ)/(N+u : ℕ)))^2) ≤ C*((N+u : ℕ) : ℝ) at hg
  have hdenpos : 0 ≤ C*((N+u : ℕ) : ℝ) := le_trans (by positivity) hg
  have henergypos : 0 ≤ MomentBound.quadEnergy b := by unfold MomentBound.quadEnergy; positivity
  have h1 := hh.trans (mul_le_mul_of_nonneg_left hg henergypos)
  have h2 := mul_le_mul_of_nonneg_left (MomentBound.smooth_energy_bound hA u) hdenpos
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul,Nat.cast_add] at h1 h2
  exact h1.trans (by simpa only [mul_comm] using h2)

noncomputable def denominatorLimit (T : Finset ℕ) : ℝ := 2-∑ i ∈ T, (coeff i)^2

lemma denominatorLimit_nonneg (T : Finset ℕ) : 0 ≤ denominatorLimit T := by
  apply ge_of_tendsto' (special_weight_grid_tendsto T)
  intro n
  unfold grid
  positivity

lemma sixteen_modes_strict : 2*denominatorLimit (range 16) < (7 : ℝ)/2 := by
  have hs : (31 : ℝ)/200 < ∑ j ∈ range 16, 1/(4*(j : ℝ)+3)^2 := by
    norm_num [sum_range_succ]
  have he : (∑ j ∈ range 16, (coeff j)^2) = (16/Real.pi^2)*∑ j ∈ range 16, 1/(4*(j : ℝ)+3)^2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    dsimp [coeff]
    field_simp
    norm_num
  have hp2 : Real.pi^2 < (248 : ℝ)/25 := by nlinarith [Real.pi_pos,Real.pi_lt_d4]
  have hs' : (1 : ℝ)/4 < (∑ j ∈ range 16, (coeff j)^2) := by
    rw [he,div_mul_eq_mul_div]
    apply (lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  dsimp [denominatorLimit]
  linarith

end CosineBound

lemma f_cosine_cauchy_bound (N u : ℕ) (hu : 0 < u) (T : Finset ℕ) (C : ℝ)
    (hgrid : CosineBound.grid (fun x ↦ (CosineBound.cosineWeight T CosineBound.coeff CosineBound.freq x)^2)
      (N+u) ≤ C) :
    ((f N 3 : ℝ)*(u : ℝ))^4 ≤ C*(N+u : ℝ) *
      (2*(f N 3 : ℝ)*(u : ℝ)^4+(4*(((f N 3).choose 2) : ℝ)+6*(f N 3 : ℝ)^3)*(u : ℝ)^3) := by
  classical
  unfold f
  apply Finset.sup_induction (p := fun n : ℕ ↦
    ((n : ℝ)*(u : ℝ))^4 ≤ C*(N+u : ℝ) *
      (2*(n : ℝ)*(u : ℝ)^4+(4*((n.choose 2) : ℝ)+6*(n : ℝ)^3)*(u : ℝ)^3))
  · norm_num
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa [sup_eq_right.mpr h] using hb
    · simpa [sup_eq_left.mpr h] using ha
  · intro A hA
    rcases mem_filter.mp hA with ⟨hsub,hA⟩
    exact CosineBound.cosine_cauchy_bound hA N u T C hu (mem_powerset.mp hsub) hgrid

lemma f_cosine_bound (N k : ℕ) (hk : 0 < k) (T : Finset ℕ) (C : ℝ) (hC : 0 ≤ C)
    (hgrid : CosineBound.grid (fun x ↦ (CosineBound.cosineWeight T CosineBound.coeff CosineBound.freq x)^2)
      (N+k*(f N 3)^2) ≤ C) :
    (k : ℝ)*(f N 3 : ℝ)^3 ≤ (2*k+10)*C*N + ((2*k+10)*C*k)*(f N 3 : ℝ)^2 := by
  by_cases hn0 : f N 3 = 0
  · simp [hn0]
    positivity
  let n : ℝ := f N 3
  let m : ℝ := (f N 3).choose 2
  let u : ℝ := k*n^2
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnpos : 0 < n := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : 0 < u := by dsimp [u]; positivity
  have hmc : m ≤ n^3 := by
    have hh : m ≤ n^2 := by dsimp [m,n]; exact_mod_cast Nat.choose_le_pow (f N 3) 2
    exact hh.trans (pow_le_pow_right₀ hn (by omega))
  have hraw : (n*u)^4 ≤ (C*(N+u))*(2*n*u^4+(4*m+6*n^3)*u^3) := by
    have hu' : 0 < k*(f N 3)^2 := Nat.mul_pos hk (pow_pos (Nat.pos_of_ne_zero hn0) 2)
    simpa [n,m,u,Nat.cast_mul,Nat.cast_pow] using f_cosine_cauchy_bound N (k*(f N 3)^2) hu' T C hgrid
  have hmid : 2*n*u^4+(4*m+6*n^3)*u^3 ≤ (2*k+10)*n^3*u^3 := by
    calc
      _ ≤ 2*n*u^4+10*n^3*u^3 := by nlinarith [mul_le_mul_of_nonneg_right hmc (pow_pos hu 3).le]
      _ = _ := by dsimp [u]; ring
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hmid (by positivity))
  have hmain : (k : ℝ)*n^3 ≤ C*(N+u)*(2*k+10) := by
    apply (mul_le_mul_iff_right₀ (mul_pos (pow_pos hnpos 3) (pow_pos hu 3))).mp
    calc
      _ = (n*u)^4 := by dsimp [u]; ring
      _ ≤ _ := hraw'
      _ = _ := by ring
  dsimp [u] at hmain
  change (k : ℝ)*n^3 ≤ _
  nlinarith only [hmain]

lemma f_cube_ratio_eventually_lt_cosine_bound (T : Finset ℕ) (c : ℝ)
    (hc : 2*CosineBound.denominatorLimit T < c) :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < c := by
  let D := CosineBound.denominatorLimit T
  let C : ℝ := (D+c/2)/2
  have hD0 : 0 ≤ D := CosineBound.denominatorLimit_nonneg T
  have hDC : D < C := by dsimp [C,D]; linarith
  have hCpos : 0 < C := lt_of_le_of_lt hD0 hDC
  have hCc : 2*C < c := by dsimp [C,D]; linarith
  obtain ⟨L,hL⟩ := (eventually_atTop.mp
    ((CosineBound.special_weight_grid_tendsto T).eventually_lt_const hDC))
  obtain ⟨k,hk⟩ := exists_nat_gt (10*C/(c-2*C))
  have hkpos : (0 : ℝ) < k := (div_pos (mul_pos (by norm_num) hCpos) (sub_pos.mpr hCc)).trans hk
  have hk' : 0 < k := by exact_mod_cast hkpos
  let a : ℝ := (2*k+10)*C
  let b : ℝ := (2*k+10)*C*k
  have hac : a/k < c := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh := (div_lt_iff₀ (sub_pos.mpr hCc)).mp hk
    dsimp [a]
    nlinarith
  have ht : Tendsto (fun N : ℕ ↦ a/k+(b/k)*((f N 3 : ℝ)^2/N)) atTop (nhds (a/k)) := by
    simpa using (tendsto_const_nhds (x := a/(k : ℝ))).add
      (f_square_ratio_tendsto_zero.const_mul (b/k))
  filter_upwards [eventually_ge_atTop (max L 1),ht.eventually_lt_const hac] with N hN hH
  apply lt_of_le_of_lt _ hH
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNp).mpr
  have he : (a/k+(b/k)*((f N 3 : ℝ)^2/N))*N = (a*N+b*(f N 3 : ℝ)^2)/k := by field_simp
  rw [he]
  apply (le_div_iff₀ hkpos).mpr
  have hgrid := (hL (N+k*(f N 3)^2) (by omega)).le
  simpa [a,b,mul_comm] using f_cosine_bound N k hk' T C hCpos.le hgrid

lemma f_cube_ratio_eventually_lt_seven_halves :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < (7 : ℝ)/2 :=
  f_cube_ratio_eventually_lt_cosine_bound (range 16) (7/2) CosineBound.sixteen_modes_strict




/- The exact covering and mass-balance constraints behind pair-sum shift multiplicities. -/
open Finset
namespace ShiftRigidity
open B3Aux

lemma left_cover {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    ∃ L : Finset ℕ, L ⊆ A ∧ L.card = 2*(shiftReps A i j).card ∧
      (∑ a ∈ L, a) = ∑ r ∈ shiftReps A i j, r.1 := by
  classical
  let R := shiftReps A i j
  have hR (r : R) : r.val.1 ∈ pairSums A ∧ r.val.2 ∈ pairSums A ∧
      r.val.1+i = r.val.2+j := shiftReps_mem.mp r.property
  have hex (r : R) : ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ r.val.1 = a+b :=
    mem_pairSums_iff.mp (hR r).1
  choose a ha b hb hab hs using hex
  let P (r : R) : Finset ℕ := {a r,b r}
  have hPc (r : R) : (P r).card = 2 := by simp [P,hab r]
  have hPA (r : R) : P r ⊆ A := insert_subset_iff.mpr ⟨ha r,singleton_subset_iff.mpr (hb r)⟩
  have hPs (r : R) {x : ℕ} (hx : x ∈ P r) : ∃ y ∈ A, r.val.1 = x+y := by
    simp only [P,mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact ⟨b r,hb r,hs r⟩
    · exact ⟨a r,ha r,by simpa only [add_comm] using hs r⟩
  have hdis : (↑(univ : Finset R) : Set R).PairwiseDisjoint P := by
    intro r hr r' hr' hne
    apply disjoint_left.mpr
    intro x hx hx'
    obtain ⟨y,hy,hxy⟩ := hPs r hx
    obtain ⟨y',hy',hxy'⟩ := hPs r' hx'
    have her := (hR r).2.2
    have her' := (hR r').2.2
    have hyy' : y=y' := other_summand_unique hA hNo (hPA r hx) hy hy'
      (hR r).2.1 (hR r').2.1 (by omega) (by omega)
    apply hne
    apply Subtype.ext
    apply Prod.ext <;> omega
  refine ⟨univ.biUnion P,?_,?_,?_⟩
  · intro x hx
    obtain ⟨r,hr,hxr⟩ := mem_biUnion.mp hx
    exact hPA r hxr
  · rw [card_biUnion hdis]
    simp_rw [hPc]
    simp [R,mul_comm]
  · rw [sum_biUnion hdis]
    have he (r : R) : (∑ x ∈ P r, x) = r.val.1 := by simp [P,hab r,hs r]
    simp_rw [he]
    exact sum_coe_sort _ _

lemma swap_mem {A : Finset ℕ} {i j : ℕ} {r : ℕ × ℕ} :
    r.swap ∈ shiftReps A j i ↔ r ∈ shiftReps A i j := by
  simp only [shiftReps_mem,Prod.fst_swap,Prod.snd_swap]
  constructor <;> rintro ⟨h1,h2,h3⟩ <;> exact ⟨h2,h1,h3.symm⟩

lemma card_swap (A : Finset ℕ) (i j : ℕ) :
    (shiftReps A i j).card = (shiftReps A j i).card := by
  apply card_bij (fun r _ ↦ r.swap)
  · intro r hr
    exact swap_mem.mpr hr
  · intro r hr s hs he
    exact Prod.swap_injective he
  · intro r hr
    exact ⟨r.swap,swap_mem.mpr hr,Prod.swap_swap r⟩

lemma sum_swap (A : Finset ℕ) (i j : ℕ) :
    (∑ r ∈ shiftReps A i j, r.2) = ∑ r ∈ shiftReps A j i, r.1 := by
  apply sum_bij (fun r _ ↦ r.swap)
  · intro r hr
    exact swap_mem.mpr hr
  · intro r hr s hs he
    exact Prod.swap_injective he
  · intro r hr
    exact ⟨r.swap,swap_mem.mpr hr,Prod.swap_swap r⟩
  · intro r hr
    rfl

/-- Each side of a nonexceptional shift covers exactly twice its multiplicity many
vertices of the original set. The sums of the covers retain the exact shift displacement. -/
lemma shift_covers {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    ∃ L R : Finset ℕ, L ⊆ A ∧ R ⊆ A ∧
      L.card = 2*(shiftReps A i j).card ∧ R.card = 2*(shiftReps A i j).card ∧
      (∑ a ∈ L, a)+i*(shiftReps A i j).card =
        (∑ a ∈ R, a)+j*(shiftReps A i j).card := by
  obtain ⟨L,hLA,hLc,hLs⟩ := left_cover hA i j hNo
  obtain ⟨R,hRA,hRc,hRs⟩ := left_cover hA j i (fun a ha b hb he ↦ hNo b hb a ha he.symm)
  rw [← card_swap A i j] at hRc
  refine ⟨L,R,hLA,hRA,hLc,hRc,?_⟩
  rw [hLs,hRs,← sum_swap A i j]
  have he := sum_congr (s₁ := shiftReps A i j) rfl
    (fun r hr ↦ (shiftReps_mem.mp hr).2.2)
  simpa only [sum_add_distrib,sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm] using he

/-- Exact complement balance: all displacement is accounted for by uncovered vertices. -/
lemma complement_balance {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    ∃ U V : Finset ℕ, U ⊆ A ∧ V ⊆ A ∧
      U.card + 2*(shiftReps A i j).card = A.card ∧
      V.card + 2*(shiftReps A i j).card = A.card ∧
      (∑ a ∈ U, a)+j*(shiftReps A i j).card =
        (∑ a ∈ V, a)+i*(shiftReps A i j).card := by
  obtain ⟨L,R,hLA,hRA,hLc,hRc,hs⟩ := shift_covers hA i j hNo
  refine ⟨A\L,A\R,sdiff_subset,sdiff_subset,?_,?_,?_⟩
  · rw [← hLc,card_sdiff_add_card_eq_card hLA]
  · rw [← hRc,card_sdiff_add_card_eq_card hRA]
  · have hLs := sum_sdiff (f := fun a : ℕ ↦ a) hLA
    have hRs := sum_sdiff (f := fun a : ℕ ↦ a) hRA
    dsimp only at hLs hRs
    omega

lemma strict_card_bound {A : Finset ℕ} (hA : Good A) (hAn : A.Nonempty) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    2*(shiftReps A i j).card < A.card := by
  obtain ⟨U,V,hUA,hVA,hUc,hVc,hs⟩ := complement_balance hA i j hNo
  have hAn0 : 0 < A.card := card_pos.mpr hAn
  by_contra hn
  have hU : U=∅ := card_eq_zero.mp (by omega)
  have hV : V=∅ := card_eq_zero.mp (by omega)
  simp only [hU,hV,sum_empty,zero_add] at hs
  have hrpos : 0 < (shiftReps A i j).card := by omega
  have hij : j=i := (Nat.mul_right_cancel hrpos hs)
  obtain ⟨a,ha⟩ := hAn
  exact hNo a ha a ha (by rw [hij])

/-- A diameter-sensitive improvement of the pointwise multiplicity bound. -/
lemma diameter_bound {A : Finset ℕ} (hA : Good A) (N i j : ℕ)
    (hAN : A ⊆ Icc 0 N) (hij : i ≤ j)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    (2*N+(j-i))*(shiftReps A i j).card ≤ N*A.card := by
  obtain ⟨U,V,hUA,hVA,hUc,hVc,hs⟩ := complement_balance hA i j hNo
  have hv : (∑ a ∈ V, a) ≤ V.card*N := by
    simpa only [nsmul_eq_mul] using sum_le_card_nsmul V (fun a : ℕ ↦ a) N
      (fun a ha ↦ (mem_Icc.mp (hAN (hVA ha))).2)
  have hji : j=i+(j-i) := by omega
  have hprod : j*(shiftReps A i j).card = i*(shiftReps A i j).card+(j-i)*(shiftReps A i j).card := by
    calc
      _ = (i+(j-i))*(shiftReps A i j).card := congrArg (fun x ↦ x*(shiftReps A i j).card) hji
      _ = _ := by ring
  rw [hprod] at hs
  have hc := congrArg (fun n : ℕ ↦ N*n) hVc
  dsimp only at hc
  have hdisp : (j-i)*(shiftReps A i j).card ≤ V.card*N := by omega
  calc
    _ = 2*N*(shiftReps A i j).card+(j-i)*(shiftReps A i j).card := by ring
    _ ≤ 2*N*(shiftReps A i j).card+V.card*N := Nat.add_le_add_left hdisp _
    _ = N*A.card := by nlinarith only [hc]

/-- If a shift has nearly maximal multiplicity, then the shift itself is short
relative to the containing interval. -/
lemma large_multiplicity_short_shift {A : Finset ℕ} (hA : Good A) (N i j : ℕ)
    (hAN : A ⊆ Icc 0 N) (hij : i ≤ j)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j)
    (ε : ℝ)
    (hr : (1-ε)*(A.card : ℝ) ≤ 2*((shiftReps A i j).card : ℝ)) :
    ((j-i : ℕ) : ℝ)*((shiftReps A i j).card : ℝ) ≤ ε*N*A.card := by
  have hb : (2*(N : ℝ)+(j-i : ℕ))*((shiftReps A i j).card : ℝ) ≤ (N : ℝ)*A.card := by
    exact_mod_cast diameter_bound hA N i j hAN hij hNo
  have hh := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
  nlinarith

/-- At the exact odd-cardinality maximum, each cover misses a single vertex.
Consequently the shift multiplied by its multiplicity is a difference in `A`. -/
lemma maximal_shift_difference {A : Finset ℕ} (hA : Good A) (r δ : ℕ)
    (hcard : A.card = 2*r+1)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ)
    (hR : (shiftReps A 0 δ).card = r) :
    ∃ a ∈ A, ∃ b ∈ A, a+r*δ = b := by
  obtain ⟨U,V,hUA,hVA,hUc,hVc,hs⟩ := complement_balance hA 0 δ hNo
  rw [hR,hcard] at hUc hVc
  obtain ⟨a,rfl⟩ := card_eq_one.mp (show U.card=1 by omega)
  obtain ⟨b,rfl⟩ := card_eq_one.mp (show V.card=1 by omega)
  refine ⟨a,hUA (by simp),b,hVA (by simp),?_⟩
  simpa only [hR,sum_singleton,zero_mul,add_zero,mul_comm] using hs

/-- Exact maximum multiplicity cannot persist on more than quadratically many
positive shifts. This uses a common endpoint-difference constraint, not separate
pointwise cardinality estimates. -/
lemma count_maximal_shifts {A S : Finset ℕ} (hA : Good A) (r : ℕ) (hr : 0 < r)
    (hcard : A.card = 2*r+1)
    (hS : ∀ δ ∈ S, 0 < δ ∧
      (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧ (shiftReps A 0 δ).card = r) :
    S.card ≤ A.card^2 := by
  classical
  have hex (δ : S) : ∃ a ∈ A, ∃ b ∈ A, a+r*δ.val = b :=
    maximal_shift_difference hA r δ.val hcard (hS δ.val δ.property).2.1 (hS δ.val δ.property).2.2
  choose a ha b hb hab using hex
  have hh : (univ : Finset S).card ≤ (A ×ˢ A).card := by
    apply card_le_card_of_injOn (fun δ : S ↦ (a δ,b δ))
    · intro δ hδ
      exact mem_product.mpr ⟨ha δ,hb δ⟩
    · intro δ hδ ε hε he
      have h1 : a δ=a ε := congrArg Prod.fst he
      have h2 : b δ=b ε := congrArg Prod.snd he
      have hd := hab δ
      have he' := hab ε
      have hm : r*δ.val = r*ε.val := by omega
      exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hr hm)
  simpa [card_product,pow_two] using hh

/-- The sharper simultaneous bound obtained by remembering that the endpoints
are ordered: different maximal shifts determine different two-element subsets. -/
lemma count_maximal_shifts_sharp {A S : Finset ℕ} (hA : Good A) (r : ℕ) (hr : 0 < r)
    (hcard : A.card = 2*r+1)
    (hS : ∀ δ ∈ S, 0 < δ ∧
      (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧ (shiftReps A 0 δ).card = r) :
    S.card ≤ A.card.choose 2 := by
  classical
  have hex (δ : S) : ∃ a ∈ A, ∃ b ∈ A, a+r*δ.val = b :=
    maximal_shift_difference hA r δ.val hcard (hS δ.val δ.property).2.1 (hS δ.val δ.property).2.2
  choose a ha b hb hab using hex
  have hlt (δ : S) : a δ < b δ := by
    have hh := Nat.mul_pos hr (hS δ.val δ.property).1
    have he := hab δ
    omega
  have hh : (univ : Finset S).card ≤ (A.powersetCard 2).card := by
    apply card_le_card_of_injOn (fun δ : S ↦ ({a δ,b δ} : Finset ℕ))
    · intro δ hδ
      apply mem_powersetCard.mpr
      exact ⟨insert_subset_iff.mpr ⟨ha δ,singleton_subset_iff.mpr (hb δ)⟩,by simp [(hlt δ).ne]⟩
    · intro δ hδ ε hε he
      have he' : ({a δ,b δ} : Set ℕ) = {a ε,b ε} := by
        simpa only [coe_pair] using congrArg (fun P : Finset ℕ ↦ (P : Set ℕ)) he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have hd := hab δ
        have he'' := hab ε
        have hm : r*δ.val = r*ε.val := by omega
        exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hr hm)
      · have hd := hlt δ
        have he'' := hlt ε
        omega
  simpa only [card_univ,Fintype.card_coe,card_powersetCard] using hh

/-- Weighted aggregate form of the diameter constraint for any collection of
nonexceptional positive shifts. -/
lemma sum_shift_deficits {A S : Finset ℕ} (hA : Good A) (N : ℕ)
    (hAN : A ⊆ Icc 0 N)
    (hS : ∀ δ ∈ S, ∀ a ∈ A, ∀ b ∈ A, a ≠ b+δ) :
    (∑ δ ∈ S, δ*(shiftReps A 0 δ).card) +
      2*N*(∑ δ ∈ S, (shiftReps A 0 δ).card) ≤ N*A.card*S.card := by
  have hh := sum_le_sum (s := S) (fun δ hδ ↦ diameter_bound hA N 0 δ hAN (Nat.zero_le δ)
    (by simpa only [add_zero] using hS δ hδ))
  simp only [Nat.sub_zero,add_mul,sum_add_distrib,← mul_sum,sum_const,nsmul_eq_mul,Nat.cast_id] at hh
  nlinarith only [hh]

end ShiftRigidity


/- A limitation of the half-integer positive-mode energy estimate. -/
open Finset
namespace CosineBound

lemma reciprocal_square_telescope (x : ℝ) (hx : 0 < x) :
    1/(x+2)^2 ≤ (1/4)*(1/x-1/(x+4)) := by
  have hprod : x*(x+4) ≤ (x+2)^2 := by nlinarith
  calc
    _ ≤ 1/(x*(x+4)) := one_div_le_one_div_of_le (by positivity) hprod
    _ = _ := by field_simp; ring

lemma reciprocal_tail_telescope (n : ℕ) :
    (∑ j ∈ range n, (1/(4*(j : ℝ)+5)-1/(4*(j : ℝ)+9))) = 1/5-1/(4*(n : ℝ)+5) := by
  have hh := sum_range_sub (fun j : ℕ ↦ 1/(4*(j : ℝ)+5) : ℕ → ℝ) n
  have he (j : ℕ) : 4*((j+1 : ℕ) : ℝ)+5 = 4*(j : ℝ)+9 := by push_cast; ring
  simp only [he,Nat.cast_zero,mul_zero,zero_add] at hh
  rw [← neg_sub,← hh,← sum_neg_distrib]
  apply sum_congr rfl
  intro j hj
  ring

lemma reciprocal_modes_sum_bound (n : ℕ) :
    (∑ j ∈ range n, 1/(4*(j : ℝ)+3)^2) ≤ (29 : ℝ)/180 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [sum_range_succ']
    have hterm (j : ℕ) : 1/(4*((j+1 : ℕ) : ℝ)+3)^2 ≤
        (1/4)*(1/(4*(j : ℝ)+5)-1/(4*(j : ℝ)+9)) := by
      have hh := reciprocal_square_telescope (4*(j : ℝ)+5) (by positivity)
      convert hh using 1 <;> push_cast <;> ring
    have hh := sum_le_sum (s := range n) (fun j hj ↦ hterm j)
    rw [← mul_sum,reciprocal_tail_telescope] at hh
    have hp : 0 ≤ 1/(4*(n : ℝ)+5) := by positivity
    norm_num at hh hp ⊢
    have hp' : 0 ≤ (4*(n : ℝ)+5)⁻¹ := by positivity
    linarith

lemma coeff_square_sum_upper (T : Finset ℕ) :
    (∑ j ∈ T, (coeff j)^2) ≤ 116/(45*Real.pi^2) := by
  obtain ⟨n,hn⟩ := exists_nat_subset_range T
  have hs : (∑ j ∈ T, 1/(4*(j : ℝ)+3)^2) ≤ (29 : ℝ)/180 := by
    exact (sum_le_sum_of_subset_of_nonneg hn (fun _ _ _ ↦ by positivity)).trans
      (reciprocal_modes_sum_bound n)
  have he : (∑ j ∈ T, (coeff j)^2) = (16/Real.pi^2)*∑ j ∈ T, 1/(4*(j : ℝ)+3)^2 := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    dsimp [coeff]
    field_simp
    norm_num
  rw [he]
  calc
    _ ≤ (16/Real.pi^2)*(29/180) := mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by ring

/-- The coefficient selected for these modes already minimizes their quadratic
energy expression, even if arbitrary real coefficients are allowed. -/
lemma optimal_mode_coefficients (T : Finset ℕ) (c : ℕ → ℝ) :
    denominatorLimit T ≤ 2 - 2*(∑ j ∈ T, c j*coeff j) + ∑ j ∈ T, (c j)^2 := by
  have hh := sum_nonneg (s := T) (fun j hj ↦ sq_nonneg (c j-coeff j))
  simp only [sub_sq,sum_add_distrib,sum_sub_distrib,mul_assoc,← mul_sum] at hh
  dsimp only [denominatorLimit]
  linarith

/-- Enlarging this family of modes cannot settle the conjecture: its limiting
cube-ratio coefficient remains strictly greater than `3.47`. This is a limitation
of the proved estimate, not a lower bound on the extremal function. -/
lemma positive_mode_method_barrier (T : Finset ℕ) :
    (347 : ℝ)/100 < 2*denominatorLimit T := by
  have hs := coeff_square_sum_upper T
  have hp : 116/(45*Real.pi^2) < (53 : ℝ)/200 := by
    apply (div_lt_iff₀ (by positivity : 0 < 45*Real.pi^2)).mpr
    nlinarith [Real.pi_gt_d2,Real.pi_pos]
  dsimp [denominatorLimit]
  linarith

end CosineBound


/- Certificates and counting bounds for near-maximal pair-sum shifts. -/
open Finset
namespace ShiftRigidity
open B3Aux

/-- A shift of multiplicity `r` leaves two complement sets of size `m`.
Their sum difference is exactly `r * δ`. -/
lemma deficit_certificate {A : Finset ℕ} (hA : Good A) (r m δ : ℕ)
    (hcard : A.card = 2*r+m)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ)
    (hR : (shiftReps A 0 δ).card = r) :
    ∃ U V : Finset ℕ, U ∈ A.powersetCard m ∧ V ∈ A.powersetCard m ∧
      (∑ a ∈ U, a)+r*δ = ∑ a ∈ V, a := by
  obtain ⟨U,V,hUA,hVA,hUc,hVc,hs⟩ := complement_balance hA 0 δ hNo
  rw [hR,hcard] at hUc hVc
  refine ⟨U,V,mem_powersetCard.mpr ⟨hUA,by omega⟩,mem_powersetCard.mpr ⟨hVA,by omega⟩,?_⟩
  simpa only [hR,zero_mul,add_zero,mul_comm] using hs

/-- Different positive shifts of the same multiplicity have different unordered
pairs of complement certificates. -/
lemma count_fixed_deficit {A S : Finset ℕ} (hA : Good A) (r m : ℕ) (hr : 0 < r)
    (hcard : A.card = 2*r+m)
    (hS : ∀ δ ∈ S, 0 < δ ∧
      (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧ (shiftReps A 0 δ).card = r) :
    S.card ≤ (A.card.choose m).choose 2 := by
  classical
  have hex (δ : S) : ∃ U V : Finset ℕ, U ∈ A.powersetCard m ∧ V ∈ A.powersetCard m ∧
      (∑ a ∈ U, a)+r*δ.val = ∑ a ∈ V, a :=
    deficit_certificate hA r m δ.val hcard (hS δ.val δ.property).2.1 (hS δ.val δ.property).2.2
  choose U V hU hV hsum using hex
  have hlt (δ : S) : (∑ a ∈ U δ, a) < ∑ a ∈ V δ, a := by
    have hp := Nat.mul_pos hr (hS δ.val δ.property).1
    have he := hsum δ
    omega
  have hne (δ : S) : U δ ≠ V δ := by
    intro he
    have hh := hlt δ
    rw [he] at hh
    omega
  have hh : (univ : Finset S).card ≤ ((A.powersetCard m).powersetCard 2).card := by
    apply card_le_card_of_injOn (fun δ : S ↦ ({U δ,V δ} : Finset (Finset ℕ)))
    · intro δ hδ
      apply mem_powersetCard.mpr
      exact ⟨insert_subset_iff.mpr ⟨hU δ,singleton_subset_iff.mpr (hV δ)⟩,by simp [hne δ]⟩
    · intro δ hδ ε hε he
      have he' : ({U δ,V δ} : Set (Finset ℕ)) = {U ε,V ε} := by
        simpa only [coe_pair] using congrArg (fun P : Finset (Finset ℕ) ↦ (P : Set (Finset ℕ))) he
      rcases Set.pair_eq_pair_iff.mp he' with ⟨h1,h2⟩ | ⟨h1,h2⟩
      · have hd := hsum δ
        have he'' := hsum ε
        rw [h1,h2] at hd
        have hm : r*δ.val=r*ε.val := by omega
        exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hr hm)
      · have hd := hlt δ
        have he'' := hlt ε
        rw [h1,h2] at hd
        omega
  simpa only [card_univ,Fintype.card_coe,card_powersetCard] using hh

/-- The same certificates also confine every fixed-deficit shift to a short
interval. This can be stronger than the combinatorial certificate count. -/
lemma fixed_deficit_shift_bound {A : Finset ℕ} (hA : Good A) (N r m δ : ℕ)
    (hAN : A ⊆ Icc 0 N) (hr : 0 < r) (hcard : A.card=2*r+m)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ)
    (hR : (shiftReps A 0 δ).card=r) : δ ≤ m*N/r := by
  obtain ⟨U,V,hU,hV,hs⟩ := deficit_certificate hA r m δ hcard hNo hR
  have hv : (∑ a ∈ V, a) ≤ m*N := by
    have hh := sum_le_card_nsmul V (fun a : ℕ ↦ a) N
      (fun a ha ↦ (mem_Icc.mp (hAN ((mem_powersetCard.mp hV).1 ha))).2)
    simpa only [nsmul_eq_mul,(mem_powersetCard.mp hV).2] using hh
  apply (Nat.le_div_iff_mul_le hr).mpr
  rw [Nat.mul_comm δ r]
  omega

lemma count_fixed_deficit_diameter {A S : Finset ℕ} (hA : Good A) (N r m : ℕ)
    (hAN : A ⊆ Icc 0 N) (hr : 0 < r) (hcard : A.card=2*r+m)
    (hS : ∀ δ ∈ S, 0 < δ ∧
      (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧ (shiftReps A 0 δ).card=r) :
    S.card ≤ m*N/r := by
  have hsub : S ⊆ Icc 1 (m*N/r) := by
    intro δ hδ
    exact mem_Icc.mpr ⟨(hS δ hδ).1,
      fixed_deficit_shift_bound hA N r m δ hAN hr hcard (hS δ hδ).2.1 (hS δ hδ).2.2⟩
  simpa using card_le_card hsub

/-- Simultaneous control with either available certificate bound. -/
lemma count_fixed_deficit_combined {A S : Finset ℕ} (hA : Good A) (N r m : ℕ)
    (hAN : A ⊆ Icc 0 N) (hr : 0 < r) (hcard : A.card=2*r+m)
    (hS : ∀ δ ∈ S, 0 < δ ∧
      (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧ (shiftReps A 0 δ).card=r) :
    S.card ≤ min ((A.card.choose m).choose 2) (m*N/r) :=
  le_min (count_fixed_deficit hA r m hr hcard hS)
    (count_fixed_deficit_diameter hA N r m hAN hr hcard hS)

/-- A uniform short-shift bound when the deficit is only bounded above. -/
lemma bounded_deficit_shift_bound {A : Finset ℕ} (hA : Good A) (N m δ : ℕ)
    (hAN : A ⊆ Icc 0 N) (hm : m < A.card)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ)
    (hR : A.card ≤ 2*(shiftReps A 0 δ).card+m) :
    δ ≤ (2*m*N)/(A.card-m) := by
  let r := (shiftReps A 0 δ).card
  have hsmall : A.card-m ≤ 2*r := by omega
  have hb := diameter_bound hA N 0 δ hAN (Nat.zero_le _) hNo
  simp only [Nat.sub_zero] at hb
  have hc := Nat.mul_le_mul_left N hR
  have hdisp : δ*r ≤ m*N := by
    dsimp only [r]
    nlinarith only [hb,hc]
  apply (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hm)).mpr
  calc
    _ ≤ δ*(2*r) := Nat.mul_le_mul_left δ hsmall
    _ = 2*(δ*r) := by ring
    _ ≤ 2*(m*N) := Nat.mul_le_mul_left 2 hdisp
    _ = _ := by ring

/-- A simultaneous near-maximality estimate. For an additive deficit `m < |A|`,
all qualifying positive shifts lie in an interval of length at most
`2*m*N/(|A|-m)`, even when their multiplicities differ. -/
lemma count_bounded_deficit {A S : Finset ℕ} (hA : Good A) (N m : ℕ)
    (hAN : A ⊆ Icc 0 N) (hm : m < A.card)
    (hS : ∀ δ ∈ S, 0 < δ ∧ (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧
      A.card ≤ 2*(shiftReps A 0 δ).card+m) :
    S.card ≤ (2*m*N)/(A.card-m) := by
  have hsub : S ⊆ Icc 1 ((2*m*N)/(A.card-m)) := by
    intro δ hδ
    exact mem_Icc.mpr ⟨(hS δ hδ).1,
      bounded_deficit_shift_bound hA N m δ hAN hm (hS δ hδ).2.1 (hS δ hδ).2.2⟩
  simpa using card_le_card hsub

/-- The equivalent multiplicative form avoids integer division. -/
lemma count_bounded_deficit_mul {A S : Finset ℕ} (hA : Good A) (N m : ℕ)
    (hAN : A ⊆ Icc 0 N) (hm : m < A.card)
    (hS : ∀ δ ∈ S, 0 < δ ∧ (∀ a ∈ A, ∀ b ∈ A, a+0 ≠ b+δ) ∧
      A.card ≤ 2*(shiftReps A 0 δ).card+m) :
    S.card*(A.card-m) ≤ 2*m*N :=
  (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt hm)).mp (count_bounded_deficit hA N m hAN hm hS)

end ShiftRigidity

namespace DifferenceGraph
open B3Aux

lemma two_sum_mem {A : Finset ℕ} (hA : Good A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hs : a+b=c+d) : a=c ∨ a=d := by
  have hm := sum_two_inj hA {a,b} {c,d} (by simp) (by simp)
    (by simp [ha,hb]) (by simp [hc,hd]) (by simpa using hs)
  have hmem : a ∈ ({c,d} : Multiset ℕ) := hm ▸ (by simp : a ∈ ({a,b} : Multiset ℕ))
  simpa using hmem

lemma difference_inj {A : Finset ℕ} (hA : Good A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hs : (a : ℤ)-b = c-d) : a=c ∧ b=d := by
  have he : a+d=c+b := by omega
  rcases two_sum_mem hA ha hd hc hb he with h | h
  · exact ⟨h,by omega⟩
  · exact (hab h).elim

def graph (A : Finset ℕ) : SimpleGraph ℤ where
  Adj x y := ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ x-y=(a:ℤ)-b
  symm := by
    rintro x y ⟨a,ha,b,hb,hab,h⟩
    exact ⟨b,hb,a,ha,hab.symm,by omega⟩
  loopless := by
    rintro x ⟨a,ha,b,hb,hab,h⟩
    exact hab (by omega)

lemma adj_iff (A : Finset ℕ) (x y : ℤ) :
    (graph A).Adj x y ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ x-y=(a:ℤ)-b := Iff.rfl

/-- The neighborhood of zero is the set of distinct ordered differences. -/
lemma adj_zero_iff (A : Finset ℕ) (x : ℤ) :
    (graph A).Adj 0 x ↔ ∃ a ∈ A, ∃ b ∈ A, a ≠ b ∧ x=(a:ℤ)-b := by
  rw [(graph A).adj_comm,adj_iff]
  simp

/-- In ordered-pair coordinates, the local graph is the rook graph with its
 diagonal positions deleted. -/
lemma local_adj_iff {A : Finset ℕ} (hA : Good A)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) :
    (graph A).Adj ((a:ℤ)-b) ((c:ℤ)-d) ↔
      (a=c ∧ b≠d) ∨ (b=d ∧ a≠c) := by
  constructor
  · intro h
    obtain ⟨u,hu,v,hv,huv,hs⟩ := h
    have he : a+d+v=b+c+u := by omega
    have hne : ¬ (a=c ∧ b=d) := by
      rintro ⟨rfl,rfl⟩
      exact huv (by omega)
    rcases three_sum_mem hA ha hd hv hb hc hu he with hh | hh | hh
    · exact (hab hh).elim
    · exact Or.inl ⟨hh,fun hbd ↦ hne ⟨hh,hbd⟩⟩
    · have he' : d+v=b+c := by omega
      rcases two_sum_mem hA hd hv hb hc he' with hdb | hdc
      · exact Or.inr ⟨hdb.symm,fun hac ↦ hne ⟨hac,hdb.symm⟩⟩
      · exact (hcd hdc.symm).elim
  · rintro (⟨rfl,hbd⟩ | ⟨rfl,hac⟩)
    · exact ⟨d,hd,b,hb,hbd.symm,by omega⟩
    · exact ⟨a,ha,c,hc,hac,by omega⟩

noncomputable def neighbors (A : Finset ℕ) (x : ℤ) : Finset ℤ :=
  A.offDiag.image (fun p ↦ x+(p.1:ℤ)-p.2)

lemma mem_neighbors {A : Finset ℕ} {x y : ℤ} :
    y ∈ neighbors A x ↔ (graph A).Adj x y := by
  classical
  rw [neighbors,mem_image]
  constructor
  · rintro ⟨⟨a,b⟩,hp,he⟩
    rcases mem_offDiag.mp hp with ⟨ha,hb,hab⟩
    exact ⟨b,hb,a,ha,hab.symm,by dsimp only at he; omega⟩
  · rintro ⟨a,ha,b,hb,hab,he⟩
    exact ⟨(b,a),mem_offDiag.mpr ⟨hb,ha,hab.symm⟩,by dsimp only; omega⟩

lemma card_neighbors {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (neighbors A x).card = A.card*(A.card-1) := by
  classical
  rw [neighbors,card_image_of_injOn]
  · rw [offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one]
  · rintro ⟨a,b⟩ hp ⟨c,d⟩ hq he
    obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp hp
    obtain ⟨hc,hd,hcd⟩ := mem_offDiag.mp hq
    dsimp only at he
    obtain ⟨rfl,rfl⟩ := difference_inj hA ha hb hc hd hab (by omega)
    rfl

/-- Common neighbors of an edge split into its row and column cliques. -/
lemma common_neighbors_eq {A : Finset ℕ} (hA : Good A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    neighbors A 0 ∩ neighbors A ((a:ℤ)-b) =
      ((A.erase a).erase b).image (fun d : ℕ ↦ (a:ℤ)-d) ∪
      ((A.erase a).erase b).image (fun c : ℕ ↦ (c:ℤ)-b) := by
  classical
  ext x
  simp only [mem_inter,mem_neighbors,mem_union,mem_image,mem_erase]
  constructor
  · rintro ⟨h0,h1⟩
    obtain ⟨c,hc,d,hd,hcd,rfl⟩ := (adj_zero_iff A x).mp h0
    rcases (local_adj_iff hA ha hb hc hd hab hcd).mp h1 with
      ⟨rfl,hbd⟩ | ⟨rfl,hac⟩
    · exact Or.inl ⟨d,⟨hbd.symm,hcd.symm,hd⟩,rfl⟩
    · exact Or.inr ⟨c,⟨hcd,hac.symm,hc⟩,rfl⟩
  · rintro (⟨d,⟨hdb,hda,hd⟩,rfl⟩ | ⟨c,⟨hcb,hca,hc⟩,rfl⟩)
    · exact ⟨(adj_zero_iff A _).mpr ⟨a,ha,d,hd,hda.symm,rfl⟩,
        (local_adj_iff hA ha hb ha hd hab hda.symm).mpr (Or.inl ⟨rfl,hdb.symm⟩)⟩
    · exact ⟨(adj_zero_iff A _).mpr ⟨c,hc,b,hb,hcb,rfl⟩,
        (local_adj_iff hA ha hb hc hb hab hcb).mpr (Or.inr ⟨rfl,hca.symm⟩)⟩

lemma common_neighbors_card {A : Finset ℕ} (hA : Good A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b) :
    (neighbors A 0 ∩ neighbors A ((a:ℤ)-b)).card = 2*(A.card-2) := by
  classical
  rw [common_neighbors_eq hA ha hb hab,card_union_of_disjoint]
  · have hi₁ : Function.Injective (fun d : ℕ ↦ (a:ℤ)-d) := by
      intro d e h
      dsimp only at h
      omega
    have hi₂ : Function.Injective (fun c : ℕ ↦ (c:ℤ)-b) := by
      intro c d h
      dsimp only at h
      omega
    rw [card_image_of_injective _ hi₁,card_image_of_injective _ hi₂,
      card_erase_of_mem (mem_erase.mpr ⟨hab.symm,hb⟩),card_erase_of_mem ha]
    omega
  · apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨d,hd,he⟩ := mem_image.mp hx
    obtain ⟨c,hc,hf⟩ := mem_image.mp hy
    simp only [mem_erase] at hd hc
    have hdiff : (a:ℤ)-c = (d:ℤ)-b := by omega
    obtain ⟨had,hcb⟩ := difference_inj hA ha hc.2.2 hd.2.2 hb hc.2.1.symm hdiff
    exact hd.2.1 had.symm

end DifferenceGraph

namespace ProductObstruction
open B3Aux

variable {α β : Type*}

/-- Four corners of a rectangle are incompatible with a Sidon, hence B₃,
image under an injective separable encoding. -/
lemma no_rectangle (E : Finset (α × β)) (u : α → ℕ) (v : β → ℕ)
    (hinj : Set.InjOn (fun p : α × β ↦ u p.1+v p.2) E)
    (hgood : Good (E.image (fun p ↦ u p.1+v p.2)))
    {a c : α} {b d : β} (hab : (a,b) ∈ E) (had : (a,d) ∈ E)
    (hcb : (c,b) ∈ E) (hcd : (c,d) ∈ E) : a=c ∨ b=d := by
  classical
  have hmem {p : α × β} (hp : p ∈ E) : u p.1+v p.2 ∈ E.image (fun p ↦ u p.1+v p.2) :=
    mem_image_of_mem _ hp
  have hm := sum_two_inj hgood {u a+v b,u c+v d} {u a+v d,u c+v b}
    (by simp) (by simp) (by simpa using And.intro (hmem hab) (hmem hcd))
    (by simpa using And.intro (hmem had) (hmem hcb)) (by simp; omega)
  have hh : u a+v b ∈ ({u a+v d,u c+v b} : Multiset ℕ) :=
    hm ▸ (by simp : u a+v b ∈ ({u a+v b,u c+v d} : Multiset ℕ))
  have hh' : u a+v b=u a+v d ∨ u a+v b=u c+v b := by simpa using hh
  rcases hh' with h | h
  · exact Or.inr (congrArg Prod.snd (hinj hab had h))
  · exact Or.inl (congrArg Prod.fst (hinj hab hcb h))

/-- A six-cycle gives a nontrivial equality of triple sums. -/
lemma no_hexagon (E : Finset (α × β)) (u : α → ℕ) (v : β → ℕ)
    (hinj : Set.InjOn (fun p : α × β ↦ u p.1+v p.2) E)
    (hgood : Good (E.image (fun p ↦ u p.1+v p.2)))
    {a c e : α} {b d f : β} (hac : a ≠ c) (hae : a ≠ e) (hbd : b ≠ d)
    (hab : (a,b) ∈ E) (hcd : (c,d) ∈ E) (hef : (e,f) ∈ E)
    (had : (a,d) ∈ E) (hcf : (c,f) ∈ E) (heb : (e,b) ∈ E) : False := by
  classical
  have hmem {p : α × β} (hp : p ∈ E) : u p.1+v p.2 ∈ E.image (fun p ↦ u p.1+v p.2) :=
    mem_image_of_mem _ hp
  have hh := three_sum_mem hgood (hmem hab) (hmem hcd) (hmem hef)
    (hmem had) (hmem hcf) (hmem heb) (by dsimp only; omega)
  rcases hh with h | h | h
  · exact hbd (congrArg Prod.snd (hinj hab had h))
  · exact hac (congrArg Prod.fst (hinj hab hcf h))
  · exact hae (congrArg Prod.fst (hinj hab heb h))

lemma card_le_one_add_choose_two (n : ℕ) : n ≤ 1+n.choose 2 := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    omega

/-- A rectangle-free subset of a product has at most one uncharged edge per
right vertex; all remaining edges can be charged to distinct left pairs. -/
lemma rectangle_free_card_bound (L : Finset α) (R : Finset β) (E : Finset (α × β))
    (hsub : E ⊆ L ×ˢ R)
    (hrect : ∀ a c b d, (a,b) ∈ E → (a,d) ∈ E → (c,b) ∈ E → (c,d) ∈ E → a=c ∨ b=d) :
    E.card ≤ R.card+L.card.choose 2 := by
  classical
  let F (b : β) := L.filter (fun a ↦ (a,b) ∈ E)
  have hFL (b : β) : F b ⊆ L := filter_subset _ _
  have hdis : (↑R : Set β).PairwiseDisjoint (fun b ↦ (F b).powersetCard 2) := by
    intro b hb d hd hbd
    apply disjoint_left.mpr
    intro P hPb hPd
    obtain ⟨hPFb,hPc⟩ := mem_powersetCard.mp hPb
    obtain ⟨hPFd,_⟩ := mem_powersetCard.mp hPd
    obtain ⟨a,c,hac,rfl⟩ := card_eq_two.mp hPc
    have hab := (mem_filter.mp (hPFb (by simp : a ∈ ({a,c} : Finset α)))).2
    have hcb := (mem_filter.mp (hPFb (by simp : c ∈ ({a,c} : Finset α)))).2
    have had := (mem_filter.mp (hPFd (by simp : a ∈ ({a,c} : Finset α)))).2
    have hcd := (mem_filter.mp (hPFd (by simp : c ∈ ({a,c} : Finset α)))).2
    exact (hrect a c b d hab had hcb hcd).elim hac hbd
  have hpair : (∑ b ∈ R, (F b).card.choose 2) ≤ L.card.choose 2 := by
    have hh : R.biUnion (fun b ↦ (F b).powersetCard 2) ⊆ L.powersetCard 2 := by
      intro P hP
      obtain ⟨b,hb,hPb⟩ := mem_biUnion.mp hP
      exact powersetCard_mono (hFL b) hPb
    have hc := card_le_card hh
    rw [card_biUnion hdis,card_powersetCard] at hc
    simpa only [card_powersetCard] using hc
  have hfc (b : β) : (E.filter (fun p ↦ p.2=b)).card = (F b).card := by
    apply card_bij (fun p _ ↦ p.1)
    · intro p hp
      obtain ⟨hp,hpb⟩ := mem_filter.mp hp
      apply mem_filter.mpr
      exact ⟨(mem_product.mp (hsub hp)).1,by simpa only [← hpb,Prod.mk.eta] using hp⟩
    · intro p hp q hq he
      have hp' := (mem_filter.mp hp).2
      have hq' := (mem_filter.mp hq).2
      exact Prod.ext he (hp'.trans hq'.symm)
    · intro a ha
      obtain ⟨ha,hab⟩ := mem_filter.mp ha
      exact ⟨(a,b),mem_filter.mpr ⟨hab,rfl⟩,rfl⟩
  have he : E.card = ∑ b ∈ R, (F b).card := by
    rw [card_eq_sum_card_fiberwise (f := Prod.snd) (t := R)
      (fun p hp ↦ (mem_product.mp (hsub hp)).2)]
    simp_rw [hfc]
  rw [he]
  calc
    _ ≤ ∑ b ∈ R, (1+(F b).card.choose 2) := sum_le_sum (fun b _ ↦ card_le_one_add_choose_two _)
    _ = R.card+∑ b ∈ R, (F b).card.choose 2 := by simp [sum_add_distrib]
    _ ≤ _ := Nat.add_le_add_left hpair _

lemma separable_encoding_card_bound (L : Finset α) (R : Finset β) (E : Finset (α × β))
    (u : α → ℕ) (v : β → ℕ) (hsub : E ⊆ L ×ˢ R)
    (hinj : Set.InjOn (fun p : α × β ↦ u p.1+v p.2) E)
    (hgood : Good (E.image (fun p ↦ u p.1+v p.2))) :
    E.card ≤ R.card+L.card.choose 2 :=
  rectangle_free_card_bound L R E hsub (fun _ _ _ _ ↦ no_rectangle E u v hinj hgood)

/-- The same bound needs no injectivity assumption if it is stated directly
for a B₃ set contained in a separable sum cover. -/
lemma sum_cover_card_bound (L : Finset α) (R : Finset β) (A : Finset ℕ)
    (u : α → ℕ) (v : β → ℕ) (hgood : Good A)
    (hcover : A ⊆ (L ×ˢ R).image (fun p ↦ u p.1+v p.2)) :
    A.card ≤ R.card+L.card.choose 2 := by
  classical
  have hsurj : (↑(L ×ˢ R) : Set (α × β)).SurjOn (fun p ↦ u p.1+v p.2) A := by
    intro a ha
    obtain ⟨p,hp,he⟩ := mem_image.mp (hcover ha)
    exact ⟨p,hp,he⟩
  obtain ⟨E,hE,hinj,himage⟩ := exists_subset_injOn_image_eq_of_surjOn _ _ hsurj
  have hgood' : Good (E.image (fun p ↦ u p.1+v p.2)) := himage.symm ▸ hgood
  have hb := separable_encoding_card_bound L R E u v hE hinj hgood'
  have hc : E.card=A.card := by rw [← himage,card_image_of_injOn hinj]
  simpa only [hc] using hb

end ProductObstruction

namespace CyclicExample

def code : Fin 6 → ZMod 117 := ![0,1,6,14,54,87]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma code_three_inj : Function.Injective
    (fun s : Sym (Fin 6) 3 ↦ (s.val.map code).sum) := by
  decide

lemma three_sum_unique (s t : Multiset (Fin 6)) (hs : s.card=3) (ht : t.card=3)
    (he : (s.map code).sum=(t.map code).sum) : s=t := by
  have h := code_three_inj (a₁ := ⟨s,hs⟩) (a₂ := ⟨t,ht⟩) he
  exact congrArg Subtype.val h

lemma small_cyclic_bound_fails :
    ¬ (∀ (m n : ℕ) (v : Fin n → ZMod m),
      Function.Injective (fun s : Sym (Fin n) 3 ↦ (s.val.map v).sum) →
      (n-1)^3 ≤ m) := by
  intro h
  have hh := h 117 6 code code_three_inj
  norm_num at hh

end CyclicExample

namespace ColouredPacking

variable {I J G : Type*} [AddCommGroup G]

/-- Triple sums determine their labelled entries whenever the two triples have
 the same multiset of colours. -/
def GoodFamily (v : I × J → G) : Prop :=
  ∀ a b c d e f : I × J,
    ({a.1,b.1,c.1} : Multiset I) = {d.1,e.1,f.1} →
    v a+v b+v c=v d+v e+v f →
    ({a,b,c} : Multiset (I × J)) = {d,e,f}

lemma multiset_inj {v : I × J → G} (hv : GoodFamily v)
    (s t : Multiset (I × J)) (hs : s.card=3) (ht : t.card=3)
    (hc : s.map Prod.fst=t.map Prod.fst) (he : (s.map v).sum=(t.map v).sum) : s=t := by
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hs
  obtain ⟨d,e,f,rfl⟩ := Multiset.card_eq_three.mp ht
  exact hv a b c d e f (by simpa using hc) (by simpa [add_assoc] using he)

lemma two_multiset_inj {v : I × J → G} (hv : GoodFamily v) (p : I × J)
    (s t : Multiset (I × J)) (hs : s.card=2) (ht : t.card=2)
    (hc : s.map Prod.fst=t.map Prod.fst) (he : (s.map v).sum=(t.map v).sum) : s=t := by
  apply Multiset.cons_inj_right p |>.mp
  exact multiset_inj hv (p ::ₘ s) (p ::ₘ t) (by simp [hs]) (by simp [ht])
    (by simp [hc]) (by simp [he])

lemma signed_multiset_inj {v : I × J → G} (hv : GoodFamily v) (i : I)
    {s t : Multiset (I × J)} {c d : I × J} (hs : s.card=2) (ht : t.card=2)
    (hc : s.map Prod.fst={i,c.1}) (hd : t.map Prod.fst={i,d.1})
    (hcn : c ∉ s)
    (he : (s.map v).sum-v c=(t.map v).sum-v d) : c=d ∧ s=t := by
  have hcol : (d ::ₘ s).map Prod.fst=(c ::ₘ t).map Prod.fst := by
    simp only [Multiset.map_cons,hc,hd]
    change d.1 ::ₘ i ::ₘ c.1 ::ₘ 0 = c.1 ::ₘ i ::ₘ d.1 ::ₘ 0
    calc
      _ = i ::ₘ d.1 ::ₘ c.1 ::ₘ 0 := Multiset.cons_swap _ _ _
      _ = i ::ₘ c.1 ::ₘ d.1 ::ₘ 0 := congrArg (Multiset.cons i) (Multiset.cons_swap _ _ _)
      _ = _ := Multiset.cons_swap _ _ _
  have hh := multiset_inj hv (d ::ₘ s) (c ::ₘ t) (by simp [hs]) (by simp [ht]) hcol (by
    simp only [Multiset.map_cons,Multiset.sum_cons]
    have hh := sub_eq_sub_iff_add_eq_add.mp he
    simpa only [add_comm] using hh)
  have hcd : c=d := by
    have hm : c ∈ d ::ₘ s := hh.symm ▸ Multiset.mem_cons_self c t
    exact (Multiset.mem_cons.mp hm).resolve_right hcn
  subst d
  exact ⟨rfl,Multiset.cons_inj_right c |>.mp hh⟩

lemma signed_ne_plain {v : I × J → G} (hv : GoodFamily v) (i : I)
    {s : Multiset (I × J)} {c : I × J} (hs : s.card=2)
    (hc : s.map Prod.fst={i,c.1}) (hcn : c ∉ s) (a : J) :
    (s.map v).sum-v c ≠ v (i,a) := by
  intro he
  have hcol : s.map Prod.fst=({c,(i,a)} : Multiset (I × J)).map Prod.fst := by
    simpa only [Multiset.map_cons,Multiset.map_singleton] using hc.trans (Multiset.pair_comm _ _)
  have hh := two_multiset_inj hv c s {c,(i,a)} hs (by simp) hcol (by
    simpa [add_comm] using sub_eq_iff_eq_add.mp he)
  exact hcn (hh.symm ▸ (by simp : c ∈ ({c,(i,a)} : Multiset (I × J))))

lemma cross_signed_inj {v : I × J → G} (hv : GoodFamily v) (i : I)
    {j k : I} {a b c d e f : J} (hji : j ≠ i) (hki : k ≠ i)
    (hbc : b ≠ c) (_hef : e ≠ f)
    (hs : v (i,a)+v (j,b)-v (j,c)=v (i,d)+v (k,e)-v (k,f)) :
    j=k ∧ a=d ∧ b=e ∧ c=f := by
  have hc : ({i,j,k} : Multiset I)={i,k,j} := by
    congr 1
    exact Multiset.pair_comm _ _
  have hh := hv (i,a) (j,b) (k,f) (i,d) (k,e) (j,c) hc (sub_eq_sub_iff_add_eq_add.mp hs)
  have hneg : (j,c)=(i,a) ∨ (j,c)=(j,b) ∨ (j,c)=(k,f) := by
    have hm : (j,c) ∈ ({(i,a),(j,b),(k,f)} : Multiset (I × J)) :=
      hh.symm ▸ (by simp : (j,c) ∈ ({(i,d),(k,e),(j,c)} : Multiset (I × J)))
    simpa using hm
  have hjk : j=k ∧ c=f := by
    rcases hneg with h | h | h
    · exact (hji (congrArg Prod.fst h)).elim
    · exact (hbc (congrArg Prod.snd h).symm).elim
    · exact ⟨congrArg Prod.fst h,congrArg Prod.snd h⟩
  have hanchor : (i,a)=(i,d) ∨ (i,a)=(k,e) ∨ (i,a)=(j,c) := by
    have hm : (i,a) ∈ ({(i,d),(k,e),(j,c)} : Multiset (I × J)) :=
      hh ▸ (by simp : (i,a) ∈ ({(i,a),(j,b),(k,f)} : Multiset (I × J)))
    simpa using hm
  have had : a=d := by
    rcases hanchor with h | h | h
    · exact congrArg Prod.snd h
    · exact (hki (congrArg Prod.fst h).symm).elim
    · exact (hji (congrArg Prod.fst h).symm).elim
  have hother : (j,b)=(i,d) ∨ (j,b)=(k,e) ∨ (j,b)=(j,c) := by
    have hm : (j,b) ∈ ({(i,d),(k,e),(j,c)} : Multiset (I × J)) :=
      hh ▸ (by simp : (j,b) ∈ ({(i,a),(j,b),(k,f)} : Multiset (I × J)))
    simpa using hm
  have hbe : b=e := by
    rcases hother with h | h | h
    · exact (hji (congrArg Prod.fst h)).elim
    · exact congrArg Prod.snd h
    · exact (hbc (congrArg Prod.snd h)).elim
  exact ⟨hjk.1,had,hbe,hjk.2⟩

/-- Keeping one positive colour fixed, and varying the colour of a non-cancelling
 difference, gives pairwise distinct elements of the auxiliary group. -/
lemma cross_signed_packing [Fintype I] [Fintype J] [Fintype G]
    (v : I × J → G) (hv : GoodFamily v) (i : I) :
    (Fintype.card I-1)*Fintype.card J*(Fintype.card J*(Fintype.card J-1)) ≤
      Fintype.card G := by
  classical
  let S := ((univ : Finset I).erase i) ×ˢ ((univ : Finset J) ×ˢ (univ : Finset J).offDiag)
  let code : I × (J × (J × J)) → G := fun p ↦ v (i,p.2.1)+v (p.1,p.2.2.1)-v (p.1,p.2.2.2)
  have hi : Set.InjOn code S := by
    rintro ⟨j,a,b,c⟩ hp ⟨k,d,e,f⟩ hq he
    have hp' : j ≠ i ∧ b ≠ c := by simpa [S] using hp
    have hq' : k ≠ i ∧ e ≠ f := by simpa [S] using hq
    obtain ⟨rfl,rfl,rfl,rfl⟩ := cross_signed_inj hv i hp'.1 hq'.1 hp'.2 hq'.2 he
    rfl
  have hh : (S.image code).card ≤ Fintype.card G := card_le_univ _
  rw [card_image_of_injOn hi] at hh
  simpa [S,card_product,offDiag_card,Nat.mul_sub_left_distrib,mul_assoc] using hh

/-- The same-colour signed triples supply the additional half-cubic term. -/
lemma same_signed_set [Fintype J] (v : I × J → G) (hv : GoodFamily v) (i : I) :
    ∃ T : Finset G, T.card=Fintype.card J*(Fintype.card J).choose 2 ∧
      ∀ x ∈ T, ∃ c : J, ∃ s : Multiset (I × J), s.card=2 ∧
        s.map Prod.fst={i,i} ∧ (i,c) ∉ s ∧ x=(s.map v).sum-v (i,c) := by
  classical
  let D := (c : J) × Sym ↥((univ : Finset J).erase c) 2
  let pos (d : D) : Multiset (I × J) := d.2.val.map (fun a : ↥((univ : Finset J).erase d.1) ↦ (i,a.val))
  have hpc (d : D) : (pos d).card=2 := by simp [pos]
  have hpcol (d : D) : (pos d).map Prod.fst={i,i} := by
    simp [pos,Multiset.map_map]
  have hpn (d : D) : (i,d.1) ∉ pos d := by
    intro h
    dsimp only [pos] at h
    obtain ⟨a,ha,he⟩ := Multiset.mem_map.mp h
    exact (mem_erase.mp a.property).1 (congrArg Prod.snd he)
  let code (d : D) : G := ((pos d).map v).sum-v (i,d.1)
  have hi : Function.Injective code := by
    rintro ⟨c,m⟩ ⟨d,n⟩ he
    obtain ⟨hcd,hmn⟩ := signed_multiset_inj hv i (hpc ⟨c,m⟩) (hpc ⟨d,n⟩)
      (hpcol ⟨c,m⟩) (hpcol ⟨d,n⟩) (hpn ⟨c,m⟩) he
    have hcd' : c=d := congrArg Prod.snd hcd
    subst d
    congr 1
    apply Sym.ext
    apply Multiset.map_injective (f := fun a : ↥((univ : Finset J).erase c) ↦ (i,(a : J)))
      (fun a b he ↦ Subtype.ext (congrArg Prod.snd he))
    simpa only [pos] using hmn
  have hsize (c : J) : Fintype.card (Sym ↥((univ : Finset J).erase c) 2) =
      (Fintype.card J).choose 2 := by
    rw [Sym.card_sym_eq_choose,Fintype.card_coe,card_erase_of_mem (mem_univ c),card_univ]
    have hp : 0 < Fintype.card J := Fintype.card_pos_iff.mpr ⟨c⟩
    congr 1
    omega
  refine ⟨univ.image code,?_,?_⟩
  · rw [card_image_of_injective _ hi,card_univ,Fintype.card_sigma]
    simp_rw [hsize]
    simp
  · intro x hx
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hx
    exact ⟨d.1,pos d,hpc d,hpcol d,hpn d,rfl⟩

lemma one_colour_packing [Fintype J] [Fintype G]
    (v : I × J → G) (hv : GoodFamily v) (i : I) :
    Fintype.card J*(Fintype.card J).choose 2+Fintype.card J ≤ Fintype.card G := by
  classical
  obtain ⟨T,hTc,hT⟩ := same_signed_set v hv i
  have hi : Function.Injective (fun a : J ↦ v (i,a)) := by
    intro a b he
    dsimp only at he
    have hh := hv (i,a) (i,a) (i,a) (i,b) (i,a) (i,a) rfl (by rw [he])
    have hm : (i,b) ∈ ({(i,a),(i,a),(i,a)} : Multiset (I × J)) := hh.symm ▸ (by simp)
    have hh' : (i,b)=(i,a) := by simpa using hm
    exact (congrArg Prod.snd hh').symm
  let P := (univ : Finset J).image (fun a ↦ v (i,a))
  have hPc : P.card=Fintype.card J := by
    dsimp only [P]
    rw [card_image_of_injective _ hi,card_univ]
  have hdis : Disjoint T P := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c,s,hsc,hscol,hcn,hs⟩ := hT x hx
    obtain ⟨a,ha,he⟩ := mem_image.mp hy
    exact signed_ne_plain hv i hsc hscol hcn a (hs.symm.trans he.symm)
  have hh : (T ∪ P).card ≤ Fintype.card G := card_le_univ _
  simpa only [card_union_of_disjoint hdis,hTc,hPc] using hh

lemma ordinary_code_packing [Fintype J] [Fintype G] (v : J → G)
    (hv : Function.Injective (fun s : Sym J 3 ↦ (s.val.map v).sum)) :
    Fintype.card J*(Fintype.card J).choose 2+Fintype.card J ≤ Fintype.card G := by
  let w : Unit × J → G := fun p ↦ v p.2
  have hw : GoodFamily w := by
    rintro ⟨⟨⟩,a⟩ ⟨⟨⟩,b⟩ ⟨⟨⟩,c⟩ ⟨⟨⟩,d⟩ ⟨⟨⟩,e⟩ ⟨⟨⟩,f⟩ hc he
    have hh := hv (a₁ := ⟨{a,b,c},by simp⟩) (a₂ := ⟨{d,e,f},by simp⟩)
      (by simpa [w,add_assoc] using he)
    have hh' := congrArg (Multiset.map (fun a : J ↦ ((),a))) (congrArg Subtype.val hh)
    simpa using hh'
  exact one_colour_packing w hw ()

lemma full_signed_packing [Fintype I] [Fintype J] [Fintype G]
    (v : I × J → G) (hv : GoodFamily v) (i : I) :
    Fintype.card J*(Fintype.card J).choose 2+
      (Fintype.card I-1)*Fintype.card J*(Fintype.card J*(Fintype.card J-1)) ≤
        Fintype.card G := by
  classical
  obtain ⟨T,hTc,hT⟩ := same_signed_set v hv i
  let S := ((univ : Finset I).erase i) ×ˢ ((univ : Finset J) ×ˢ (univ : Finset J).offDiag)
  let code : I × (J × (J × J)) → G := fun p ↦ v (i,p.2.1)+v (p.1,p.2.2.1)-v (p.1,p.2.2.2)
  have hi : Set.InjOn code S := by
    rintro ⟨j,a,b,c⟩ hp ⟨k,d,e,f⟩ hq he
    have hp' : j ≠ i ∧ b ≠ c := by simpa [S] using hp
    have hq' : k ≠ i ∧ e ≠ f := by simpa [S] using hq
    obtain ⟨rfl,rfl,rfl,rfl⟩ := cross_signed_inj hv i hp'.1 hq'.1 hp'.2 hq'.2 he
    rfl
  have hdis : Disjoint T (S.image code) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c,s,hsc,hscol,hcn,hs⟩ := hT x hx
    obtain ⟨⟨j,a,b,d⟩,hp,he⟩ := mem_image.mp hy
    have hp' : j ≠ i ∧ b ≠ d := by simpa [S] using hp
    have hval : (s.map v).sum-v (i,c)=
        (({(i,a),(j,b)} : Multiset (I × J)).map v).sum-v (j,d) := by
      simpa [code] using hs.symm.trans he.symm
    have hh := signed_multiset_inj hv i hsc (by simp : ({(i,a),(j,b)} : Multiset (I × J)).card=2)
      hscol (by simp) hcn hval
    exact hp'.1 (congrArg Prod.fst hh.1).symm
  have hh : (T ∪ S.image code).card ≤ Fintype.card G := card_le_univ _
  rw [card_union_of_disjoint hdis,hTc,card_image_of_injOn hi] at hh
  simpa [S,card_product,offDiag_card,Nat.mul_sub_left_distrib,mul_assoc] using hh

/-- The finite six-point example modulo 117 cannot be amplified past constant
one by replacing each tag with an equally sized compatible fibre. -/
lemma six_colour_no_gain [Fintype G] (q : ℕ) (hq : 2 ≤ q)
    (v : Fin 6 × Fin q → G) (hv : GoodFamily v) :
    (6*q)^3 ≤ 117*Fintype.card G := by
  have hb := cross_signed_packing v hv (0 : Fin 6)
  norm_num only [Fintype.card_fin,Nat.reduceSub] at hb
  have hq' : q ≤ 2*(q-1) := by omega
  have hh := Nat.mul_le_mul_left (5*q*q) hq'
  have hc : 5*q^3 ≤ 2*Fintype.card G := by nlinarith
  nlinarith [Nat.zero_le (Fintype.card G)]

/-- A fixed modular tag satisfying the elementary signed-triple packing bound
cannot yield an asymptotic gain through equally sized compatible fibres once
there are at least three colours. The explicit threshold `q ≥ 10` suffices. -/
lemma fixed_tag_no_gain [Fintype G] (k q m : ℕ) (hk : 3 ≤ k) (hq : 10 ≤ q)
    (hm : k*k.choose 2+k ≤ m)
    (v : Fin k × Fin q → G) (hv : GoodFamily v) :
    (k*q)^3 ≤ m*Fintype.card G := by
  have hb := full_signed_packing v hv ⟨0,by omega⟩
  simp only [Fintype.card_fin] at hb
  have hbR : (q : ℝ)*(q.choose 2 : ℝ)+
      ((k:ℝ)-1)*q*(q*((q:ℝ)-1)) ≤ Fintype.card G := by
    have hh : ((q*q.choose 2+(k-1)*q*(q*(q-1)) : ℕ) : ℝ) ≤ Fintype.card G :=
      Nat.cast_le.mpr hb
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ k),
      Nat.cast_sub (by omega : 1 ≤ q),Nat.cast_one] using hh
  have hmR : (k : ℝ)*(k.choose 2 : ℝ)+k ≤ m := by exact_mod_cast hm
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hqR : (10 : ℝ) ≤ q := by exact_mod_cast hq
  rw [Nat.cast_choose_two] at hbR hmR
  let K : ℝ := k
  let Q : ℝ := q
  let P : ℝ := K*(K^2-K+2)/2
  let R : ℝ := (K-1/2)*Q^2*(Q-1)
  have hP : P ≤ m := by dsimp [P,K]; nlinarith [hmR]
  have hR : R ≤ Fintype.card G := by dsimp [R,K,Q]; nlinarith [hbR]
  have hP0 : 0 ≤ P := by
    have : 0 ≤ K^2-K+2 := by dsimp [K]; nlinarith
    dsimp only [P]
    positivity
  have hR0 : 0 ≤ R := by
    have : 0 ≤ K-1/2 := by dsimp [K]; linarith
    have : 0 ≤ Q-1 := by dsimp [Q]; linarith
    dsimp only [R]
    positivity
  have haux : 0 ≤ (K-3)*(18*K^2-13*K+6)*(Q-1)+4*K^2*(Q-10) := by
    have h1 : 0 ≤ K-3 := by dsimp [K]; linarith
    have h2 : 0 ≤ 18*K^2-13*K+6 := by dsimp [K]; nlinarith
    have h3 : 0 ≤ Q-1 := by dsimp [Q]; linarith
    have h4 : 0 ≤ Q-10 := by dsimp [Q]; linarith
    positivity
  have hid : P*R-(K*Q)^3 = K*Q^2/36*
      ((K-3)*(18*K^2-13*K+6)*(Q-1)+4*K^2*(Q-10)) := by
    dsimp [P,R]
    ring
  have hlow : (K*Q)^3 ≤ P*R := by
    have hcoef : 0 ≤ K*Q^2/36 := by dsimp [K,Q]; positivity
    have hh := mul_nonneg hcoef haux
    rw [← hid] at hh
    linarith
  have hprod : P*R ≤ (m : ℝ)*Fintype.card G :=
    mul_le_mul hP hR hR0 (Nat.cast_nonneg m)
  have hh : ((k : ℝ)*q)^3 ≤ (m : ℝ)*Fintype.card G := hlow.trans hprod
  exact_mod_cast hh

lemma modular_tag_no_gain [Fintype G] (k q m : ℕ) [NeZero m]
    (hk : 3 ≤ k) (hq : 10 ≤ q) (tag : Fin k → ZMod m)
    (htag : Function.Injective (fun s : Sym (Fin k) 3 ↦ (s.val.map tag).sum))
    (v : Fin k × Fin q → G) (hv : GoodFamily v) :
    (k*q)^3 ≤ m*Fintype.card G := by
  have hm := ordinary_code_packing tag htag
  simp only [Fintype.card_fin,ZMod.card] at hm
  exact fixed_tag_no_gain k q m hk hq hm v hv

end ColouredPacking

/- Exact finite-set criteria for disproving the asymptotic assertion.
No family satisfying the criterion is constructed in this file. -/
open Finset Filter
open scoped Asymptotics
namespace CounterCriterion
open B3Aux

lemma card_le_f {N : ℕ} {A : Finset ℕ} (hAN : A ⊆ Icc 1 N) (hA : Good A) :
    A.card ≤ f N 3 := by
  classical
  unfold f
  exact le_sup (mem_filter.mpr ⟨mem_powerset.mpr hAN,hA⟩)

lemma maximizing_set (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ Good A ∧ A.card=f N 3 := by
  classical
  let C := (Icc 1 N).powerset.filter Good
  have hem : (∅ : Finset ℕ) ∈ C := by
    apply mem_filter.mpr
    refine ⟨mem_powerset.mpr (empty_subset _),?_⟩
    intro s t hs ht hsm htm he
    obtain ⟨x,hx⟩ := Multiset.card_pos_iff_exists_mem.mp (show 0 < s.card by omega)
    exact False.elim (by simpa using hsm x hx)
  obtain ⟨A,hAC,hmax⟩ := exists_mem_eq_sup C ⟨∅,hem⟩ card
  obtain ⟨hAN,hA⟩ := mem_filter.mp hAC
  exact ⟨A,mem_powerset.mp hAN,hA,hmax.symm⟩

lemma ratio_cube (N : ℕ) :
    ((f N 3 : ℝ)/(N : ℝ)^((1 : ℝ)/3))^3 = (f N 3 : ℝ)^3/N := by
  rw [div_pow]
  congr 1
  simpa [one_div] using Real.rpow_inv_natCast_pow (x := (N : ℝ)) (n := 3)
    (Nat.cast_nonneg N) (by decide)

lemma target_iff_cube_upper :
    ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3))) ↔
      ∀ c : ℝ, 1 < c → ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < c := by
  constructor
  · intro h c hc
    have ht := (target_iff_ratio.mp h).pow 3
    simp only [ratio_cube,one_pow] at ht
    exact ht.eventually_lt_const hc
  · intro h
    apply target_iff_sharp_upper.mpr
    intro c hc
    have hc0 : 0 ≤ c := by linarith
    have hc3 : 1 < c^3 := by nlinarith [sq_nonneg (c-1)]
    filter_upwards [h (c^3) hc3] with N hN
    rw [← ratio_cube] at hN
    by_contra hn
    have hh := pow_le_pow_left₀ hc0 (le_of_not_gt hn) 3
    linarith

lemma negation_iff_frequent_cube_gain :
    (¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3)))) ↔
      ∃ c : ℝ, 1 < c ∧ ∃ᶠ N : ℕ in atTop, c ≤ (f N 3 : ℝ)^3/N := by
  rw [target_iff_cube_upper]
  push_neg
  rfl

lemma negation_iff_integer_gain :
    (¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3)))) ↔
      ∃ k : ℕ, 1 ≤ k ∧ ∀ B : ℕ, ∃ N : ℕ,
        B ≤ N ∧ 1 ≤ N ∧ (k+1)*N ≤ k*(f N 3)^3 := by
  constructor
  · intro hn
    obtain ⟨c,hc,hfreq⟩ := negation_iff_frequent_cube_gain.mp hn
    obtain ⟨l,hl⟩ := exists_nat_one_div_lt (sub_pos.mpr hc)
    let k := l+1
    have hk : 0 < (k : ℝ) := by dsimp [k]; positivity
    have hkc : (k : ℝ)+1 < k*c := by
      have hh := (div_lt_iff₀ (by positivity : (0 : ℝ) < (l:ℝ)+1)).mp hl
      dsimp [k]
      push_cast
      nlinarith
    refine ⟨k,by dsimp [k]; omega,fun B ↦ ?_⟩
    obtain ⟨N,hBN,hN⟩ := frequently_atTop.mp
      (hfreq.and_eventually (eventually_ge_atTop (1 : ℕ))) B
    refine ⟨N,hBN,hN.2,?_⟩
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hh := (le_div_iff₀ hNp).mp hN.1
    have h1 := mul_le_mul_of_nonneg_left hh hk.le
    have h2 := mul_le_mul_of_nonneg_right hkc.le hNp.le
    have hR : ((k : ℝ)+1)*N ≤ k*(f N 3 : ℝ)^3 := by nlinarith [h1,h2]
    exact_mod_cast hR
  · rintro ⟨k,hk,hfam⟩ htarget
    have hkR : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
    have hc : 1 < 1+1/(k : ℝ) := by
      have hh := one_div_pos.mpr hkR
      linarith
    obtain ⟨B,hB⟩ := eventually_atTop.mp (target_iff_cube_upper.mp htarget _ hc)
    obtain ⟨N,hBN,hN,hgain⟩ := hfam B
    have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hh := (div_lt_iff₀ hNp).mp (hB N hBN)
    have hh' := mul_lt_mul_of_pos_left hh hkR
    have hgainR : ((k : ℝ)+1)*N ≤ k*(f N 3 : ℝ)^3 := by exact_mod_cast hgain
    have he : (k : ℝ)*((1+1/(k:ℝ))*N) = ((k:ℝ)+1)*N := by field_simp
    rw [he] at hh'
    exact (not_lt_of_ge hgainR) hh'

lemma negation_iff_dense_sets :
    (¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3)))) ↔
      ∃ k : ℕ, 1 ≤ k ∧ ∀ B : ℕ, ∃ N : ℕ, ∃ A : Finset ℕ,
        B ≤ N ∧ 1 ≤ N ∧ A ⊆ Icc 1 N ∧ Good A ∧ (k+1)*N ≤ k*A.card^3 := by
  rw [negation_iff_integer_gain]
  constructor
  · rintro ⟨k,hk,hfam⟩
    refine ⟨k,hk,fun B ↦ ?_⟩
    obtain ⟨N,hBN,hN,hgain⟩ := hfam B
    obtain ⟨A,hAN,hA,hcard⟩ := maximizing_set N
    exact ⟨N,A,hBN,hN,hAN,hA,by simpa [hcard] using hgain⟩
  · rintro ⟨k,hk,hfam⟩
    refine ⟨k,hk,fun B ↦ ?_⟩
    obtain ⟨N,A,hBN,hN,hAN,hA,hgain⟩ := hfam B
    exact ⟨N,hBN,hN,hgain.trans (Nat.mul_le_mul_left k
      (Nat.pow_le_pow_left (card_le_f hAN hA) 3))⟩

/-- A cyclic B₃ code gives an integer B₃ set in an interval of the same size. -/
lemma set_of_cyclic_code {J : Type*} [Fintype J] [Nonempty J]
    (m : ℕ) [NeZero m] (v : J → ZMod m)
    (hv : Function.Injective (fun s : Sym J 3 ↦ (s.val.map v).sum)) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 m ∧ A.card=Fintype.card J ∧ Good A := by
  let code : J → ℕ := fun a ↦ (v a).val+1
  have hi : Function.Injective code := by
    intro a b he
    have hab : v a=v b := ZMod.val_injective m (Nat.add_right_cancel he)
    have hh := hv (a₁ := ⟨{a,a,a},by simp⟩) (a₂ := ⟨{b,b,b},by simp⟩)
      (by simp [hab])
    have hh' : ({a,a,a} : Multiset J) = {b,b,b} := congrArg Subtype.val hh
    have hm : a ∈ ({b,b,b} : Multiset J) := hh' ▸ (by simp)
    simpa using hm
  have hb (a : J) : 1 ≤ code a ∧ code a ≤ m := by
    have hh := ZMod.val_lt (v a)
    dsimp [code]
    omega
  have sumcode (s : Multiset J) :
      ((s.map code).sum : ZMod m) = (s.map v).sum+(s.card : ZMod m) := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,
        Nat.cast_add,Nat.cast_one,ih]
      simp [code,add_assoc,add_left_comm,add_comm]
  have hs (s t : Multiset J) (hsc : s.card=3) (htc : t.card=3)
      (he : (s.map code).sum=(t.map code).sum) : s=t := by
    have hh := congrArg (fun n : ℕ ↦ (n : ZMod m)) he
    dsimp only at hh
    rw [sumcode,sumcode,hsc,htc] at hh
    exact congrArg Subtype.val (hv (a₁ := ⟨s,hsc⟩) (a₂ := ⟨t,htc⟩)
      (add_right_cancel hh))
  exact BoseConstruction.exists_set_of_code m 3 code hi hb hs

/-- A fixed cubic gain in arbitrarily large cyclic groups would suffice for
an actual disproof. This theorem does not construct such codes. -/
lemma not_target_of_cyclic_gain (k : ℕ) (hk : 1 ≤ k)
    (hfam : ∀ B : ℕ, ∃ m n : ℕ, B ≤ m ∧ 1 ≤ m ∧ 0 < n ∧
      ∃ v : Fin n → ZMod m,
        Function.Injective (fun s : Sym (Fin n) 3 ↦ (s.val.map v).sum) ∧
          (k+1)*m ≤ k*n^3) :
    ¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3))) := by
  apply negation_iff_dense_sets.mpr
  refine ⟨k,hk,fun B ↦ ?_⟩
  obtain ⟨m,n,hBm,hm,hn,v,hv,hgain⟩ := hfam B
  haveI : NeZero m := ⟨by omega⟩
  haveI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨A,hAm,hcard,hA⟩ := set_of_cyclic_code m v hv
  refine ⟨m,A,hBm,hm,hAm,hA,?_⟩
  simpa only [hcard,Fintype.card_fin] using hgain

/-- The excess in the standard Bose--Chowla examples is only a vanishing
lower-order term: a fixed cubic gain bounds the parameter. -/
lemma bose_gain_parameter_bound (k p : ℕ) (hp : 0 < p)
    (hgain : (k+1)*(p^3-1) ≤ k*p^3) : p^3 ≤ k+1 := by
  have hp3 : 1 ≤ p^3 := by have hh := pow_pos hp 3; omega
  have hsplit : p^3=(p^3-1)+1 := by omega
  have hh : k*p^3=k*(p^3-1)+k := by
    calc
      _ = k*((p^3-1)+1) := congrArg (fun x ↦ k*x) hsplit
      _ = _ := by ring
  rw [Nat.add_mul,Nat.one_mul,hh] at hgain
  omega

end CounterCriterion

/- A conditional route from compatible two-colour fibres to a counterexample.
The required asymptotic family is not constructed here. -/
open Finset Filter
open scoped Asymptotics
namespace TwoColourLift
open ColouredPacking

lemma product_code_injective {I J G H : Type*} [AddCommGroup G] [AddCommGroup H]
    (tag : I → H)
    (htag : Function.Injective (fun s : Sym I 3 ↦ (s.val.map tag).sum))
    (v : I × J → G) (hv : GoodFamily v) :
    Function.Injective (fun s : Sym (I × J) 3 ↦
      (s.val.map (fun p ↦ (tag p.1,v p))).sum) := by
  let w : I × J → H × G := fun p ↦ (tag p.1,v p)
  have hfst (s : Multiset (I × J)) :
      ((s.map w).sum).1 = ((s.map Prod.fst).map tag).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih => simpa [w] using congrArg (fun x ↦ tag a.1+x) ih
  have hsnd (s : Multiset (I × J)) : ((s.map w).sum).2 = (s.map v).sum := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih => simpa [w] using congrArg (fun x ↦ v a+x) ih
  intro s t he
  have h₁ := congrArg Prod.fst he
  have h₂ := congrArg Prod.snd he
  change ((s.val.map w).sum).1 = ((t.val.map w).sum).1 at h₁
  change ((s.val.map w).sum).2 = ((t.val.map w).sum).2 at h₂
  rw [hfst,hfst] at h₁
  rw [hsnd,hsnd] at h₂
  have hcol := congrArg Subtype.val (htag
    (a₁ := ⟨s.val.map Prod.fst,by simp⟩) (a₂ := ⟨t.val.map Prod.fst,by simp⟩) h₁)
  exact Sym.ext (multiset_inj hv s.val t.val s.property t.property hcol h₂)

/-- The two colours 0 and 1 have distinct three-element multiset sums modulo 4. -/
lemma binary_tag_injective : Function.Injective
    (fun s : Sym (Fin 2) 3 ↦ (s.val.map (fun i ↦ (i.val : ZMod 4))).sum) := by
  decide

lemma integer_set_of_two_colour_fibres (m q : ℕ) (hm : Odd m) (hq : 0 < q)
    (v : Fin 2 × Fin q → ZMod m) (hv : GoodFamily v) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (4*m) ∧ A.card=2*q ∧ B3Aux.Good A := by
  have hcop : Nat.Coprime 4 m := by
    simpa using (Nat.coprime_two_left.mpr hm).pow_left 2
  have hm0 : m ≠ 0 := by intro he; simp [he] at hm
  haveI : NeZero (4*m) := ⟨by omega⟩
  haveI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  let e := ZMod.chineseRemainder hcop
  let w : Fin 2 × Fin q → ZMod 4 × ZMod m := fun p ↦ (p.1.val,v p)
  have hw : Function.Injective (fun s : Sym (Fin 2 × Fin q) 3 ↦ (s.val.map w).sum) :=
    product_code_injective (fun i : Fin 2 ↦ (i.val : ZMod 4)) binary_tag_injective v hv
  let code : Fin 2 × Fin q → ZMod (4*m) := fun p ↦ e.symm (w p)
  have hcode : Function.Injective
      (fun s : Sym (Fin 2 × Fin q) 3 ↦ (s.val.map code).sum) := by
    intro s t he
    apply hw
    have hh := congrArg e he
    simpa [map_multiset_sum,Multiset.map_map,code,Function.comp_def] using hh
  obtain ⟨A,hAN,hcard,hA⟩ := CounterCriterion.set_of_cyclic_code (4*m) code hcode
  exact ⟨A,hAN,by simpa only [Fintype.card_prod,Fintype.card_fin] using hcard,hA⟩

/-- This is a sufficient condition for disproving the original conjecture.
Its hypothesis requires arbitrarily large fibres with a fixed gain below 2q³. -/
lemma not_target_of_two_colour_gain (k : ℕ) (hk : 1 ≤ k)
    (hfam : ∀ B : ℕ, ∃ m q : ℕ, B ≤ q ∧ 0 < q ∧ Odd m ∧
      ∃ v : Fin 2 × Fin q → ZMod m, GoodFamily v ∧ (k+1)*m ≤ 2*k*q^3) :
    ¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3))) := by
  apply CounterCriterion.negation_iff_dense_sets.mpr
  refine ⟨k,hk,fun B ↦ ?_⟩
  obtain ⟨m,q,hBq,hq,hm,v,hv,hgain⟩ := hfam B
  obtain ⟨A,hAN,hcard,hA⟩ := integer_set_of_two_colour_fibres m q hm hq v hv
  have hm0 : m ≠ 0 := by intro he; simp [he] at hm
  haveI : NeZero m := ⟨hm0⟩
  have hbound := one_colour_packing v hv (0 : Fin 2)
  simp only [Fintype.card_fin,ZMod.card] at hbound
  refine ⟨4*m,A,by omega,by omega,hAN,hA,?_⟩
  rw [hcard]
  nlinarith only [hgain]

end TwoColourLift

/- Additional local graph constraints; these do not settle the asymptotic bound. -/

open Finset
namespace DifferenceGraph
open B3Aux

/-- A point outside a translate of the original clique has at most two
neighbors in that clique. -/
lemma outside_clique_neighbors {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A, x ≠ (a : ℤ)) :
    ((A.image (fun a : ℕ ↦ (a : ℤ))) ∩ neighbors A x).card ≤ 2 := by
  classical
  let S := (A.image (fun a : ℕ ↦ (a : ℤ))) ∩ neighbors A x
  by_cases hn : S.Nonempty
  · obtain ⟨a',ha'⟩ := hn
    obtain ⟨a,ha,rfl⟩ := mem_image.mp (mem_inter.mp ha').1
    obtain ⟨u,hu,v,hv,huv,he⟩ := (mem_neighbors.mp (mem_inter.mp ha').2)
    have hxa : x=(a : ℤ)+u-v := by omega
    have hva : v ≠ a := by intro h; apply hx u hu; omega
    have hvu : v ≠ u := huv.symm
    have hsub : S ⊆ {(a : ℤ),(u : ℤ)} := by
      intro b' hb'
      obtain ⟨b,hb,rfl⟩ := mem_image.mp (mem_inter.mp hb').1
      obtain ⟨w,hw,z,hz,hwz,he'⟩ := mem_neighbors.mp (mem_inter.mp hb').2
      have hs : a+u+z=b+w+v := by omega
      have hm := three_sum_mem hA hv hb hw ha hu hz (show v+b+w=a+u+z by omega)
      rcases hm with h | h | h
      · exact (hva h).elim
      · exact (hvu h).elim
      · have hp : b+w=a+u := by omega
        rcases two_sum_mem hA hb hw ha hu hp with h | h <;> simp [h]
    exact (card_le_card hsub).trans card_le_two
  · have he : S=∅ := not_nonempty_iff_eq_empty.mp hn
    change S.card ≤ 2
    simp [he]

/-- In the common-neighbor graph of two distinct nonadjacent points, an
adjacent common neighbor is one of the two switches of the original pairs. -/
lemma common_neighbor_switch {A : Finset ℕ} (hA : Good A)
    {δ y : ℤ} (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d)
    (hrep : (a : ℤ)-b-δ=(c : ℤ)-d)
    (hy0 : (graph A).Adj 0 y) (hyδ : (graph A).Adj δ y)
    (hxy : (graph A).Adj ((a : ℤ)-b) y) :
    y=(a : ℤ)-c ∨ y=(d : ℤ)-b := by
  have hac : a ≠ c := by
    intro he
    have hdb : d ≠ b := by intro h; apply hδ; omega
    apply hno
    exact (adj_zero_iff A δ).mpr ⟨d,hd,b,hb,hdb,by omega⟩
  have hbd : b ≠ d := by
    intro he
    apply hno
    exact (adj_zero_iff A δ).mpr ⟨a,ha,c,hc,hac,by omega⟩
  obtain ⟨a',ha',b',hb',hab',hy⟩ := (adj_zero_iff A y).mp hy0
  obtain ⟨c',hc',d',hd',hcd',hy'⟩ := (graph A).symm hyδ
  have hL : (a=a' ∧ b≠b') ∨ (b=b' ∧ a≠a') := by
    apply (local_adj_iff hA ha hb ha' hb' hab hab').mp
    simpa only [hy] using hxy
  have hR : (c=c' ∧ d≠d') ∨ (d=d' ∧ c≠c') := by
    apply (local_adj_iff hA hc hd hc' hd' hcd hcd').mp
    obtain ⟨u,hu,v,hv,huv,he⟩ := hxy
    exact ⟨u,hu,v,hv,huv,by omega⟩
  rcases hL with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩ <;>
    rcases hR with ⟨h₃,h₄⟩ | ⟨h₃,h₄⟩
  · have hh := difference_inj hA hb hd hb' hd' hbd
      (show (b : ℤ)-d=(b' : ℤ)-d' by omega)
    exact (h₂ hh.1).elim
  · have hs : b+c=b'+c' := by omega
    rcases two_sum_mem hA hb hc hb' hc' hs with he | he
    · exact (h₂ he).elim
    · exact Or.inl (by omega)
  · have hs : a+d=a'+d' := by omega
    rcases two_sum_mem hA ha hd ha' hd' hs with he | he
    · exact (h₂ he).elim
    · exact Or.inr (by omega)
  · have hh := difference_inj hA ha hc ha' hc' hac
      (show (a : ℤ)-c=(a' : ℤ)-c' by omega)
    exact (h₂ hh.1).elim

/-- Every vertex in the common-neighbor graph of distinct nonadjacent
points has degree at most two. -/
lemma common_neighbor_degree_le_two {A : Finset ℕ} (hA : Good A)
    {δ x : ℤ} (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    (hx0 : (graph A).Adj 0 x) (hxδ : (graph A).Adj δ x) :
    (neighbors A 0 ∩ neighbors A δ ∩ neighbors A x).card ≤ 2 := by
  classical
  obtain ⟨a,ha,b,hb,hab,hx⟩ := (adj_zero_iff A x).mp hx0
  obtain ⟨c,hc,d,hd,hcd,hx'⟩ := (graph A).symm hxδ
  have hsub : neighbors A 0 ∩ neighbors A δ ∩ neighbors A x ⊆
      {((a : ℤ)-c),((d : ℤ)-b)} := by
    intro y hy
    have hy0 := mem_neighbors.mp (mem_inter.mp (mem_inter.mp hy).1).1
    have hyδ := mem_neighbors.mp (mem_inter.mp (mem_inter.mp hy).1).2
    have hxy := mem_neighbors.mp (mem_inter.mp hy).2
    have hs := common_neighbor_switch hA hδ hno ha hb hc hd hab hcd
      (show (a : ℤ)-b-δ=(c : ℤ)-d by omega) hy0 hyδ
      (by simpa only [hx] using hxy)
    simpa only [mem_insert,mem_singleton] using hs
  exact (card_le_card hsub).trans card_le_two

end DifferenceGraph


/- A sharper explicit finite-mode upper bound. This is not the sharp
asymptotic constant asked for in Erdős problem 241. -/

open Finset Filter
namespace CosineBound

noncomputable def reciprocalTerm (j : ℕ) : ℝ := 1/(4*(j : ℝ)+3)^2

noncomputable def tailPotential (j : ℕ) : ℝ :=
  1/(4*(4*(j : ℝ)+3)) + 1/(2*(4*(j : ℝ)+3)^2)

lemma tailPotential_step (j : ℕ) :
    tailPotential j - tailPotential (j+1) ≤ reciprocalTerm j := by
  let x : ℝ := 4*(j : ℝ)+3
  have hx : 0 < x := by dsimp [x]; positivity
  have hx4 : 0 < x+4 := by positivity
  have he : tailPotential j - tailPotential (j+1) =
      reciprocalTerm j - 8/(x^2*(x+4)^2) := by
    have hj : 4*((j+1 : ℕ) : ℝ)+3=x+4 := by dsimp [x]; push_cast; ring
    simp only [tailPotential,reciprocalTerm,hj]
    change 1/(4*x)+1/(2*x^2) - (1/(4*(x+4))+1/(2*(x+4)^2)) =
      1/x^2-8/(x^2*(x+4)^2)
    field_simp
    ring
  rw [he]
  have : 0 ≤ 8/(x^2*(x+4)^2) := by positivity
  linarith

lemma reciprocal_sum_lower (K N : ℕ) (hKN : K ≤ N) :
    (∑ j ∈ range K, reciprocalTerm j) + tailPotential K - tailPotential N ≤
      ∑ j ∈ range N, reciprocalTerm j := by
  induction N, hKN using Nat.le_induction with
  | base => linarith
  | succ N hKN ih =>
    rw [sum_range_succ]
    have hs := tailPotential_step N
    linarith

set_option maxHeartbeats 3000000 in
lemma sixty_four_reciprocal_terms :
    (1578947349 : ℝ)/10000000000 < ∑ j ∈ range 64, reciprocalTerm j := by
  norm_num [reciprocalTerm,sum_range_succ]

lemma million_reciprocal_terms :
    (15886737 : ℝ)/100000000 < ∑ j ∈ range 1000000, reciprocalTerm j := by
  have hs := sixty_four_reciprocal_terms
  have ht := reciprocal_sum_lower 64 1000000 (by norm_num)
  have hp : (9726351 : ℝ)/10000000000 < tailPotential 64-tailPotential 1000000 := by
    norm_num [tailPotential]
  linarith

lemma coefficient_sum_factor (N : ℕ) :
    (∑ j ∈ range N, (coeff j)^2) = (16/Real.pi^2)*∑ j ∈ range N, reciprocalTerm j := by
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  dsimp [coeff,reciprocalTerm]
  field_simp
  norm_num

lemma million_modes_strict :
    2*denominatorLimit (range 1000000) < (348491 : ℝ)/100000 := by
  have hs := million_reciprocal_terms
  have hp2 : Real.pi^2 < (986961 : ℝ)/100000 := by
    nlinarith [Real.pi_pos,Real.pi_lt_d6]
  have hs' : (51509 : ℝ)/200000 < ∑ j ∈ range 1000000, (coeff j)^2 := by
    rw [coefficient_sum_factor,div_mul_eq_mul_div]
    apply (lt_div_iff₀ (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith
  dsimp [denominatorLimit]
  linarith

end CosineBound

lemma f_cube_ratio_eventually_lt_refined_cosine_bound :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < (348491 : ℝ)/100000 :=
  f_cube_ratio_eventually_lt_cosine_bound (range 1000000) (348491/100000)
    CosineBound.million_modes_strict

lemma f_cube_ratio_eventually_lt_349_100 :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < (349 : ℝ)/100 := by
  filter_upwards [f_cube_ratio_eventually_lt_refined_cosine_bound] with N hN
  exact hN.trans (by norm_num)

/- A barrier for a class of auxiliary weights; not a claim about the
extremal B₃ function itself. -/
open Finset intervalIntegral
namespace CosineBound

lemma tent_cos_integral_nonneg (θ : ℝ) :
    0 ≤ ∫ x in (0 : ℝ)..1, (1-x)*Real.cos (θ*x) := by
  by_cases hθ : θ=0
  · subst θ
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    simp only [zero_mul,Real.cos_zero,mul_one]
    exact sub_nonneg.mpr hx.2
  · have hd (x : ℝ) :
        HasDerivAt (fun x : ℝ ↦ (1-x)*Real.sin (θ*x)/θ - Real.cos (θ*x)/θ^2)
          ((1-x)*Real.cos (θ*x)) x := by
      have hsin := ((hasDerivAt_id x).const_mul θ).sin
      have hcos := ((hasDerivAt_id x).const_mul θ).cos
      have h := (((hasDerivAt_const x (1 : ℝ)).sub (hasDerivAt_id x)).mul hsin).div_const θ
      have hh := h.sub (hcos.div_const (θ^2))
      convert hh using 1; simp only [mul_one,zero_sub, Pi.sub_apply, id_eq]
      field_simp
      ring
    have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun x _ ↦ hd x)
      (((continuous_const.sub continuous_id).mul
        (Real.continuous_cos.comp (continuous_const.mul continuous_id))).intervalIntegrable _ _)
    have hv : (∫ x in (0 : ℝ)..1, (1-x)*Real.cos (θ*x)) =
        (1-Real.cos θ)/θ^2 := by
      rw [hi]
      simp
      ring
    rw [hv]
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one θ)) (sq_nonneg θ)

lemma tent_integral : (∫ x in (0 : ℝ)..1, (1-x)) = (1 : ℝ)/2 := by
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun x : ℝ ↦ x)
    (continuous_const.intervalIntegrable _ _) (continuous_id.intervalIntegrable _ _)]
  norm_num

lemma tent_square_integral : (∫ x in (0 : ℝ)..1, (1-x)^2) = (1 : ℝ)/3 := by
  have he : (fun x : ℝ ↦ (1-x)^2) = (fun x : ℝ ↦ 1-2*x+x^2) := by
    funext x
    ring
  rw [he,intervalIntegral.integral_add (f := fun x : ℝ ↦ 1-2*x) (g := fun x : ℝ ↦ x^2)
    ((continuous_const.sub (continuous_const.mul continuous_id)).intervalIntegrable _ _)
    ((continuous_id.pow 2).intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun _ : ℝ ↦ (1 : ℝ)) (g := fun x : ℝ ↦ 2*x) (continuous_const.intervalIntegrable _ _)
      ((continuous_const.mul continuous_id).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul]
  norm_num

lemma cosineWeight_continuous {ι : Type*} (T : Finset ι) (c θ : ι → ℝ) :
    Continuous (cosineWeight T c θ) := by
  unfold cosineWeight
  fun_prop

lemma cosineWeight_even {ι : Type*} (T : Finset ι) (c θ : ι → ℝ) (x : ℝ) :
    cosineWeight T c θ (-x) = cosineWeight T c θ x := by
  simp [cosineWeight,mul_neg,Real.cos_neg]

lemma cosineWeight_tent_integral {ι : Type*} (T : Finset ι) (c θ : ι → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    (1 : ℝ)/2 ≤ ∫ x in (0 : ℝ)..1, cosineWeight T c θ x*(1-x) := by
  have he : (fun x : ℝ ↦ cosineWeight T c θ x*(1-x)) =
      (fun x : ℝ ↦ (1-x)+∑ i ∈ T, c i*((1-x)*Real.cos (θ i*x))) := by
    funext x
    simp only [cosineWeight,add_mul,one_mul,sum_mul]
    congr 1
    apply sum_congr rfl
    intro i hi
    ring
  rw [he,intervalIntegral.integral_add (f := fun x : ℝ ↦ 1-x)
    (g := fun x : ℝ ↦ ∑ i ∈ T, c i*((1-x)*Real.cos (θ i*x)))
    ((continuous_const.sub continuous_id).intervalIntegrable _ _)
    (by exact Continuous.intervalIntegrable (by fun_prop) _ _),tent_integral,
    intervalIntegral.integral_finset_sum (fun i _ ↦ (by exact Continuous.intervalIntegrable (by fun_prop) _ _))]
  have hh : 0 ≤ ∑ i ∈ T, ∫ x in (0 : ℝ)..1, c i*((1-x)*Real.cos (θ i*x)) := by
    apply sum_nonneg
    intro i hi
    rw [intervalIntegral.integral_const_mul]
    exact mul_nonneg (hc i hi) (tent_cos_integral_nonneg (θ i))
  linarith

lemma cosineWeight_half_square_integral {ι : Type*} (T : Finset ι) (c θ : ι → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    (3 : ℝ)/4 ≤ ∫ x in (0 : ℝ)..1, (cosineWeight T c θ x)^2 := by
  have hcont := cosineWeight_continuous T c θ
  have hh := intervalIntegral.integral_nonneg_of_forall (a := (0 : ℝ)) (b := 1) (μ := MeasureTheory.volume) (by norm_num)
    (fun x ↦ sq_nonneg (cosineWeight T c θ x-(3/2)*(1-x)))
  have he : (fun x : ℝ ↦ (cosineWeight T c θ x-(3/2)*(1-x))^2) =
      (fun x : ℝ ↦ (cosineWeight T c θ x)^2 -
        3*(cosineWeight T c θ x*(1-x))+(9/4)*(1-x)^2) := by
    funext x
    ring
  rw [he,intervalIntegral.integral_add
    (f := fun x : ℝ ↦ (cosineWeight T c θ x)^2-3*(cosineWeight T c θ x*(1-x)))
    (g := fun x : ℝ ↦ (9/4)*(1-x)^2)
    (((hcont.pow 2).sub (continuous_const.mul
      (hcont.mul (continuous_const.sub continuous_id)))).intervalIntegrable _ _)
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).intervalIntegrable _ _),
    intervalIntegral.integral_sub (f := fun x : ℝ ↦ (cosineWeight T c θ x)^2)
      (g := fun x : ℝ ↦ 3*(cosineWeight T c θ x*(1-x))) ((hcont.pow 2).intervalIntegrable _ _)
      ((continuous_const.mul (hcont.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,tent_square_integral] at hh
  have ht := cosineWeight_tent_integral T c θ hc
  linarith

lemma cosineWeight_square_integral_barrier {ι : Type*} (T : Finset ι) (c θ : ι → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    (3 : ℝ)/2 ≤ ∫ x in (-1 : ℝ)..1, (cosineWeight T c θ x)^2 := by
  have hcont := (cosineWeight_continuous T c θ).pow 2
  have hs : (∫ x in (-1 : ℝ)..0, (cosineWeight T c θ x)^2) =
      (∫ x in (0 : ℝ)..1, (cosineWeight T c θ x)^2) := by
    have hn := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := 1)
      (f := fun x : ℝ ↦ (cosineWeight T c θ x)^2)
    simpa only [cosineWeight_even,neg_zero] using hn.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hcont.intervalIntegrable (-1) 0) (hcont.intervalIntegrable _ _),hs]
  have hh := cosineWeight_half_square_integral T c θ hc
  linarith

lemma cosine_symmetric_integral (θ : ℝ) :
    (∫ x in (-1 : ℝ)..1, Real.cos (θ*x)) = 2*Real.sinc θ := by
  by_cases hθ : θ=0
  · subst θ
    norm_num
  · have hh := intervalIntegral.mul_integral_comp_mul_left (f := Real.cos) (a := (-1 : ℝ)) (b := 1) θ
    rw [integral_cos] at hh
    simp only [mul_neg_one,mul_one,Real.sin_neg,sub_neg_eq_add] at hh
    rw [Real.sinc_of_ne_zero hθ]
    apply (mul_left_cancel₀ hθ)
    field_simp
    linarith

lemma cosine_product_symmetric_integral (a b : ℝ) :
    (∫ x in (-1 : ℝ)..1, Real.cos (a*x)*Real.cos (b*x)) =
      Real.sinc (a-b)+Real.sinc (a+b) := by
  have he : (fun x : ℝ ↦ Real.cos (a*x)*Real.cos (b*x)) =
      (fun x : ℝ ↦ (1/2)*(Real.cos ((a-b)*x)+Real.cos ((a+b)*x))) := by
    funext x
    simp only [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  rw [he,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (f := fun x : ℝ ↦ Real.cos ((a-b)*x))
      (g := fun x : ℝ ↦ Real.cos ((a+b)*x))
      (by exact Continuous.intervalIntegrable (by fun_prop) _ _)
      (by exact Continuous.intervalIntegrable (by fun_prop) _ _),
    cosine_symmetric_integral,cosine_symmetric_integral]
  ring

lemma cosineWeight_square_integral_eq {ι : Type*} (T : Finset ι) (c θ : ι → ℝ) :
    (∫ x in (-1 : ℝ)..1, (cosineWeight T c θ x)^2) =
      2+4*(∑ i ∈ T, c i*Real.sinc (θ i))+
        ∑ i ∈ T, ∑ j ∈ T, c i*c j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)) := by
  have he : (fun x ↦ (cosineWeight T c θ x)^2) = (fun x ↦
      (1+2*(∑ i ∈ T, c i*Real.cos (θ i*x)))+
        ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x))) := by
    funext x
    dsimp only [cosineWeight]
    rw [add_sq]
    have hp : (∑ i ∈ T, c i*Real.cos (θ i*x))^2 =
        ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)) := by
      rw [pow_two,mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    rw [hp]
    ring
  rw [he,intervalIntegral.integral_add
    (f := fun x : ℝ ↦ 1+2*(∑ i ∈ T, c i*Real.cos (θ i*x)))
    (g := fun x : ℝ ↦ ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)))
    (by exact Continuous.intervalIntegrable (by fun_prop) _ _)
    (by exact Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_add (f := fun _ : ℝ ↦ (1 : ℝ))
      (g := fun x : ℝ ↦ 2*(∑ i ∈ T, c i*Real.cos (θ i*x)))
      (continuous_const.intervalIntegrable _ _)
      (by exact Continuous.intervalIntegrable (by fun_prop) _ _),
    intervalIntegral.integral_const_mul]
  have hi₁ := intervalIntegral.integral_finset_sum (a := (-1 : ℝ)) (b := 1) (μ := MeasureTheory.volume) (s := T)
    (f := fun i x ↦ c i*Real.cos (θ i*x))
    (fun i hi ↦ (by exact Continuous.intervalIntegrable (by fun_prop) _ _))
  have hi₂ := intervalIntegral.integral_finset_sum (a := (-1 : ℝ)) (b := 1) (μ := MeasureTheory.volume) (s := T)
    (f := fun i x ↦ ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)))
    (fun i hi ↦ (by exact Continuous.intervalIntegrable (by fun_prop) _ _))
  have hi₃ (i : ι) := intervalIntegral.integral_finset_sum (a := (-1 : ℝ)) (b := 1) (μ := MeasureTheory.volume) (s := T)
    (f := fun j x ↦ (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)))
    (fun j hj ↦ (by exact Continuous.intervalIntegrable (by fun_prop) _ _))
  rw [hi₁,hi₂]
  simp only [hi₃, intervalIntegral.integral_const_mul, cosine_symmetric_integral,
    cosine_product_symmetric_integral, intervalIntegral.integral_const, sub_neg_eq_add,
    smul_eq_mul, mul_one]
  have hsum : (∑ i ∈ T, c i*(2*Real.sinc (θ i))) =
      2*∑ i ∈ T, c i*Real.sinc (θ i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hsum]
  ring

/-- For any nonnegative finite collection of cosine modes, the cube-ratio
coefficient in this energy method is at least three. This says nothing about
whether the actual extremal cube ratio is below three. -/
lemma arbitrary_positive_modes_barrier {ι : Type*} (T : Finset ι) (c θ : ι → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    (3 : ℝ) ≤ 2*(2+4*(∑ i ∈ T, c i*Real.sinc (θ i))+
      ∑ i ∈ T, ∑ j ∈ T, c i*c j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j))) := by
  rw [← cosineWeight_square_integral_eq]
  have hh := cosineWeight_square_integral_barrier T c θ hc
  linarith

end CosineBound

/- Real-variable optimization for non-uniform coloured packing.
This file does not prove the Erdős conjecture. -/
namespace WeightedPacking

/-- The half-cubic packing expression is minimized by balanced weights.
The hypothesis on `s` is the Cauchy bound on all weights other than the largest. -/
lemma balanced_bound (k n t s : ℝ) (hk : 2 ≤ k) (hn : 0 ≤ n)
    (ht : 0 ≤ t) (hmax : n ≤ k*t)
    (hs : (k-1)*t^2+(n-t)^2 ≤ (k-1)*s) :
    (k-1/2)*n^3 ≤ k^3*(t*s-t^3/2) := by
  let r := k*t-n
  have hr : 0 ≤ r := by dsimp [r]; linarith
  have hcoef : 0 ≤ 8*k^2-21*k+11 := by
    nlinarith [sq_nonneg (k-2)]
  have hquad : 0 ≤ (k+1)*r^2+(3-k)*n*r+(k-1)*(2*k-3)*n^2 := by
    have h1 := mul_nonneg (show 0 ≤ k+1 by linarith) (sq_nonneg (r-n/2))
    have h2 := mul_nonneg (mul_nonneg hn hr) (show (0:ℝ) ≤ 4 by norm_num)
    have h3 := mul_nonneg hcoef (sq_nonneg n)
    nlinarith
  have hprod := mul_nonneg hr hquad
  have hid : r*((k+1)*r^2+(3-k)*n*r+(k-1)*(2*k-3)*n^2) =
      k^3*(t*((k-1)*t^2+(n-t)^2)*2-(k-1)*t^3) -
        (k-1)*(2*k-1)*n^3 := by dsimp [r]; ring
  rw [hid] at hprod
  have hmul := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*k^3*t by positivity)
  have hres : 0 ≤ (k-1)*(k^3*(t*s-t^3/2)-(k-1/2)*n^3) := by
    nlinarith [hmul]
  have hk1 : 0 < k-1 := by linarith
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hk1).mp hres)

/-- The elementary lower bound for a B₃ modular tag has a uniform margin
above the balanced fibre coefficient as soon as there are three colours. -/
lemma tag_margin (k m : ℝ) (hk : 3 ≤ k)
    (hm : k*(k^2-k+2)/2 ≤ m) :
    (10/9)*k^3 ≤ m*(k-1/2) := by
  have h0 : 0 ≤ 18*k^2-13*k+6 := by nlinarith
  have hp := mul_nonneg (mul_nonneg (show 0 ≤ k by linarith)
    (show 0 ≤ k-3 by linarith)) h0
  have hid : k*(k-3)*(18*k^2-13*k+6) =
      36*(k*(k^2-k+2)/2*(k-1/2)-(10/9)*k^3) := by ring
  rw [hid] at hp
  have hh := mul_le_mul_of_nonneg_right hm (show 0 ≤ k-1/2 by linarith)
  nlinarith

/-- Unequal fibres cannot improve the fixed-tag construction once the total
fibre size is at least nine times the tag modulus, provided the signed-packing
inequalities are available. -/
lemma no_gain_from_packing (k n t s m M : ℝ) (hk : 3 ≤ k)
    (hn : 0 ≤ n) (ht : 0 ≤ t) (hmax : n ≤ k*t)
    (hs : (k-1)*t^2+(n-t)^2 ≤ (k-1)*s)
    (hm : k*(k^2-k+2)/2 ≤ m) (hlarge : 9*m ≤ n)
    (hpack : t*s-t^3/2-n^2 ≤ M) : n^3 ≤ m*M := by
  have hk0 : 0 < k := by linarith
  have hm0 : 0 ≤ m := by
    have : 0 ≤ k^2-k+2 := by nlinarith
    have hp : 0 ≤ k*(k^2-k+2)/2 := by positivity
    linarith
  have hb := balanced_bound k n t s (by linarith) hn ht hmax hs
  have hb' : (k-1/2)*n^3 ≤ k^3*(M+n^2) := by
    have hh := mul_le_mul_of_nonneg_left hpack (show 0 ≤ k^3 by positivity)
    nlinarith
  have h1 := mul_le_mul_of_nonneg_left hb' hm0
  have h2 := mul_le_mul_of_nonneg_right (tag_margin k m hk hm)
    (show 0 ≤ n^3 by positivity)
  have h3 := mul_le_mul_of_nonneg_right hlarge (sq_nonneg n)
  have hk3 : 0 < k^3 := by positivity
  have h4 : (10/9)*n^3 ≤ m*(M+n^2) := by
    apply (mul_le_mul_iff_right₀ hk3).mp
    nlinarith [h1,h2]
  nlinarith [h3]

open Finset in
/-- The same optimization, now for an arbitrary finite list of nonnegative
fibre sizes satisfying the leading signed-packing bound. -/
lemma finite_weights_no_gain {I : Type*} [Fintype I] (q : I → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hk : 3 ≤ Fintype.card I) (m M : ℝ)
    (hm : (Fintype.card I : ℝ)*((Fintype.card I : ℝ)^2-Fintype.card I+2)/2 ≤ m)
    (hlarge : 9*m ≤ ∑ i, q i)
    (hpack : ∀ i, q i*(∑ j, (q j)^2)-(q i)^3/2-(∑ j, q j)^2 ≤ M) :
    (∑ i, q i)^3 ≤ m*M := by
  classical
  have hnI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨i,hi,hmax⟩ := exists_max_image (univ : Finset I) q univ_nonempty
  let k : ℝ := Fintype.card I
  let n : ℝ := ∑ j, q j
  let s : ℝ := ∑ j, (q j)^2
  have hkR : 3 ≤ k := by dsimp [k]; exact_mod_cast hk
  have hn : 0 ≤ n := sum_nonneg (fun j _ ↦ hq j)
  have hbound : n ≤ k*q i := by
    simpa [n,k,nsmul_eq_mul] using sum_le_card_nsmul univ q (q i) hmax
  have h₁ := sum_erase_add univ q hi
  have h₂ := sum_erase_add univ (fun j ↦ (q j)^2) hi
  have he : (((univ : Finset I).erase i).card : ℝ) = k-1 := by
    rw [card_erase_of_mem hi,card_univ,Nat.cast_sub (by omega : 1 ≤ Fintype.card I)]
    simp [k]
  have hc := sq_sum_le_card_mul_sum_sq (s := (univ : Finset I).erase i) (f := q)
  rw [he] at hc
  have hsum₁ : ∑ j ∈ univ.erase i, q j = n-q i := by
    dsimp [n]; linarith only [h₁]
  have hsum₂ : ∑ j ∈ univ.erase i, (q j)^2 = s-(q i)^2 := by
    dsimp [s]; linarith only [h₂]
  rw [hsum₁,hsum₂] at hc
  have hs : (k-1)*(q i)^2+(n-q i)^2 ≤ (k-1)*s := by
    nlinarith only [hc]
  exact no_gain_from_packing k n (q i) s m M hkR hn (hq i) hbound hs hm hlarge (hpack i)

end WeightedPacking

/- Signed-triple packing for genuinely unequal fibres.
The colour map is defined on the actual set of labelled points, so no padding
by additional, possibly incompatible points is assumed. -/
open Finset
namespace UnequalColouredPacking

variable {I K G : Type*} [AddCommGroup G]

def GoodColours (colour : K → I) (v : K → G) : Prop :=
  ∀ s t : Multiset K, s.card=3 → t.card=3 →
    s.map colour=t.map colour → (s.map v).sum=(t.map v).sum → s=t

lemma signed_inj {colour : K → I} {v : K → G} (hv : GoodColours colour v) (i : I)
    {s t : Multiset K} {c d : K} (hs : s.card=2) (ht : t.card=2)
    (hc : s.map colour={i,colour c}) (hd : t.map colour={i,colour d})
    (hcn : c ∉ s) (he : (s.map v).sum-v c=(t.map v).sum-v d) : c=d ∧ s=t := by
  have hcol : (d ::ₘ s).map colour=(c ::ₘ t).map colour := by
    simp only [Multiset.map_cons,hc,hd]
    change colour d ::ₘ i ::ₘ colour c ::ₘ 0 = colour c ::ₘ i ::ₘ colour d ::ₘ 0
    calc
      _ = i ::ₘ colour d ::ₘ colour c ::ₘ 0 := Multiset.cons_swap _ _ _
      _ = i ::ₘ colour c ::ₘ colour d ::ₘ 0 := congrArg (Multiset.cons i) (Multiset.cons_swap _ _ _)
      _ = _ := Multiset.cons_swap _ _ _
  have hh := hv (d ::ₘ s) (c ::ₘ t) (by simp [hs]) (by simp [ht]) hcol (by
    simp only [Multiset.map_cons,Multiset.sum_cons]
    have hh := sub_eq_sub_iff_add_eq_add.mp he
    simpa only [add_comm] using hh)
  have hcd : c=d := by
    have hm : c ∈ d ::ₘ s := hh.symm ▸ Multiset.mem_cons_self c t
    exact (Multiset.mem_cons.mp hm).resolve_right hcn
  subst d
  exact ⟨rfl,Multiset.cons_inj_right c |>.mp hh⟩

lemma signed_ne_plain {colour : K → I} {v : K → G} (hv : GoodColours colour v) (i : I)
    {s : Multiset K} {c a : K} (hs : s.card=2)
    (hc : s.map colour={i,colour c}) (hcn : c ∉ s) (ha : colour a=i) :
    (s.map v).sum-v c ≠ v a := by
  intro he
  have hh := hv (c ::ₘ s) {c,c,a} (by simp [hs]) (by simp) (by
    simp only [Multiset.map_cons,hc]
    simp only [Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_singleton,ha]
    exact congrArg (Multiset.cons (colour c)) (Multiset.cons_swap _ _ _)) (by
    have hval := sub_eq_iff_eq_add.mp he
    simp [hval,add_comm])
  have heq : s=({c,a} : Multiset K) := by
    apply Multiset.cons_inj_right c |>.mp
    simpa using hh
  exact hcn (heq.symm ▸ (by simp))

noncomputable def fibre [Fintype K] (colour : K → I) (i : I) : Finset K :=
  open scoped Classical in univ.filter (fun a ↦ colour a=i)

lemma mem_fibre [Fintype K] {colour : K → I} {i : I} {a : K} :
    a ∈ fibre colour i ↔ colour a=i := by
  classical
  simp [fibre]

lemma fibre_injective [Fintype K] {colour : K → I} {v : K → G}
    (hv : GoodColours colour v) (i : I) : Set.InjOn v (fibre colour i) := by
  intro a ha b hb he
  have hh := hv {a,a,a} {b,b,b} (by simp) (by simp)
    (by simp [mem_fibre.mp ha,mem_fibre.mp hb]) (by simp [he])
  have hm : a ∈ ({b,b,b} : Multiset K) := hh ▸ (by simp)
  simpa using hm

lemma same_signed_set [Fintype K] {colour : K → I} {v : K → G}
    (hv : GoodColours colour v) (i : I) :
    ∃ T : Finset G, T.card=(fibre colour i).card*((fibre colour i).card).choose 2 ∧
      ∀ x ∈ T, ∃ c : K, colour c=i ∧ ∃ s : Multiset K, s.card=2 ∧
        s.map colour={i,i} ∧ c ∉ s ∧ x=(s.map v).sum-v c := by
  classical
  let A := fibre colour i
  let D := (c : A) × Sym ↥(A.erase c.val) 2
  let pos (d : D) : Multiset K := d.2.val.map (fun a : ↥(A.erase d.1.val) ↦ a.val)
  have hpc (d : D) : (pos d).card=2 := by simp [pos]
  have hpcol (d : D) : (pos d).map colour={i,i} := by
    have he (a : ↥(A.erase d.1.val)) : colour a.val=i :=
      mem_fibre.mp (mem_erase.mp a.property).2
    simp only [pos,Multiset.map_map]
    have hm : d.2.val.map (colour ∘ fun a : ↥(A.erase d.1.val) ↦ a.val) =
        d.2.val.map (fun _ ↦ i) := by
      apply Multiset.map_congr rfl
      intro a ha
      exact he a
    rw [hm]
    simp
  have hpn (d : D) : d.1.val ∉ pos d := by
    intro h
    obtain ⟨a,ha,he⟩ := Multiset.mem_map.mp h
    exact (mem_erase.mp a.property).1 he
  let code (d : D) : G := ((pos d).map v).sum-v d.1.val
  have hi : Function.Injective code := by
    rintro ⟨c,m⟩ ⟨d,n⟩ he
    obtain ⟨hcd,hmn⟩ := signed_inj hv i (hpc ⟨c,m⟩) (hpc ⟨d,n⟩)
      (by simpa [mem_fibre.mp c.property] using hpcol ⟨c,m⟩)
      (by simpa [mem_fibre.mp d.property] using hpcol ⟨d,n⟩) (hpn ⟨c,m⟩) he
    have hcd' : c=d := Subtype.ext hcd
    subst d
    congr 1
    apply Sym.ext
    apply Multiset.map_injective (f := fun a : ↥(A.erase c.val) ↦ a.val) Subtype.val_injective
    simpa only [pos] using hmn
  have hsize (c : A) : Fintype.card (Sym ↥(A.erase c.val) 2) = A.card.choose 2 := by
    rw [Sym.card_sym_eq_choose,Fintype.card_coe,card_erase_of_mem c.property]
    have hp : 0 < A.card := card_pos.mpr ⟨c.val,c.property⟩
    congr 1
    omega
  refine ⟨univ.image code,?_,?_⟩
  · rw [card_image_of_injective _ hi,card_univ,Fintype.card_sigma]
    simp_rw [hsize]
    simp [A]
  · intro x hx
    obtain ⟨d,hd,rfl⟩ := mem_image.mp hx
    exact ⟨d.1.val,mem_fibre.mp d.1.property,pos d,hpc d,hpcol d,hpn d,rfl⟩

noncomputable def crossSet [Fintype K] (colour : K → I) (v : K → G) (i j : I) : Finset G :=
  open scoped Classical in
  ((fibre colour i) ×ˢ (fibre colour j).offDiag).image (fun p ↦ v p.1+v p.2.1-v p.2.2)

lemma crossSet_representative [Fintype K] {colour : K → I} {v : K → G} {i j : I}
    (hji : j ≠ i) {x : G} (hx : x ∈ crossSet colour v i j) :
    ∃ c : K, colour c=j ∧ ∃ s : Multiset K, s.card=2 ∧
      s.map colour={i,j} ∧ c ∉ s ∧ x=(s.map v).sum-v c := by
  classical
  obtain ⟨⟨a,b,c⟩,hp,he⟩ := mem_image.mp hx
  rcases mem_product.mp hp with ⟨ha,hbc⟩
  rcases mem_offDiag.mp hbc with ⟨hb,hc,hbc⟩
  have ha' := mem_fibre.mp ha
  have hb' := mem_fibre.mp hb
  have hc' := mem_fibre.mp hc
  refine ⟨c,hc',{a,b},by simp,by simp [ha',hb'],?_,?_⟩
  · simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton]
    rintro (rfl | rfl)
    · exact hji (hc'.symm.trans ha')
    · exact hbc rfl
  · simpa using he.symm

lemma card_crossSet [Fintype K] {colour : K → I} {v : K → G}
    (hv : GoodColours colour v) {i j : I} (hji : j ≠ i) :
    (crossSet colour v i j).card =
      (fibre colour i).card*((fibre colour j).card*((fibre colour j).card-1)) := by
  classical
  unfold crossSet
  rw [card_image_of_injOn]
  · simp [card_product,offDiag_card,Nat.mul_sub_left_distrib]
  · rintro ⟨a,b,c⟩ hp ⟨d,e,f⟩ hq he
    rcases mem_product.mp hp with ⟨ha,hbc⟩
    rcases mem_product.mp hq with ⟨hd,hef⟩
    rcases mem_offDiag.mp hbc with ⟨hb,hc,hbc⟩
    rcases mem_offDiag.mp hef with ⟨he',hf,hef⟩
    have ha' := mem_fibre.mp ha
    have hb' := mem_fibre.mp hb
    have hc' := mem_fibre.mp hc
    have hd' := mem_fibre.mp hd
    have he'' := mem_fibre.mp he'
    have hf' := mem_fibre.mp hf
    have hcn : c ∉ ({a,b} : Multiset K) := by
      simp only [Multiset.insert_eq_cons,Multiset.mem_cons,Multiset.mem_singleton]
      rintro (rfl | rfl)
      · exact hji (hc'.symm.trans ha')
      · exact hbc rfl
    obtain ⟨hcf,hm⟩ := signed_inj hv i (s := {a,b}) (t := {d,e}) (c := c) (d := f)
      (by simp) (by simp) (by simp [ha',hb',hc'])
      (by simp [hd',he'',hf']) hcn (by simpa using he)
    have had : a=d := by
      have haMem : a ∈ ({d,e} : Multiset K) := hm ▸ (by simp)
      rcases (show a=d ∨ a=e by simpa using haMem) with h | h
      · exact h
      · exact (hji (he''.symm.trans (h ▸ ha'))).elim
    subst d
    have hbe : b=e := by simpa using Multiset.cons_inj_right a |>.mp hm
    subst e
    subst f
    rfl

/-- Exact packing for an arbitrary colour map; fibres may have different sizes
and may even be empty. -/
lemma full_signed_packing [Fintype I] [DecidableEq I] [Fintype K] [Fintype G]
    {colour : K → I} {v : K → G} (hv : GoodColours colour v) (i : I) :
    (fibre colour i).card*((fibre colour i).card).choose 2+
      (∑ j ∈ univ.erase i, (fibre colour i).card*
        ((fibre colour j).card*((fibre colour j).card-1)))+
      (fibre colour i).card ≤ Fintype.card G := by
  classical
  obtain ⟨T,hTc,hT⟩ := same_signed_set hv i
  let C := (univ.erase i).biUnion (crossSet colour v i)
  let P := (fibre colour i).image v
  have hCC : (↑(univ.erase i) : Set I).PairwiseDisjoint (crossSet colour v i) := by
    intro j hj k hk hjk
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c,hc,s,hs,hsc,hcn,hx⟩ := crossSet_representative (mem_erase.mp hj).1 hx
    obtain ⟨d,hd,t,ht,htc,hdn,hy⟩ := crossSet_representative (mem_erase.mp hk).1 hy
    have hh := signed_inj hv i hs ht (by simpa [hc] using hsc)
      (by simpa [hd] using htc) hcn (hx.symm.trans hy)
    exact hjk (hc.symm.trans ((congrArg colour hh.1).trans hd))
  have hTcC : Disjoint T C := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c,hc,s,hs,hsc,hcn,hx⟩ := hT x hx
    obtain ⟨j,hj,hy⟩ := mem_biUnion.mp hy
    obtain ⟨d,hd,t,ht,htc,hdn,hy⟩ := crossSet_representative (mem_erase.mp hj).1 hy
    have hh := signed_inj hv i hs ht (by simpa [hc] using hsc)
      (by simpa [hd] using htc) hcn (hx.symm.trans hy)
    exact (mem_erase.mp hj).1 (hd.symm.trans ((congrArg colour hh.1).symm.trans hc))
  have hTP : Disjoint T P := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨c,hc,s,hs,hsc,hcn,hx⟩ := hT x hx
    obtain ⟨a,ha,hy⟩ := mem_image.mp hy
    exact signed_ne_plain hv i hs (by simpa [hc] using hsc) hcn
      (mem_fibre.mp ha) (hx.symm.trans hy.symm)
  have hCP : Disjoint C P := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨j,hj,hx⟩ := mem_biUnion.mp hx
    obtain ⟨c,hc,s,hs,hsc,hcn,hx⟩ := crossSet_representative (mem_erase.mp hj).1 hx
    obtain ⟨a,ha,hy⟩ := mem_image.mp hy
    exact signed_ne_plain hv i hs (by simpa [hc] using hsc) hcn
      (mem_fibre.mp ha) (hx.symm.trans hy.symm)
  have hCc : C.card = ∑ j ∈ univ.erase i, (fibre colour i).card*
      ((fibre colour j).card*((fibre colour j).card-1)) := by
    dsimp only [C]
    rw [card_biUnion hCC]
    apply sum_congr rfl
    intro j hj
    exact card_crossSet hv (mem_erase.mp hj).1
  have hPc : P.card=(fibre colour i).card := card_image_of_injOn (fibre_injective hv i)
  have hh : ((T ∪ C) ∪ P).card ≤ Fintype.card G := card_le_univ _
  rw [card_union_of_disjoint (disjoint_union_left.mpr ⟨hTP,hCP⟩),
    card_union_of_disjoint hTcC,hTc,hCc,hPc] at hh
  exact hh

lemma sum_card_fibres [Fintype I] [Fintype K] (colour : K → I) :
    (∑ i, (fibre colour i).card) = Fintype.card K := by
  classical
  simpa [fibre] using sum_card_fiberwise_eq_card_filter
    (univ : Finset K) (univ : Finset I) colour

lemma cast_mul_pred (a : ℕ) : ((a*(a-1) : ℕ) : ℝ) = (a : ℝ)^2-a := by
  cases a with
  | zero => norm_num
  | succ a => simp only [Nat.add_sub_cancel,Nat.cast_mul,Nat.cast_add,Nat.cast_one]; ring

lemma cast_cross_card (a b : ℕ) :
    ((a*(b*(b-1)) : ℕ) : ℝ) = (a : ℝ)*((b : ℝ)^2-b) := by
  rw [Nat.cast_mul,cast_mul_pred]

/-- The leading real-valued packing inequality, with a uniform quadratic
error term, now follows from the exact finite combinatorics. -/
lemma leading_signed_packing [Fintype I] [Fintype K] [Fintype G]
    {colour : K → I} {v : K → G} (hv : GoodColours colour v) (i : I) :
    ((fibre colour i).card : ℝ)*(∑ j, ((fibre colour j).card : ℝ)^2)-
      ((fibre colour i).card : ℝ)^3/2-(∑ j, ((fibre colour j).card : ℝ))^2 ≤
        (Fintype.card G : ℝ) := by
  classical
  have hR := Nat.cast_le (α := ℝ) |>.mpr (full_signed_packing hv i)
  simp only [Nat.cast_add,Nat.cast_sum,cast_cross_card] at hR
  simp only [Nat.cast_mul,Nat.cast_choose_two] at hR
  let q : I → ℝ := fun j ↦ (fibre colour j).card
  change q i*(q i*(q i-1)/2)+(∑ j ∈ univ.erase i, q i*((q j)^2-q j))+q i ≤
    (Fintype.card G : ℝ) at hR
  change q i*(∑ j, (q j)^2)-(q i)^3/2-(∑ j, q j)^2 ≤ (Fintype.card G : ℝ)
  rw [← mul_sum] at hR
  have hsum : (∑ j ∈ univ.erase i, ((q j)^2-q j)) =
      (∑ j, (q j)^2)-(∑ j, q j)-((q i)^2-q i) := by
    rw [sum_sub_distrib]
    have h₁ := sum_erase_add univ q (mem_univ i)
    have h₂ := sum_erase_add univ (fun j ↦ (q j)^2) (mem_univ i)
    linarith
  rw [hsum] at hR
  have hq (j : I) : 0 ≤ q j := Nat.cast_nonneg _
  have hn : 0 ≤ ∑ j, q j := sum_nonneg (fun j _ ↦ hq j)
  have hqi : q i ≤ ∑ j, q j := single_le_sum (fun j _ ↦ hq j) (mem_univ i)
  have hh := mul_le_mul_of_nonneg_right hqi hn
  nlinarith [hq i,sq_nonneg (q i)]

/-- With at least three colours, allowing unequal fibres does not rescue a
fixed modular B₃ tag construction. The statement applies to the actual labelled
points, rather than to equal-size supersets of the fibres. -/
lemma modular_tag_no_gain [Fintype I] [Fintype K] [Fintype G]
    {colour : K → I} {v : K → G} (hv : GoodColours colour v)
    (m : ℕ) [NeZero m] (hk : 3 ≤ Fintype.card I)
    (tag : I → ZMod m)
    (htag : Function.Injective (fun s : Sym I 3 ↦ (s.val.map tag).sum))
    (hlarge : 9*m ≤ Fintype.card K) :
    (Fintype.card K)^3 ≤ m*Fintype.card G := by
  classical
  let q : I → ℝ := fun i ↦ (fibre colour i).card
  have hq (i : I) : 0 ≤ q i := Nat.cast_nonneg _
  have hsum : (∑ i, q i) = (Fintype.card K : ℝ) := by
    simpa only [q,Nat.cast_sum] using congrArg (fun n : ℕ ↦ (n : ℝ)) (sum_card_fibres colour)
  have htagbound := ColouredPacking.ordinary_code_packing tag htag
  simp only [ZMod.card] at htagbound
  have htagR : (Fintype.card I : ℝ)*((Fintype.card I : ℝ)^2-Fintype.card I+2)/2 ≤ m := by
    have hh := Nat.cast_le (α := ℝ) |>.mpr htagbound
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_choose_two] at hh
    nlinarith
  have hh := WeightedPacking.finite_weights_no_gain q hq hk m (Fintype.card G)
    htagR (by rw [hsum]; exact_mod_cast hlarge)
    (fun i ↦ leading_signed_packing hv i)
  rw [hsum] at hh
  exact_mod_cast hh

end UnequalColouredPacking

/- Integer lifts of two compatible fibres, with no coprimality restriction.
This file gives a conditional disproof criterion, not a counterexample family. -/
open Finset Filter
open scoped Asymptotics
namespace TwoColourLift
open ColouredPacking

lemma block_index_eq {m u v a b : ℕ} (_hm : 0 < m) (hu : u < m) (hv : v < m)
    (he : u+m*a=v+m*b) : a=b := by
  rcases lt_trichotomy a b with h | h | h
  · have hab : a+1 ≤ b := h
    have hh := Nat.mul_le_mul_left m hab
    nlinarith
  · exact h
  · have hab : b+1 ≤ a := h
    have hh := Nat.mul_le_mul_left m hab
    nlinarith

lemma binary_colour_multiset_eq {s t : Multiset (Fin 2)}
    (hs : s.card=3) (ht : t.card=3)
    (he : (s.map Fin.val).sum=(t.map Fin.val).sum) : s=t := by
  apply congrArg Subtype.val (binary_tag_injective (a₁ := ⟨s,hs⟩) (a₂ := ⟨t,ht⟩) ?_)
  have hc := congrArg (fun n : ℕ ↦ (n : ZMod 4)) he
  simpa only [Nat.cast_multiset_sum,Multiset.map_map,Function.comp_def] using hc

noncomputable def integerLift (m q : ℕ) [NeZero m]
    (v : Fin 2 × Fin q → ZMod m) (p : Fin 2 × Fin q) : ℕ :=
  (v p).val+3*m*p.1.val+1

lemma integerLift_sum (m q : ℕ) [NeZero m] (v : Fin 2 × Fin q → ZMod m)
    (s : Multiset (Fin 2 × Fin q)) :
    (s.map (integerLift m q v)).sum =
      (s.map (fun p ↦ (v p).val)).sum+
        3*m*(s.map (fun p ↦ p.1.val)).sum+s.card := by
  induction s using Multiset.induction_on with
  | empty => simp
  | @cons a s ih =>
    simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons]
    rw [ih]
    dsimp only [integerLift]
    ring

lemma three_value_sum_lt (m q : ℕ) [NeZero m] (v : Fin 2 × Fin q → ZMod m)
    (s : Multiset (Fin 2 × Fin q)) (hs : s.card=3) :
    (s.map (fun p ↦ (v p).val)).sum < 3*m := by
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hs
  have ha := ZMod.val_lt (v a)
  have hb := ZMod.val_lt (v b)
  have hc := ZMod.val_lt (v c)
  simpa [add_assoc] using (show (v a).val + (v b).val + (v c).val < 3*m by omega)

lemma integerLift_multiset_inj (m q : ℕ) [NeZero m]
    (v : Fin 2 × Fin q → ZMod m) (hv : GoodFamily v)
    (s t : Multiset (Fin 2 × Fin q)) (hs : s.card=3) (ht : t.card=3)
    (he : (s.map (integerLift m q v)).sum=(t.map (integerLift m q v)).sum) : s=t := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [integerLift_sum,integerLift_sum,hs,ht] at he
  have he' := Nat.add_right_cancel he
  have hcolsum := block_index_eq (by omega : 0 < 3*m)
    (three_value_sum_lt m q v s hs) (three_value_sum_lt m q v t ht) he'
  have hcol : s.map Prod.fst=t.map Prod.fst := by
    apply binary_colour_multiset_eq (by simp [hs]) (by simp [ht])
    simpa only [Multiset.map_map,Function.comp_def] using hcolsum
  have hvalsum : (s.map (fun p ↦ (v p).val)).sum =
      (t.map (fun p ↦ (v p).val)).sum := by
    rw [hcolsum] at he'
    exact Nat.add_right_cancel he'
  have hval : (s.map v).sum=(t.map v).sum := by
    have hc := congrArg (fun n : ℕ ↦ (n : ZMod m)) hvalsum
    simpa only [Nat.cast_multiset_sum,Multiset.map_map,Function.comp_def,ZMod.natCast_zmod_val] using hc
  exact multiset_inj hv s t hs ht hcol hval

/-- Every positive auxiliary modulus can be used. Oddness was only needed by
an alternative CRT encoding, not by the two-colour construction itself. -/
lemma integer_set_of_two_colour_fibres_any_modulus (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    (v : Fin 2 × Fin q → ZMod m) (hv : GoodFamily v) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (4*m) ∧ A.card=2*q ∧ B3Aux.Good A := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  have hi : Function.Injective (integerLift m q v) := by
    intro a b he
    have hh := integerLift_multiset_inj m q v hv {a,a,a} {b,b,b}
      (by simp) (by simp) (by simp [he])
    have hm : a ∈ ({b,b,b} : Multiset (Fin 2 × Fin q)) := hh ▸ (by simp)
    simpa using hm
  have hb (a : Fin 2 × Fin q) : 1 ≤ integerLift m q v a ∧ integerLift m q v a ≤ 4*m := by
    have hav := ZMod.val_lt (v a)
    have hac := a.1.isLt
    dsimp [integerLift]
    constructor
    · omega
    · have hh : a.1.val ≤ 1 := by omega
      have hmul := Nat.mul_le_mul_left (3*m) hh
      nlinarith
  obtain ⟨A,hAN,hcard,hA⟩ := BoseConstruction.exists_set_of_code (4*m) 3
    (integerLift m q v) hi hb (integerLift_multiset_inj m q v hv)
  exact ⟨A,hAN,by simpa only [Fintype.card_prod,Fintype.card_fin] using hcard,hA⟩

/-- A strengthened sufficient criterion that also allows even auxiliary moduli.
The hypothesis still requires an actual unbounded fixed-gain family. -/
lemma not_target_of_two_colour_gain_any_modulus (k : ℕ) (hk : 1 ≤ k)
    (hfam : ∀ B : ℕ, ∃ m q : ℕ, B ≤ q ∧ 0 < q ∧ 0 < m ∧
      ∃ v : Fin 2 × Fin q → ZMod m, GoodFamily v ∧ (k+1)*m ≤ 2*k*q^3) :
    ¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3))) := by
  apply CounterCriterion.negation_iff_dense_sets.mpr
  refine ⟨k,hk,fun B ↦ ?_⟩
  obtain ⟨m,q,hBq,hq,hm,v,hv,hgain⟩ := hfam B
  obtain ⟨A,hAN,hcard,hA⟩ := integer_set_of_two_colour_fibres_any_modulus m q hm hq v hv
  haveI : NeZero m := ⟨by omega⟩
  have hbound := one_colour_packing v hv (0 : Fin 2)
  simp only [Fintype.card_fin,ZMod.card] at hbound
  refine ⟨4*m,A,by omega,by omega,hAN,hA,?_⟩
  rw [hcard]
  nlinarith only [hgain]

end TwoColourLift

/- Common-neighbour components in a B₃ difference graph have at most four
vertices. This is local structure, not an asymptotic extremal estimate. -/
open Finset
namespace DifferenceGraph
open B3Aux

noncomputable def switchSquare (a b c d : ℕ) : Finset ℤ :=
  {(a : ℤ)-b,(a : ℤ)-c,(d : ℤ)-b,(d : ℤ)-c}

lemma cross_ne_of_nonadjacent {A : Finset ℕ} {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hrep : (a : ℤ)-b-δ=(c : ℤ)-d) : a ≠ c ∧ b ≠ d := by
  have hac : a ≠ c := by
    intro h
    have hdb : d ≠ b := by intro hh; apply hδ; omega
    exact hno ((adj_zero_iff A δ).mpr ⟨d,hd,b,hb,hdb,by omega⟩)
  refine ⟨hac,?_⟩
  intro h
  exact hno ((adj_zero_iff A δ).mpr ⟨a,ha,c,hc,hac,by omega⟩)

lemma switchSquare_subset_common {A : Finset ℕ} {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hrep : (a : ℤ)-b-δ=(c : ℤ)-d) :
    switchSquare a b c d ⊆ neighbors A 0 ∩ neighbors A δ := by
  obtain ⟨hac,hbd⟩ := cross_ne_of_nonadjacent hδ hno ha hb hc hd hrep
  intro x hx
  simp only [switchSquare,mem_insert,mem_singleton] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · exact mem_inter.mpr ⟨mem_neighbors.mpr ((adj_zero_iff A _).mpr ⟨a,ha,b,hb,hab,rfl⟩),
      mem_neighbors.mpr ⟨d,hd,c,hc,hcd.symm,by omega⟩⟩
  · exact mem_inter.mpr ⟨mem_neighbors.mpr ((adj_zero_iff A _).mpr ⟨a,ha,c,hc,hac,rfl⟩),
      mem_neighbors.mpr ⟨d,hd,b,hb,hbd.symm,by omega⟩⟩
  · exact mem_inter.mpr ⟨mem_neighbors.mpr ((adj_zero_iff A _).mpr ⟨d,hd,b,hb,hbd.symm,rfl⟩),
      mem_neighbors.mpr ⟨a,ha,c,hc,hac,by omega⟩⟩
  · exact mem_inter.mpr ⟨mem_neighbors.mpr ((adj_zero_iff A _).mpr ⟨d,hd,c,hc,hcd.symm,rfl⟩),
      mem_neighbors.mpr ⟨a,ha,b,hb,hab,by omega⟩⟩

/-- None of the four switched representations has an edge to another
component of the induced common-neighbour graph. -/
lemma switchSquare_closed {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hrep : (a : ℤ)-b-δ=(c : ℤ)-d)
    {x y : ℤ} (hx : x ∈ switchSquare a b c d)
    (hy : y ∈ neighbors A 0 ∩ neighbors A δ) (hxy : (graph A).Adj x y) :
    y ∈ switchSquare a b c d := by
  obtain ⟨hac,hbd⟩ := cross_ne_of_nonadjacent hδ hno ha hb hc hd hrep
  have hy0 := mem_neighbors.mp (mem_inter.mp hy).1
  have hyδ := mem_neighbors.mp (mem_inter.mp hy).2
  simp only [switchSquare,mem_insert,mem_singleton] at hx ⊢
  rcases hx with rfl | rfl | rfl | rfl
  · have hh := common_neighbor_switch hA hδ hno ha hb hc hd hab hcd hrep hy0 hyδ hxy
    tauto
  · have hh := common_neighbor_switch hA hδ hno ha hc hb hd hac hbd
      (show (a : ℤ)-c-δ=(b : ℤ)-d by omega) hy0 hyδ hxy
    tauto
  · have hh := common_neighbor_switch hA hδ hno hd hb hc ha hbd.symm hac.symm
      (show (d : ℤ)-b-δ=(c : ℤ)-a by omega) hy0 hyδ hxy
    tauto
  · have hh := common_neighbor_switch hA hδ hno hd hc hb ha hcd.symm hab.symm
      (show (d : ℤ)-c-δ=(b : ℤ)-a by omega) hy0 hyδ hxy
    tauto

noncomputable def commonGraph (A : Finset ℕ) (δ : ℤ) :
    SimpleGraph ↥(neighbors A 0 ∩ neighbors A δ) :=
  (graph A).induce ↑(neighbors A 0 ∩ neighbors A δ)

lemma reachable_preserves_closed {V : Type*} {G : SimpleGraph V} {S : Set V}
    (hS : ∀ ⦃x y⦄, x ∈ S → G.Adj x y → y ∈ S) {x y : V}
    (hx : x ∈ S) (hxy : G.Reachable x y) : y ∈ S := by
  obtain ⟨p⟩ := hxy
  revert hx
  induction p with
  | nil => exact id
  | cons h p ih => intro hx; exact ih (hS hx h)

lemma reachable_in_switchSquare {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hrep : (a : ℤ)-b-δ=(c : ℤ)-d)
    {x y : ↥(neighbors A 0 ∩ neighbors A δ)} (hx : x.val=(a : ℤ)-b)
    (hxy : (commonGraph A δ).Reachable x y) :
    y.val ∈ switchSquare a b c d := by
  exact reachable_preserves_closed (S := {p | p.val ∈ switchSquare a b c d})
    (fun _ _ hmem hadj ↦ switchSquare_closed hA hδ hno ha hb hc hd hab hcd hrep
      hmem (Subtype.property _) hadj) (by simp [hx,switchSquare]) hxy

lemma commonGraph_step {A : Finset ℕ} {δ : ℤ}
    {x y : ↥(neighbors A 0 ∩ neighbors A δ)} {u v : ℕ}
    (hu : u ∈ A) (hv : v ∈ A) (he : x.val-y.val=(u : ℤ)-v) :
    (commonGraph A δ).Reachable x y := by
  by_cases h : u=v
  · have hxy : x=y := Subtype.ext (by omega)
    subst y
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable (show (commonGraph A δ).Adj x y from ⟨u,hu,v,hv,h,he⟩)

lemma switchSquare_reachable {A : Finset ℕ} {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hrep : (a : ℤ)-b-δ=(c : ℤ)-d)
    {x y : ↥(neighbors A 0 ∩ neighbors A δ)} (hx : x.val=(a : ℤ)-b)
    (hy : y.val ∈ switchSquare a b c d) :
    (commonGraph A δ).Reachable x y := by
  have hsub := switchSquare_subset_common hδ hno ha hb hc hd hab hcd hrep
  let z : ↥(neighbors A 0 ∩ neighbors A δ) := ⟨(a : ℤ)-c,hsub (by simp [switchSquare])⟩
  have hxz : (commonGraph A δ).Reachable x z := commonGraph_step hc hb (by dsimp [z]; omega)
  simp only [switchSquare,mem_insert,mem_singleton] at hy
  rcases hy with hy | hy | hy | hy
  · have he : x=y := Subtype.ext (by omega)
    subst y
    exact SimpleGraph.Reachable.refl _
  · exact commonGraph_step hc hb (by omega)
  · exact commonGraph_step ha hd (by omega)
  · exact hxz.trans (commonGraph_step ha hd (by dsimp [z]; omega))

open scoped Classical in
/-- An exact finite description of a connected component: the four corner
values may coalesce to two or one when a pair has repeated entries. -/
lemma common_component_eq_switchSquare {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hrep : (a : ℤ)-b-δ=(c : ℤ)-d)
    (x : ↥(neighbors A 0 ∩ neighbors A δ)) (hx : x.val=(a : ℤ)-b) :
    ((univ.filter (fun y ↦ (commonGraph A δ).Reachable x y)).image Subtype.val) =
      switchSquare a b c d := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨y,hy,rfl⟩ := mem_image.mp hz
    exact reachable_in_switchSquare hA hδ hno ha hb hc hd hab hcd hrep hx (mem_filter.mp hy).2
  · intro hz
    let y : ↥(neighbors A 0 ∩ neighbors A δ) :=
      ⟨z,switchSquare_subset_common hδ hno ha hb hc hd hab hcd hrep hz⟩
    exact mem_image.mpr ⟨y,mem_filter.mpr ⟨mem_univ _,
      switchSquare_reachable hδ hno ha hb hc hd hab hcd hrep hx hz⟩,rfl⟩

open scoped Classical in
lemma common_component_card_le_four {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    (x : ↥(neighbors A 0 ∩ neighbors A δ)) :
    (univ.filter (fun y ↦ (commonGraph A δ).Reachable x y)).card ≤ 4 := by
  classical
  obtain ⟨a,ha,b,hb,hab,hx⟩ := (adj_zero_iff A x.val).mp
    (mem_neighbors.mp (mem_inter.mp x.property).1)
  obtain ⟨c,hc,d,hd,hcd,hx'⟩ := (graph A).symm
    (mem_neighbors.mp (mem_inter.mp x.property).2)
  have he := common_component_eq_switchSquare hA hδ hno ha hb hc hd hab hcd
    (show (a : ℤ)-b-δ=(c : ℤ)-d by omega) x hx
  have hcard := congrArg Finset.card he
  rw [card_image_of_injective _ Subtype.val_injective] at hcard
  exact hcard.le.trans card_le_four

lemma switchSquare_card {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (hrep : (a : ℤ)-b-δ=(c : ℤ)-d) :
    (switchSquare a b c d).card = ({a,d} : Finset ℕ).card*({b,c} : Finset ℕ).card := by
  classical
  obtain ⟨hac,hbd⟩ := cross_ne_of_nonadjacent hδ hno ha hb hc hd hrep
  let P : Finset ℕ := {a,d}
  let Q : Finset ℕ := {b,c}
  have hPA : P ⊆ A := by simpa [P,insert_subset_iff,singleton_subset_iff] using And.intro ha hd
  have hQA : Q ⊆ A := by simpa [Q,insert_subset_iff,singleton_subset_iff] using And.intro hb hc
  have hPQ : Disjoint P Q := by
    simp [P,Q,disjoint_left,hab,hac,hbd.symm,hcd.symm]
  have he : (P ×ˢ Q).image (fun p : ℕ × ℕ ↦ (p.1 : ℤ)-p.2) = switchSquare a b c d := by
    ext z
    simp only [P,Q,switchSquare,mem_image,mem_product,mem_insert,mem_singleton]
    constructor
    · rintro ⟨⟨u,v⟩,⟨hu,hv⟩,rfl⟩
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl <;> tauto
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨(a,b),⟨Or.inl rfl,Or.inl rfl⟩,rfl⟩
      · exact ⟨(a,c),⟨Or.inl rfl,Or.inr rfl⟩,rfl⟩
      · exact ⟨(d,b),⟨Or.inr rfl,Or.inl rfl⟩,rfl⟩
      · exact ⟨(d,c),⟨Or.inr rfl,Or.inr rfl⟩,rfl⟩
  have hi : Set.InjOn (fun p : ℕ × ℕ ↦ (p.1 : ℤ)-p.2) (↑(P ×ˢ Q) : Set (ℕ × ℕ)) := by
    rintro ⟨u,v⟩ hp ⟨w,z⟩ hq heq
    obtain ⟨hu,hv⟩ := mem_product.mp hp
    obtain ⟨hw,hz⟩ := mem_product.mp hq
    have huv : u ≠ v := by
      intro he
      exact disjoint_left.mp hPQ hu (he ▸ hv)
    obtain ⟨huw,hvz⟩ := difference_inj hA (hPA hu) (hQA hv) (hPA hw) (hQA hz) huv heq
    exact Prod.ext huw hvz
  rw [← he,card_image_of_injOn hi,card_product]

open scoped Classical in
lemma common_component_card_cases {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    (x : ↥(neighbors A 0 ∩ neighbors A δ)) :
    (univ.filter (fun y ↦ (commonGraph A δ).Reachable x y)).card = 1 ∨
    (univ.filter (fun y ↦ (commonGraph A δ).Reachable x y)).card = 2 ∨
    (univ.filter (fun y ↦ (commonGraph A δ).Reachable x y)).card = 4 := by
  classical
  obtain ⟨a,ha,b,hb,hab,hx⟩ := (adj_zero_iff A x.val).mp
    (mem_neighbors.mp (mem_inter.mp x.property).1)
  obtain ⟨c,hc,d,hd,hcd,hx'⟩ := (graph A).symm
    (mem_neighbors.mp (mem_inter.mp x.property).2)
  have hrep : (a : ℤ)-b-δ=(c : ℤ)-d := by omega
  have he := congrArg Finset.card
    (common_component_eq_switchSquare hA hδ hno ha hb hc hd hab hcd hrep x hx)
  rw [card_image_of_injective _ Subtype.val_injective,
    switchSquare_card hA hδ hno ha hb hc hd hab hcd hrep] at he
  have hh : ({a,d} : Finset ℕ).card*({b,c} : Finset ℕ).card = 1 ∨
      ({a,d} : Finset ℕ).card*({b,c} : Finset ℕ).card = 2 ∨
      ({a,d} : Finset ℕ).card*({b,c} : Finset ℕ).card = 4 := by
    by_cases had : a=d <;> by_cases hbc : b=c <;> simp [had,hbc]
  rcases hh with hh | hh | hh
  · exact Or.inl (he.trans hh)
  · exact Or.inr (Or.inl (he.trans hh))
  · exact Or.inr (Or.inr (he.trans hh))

lemma nondegenerate_common_neighbors_eq {A : Finset ℕ} (hA : Good A) {δ : ℤ}
    (hδ : δ ≠ 0) (hno : ¬ (graph A).Adj 0 δ)
    {a b c d : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hc : c ∈ A) (hd : d ∈ A)
    (hab : a ≠ b) (hcd : c ≠ d) (had : a ≠ d) (hbc : b ≠ c)
    (hrep : (a : ℤ)-b-δ=(c : ℤ)-d) :
    neighbors A 0 ∩ neighbors A δ ∩ neighbors A ((a : ℤ)-b) =
      {(a : ℤ)-c,(d : ℤ)-b} := by
  have hsub := switchSquare_subset_common hδ hno ha hb hc hd hab hcd hrep
  ext y
  constructor
  · intro hy
    obtain ⟨hy,hxy⟩ := mem_inter.mp hy
    obtain ⟨hy0,hyδ⟩ := mem_inter.mp hy
    have hh := common_neighbor_switch hA hδ hno ha hb hc hd hab hcd hrep
      (mem_neighbors.mp hy0) (mem_neighbors.mp hyδ) (mem_neighbors.mp hxy)
    simpa only [mem_insert,mem_singleton] using hh
  · intro hy
    simp only [mem_insert,mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact mem_inter.mpr ⟨hsub (by simp [switchSquare]),
        mem_neighbors.mpr ⟨c,hc,b,hb,hbc.symm,by omega⟩⟩
    · exact mem_inter.mpr ⟨hsub (by simp [switchSquare]),
        mem_neighbors.mpr ⟨a,ha,d,hd,had,by omega⟩⟩

end DifferenceGraph

/- The energy upper bound with arbitrary finite positive cosine weights.
This generalization does not settle Erdős 241. -/
namespace CosineBound

lemma general_cosine_energy_lower {ι : Type*} [Fintype ι] (b : ι → ℤ) (L : ℕ)
    (hb : ∀ i j, b i-b j ∈ Icc (-(L : ℤ)) L) (T : Finset ℕ) (weights frequencies : ℕ → ℝ) (hw : ∀ i ∈ T, 0 ≤ weights i) :
    (Fintype.card ι : ℝ)^4 ≤ MomentBound.quadEnergy b *
      (∑ d ∈ Icc (-(L : ℤ)) L, (cosineWeight T weights frequencies ((d : ℝ)/L))^2) := by
  have hh := cosineWeight_pair_sum T weights frequencies hw
    (fun i ↦ (b i : ℝ)/L)
  have he : (∑ d ∈ Icc (-(L : ℤ)) L,
      MomentBound.differenceCount b d * cosineWeight T weights frequencies ((d : ℝ)/L)) =
      ∑ i, ∑ j, cosineWeight T weights frequencies ((b i : ℝ)/L-(b j : ℝ)/L) := by
    rw [MomentBound.sum_differenceCount_mul b _ hb]
    simp only [Int.cast_sub,sub_div]
  rw [← he] at hh
  have hs := pow_le_pow_left₀ (sq_nonneg (Fintype.card ι : ℝ)) hh 2
  have hc := sum_mul_sq_le_sq_mul_sq (Icc (-(L : ℤ)) L) (MomentBound.differenceCount b)
    (fun d ↦ cosineWeight T weights frequencies ((d : ℝ)/L))
  rw [MomentBound.difference_energy_eq b _ hb] at hc
  have hp : ((Fintype.card ι : ℝ)^2)^2 = (Fintype.card ι : ℝ)^4 := by ring
  rw [hp] at hs
  exact hs.trans hc

lemma general_cosine_cauchy_bound {A : Finset ℕ} (hA : B3Aux.Good A) (N u : ℕ) (T : Finset ℕ) (weights frequencies : ℕ → ℝ) (hw : ∀ i ∈ T, 0 ≤ weights i) (C : ℝ)
    (hu : 0 < u) (hAN : A ⊆ Icc 1 N)
    (hgrid : grid (fun x ↦ (cosineWeight T weights frequencies x)^2) (N+u) ≤ C) :
    ((A.card : ℝ)*(u : ℝ))^4 ≤ C*(N+u : ℝ) *
      (2*(A.card : ℝ)*(u : ℝ)^4+(4*((A.card.choose 2) : ℝ)+6*(A.card : ℝ)^3)*(u : ℝ)^3) := by
  let b : A × Fin u → ℤ := fun p ↦ (p.1 : ℕ) + (p.2 : ℕ)
  have hb (i j : A × Fin u) : b i-b j ∈ Icc (-(N+u : ℤ)) (N+u : ℤ) := by
    have hi := (mem_Icc.mp (hAN i.1.property)).2
    have hj := (mem_Icc.mp (hAN j.1.property)).2
    have hui := i.2.isLt
    have huj := j.2.isLt
    simp only [b,mem_Icc]
    omega
  have hh := general_cosine_energy_lower b (N+u) (by simpa only [Nat.cast_add] using hb) T weights frequencies hw
  have hNp : (0 : ℝ) < N+u := by exact_mod_cast (show 0 < N+u by omega)
  have hg := (div_le_iff₀ (by exact_mod_cast (show 0 < N+u by omega) : (0 : ℝ) < (N+u : ℕ))).mp hgrid
  change (∑ d ∈ Icc (-((N+u : ℕ) : ℤ)) (N+u : ℕ),
    (cosineWeight T weights frequencies ((d : ℝ)/(N+u : ℕ)))^2) ≤ C*((N+u : ℕ) : ℝ) at hg
  have hdenpos : 0 ≤ C*((N+u : ℕ) : ℝ) := le_trans (by positivity) hg
  have henergypos : 0 ≤ MomentBound.quadEnergy b := by unfold MomentBound.quadEnergy; positivity
  have h1 := hh.trans (mul_le_mul_of_nonneg_left hg henergypos)
  have h2 := mul_le_mul_of_nonneg_left (MomentBound.smooth_energy_bound hA u) hdenpos
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul,Nat.cast_add] at h1 h2
  exact h1.trans (by simpa only [mul_comm] using h2)

noncomputable def generalDenominator (T : Finset ℕ) (weights frequencies : ℕ → ℝ) : ℝ :=
  2+4*(∑ i ∈ T, weights i*Real.sinc (frequencies i))+
    ∑ i ∈ T, ∑ j ∈ T, weights i*weights j*
      (Real.sinc (frequencies i-frequencies j)+Real.sinc (frequencies i+frequencies j))

lemma generalDenominator_nonneg (T : Finset ℕ) (weights frequencies : ℕ → ℝ) :
    0 ≤ generalDenominator T weights frequencies := by
  apply ge_of_tendsto' (cosineWeight_grid_tendsto T weights frequencies)
  intro n
  unfold grid
  positivity

end CosineBound

lemma f_general_cosine_cauchy_bound (N u : ℕ) (hu : 0 < u) (T : Finset ℕ) (weights frequencies : ℕ → ℝ) (hw : ∀ i ∈ T, 0 ≤ weights i) (C : ℝ)
    (hgrid : CosineBound.grid (fun x ↦ (CosineBound.cosineWeight T weights frequencies x)^2)
      (N+u) ≤ C) :
    ((f N 3 : ℝ)*(u : ℝ))^4 ≤ C*(N+u : ℝ) *
      (2*(f N 3 : ℝ)*(u : ℝ)^4+(4*(((f N 3).choose 2) : ℝ)+6*(f N 3 : ℝ)^3)*(u : ℝ)^3) := by
  classical
  unfold f
  apply Finset.sup_induction (p := fun n : ℕ ↦
    ((n : ℝ)*(u : ℝ))^4 ≤ C*(N+u : ℝ) *
      (2*(n : ℝ)*(u : ℝ)^4+(4*((n.choose 2) : ℝ)+6*(n : ℝ)^3)*(u : ℝ)^3))
  · norm_num
  · intro a ha b hb
    rcases le_total a b with h | h
    · simpa [sup_eq_right.mpr h] using hb
    · simpa [sup_eq_left.mpr h] using ha
  · intro A hA
    rcases mem_filter.mp hA with ⟨hsub,hA⟩
    exact CosineBound.general_cosine_cauchy_bound hA N u T weights frequencies hw C hu (mem_powerset.mp hsub) hgrid

lemma f_general_cosine_bound (N k : ℕ) (hk : 0 < k) (T : Finset ℕ) (weights frequencies : ℕ → ℝ) (hw : ∀ i ∈ T, 0 ≤ weights i) (C : ℝ) (hC : 0 ≤ C)
    (hgrid : CosineBound.grid (fun x ↦ (CosineBound.cosineWeight T weights frequencies x)^2)
      (N+k*(f N 3)^2) ≤ C) :
    (k : ℝ)*(f N 3 : ℝ)^3 ≤ (2*k+10)*C*N + ((2*k+10)*C*k)*(f N 3 : ℝ)^2 := by
  by_cases hn0 : f N 3 = 0
  · simp [hn0]
    positivity
  let n : ℝ := f N 3
  let m : ℝ := (f N 3).choose 2
  let u : ℝ := k*n^2
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnpos : 0 < n := by linarith
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hu : 0 < u := by dsimp [u]; positivity
  have hmc : m ≤ n^3 := by
    have hh : m ≤ n^2 := by dsimp [m,n]; exact_mod_cast Nat.choose_le_pow (f N 3) 2
    exact hh.trans (pow_le_pow_right₀ hn (by omega))
  have hraw : (n*u)^4 ≤ (C*(N+u))*(2*n*u^4+(4*m+6*n^3)*u^3) := by
    have hu' : 0 < k*(f N 3)^2 := Nat.mul_pos hk (pow_pos (Nat.pos_of_ne_zero hn0) 2)
    simpa [n,m,u,Nat.cast_mul,Nat.cast_pow] using f_general_cosine_cauchy_bound N (k*(f N 3)^2) hu' T weights frequencies hw C hgrid
  have hmid : 2*n*u^4+(4*m+6*n^3)*u^3 ≤ (2*k+10)*n^3*u^3 := by
    calc
      _ ≤ 2*n*u^4+10*n^3*u^3 := by nlinarith [mul_le_mul_of_nonneg_right hmc (pow_pos hu 3).le]
      _ = _ := by dsimp [u]; ring
  have hraw' := hraw.trans (mul_le_mul_of_nonneg_left hmid (by positivity))
  have hmain : (k : ℝ)*n^3 ≤ C*(N+u)*(2*k+10) := by
    apply (mul_le_mul_iff_right₀ (mul_pos (pow_pos hnpos 3) (pow_pos hu 3))).mp
    calc
      _ = (n*u)^4 := by dsimp [u]; ring
      _ ≤ _ := hraw'
      _ = _ := by ring
  dsimp [u] at hmain
  change (k : ℝ)*n^3 ≤ _
  nlinarith only [hmain]

lemma f_cube_ratio_eventually_lt_general_cosine_bound (T : Finset ℕ) (weights frequencies : ℕ → ℝ) (hw : ∀ i ∈ T, 0 ≤ weights i) (c : ℝ)
    (hc : 2*CosineBound.generalDenominator T weights frequencies < c) :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < c := by
  let D := CosineBound.generalDenominator T weights frequencies
  let C : ℝ := (D+c/2)/2
  have hD0 : 0 ≤ D := CosineBound.generalDenominator_nonneg T weights frequencies
  have hDC : D < C := by dsimp [C,D]; linarith
  have hCpos : 0 < C := lt_of_le_of_lt hD0 hDC
  have hCc : 2*C < c := by dsimp [C,D]; linarith
  obtain ⟨L,hL⟩ := (eventually_atTop.mp
    ((CosineBound.cosineWeight_grid_tendsto T weights frequencies).eventually_lt_const hDC))
  obtain ⟨k,hk⟩ := exists_nat_gt (10*C/(c-2*C))
  have hkpos : (0 : ℝ) < k := (div_pos (mul_pos (by norm_num) hCpos) (sub_pos.mpr hCc)).trans hk
  have hk' : 0 < k := by exact_mod_cast hkpos
  let a : ℝ := (2*k+10)*C
  let b : ℝ := (2*k+10)*C*k
  have hac : a/k < c := by
    apply (div_lt_iff₀ hkpos).mpr
    have hh := (div_lt_iff₀ (sub_pos.mpr hCc)).mp hk
    dsimp [a]
    nlinarith
  have ht : Tendsto (fun N : ℕ ↦ a/k+(b/k)*((f N 3 : ℝ)^2/N)) atTop (nhds (a/k)) := by
    simpa using (tendsto_const_nhds (x := a/(k : ℝ))).add
      (f_square_ratio_tendsto_zero.const_mul (b/k))
  filter_upwards [eventually_ge_atTop (max L 1),ht.eventually_lt_const hac] with N hN hH
  apply lt_of_le_of_lt _ hH
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  apply (div_le_iff₀ hNp).mpr
  have he : (a/k+(b/k)*((f N 3 : ℝ)^2/N))*N = (a*N+b*(f N 3 : ℝ)^2)/k := by field_simp
  rw [he]
  apply (le_div_iff₀ hkpos).mpr
  have hgrid := (hL (N+k*(f N 3)^2) (by omega)).le
  simpa [a,b,mul_comm] using f_general_cosine_bound N k hk' T weights frequencies hw C hCpos.le hgrid




/- A certified first-mode perturbation of the cosine bound.
This improves an auxiliary bound; it does not settle Erdős 241. -/
namespace CosineBound

lemma generalDenominator_insert (T : Finset ℕ) (w θ : ℕ → ℝ) (i : ℕ)
    (hi : i ∉ T) :
    generalDenominator (insert i T) w θ = generalDenominator T w θ +
      4*w i*Real.sinc (θ i) + (w i)^2*(1+Real.sinc (2*θ i)) +
      2*w i*∑ j ∈ T, w j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)) := by
  have hs : (∑ j ∈ T, w j*w i*(Real.sinc (θ j-θ i)+Real.sinc (θ j+θ i))) =
      w i*∑ j ∈ T, w j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    rw [show θ j-θ i = -(θ i-θ j) by ring, Real.sinc_neg, add_comm (θ j) (θ i)]
    ring
  have ht : (∑ j ∈ T, w i*w j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j))) =
      w i*∑ j ∈ T, w j*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  unfold generalDenominator
  simp only [sum_insert hi,sub_self,Real.sinc_zero,show θ i+θ i=2*θ i by ring]
  simp_rw [sum_add_distrib]
  rw [hs,ht]
  ring

lemma generalDenominator_standard (T : Finset ℕ) :
    generalDenominator T coeff freq = denominatorLimit T := by
  unfold generalDenominator denominatorLimit
  simp only [sinc_freq,sinc_freq_sub,sinc_freq_add,add_zero]
  have hd : (∑ i ∈ T, ∑ j ∈ T, coeff i*coeff j*(if i=j then (1:ℝ) else 0)) =
      ∑ i ∈ T, (coeff i)^2 := by
    apply sum_congr rfl
    intro i hi
    simp [mul_ite, hi, ← sq]
  rw [hd]
  have hl : (∑ i ∈ T, coeff i*(-coeff i/2)) = -(∑ i ∈ T, (coeff i)^2)/2 := by
    rw [← sum_neg_distrib, sum_div]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hl]
  ring

noncomputable def shiftedFreq (j : ℕ) : ℝ := if j=0 then 49*Real.pi/32 else freq j

lemma shiftedFreq_of_ne {j : ℕ} (hj : j ≠ 0) : shiftedFreq j = freq j := by
  simp [shiftedFreq,hj]

lemma sinc_shifted_zero : Real.sinc (shiftedFreq 0) =
    -32*Real.cos (Real.pi/32)/(49*Real.pi) := by
  have hp := Real.pi_pos
  have ht : shiftedFreq 0 = (Real.pi/32+Real.pi/2)+Real.pi := by simp [shiftedFreq]; ring
  rw [Real.sinc_of_ne_zero (by simp [shiftedFreq]), ht,
    Real.sin_add_pi,Real.sin_add_pi_div_two]
  field_simp
  ring

lemma sinc_twice_shifted_zero : Real.sinc (2*shiftedFreq 0) =
    -16*Real.sin (Real.pi/16)/(49*Real.pi) := by
  have hp := Real.pi_pos
  have ht : 2*shiftedFreq 0 = (Real.pi/16+Real.pi)+1*(2*Real.pi) := by
    simp [shiftedFreq]; ring
  rw [Real.sinc_of_ne_zero (by simp [shiftedFreq]), ht,
    ← Nat.cast_one (R := ℝ),Real.sin_add_nat_mul_two_pi,Real.sin_add_pi]
  field_simp
  ring

noncomputable def shiftTerm (j : ℕ) : ℝ :=
  1/((4*(j : ℝ)+3)*(64*(j : ℝ)-1)) +
  1/((4*(j : ℝ)+3)*(64*(j : ℝ)+97))

lemma shiftTerm_pos {j : ℕ} (hj : 0 < j) : 0 < shiftTerm j := by
  have h : (1 : ℝ) ≤ j := by exact_mod_cast hj
  dsimp [shiftTerm]
  have h1 : 0 < 64*(j : ℝ)-1 := by linarith
  positivity

lemma sinc_shifted_cross (j : ℕ) (hj : j ≠ 0) :
    coeff j * (Real.sinc (shiftedFreq 0-freq j)+Real.sinc (shiftedFreq 0+freq j)) =
    -(128*Real.sin (Real.pi/32)/Real.pi^2)*shiftTerm j := by
  have hj1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
  have hp := Real.pi_pos
  have he1 : shiftedFreq 0-freq j = Real.pi/32-(j : ℝ)*(2*Real.pi) := by
    simp [shiftedFreq,freq]; ring
  have he2 : shiftedFreq 0+freq j = ((Real.pi/32+Real.pi)+1*(2*Real.pi))+
      (j : ℝ)*(2*Real.pi) := by simp [shiftedFreq,freq]; ring
  have hn1 : shiftedFreq 0-freq j ≠ 0 := by
    rw [he1]
    have : Real.pi ≤ (j : ℝ)*Real.pi := le_mul_of_one_le_left hp.le hj1
    nlinarith
  have hn2 : shiftedFreq 0+freq j ≠ 0 := by
    have : 0 < shiftedFreq 0 := by simp [shiftedFreq]; positivity
    exact (add_pos this (freq_pos j)).ne'
  rw [Real.sinc_of_ne_zero hn1,Real.sinc_of_ne_zero hn2,he1,he2,
    Real.sin_sub_nat_mul_two_pi,Real.sin_add_nat_mul_two_pi,
    show (1 : ℝ) = (1 : ℕ) by norm_num,Real.sin_add_nat_mul_two_pi,Real.sin_add_pi]
  have hd : (64*(j : ℝ)-1) ≠ 0 := by linarith
  have hd' : (4*(j : ℝ)+3) ≠ 0 := by positivity
  have hd'' : (64*(j : ℝ)+97) ≠ 0 := by positivity
  have hn1' : Real.pi/32-(j : ℝ)*(2*Real.pi) ≠ 0 := he1 ▸ hn1
  have hn2' : ((Real.pi/32+Real.pi)+1*(2*Real.pi))+(j : ℝ)*(2*Real.pi) ≠ 0 := he2 ▸ hn2
  unfold coeff shiftTerm
  field_simp
  ring_nf
  field_simp [show 1-(j : ℝ)*64 ≠ 0 by linarith,
    show -1+(j : ℝ)*64 ≠ 0 by linarith]
  ring

lemma generalDenominator_congr_freq (T : Finset ℕ) (w θ φ : ℕ → ℝ)
    (he : ∀ j ∈ T, θ j = φ j) : generalDenominator T w θ = generalDenominator T w φ := by
  unfold generalDenominator
  congr 1
  · congr 2
    apply sum_congr rfl
    intro j hj
    rw [he j hj]
  · apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [he i hi,he j hj]

lemma shifted_denominator_difference (T : Finset ℕ) (hT : 0 ∉ T) :
    generalDenominator (insert 0 T) coeff shiftedFreq - denominatorLimit (insert 0 T) =
      (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
      256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
      (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*∑ j ∈ T, shiftTerm j := by
  have hj (j : ℕ) (h : j ∈ T) : j ≠ 0 := by rintro rfl; exact hT h
  have hg := generalDenominator_congr_freq T coeff shiftedFreq freq
    (fun j h ↦ shiftedFreq_of_ne (hj j h))
  have hcross : (∑ j ∈ T, coeff j*(Real.sinc (shiftedFreq 0-shiftedFreq j)+
      Real.sinc (shiftedFreq 0+shiftedFreq j))) =
      -(128*Real.sin (Real.pi/32)/Real.pi^2)*∑ j ∈ T, shiftTerm j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j h
    rw [shiftedFreq_of_ne (hj j h)]
    exact sinc_shifted_cross j (hj j h)
  have hcross0 : (∑ j ∈ T, coeff j*(Real.sinc (freq 0-freq j)+
      Real.sinc (freq 0+freq j))) = 0 := by
    apply sum_eq_zero
    intro j h
    simp [sinc_freq_sub,sinc_freq_add,Ne.symm (hj j h)]
  have hdiag : Real.sinc (2*freq 0) = 0 := by
    rw [show 2*freq 0=freq 0+freq 0 by ring,sinc_freq_add]
  rw [← generalDenominator_standard, generalDenominator_insert T coeff shiftedFreq 0 hT,
    generalDenominator_insert T coeff freq 0 hT, hg, hcross, hcross0, hdiag,
    sinc_shifted_zero,sinc_twice_shifted_zero,sinc_freq]
  simp only [coeff,Nat.cast_zero,mul_zero,zero_add]
  field_simp
  ring

set_option maxHeartbeats 3000000 in
lemma thirty_two_shift_terms :
    (6469 : ℝ)/1000000 < ∑ j ∈ (range 33).erase 0, shiftTerm j := by
  rw [sum_erase_eq_sub (mem_range.mpr (by norm_num : 0 < 33))]
  norm_num [shiftTerm,sum_range_succ]

lemma million_shift_terms :
    (6469 : ℝ)/1000000 ≤ ∑ j ∈ (range 1000000).erase 0, shiftTerm j := by
  apply thirty_two_shift_terms.le.trans
  apply sum_le_sum_of_subset_of_nonneg
  · exact erase_subset_erase 0 (range_mono (by norm_num))
  · intro j hj _
    exact (shiftTerm_pos (Nat.pos_of_ne_zero (ne_of_mem_erase hj))).le

lemma shift_arithmetic_bound (R : ℝ) (hR : (6469 : ℝ)/1000000 ≤ R) :
    (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
      256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
      (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*R < -(3 : ℝ)/2000 := by
  have hp := Real.pi_pos
  have hp32 : 0 < Real.pi/32 := by positivity
  have hp16 : 0 < Real.pi/16 := by positivity
  have hs32 := (Real.sin_gt_sub_cube hp32 (by linarith [Real.pi_lt_four])).le
  have hs16 := (Real.sin_gt_sub_cube hp16 (by linarith [Real.pi_lt_four])).le
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi/32)
  have hs0 : 0 ≤ Real.sin (Real.pi/32) :=
    (Real.sin_pos_of_pos_of_lt_pi hp32 (by linarith)).le
  let R₀ : ℝ := 6469/1000000
  have hR₀ : 0 ≤ R₀ := by norm_num [R₀]
  have hb : (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
      256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
      (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*R ≤
      (32/9-(512/147)*(1-(Real.pi/32)^2/2))/Real.pi^2 -
      256*(Real.pi/16-(Real.pi/16)^3/4)/(441*Real.pi^3) -
      (1024*(Real.pi/32-(Real.pi/32)^3/4)/(3*Real.pi^3))*R₀ := by
    calc
      _ ≤ (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
          256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
          (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*R₀ := by
        gcongr
      _ ≤ _ := by gcongr
  have he : (32/9-(512/147)*(1-(Real.pi/32)^2/2))/Real.pi^2 -
      256*(Real.pi/16-(Real.pi/16)^3/4)/(441*Real.pi^3) -
      (1024*(Real.pi/32-(Real.pi/32)^3/4)/(3*Real.pi^3))*R₀ =
      (16/441-(32/3)*R₀)/Real.pi^2+1/576+R₀/384 := by
    field_simp
    ring
  rw [he] at hb
  have hp2 : Real.pi^2 < (986961 : ℝ)/100000 := by
    nlinarith [Real.pi_lt_d6]
  have hd : (16/441-(32/3)*R₀)/Real.pi^2 ≤
      (16/441-(32/3)*R₀)/(986961/100000) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) (by norm_num)).mpr
    dsimp [R₀]
    nlinarith only [hp2]
  have hfinal : (16/441-(32/3)*R₀)/(986961/100000)+1/576+R₀/384 < -(3 : ℝ)/2000 := by
    norm_num [R₀]
  linarith

lemma shifted_million_modes_strict :
    2*generalDenominator (range 1000000) coeff shiftedFreq < (3482 : ℝ)/1000 := by
  have hh := shifted_denominator_difference ((range 1000000).erase 0) (by simp)
  rw [insert_erase (mem_range.mpr (by norm_num : 0 < 1000000))] at hh
  have hb := shift_arithmetic_bound _ million_shift_terms
  rw [← hh] at hb
  have ho := million_modes_strict
  linarith

end CosineBound

lemma f_cube_ratio_eventually_lt_shifted_cosine_bound :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < (3482 : ℝ)/1000 :=
  f_cube_ratio_eventually_lt_general_cosine_bound (range 1000000)
    CosineBound.coeff CosineBound.shiftedFreq
    (fun i _ ↦ (CosineBound.coeff_pos i).le) (3482/1000)
    CosineBound.shifted_million_modes_strict



/- Exact coupled-shift and signed five-term bounds for arbitrary B3 sets.
These are auxiliary estimates, not a settlement of Erdős 241. -/
open Finset
namespace CoupledShifts
open B3Aux

/-- Uniqueness of a noncancelling signed triple, with an order on its pair. -/
lemma signed_triple_unique {A : Finset ℕ} (hA : Good A)
    {b d e b' d' e' : ℕ} (hb : b ∈ A) (hd : d ∈ A) (he : e ∈ A)
    (hb' : b' ∈ A) (hd' : d' ∈ A) (he' : e' ∈ A)
    (hbd : b ≠ d) (hbe : b ≠ e)
    (hs : (b : ℤ)-d-e=(b' : ℤ)-d'-e') :
    b=b' ∧ ((d=d' ∧ e=e') ∨ (d=e' ∧ e=d')) := by
  have hsum : b+d'+e'=b'+d+e := by omega
  have hbb : b=b' := by
    rcases three_sum_mem hA hb hd' he' hb' hd he hsum with h | h | h
    · exact h
    · exact (hbd h).elim
    · exact (hbe h).elim
  refine ⟨hbb,?_⟩
  have hpair : d+e=d'+e' := by omega
  rcases DifferenceGraph.two_sum_mem hA hd he hd' he' hpair with h | h
  · exact Or.inl ⟨h,by omega⟩
  · exact Or.inr ⟨h,by omega⟩

noncomputable def pairSet (A : Finset ℕ) : Finset ℤ :=
  (A ×ˢ A).image (fun p ↦ (p.1 : ℤ)+p.2)

lemma mem_pairSet {A : Finset ℕ} {x : ℤ} :
    x ∈ pairSet A ↔ ∃ a ∈ A, ∃ b ∈ A, x=(a : ℤ)+b := by
  classical
  simp only [pairSet,mem_image,mem_product,Prod.exists]
  constructor
  · rintro ⟨a,b,⟨ha,hb⟩,he⟩
    exact ⟨a,ha,b,hb,he.symm⟩
  · rintro ⟨a,ha,b,hb,he⟩
    exact ⟨a,b,⟨ha,hb⟩,he.symm⟩

noncomputable def shiftSupport (A : Finset ℕ) (δ : ℤ) : Finset ℤ :=
  (pairSet A).filter (fun t ↦ t-δ ∈ pairSet A)

lemma mem_shiftSupport {A : Finset ℕ} {t δ : ℤ} :
    t ∈ shiftSupport A δ ↔ t ∈ pairSet A ∧ t-δ ∈ pairSet A := by
  classical
  simp [shiftSupport]

lemma pair_difference {A : Finset ℕ} (hA : Good A)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    {s t : ℤ} (hs : s ∈ pairSet A) (ht : t ∈ pairSet A)
    (he : s-t=(a : ℤ)-b) : ∃ c ∈ A, s=(a : ℤ)+c ∧ t=(b : ℤ)+c := by
  obtain ⟨u,hu,v,hv,hs⟩ := mem_pairSet.mp hs
  obtain ⟨w,hw,z,hz,ht⟩ := mem_pairSet.mp ht
  have hh : a+w+z=b+u+v := by omega
  rcases three_sum_mem hA ha hw hz hb hu hv hh with h | h | h
  · exact (hab h).elim
  · exact ⟨v,hv,by omega,by omega⟩
  · exact ⟨u,hu,by omega,by omega⟩

/-- Two shifts separated by an A-difference have at most one common pair sum,
provided the first shift is not itself an A-difference (zero included). -/
lemma shift_intersection_card_le_one {A : Finset ℕ} (hA : Good A)
    {δ ε : ℤ} {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a ≠ b)
    (hde : δ-ε=(a : ℤ)-b)
    (hδ : ∀ u ∈ A, ∀ v ∈ A, δ ≠ (u : ℤ)-v) :
    (shiftSupport A δ ∩ shiftSupport A ε).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro s hs t ht
  obtain ⟨hsδ,hsε⟩ := mem_inter.mp hs
  obtain ⟨htδ,htε⟩ := mem_inter.mp ht
  obtain ⟨c,hc,hsc,hsc'⟩ := pair_difference hA hb ha hab.symm
    (mem_shiftSupport.mp hsδ).2 (mem_shiftSupport.mp hsε).2 (by omega)
  obtain ⟨d,hd,htd,htd'⟩ := pair_difference hA hb ha hab.symm
    (mem_shiftSupport.mp htδ).2 (mem_shiftSupport.mp htε).2 (by omega)
  obtain ⟨u,hu,v,hv,hsuv⟩ := mem_pairSet.mp (mem_shiftSupport.mp hsδ).1
  obtain ⟨w,hw,z,hz,htwz⟩ := mem_pairSet.mp (mem_shiftSupport.mp htδ).1
  have hcu : c ≠ u := by intro h; exact hδ v hv b hb (by omega)
  have hcv : c ≠ v := by intro h; exact hδ u hu b hb (by omega)
  have hh := signed_triple_unique hA hc hu hv hd hw hz hcu hcv
    (show (c : ℤ)-u-v=(d : ℤ)-w-z by omega)
  omega

/-- The ordered signed triples at x. -/
noncomputable def triples (A : Finset ℕ) (x : ℤ) : Finset (A × A × A) :=
  univ.filter (fun p ↦ (p.1 : ℕ)-(p.2.1 : ℤ)-(p.2.2 : ℤ)=x)

lemma triples_card_le_two {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A, x ≠ -(a : ℤ)) : (triples A x).card ≤ 2 := by
  classical
  have hh : (triples A x).card ≤ (univ : Finset Bool).card := by
    apply card_le_card_of_injOn (fun p : A × A × A ↦ decide ((p.2.1 : ℕ) ≤ p.2.2))
      (fun _ _ ↦ mem_univ _)
    rintro ⟨b,d,e⟩ hp ⟨b',d',e'⟩ hq heq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    have hbd : (b : ℕ) ≠ d := by intro h; exact hx e e.property (by dsimp only at hp'; omega)
    have hbe : (b : ℕ) ≠ e := by intro h; exact hx d d.property (by dsimp only at hp'; omega)
    obtain ⟨hbb,hpair⟩ := signed_triple_unique hA b.property d.property e.property
      b'.property d'.property e'.property hbd hbe (by dsimp only at hp' hq'; omega)
    have hord : ((d : ℕ) ≤ e) ↔ ((d' : ℕ) ≤ e') := by simpa using heq
    have hdd : (d : ℕ)=d' := by rcases hpair with h | h <;> omega
    have hee : (e : ℕ)=e' := by rcases hpair with h | h <;> omega
    exact Prod.ext (Subtype.ext hbb) (Prod.ext (Subtype.ext hdd) (Subtype.ext hee))
  simpa using hh

abbrev Five (A : Finset ℕ) := (A × A) × (A × A × A)

noncomputable def fives (A : Finset ℕ) (x : ℤ) : Finset (Five A) :=
  univ.filter (fun p ↦ (p.1.1 : ℤ)+p.1.2-p.2.1-p.2.2.1-p.2.2.2=x)

noncomputable def mainFives (A : Finset ℕ) (x : ℤ) : Finset (Five A) :=
  (fives A x).filter (fun p ↦ p.1.2 ≠ p.2.2.1 ∧ p.1.2 ≠ p.2.2.2)

lemma mainFives_card {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (mainFives A x).card ≤ 2*A.card^2 := by
  classical
  have hh : (mainFives A x).card ≤ (univ : Finset (A × A × Bool)).card := by
    apply card_le_card_of_injOn (fun p : Five A ↦
      (p.1.1,p.2.1,decide ((p.2.2.1 : ℕ) ≤ p.2.2.2))) (fun _ _ ↦ mem_univ _)
    rintro ⟨⟨a,b⟩,c,d,e⟩ hp ⟨⟨a',b'⟩,c',d',e'⟩ hq heq
    have haa := congrArg Prod.fst heq
    have hcc := congrArg (Prod.fst ∘ Prod.snd) heq
    have hord := congrArg (Prod.snd ∘ Prod.snd) heq
    dsimp only [Function.comp_apply] at haa hcc hord
    subst a'; subst c'
    obtain ⟨hp,hbd,hbe⟩ := mem_filter.mp hp
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp (mem_filter.mp hq).1).2
    obtain ⟨hbb,hpair⟩ := signed_triple_unique hA b.property d.property e.property
      b'.property d'.property e'.property
      (fun h ↦ hbd (Subtype.ext h)) (fun h ↦ hbe (Subtype.ext h))
      (by dsimp only at hp' hq'; omega)
    have hord' : ((d : ℕ) ≤ e) ↔ ((d' : ℕ) ≤ e') := by simpa using hord
    have hdd : (d : ℕ)=d' := by rcases hpair with h | h <;> omega
    have hee : (e : ℕ)=e' := by rcases hpair with h | h <;> omega
    exact Prod.ext (Prod.ext rfl (Subtype.ext hbb))
      (Prod.ext rfl (Prod.ext (Subtype.ext hdd) (Subtype.ext hee)))
  simpa [pow_two,mul_assoc,mul_comm,mul_left_comm] using hh

lemma triples_card_le_twice {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (triples A x).card ≤ 2*A.card := by
  classical
  have hh : (triples A x).card ≤ (univ : Finset (A × Bool)).card := by
    apply card_le_card_of_injOn (fun p : A × A × A ↦
      (p.1,decide ((p.2.1 : ℕ) ≤ p.2.2))) (fun _ _ ↦ mem_univ _)
    rintro ⟨b,d,e⟩ hp ⟨b',d',e'⟩ hq heq
    have hbb := congrArg Prod.fst heq
    have hord := congrArg Prod.snd heq
    dsimp only at hbb hord
    subst b'
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    have hsum : (d : ℕ)+e=d'+e' := by dsimp only at hp' hq'; omega
    have hh := DifferenceGraph.two_sum_mem hA d.property e.property d'.property e'.property hsum
    have hord' : ((d : ℕ) ≤ e) ↔ ((d' : ℕ) ≤ e') := by simpa using hord
    have hdd : (d : ℕ)=d' := by rcases hh with h | h <;> omega
    have hee : (e : ℕ)=e' := by omega
    exact Prod.ext rfl (Prod.ext (Subtype.ext hdd) (Subtype.ext hee))
  simpa [mul_comm] using hh

lemma fives_card_recurrence {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (fives A x).card ≤ 2*A.card^2+2*A.card*(triples A x).card := by
  classical
  let S : Finset (A × (A × A × A)) := univ ×ˢ triples A x
  let i₁ : A × (A × A × A) → Five A := fun p ↦ ((p.2.1,p.1),(p.2.2.1,p.1,p.2.2.2))
  let i₂ : A × (A × A × A) → Five A := fun p ↦ ((p.2.1,p.1),(p.2.2.1,p.2.2.2,p.1))
  have hsub : fives A x ⊆ mainFives A x ∪ S.image i₁ ∪ S.image i₂ := by
    rintro ⟨⟨a,b⟩,c,d,e⟩ hp
    by_cases hbd : b=d
    · subst d
      apply mem_union_left
      apply mem_union_right
      apply mem_image.mpr
      refine ⟨(b,a,c,e),?_,rfl⟩
      apply mem_product.mpr
      refine ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
      have hh := (mem_filter.mp hp).2
      dsimp only at hh ⊢
      omega
    · by_cases hbe : b=e
      · subst e
        apply mem_union_right
        apply mem_image.mpr
        refine ⟨(b,a,c,d),?_,rfl⟩
        apply mem_product.mpr
        refine ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,?_⟩⟩
        have hh := (mem_filter.mp hp).2
        dsimp only at hh ⊢
        omega
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,hbd,hbe⟩))
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have hh' := card_union_le (mainFives A x) (S.image i₁)
  have h₁ := card_image_le (s := S) (f := i₁)
  have h₂ := card_image_le (s := S) (f := i₂)
  have hS : S.card=A.card*(triples A x).card := by simp [S]
  have hm := mainFives_card hA x
  nlinarith only [hh,hh',h₁,h₂,hS,hm]

/-- A signed five-term count coupled across A-translates of fourth counts. -/
lemma fives_card_nonexceptional {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A, x ≠ -(a : ℤ)) :
    (fives A x).card ≤ 2*A.card^2+4*A.card := by
  have hh := fives_card_recurrence hA x
  have ht := Nat.mul_le_mul_left (2*A.card) (triples_card_le_two hA x hx)
  omega

lemma fives_card_uniform {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (fives A x).card ≤ 6*A.card^2 := by
  have hh := fives_card_recurrence hA x
  have ht := Nat.mul_le_mul_left (2*A.card) (triples_card_le_twice hA x)
  nlinarith

noncomputable def negativeCore (A : Finset ℕ) : Finset ℤ :=
  A.image (fun a : ℕ ↦ -(a : ℤ))

lemma fives_card_bound {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (fives A x).card ≤ 2*A.card^2+4*A.card+
      if x ∈ negativeCore A then 4*A.card^2 else 0 := by
  classical
  by_cases hx : x ∈ negativeCore A
  · rw [if_pos hx]
    have hh := fives_card_uniform hA x
    omega
  · rw [if_neg hx,add_zero]
    apply fives_card_nonexceptional hA x
    intro a ha he
    apply hx
    exact mem_image.mpr ⟨a,ha,he.symm⟩

lemma sum_fives_bound {A : Finset ℕ} (hA : Good A) (S : Finset ℤ) :
    (∑ x ∈ S, (fives A x).card) ≤
      (2*A.card^2+4*A.card)*S.card+4*A.card^2*(S ∩ negativeCore A).card := by
  classical
  have hh := sum_le_sum (s := S) (fun x _ ↦ fives_card_bound hA x)
  have he : (∑ x ∈ S, if x ∈ negativeCore A then 4*A.card^2 else 0) =
      4*A.card^2*(S ∩ negativeCore A).card := by
    rw [← sum_filter]
    have hS : S.filter (fun x ↦ x ∈ negativeCore A)=S ∩ negativeCore A := by ext; simp
    rw [hS]
    simp [mul_comm]
  rw [sum_add_distrib,he] at hh
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm] using hh

lemma sum_fives_coarse {A : Finset ℕ} (hA : Good A) (S : Finset ℤ) :
    (∑ x ∈ S, (fives A x).card) ≤
      (2*A.card^2+4*A.card)*S.card+4*A.card^3 := by
  have hc : (S ∩ negativeCore A).card ≤ A.card :=
    (card_le_card inter_subset_right).trans (card_image_le)
  have hh := Nat.mul_le_mul_left (4*A.card^2) hc
  have hs := sum_fives_bound hA S
  nlinarith only [hh,hs]

noncomputable def fours (A : Finset ℕ) (δ : ℤ) : Finset ((A × A) × (A × A)) :=
  univ.filter (fun p ↦ (p.1.1 : ℤ)+p.1.2-p.2.1-p.2.2=δ)

lemma fives_eq_sum_fours (A : Finset ℕ) (x : ℤ) :
    (fives A x).card = ∑ c : A, (fours A (x+c)).card := by
  classical
  let e : Five A ≃ A × ((A × A) × (A × A)) :=
    { toFun := fun p ↦ (p.2.1,(p.1,(p.2.2.1,p.2.2.2)))
      invFun := fun p ↦ (p.2.1,(p.1,p.2.2.1,p.2.2.2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have he : (fives A x).card =
      (univ.filter (fun p : A × ((A × A) × (A × A)) ↦ p.2 ∈ fours A (x+p.1))).card := by
    apply card_bij (fun p _ ↦ e p)
    · intro p hp
      simp only [mem_filter,mem_univ,true_and,fours]
      have hh := (mem_filter.mp hp).2
      dsimp [e] at hh ⊢
      omega
    · intro p hp q hq hh
      exact e.injective hh
    · intro p hp
      refine ⟨e.symm p,?_,e.apply_symm_apply p⟩
      apply mem_filter.mpr
      refine ⟨mem_univ _,?_⟩
      have hh := (mem_filter.mp (mem_filter.mp hp).2).2
      dsimp [e] at hh ⊢
      omega
  rw [he]
  simp only [fours,card_eq_sum_ones,sum_filter,mem_filter,mem_univ,true_and,Fintype.sum_prod_type]

lemma sum_translated_fours {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A, x ≠ -(a : ℤ)) :
    (∑ c : A, (fours A (x+c)).card) ≤ 2*A.card^2+4*A.card := by
  rw [← fives_eq_sum_fours]
  exact fives_card_nonexceptional hA x hx

end CoupledShifts

/- Pointwise fourth-energy bounds including repeated summands.
These estimates do not settle the sharp B3 asymptotic. -/
namespace FullQuadBound
open Finset B3Aux MomentBound

noncomputable def positivePairs (A : Finset ℕ) (i j : ℕ) : Finset (A × A) :=
  univ.filter (fun p ↦ ∃ c d : A, (p.1 : ℕ)+p.2+i=c+d+j)

noncomputable def quads (A : Finset ℕ) (i j : ℕ) : Finset (Quad A) :=
  univ.filter (fun p ↦ (p.1.1 : ℕ)+p.1.2+i=p.2.1+p.2.2+j)

lemma second_unique {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j)
    {a b b' c d e f : A}
    (h : (a : ℕ)+b+i=c+d+j) (h' : (a : ℕ)+b'+i=e+f+j) : b=b' := by
  have he : (b : ℕ)+e+f=b'+c+d := by omega
  rcases three_sum_mem hA b.property e.property f.property
    b'.property c.property d.property he with hb | hb | hb
  · exact Subtype.ext hb
  · exact (hNo a a.property d d.property (by omega)).elim
  · exact (hNo a a.property c c.property (by omega)).elim

lemma positivePairs_nonexceptional {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    (positivePairs A i j).card ≤ A.card := by
  classical
  have hh : (positivePairs A i j).card ≤ (univ : Finset A).card := by
    apply card_le_card_of_injOn Prod.fst (fun _ _ ↦ mem_univ _)
    rintro ⟨a,b⟩ hp ⟨a',b'⟩ hq he
    dsimp only at he
    subst a'
    obtain ⟨c,d,h⟩ := (mem_filter.mp hp).2
    obtain ⟨e,f,h'⟩ := (mem_filter.mp hq).2
    exact Prod.ext rfl (second_unique hA i j hNo h h')
  simpa only [card_univ,Fintype.card_coe] using hh

lemma quads_le_twice_positivePairs {A : Finset ℕ} (hA : Good A) (i j : ℕ) :
    (quads A i j).card ≤ 2*(positivePairs A i j).card := by
  classical
  have hh : (quads A i j).card ≤ 2*(positivePairs A i j).card := by
    apply card_le_mul_card_image_of_maps_to (f := Prod.fst)
      (t := positivePairs A i j) ?_ 2 ?_
    · intro p hp
      exact mem_filter.mpr ⟨mem_univ _,p.2.1,p.2.2,(mem_filter.mp hp).2⟩
    · intro r hr
      by_cases hn : ((quads A i j).filter (fun p ↦ p.1=r)).Nonempty
      · obtain ⟨p,hp⟩ := hn
        have hsub : ((quads A i j).filter (fun q ↦ q.1=r)) ⊆ {p,(p.1,p.2.swap)} := by
          intro q hq
          obtain ⟨hp0,hpr⟩ := mem_filter.mp hp
          obtain ⟨hq0,hqr⟩ := mem_filter.mp hq
          have hpair : q.1=p.1 := hqr.trans hpr.symm
          have hpEq := (mem_filter.mp hp0).2
          have hqEq := (mem_filter.mp hq0).2
          rw [hpair] at hqEq
          have he : (q.2.1 : ℕ)+q.2.2=p.2.1+p.2.2 := by omega
          rcases two_sum_permutation hA q.2.1 q.2.2 p.2.1 p.2.2 he with
            ⟨h1,h2⟩ | ⟨h1,h2⟩
          · exact mem_insert.mpr (Or.inl (Prod.ext hpair (Prod.ext h1 h2)))
          · exact mem_insert_of_mem (mem_singleton.mpr (Prod.ext hpair (Prod.ext h1 h2)))
        exact (card_le_card hsub).trans (card_le_two (a := p) (b := (p.1,p.2.swap)))
      · simp only [not_nonempty_iff_eq_empty.mp hn,card_empty]
        omega
  simpa only [mul_comm] using hh

/-- The bound includes quadruples with a repeated positive or negative summand. -/
lemma quads_nonexceptional {A : Finset ℕ} (hA : Good A) (i j : ℕ)
    (hNo : ∀ a ∈ A, ∀ b ∈ A, a+i ≠ b+j) :
    (quads A i j).card ≤ 2*A.card :=
  (quads_le_twice_positivePairs hA i j).trans
    (Nat.mul_le_mul_left 2 (positivePairs_nonexceptional hA i j hNo))

lemma quads_diagonal {A : Finset ℕ} (hA : Good A) (i : ℕ) :
    (quads A i i).card ≤ 2*A.card^2 := by
  have hp : (positivePairs A i i).card ≤ A.card^2 := by
    have hh := card_le_univ (positivePairs A i i)
    simpa only [Fintype.card_prod,Fintype.card_coe,pow_two] using hh
  exact (quads_le_twice_positivePairs hA i i).trans (Nat.mul_le_mul_left 2 hp)

lemma quads_exceptional {A : Finset ℕ} (hA : Good A) (i j : ℕ) (hij : i ≠ j)
    {a b : ℕ} (ha : a ∈ A) (hb : b ∈ A) (hab : a+i=b+j) :
    (quads A i j).card ≤ 4*A.card := by
  classical
  let a₀ : A := ⟨a,ha⟩
  have hab' : a ≠ b := by omega
  have hsub : positivePairs A i j ⊆
      ({a₀} ×ˢ univ) ∪ (univ ×ˢ {a₀}) := by
    rintro ⟨x,y⟩ hp
    obtain ⟨c,d,he⟩ := (mem_filter.mp hp).2
    dsimp only at he
    have hh : a+(c : ℕ)+d=b+x+y := by omega
    rcases three_sum_mem hA ha c.property d.property hb x.property y.property hh with
      h | h | h
    · exact (hab' h).elim
    · apply mem_union_left
      exact mem_product.mpr ⟨mem_singleton.mpr (Subtype.ext h.symm),mem_univ _⟩
    · apply mem_union_right
      exact mem_product.mpr ⟨mem_univ _,mem_singleton.mpr (Subtype.ext h.symm)⟩
  have hp : (positivePairs A i j).card ≤ 2*A.card := by
    have hh := (card_le_card hsub).trans (card_union_le _ _)
    simpa only [card_product,card_singleton,card_univ,Fintype.card_coe,
      one_mul,mul_one,two_mul] using hh
  have hh := (quads_le_twice_positivePairs hA i j).trans (Nat.mul_le_mul_left 2 hp)
  nlinarith only [hh]

lemma quads_bound {A : Finset ℕ} (hA : Good A) (i j : ℕ) :
    (quads A i j).card ≤ 2*A.card +
      (if i=j then 2*A.card^2 else 0) +
      (if ∃ a ∈ A, ∃ b ∈ A, a+i=b+j then 2*A.card else 0) := by
  classical
  by_cases hij : i=j
  · subst j
    have hh := quads_diagonal hA i
    simp only [if_true]
    omega
  · simp only [hij,if_false,add_zero]
    split_ifs with h
    · obtain ⟨a,ha,b,hb,hab⟩ := h
      have hh := quads_exceptional hA i j hij ha hb hab
      omega
    · exact quads_nonexceptional hA i j (by simpa only [not_exists,not_and] using h)

lemma card_fullQuads_eq (A : Finset ℕ) (u : ℕ) :
    (fullQuads A u).card = ∑ q : Quad (Fin u), (quads A (leftShift q) (rightShift q)).card := by
  classical
  simp only [fullQuads,quads,card_eq_sum_ones,sum_filter]
  rw [Fintype.sum_prod_type,sum_comm]

/-- Repeated summands require no separate cubic error term. The exceptional
shift count is retained explicitly so that local clustering bounds can be used. -/
lemma smoothed_card_bound {A : Finset ℕ} (hA : Good A) (u : ℕ) :
    (fullQuads A u).card ≤ 2*A.card*u^4+2*A.card^2*u^3+
      2*A.card*(badShiftQuads A u).card := by
  classical
  have hh := sum_le_sum (s := (univ : Finset (Quad (Fin u))))
    (fun q _ ↦ quads_bound hA (leftShift q) (rightShift q))
  rw [← card_fullQuads_eq,sum_add_distrib,sum_add_distrib] at hh
  have hd : (∑ q : Quad (Fin u), if leftShift q=rightShift q then 2*A.card^2 else 0) =
      2*A.card^2*(shiftFiber u 0 0).card := by
    simp only [shiftFiber,add_zero,← sum_filter,sum_const,nsmul_eq_mul,Nat.cast_id]
    ring
  have hb : (∑ q : Quad (Fin u),
      if ∃ a ∈ A, ∃ b ∈ A, a+leftShift q=b+rightShift q then 2*A.card else 0) =
      2*A.card*(badShiftQuads A u).card := by
    rw [← sum_filter]
    simp only [badShiftQuads,sum_const,nsmul_eq_mul,Nat.cast_id]
    ring
  rw [hd,hb] at hh
  have hc : (∑ _q : Quad (Fin u), 2*A.card) = 2*A.card*u^4 := by
    simp only [sum_const,card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    ring
  rw [hc] at hh
  exact hh.trans (Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul_left (2*A.card^2) (card_shiftFiber u 0 0)) _) _)

lemma smooth_energy_refined {A : Finset ℕ} (hA : Good A) (u : ℕ) :
    quadEnergy (fun p : A × Fin u ↦ ((p.1 : ℕ)+(p.2 : ℕ) : ℤ)) ≤
      2*(A.card : ℝ)*(u : ℝ)^4+2*(A.card : ℝ)^2*(u : ℝ)^3+
      2*(A.card : ℝ)*((badShiftQuads A u).card : ℝ) := by
  rw [quadEnergy_smooth_eq]
  exact_mod_cast smoothed_card_bound hA u

end FullQuadBound

/- Local clustering estimates for arbitrary B3 sets.
These are auxiliary estimates, not a settlement of Erdős 241. -/
namespace ShortDifferences
open Finset UnequalColouredPacking

lemma coloured_excess_bound {I J G : Type*} [Fintype I] [Fintype J]
    [AddCommGroup G] [Fintype G] (colour : J → I) (v : J → G)
    (hv : GoodColours colour v) :
    let E := ∑ i, (fibre colour i).card*((fibre colour i).card-1)
    (E+Fintype.card J)*(E+2) ≤ 2*Fintype.card G*Fintype.card J := by
  classical
  let q (i : I) := (fibre colour i).card
  let E := ∑ i, q i*(q i-1)
  change (E+Fintype.card J)*(E+2) ≤ _
  have hi (i : I) : q i*(E+2) ≤ 2*Fintype.card G := by
    let R := ∑ j ∈ univ.erase i, q j*(q j-1)
    have hp := full_signed_packing hv i
    have hp' : q i*(q i).choose 2+q i*R+q i ≤ Fintype.card G := by
      simpa only [q,R,mul_sum] using hp
    have hs : R+q i*(q i-1)=E := sum_erase_add _ _ (mem_univ i)
    have hpR := (Nat.cast_le (α := ℝ)).mpr hp'
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_choose_two] at hpR
    have hsR := congrArg (fun n : ℕ ↦ (n : ℝ)) hs
    simp only [Nat.cast_add,cast_mul_pred] at hsR
    have hsm := congrArg (fun x : ℝ ↦ (q i : ℝ)*x) hsR
    dsimp only at hsm
    have hR0 := mul_nonneg (Nat.cast_nonneg (q i) : (0 : ℝ) ≤ q i)
      (Nat.cast_nonneg R : (0 : ℝ) ≤ R)
    have hmain : (q i : ℝ)*((E : ℝ)+2) ≤ 2*Fintype.card G := by nlinarith
    exact_mod_cast hmain
  have hqsum : ∑ i, (q i : ℝ) = Fintype.card J := by
    exact_mod_cast sum_card_fibres colour
  have hEsum : ∑ i, ((q i : ℝ)^2-q i)=(E : ℝ) := by
    simp only [E,Nat.cast_sum,cast_mul_pred]
  have hsq : ∑ i, (q i : ℝ)^2 = (E : ℝ)+Fintype.card J := by
    rw [sum_sub_distrib,hqsum] at hEsum
    linarith
  have hweighted : ∑ i, (q i : ℝ)^2*((E : ℝ)+2) ≤
      ∑ i, (q i : ℝ)*(2*Fintype.card G) := by
    apply sum_le_sum
    intro i _
    have hR : (q i : ℝ)*((E : ℝ)+2) ≤ 2*Fintype.card G := by exact_mod_cast hi i
    have hh := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (q i) : (0 : ℝ) ≤ q i)
    simpa only [pow_two,mul_assoc] using hh
  rw [← sum_mul,← sum_mul,hsq,hqsum] at hweighted
  have hmain : ((E : ℝ)+Fintype.card J)*((E : ℝ)+2) ≤
      2*Fintype.card G*Fintype.card J := by nlinarith only [hweighted]
  exact_mod_cast hmain

def blockColour (A : Finset ℕ) (u : ℕ) (a : A) : A.image (fun x ↦ x/u) :=
  ⟨a.val/u,mem_image_of_mem _ a.property⟩

def blockValue (A : Finset ℕ) (u : ℕ) (a : A) : ZMod (3*u) := a.val%u

lemma block_compatible (A : Finset ℕ) (hA : B3Aux.Good A) (u : ℕ) (hu : 0 < u) :
    GoodColours (blockColour A u) (blockValue A u) := by
  classical
  intro s t hs ht hc he
  have hbound (r : Multiset A) (hr : r.card=3) :
      (r.map (fun a : A ↦ a.val%u)).sum < 3*u := by
    obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hr
    have ha := Nat.mod_lt a.val hu
    have hb := Nat.mod_lt b.val hu
    have hh := Nat.mod_lt c.val hu
    simp only [Multiset.insert_eq_cons,Multiset.map_cons,Multiset.map_singleton,
      Multiset.sum_cons,Multiset.sum_singleton]
    omega
  have hquot : (s.map (fun a : A ↦ a.val/u)).sum=(t.map (fun a : A ↦ a.val/u)).sum := by
    have hh := congrArg (fun r : Multiset (A.image (fun x ↦ x/u)) ↦
      (r.map Subtype.val).sum) hc
    simpa only [Multiset.map_map,Function.comp_def,blockColour] using hh
  have hremcast : (((s.map (fun a : A ↦ a.val%u)).sum : ℕ) : ZMod (3*u)) =
      (((t.map (fun a : A ↦ a.val%u)).sum : ℕ) : ZMod (3*u)) := by
    simpa only [Nat.cast_multiset_sum,Multiset.map_map,Function.comp_def,blockValue] using he
  have hrem : (s.map (fun a : A ↦ a.val%u)).sum=(t.map (fun a : A ↦ a.val%u)).sum := by
    have hh := congrArg ZMod.val hremcast
    simpa only [ZMod.val_natCast_of_lt (hbound s hs),
      ZMod.val_natCast_of_lt (hbound t ht)] using hh
  have hdecomp (r : Multiset A) : (r.map (fun a : A ↦ a.val)).sum =
      (r.map (fun a : A ↦ a.val%u)).sum+u*(r.map (fun a : A ↦ a.val/u)).sum := by
    induction r using Multiset.induction_on with
    | empty => simp
    | @cons a r ih =>
      simp only [Multiset.map_cons,Multiset.sum_cons]
      rw [ih,mul_add]
      have hh := Nat.mod_add_div a.val u
      omega
  apply Multiset.map_injective Subtype.val_injective
  apply hA (s.map Subtype.val) (t.map Subtype.val) (by simpa using hs) (by simpa using ht)
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hx
    exact a.property
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := Multiset.mem_map.mp hx
    exact a.property
  · rw [hdecomp,hdecomp,hquot,hrem]

lemma block_fibre_card (A : Finset ℕ) (u : ℕ) (i : A.image (fun x ↦ x/u)) :
    (fibre (blockColour A u) i).card=(A.filter (fun x ↦ x/u=i.val)).card := by
  classical
  have hmem (a : A) : a ∈ fibre (blockColour A u) i ↔ a.val/u=i.val := by
    simp [fibre,blockColour,Subtype.ext_iff]
  apply card_bij (fun a _ ↦ a.val)
  · intro a ha
    exact mem_filter.mpr ⟨a.property,(hmem a).mp ha⟩
  · intro a ha b hb he
    exact Subtype.ext he
  · intro a ha
    obtain ⟨ha,hq⟩ := mem_filter.mp ha
    exact ⟨⟨a,ha⟩,(hmem ⟨a,ha⟩).mpr hq,rfl⟩

def blockExcess (A : Finset ℕ) (u : ℕ) : ℕ :=
  ∑ i ∈ A.image (fun x ↦ x/u), (A.filter (fun x ↦ x/u=i)).card*
    ((A.filter (fun x ↦ x/u=i)).card-1)

/-- A uniform local clustering bound, with no assumption on the containing interval. -/
lemma block_excess_bound (A : Finset ℕ) (hA : B3Aux.Good A) (u : ℕ) (hu : 0 < u) :
    (blockExcess A u+A.card)*(blockExcess A u+2) ≤ 6*u*A.card := by
  haveI : NeZero (3*u) := ⟨by omega⟩
  have hh := coloured_excess_bound (blockColour A u) (blockValue A u) (block_compatible A hA u hu)
  have hE : (∑ i : A.image (fun x ↦ x/u), (fibre (blockColour A u) i).card*
      ((fibre (blockColour A u) i).card-1)) = blockExcess A u := by
    simp_rw [block_fibre_card]
    exact sum_coe_sort (A.image (fun x ↦ x/u)) (fun i : ℕ ↦
      (A.filter (fun x ↦ x/u=i)).card*((A.filter (fun x ↦ x/u=i)).card-1))
  dsimp only at hh
  rw [hE] at hh
  simpa only [Fintype.card_coe,ZMod.card,← mul_assoc,Nat.reduceMul] using hh

lemma good_translate (A : Finset ℕ) (hA : B3Aux.Good A) (s : ℕ) :
    B3Aux.Good (A.image (fun a ↦ a+s)) := by
  intro r t hr ht hrA htA he
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hr
  obtain ⟨d,e,f,rfl⟩ := Multiset.card_eq_three.mp ht
  obtain ⟨a,ha,rfl⟩ := mem_image.mp (hrA a (by simp))
  obtain ⟨b,hb,rfl⟩ := mem_image.mp (hrA b (by simp))
  obtain ⟨c,hc,rfl⟩ := mem_image.mp (hrA c (by simp))
  obtain ⟨d,hd,rfl⟩ := mem_image.mp (htA d (by simp))
  obtain ⟨e,heA,rfl⟩ := mem_image.mp (htA e (by simp))
  obtain ⟨f,hf,rfl⟩ := mem_image.mp (htA f (by simp))
  have hh := hA {a,b,c} {d,e,f} (by simp) (by simp) (by simp [ha,hb,hc])
    (by simp [hd,heA,hf]) (by simp only [Multiset.insert_eq_cons,Multiset.sum_cons,Multiset.sum_singleton] at he ⊢; omega)
  simpa using congrArg (Multiset.map (fun a : ℕ ↦ a+s)) hh

def withinPairs (A : Finset ℕ) (u : ℕ) : Finset (ℕ × ℕ) :=
  A.offDiag.filter (fun p ↦ p.1/u=p.2/u)

lemma withinPairs_card (A : Finset ℕ) (u : ℕ) : (withinPairs A u).card=blockExcess A u := by
  have hm : Set.MapsTo (fun p : ℕ × ℕ ↦ p.1/u) (withinPairs A u) (A.image (fun x ↦ x/u)) := by
    intro p hp
    change p ∈ withinPairs A u at hp
    have hpa : p.1 ∈ A := (mem_offDiag.mp (mem_filter.mp hp).1).1
    exact mem_image_of_mem (fun x : ℕ ↦ x/u) hpa
  rw [card_eq_sum_card_fiberwise (f := fun p : ℕ × ℕ ↦ p.1/u)
    (s := withinPairs A u) (t := A.image (fun x ↦ x/u)) hm]
  unfold blockExcess
  apply sum_congr rfl
  intro i hi
  have he : (withinPairs A u).filter (fun p ↦ p.1/u=i) =
      (A.filter (fun x ↦ x/u=i)).offDiag := by
    ext ⟨a,b⟩
    simp only [withinPairs,mem_filter,mem_offDiag]
    constructor
    · rintro ⟨⟨⟨ha,hb,hab⟩,he⟩,hai⟩
      exact ⟨⟨ha,hai⟩,⟨hb,he.symm.trans hai⟩,hab⟩
    · rintro ⟨⟨ha,hai⟩,⟨hb,hbi⟩,hab⟩
      exact ⟨⟨⟨ha,hb,hab⟩,hai.trans hbi.symm⟩,hai⟩
  rw [he,offDiag_card,Nat.mul_sub_left_distrib,Nat.mul_one]

lemma ordered_block_alternative (a b u : ℕ) (hu : 0 < u)
    (hab : a ≤ b) (hshort : b < a+u) :
    a/(2*u)=b/(2*u) ∨ (a+u)/(2*u)=(b+u)/(2*u) := by
  let q := a/(2*u)
  let r := a%(2*u)
  have hr : r < 2*u := Nat.mod_lt _ (by omega)
  have hdec : 2*u*q+r=a := Nat.div_add_mod a (2*u)
  by_cases hru : r < u
  · left
    have hb0 : q*(2*u) ≤ b := by nlinarith
    have hb1 : b < (q+1)*(2*u) := by nlinarith
    exact (Nat.div_eq_of_lt_le hb0 hb1).symm
  · right
    have ha0 : (q+1)*(2*u) ≤ a+u := by nlinarith
    have ha1 : a+u < ((q+1)+1)*(2*u) := by nlinarith
    have hb0 : (q+1)*(2*u) ≤ b+u := by nlinarith
    have hb1 : b+u < ((q+1)+1)*(2*u) := by nlinarith
    rw [Nat.div_eq_of_lt_le ha0 ha1,Nat.div_eq_of_lt_le hb0 hb1]

lemma block_alternative (a b u : ℕ) (hu : 0 < u)
    (hab : a < b+u) (hba : b < a+u) :
    a/(2*u)=b/(2*u) ∨ (a+u)/(2*u)=(b+u)/(2*u) := by
  rcases le_total a b with h | h
  · exact ordered_block_alternative a b u hu h hba
  · exact (ordered_block_alternative b a u hu h hab).elim
      (fun he ↦ Or.inl he.symm) (fun he ↦ Or.inr he.symm)

def shortPairs (A : Finset ℕ) (u : ℕ) : Finset (ℕ × ℕ) :=
  A.offDiag.filter (fun p ↦ p.1 < p.2+u ∧ p.2 < p.1+u)

lemma shortPairs_le_excesses (A : Finset ℕ) (u : ℕ) (hu : 0 < u) :
    (shortPairs A u).card ≤ blockExcess A (2*u)+
      blockExcess (A.image (fun a ↦ a+u)) (2*u) := by
  let P := A.offDiag.filter (fun p ↦ (p.1+u)/(2*u)=(p.2+u)/(2*u))
  have hsub : shortPairs A u ⊆ withinPairs A (2*u) ∪ P := by
    intro p hp
    obtain ⟨hp,h1,h2⟩ := mem_filter.mp hp
    rcases block_alternative p.1 p.2 u hu h1 h2 with he | he
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,he⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,he⟩)
  have hP : P.card ≤ (withinPairs (A.image (fun a ↦ a+u)) (2*u)).card := by
    apply card_le_card_of_injOn (fun p : ℕ × ℕ ↦ (p.1+u,p.2+u))
    · intro p hp
      obtain ⟨hp,he⟩ := mem_filter.mp hp
      obtain ⟨ha,hb,hab⟩ := mem_offDiag.mp hp
      exact mem_filter.mpr ⟨mem_offDiag.mpr ⟨mem_image_of_mem _ ha,
        mem_image_of_mem _ hb,by simpa using hab⟩,he⟩
    · intro p hp q hq he
      apply Prod.ext
      · exact Nat.add_right_cancel (congrArg Prod.fst he)
      · exact Nat.add_right_cancel (congrArg Prod.snd he)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  rw [withinPairs_card] at hh
  rw [withinPairs_card] at hP
  omega

/-- Ordered pairs of distinct points at distance less than u obey a global
clustering estimate. Both orientations are included. -/
lemma shortPairs_square_bound (A : Finset ℕ) (hA : B3Aux.Good A) (u : ℕ) (hu : 0 < u) :
    (shortPairs A u).card^2 ≤ 48*u*A.card := by
  let B := A.image (fun a ↦ a+u)
  have hB : B3Aux.Good B := good_translate A hA u
  have hBc : B.card=A.card := card_image_of_injective _ (fun a b he ↦ Nat.add_right_cancel he)
  have h0 := block_excess_bound A hA (2*u) (by omega)
  have h1 := block_excess_bound B hB (2*u) (by omega)
  rw [hBc] at h1
  have he := shortPairs_le_excesses A u hu
  have h0' : (blockExcess A (2*u))^2 ≤ 12*u*A.card := by nlinarith only [h0]
  have h1' : (blockExcess B (2*u))^2 ≤ 12*u*A.card := by nlinarith only [h1]
  have h0R : (blockExcess A (2*u) : ℝ)^2 ≤ 12*(u : ℝ)*A.card := by exact_mod_cast h0'
  have h1R : (blockExcess B (2*u) : ℝ)^2 ≤ 12*(u : ℝ)*A.card := by exact_mod_cast h1'
  have heR : ((shortPairs A u).card : ℝ) ≤
      (blockExcess A (2*u) : ℝ)+(blockExcess B (2*u) : ℝ) := by exact_mod_cast he
  have hsR := pow_le_pow_left₀ (Nat.cast_nonneg (shortPairs A u).card) heR 2
  have hfin : ((shortPairs A u).card : ℝ)^2 ≤ 48*(u : ℝ)*A.card := by
    nlinarith [sq_nonneg ((blockExcess A (2*u) : ℝ)-(blockExcess B (2*u) : ℝ))]
  exact_mod_cast hfin

end ShortDifferences

/- Smoothed fourth-energy bounds with a local clustering error.
The leading coefficient is unchanged; this is not a settlement of Erdős 241. -/
namespace LocalSmoothedEnergy
open Finset MomentBound ShortDifferences

lemma badShiftQuads_local_bound (A : Finset ℕ) (u : ℕ) (_hu : 0 < u) :
    (badShiftQuads A u).card ≤ ((shortPairs A (2*u)).card+1)*u^3 := by
  classical
  have hsub : badShiftQuads A u ⊆ shiftFiber u 0 0 ∪
      (shortPairs A (2*u)).biUnion (fun p ↦ shiftFiber u p.1 p.2) := by
    intro q hq
    obtain ⟨a,ha,b,hb,he⟩ := (mem_filter.mp hq).2
    by_cases hab : a=b
    · apply mem_union_left
      exact mem_filter.mpr ⟨mem_univ _,by simp only [hab] at he; simpa [add_comm] using he⟩
    · have hl : leftShift q < 2*u := by
        have h1 := q.1.1.isLt
        have h2 := q.1.2.isLt
        dsimp only [leftShift]
        omega
      have hr : rightShift q < 2*u := by
        have h1 := q.2.1.isLt
        have h2 := q.2.2.isLt
        dsimp only [rightShift]
        omega
      have hp : (a,b) ∈ shortPairs A (2*u) :=
        mem_filter.mpr ⟨mem_offDiag.mpr ⟨ha,hb,hab⟩,by dsimp only; omega⟩
      exact mem_union_right _ (mem_biUnion.mpr ⟨(a,b),hp,
        mem_filter.mpr ⟨mem_univ _,by dsimp only; omega⟩⟩)
  have hh := (card_le_card hsub).trans (card_union_le _ _)
  have hb : ((shortPairs A (2*u)).biUnion (fun p ↦ shiftFiber u p.1 p.2)).card ≤
      (shortPairs A (2*u)).card*u^3 := by
    calc
      _ ≤ ∑ p ∈ shortPairs A (2*u), (shiftFiber u p.1 p.2).card := card_biUnion_le
      _ ≤ ∑ _p ∈ shortPairs A (2*u), u^3 := sum_le_sum (fun p _ ↦ card_shiftFiber u p.1 p.2)
      _ = _ := by simp
  have hd := card_shiftFiber u 0 0
  nlinarith only [hh,hb,hd]

lemma smooth_energy_local_integer {A : Finset ℕ} (hA : B3Aux.Good A) (u : ℕ) (hu : 0 < u) :
    (fullQuads A u).card ≤ 2*A.card*u^4+
      (2*A.card^2+2*A.card*((shortPairs A (2*u)).card+1))*u^3 := by
  have h0 := FullQuadBound.smoothed_card_bound hA u
  have h1 := Nat.mul_le_mul_left (2*A.card) (badShiftQuads_local_bound A u hu)
  nlinarith only [h0,h1]

lemma smooth_energy_local {A : Finset ℕ} (hA : B3Aux.Good A) (u : ℕ) (hu : 0 < u) :
    quadEnergy (fun p : A × Fin u ↦ ((p.1 : ℕ)+(p.2 : ℕ) : ℤ)) ≤
      2*(A.card : ℝ)*(u : ℝ)^4+
        (2*(A.card : ℝ)^2+2*(A.card : ℝ)*(1+Real.sqrt (96*(u : ℝ)*A.card)))*(u : ℝ)^3 := by
  have hH := shortPairs_square_bound A hA (2*u) (by omega)
  have hHR : ((shortPairs A (2*u)).card : ℝ)^2 ≤ 96*(u : ℝ)*A.card := by
    have hh := (Nat.cast_le (α := ℝ)).mpr hH
    push_cast at hh
    nlinarith only [hh]
  have hs0 : 0 ≤ Real.sqrt (96*(u : ℝ)*A.card) := Real.sqrt_nonneg _
  have hsq := Real.sq_sqrt (by positivity : 0 ≤ 96*(u : ℝ)*A.card)
  have hle : ((shortPairs A (2*u)).card : ℝ) ≤ Real.sqrt (96*(u : ℝ)*A.card) := by
    nlinarith
  have hcard : ((fullQuads A u).card : ℝ) ≤ 2*(A.card : ℝ)*(u : ℝ)^4+
      (2*(A.card : ℝ)^2+2*(A.card : ℝ)*(((shortPairs A (2*u)).card : ℝ)+1))*(u : ℝ)^3 := by
    exact_mod_cast smooth_energy_local_integer hA u hu
  rw [quadEnergy_smooth_eq]
  have hh := mul_le_mul_of_nonneg_left hle (by positivity : 0 ≤ 2*(A.card : ℝ)*(u : ℝ)^3)
  nlinarith only [hcard,hh]

/-- Smoothing at a scale much larger than |A| already gives leading energy
coefficient two. No hypothesis on the diameter of A is used here. -/
lemma smooth_energy_scale {A : Finset ℕ} (hA : B3Aux.Good A) (hAn : 0 < A.card)
    (k u : ℕ) (hk : 0 < k) (hu : k^2*A.card ≤ u) :
    (k : ℝ)*quadEnergy (fun p : A × Fin u ↦ ((p.1 : ℕ)+(p.2 : ℕ) : ℤ)) ≤
      (2*(k : ℝ)+24)*(A.card : ℝ)*(u : ℝ)^4 := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hn1 : (1 : ℝ) ≤ A.card := by exact_mod_cast hAn
  have hkn : (k : ℝ)^2*A.card ≤ u := by exact_mod_cast hu
  have hu0 : 0 < u := lt_of_lt_of_le (Nat.mul_pos (pow_pos hk 2) hAn) hu
  have hE := smooth_energy_local hA u hu0
  have hk0 := Nat.cast_nonneg k (α := ℝ)
  have hn0 := Nat.cast_nonneg A.card (α := ℝ)
  have huR : (0 : ℝ) ≤ u := Nat.cast_nonneg u
  have hku : (k : ℝ) ≤ u := by
    have hh := mul_le_mul_of_nonneg_left hn1 (sq_nonneg (k : ℝ))
    nlinarith
  have hknu : (k : ℝ)*A.card ≤ u := by
    have hh := mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ (k : ℝ)^2 by nlinarith) hn0
    exact hh.trans hkn
  let S := Real.sqrt (96*(u : ℝ)*A.card)
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S^2=96*(u : ℝ)*A.card := Real.sq_sqrt (by positivity)
  have hksq : ((k : ℝ)*S)^2 ≤ (10*(u : ℝ))^2 := by
    rw [mul_pow,hS2]
    have hh := mul_le_mul_of_nonneg_left hkn (by positivity : 0 ≤ 96*(u : ℝ))
    nlinarith only [hh,sq_nonneg (u : ℝ)]
  have hkS : (k : ℝ)*S ≤ 10*(u : ℝ) := by
    nlinarith [mul_nonneg hk0 hS0]
  have herr : (k : ℝ)*(2*(A.card : ℝ)^2+2*A.card*(1+S)) ≤ 24*A.card*(u : ℝ) := by
    have hh := mul_le_mul_of_nonneg_left (show (k : ℝ)*A.card+k+k*S ≤ 12*(u : ℝ) by
      linarith) (by positivity : 0 ≤ 2*(A.card : ℝ))
    nlinarith only [hh]
  have h0 := mul_le_mul_of_nonneg_left hE hk0
  have h1 := mul_le_mul_of_nonneg_right herr (pow_nonneg huR 3)
  change (k : ℝ)*quadEnergy _ ≤ _
  dsimp only [S] at h1
  nlinarith only [h0,h1]

end LocalSmoothedEnergy

/- A finite cosine estimate using smoothing on scales larger than |A|.
This sharpens the error term, not the leading constant in Erdős 241. -/
open Finset Filter
namespace LocalCosineUpper
open CosineBound LocalSmoothedEnergy

lemma finite_bound {A : Finset ℕ} (hA : B3Aux.Good A)
    (N k u : ℕ) (hAn : 0 < A.card) (hk : 0 < k) (hu : k^2*A.card ≤ u)
    (hAN : A ⊆ Icc 1 N) (T : Finset ℕ) (c θ : ℕ → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) (D B : ℝ)
    (hgrid : (∑ d ∈ Icc (-((N+u : ℕ) : ℤ)) (N+u : ℕ),
      (cosineWeight T c θ ((d : ℝ)/(N+u : ℕ)))^2) ≤ D*(N+u)+B) :
    (k : ℝ)*(A.card : ℝ)^3 ≤ (2*k+24)*(D*(N+u)+B) := by
  let b : A × Fin u → ℤ := fun p ↦ (p.1 : ℕ)+(p.2 : ℕ)
  have hb (i j : A × Fin u) : b i-b j ∈ Icc (-((N+u : ℕ) : ℤ)) (N+u : ℕ) := by
    have hi := (mem_Icc.mp (hAN i.1.property)).2
    have hj := (mem_Icc.mp (hAN j.1.property)).2
    have hui := i.2.isLt
    have huj := j.2.isLt
    simp only [b,mem_Icc]
    omega
  have hlow := general_cosine_energy_lower b (N+u) hb T c θ hc
  have hE := smooth_energy_scale hA hAn k u hk hu
  have hEp : 0 ≤ MomentBound.quadEnergy b := by unfold MomentBound.quadEnergy; positivity
  have hM : 0 ≤ D*(N+u)+B := (by positivity : 0 ≤ ∑ d ∈
    Icc (-((N+u : ℕ) : ℤ)) (N+u : ℕ),
      (cosineWeight T c θ ((d : ℝ)/(N+u : ℕ)))^2).trans hgrid
  have h1 := mul_le_mul_of_nonneg_left (hlow.trans (mul_le_mul_of_nonneg_left hgrid hEp))
    (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have h2 := mul_le_mul_of_nonneg_right hE hM
  simp only [Fintype.card_prod,Fintype.card_coe,Fintype.card_fin,Nat.cast_mul] at h1
  have hnR : (0 : ℝ) < A.card := by exact_mod_cast hAn
  have huN : 0 < u := lt_of_lt_of_le (Nat.mul_pos (pow_pos hk 2) hAn) hu
  have huR : (0 : ℝ) < u := by exact_mod_cast huN
  apply (mul_le_mul_iff_right₀ (mul_pos hnR (pow_pos huR 4))).mp
  calc
    ((A.card : ℝ)*(u : ℝ)^4)*((k : ℝ)*(A.card : ℝ)^3) =
        (k : ℝ)*((A.card : ℝ)*(u : ℝ))^4 := by ring
    _ ≤ (k : ℝ)*(MomentBound.quadEnergy b*(D*(N+u)+B)) := h1
    _ = ((k : ℝ)*MomentBound.quadEnergy b)*(D*(N+u)+B) := by ring
    _ ≤ ((2*(k : ℝ)+24)*(A.card : ℝ)*(u : ℝ)^4)*(D*(N+u)+B) := h2
    _ = _ := by ring

lemma f_finite_bound (N k : ℕ) (hk : 0 < k)
    (T : Finset ℕ) (c θ : ℕ → ℝ) (hc : ∀ i ∈ T, 0 ≤ c i)
    (D B : ℝ) (hD : 0 ≤ D) (hB : 0 ≤ B)
    (hgrid : (∑ d ∈ Icc (-((N+k^2*f N 3 : ℕ) : ℤ)) (N+k^2*f N 3 : ℕ),
      (cosineWeight T c θ ((d : ℝ)/(N+k^2*f N 3 : ℕ)))^2) ≤
        D*(N+k^2*f N 3)+B) :
    (k : ℝ)*(f N 3 : ℝ)^3 ≤ (2*k+24)*(D*(N+k^2*f N 3)+B) := by
  classical
  by_cases hn : f N 3=0
  · simp only [hn,Nat.cast_zero,zero_pow (by decide : 3 ≠ 0),mul_zero]
    positivity
  have hmax : ∃ A : Finset ℕ, A ⊆ Icc 1 N ∧ B3Aux.Good A ∧ A.card=f N 3 := by
    let S := (Icc 1 N).powerset.filter (fun A ↦ B3Aux.Good A)
    have hS : S.Nonempty := by
      refine ⟨∅,mem_filter.mpr ⟨mem_powerset.mpr (empty_subset _),?_⟩⟩
      intro s t hs ht hsA htA he
      have hsempty : s=0 := Multiset.eq_zero_of_forall_notMem (fun x hx ↦ by simpa using hsA x hx)
      simp [hsempty] at hs
    obtain ⟨A,hAS,hcard⟩ := Finset.exists_mem_eq_sup S hS card
    refine ⟨A,mem_powerset.mp (mem_filter.mp hAS).1,(mem_filter.mp hAS).2,?_⟩
    exact hcard.symm
  obtain ⟨A,hAN,hA,hcard⟩ := hmax
  have hh := finite_bound hA N k (k^2*f N 3) (by omega) hk (by rw [hcard])
    hAN T c θ hc D B (by simpa only [Nat.cast_mul,Nat.cast_pow] using hgrid)
  simpa only [hcard,Nat.cast_mul,Nat.cast_pow] using hh

end LocalCosineUpper

/- A first-order grid-error bound for finite cosine weights. -/
open Finset Filter
namespace CosineBound

lemma sinc_abs_eq (x : ℝ) : Real.sinc |x|=Real.sinc x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h,Real.sinc_neg]

lemma sinc_lower_small {x : ℝ} (hx : |x| ≤ 1) : 1-|x|/4 ≤ Real.sinc x := by
  by_cases hz : x=0
  · simp [hz]
  have hp : 0 < |x| := abs_pos.mpr hz
  have hs := (Real.sin_gt_sub_cube hp hx).le
  have hpow : |x|^3 ≤ |x|^2 := by nlinarith [mul_le_mul_of_nonneg_left hx (sq_nonneg |x|)]
  rw [← sinc_abs_eq,Real.sinc_of_ne_zero hp.ne']
  apply (le_div_iff₀ hp).mpr
  nlinarith

lemma cos_grid_quotient (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθ : θ ≠ 0)
    (hs : Real.sinc (θ/(2*n)) ≠ 0) :
    cosGrid n θ = Real.sin (θ+θ/(2*n))/((θ/2)*Real.sinc (θ/(2*n))) := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hh0 : θ/(2*n) ≠ 0 := div_ne_zero hθ (mul_ne_zero (by norm_num) hn0)
  have hSn : Real.sin (θ/(2*n)) ≠ 0 := by
    rw [Real.sinc_of_ne_zero hh0] at hs
    exact (div_ne_zero_iff.mp hs).1
  have hi := cos_grid_identity n (θ/n)
  have hf (d : ℤ) : (d : ℝ)*(θ/n)=θ*((d : ℝ)/n) := by ring
  simp_rw [hf] at hi
  have he1 : θ/(n : ℝ)/2=θ/(2*n) := by ring
  have he2 : ((n : ℝ)+1/2)*(θ/n)=θ+θ/(2*n) := by field_simp
  rw [he1,he2] at hi
  rw [← hi,Real.sinc_of_ne_zero hh0]
  dsimp only [cosGrid]
  have hSn' : Real.sin (θ/((n : ℝ)*2)) ≠ 0 := by simpa only [mul_comm] using hSn
  field_simp [hSn,hSn']

lemma cos_grid_error (n : ℕ) (hn : 0 < n) (θ : ℝ) (hθn : |θ| ≤ 2*n) :
    |cosGrid n θ-2*Real.sinc θ| ≤ 2/(n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hz : θ=0
  · subst θ
    have he : cosGrid n 0=(2*(n : ℝ)+1)/n := by
      have hh := MomentBound.sum_symmetric_pow_zero n
      simpa [cosGrid] using congrArg (fun x : ℝ ↦ x/n) hh
    rw [he,Real.sinc_zero,mul_one]
    have hh : (2*(n : ℝ)+1)/n-2=1/n := by field_simp; ring
    rw [hh,abs_of_pos (one_div_pos.mpr hnR)]
    exact div_le_div_of_nonneg_right (by norm_num) hnR.le
  let h : ℝ := θ/(2*n)
  have hhabs : |h|=|θ|/(2*n) := by simp [h,abs_div,abs_of_pos hnR]
  have hh1 : |h| ≤ 1 := by rw [hhabs]; apply (div_le_one (by positivity)).mpr; exact hθn
  have hsinc := sinc_lower_small hh1
  have hsinc' : (3 : ℝ)/4 ≤ Real.sinc h := by linarith
  have hsincp : 0 < Real.sinc h := by linarith
  have hsinc0 : Real.sinc h ≠ 0 := hsincp.ne'
  have herr : |1-Real.sinc h| ≤ |h|/4 := by
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.sinc_le_one h))]
    linarith
  have hnum : |Real.sin (θ+h)-Real.sinc h*Real.sin θ| ≤ (5 : ℝ)/4*|h| := by
    calc
      _ = |(Real.sin (θ+h)-Real.sin θ)+(1-Real.sinc h)*Real.sin θ| := by congr 1; ring
      _ ≤ |Real.sin (θ+h)-Real.sin θ|+|(1-Real.sinc h)*Real.sin θ| := abs_add_le _ _
      _ ≤ |h|+|1-Real.sinc h| *1 := by
        rw [abs_mul]
        apply add_le_add
        · simpa only [add_sub_cancel_left] using Real.abs_sin_sub_sin_le (θ+h) θ
        · exact mul_le_mul_of_nonneg_left (Real.abs_sin_le_one θ) (abs_nonneg _)
      _ ≤ (5 : ℝ)/4*|h| := by linarith
  have hident : cosGrid n θ-2*Real.sinc θ =
      (Real.sin (θ+h)-Real.sinc h*Real.sin θ)/((θ/2)*Real.sinc h) := by
    rw [cos_grid_quotient n hn θ hz hsinc0,Real.sinc_of_ne_zero hz]
    change Real.sin (θ+h)/((θ/2)*Real.sinc h)-2*(Real.sin θ/θ)=_
    field_simp
  have hden : 0 < (|θ|/2)*Real.sinc h := by positivity
  rw [hident,abs_div,abs_mul,abs_div,abs_of_pos hsincp,show |(2 : ℝ)|=2 by norm_num]
  apply (div_le_iff₀ hden).mpr
  have hnh := mul_le_mul_of_nonneg_right hnum hnR.le
  have hhh : |h| *(n : ℝ)=|θ|/2 := by rw [hhabs]; field_simp
  have hnnum : |Real.sin (θ+h)-Real.sinc h*Real.sin θ| *(n : ℝ) ≤
      |θ| *Real.sinc h := by
    have hm := mul_le_mul_of_nonneg_left hsinc' (abs_nonneg θ)
    nlinarith only [hnh,hhh,hm,abs_nonneg θ]
  have he : (2/(n : ℝ)*((|θ|/2)*Real.sinc h))*(n : ℝ)=|θ| *Real.sinc h := by
    field_simp
  nlinarith only [hnnum,he,hnR]

lemma cos_grid_eventually_le (θ : ℝ) :
    ∀ᶠ n : ℕ in atTop, cosGrid n θ ≤ 2*Real.sinc θ+2/(n : ℝ) := by
  obtain ⟨L,hL⟩ := exists_nat_gt |θ|
  filter_upwards [eventually_ge_atTop (max L 1)] with n hn
  have hn0 : 0 < n := by omega
  have hLn : (L : ℝ) ≤ n := by exact_mod_cast (show L ≤ n by omega)
  have hh := cos_grid_error n hn0 θ (by linarith [Nat.cast_nonneg n (α := ℝ)])
  linarith [(abs_le.mp hh).2]

end CosineBound

/- Affine grid-sum bounds for positive finite cosine weights. -/
open Finset Filter
namespace CosineBound

def GridUpper (w : ℝ → ℝ) (D B : ℝ) : Prop :=
  ∀ᶠ n : ℕ in atTop, (n : ℝ)*grid w n ≤ D*n+B

lemma GridUpper.add {w v : ℝ → ℝ} {D B E C : ℝ}
    (hw : GridUpper w D B) (hv : GridUpper v E C) :
    GridUpper (fun x ↦ w x+v x) (D+E) (B+C) := by
  filter_upwards [hw,hv] with n hn hm
  rw [grid_add]
  nlinarith only [hn,hm]

lemma GridUpper.const_mul {w : ℝ → ℝ} {D B : ℝ}
    (hw : GridUpper w D B) (a : ℝ) (ha : 0 ≤ a) :
    GridUpper (fun x ↦ a*w x) (a*D) (a*B) := by
  filter_upwards [hw] with n hn
  rw [grid_const_mul]
  have hh := mul_le_mul_of_nonneg_left hn ha
  nlinarith only [hh]

lemma GridUpper.sum {ι : Type*} (T : Finset ι) (w : ι → ℝ → ℝ) (D B : ι → ℝ)
    (h : ∀ i ∈ T, GridUpper (w i) (D i) (B i)) :
    GridUpper (fun x ↦ ∑ i ∈ T, w i x) (∑ i ∈ T, D i) (∑ i ∈ T, B i) := by
  have hh : ∀ᶠ n : ℕ in atTop, ∀ i ∈ T, (n : ℝ)*grid (w i) n ≤ D i*n+B i :=
    (eventually_all_finset T).mpr h
  filter_upwards [hh] with n hn
  rw [grid_sum,mul_sum]
  have hm := sum_le_sum hn
  simpa only [sum_add_distrib,← sum_mul] using hm

lemma gridUpper_cos (θ : ℝ) : GridUpper (fun x ↦ Real.cos (θ*x)) (2*Real.sinc θ) 2 := by
  filter_upwards [cos_grid_eventually_le θ,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hh := mul_le_mul_of_nonneg_left hn hnR.le
  have he : (n : ℝ)*(2*Real.sinc θ+2/(n : ℝ))=(2*Real.sinc θ)*n+2 := by field_simp
  rw [he] at hh
  exact hh

lemma gridUpper_one : GridUpper (fun _ ↦ 1) 2 2 := by
  simpa only [zero_mul,Real.cos_zero,Real.sinc_zero,mul_one] using gridUpper_cos 0

lemma gridUpper_cos_mul (a b : ℝ) :
    GridUpper (fun x ↦ Real.cos (a*x)*Real.cos (b*x))
      (Real.sinc (a-b)+Real.sinc (a+b)) 2 := by
  have hh := ((gridUpper_cos (a-b)).add (gridUpper_cos (a+b))).const_mul (1/2) (by norm_num)
  have he : (fun x ↦ (1/2)*(Real.cos ((a-b)*x)+Real.cos ((a+b)*x))) =
      (fun x ↦ Real.cos (a*x)*Real.cos (b*x)) := by
    funext x
    simp only [sub_mul,add_mul,Real.cos_sub,Real.cos_add]
    ring
  rw [he] at hh
  convert hh using 1 <;> ring

noncomputable def gridError (T : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  2*(1+∑ i ∈ T, c i)^2

lemma gridError_nonneg (T : Finset ℕ) (c : ℕ → ℝ) : 0 ≤ gridError T c := by
  unfold gridError
  positivity

lemma cosineWeight_grid_upper (T : Finset ℕ) (c θ : ℕ → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    GridUpper (fun x ↦ (cosineWeight T c θ x)^2)
      (generalDenominator T c θ) (gridError T c) := by
  have h1 := (GridUpper.sum T (fun i x ↦ c i*Real.cos (θ i*x))
    (fun i ↦ c i*(2*Real.sinc (θ i))) (fun i ↦ c i*2)
    (fun i hi ↦ (gridUpper_cos (θ i)).const_mul (c i) (hc i hi))).const_mul 2 (by norm_num)
  have h2 := GridUpper.sum T (fun i x ↦ ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)))
    (fun i ↦ ∑ j ∈ T, (c i*c j)*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)))
    (fun i ↦ ∑ j ∈ T, (c i*c j)*2) (fun i hi ↦
      GridUpper.sum T (fun j x ↦ (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)))
        (fun j ↦ (c i*c j)*(Real.sinc (θ i-θ j)+Real.sinc (θ i+θ j)))
        (fun j ↦ (c i*c j)*2) (fun j hj ↦
          (gridUpper_cos_mul (θ i) (θ j)).const_mul (c i*c j) (mul_nonneg (hc i hi) (hc j hj))))
  have hh := (gridUpper_one.add h1).add h2
  have he : (fun x ↦ (1+2*(∑ i ∈ T, c i*Real.cos (θ i*x)))+
      ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x))) =
      (fun x ↦ (cosineWeight T c θ x)^2) := by
    funext x
    dsimp only [cosineWeight]
    have hp : (∑ i ∈ T, c i*Real.cos (θ i*x))^2 =
        ∑ i ∈ T, ∑ j ∈ T, (c i*c j)*(Real.cos (θ i*x)*Real.cos (θ j*x)) := by
      rw [pow_two,mul_sum]
      apply sum_congr rfl
      intro i hi
      rw [sum_mul]
      apply sum_congr rfl
      intro j hj
      ring
    rw [← hp]
    ring
  rw [he] at hh
  have hlin : (∑ i ∈ T, c i*(2*Real.sinc (θ i)))=2*∑ i ∈ T, c i*Real.sinc (θ i) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro i hi
    ring
  have hquad : (∑ i ∈ T, ∑ j ∈ T, (c i*c j)*2)=2*(∑ i ∈ T, c i)^2 := by
    rw [pow_two,sum_mul_sum,mul_sum]
    apply sum_congr rfl
    intro i hi
    rw [mul_sum]
    apply sum_congr rfl
    intro j hj
    ring
  rw [hlin,hquad,← sum_mul] at hh
  convert hh using 1 <;> simp only [generalDenominator,gridError] <;> ring

lemma cosineWeight_sum_eventually_le (T : Finset ℕ) (c θ : ℕ → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    ∀ᶠ n : ℕ in atTop, (∑ d ∈ Icc (-(n : ℤ)) n,
      (cosineWeight T c θ ((d : ℝ)/n))^2) ≤
        generalDenominator T c θ*n+gridError T c := by
  filter_upwards [cosineWeight_grid_upper T c θ hc,eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  simpa only [grid,mul_div_cancel₀ _ hn0] using hn

end CosineBound

/- A quantitative error term for the finite cosine upper bound.
The leading coefficient is unchanged, so this does not settle Erdős 241. -/
open Finset Filter
namespace QuantitativeCosineUpper
open CosineBound LocalCosineUpper

lemma optimize_arithmetic (n N s k D B : ℝ)
    (hn : 1 ≤ n) (hs : 1 ≤ s) (hsn : s^3=n)
    (hk : 0 < k) (hsk : s^2 ≤ k) (hks : k ≤ 4*s^2)
    (hD : 0 ≤ D) (hB : 0 ≤ B) (hN : N ≤ 64*n^3)
    (hraw : k*n^3 ≤ (2*k+24)*(D*(N+k^2*n)+B)) :
    n^3 ≤ 2*D*N+2000*(D+B+1)*s*n^2 := by
  have hn0 : 0 ≤ n := by linarith
  have hs0 : 0 ≤ s := by linarith
  have hk1 : 1 ≤ k := by nlinarith [sq_nonneg (s-1)]
  have hunit : 1 ≤ s*n^2 := by
    have hn2 : 1 ≤ n^2 := by nlinarith
    nlinarith
  have hkn : n^3 ≤ k*s*n^2 := by
    calc
      n^3 = (s^2*s)*n^2 := by rw [← pow_succ,hsn]; ring
      _ ≤ k*s*n^2 := by gcongr
  have hkk : k^2*n ≤ 16*s*n^2 := by
    have hh := pow_le_pow_left₀ hk.le hks 2
    have hm := mul_le_mul_of_nonneg_right hh hn0
    have he : (4*s^2)^2*n=16*s*n^2 := by rw [← hsn]; ring
    rwa [he] at hm
  have hNbig : 24*D*N ≤ 1536*D*k*s*n^2 := by
    have hh := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 24*D)
    have hm := mul_le_mul_of_nonneg_left hkn (by positivity : 0 ≤ 1536*D)
    nlinarith only [hh,hm]
  have hrest : 26*k*(D*k^2*n+B) ≤ (416*D+26*B)*k*s*n^2 := by
    have h1 := mul_le_mul_of_nonneg_left hkk hD
    have h2 := mul_le_mul_of_nonneg_left hunit hB
    have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity : 0 ≤ 26*k)
    nlinarith only [hh]
  have hcoef : 2*k+24 ≤ 26*k := by linarith
  have hx := mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ D*k^2*n+B)
  have hmid : k*n^3 ≤ 2*D*k*N+(1952*D+26*B)*k*s*n^2 := by
    nlinarith only [hraw,hx,hNbig,hrest]
  have hconst : 1952*D+26*B ≤ 2000*(D+B+1) := by linarith
  have hlast := mul_le_mul_of_nonneg_right hconst (by positivity : 0 ≤ k*s*n^2)
  apply (mul_le_mul_iff_right₀ hk).mp
  nlinarith only [hmid,hlast]

lemma root_excess (n a s K : ℝ) (hn : 0 < n) (ha : 0 ≤ a) (hs : 0 ≤ s) (hK : 0 ≤ K)
    (h : n^3 ≤ a^3+K*s*n^2) : n ≤ a+K*s := by
  by_cases hna : n ≤ a
  · exact hna.trans (le_add_of_nonneg_right (mul_nonneg hK hs))
  have han : 0 ≤ n-a := by linarith
  have hh := mul_nonneg han (show 0 ≤ n*a+a^2 by positivity)
  have hmid : (n-a)*n^2 ≤ K*s*n^2 := by nlinarith only [h,hh]
  have hsq : 0 < n^2 := sq_pos_of_pos hn
  have hle : n-a ≤ K*s := (mul_le_mul_iff_left₀ hsq).mp hmid
  linarith


/-- A fixed finite cosine weight gives an N^(1/9) error, with its original
leading coefficient. No numerical optimization is used in this theorem. -/
lemma f_ninth_root_error (T : Finset ℕ) (c θ : ℕ → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    ∀ᶠ N : ℕ in atTop,
      (f N 3 : ℝ) ≤ (2*generalDenominator T c θ)^((1 : ℝ)/3)*(N : ℝ)^((1 : ℝ)/3)+
        (4000*(generalDenominator T c θ+gridError T c+1))*(N : ℝ)^((1 : ℝ)/9) := by
  let D := generalDenominator T c θ
  let B := gridError T c
  have hD : 0 ≤ D := generalDenominator_nonneg T c θ
  have hB : 0 ≤ B := gridError_nonneg T c
  obtain ⟨L,hL⟩ := eventually_atTop.mp (cosineWeight_sum_eventually_le T c θ hc)
  filter_upwards [eventually_ge_atTop (max L 8),f_cuberoot_bounds] with N hN hcoarse
  have hN8 : 8 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hrev : (N : ℝ) ≤ 64*(f N 3 : ℝ)^3 := by exact_mod_cast f_reverse_cube_bound N hN8
  have hnN : 0 < f N 3 := by
    by_contra hh
    have hz : f N 3=0 := by omega
    rw [hz] at hrev
    norm_num at hrev
    linarith
  let n : ℝ := f N 3
  have hn : 1 ≤ n := by dsimp [n]; exact_mod_cast hnN
  have hnp : 0 < n := by linarith
  let s : ℝ := n^((1 : ℝ)/3)
  have hs : 1 ≤ s := Real.one_le_rpow hn (by norm_num)
  have hs0 : 0 ≤ s := by linarith
  have hsn : s^3=n := by
    simpa only [s,one_div] using Real.rpow_inv_natCast_pow hnp.le (by decide : 3 ≠ 0)
  let t : ℕ := ⌈s⌉₊
  have hst : s ≤ (t : ℝ) := Nat.le_ceil s
  have ht : (t : ℝ) ≤ 2*s := by
    have hh := Nat.ceil_lt_add_one hs0
    dsimp only [t]
    linarith
  have htN : 0 < t := by
    have hh : (0 : ℝ) < t := by linarith
    exact_mod_cast hh
  let k : ℕ := t^2
  have hk : 0 < k := pow_pos htN 2
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk : s^2 ≤ (k : ℝ) := by
    simpa only [k,Nat.cast_pow] using pow_le_pow_left₀ hs0 hst 2
  have hks : (k : ℝ) ≤ 4*s^2 := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg t (α := ℝ)) ht 2
    simpa only [k,Nat.cast_pow,mul_pow,show (2 : ℝ)^2=4 by norm_num] using hh
  have hgrid := hL (N+k^2*f N 3) (by omega)
  have hraw := f_finite_bound N k hk T c θ hc D B hD hB (by
    simpa only [D,B,Nat.cast_add,Nat.cast_mul,Nat.cast_pow] using hgrid)
  have hopt := optimize_arithmetic n N s k D B hn hs hsn hkR hsk hks hD hB hrev hraw
  let R : ℝ := (N : ℝ)^((1 : ℝ)/3)
  let m : ℝ := (N : ℝ)^((1 : ℝ)/9)
  let a : ℝ := (2*D)^((1 : ℝ)/3)*R
  have hR0 : 0 ≤ R := Real.rpow_nonneg hNp.le _
  have hm0 : 0 ≤ m := Real.rpow_nonneg hNp.le _
  have ha0 : 0 ≤ a := mul_nonneg (Real.rpow_nonneg (by positivity) _) hR0
  have hR : R^3=(N : ℝ) := by
    simpa only [R,one_div] using Real.rpow_inv_natCast_pow hNp.le (by decide : 3 ≠ 0)
  have hm : m^3=R := by
    dsimp only [m,R]
    rw [← Real.rpow_mul_natCast hNp.le]
    norm_num
  have ha : a^3=2*D*N := by
    dsimp only [a]
    rw [mul_pow,hR]
    have hh : ((2*D)^((1 : ℝ)/3))^3=2*D := by
      simpa only [one_div] using Real.rpow_inv_natCast_pow (by positivity : 0 ≤ 2*D) (by decide : 3 ≠ 0)
    rw [hh]
  have hsm : s ≤ 2*m := by
    apply le_of_pow_le_pow_left₀ (by decide : 3 ≠ 0) (by positivity)
    rw [hsn,mul_pow,hm]
    change n ≤ 2^3*R
    have hh : n ≤ 3*R := hcoarse.1
    nlinarith only [hh,hR0]
  have hroot := root_excess n a s (2000*(D+B+1)) hnp ha0 hs0 (by positivity) (by rwa [ha])
  have herr := mul_le_mul_of_nonneg_left hsm (by positivity : 0 ≤ 2000*(D+B+1))
  change n ≤ a+(4000*(D+B+1))*m
  nlinarith only [hroot,herr]

/-- Absorbing the finitely many small values gives an all-N bound with the
same exact leading coefficient. -/
lemma f_ninth_root_error_global (T : Finset ℕ) (c θ : ℕ → ℝ)
    (hc : ∀ i ∈ T, 0 ≤ c i) :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      (f N 3 : ℝ) ≤ (2*generalDenominator T c θ)^((1 : ℝ)/3)*(N : ℝ)^((1 : ℝ)/3)+
        K*(N : ℝ)^((1 : ℝ)/9) := by
  let a := (2*generalDenominator T c θ)^((1 : ℝ)/3)
  let K := 4000*(generalDenominator T c θ+gridError T c+1)
  have ha : 0 ≤ a := Real.rpow_nonneg (by positivity [generalDenominator_nonneg T c θ]) _
  have hK : 0 < K := by
    have hd := generalDenominator_nonneg T c θ
    have hb := gridError_nonneg T c
    dsimp only [K]
    positivity
  obtain ⟨M,hM⟩ := eventually_atTop.mp (f_ninth_root_error T c θ hc)
  refine ⟨K+M+1,by positivity,fun N ↦ ?_⟩
  have hr : 0 ≤ (N : ℝ)^((1 : ℝ)/9) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hfirst : 0 ≤ a*(N : ℝ)^((1 : ℝ)/3) := mul_nonneg ha (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  change (f N 3 : ℝ) ≤ a*(N : ℝ)^((1 : ℝ)/3)+(K+M+1)*(N : ℝ)^((1 : ℝ)/9)
  by_cases hNM : M ≤ N
  · have hh := hM N hNM
    have he := mul_le_mul_of_nonneg_right (show K ≤ K+(M : ℝ)+1 by linarith [Nat.cast_nonneg M (α := ℝ)]) hr
    change (f N 3 : ℝ) ≤ a*(N : ℝ)^((1 : ℝ)/3)+K*(N : ℝ)^((1 : ℝ)/9) at hh
    linarith
  · have hf : (f N 3 : ℝ) ≤ N := by exact_mod_cast f_le N 3
    by_cases hN : N=0
    · subst N
      have hz : (f 0 3 : ℝ)=0 := le_antisymm (by simpa using hf) (Nat.cast_nonneg _)
      rw [hz]
      positivity
    · have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
      have hpow : 1 ≤ (N : ℝ)^((1 : ℝ)/9) := Real.one_le_rpow hn1 (by norm_num)
      have hMN : (N : ℝ) ≤ M := by exact_mod_cast (show N ≤ M by omega)
      have hm := mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg M : (0 : ℝ) ≤ M)
      have he := mul_le_mul_of_nonneg_right (show (M : ℝ) ≤ K+M+1 by linarith) hr
      nlinarith only [hf,hMN,hm,he,hfirst]




end QuantitativeCosineUpper


/- A carry-aware three-tag encoding. Its disproof criterion remains conditional:
no unbounded family satisfying it is constructed here. -/
open Finset Filter
open scoped Asymptotics
namespace ThreeTagIntegerLift
open ColouredPacking TwoColourLift

/-- The carry when a pure colour-zero triple meets a pure colour-one triple. -/
def PureSeparated {J : Type*} (m : ℕ) (v : Fin 2 × J → ZMod m) : Prop :=
  ∀ a b c d e f : J,
    v (0,a)+v (0,b)+v (0,c) ≠ v (1,d)+v (1,e)+v (1,f)+1

noncomputable def code {J : Type*} (m : ℕ) [NeZero m]
    (v : Fin 2 × J → ZMod m) (a : Fin 2 × J) : ℕ :=
  3*(v a).val+a.1.val+1

lemma pure_contradiction {J : Type*} (m : ℕ) [NeZero m]
    (v : Fin 2 × J → ZMod m) (hp : PureSeparated m v)
    (a b c d e f : Fin 2 × J)
    (h₀ : a.1.val+b.1.val+c.1.val=0)
    (h₁ : d.1.val+e.1.val+f.1.val=3)
    (he : (v a).val+(v b).val+(v c).val=
      (v d).val+(v e).val+(v f).val+1) : False := by
  have hda := d.1.isLt
  have hea := e.1.isLt
  have hfa := f.1.isLt
  have ha : a=(0,a.2) := Prod.ext (Fin.ext (by change a.1.val=0; omega)) rfl
  have hb : b=(0,b.2) := Prod.ext (Fin.ext (by change b.1.val=0; omega)) rfl
  have hc : c=(0,c.2) := Prod.ext (Fin.ext (by change c.1.val=0; omega)) rfl
  have hd : d=(1,d.2) := Prod.ext (Fin.ext (by change d.1.val=1; omega)) rfl
  have he' : e=(1,e.2) := Prod.ext (Fin.ext (by change e.1.val=1; omega)) rfl
  have hf : f=(1,f.2) := Prod.ext (Fin.ext (by change f.1.val=1; omega)) rfl
  have hh := congrArg (fun n : ℕ ↦ (n : ZMod m)) he
  simp only [Nat.cast_add,ZMod.natCast_zmod_val,Nat.cast_one] at hh
  rw [ha,hb,hc,hd,he',hf] at hh
  exact hp a.2 b.2 c.2 d.2 e.2 f.2 hh

lemma triple_inj {J : Type*} (m : ℕ) [NeZero m]
    (v : Fin 2 × J → ZMod m) (hv : GoodFamily v) (hp : PureSeparated m v)
    (a b c d e f : Fin 2 × J)
    (he : code m v a+code m v b+code m v c=code m v d+code m v e+code m v f) :
    ({a,b,c} : Multiset (Fin 2 × J))={d,e,f} := by
  have ha := a.1.isLt
  have hb := b.1.isLt
  have hc := c.1.isLt
  have hd := d.1.isLt
  have he' := e.1.isLt
  have hf := f.1.isLt
  dsimp only [code] at he
  by_cases hcol : a.1.val+b.1.val+c.1.val=d.1.val+e.1.val+f.1.val
  · have htags : ({a.1,b.1,c.1} : Multiset (Fin 2))={d.1,e.1,f.1} := by
      apply binary_colour_multiset_eq (by simp) (by simp)
      simpa [add_assoc] using hcol
    apply hv a b c d e f htags
    have hval : (v a).val+(v b).val+(v c).val=(v d).val+(v e).val+(v f).val := by omega
    have hh := congrArg (fun n : ℕ ↦ (n : ZMod m)) hval
    simpa only [Nat.cast_add,ZMod.natCast_zmod_val] using hh
  · have hh : (a.1.val+b.1.val+c.1.val=0 ∧ d.1.val+e.1.val+f.1.val=3) ∨
        (a.1.val+b.1.val+c.1.val=3 ∧ d.1.val+e.1.val+f.1.val=0) := by omega
    rcases hh with ⟨h0,h1⟩ | ⟨h1,h0⟩
    · exact (pure_contradiction m v hp a b c d e f h0 h1 (by omega)).elim
    · exact (pure_contradiction m v hp d e f a b c h0 h1 (by omega)).elim

lemma multiset_inj {J : Type*} (m : ℕ) [NeZero m]
    (v : Fin 2 × J → ZMod m) (hv : GoodFamily v) (hp : PureSeparated m v)
    (s t : Multiset (Fin 2 × J)) (hs : s.card=3) (ht : t.card=3)
    (he : (s.map (code m v)).sum=(t.map (code m v)).sum) : s=t := by
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hs
  obtain ⟨d,e,f,rfl⟩ := Multiset.card_eq_three.mp ht
  exact triple_inj m v hv hp a b c d e f (by simpa [add_assoc] using he)

/-- An interval of length 3m suffices with the stated shifted-pure separation.
There is no coprimality assumption on m. -/
lemma integer_set_of_three_tag_fibres (m q : ℕ) (hm : 0 < m) (hq : 0 < q)
    (v : Fin 2 × Fin q → ZMod m) (hv : GoodFamily v) (hp : PureSeparated m v) :
    ∃ A : Finset ℕ, A ⊆ Icc 1 (3*m) ∧ A.card=2*q ∧ B3Aux.Good A := by
  haveI : NeZero m := ⟨by omega⟩
  haveI : Nonempty (Fin q) := ⟨⟨0,hq⟩⟩
  have hi : Function.Injective (code m v) := by
    intro a b he
    have hh := triple_inj m v hv hp a a a b b b (by rw [he])
    have hm : a ∈ ({b,b,b} : Multiset (Fin 2 × Fin q)) := hh ▸ (by simp)
    simpa using hm
  have hb (a : Fin 2 × Fin q) : 1 ≤ code m v a ∧ code m v a ≤ 3*m := by
    have hav := ZMod.val_lt (v a)
    have hac := a.1.isLt
    dsimp only [code]
    omega
  obtain ⟨A,hAN,hcard,hA⟩ := BoseConstruction.exists_set_of_code (3*m) 3
    (code m v) hi hb (multiset_inj m v hv hp)
  exact ⟨A,hAN,by simpa only [Fintype.card_prod,Fintype.card_fin] using hcard,hA⟩

/-- The original target's negation follows from an ACTUAL unbounded family
with shifted-pure separation and a fixed gain below (8/3)q^3. -/
lemma not_target_of_three_tag_gain (k : ℕ) (hk : 1 ≤ k)
    (hfam : ∀ B : ℕ, ∃ m q : ℕ, B ≤ q ∧ 0 < q ∧ 0 < m ∧
      ∃ v : Fin 2 × Fin q → ZMod m,
        GoodFamily v ∧ PureSeparated m v ∧ 3*(k+1)*m ≤ 8*k*q^3) :
    ¬ ((fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ)^((1 : ℝ)/3))) := by
  apply CounterCriterion.negation_iff_dense_sets.mpr
  refine ⟨k,hk,fun B ↦ ?_⟩
  obtain ⟨m,q,hBq,hq,hm,v,hv,hp,hgain⟩ := hfam B
  obtain ⟨A,hAN,hcard,hA⟩ := integer_set_of_three_tag_fibres m q hm hq v hv hp
  haveI : NeZero m := ⟨by omega⟩
  have hbound := one_colour_packing v hv (0 : Fin 2)
  simp only [Fintype.card_fin,ZMod.card] at hbound
  refine ⟨3*m,A,by omega,by omega,hAN,hA,?_⟩
  rw [hcard]
  nlinarith only [hgain]

end ThreeTagIntegerLift


/- The following auxiliary results improve a five-term counting constant.
They are not a settlement of the original conjecture below. -/
namespace ProjectiveBinaryLiftObstruction
variable {J G : Type*} [AddCommGroup G]
def GoodTriple (v : J → G) : Prop :=
  ∀ a b c d e f : J, v a+v b+v c=v d+v e+v f →
    ({a,b,c} : Multiset J)={d,e,f}
end ProjectiveBinaryLiftObstruction


/- Pair packings attached to non-cancelling two-versus-three representations.
These are auxiliary structural results, not a settlement of Erdős 241. -/
open Finset
namespace FiveBlockPacking
open ProjectiveBinaryLiftObstruction

variable {J G : Type*} [DecidableEq J] [AddCommGroup G]

omit [DecidableEq J] in
lemma multiset_inj {v : J → G} (hv : GoodTriple v)
    (s t : Multiset J) (hs : s.card=3) (ht : t.card=3)
    (he : (s.map v).sum=(t.map v).sum) : s=t := by
  obtain ⟨a,b,c,rfl⟩ := Multiset.card_eq_three.mp hs
  obtain ⟨d,e,f,rfl⟩ := Multiset.card_eq_three.mp ht
  exact hv a b c d e f (by simpa [add_assoc] using he)

lemma triple_set_inj {v : J → G} (hv : GoodTriple v)
    {s t : Finset J} (hs : s.card=3) (ht : t.card=3)
    (he : ∑ a ∈ s, v a = ∑ a ∈ t, v a) : s=t := by
  apply Finset.eq_of_veq
  exact multiset_inj hv s.val t.val hs ht he

lemma signed_pair_inj {v : J → G} (hv : GoodTriple v)
    {s t : Finset J} {c d : J} (hs : s.card=2) (ht : t.card=2)
    (hcs : c ∉ s)
    (he : (∑ a ∈ s, v a)-v c=(∑ a ∈ t, v a)-v d) : c=d ∧ s=t := by
  have hh := multiset_inj hv (d ::ₘ s.val) (c ::ₘ t.val)
    (by simpa using hs) (by simpa using ht) (by
      simp only [Multiset.map_cons,Multiset.sum_cons]
      change v d+(∑ a ∈ s,v a)=v c+(∑ a ∈ t,v a)
      have h := sub_eq_sub_iff_add_eq_add.mp he
      simpa only [add_comm] using h)
  have hcd : c=d := by
    have hm : c ∈ d ::ₘ s.val := hh.symm ▸ Multiset.mem_cons_self c t.val
    exact (Multiset.mem_cons.mp hm).resolve_right hcs
  subst d
  exact ⟨rfl,Finset.eq_of_veq (Multiset.cons_inj_right c |>.mp hh)⟩

abbrev Block (J : Type*) := Finset J × Finset J

def Valid (v : J → G) (x : G) (R : Block J) : Prop :=
  R.1.card=2 ∧ R.2.card=3 ∧ Disjoint R.1 R.2 ∧
    (∑ a ∈ R.1,v a)-(∑ a ∈ R.2,v a)=x

lemma erase_singleton {s : Finset J} {a : J} (hs : s.card=2) (ha : a ∈ s) :
    ∃ b, s.erase a={b} ∧ b ∈ s ∧ b ≠ a := by
  have hc : (s.erase a).card=1 := by rw [card_erase_of_mem ha,hs]
  obtain ⟨b,hb⟩ := card_eq_one.mp hc
  refine ⟨b,hb,?_,?_⟩
  · exact (mem_erase.mp (show b ∈ s.erase a by rw [hb]; simp)).2
  · exact (mem_erase.mp (show b ∈ s.erase a by rw [hb]; simp)).1

lemma cross_rigidity {v : J → G} (hv : GoodTriple v) {x : G}
    {R S : Block J} (hR : Valid v x R) (hS : Valid v x S)
    {a c : J} (haR : a ∈ R.1) (haS : a ∈ S.1)
    (hcR : c ∈ R.2) (hcS : c ∈ S.2) : R=S := by
  obtain ⟨b,hb,hbR,hba⟩ := erase_singleton hR.1 haR
  obtain ⟨d,hd,hdS,hda⟩ := erase_singleton hS.1 haS
  have hpR := sum_erase_add R.1 v haR
  have hpS := sum_erase_add S.1 v haS
  rw [hb,sum_singleton] at hpR
  rw [hd,sum_singleton] at hpS
  have hnR := sum_erase_add R.2 v hcR
  have hnS := sum_erase_add S.2 v hcS
  have he : (∑ j ∈ R.2.erase c,v j)-v b=(∑ j ∈ S.2.erase c,v j)-v d := by
    have hh := hR.2.2.2.trans hS.2.2.2.symm
    rw [← hpR,← hpS,← hnR,← hnS] at hh
    apply neg_injective
    have hh' := add_left_cancel (a := v a-v c)
      (show (v a-v c)+(v b-(∑ j ∈ R.2.erase c,v j))=
        (v a-v c)+(v d-(∑ j ∈ S.2.erase c,v j)) by
          convert hh using 1 <;> abel)
    convert hh' using 1 <;> abel
  obtain ⟨hbd,hneg⟩ := signed_pair_inj hv
    (by rw [card_erase_of_mem hcR,hR.2.1])
    (by rw [card_erase_of_mem hcS,hS.2.1])
    (fun h ↦ disjoint_left.mp hR.2.2.1 hbR (mem_erase.mp h).2) he
  have hpos : R.1=S.1 := by
    rw [← insert_erase haR,← insert_erase haS,hb,hd,hbd]
  have hneg' : R.2=S.2 := by
    rw [← insert_erase hcR,← insert_erase hcS,hneg]
  exact Prod.ext hpos hneg'

lemma positive_pair_rigidity {v : J → G} (hv : GoodTriple v) {x : G}
    {R S : Block J} (hR : Valid v x R) (hS : Valid v x S)
    (hp : R.1=S.1) : R=S := by
  apply Prod.ext hp
  apply triple_set_inj hv hR.2.1 hS.2.1
  have he := hR.2.2.2.trans hS.2.2.2.symm
  rw [hp] at he
  exact sub_right_inj.mp he

lemma negative_pair_rigidity {v : J → G} (hv : GoodTriple v) {x : G}
    {R S : Block J} (hR : Valid v x R) (hS : Valid v x S)
    {c d : J} (hcd : c ≠ d)
    (hcR : c ∈ R.2) (hdR : d ∈ R.2)
    (hcS : c ∈ S.2) (hdS : d ∈ S.2) : R=S := by
  have hdR' : d ∈ R.2.erase c := mem_erase.mpr ⟨hcd.symm,hdR⟩
  have hdS' : d ∈ S.2.erase c := mem_erase.mpr ⟨hcd.symm,hdS⟩
  obtain ⟨e,he,heR,hed⟩ := erase_singleton
    (by rw [card_erase_of_mem hcR,hR.2.1]) hdR'
  obtain ⟨f,hf,hfS,hfd⟩ := erase_singleton
    (by rw [card_erase_of_mem hcS,hS.2.1]) hdS'
  have hsR := sum_erase_add R.2 v hcR
  have hsR' := sum_erase_add (R.2.erase c) v hdR'
  rw [he,sum_singleton] at hsR'
  have hsS := sum_erase_add S.2 v hcS
  have hsS' := sum_erase_add (S.2.erase c) v hdS'
  rw [hf,sum_singleton] at hsS'
  have hh : (∑ j ∈ R.1,v j)-v e=(∑ j ∈ S.1,v j)-v f := by
    have hh := hR.2.2.2.trans hS.2.2.2.symm
    rw [← hsR,← hsS,← hsR',← hsS'] at hh
    apply add_right_cancel (b := -v d-v c)
    convert hh using 1 <;> abel
  obtain ⟨hef,hpos⟩ := signed_pair_inj hv hR.1 hS.1
    (fun h ↦ disjoint_left.mp hR.2.2.1 h (mem_erase.mp heR).2) hh
  exact positive_pair_rigidity hv hR hS hpos

noncomputable def cross (F : Finset (Block J)) : Finset (J × J) :=
  F.biUnion (fun R ↦ R.1 ×ˢ R.2)

lemma cross_disjoint {v : J → G} (hv : GoodTriple v) {x : G}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    (F : Set (Block J)).PairwiseDisjoint (fun R ↦ R.1 ×ˢ R.2) := by
  intro R hR S hS hRS
  apply disjoint_left.mpr
  intro p hp hq
  exact hRS (cross_rigidity hv (hF R hR) (hF S hS)
    (mem_product.mp hp).1 (mem_product.mp hq).1
    (mem_product.mp hp).2 (mem_product.mp hq).2)

lemma cross_card {v : J → G} (hv : GoodTriple v) {x : G}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    (cross F).card=6*F.card := by
  classical
  rw [cross,card_biUnion (cross_disjoint hv hF)]
  have he (R : Block J) (hR : R ∈ F) : (R.1 ×ˢ R.2).card=6 := by
    rw [card_product,(hF R hR).1,(hF R hR).2.1]
  simp_rw [sum_congr rfl he]
  simp [mul_comm]

lemma cross_subset_offDiag [Fintype J] {v : J → G} {x : G}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    cross F ⊆ (univ : Finset J).offDiag := by
  classical
  intro p hp
  obtain ⟨R,hR,hp⟩ := mem_biUnion.mp hp
  refine mem_offDiag.mpr ⟨mem_univ _,mem_univ _,?_⟩
  intro he
  have hh := mem_product.mp hp
  exact disjoint_left.mp (hF R hR).2.2.1 hh.1 (he.symm ▸ hh.2)

lemma cross_packing [Fintype J] {v : J → G} (hv : GoodTriple v) {x : G}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    6*F.card ≤ Fintype.card J*(Fintype.card J-1) := by
  have hh := card_le_card (cross_subset_offDiag hF)
  rw [cross_card hv hF,offDiag_card,card_univ] at hh
  simpa [Nat.mul_sub_left_distrib] using hh

lemma cross_sum {v : J → G} (hv : GoodTriple v) {x : G}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    (w : J → ℝ) :
    (∑ p ∈ cross F,w p.1*w p.2)=
      ∑ R ∈ F,(∑ a ∈ R.1,w a)*(∑ b ∈ R.2,w b) := by
  classical
  rw [cross,sum_biUnion (cross_disjoint hv hF)]
  apply sum_congr rfl
  intro R hR
  rw [sum_product,← sum_mul_sum]

omit [DecidableEq J] in
lemma shifted_balance {v : J → ℝ} {x : ℝ} {R : Block J}
    (hR : Valid v x R) :
    (∑ a ∈ R.1,(v a+x))=(∑ a ∈ R.2,(v a+x)) := by
  simp only [sum_add_distrib,sum_const,nsmul_eq_mul,hR.1,hR.2.1,Nat.cast_ofNat]
  have hh := hR.2.2.2
  linarith

/-- The cross-pair products form a sum of squares after the prescribed shift. -/
lemma cross_sum_squares {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    (∑ p ∈ cross F,(v p.1+x)*(v p.2+x))=
      ∑ R ∈ F,(∑ a ∈ R.1,(v a+x))^2 := by
  rw [cross_sum hv hF (fun a ↦ v a+x)]
  apply sum_congr rfl
  intro R hR
  rw [← shifted_balance (hF R hR),pow_two]

lemma offDiag_product [Fintype J] (w : J → ℝ) :
    (∑ p ∈ (univ : Finset J).offDiag,w p.1*w p.2)=
      (∑ a,w a)^2-∑ a,(w a)^2 := by
  have hh := sum_union (s₁ := (univ : Finset J).diag)
    (s₂ := (univ : Finset J).offDiag) (f := fun p ↦ w p.1*w p.2)
    (disjoint_diag_offDiag _)
  rw [diag_union_offDiag,sum_diag,sum_product,← sum_mul_sum] at hh
  simpa [pow_two] using eq_sub_of_add_eq' hh.symm

/-- An exact weighted deficit identity, with no density or distribution assumptions. -/
lemma missing_cross_identity [Fintype J] {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    (∑ p ∈ (univ : Finset J).offDiag \ cross F,(v p.1+x)*(v p.2+x))=
      (∑ a,(v a+x))^2-(∑ a,(v a+x)^2)-
        ∑ R ∈ F,(∑ a ∈ R.1,(v a+x))^2 := by
  have hh := sum_sdiff (f := fun p : J × J ↦ (v p.1+x)*(v p.2+x))
    (cross_subset_offDiag hF)
  rw [cross_sum_squares hv hF,offDiag_product (fun a ↦ v a+x)] at hh
  linarith

lemma cross_linear_sums {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) :
    (∑ p ∈ cross F,(v p.1+x))=3*∑ R ∈ F,∑ a ∈ R.1,(v a+x) ∧
    (∑ p ∈ cross F,(v p.2+x))=2*∑ R ∈ F,∑ a ∈ R.1,(v a+x) := by
  classical
  constructor
  · rw [cross,sum_biUnion (cross_disjoint hv hF),mul_sum]
    apply sum_congr rfl
    intro R hR
    rw [sum_product]
    simp only [sum_const,nsmul_eq_mul,(hF R hR).2.1,Nat.cast_ofNat]
    rw [mul_sum]
  · rw [cross,sum_biUnion (cross_disjoint hv hF),mul_sum]
    apply sum_congr rfl
    intro R hR
    rw [sum_product]
    simp only [sum_const,nsmul_eq_mul,(hF R hR).1,Nat.cast_ofNat]
    rw [shifted_balance (hF R hR)]

lemma offDiag_fst [Fintype J] (w : J → ℝ) :
    (∑ p ∈ (univ : Finset J).offDiag,w p.1)=
      ((Fintype.card J : ℝ)-1)*∑ a,w a := by
  have hh := sum_union (s₁ := (univ : Finset J).diag)
    (s₂ := (univ : Finset J).offDiag) (f := fun p ↦ w p.1)
    (disjoint_diag_offDiag _)
  rw [diag_union_offDiag,sum_diag,sum_product] at hh
  simp only [sum_const,nsmul_eq_mul,card_univ,← mul_sum] at hh
  linarith

lemma offDiag_snd [Fintype J] (w : J → ℝ) :
    (∑ p ∈ (univ : Finset J).offDiag,w p.2)=
      ((Fintype.card J : ℝ)-1)*∑ a,w a := by
  have hh := sum_union (s₁ := (univ : Finset J).diag)
    (s₂ := (univ : Finset J).offDiag) (f := fun p ↦ w p.2)
    (disjoint_diag_offDiag _)
  rw [diag_union_offDiag,sum_diag,sum_product] at hh
  simp only [sum_const,nsmul_eq_mul,card_univ] at hh
  linarith

/-- Complete directed-pair saturation is impossible over the reals. This is
only a strict finite improvement, not a leading asymptotic bound. -/
lemma cross_ne_offDiag [Fintype J] {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    (hn : 2 ≤ Fintype.card J) : cross F ≠ (univ : Finset J).offDiag := by
  intro he
  obtain ⟨hfirst,hsecond⟩ := cross_linear_sums hv hF
  rw [he,offDiag_fst (fun a ↦ v a+x)] at hfirst
  rw [he,offDiag_snd (fun a ↦ v a+x)] at hsecond
  have hmean : (∑ a,(v a+x))=0 := by
    have hn' : (2 : ℝ) ≤ Fintype.card J := by exact_mod_cast hn
    have hh : ((Fintype.card J : ℝ)-1)*(∑ a,(v a+x))=0 := by linarith
    exact (mul_eq_zero.mp hh).resolve_left (by linarith)
  have hh := cross_sum_squares hv hF
  rw [he,offDiag_product (fun a ↦ v a+x),hmean,zero_pow (by decide),zero_sub] at hh
  have hsq : 0 ≤ ∑ R ∈ F,(∑ a ∈ R.1,(v a+x))^2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hzero : (∑ a,(v a+x)^2)=0 := by
    have hnonneg : 0 ≤ ∑ a,(v a+x)^2 := sum_nonneg (fun _ _ ↦ sq_nonneg _)
    linarith
  have hall (a : J) : v a+x=0 := by
    have hle := single_le_sum (f := fun a ↦ (v a+x)^2)
      (fun b _ ↦ sq_nonneg (v b+x)) (mem_univ a)
    rw [hzero] at hle
    exact sq_eq_zero_iff.mp (le_antisymm hle (sq_nonneg _))
  have hi : Function.Injective v := by
    intro a b hab
    have hm := hv a a a b b b (by rw [hab])
    have hmem : a ∈ ({b,b,b} : Multiset J) := hm ▸ (by simp)
    simpa using hmem
  have hsub : Subsingleton J := ⟨fun a b ↦ hi (by linarith [hall a,hall b])⟩
  haveI := hsub
  have hc : Fintype.card J ≤ 1 := Fintype.card_le_one_iff_subsingleton.mpr hsub
  omega

lemma cross_packing_strict [Fintype J] {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    (hn : 2 ≤ Fintype.card J) :
    6*F.card < Fintype.card J*(Fintype.card J-1) := by
  have hh := card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨cross_subset_offDiag hF,cross_ne_offDiag hv hF hn⟩)
  rw [cross_card hv hF,offDiag_card,card_univ] at hh
  simpa [Nat.mul_sub_left_distrib] using hh

end FiveBlockPacking


/- Quantitative local obstruction for nearly saturated five-block packings.
This is auxiliary work on Erdős 241, not a settlement. -/
open Finset
namespace FiveBlockGram
open ProjectiveBinaryLiftObstruction FiveBlockPacking

variable {J : Type*} [DecidableEq J]
open scoped Classical

def Supported (S : Finset J) (F : Finset (Block J)) : Prop :=
  ∀ R ∈ F, R.1 ⊆ S ∧ R.2 ⊆ S

noncomputable def posDegree (F : Finset (Block J)) (a : J) : ℝ :=
  ∑ R ∈ F, if a ∈ R.1 then 1 else 0
noncomputable def negDegree (F : Finset (Block J)) (a : J) : ℝ :=
  ∑ R ∈ F, if a ∈ R.2 then 1 else 0
noncomputable def incidence (R : Block J) (a : J) : ℝ :=
  (if a ∈ R.1 then 1 else 0)-(if a ∈ R.2 then 1 else 0)
noncomputable def gram (F : Finset (Block J)) (a b : J) : ℝ :=
  ∑ R ∈ F, incidence R a * incidence R b
noncomputable def crossHit (F : Finset (Block J)) (a b : J) : ℝ :=
  if (a,b) ∈ cross F then 1 else 0
noncomputable def missing (F : Finset (Block J)) (a b : J) : ℝ :=
  (1-crossHit F a b)+(1-crossHit F b a)
noncomputable def missingDegree (S : Finset J) (F : Finset (Block J)) (a : J) : ℝ :=
  ∑ b ∈ S.erase a, missing F a b

lemma indicator_sum_le_one {T : Type*} (F : Finset T) (p : T → Prop)
    [DecidablePred p] (hu : ∀ R ∈ F, ∀ S ∈ F, p R → p S → R=S) :
    (∑ R ∈ F, if p R then (1 : ℝ) else 0) ≤ 1 := by
  rw [sum_boole]
  norm_cast
  apply card_le_one.mpr
  intro R hR S hS
  exact hu R (mem_filter.mp hR).1 S (mem_filter.mp hS).1
    (mem_filter.mp hR).2 (mem_filter.mp hS).2

lemma indicator_sum_eq {T : Type*} (F : Finset T) (p : T → Prop)
    [DecidablePred p] (hu : ∀ R ∈ F, ∀ S ∈ F, p R → p S → R=S) :
    (∑ R ∈ F, if p R then (1 : ℝ) else 0)=if ∃ R ∈ F,p R then 1 else 0 := by
  by_cases hp : ∃ R ∈ F,p R
  · rw [if_pos hp]
    apply le_antisymm (indicator_sum_le_one F p hu)
    obtain ⟨R,hR,hp⟩ := hp
    have hh := single_le_sum (f := fun R ↦ if p R then (1 : ℝ) else 0)
      (fun a _ ↦ by dsimp only; split_ifs <;> norm_num) hR
    simpa [hp] using hh
  · rw [if_neg hp]
    apply sum_eq_zero
    intro R hR
    exact if_neg (fun h ↦ hp ⟨R,hR,h⟩)

lemma pair_of_two_members {P : Finset J} {a b : J} (hP : P.card=2)
    (hab : a ≠ b) (ha : a ∈ P) (hb : b ∈ P) : P={a,b} := by
  symm
  apply Finset.eq_of_subset_of_card_le (s := {a,b}) (t := P) (by
    intro j hj
    rcases mem_insert.mp hj with rfl | hj
    · exact ha
    · exact mem_singleton.mp hj ▸ hb)
  simp [hP,hab]

lemma gram_offDiag_le {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {a b : J} (hab : a ≠ b) : gram F a b ≤ missing F a b := by
  have hp := indicator_sum_le_one F (fun R ↦ a ∈ R.1 ∧ b ∈ R.1) (by
    intro R hR S hS hRP hSP
    apply positive_pair_rigidity hv (hF R hR) (hF S hS)
    rw [pair_of_two_members (hF R hR).1 hab hRP.1 hRP.2,
      pair_of_two_members (hF S hS).1 hab hSP.1 hSP.2])
  have hn := indicator_sum_le_one F (fun R ↦ a ∈ R.2 ∧ b ∈ R.2) (by
    intro R hR S hS hRP hSP
    exact negative_pair_rigidity hv (hF R hR) (hF S hS) hab
      hRP.1 hRP.2 hSP.1 hSP.2)
  have hc (a b : J) : (∑ R ∈ F, if a ∈ R.1 ∧ b ∈ R.2 then (1 : ℝ) else 0)=
      crossHit F a b := by
    rw [indicator_sum_eq F _ (by
      intro R hR S hS hRP hSP
      exact cross_rigidity hv (hF R hR) (hF S hS) hRP.1 hSP.1 hRP.2 hSP.2)]
    simp [crossHit,cross]
  have he : gram F a b=
      (∑ R ∈ F,if a ∈ R.1 ∧ b ∈ R.1 then (1 : ℝ) else 0)+
      (∑ R ∈ F,if a ∈ R.2 ∧ b ∈ R.2 then (1 : ℝ) else 0)-
      (∑ R ∈ F,if a ∈ R.1 ∧ b ∈ R.2 then (1 : ℝ) else 0)-
      (∑ R ∈ F,if b ∈ R.1 ∧ a ∈ R.2 then (1 : ℝ) else 0) := by
    simp only [gram,← sum_add_distrib,← sum_sub_distrib]
    apply sum_congr rfl
    intro R hR
    by_cases haP : a ∈ R.1 <;> by_cases haQ : a ∈ R.2 <;>
      by_cases hbP : b ∈ R.1 <;> by_cases hbQ : b ∈ R.2 <;>
      simp [incidence,haP,haQ,hbP,hbQ]
  rw [hc a b,hc b a] at he
  dsimp only [missing]
  linarith

lemma missing_nonneg (F : Finset (Block J)) (a b : J) : 0 ≤ missing F a b := by
  simp only [missing,crossHit]
  split_ifs <;> norm_num

lemma incidence_sum {v : J → ℝ} {x : ℝ} {R : Block J}
    (hR : Valid v x R) {S : Finset J} (hS : R.1 ⊆ S ∧ R.2 ⊆ S) :
    (∑ a ∈ S,incidence R a) = -1 := by
  have h₁ : S.filter (fun a ↦ a ∈ R.1)=R.1 := filter_mem_eq_inter.trans (inter_eq_right.mpr hS.1)
  have h₂ : S.filter (fun a ↦ a ∈ R.2)=R.2 := filter_mem_eq_inter.trans (inter_eq_right.mpr hS.2)
  simp only [incidence,sum_sub_distrib,sum_boole,h₁,h₂,hR.1,hR.2.1]
  norm_num

lemma gram_diagonal {v : J → ℝ} {x : ℝ} {F : Finset (Block J)}
    (hF : ∀ R ∈ F, Valid v x R) (a : J) :
    gram F a a=posDegree F a+negDegree F a := by
  simp only [gram,posDegree,negDegree,← sum_add_distrib]
  apply sum_congr rfl
  intro R hR
  have hd := disjoint_left.mp (hF R hR).2.2.1
  dsimp [incidence]
  split_ifs <;> norm_num <;> tauto

lemma gram_row_sum {v : J → ℝ} {x : ℝ} {F : Finset (Block J)}
    (hF : ∀ R ∈ F, Valid v x R) {S : Finset J} (hS : Supported S F) (a : J) :
    (∑ b ∈ S,gram F a b)=negDegree F a-posDegree F a := by
  simp only [gram]
  rw [sum_comm]
  simp_rw [← mul_sum]
  have he : (∑ R ∈ F,incidence R a * (∑ b ∈ S,incidence R b))=
      ∑ R ∈ F,-incidence R a := by
    apply sum_congr rfl
    intro R hR
    rw [incidence_sum (hF R hR) (hS R hR)]
    ring
  rw [he]
  simp only [incidence,neg_sub,sum_sub_distrib,posDegree,negDegree]

lemma incidence_shift_sum {v : J → ℝ} {x : ℝ} {R : Block J}
    (hR : Valid v x R) {S : Finset J} (hS : R.1 ⊆ S ∧ R.2 ⊆ S) :
    (∑ a ∈ S,incidence R a*(v a+x))=0 := by
  simp only [incidence,sub_mul,ite_mul,one_mul,zero_mul,sum_sub_distrib,sum_ite_mem]
  rw [inter_eq_right.mpr hS.1,inter_eq_right.mpr hS.2,shifted_balance hR,sub_self]

lemma gram_mul_shift {v : J → ℝ} {x : ℝ} {F : Finset (Block J)}
    (hF : ∀ R ∈ F, Valid v x R) {S : Finset J} (hS : Supported S F) (a : J) :
    (∑ b ∈ S,gram F a b*(v b+x))=0 := by
  simp only [gram,sum_mul]
  rw [sum_comm]
  apply sum_eq_zero
  intro R hR
  simp_rw [mul_assoc,← mul_sum]
  rw [incidence_shift_sum (hF R hR) (hS R hR),mul_zero]

/-- A simple maximum-coordinate form of the strict diagonal dominance argument. -/
lemma row_abs_bound {S : Finset J} (M : J → J → ℝ) (b : J → ℝ) {a : J}
    (ha : a ∈ S) (hba : 0 < |b a|) (hmax : ∀ j ∈ S, |b j| ≤ |b a|)
    (hdiag : 0 ≤ M a a) (he : (∑ j ∈ S,M a j*b j)=0) :
    M a a ≤ ∑ j ∈ S.erase a, |M a j| := by
  have hs := sum_erase_add S (fun j ↦ M a j*b j) ha
  rw [he] at hs
  have habs : M a a * |b a| = |∑ j ∈ S.erase a,M a j*b j| := by
    have he' : M a a*b a=-(∑ j ∈ S.erase a,M a j*b j) := by linarith
    have hh := congrArg abs he'
    simpa [abs_mul,abs_of_nonneg hdiag] using hh
  have hh : M a a*|b a| ≤ (∑ j ∈ S.erase a,|M a j|)*|b a| := by
    rw [habs,sum_mul]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro j hj
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hmax j (mem_erase.mp hj).2) (abs_nonneg _)
  exact le_of_mul_le_mul_right hh hba

lemma local_margin {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) {a : J} (ha : a ∈ S)
    (hba : 0 < |v a+x|) (hmax : ∀ j ∈ S, |v j+x| ≤ |v a+x|) :
    negDegree F a-posDegree F a ≤ 2*missingDegree S F a := by
  have hd : 0 ≤ gram F a a := sum_nonneg (fun R _ ↦ mul_self_nonneg (incidence R a))
  have hrow := row_abs_bound (gram F) (fun j ↦ v j+x) ha hba hmax hd
    (gram_mul_shift hF hS a)
  have hm (j : J) (hj : j ∈ S.erase a) :
      |gram F a j| ≤ 2*missing F a j-gram F a j := by
    have hh := gram_offDiag_le hv hF (mem_erase.mp hj).1.symm
    have hn := missing_nonneg F a j
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  have hsum := sum_le_sum hm
  simp only [sum_sub_distrib,← mul_sum] at hsum
  have he := sum_erase_add S (gram F a) ha
  rw [gram_row_sum hF hS] at he
  dsimp only [missingDegree]
  linarith

lemma crossHit_eq_sum {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) (a b : J) :
    crossHit F a b=∑ R ∈ F, if a ∈ R.1 ∧ b ∈ R.2 then (1 : ℝ) else 0 := by
  symm
  rw [indicator_sum_eq F _ (by
    intro R hR S hS hRP hSP
    exact cross_rigidity hv (hF R hR) (hF S hS) hRP.1 hSP.1 hRP.2 hSP.2)]
  simp [crossHit,cross]

lemma crossHit_diagonal {v : J → ℝ} {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) (a : J) :
    crossHit F a a=0 := by
  apply if_neg
  intro h
  obtain ⟨R,hR,h⟩ := mem_biUnion.mp h
  exact disjoint_left.mp (hF R hR).2.2.1 (mem_product.mp h).1 (mem_product.mp h).2

lemma crossHit_sum_left {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) (a : J) :
    (∑ b ∈ S.erase a,crossHit F a b)=3*posDegree F a := by
  rw [sum_erase S (crossHit_diagonal hF a)]
  simp_rw [crossHit_eq_sum hv hF]
  rw [sum_comm]
  dsimp only [posDegree]
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  by_cases ha : a ∈ R.1
  · simp only [ha,true_and,ite_true,mul_one,sum_boole]
    have he : S.filter (fun b ↦ b ∈ R.2)=R.2 :=
      filter_mem_eq_inter.trans (inter_eq_right.mpr (hS R hR).2)
    rw [he,(hF R hR).2.1]
    norm_num
  · simp [ha]

lemma crossHit_sum_right {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) (a : J) :
    (∑ b ∈ S.erase a,crossHit F b a)=2*negDegree F a := by
  rw [sum_erase S (f := fun b ↦ crossHit F b a) (crossHit_diagonal hF a)]
  simp_rw [crossHit_eq_sum hv hF]
  rw [sum_comm]
  dsimp only [negDegree]
  rw [mul_sum]
  apply sum_congr rfl
  intro R hR
  by_cases ha : a ∈ R.2
  · simp only [ha,and_true,ite_true,mul_one,sum_boole]
    have he : S.filter (fun b ↦ b ∈ R.1)=R.1 :=
      filter_mem_eq_inter.trans (inter_eq_right.mpr (hS R hR).1)
    rw [he,(hF R hR).1]
    norm_num
  · simp [ha]

lemma erase_card_real {S : Finset J} {a : J} (ha : a ∈ S) :
    ((S.erase a).card : ℝ)=(S.card : ℝ)-1 := by
  have hh := card_erase_add_one ha
  have hh' : ((S.erase a).card : ℝ)+1=(S.card : ℝ) := by exact_mod_cast hh
  linarith

lemma missingDegree_eq {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) {a : J} (ha : a ∈ S) :
    missingDegree S F a=2*((S.card : ℝ)-1)-3*posDegree F a-2*negDegree F a := by
  simp only [missingDegree,missing,sum_add_distrib,sum_sub_distrib,sum_const,nsmul_eq_mul]
  rw [crossHit_sum_left hv hF hS,crossHit_sum_right hv hF hS,erase_card_real ha]
  ring

lemma positive_degree_le {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) {a : J} (ha : a ∈ S) :
    3*posDegree F a ≤ (S.card : ℝ)-1 := by
  rw [← crossHit_sum_left hv hF hS,← erase_card_real ha]
  calc
    (∑ b ∈ S.erase a,crossHit F a b) ≤ ∑ b ∈ S.erase a,(1 : ℝ) := by
      apply sum_le_sum
      intro b hb
      dsimp only [crossHit]
      split_ifs <;> norm_num
    _ = _ := by simp

lemma exists_missing_degree {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) (hn : 2 ≤ S.card) :
    ∃ a ∈ S, (S.card : ℝ)-1 ≤ 15*missingDegree S F a := by
  have hi : Function.Injective v := by
    intro a b hab
    have hm := hv a a a b b b (by rw [hab])
    have hmem : a ∈ ({b,b,b} : Multiset J) := hm ▸ (by simp)
    simpa using hmem
  have hex : ∃ a ∈ S,v a+x ≠ 0 := by
    by_contra hh
    push_neg at hh
    have hc : S.card ≤ 1 := card_le_one.mpr (by
      intro a ha b hb
      apply hi
      linarith [hh a ha,hh b hb])
    omega
  obtain ⟨b,hb,hbx⟩ := hex
  obtain ⟨a,ha,hmax⟩ := exists_max_image S (fun a ↦ |v a+x|) ⟨b,hb⟩
  have hba : 0 < |v a+x| := (abs_pos.mpr hbx).trans_le (hmax b hb)
  have hm := local_margin hv hF hS ha hba hmax
  have he := missingDegree_eq hv hF hS ha
  have hp := positive_degree_le hv hF hS ha
  exact ⟨a,ha,by linarith⟩

end FiveBlockGram


/- A fixed deficit in real five-block packings. Auxiliary to Erdős 241. -/
open Finset
namespace FiveBlockDeficit
open ProjectiveBinaryLiftObstruction FiveBlockPacking FiveBlockGram
open scoped Classical
variable {J : Type*} [DecidableEq J]

noncomputable def incident (F : Finset (Block J)) (a : J) : Finset (Block J) :=
  F.filter (fun R ↦ a ∈ R.1 ∨ a ∈ R.2)
noncomputable def cooccurring (F : Finset (Block J)) (a b : J) : Finset (Block J) :=
  (incident F a).filter (fun R ↦ b ∈ R.1 ∨ b ∈ R.2)
noncomputable def restrict (F : Finset (Block J)) (S : Finset J) : Finset (Block J) :=
  F.filter (fun R ↦ R.1 ⊆ S ∧ R.2 ⊆ S)

lemma cooccurring_card {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {a b : J} (hab : a ≠ b) : (cooccurring F a b).card ≤ 4 := by
  have hp := indicator_sum_le_one F (fun R ↦ a ∈ R.1 ∧ b ∈ R.1) (by
    intro R hR S hS hRP hSP
    apply positive_pair_rigidity hv (hF R hR) (hF S hS)
    rw [pair_of_two_members (hF R hR).1 hab hRP.1 hRP.2,
      pair_of_two_members (hF S hS).1 hab hSP.1 hSP.2])
  have hn := indicator_sum_le_one F (fun R ↦ a ∈ R.2 ∧ b ∈ R.2) (by
    intro R hR S hS hRP hSP
    exact negative_pair_rigidity hv (hF R hR) (hF S hS) hab
      hRP.1 hRP.2 hSP.1 hSP.2)
  have hc (a b : J) := indicator_sum_le_one F (fun R ↦ a ∈ R.1 ∧ b ∈ R.2) (by
    intro R hR S hS hRP hSP
    exact cross_rigidity hv (hF R hR) (hF S hS) hRP.1 hSP.1 hRP.2 hSP.2)
  have he : ((cooccurring F a b).card : ℝ)=
      ∑ R ∈ F,if (a ∈ R.1 ∨ a ∈ R.2) ∧ (b ∈ R.1 ∨ b ∈ R.2) then (1 : ℝ) else 0 := by
    simp [cooccurring,incident,filter_filter,sum_boole]
  have hh : ((cooccurring F a b).card : ℝ) ≤
      (∑ R ∈ F,if a ∈ R.1 ∧ b ∈ R.1 then (1 : ℝ) else 0)+
      (∑ R ∈ F,if a ∈ R.2 ∧ b ∈ R.2 then (1 : ℝ) else 0)+
      (∑ R ∈ F,if a ∈ R.1 ∧ b ∈ R.2 then (1 : ℝ) else 0)+
      (∑ R ∈ F,if b ∈ R.1 ∧ a ∈ R.2 then (1 : ℝ) else 0) := by
    rw [he]
    simp only [← sum_add_distrib]
    apply sum_le_sum
    intro R hR
    by_cases haP : a ∈ R.1 <;> by_cases haQ : a ∈ R.2 <;>
      by_cases hbP : b ∈ R.1 <;> by_cases hbQ : b ∈ R.2 <;>
      norm_num [haP,haQ,hbP,hbQ]
  have hh' : ((cooccurring F a b).card : ℝ) ≤ 4 := by linarith [hc a b,hc b a]
  exact_mod_cast hh'

lemma restrict_subset (F : Finset (Block J)) (S : Finset J) : restrict F S ⊆ F := filter_subset _ _
lemma restrict_supported (F : Finset (Block J)) (S : Finset J) : Supported S (restrict F S) := by
  intro R hR
  exact (mem_filter.mp hR).2

lemma lost_incident_card {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S B : Finset J} (hS : Supported S F) {a : J} (ha : a ∈ S \ B) :
    (incident (F \ restrict F (S \ B)) a).card ≤ 4*B.card := by
  have hcover : incident (F \ restrict F (S \ B)) a ⊆
      B.biUnion (fun b ↦ cooccurring F a b) := by
    intro R hR
    obtain ⟨hRF,hai⟩ := mem_filter.mp hR
    obtain ⟨hRF,hRn⟩ := mem_sdiff.mp hRF
    have hex : ∃ b ∈ B, b ∈ R.1 ∨ b ∈ R.2 := by
      by_contra hh
      apply hRn
      apply mem_filter.mpr
      refine ⟨hRF,?_,?_⟩
      · intro b hb
        exact mem_sdiff.mpr ⟨(hS R hRF).1 hb,fun h ↦ hh ⟨b,h,Or.inl hb⟩⟩
      · intro b hb
        exact mem_sdiff.mpr ⟨(hS R hRF).2 hb,fun h ↦ hh ⟨b,h,Or.inr hb⟩⟩
    obtain ⟨b,hb,hbi⟩ := hex
    apply mem_biUnion.mpr
    exact ⟨b,hb,mem_filter.mpr ⟨mem_filter.mpr ⟨hRF,hai⟩,hbi⟩⟩
  have hh := (card_le_card hcover).trans card_biUnion_le
  calc
    _ ≤ ∑ b ∈ B,(cooccurring F a b).card := hh
    _ ≤ ∑ b ∈ B,4 := by
      apply sum_le_sum
      intro b hb
      apply cooccurring_card hv hF
      intro he
      exact (mem_sdiff.mp ha).2 (he.symm ▸ hb)
    _ = _ := by simp [mul_comm]

lemma weighted_degree_loss {v : J → ℝ} {x : ℝ}
    {F T : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R) (hT : T ⊆ F) (a : J) :
    3*posDegree F a+2*negDegree F a ≤
      3*posDegree T a+2*negDegree T a+3*(incident (F \ T) a).card := by
  have hp : posDegree (F \ T) a+posDegree T a=posDegree F a := sum_sdiff hT
  have hn : negDegree (F \ T) a+negDegree T a=negDegree F a := sum_sdiff hT
  have hh : 3*posDegree (F \ T) a+2*negDegree (F \ T) a ≤
      3*(incident (F \ T) a).card := by
    dsimp only [posDegree,negDegree,incident]
    rw [← sum_boole, mul_sum, mul_sum, mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro R hR
    have hd := disjoint_left.mp (hF R (mem_sdiff.mp hR).1).2.2.1
    by_cases haP : a ∈ R.1 <;> by_cases haQ : a ∈ R.2 <;>
      norm_num [haP,haQ] <;> exact (hd haP haQ).elim
  linarith

lemma missingDegree_restrict_le {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S B : Finset J} (hS : Supported S F) {a : J} (ha : a ∈ S \ B) :
    missingDegree (S \ B) (restrict F (S \ B)) a ≤
      missingDegree S F a+12*B.card := by
  have hT : ∀ R ∈ restrict F (S \ B),Valid v x R := fun R hR ↦ hF R (restrict_subset _ _ hR)
  rw [missingDegree_eq hv hT (restrict_supported _ _) ha,
    missingDegree_eq hv hF hS (mem_sdiff.mp ha).1]
  have hcard : ((S \ B).card : ℝ) ≤ S.card := by exact_mod_cast card_le_card (sdiff_subset : S \ B ⊆ S)
  have hinc : ((incident (F \ restrict F (S \ B)) a).card : ℝ) ≤ 4*B.card := by
    exact_mod_cast lost_incident_card hv hF hS ha
  have hw := weighted_degree_loss hF (restrict_subset F (S \ B)) a
  linarith

lemma sum_degrees {v : J → ℝ} {x : ℝ} {F : Finset (Block J)}
    (hF : ∀ R ∈ F, Valid v x R) {S : Finset J} (hS : Supported S F) :
    (∑ a ∈ S,posDegree F a)=2*F.card ∧ (∑ a ∈ S,negDegree F a)=3*F.card := by
  constructor
  · dsimp only [posDegree]
    rw [sum_comm]
    have he : (∑ R ∈ F,∑ a ∈ S,if a ∈ R.1 then (1 : ℝ) else 0)=∑ R ∈ F,2 := by
      apply sum_congr rfl
      intro R hR
      rw [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (hS R hR).1,(hF R hR).1]
      norm_num
    rw [he]
    simp [mul_comm]
  · dsimp only [negDegree]
    rw [sum_comm]
    have he : (∑ R ∈ F,∑ a ∈ S,if a ∈ R.2 then (1 : ℝ) else 0)=∑ R ∈ F,3 := by
      apply sum_congr rfl
      intro R hR
      rw [sum_boole,filter_mem_eq_inter,inter_eq_right.mpr (hS R hR).2,(hF R hR).2.1]
      norm_num
    rw [he]
    simp [mul_comm]

lemma sum_missingDegree {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) :
    (∑ a ∈ S,missingDegree S F a)=2*((S.card : ℝ)*(S.card-1)-6*F.card) := by
  have he := sum_congr rfl (fun a ha ↦ missingDegree_eq hv hF hS ha)
  rw [he]
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul,← mul_sum]
  rw [(sum_degrees hF hS).1,(sum_degrees hF hS).2]
  ring

lemma missingDegree_nonneg (S : Finset J) (F : Finset (Block J)) (a : J) :
    0 ≤ missingDegree S F a := sum_nonneg (fun b _ ↦ missing_nonneg F a b)

/-- A deliberately conservative fixed deficit. This concerns only the five-distinct-label
blocks, not all ordered five-term representations, and does not settle Erdős 241. -/
lemma fixed_deficit {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) (hn : 2 ≤ S.card) :
    (S.card : ℝ)^2 ≤ 1000000*((S.card : ℝ)*(S.card-1)-6*F.card) := by
  by_contra hbad
  have hd : 1000000*((S.card : ℝ)*(S.card-1)-6*F.card)<(S.card : ℝ)^2 := lt_of_not_ge hbad
  let B := S.filter (fun a ↦ (S.card : ℝ)/100 ≤ missingDegree S F a)
  have hBS : B ⊆ S := filter_subset _ _
  have hBbound : (B.card : ℝ)*((S.card : ℝ)/100) ≤
      2*((S.card : ℝ)*(S.card-1)-6*F.card) := by
    calc
      _ = ∑ a ∈ B,(S.card : ℝ)/100 := by simp
      _ ≤ ∑ a ∈ B,missingDegree S F a := sum_le_sum (fun a ha ↦ (mem_filter.mp ha).2)
      _ ≤ ∑ a ∈ S,missingDegree S F a := sum_le_sum_of_subset_of_nonneg hBS
        (fun a _ _ ↦ missingDegree_nonneg S F a)
      _ = _ := sum_missingDegree hv hF hS
  have hn' : (2 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < S.card := by linarith
  have hBsmall : (B.card : ℝ)<(S.card : ℝ)/5000 := by
    have hh : (B.card : ℝ)*(S.card : ℝ)<(S.card : ℝ)^2/5000 := by nlinarith
    have hh' : (B.card : ℝ)*(S.card : ℝ)<((S.card : ℝ)/5000)*(S.card : ℝ) := by nlinarith
    exact lt_of_mul_lt_mul_right hh' hnpos.le
  have hUcard : ((S \ B).card : ℝ)=(S.card : ℝ)-B.card := by
    have hh := card_sdiff_add_card_eq_card hBS
    have hh' : ((S \ B).card : ℝ)+B.card=S.card := by exact_mod_cast hh
    linarith
  have hUn : 2 ≤ (S \ B).card := by
    have hh : (1 : ℝ)<(S \ B).card := by rw [hUcard]; linarith
    have hh' : 1 < (S \ B).card := by exact_mod_cast hh
    omega
  have hT : ∀ R ∈ restrict F (S \ B),Valid v x R := fun R hR ↦ hF R (restrict_subset _ _ hR)
  obtain ⟨a,ha,hlow⟩ := exists_missing_degree hv hT (restrict_supported _ _) hUn
  have ha' : missingDegree S F a < (S.card : ℝ)/100 := by
    have hna := (mem_sdiff.mp ha).2
    have has := (mem_sdiff.mp ha).1
    exact lt_of_not_ge (fun h ↦ hna (mem_filter.mpr ⟨has,h⟩))
  have hupp := missingDegree_restrict_le hv hF hS ha
  rw [hUcard] at hlow
  linarith

end FiveBlockDeficit


/- Application of the real five-block deficit to the B₃ predicate used by
Erdős 241. This does not settle that conjecture. -/
open Finset
namespace FiveBlockNatural
open ProjectiveBinaryLiftObstruction FiveBlockPacking FiveBlockDeficit
open scoped Classical

lemma goodTriple_real {A : Finset ℕ} (hA : B3Aux.Good A) :
    GoodTriple (fun a : A ↦ (a.val : ℝ)) := by
  intro a b c d e f he
  dsimp only at he
  have he' : a.val+b.val+c.val=d.val+e.val+f.val := by exact_mod_cast he
  have hh := hA ({a.val,b.val,c.val}) ({d.val,e.val,f.val}) (by simp) (by simp)
    (by simp [a.property,b.property,c.property])
    (by simp [d.property,e.property,f.property]) (by simpa [add_assoc] using he')
  apply Multiset.map_injective (f := (fun a : A ↦ (a : ℕ))) Subtype.val_injective
  simpa using hh

/-- Unordered representations with five distinct labels. -/
noncomputable def blocks (A : Finset ℕ) (x : ℝ) : Finset (Block A) :=
  univ.filter (Valid (fun a : A ↦ (a.val : ℝ)) x)

lemma fixed_deficit {A : Finset ℕ} (hA : B3Aux.Good A) (x : ℝ)
    (hn : 2 ≤ A.card) :
    (A.card : ℝ)^2 ≤ 1000000*((A.card : ℝ)*(A.card-1)-6*(blocks A x).card) := by
  have hh := FiveBlockDeficit.fixed_deficit (goodTriple_real hA)
    (F := blocks A x) (S := univ) (fun R hR ↦ (mem_filter.mp hR).2)
    (fun R _ ↦ ⟨subset_univ _,subset_univ _⟩) (by simpa using hn)
  simpa only [card_univ,Fintype.card_coe] using hh

lemma block_count_bound {A : Finset ℕ} (hA : B3Aux.Good A) (x : ℝ)
    (hn : 2 ≤ A.card) :
    ((blocks A x).card : ℝ) ≤ (999999 : ℝ)/6000000*(A.card : ℝ)^2-(A.card : ℝ)/6 := by
  have hh := fixed_deficit hA x hn
  nlinarith

end FiveBlockNatural


/- Removing repetitions and cancellations from the fixed five-block deficit.
Auxiliary to Erdős 241, not a settlement. -/
open Finset
namespace OrderedFiveDeficit
open B3Aux CoupledShifts FiveBlockNatural FiveBlockPacking
open scoped Classical

private def CrossDistinct {A : Finset ℕ} (p : Five A) : Prop :=
  p.1.1 ≠ p.2.1 ∧ p.1.1 ≠ p.2.2.1 ∧ p.1.1 ≠ p.2.2.2 ∧
  p.1.2 ≠ p.2.1 ∧ p.1.2 ≠ p.2.2.1 ∧ p.1.2 ≠ p.2.2.2
private def WithinDistinct {A : Finset ℕ} (p : Five A) : Prop :=
  p.1.1 ≠ p.1.2 ∧ p.2.1 ≠ p.2.2.1 ∧ p.2.1 ≠ p.2.2.2 ∧ p.2.2.1 ≠ p.2.2.2

noncomputable def reduced (A : Finset ℕ) (x : ℤ) : Finset (Five A) :=
  (fives A x).filter CrossDistinct
noncomputable def distinct (A : Finset ℕ) (x : ℤ) : Finset (Five A) :=
  (reduced A x).filter WithinDistinct
noncomputable def blockOf {A : Finset ℕ} (p : Five A) : Block A :=
  ({p.1.1,p.1.2},{p.2.1,p.2.2.1,p.2.2.2})

lemma distinct_block_valid {A : Finset ℕ} {x : ℤ} {p : Five A}
    (hp : p ∈ distinct A x) : blockOf p ∈ blocks A (x : ℝ) := by
  obtain ⟨hp,hwithin⟩ := mem_filter.mp hp
  obtain ⟨hp,hcross⟩ := mem_filter.mp hp
  obtain ⟨hac,had,hae,hbc,hbd,hbe⟩ := hcross
  obtain ⟨hab,hcd,hce,hde⟩ := hwithin
  apply mem_filter.mpr
  refine ⟨mem_univ _,?_,?_,?_,?_⟩
  · simp [blockOf,hab]
  · simp [blockOf,hcd,hce,hde]
  · simp [blockOf,Finset.disjoint_left,hac,had,hae,hbc,hbd,hbe]
  · have he := (mem_filter.mp hp).2
    have he' : (p.1.1.val : ℝ)+p.1.2.val-p.2.1.val-p.2.2.1.val-p.2.2.2.val=(x : ℝ) := by
      exact_mod_cast he
    dsimp only [blockOf]
    simp [hab,hcd,hce,hde]
    linarith

lemma distinct_fiber_card {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (R : Block A) (hR : R ∈ blocks A (x : ℝ)) :
    ((distinct A x).filter (fun p ↦ blockOf p=R)).card ≤ 12 := by
  let T := R.1 ×ˢ R.2.offDiag
  have hcard : T.card=12 := by
    have hvalid := (mem_filter.mp hR).2
    rw [card_product,offDiag_card,hvalid.1,hvalid.2.1]
  rw [← hcard]
  apply card_le_card_of_injOn (fun p : Five A ↦ (p.1.1,p.2.1,p.2.2.1))
  · intro p hp
    obtain ⟨hp,hpR⟩ := mem_filter.mp hp
    have hwd := (mem_filter.mp hp).2
    change (p.1.1,p.2.1,p.2.2.1) ∈ R.1 ×ˢ R.2.offDiag
    rw [← hpR]
    exact mem_product.mpr ⟨by simp [blockOf],mem_offDiag.mpr
      ⟨by simp [blockOf],by simp [blockOf],hwd.2.1⟩⟩
  · rintro ⟨⟨a,b⟩,c,d,e⟩ hp ⟨⟨a',b'⟩,c',d',e'⟩ hq he
    have haa := congrArg Prod.fst he
    have hcc := congrArg (Prod.fst ∘ Prod.snd) he
    have hdd := congrArg (Prod.snd ∘ Prod.snd) he
    dsimp only [Function.comp_apply] at haa hcc hdd
    subst a'; subst c'; subst d'
    have hp' := (mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).1).2
    have hq' := (mem_filter.mp (mem_filter.mp (mem_filter.mp (mem_filter.mp hq).1).1).1).2
    have hc := (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
    have hbe : b.val ≠ e.val := fun h ↦ hc.2.2.2.2.2 (Subtype.ext h)
    obtain ⟨hbb,hee⟩ := DifferenceGraph.difference_inj hA b.property e.property
      b'.property e'.property hbe (by dsimp only at hp' hq'; omega)
    exact Prod.ext (Prod.ext rfl (Subtype.ext hbb))
      (Prod.ext rfl (Prod.ext rfl (Subtype.ext hee)))

lemma distinct_card {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (distinct A x).card ≤ 12*(blocks A (x : ℝ)).card := by
  exact card_le_mul_card_image_of_maps_to (f := @blockOf A)
    (fun _ hp ↦ distinct_block_valid hp) 12 (distinct_fiber_card hA x)

private def cancelCode {A : Finset ℕ} (i : Fin 6) (p : A × (A × A × A)) : Five A :=
  ![((p.1,p.2.1),(p.1,p.2.2.1,p.2.2.2)),
    ((p.1,p.2.1),(p.2.2.1,p.1,p.2.2.2)),
    ((p.1,p.2.1),(p.2.2.1,p.2.2.2,p.1)),
    ((p.2.1,p.1),(p.1,p.2.2.1,p.2.2.2)),
    ((p.2.1,p.1),(p.2.2.1,p.1,p.2.2.2)),
    ((p.2.1,p.1),(p.2.2.1,p.2.2.2,p.1))] i

lemma cancelled_card {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A,x ≠ -(a : ℤ)) :
    ((fives A x).filter (fun p ↦ ¬CrossDistinct p)).card ≤ 12*A.card := by
  let T := (univ : Finset A) ×ˢ triples A x
  have hcover : (fives A x).filter (fun p ↦ ¬CrossDistinct p) ⊆
      (univ : Finset (Fin 6)).biUnion (fun i ↦ T.image (cancelCode i)) := by
    rintro ⟨⟨a,b⟩,c,d,e⟩ hp
    obtain ⟨hp,hn⟩ := mem_filter.mp hp
    have hs := (mem_filter.mp hp).2
    dsimp only [CrossDistinct] at hn
    push_neg at hn
    have insertIt (i : Fin 6) (z u v w : A)
        (htri : (u.val : ℤ)-v.val-w.val=x)
        (he : cancelCode i (z,u,v,w)=((a,b),c,d,e)) :
        ((a,b),c,d,e) ∈ (univ : Finset (Fin 6)).biUnion (fun i ↦ T.image (cancelCode i)) := by
      apply mem_biUnion.mpr
      refine ⟨i,mem_univ _,mem_image.mpr ⟨(z,u,v,w),?_,he⟩⟩
      exact mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨mem_univ _,htri⟩⟩
    by_cases hac : a=c
    · subst c
      exact insertIt 0 a b d e (by dsimp only at hs; omega) rfl
    by_cases had : a=d
    · subst d
      exact insertIt 1 a b c e (by dsimp only at hs; omega) rfl
    by_cases hae : a=e
    · subst e
      exact insertIt 2 a b c d (by dsimp only at hs; omega) rfl
    by_cases hbc : b=c
    · subst c
      exact insertIt 3 b a d e (by dsimp only at hs; omega) rfl
    by_cases hbd : b=d
    · subst d
      exact insertIt 4 b a c e (by dsimp only at hs; omega) rfl
    have hbe := hn hac had hae hbc hbd
    subst e
    exact insertIt 5 b a c d (by dsimp only at hs; omega) rfl
  have hh := (card_le_card hcover).trans card_biUnion_le
  have hb : (∑ i : Fin 6,(T.image (cancelCode i)).card) ≤ ∑ _i : Fin 6,T.card :=
    sum_le_sum (fun _ _ ↦ card_image_le)
  have ht : T.card=A.card*(triples A x).card := by simp [T]
  have htr := triples_card_le_two hA x hx
  simp only [sum_const,card_univ,Fintype.card_fin,smul_eq_mul] at hb
  rw [ht] at hb
  nlinarith

private noncomputable def positiveRepeat (A : Finset ℕ) (x : ℤ) : Finset (Five A) :=
  (fives A x).filter (fun p ↦ p.1.1=p.1.2)
private noncomputable def negativeRepeat (A : Finset ℕ) (x : ℤ) : Finset (Five A) :=
  (reduced A x).filter (fun p ↦ p.2.1=p.2.2.1)

lemma positive_repeat_fiber {A : Finset ℕ} (hA : Good A) (x : ℤ) (u : A) :
    ((positiveRepeat A x).filter (fun p ↦ p.1.1=u)).card ≤ 27 := by
  let F := (positiveRepeat A x).filter (fun p ↦ p.1.1=u)
  by_cases hF : F.Nonempty
  swap
  · have he : F=∅ := not_nonempty_iff_eq_empty.mp hF
    change F.card ≤ 27
    rw [he]
    simp
  obtain ⟨p₀,hp₀⟩ := hF
  let T : Finset A := {p₀.2.1,p₀.2.2.1,p₀.2.2.2}
  have hfix (p : Five A) (hp : p ∈ F) : p.1=(u,u) := by
    obtain ⟨hp,hu⟩ := mem_filter.mp hp
    have he := (mem_filter.mp hp).2
    exact Prod.ext hu (he.symm.trans hu)
  have hsum (p : Five A) (hp : p ∈ F) :
      ({p.2.1,p.2.2.1,p.2.2.2} : Multiset A)={p₀.2.1,p₀.2.2.1,p₀.2.2.2} := by
    have hp' := (mem_filter.mp (mem_filter.mp (mem_filter.mp hp).1).1).2
    have h₀' := (mem_filter.mp (mem_filter.mp (mem_filter.mp hp₀).1).1).2
    rw [hfix p hp] at hp'
    rw [hfix p₀ hp₀] at h₀'
    apply goodTriple_real hA
    dsimp only
    have hh : p.2.1.val+p.2.2.1.val+p.2.2.2.val=
        p₀.2.1.val+p₀.2.2.1.val+p₀.2.2.2.val := by omega
    exact_mod_cast hh
  have hh : F.card ≤ (T ×ˢ (T ×ˢ T)).card := by
    apply card_le_card_of_injOn (fun p : Five A ↦ p.2)
    · intro p hp
      have hm (a : A) (ha : a ∈ ({p.2.1,p.2.2.1,p.2.2.2} : Multiset A)) : a ∈ T := by
        have ha' := hsum p hp ▸ ha
        simpa [T] using ha'
      exact mem_product.mpr ⟨hm _ (by simp),mem_product.mpr ⟨hm _ (by simp),hm _ (by simp)⟩⟩
    · intro p hp q hq he
      exact Prod.ext ((hfix p hp).trans (hfix q hq).symm) he
  have hc : T.card ≤ 3 := card_le_three
  have hbound : (T ×ˢ (T ×ˢ T)).card ≤ 27 := by
    simp only [card_product]
    calc T.card*(T.card*T.card) ≤ 3*(3*3) := Nat.mul_le_mul hc (Nat.mul_le_mul hc hc)
         _ = 27 := rfl
  exact hh.trans hbound

lemma positive_repeat_card {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (positiveRepeat A x).card ≤ 27*A.card := by
  have hh := card_le_mul_card_image_of_maps_to (s := positiveRepeat A x)
    (t := (univ : Finset A)) (f := fun p ↦ p.1.1) (fun _ _ ↦ mem_univ _) 27
    (fun u _ ↦ positive_repeat_fiber hA x u)
  simpa using hh

lemma negative_repeat_fiber {A : Finset ℕ} (hA : Good A) (x : ℤ) (u : A) :
    ((negativeRepeat A x).filter (fun p ↦ p.2.1=u)).card ≤ 2 := by
  have hh : ((negativeRepeat A x).filter (fun p ↦ p.2.1=u)).card ≤ (univ : Finset Bool).card := by
    apply card_le_card_of_injOn (fun p : Five A ↦ decide (p.1.1.val ≤ p.1.2.val))
      (fun _ _ ↦ mem_univ _)
    rintro ⟨⟨a,b⟩,c,d,e⟩ hp ⟨⟨a',b'⟩,c',d',e'⟩ hq he
    obtain ⟨hp,hcu⟩ := mem_filter.mp hp
    obtain ⟨hq,hc'u⟩ := mem_filter.mp hq
    obtain ⟨hp,hcd⟩ := mem_filter.mp hp
    obtain ⟨hq,hc'd'⟩ := mem_filter.mp hq
    dsimp only at hcu hc'u hcd hc'd'
    subst c; subst c'; subst d; subst d'
    obtain ⟨hp,hcross⟩ := mem_filter.mp hp
    obtain ⟨hq,hcross'⟩ := mem_filter.mp hq
    have hp' := (mem_filter.mp hp).2
    have hq' := (mem_filter.mp hq).2
    have hea : e.val ≠ a.val := fun h ↦ hcross.2.2.1 (Subtype.ext h.symm)
    have heb : e.val ≠ b.val := fun h ↦ hcross.2.2.2.2.2 (Subtype.ext h.symm)
    obtain ⟨hee,hpair⟩ := signed_triple_unique hA e.property a.property b.property
      e'.property a'.property b'.property hea heb (by dsimp only at hp' hq'; omega)
    have hord : (a.val ≤ b.val) ↔ (a'.val ≤ b'.val) := by simpa using he
    have haa : a.val=a'.val := by rcases hpair with h | h <;> omega
    have hbb : b.val=b'.val := by rcases hpair with h | h <;> omega
    exact Prod.ext (Prod.ext (Subtype.ext haa) (Subtype.ext hbb))
      (Prod.ext rfl (Prod.ext rfl (Subtype.ext hee)))
  simpa using hh

lemma negative_repeat_card {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (negativeRepeat A x).card ≤ 2*A.card := by
  have hh := card_le_mul_card_image_of_maps_to (s := negativeRepeat A x)
    (t := (univ : Finset A)) (f := fun p ↦ p.2.1) (fun _ _ ↦ mem_univ _) 2
    (fun u _ ↦ negative_repeat_fiber hA x u)
  simpa using hh

private def negativeRepeatCode {A : Finset ℕ} (i : Fin 3) (p : Five A) : Five A :=
  ![p,(p.1,p.2.1,p.2.2.2,p.2.2.1),(p.1,p.2.2.2,p.2.1,p.2.2.1)] i

lemma reduced_card {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    (reduced A x).card ≤ (distinct A x).card+33*A.card := by
  let T := (univ : Finset (Fin 3)).biUnion (fun i ↦ (negativeRepeat A x).image (negativeRepeatCode i))
  have hcover : reduced A x ⊆ distinct A x ∪ positiveRepeat A x ∪ T := by
    rintro ⟨⟨a,b⟩,c,d,e⟩ hp
    have hp' := (mem_filter.mp hp).1
    have hc := (mem_filter.mp hp).2
    have hs := (mem_filter.mp hp').2
    by_cases hab : a=b
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hp',hab⟩))
    by_cases hcd : c=d
    · apply mem_union_right
      apply mem_biUnion.mpr
      exact ⟨0,mem_univ _,mem_image.mpr ⟨((a,b),c,d,e),mem_filter.mpr ⟨hp,hcd⟩,rfl⟩⟩
    by_cases hce : c=e
    · subst e
      have hq : ((a,b),c,c,d) ∈ negativeRepeat A x := by
        apply mem_filter.mpr
        refine ⟨mem_filter.mpr ⟨?_,?_⟩,rfl⟩
        · exact mem_filter.mpr ⟨mem_univ _,by dsimp only at hs ⊢; omega⟩
        · dsimp only [CrossDistinct] at hc ⊢
          tauto
      apply mem_union_right
      apply mem_biUnion.mpr
      exact ⟨1,mem_univ _,mem_image.mpr ⟨((a,b),c,c,d),hq,rfl⟩⟩
    by_cases hde : d=e
    · subst e
      have hq : ((a,b),d,d,c) ∈ negativeRepeat A x := by
        apply mem_filter.mpr
        refine ⟨mem_filter.mpr ⟨?_,?_⟩,rfl⟩
        · exact mem_filter.mpr ⟨mem_univ _,by dsimp only at hs ⊢; omega⟩
        · dsimp only [CrossDistinct] at hc ⊢
          tauto
      apply mem_union_right
      apply mem_biUnion.mpr
      exact ⟨2,mem_univ _,mem_image.mpr ⟨((a,b),d,d,c),hq,rfl⟩⟩
    exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hp,hab,hcd,hce,hde⟩))
  have hT : T.card ≤ 3*(negativeRepeat A x).card := by
    apply card_biUnion_le.trans
    calc
      (∑ i : Fin 3,((negativeRepeat A x).image (negativeRepeatCode i)).card) ≤
          ∑ _i : Fin 3,(negativeRepeat A x).card := sum_le_sum (fun _ _ ↦ card_image_le)
      _ = _ := by simp
  have hh := (card_le_card hcover).trans (card_union_le _ _)
  have hh' := card_union_le (distinct A x) (positiveRepeat A x)
  have hp := positive_repeat_card hA x
  have hn := negative_repeat_card hA x
  omega

lemma fives_le_blocks {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A,x ≠ -(a : ℤ)) :
    (fives A x).card ≤ 12*(blocks A (x : ℝ)).card+45*A.card := by
  have he := card_filter_add_card_filter_not (s := fives A x) CrossDistinct
  have hc := cancelled_card hA x hx
  have hr := reduced_card hA x
  have hd := distinct_card hA x
  change (reduced A x).card+((fives A x).filter (fun p ↦ ¬CrossDistinct p)).card=(fives A x).card at he
  omega

/-- A universal improved leading coefficient for the FULL ordered five-term count,
including repeated entries, away from the unavoidable exceptional core -A. -/
lemma fives_card_fixed_deficit {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A,x ≠ -(a : ℤ)) :
    500000*(fives A x).card ≤ 999999*A.card^2+22500000*A.card := by
  by_cases hn : 2 ≤ A.card
  · have hb := FiveBlockNatural.block_count_bound hA (x : ℝ) hn
    have hf : ((fives A x).card : ℝ) ≤ 12*(blocks A (x : ℝ)).card+45*A.card := by
      exact_mod_cast fives_le_blocks hA x hx
    have hh : (500000 : ℝ)*(fives A x).card ≤ 999999*(A.card : ℝ)^2+22500000*A.card := by
      nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
    exact_mod_cast hh
  · have hf := fives_card_uniform hA x
    have hn' : A.card=0 ∨ A.card=1 := by omega
    rcases hn' with hc | hc <;> rw [hc] at hf ⊢ <;> norm_num at hf ⊢ <;> omega

lemma fives_fixed_with_core {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    500000*(fives A x).card ≤ 999999*A.card^2+22500000*A.card+
      if x ∈ negativeCore A then 3000000*A.card^2 else 0 := by
  by_cases hx : x ∈ negativeCore A
  · rw [if_pos hx]
    have hh := fives_card_uniform hA x
    omega
  · rw [if_neg hx,add_zero]
    apply fives_card_fixed_deficit hA x
    intro a ha he
    exact hx (mem_image.mpr ⟨a,ha,he.symm⟩)

lemma sum_fives_fixed_deficit {A : Finset ℕ} (hA : Good A) (S : Finset ℤ) :
    500000*(∑ x ∈ S,(fives A x).card) ≤
      (999999*A.card^2+22500000*A.card)*S.card+
        3000000*A.card^2*(S ∩ negativeCore A).card := by
  have hh := sum_le_sum (s := S) (fun x _ ↦ fives_fixed_with_core hA x)
  have he : (∑ x ∈ S,if x ∈ negativeCore A then 3000000*A.card^2 else 0)=
      3000000*A.card^2*(S ∩ negativeCore A).card := by
    rw [← sum_filter]
    have hS : S.filter (fun x ↦ x ∈ negativeCore A)=S ∩ negativeCore A := by ext; simp
    rw [hS]
    simp [mul_comm]
  rw [sum_add_distrib,he,← mul_sum] at hh
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm] using hh

lemma nonzero_exceptional_card {A : Finset ℕ} (hA : Good A) {δ : ℤ} (hδ : δ ≠ 0) :
    (A.filter (fun a : ℕ ↦ δ-(a : ℤ) ∈ negativeCore A)).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha c hc
  obtain ⟨ha,ha'⟩ := mem_filter.mp ha
  obtain ⟨hc,hc'⟩ := mem_filter.mp hc
  obtain ⟨b,hb,heb⟩ := mem_image.mp ha'
  obtain ⟨d,hd,hed⟩ := mem_image.mp hc'
  have hab : a ≠ b := by intro h; exact hδ (by omega)
  exact (DifferenceGraph.difference_inj hA ha hb hc hd hab (by omega)).1

/-- The sum on the left counts ordered six-tuples with three positive and three
negative summands at a NONZERO shift. The zero shift has a different main term. -/
lemma nonzero_sixfold_bound {A : Finset ℕ} (hA : Good A) {δ : ℤ} (hδ : δ ≠ 0) :
    500000*(∑ a ∈ A,(fives A (δ-(a : ℤ))).card) ≤
      999999*A.card^3+25500000*A.card^2 := by
  let E := A.filter (fun a : ℕ ↦ δ-(a : ℤ) ∈ negativeCore A)
  have hE : E.card ≤ 1 := nonzero_exceptional_card hA hδ
  have hh := sum_le_sum (s := A) (fun a _ ↦ fives_fixed_with_core hA (δ-(a : ℤ)))
  have he : (∑ a ∈ A,if δ-(a : ℤ) ∈ negativeCore A then 3000000*A.card^2 else 0)=
      3000000*A.card^2*E.card := by
    rw [← sum_filter]
    simp only [E,sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm]
  rw [sum_add_distrib,he,← mul_sum] at hh
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at hh
  have hsmall := Nat.mul_le_mul_left (3000000*A.card^2) hE
  nlinarith only [hh,hsmall]

end OrderedFiveDeficit

/- A sharper quantitative consequence of the existing five-block Gram
obstruction. This improves unrestricted auxiliary counting constants but
is not a proof of the sharp asymptotic conjecture. -/
open Finset
namespace RefinedFiveDeficit
open ProjectiveBinaryLiftObstruction FiveBlockPacking FiveBlockGram FiveBlockDeficit
open B3Aux CoupledShifts FiveBlockNatural
open scoped Classical

lemma block_deficit {J : Type*} [DecidableEq J]
    {v : J → ℝ} (hv : GoodTriple v) {x : ℝ}
    {F : Finset (Block J)} (hF : ∀ R ∈ F, Valid v x R)
    {S : Finset J} (hS : Supported S F) (hn : 2 ≤ S.card) :
    ((S.card : ℝ)-1)^2 ≤ 21720*((S.card : ℝ)*(S.card-1)-6*F.card) := by
  by_contra hbad
  have hd := lt_of_not_ge hbad
  let B := S.filter (fun a ↦ ((S.card : ℝ)-1)/30 ≤ missingDegree S F a)
  have hBS : B ⊆ S := filter_subset _ _
  have hBbound : (B.card : ℝ)*(((S.card : ℝ)-1)/30) ≤
      2*((S.card : ℝ)*(S.card-1)-6*F.card) := by
    calc
      _ = ∑ a ∈ B,((S.card : ℝ)-1)/30 := by simp
      _ ≤ ∑ a ∈ B,missingDegree S F a :=
        sum_le_sum (fun a ha ↦ (mem_filter.mp ha).2)
      _ ≤ ∑ a ∈ S,missingDegree S F a := sum_le_sum_of_subset_of_nonneg hBS
        (fun a _ _ ↦ missingDegree_nonneg S F a)
      _ = _ := sum_missingDegree hv hF hS
  have hn' : (2 : ℝ) ≤ S.card := by exact_mod_cast hn
  have hpos : 0 < (S.card : ℝ)-1 := by linarith
  have hBsmall : (B.card : ℝ)<((S.card : ℝ)-1)/362 := by
    have hh : (B.card : ℝ)*((S.card : ℝ)-1)<
        (((S.card : ℝ)-1)/362)*((S.card : ℝ)-1) := by nlinarith
    exact lt_of_mul_lt_mul_right hh hpos.le
  have hUcard : ((S \ B).card : ℝ)=(S.card : ℝ)-B.card := by
    have hh := card_sdiff_add_card_eq_card hBS
    have hh' : ((S \ B).card : ℝ)+B.card=S.card := by exact_mod_cast hh
    linarith
  have hUn : 2 ≤ (S \ B).card := by
    have hh : (1 : ℝ)<(S \ B).card := by rw [hUcard]; linarith
    have hh' : 1 < (S \ B).card := by exact_mod_cast hh
    omega
  have hT : ∀ R ∈ restrict F (S \ B),Valid v x R :=
    fun R hR ↦ hF R (restrict_subset _ _ hR)
  obtain ⟨a,ha,hlow⟩ := exists_missing_degree hv hT (restrict_supported _ _) hUn
  have ha' : missingDegree S F a < ((S.card : ℝ)-1)/30 := by
    have hna := (mem_sdiff.mp ha).2
    have has := (mem_sdiff.mp ha).1
    exact lt_of_not_ge (fun h ↦ hna (mem_filter.mpr ⟨has,h⟩))
  have hupp := missingDegree_restrict_le hv hF hS ha
  rw [hUcard] at hlow
  linarith

lemma natural_block_deficit {A : Finset ℕ} (hA : Good A) (x : ℝ)
    (hn : 2 ≤ A.card) :
    ((A.card : ℝ)-1)^2 ≤
      21720*((A.card : ℝ)*(A.card-1)-6*(blocks A x).card) := by
  have hh := block_deficit (goodTriple_real hA)
    (F := blocks A x) (S := univ) (fun R hR ↦ (mem_filter.mp hR).2)
    (fun R _ ↦ ⟨subset_univ _,subset_univ _⟩) (by simpa using hn)
  simpa only [card_univ,Fintype.card_coe] using hh

/-- All ordered five-tuples are counted, including repetitions. -/
lemma fives_bound {A : Finset ℕ} (hA : Good A) (x : ℤ)
    (hx : ∀ a ∈ A,x ≠ -(a : ℤ)) :
    10860*(fives A x).card ≤ 21719*A.card^2+466982*A.card := by
  by_cases hn : 2 ≤ A.card
  · have hb := natural_block_deficit hA (x : ℝ) hn
    have hf : ((fives A x).card : ℝ) ≤ 12*(blocks A (x : ℝ)).card+45*A.card := by
      exact_mod_cast OrderedFiveDeficit.fives_le_blocks hA x hx
    have hh : (10860 : ℝ)*(fives A x).card ≤
        21719*(A.card : ℝ)^2+466982*A.card := by
      nlinarith [Nat.cast_nonneg (α := ℝ) A.card]
    exact_mod_cast hh
  · have hf := fives_card_uniform hA x
    have hn' : A.card=0 ∨ A.card=1 := by omega
    rcases hn' with hc | hc <;> rw [hc] at hf ⊢ <;> norm_num at hf ⊢ <;> omega

lemma fives_with_core {A : Finset ℕ} (hA : Good A) (x : ℤ) :
    10860*(fives A x).card ≤ 21719*A.card^2+466982*A.card+
      if x ∈ negativeCore A then 43441*A.card^2 else 0 := by
  by_cases hx : x ∈ negativeCore A
  · rw [if_pos hx]
    have hh := fives_card_uniform hA x
    omega
  · rw [if_neg hx,add_zero]
    apply fives_bound hA x
    intro a ha he
    exact hx (mem_image.mpr ⟨a,ha,he.symm⟩)

lemma sum_fives {A : Finset ℕ} (hA : Good A) (S : Finset ℤ) :
    10860*(∑ x ∈ S,(fives A x).card) ≤
      (21719*A.card^2+466982*A.card)*S.card+
        43441*A.card^2*(S ∩ negativeCore A).card := by
  have hh := sum_le_sum (s := S) (fun x _ ↦ fives_with_core hA x)
  have he : (∑ x ∈ S,if x ∈ negativeCore A then 43441*A.card^2 else 0)=
      43441*A.card^2*(S ∩ negativeCore A).card := by
    rw [← sum_filter]
    have hS : S.filter (fun x ↦ x ∈ negativeCore A)=S ∩ negativeCore A := by ext; simp
    rw [hS]
    simp [mul_comm]
  rw [sum_add_distrib,he,← mul_sum] at hh
  simpa only [sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm] using hh

/-- The zero shift is excluded: its trivial triple coincidences have a
larger main term than the nonzero-shift estimate proved here. -/
lemma nonzero_sixfold {A : Finset ℕ} (hA : Good A) {δ : ℤ} (hδ : δ ≠ 0) :
    10860*(∑ a ∈ A,(fives A (δ-(a : ℤ))).card) ≤
      21719*A.card^3+510423*A.card^2 := by
  let E := A.filter (fun a : ℕ ↦ δ-(a : ℤ) ∈ negativeCore A)
  have hE : E.card ≤ 1 := OrderedFiveDeficit.nonzero_exceptional_card hA hδ
  have hh := sum_le_sum (s := A) (fun a _ ↦ fives_with_core hA (δ-(a : ℤ)))
  have he : (∑ a ∈ A,if δ-(a : ℤ) ∈ negativeCore A then 43441*A.card^2 else 0)=
      43441*A.card^2*E.card := by
    rw [← sum_filter]
    simp only [E,sum_const,nsmul_eq_mul,Nat.cast_id,mul_comm]
  rw [sum_add_distrib,he,← mul_sum] at hh
  simp only [sum_const,nsmul_eq_mul,Nat.cast_id] at hh
  have hsmall := Nat.mul_le_mul_left (43441*A.card^2) hE
  nlinarith only [hh,hsmall]

end RefinedFiveDeficit

/- A telescoping certificate improves the auxiliary cubic upper coefficient
from 3.482 to 3.48128. It does not prove the conjectured coefficient one. -/
namespace CosineBound

noncomputable def shiftTailPotential (j : ℕ) : ℝ :=
  1/(32*(4*(j : ℝ)+1))

lemma shiftTerm_simplify {j : ℕ} (hj : 0 < j) :
    shiftTerm j = 32/((64*(j : ℝ)-1)*(64*(j : ℝ)+97)) := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : 64*(j : ℝ)-1 ≠ 0 := by linarith
  have h2 : 64*(j : ℝ)+97 ≠ 0 := by positivity
  have h3 : 4*(j : ℝ)+3 ≠ 0 := by positivity
  unfold shiftTerm
  field_simp [h1, h2, h3]
  ring_nf
  field_simp [show -1+(j : ℝ)*64 ≠ 0 by linarith]
  ring

lemma shiftTailPotential_step {j : ℕ} (hj : 0 < j) :
    shiftTailPotential j-shiftTailPotential (j+1) ≤ shiftTerm j := by
  have hj' : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have h1 : 0 < (64*(j : ℝ)-1)*(64*(j : ℝ)+97) :=
    mul_pos (by linarith) (by positivity)
  have h2 : 0 < (64*(j : ℝ)+16)*(64*(j : ℝ)+80) := by positivity
  have he : shiftTailPotential j-shiftTailPotential (j+1) =
      32/((64*(j : ℝ)+16)*(64*(j : ℝ)+80)) := by
    unfold shiftTailPotential
    push_cast
    field_simp
    ring
  rw [he,shiftTerm_simplify hj]
  apply (div_le_div_iff₀ h2 h1).mpr
  nlinarith only []

lemma shift_sum_lower (K N : ℕ) (hK : 0 < K) (hKN : K ≤ N) :
    (∑ j ∈ range K,shiftTerm j)+shiftTailPotential K-shiftTailPotential N ≤
      ∑ j ∈ range N,shiftTerm j := by
  induction N,hKN using Nat.le_induction with
  | base => linarith
  | succ N hKN ih =>
    rw [sum_range_succ]
    have hs := shiftTailPotential_step (lt_of_lt_of_le hK hKN)
    linarith

lemma million_shift_terms_with_tail :
    (6703954 : ℝ)/1000000000 ≤ ∑ j ∈ (range 1000000).erase 0,shiftTerm j := by
  have hsum := shift_sum_lower 33 1000000 (by norm_num) (by norm_num)
  have hsmall := thirty_two_shift_terms
  rw [sum_erase_eq_sub (mem_range.mpr (by norm_num : 0 < 33))] at hsmall
  rw [sum_erase_eq_sub (mem_range.mpr (by norm_num : 0 < 1000000))]
  norm_num [shiftTailPotential] at hsum
  linarith

lemma shift_tail_arithmetic_bound (R : ℝ) (hR : (6703954 : ℝ)/1000000000 ≤ R) :
    (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
      256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
      (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*R < -(363 : ℝ)/200000 := by
  have hp := Real.pi_pos
  have hp32 : 0 < Real.pi/32 := by positivity
  have hp16 : 0 < Real.pi/16 := by positivity
  have hs32 := (Real.sin_gt_sub_cube hp32 (by linarith [Real.pi_lt_four])).le
  have hs16 := (Real.sin_gt_sub_cube hp16 (by linarith [Real.pi_lt_four])).le
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi/32)
  have hs0 : 0 ≤ Real.sin (Real.pi/32) :=
    (Real.sin_pos_of_pos_of_lt_pi hp32 (by linarith)).le
  let R₀ : ℝ := 6703954/1000000000
  have hR₀ : 0 ≤ R₀ := by norm_num [R₀]
  have hb : (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
      256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
      (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*R ≤
      (32/9-(512/147)*(1-(Real.pi/32)^2/2))/Real.pi^2 -
      256*(Real.pi/16-(Real.pi/16)^3/4)/(441*Real.pi^3) -
      (1024*(Real.pi/32-(Real.pi/32)^3/4)/(3*Real.pi^3))*R₀ := by
    calc
      _ ≤ (32/9-(512/147)*Real.cos (Real.pi/32))/Real.pi^2 -
          256*Real.sin (Real.pi/16)/(441*Real.pi^3) -
          (1024*Real.sin (Real.pi/32)/(3*Real.pi^3))*R₀ := by
        gcongr
      _ ≤ _ := by gcongr
  have he : (32/9-(512/147)*(1-(Real.pi/32)^2/2))/Real.pi^2 -
      256*(Real.pi/16-(Real.pi/16)^3/4)/(441*Real.pi^3) -
      (1024*(Real.pi/32-(Real.pi/32)^3/4)/(3*Real.pi^3))*R₀ =
      (16/441-(32/3)*R₀)/Real.pi^2+1/576+R₀/384 := by
    field_simp
    ring
  rw [he] at hb
  have hp2 : Real.pi^2 < (986961 : ℝ)/100000 := by
    nlinarith [Real.pi_lt_d6]
  have hd : (16/441-(32/3)*R₀)/Real.pi^2 ≤
      (16/441-(32/3)*R₀)/(986961/100000) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hp) (by norm_num)).mpr
    dsimp [R₀]
    nlinarith only [hp2]
  have hfinal : (16/441-(32/3)*R₀)/(986961/100000)+1/576+R₀/384 < -(363 : ℝ)/200000 := by
    norm_num [R₀]
  linarith

lemma shifted_million_modes_tail_strict :
    2*generalDenominator (range 1000000) coeff shiftedFreq < (348128 : ℝ)/100000 := by
  have hh := shifted_denominator_difference ((range 1000000).erase 0) (by simp)
  rw [insert_erase (mem_range.mpr (by norm_num : 0 < 1000000))] at hh
  have hb := shift_tail_arithmetic_bound _ million_shift_terms_with_tail
  rw [← hh] at hb
  have ho := million_modes_strict
  linarith

end CosineBound

lemma f_cube_ratio_eventually_lt_shifted_cosine_tail_bound :
    ∀ᶠ N : ℕ in atTop, (f N 3 : ℝ)^3/N < (348128 : ℝ)/100000 :=
  f_cube_ratio_eventually_lt_general_cosine_bound (range 1000000)
    CosineBound.coeff CosineBound.shiftedFreq
    (fun i _ ↦ (CosineBound.coeff_pos i).le) (348128/100000)
    CosineBound.shifted_million_modes_tail_strict


/- A rational first-weight adjustment further improves the auxiliary upper
coefficient to 3.4812. The original coefficient-one conjecture remains open here. -/
namespace CosineBound

noncomputable def adjustedCoeff (j : ℕ) : ℝ :=
  coeff j + if j=0 then 1/150 else 0

lemma adjustedCoeff_pos (j : ℕ) : 0 < adjustedCoeff j := by
  unfold adjustedCoeff
  have hc := coeff_pos j
  split_ifs <;> linarith

lemma generalDenominator_congr_weights (T : Finset ℕ) (w v θ : ℕ → ℝ)
    (he : ∀ j ∈ T,w j=v j) : generalDenominator T w θ=generalDenominator T v θ := by
  unfold generalDenominator
  congr 1
  · congr 2
    apply sum_congr rfl
    intro j hj
    rw [he j hj]
  · apply sum_congr rfl
    intro i hi
    apply sum_congr rfl
    intro j hj
    rw [he i hi,he j hj]

noncomputable def shiftGradient (R : ℝ) : ℝ :=
  8/(3*Real.pi)-128*Real.cos (Real.pi/32)/(49*Real.pi)-
    128*Real.sin (Real.pi/16)/(147*Real.pi^2)-
    (256*Real.sin (Real.pi/32)/Real.pi^2)*R

lemma shiftGradient_bound (R : ℝ) (hR : (6703954 : ℝ)/1000000000 ≤ R) :
    shiftGradient R < -(8 : ℝ)/625 := by
  have hp := Real.pi_pos
  have hp32 : 0 < Real.pi/32 := by positivity
  have hp16 : 0 < Real.pi/16 := by positivity
  have hs32 := (Real.sin_gt_sub_cube hp32 (by linarith [Real.pi_lt_four])).le
  have hs16 := (Real.sin_gt_sub_cube hp16 (by linarith [Real.pi_lt_four])).le
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi/32)
  have hs0 : 0 ≤ Real.sin (Real.pi/32) :=
    (Real.sin_pos_of_pos_of_lt_pi hp32 (by linarith)).le
  let R₀ : ℝ := 6703954/1000000000
  have hR₀ : 0 ≤ R₀ := by norm_num [R₀]
  have hb : shiftGradient R ≤
      8/(3*Real.pi)-128*(1-(Real.pi/32)^2/2)/(49*Real.pi)-
        128*(Real.pi/16-(Real.pi/16)^3/4)/(147*Real.pi^2)-
        (256*(Real.pi/32-(Real.pi/32)^3/4)/Real.pi^2)*R₀ := by
    unfold shiftGradient
    calc
      _ ≤ 8/(3*Real.pi)-128*Real.cos (Real.pi/32)/(49*Real.pi)-
          128*Real.sin (Real.pi/16)/(147*Real.pi^2)-
          (256*Real.sin (Real.pi/32)/Real.pi^2)*R₀ := by gcongr
      _ ≤ _ := by gcongr
  have he : 8/(3*Real.pi)-128*(1-(Real.pi/32)^2/2)/(49*Real.pi)-
      128*(Real.pi/16-(Real.pi/16)^3/4)/(147*Real.pi^2)-
      (256*(Real.pi/32-(Real.pi/32)^3/4)/Real.pi^2)*R₀ =
      -(8*R₀)/Real.pi+Real.pi*(25/18816+R₀/512) := by
    field_simp
    ring
  rw [he] at hb
  have hpi : Real.pi ≤ (22 : ℝ)/7 := Real.pi_lt_d6.le.trans (by norm_num)
  have hd : -(8*R₀)/Real.pi ≤ -(8*R₀)/(22/7) := by
    apply (div_le_div_iff₀ hp (by norm_num)).mpr
    nlinarith only [hpi,hR₀]
  have hm : Real.pi*(25/18816+R₀/512) ≤ (22/7)*(25/18816+R₀/512) := by
    gcongr
  have hf : -(8*R₀)/(22/7)+(22/7)*(25/18816+R₀/512) < -(8 : ℝ)/625 := by
    norm_num [R₀]
  linarith

lemma adjusted_denominator_difference (T : Finset ℕ) (hT : 0 ∉ T) :
    generalDenominator (insert 0 T) adjustedCoeff shiftedFreq-
      generalDenominator (insert 0 T) coeff shiftedFreq =
      shiftGradient (∑ j ∈ T,shiftTerm j)/150+
        (1+Real.sinc (2*shiftedFreq 0))/22500 := by
  have hj (j : ℕ) (h : j ∈ T) : j ≠ 0 := by rintro rfl; exact hT h
  have hw (j : ℕ) (h : j ∈ T) : adjustedCoeff j=coeff j := by
    simp [adjustedCoeff,hj j h]
  have hg := generalDenominator_congr_weights T adjustedCoeff coeff shiftedFreq hw
  have hcross : (∑ j ∈ T,coeff j*(Real.sinc (shiftedFreq 0-shiftedFreq j)+
      Real.sinc (shiftedFreq 0+shiftedFreq j))) =
      -(128*Real.sin (Real.pi/32)/Real.pi^2)*∑ j ∈ T,shiftTerm j := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j h
    rw [shiftedFreq_of_ne (hj j h)]
    exact sinc_shifted_cross j (hj j h)
  have hcross' : (∑ j ∈ T,adjustedCoeff j*(Real.sinc (shiftedFreq 0-shiftedFreq j)+
      Real.sinc (shiftedFreq 0+shiftedFreq j))) =
      -(128*Real.sin (Real.pi/32)/Real.pi^2)*∑ j ∈ T,shiftTerm j := by
    rw [← hcross]
    apply sum_congr rfl
    intro j h
    rw [hw j h]
  rw [generalDenominator_insert T adjustedCoeff shiftedFreq 0 hT,
    generalDenominator_insert T coeff shiftedFreq 0 hT,hg,hcross,hcross',
    sinc_shifted_zero,sinc_twice_shifted_zero]
  unfold shiftGradient
  simp only [adjustedCoeff,coeff,Nat.cast_zero,mul_zero,zero_add,ite_true]
  field_simp
  ring

lemma adjusted_million_modes_strict :
    2*generalDenominator (range 1000000) adjustedCoeff shiftedFreq < (8703 : ℝ)/2500 := by
  have hh := adjusted_denominator_difference ((range 1000000).erase 0) (by simp)
  rw [insert_erase (mem_range.mpr (by norm_num : 0 < 1000000))] at hh
  have hb := shiftGradient_bound _ million_shift_terms_with_tail
  have hd : 1+Real.sinc (2*shiftedFreq 0) ≤ 1 := by
    rw [sinc_twice_shifted_zero]
    have hs : 0 ≤ Real.sin (Real.pi/16) :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).le
    have hp := Real.pi_pos
    have : 0 ≤ 16*Real.sin (Real.pi/16)/(49*Real.pi) := by positivity
    simp only [neg_mul,neg_div]
    linarith
  have ho := shifted_million_modes_tail_strict
  linarith

end CosineBound

lemma f_cube_ratio_eventually_lt_adjusted_cosine_bound :
    ∀ᶠ N : ℕ in atTop,(f N 3 : ℝ)^3/N < (8703 : ℝ)/2500 :=
  f_cube_ratio_eventually_lt_general_cosine_bound (range 1000000)
    CosineBound.adjustedCoeff CosineBound.shiftedFreq
    (fun i _ ↦ (CosineBound.adjustedCoeff_pos i).le) (8703/2500)
    CosineBound.adjusted_million_modes_strict


/--
Is it true that $f(N)\sim N^{1/3}$?

Originally asked to Erdős by Bose.

This is discussed in problem C11 of Guy's collection [Gu04].
-/
theorem erdos_241 :
    (fun N ↦ (f N 3 : ℝ)) ~[atTop] (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / 3)) := by
  sorry

/--
The conjecture that the size of the set $A\subseteq \{1,\ldots,N\}$ is asymptotically $N^{1/r}$.
-/
def BoseChowlaConjecture (r : ℕ) : Prop :=
  (fun N ↦ (f N r : ℝ)) ~[atTop] (fun N ↦ (N : ℝ) ^ ((1 : ℝ) / r))

end Erdos241
