import Submission.ArithmeticReduction
import Submission.NonemptyArithmeticCompletion

/-! Completion at a least odd period, preserving separation of comparable
classes. This is a normal form for hypothetical covers, not their exclusion. -/
namespace Erdos7SeparatedCompletion
open Erdos7Reduction Erdos7NonemptyArithmeticCompletion
set_option autoImplicit false
set_option maxHeartbeats 4000000

def CoversOn (S : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ x : ℤ, ∃ d ∈ S, (d : ℤ) ∣ x-a d

def Downclosed (S : Finset ℕ) : Prop :=
  ∀ n ∈ S, ∀ d, 1 < d → d ∣ n → d ∈ S

def Separated (S : Finset ℕ) (a : ℕ → ℤ) : Prop :=
  ∀ m ∈ S, ∀ n ∈ S, m ≠ n → m ∣ n → ¬ (m : ℤ) ∣ a n-a m

lemma coversOn_hasCover (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (S : Finset ℕ) (a : ℕ → ℤ) (hS : S ⊆ nontrivialDivisors N)
    (hc : CoversOn S a) : HasOddArithmeticCover N S.card := by
  classical
  refine ⟨hN, ↥S, inferInstance, (fun d => d.val), (fun d => a d.val),
    Subtype.val_injective, ?_, ?_, ?_, ?_⟩
  · intro d
    have hd := (mem_nontrivialDivisors N d hN).mp (hS d.property)
    exact ⟨hd.1, hodd.of_dvd_nat hd.2⟩
  · intro x
    obtain ⟨d,hd,hx⟩ := hc x
    exact ⟨⟨d,hd⟩,hx⟩
  · intro d
    exact ((mem_nontrivialDivisors N d hN).mp (hS d.property)).2
  · simp

lemma smaller_divisor_hole (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (hmin : ∀ M, M < N → Odd M → ∀ K, ¬ HasOddArithmeticCover M K)
    (S : Finset ℕ) (a : ℕ → ℤ) (hS : S ⊆ nontrivialDivisors N)
    (d : ℕ) (hd : d ∈ nontrivialDivisors N) (hdN : d < N) :
    ∃ x : ℤ, ∀ m ∈ S, m ∣ d → ¬ (m : ℤ) ∣ x-a m := by
  classical
  have hd' := (mem_nontrivialDivisors N d hN).mp hd
  have hd0 : 0 < d := by omega
  have hdo : Odd d := hodd.of_dvd_nat hd'.2
  let T := S.filter (· ∣ d)
  have hT : T ⊆ nontrivialDivisors d := by
    intro m hm
    obtain ⟨hm, hmd⟩ := Finset.mem_filter.mp hm
    exact (mem_nontrivialDivisors d m hd0).mpr
      ⟨((mem_nontrivialDivisors N m hN).mp (hS hm)).1,hmd⟩
  have hn : ¬ CoversOn T a := by
    intro hc
    exact hmin d hdN hdo T.card (coversOn_hasCover d hd0 hdo T a hT hc)
  unfold CoversOn at hn
  push_neg at hn
  obtain ⟨x,hx⟩ := hn
  exact ⟨x,fun m hm hmd => hx m (Finset.mem_filter.mpr ⟨hm,hmd⟩)⟩

lemma separated_insert (S : Finset ℕ) (a : ℕ → ℤ)
    (hc : CoversOn S a) (hclosed : Downclosed S) (hsep : Separated S a)
    (d : ℕ) (hd : 1 < d) (hdS : d ∉ S)
    (hlower : ∀ m, 1 < m → m ∣ d → m ≠ d → m ∈ S)
    (x : ℤ) (hx : ∀ m ∈ S, m ∣ d → ¬ (m : ℤ) ∣ x-a m) :
    CoversOn (insert d S) (Function.update a d x) ∧
    Downclosed (insert d S) ∧ Separated (insert d S) (Function.update a d x) := by
  classical
  have hne (m : ℕ) (hm : m ∈ S) : m ≠ d := by
    intro he; subst m; exact hdS hm
  refine ⟨?_,?_,?_⟩
  · intro z
    obtain ⟨m,hm,hz⟩ := hc z
    exact ⟨m,Finset.mem_insert_of_mem hm,by simpa [hne m hm] using hz⟩
  · intro n hn m hm hmn
    rcases Finset.mem_insert.mp hn with hnd | hn
    · subst n
      by_cases he : m = d
      · subst m; simp
      · exact Finset.mem_insert_of_mem (hlower m hm hmn he)
    · exact Finset.mem_insert_of_mem (hclosed n hn m hm hmn)
  · intro m hm n hn hmn hdiv
    rcases Finset.mem_insert.mp hm with hmd | hm
    · subst m
      rcases Finset.mem_insert.mp hn with hnd | hn
      · exact False.elim (hmn hnd.symm)
      · exact False.elim (hdS (hclosed n hn d hd hdiv))
    · rcases Finset.mem_insert.mp hn with hnd | hn
      · subst n
        simpa [hne m hm] using hx m hm hdiv
      · simpa [hne m hm,hne n hn] using hsep m hm n hn hmn hdiv

/-- At a least odd period, a separated divisor-closed cover can be extended
until every proper nontrivial divisor is represented. The full-period label
is deliberately not required: adding it could be impossible. -/
theorem complete_proper_divisors (N : ℕ) (hN : 0 < N) (hodd : Odd N)
    (hmin : ∀ M, M < N → Odd M → ∀ K, ¬ HasOddArithmeticCover M K)
    (S : Finset ℕ) (a : ℕ → ℤ) (hS : S ⊆ nontrivialDivisors N)
    (hc : CoversOn S a) (hclosed : Downclosed S) (hsep : Separated S a) :
    ∃ (T : Finset ℕ) (b : ℕ → ℤ),
      T ⊆ nontrivialDivisors N ∧ CoversOn T b ∧ Downclosed T ∧ Separated T b ∧
      ∀ d, 1 < d → d ∣ N → d < N → d ∈ T := by
  classical
  let D := nontrivialDivisors N
  let P (k : ℕ) := ∃ (T : Finset ℕ) (b : ℕ → ℤ),
    T ⊆ D ∧ CoversOn T b ∧ Downclosed T ∧ Separated T b ∧ (D \ T).card = k
  have hex : ∃ k, P k := ⟨(D \ S).card,S,a,hS,hc,hclosed,hsep,rfl⟩
  obtain ⟨T,b,hT,hcov,hcl,hse,hcard⟩ := Nat.find_spec hex
  refine ⟨T,b,hT,hcov,hcl,hse,?_⟩
  by_contra hn
  push_neg at hn
  obtain ⟨e,he,heN,helt,heT⟩ := hn
  let F := (D \ T).filter (· < N)
  have heF : e ∈ F := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
      ⟨(mem_nontrivialDivisors N e hN).mpr ⟨he,heN⟩,heT⟩,helt⟩
  have hF : F.Nonempty := ⟨e,heF⟩
  let d := F.min' hF
  have hdF : d ∈ F := Finset.min'_mem F hF
  obtain ⟨hdDT,hdN⟩ := Finset.mem_filter.mp hdF
  obtain ⟨hdD,hdT⟩ := Finset.mem_sdiff.mp hdDT
  have hd := (mem_nontrivialDivisors N d hN).mp hdD
  have hlow : ∀ m, 1 < m → m ∣ d → m ≠ d → m ∈ T := by
    intro m hm hmd hne
    by_contra hmT
    have hmdlt : m < d := Nat.lt_of_le_of_ne (Nat.le_of_dvd (by omega) hmd) hne
    have hmF : m ∈ F := Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr
      ⟨(mem_nontrivialDivisors N m hN).mpr ⟨hm,hmd.trans hd.2⟩,hmT⟩,
      hmdlt.trans hdN⟩
    have hle : d ≤ m := Finset.min'_le F m hmF
    omega
  obtain ⟨x,hx⟩ := smaller_divisor_hole N hN hodd hmin T b hT d hdD hdN
  obtain ⟨hcov',hcl',hse'⟩ := separated_insert T b hcov hcl hse d hd.1 hdT hlow x hx
  have hsub : insert d T ⊆ D := Finset.insert_subset hdD hT
  have hP : P ((D \ insert d T).card) :=
    ⟨insert d T,Function.update b d x,hsub,hcov',hcl',hse',rfl⟩
  have hleast := Nat.find_min' hex hP
  have hstrict : D \ insert d T ⊂ D \ T := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.sdiff_subset_sdiff (by rfl) (Finset.subset_insert d T),?_⟩
    intro heq
    have hmem : d ∈ D \ T := Finset.mem_sdiff.mpr ⟨hdD,hdT⟩
    rw [←heq] at hmem
    simp at hmem
  have hlt := Finset.card_lt_card hstrict
  omega

/-- Every hypothetical odd cover has a least-period representative and then
an enlarged, comparable-separated family containing every proper divisor.
No preservation of the number of classes or private points is asserted. -/
theorem least_period_normal_form (N K : ℕ) (hodd : Odd N)
    (hc : HasOddArithmeticCover N K) :
    ∃ M, M ≤ N ∧ 0 < M ∧ Odd M ∧
      (∀ L, L < M → Odd L → ∀ k, ¬ HasOddArithmeticCover L k) ∧
      ∃ (T : Finset ℕ) (b : ℕ → ℤ),
        T ⊆ nontrivialDivisors M ∧ CoversOn T b ∧ Downclosed T ∧ Separated T b ∧
        ∀ d, 1 < d → d ∣ M → d < M → d ∈ T := by
  classical
  have hex : ∃ M, Odd M ∧ ∃ k, HasOddArithmeticCover M k := ⟨N,hodd,K,hc⟩
  let M := Nat.find hex
  obtain ⟨hMo,k,hk⟩ := Nat.find_spec hex
  have hM0 : 0 < M := hk.1
  have hmin : ∀ L, L < M → Odd L → ∀ k, ¬ HasOddArithmeticCover L k := by
    intro L hL hLo k hcov
    have hle := Nat.find_min' hex ⟨hLo,k,hcov⟩
    omega
  obtain ⟨I,fI,m,a,hm,hmM,_,hcl,hpriv⟩ :=
    exists_irredundant_divisor_closed_odd_cover M k hk
  letI : Fintype I := fI
  let S := Finset.univ.image m
  let b := completedResidue m a (fun _ => 0)
  have hb (i : I) : b (m i) = a i := completedResidue_old m a _ hm.1 i
  have hS : S ⊆ nontrivialDivisors M := by
    intro d hd
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
    exact (mem_nontrivialDivisors M (m i) hM0).mpr ⟨(hm.2.1 i).1,hmM i⟩
  have hcov : CoversOn S b := by
    intro x
    obtain ⟨i,hi⟩ := hm.2.2 x
    exact ⟨m i,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩,by simpa [hb] using hi⟩
  have hclosed : Downclosed S := by
    intro n hn d hd hdn
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hn
    obtain ⟨j,hj⟩ := hcl i d hd hdn
    exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
  have hsep : Separated S b := by
    intro d hd n hn hne hdiv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hd
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hn
    rw [hb,hb]
    exact residue_not_congruent_of_proper_modulus_divisor m a hpriv hm.2.2
      (fun hij => hne (congrArg m hij)) hdiv
  exact ⟨M,Nat.find_min' hex ⟨hodd,K,hc⟩,hM0,hMo,hmin,
    complete_proper_divisors M hM0 hMo hmin S b hS hcov hclosed hsep⟩

/-- Arithmetic entry point, with an odd product period. -/
theorem arithmetic_normal_form {I : Type} [Fintype I]
    (m : I → ℕ) (a : I → ℤ) (hc : IsOddArithmeticCover m a) :
    ∃ (N : ℕ) (T : Finset ℕ) (b : ℕ → ℤ),
      0 < N ∧ Odd N ∧ T ⊆ nontrivialDivisors N ∧ CoversOn T b ∧
      Downclosed T ∧ Separated T b ∧
      ∀ d, 1 < d → d ∣ N → d < N → d ∈ T := by
  classical
  let P := ∏ i, m i
  have hP : 0 < P := Finset.prod_pos (fun i _ => by have := (hc.2.1 i).1; omega)
  have hPo : Odd P := Finset.prod_induction m Odd
    (fun _ _ hu hv => hu.mul hv) (by norm_num) (fun i _ => (hc.2.1 i).2)
  have hpkg : HasOddArithmeticCover P (Fintype.card I) :=
    ⟨hP,I,inferInstance,m,a,hc.1,hc.2.1,hc.2.2,
      fun i => Finset.dvd_prod_of_mem m (Finset.mem_univ i),le_rfl⟩
  obtain ⟨N,_,hN,hNo,_,T,b,hT,hcov,hcl,hsep,hfull⟩ :=
    least_period_normal_form P (Fintype.card I) hPo hpkg
  exact ⟨N,T,b,hN,hNo,hT,hcov,hcl,hsep,hfull⟩

#print axioms least_period_normal_form
#print axioms arithmetic_normal_form

#print axioms complete_proper_divisors
end Erdos7SeparatedCompletion
