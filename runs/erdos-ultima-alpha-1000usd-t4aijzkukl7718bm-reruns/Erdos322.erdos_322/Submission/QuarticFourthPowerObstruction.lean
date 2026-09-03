import Submission.Spec

/-! A finite obstruction to fourth-power target amplification. -/
namespace Erdos322Research.QuarticFourthPower

open Erdos322

set_option maxRecDepth 100000

private def rootApprox (n : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, lo, _ => lo
  | k+1, lo, hi =>
      let mid := (lo+hi)/2
      if mid^4 ≤ n then rootApprox n k mid hi else rootApprox n k lo mid

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem finite_certificate :
    ∀ (x y : Fin 26) (z : Fin 52),
      let S := (10*x.val)^4+(10*y.val)^4+(5*z.val)^4
      S ≤ 259^4 →
      (x.val=0 ∧ y.val=0 ∧ z.val=0) ∨
      (let q := rootApprox (259^4-S) 9 0 512
       q^4 < 259^4-S ∧ 259^4-S < (q+1)^4) := by
  decide

private lemma fourth_mod_five (a : ℕ) : a^4%5=if 5∣a then 0 else 1 := by
  have h : ∀ r : Fin 5, r.val^4%5=if r.val%5=0 then 0 else 1 := by decide
  have hh := h ⟨a%5,Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.mod_mod,←Nat.pow_mod,Nat.dvd_iff_mod_eq_zero] using hh

private lemma fourth_mod_sixteen (a : ℕ) : a^4%16=if 2∣a then 0 else 1 := by
  have h : ∀ r : Fin 16, r.val^4%16=if r.val%2=0 then 0 else 1 := by decide
  have hh := h ⟨a%16,Nat.mod_lt _ (by decide)⟩
  simpa only [Nat.mod_mod_of_dvd a (by decide : 2∣16),←Nat.pow_mod,
    Nat.dvd_iff_mod_eq_zero] using hh

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private lemma permutation_certificate :
    ∀ p q : Fin 4 → Bool,
      (∑ i, if p i then (0:ℕ) else 1)=1 →
      (∑ i, if q i then (0:ℕ) else 1)=1 →
      ∃ σ : Fin 4 → Fin 4, Function.Bijective σ ∧
        p (σ 0)=true ∧ q (σ 0)=true ∧
        p (σ 1)=true ∧ q (σ 1)=true ∧ p (σ 2)=true := by
  decide

private lemma residue_count {n m d : ℕ} (a : Fin 4 → ℕ)
    (ha : ∑ i, a i^4=n) (hm : 4 < m) (hn : n%m=1)
    (hres : ∀ x : ℕ, x^4%m=if d∣x then 0 else 1) :
    (∑ i, if d∣a i then (0:ℕ) else 1)=1 := by
  have hb : (∑ i : Fin 4, if d∣a i then (0:ℕ) else 1) ≤ 4 := by
    calc
      _ ≤ ∑ _i : Fin 4, (1:ℕ) := Finset.sum_le_sum (fun i _ ↦ by split_ifs <;> omega)
      _ = 4 := by simp
  have hh := congrArg (fun z : ℕ ↦ z%m) ha
  dsimp only at hh
  rw [Finset.sum_nat_mod] at hh
  simp only [hres,hn] at hh
  rw [Nat.mod_eq_of_lt (hb.trans_lt hm)] at hh
  exact hh

/-- The only representations of `259^4` are the one-coordinate ones. -/
theorem single_coordinate_of_sum {a : Fin 4 → ℕ} (ha : ∑ i, a i^4=259^4) :
    ∃ j : Fin 4, a j=259 ∧ ∀ i, i≠j → a i=0 := by
  have hbound (i : Fin 4) : a i≤259 := by
    apply (Nat.pow_le_pow_iff_left (by decide : (4:ℕ)≠0)).mp
    rw [←ha]
    exact Finset.single_le_sum (f := fun i : Fin 4 ↦ a i^4)
      (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  have hp := residue_count a ha (by decide : 4 < 5) (by decide) fourth_mod_five
  have hq := residue_count a ha (by decide : 4 < 16) (by decide) fourth_mod_sixteen
  obtain ⟨σ,hσ,hp0,hq0,hp1,hq1,hp2⟩ := permutation_certificate
    (fun i ↦ decide (5∣a i)) (fun i ↦ decide (2∣a i)) (by simpa using hp) (by simpa using hq)
  have h50 : 5∣a (σ 0) := of_decide_eq_true hp0
  have h20 : 2∣a (σ 0) := of_decide_eq_true hq0
  have h51 : 5∣a (σ 1) := of_decide_eq_true hp1
  have h21 : 2∣a (σ 1) := of_decide_eq_true hq1
  have h52 : 5∣a (σ 2) := of_decide_eq_true hp2
  have hd0 : 10∣a (σ 0) := by
    apply Nat.dvd_of_mod_eq_zero
    have := Nat.mod_eq_zero_of_dvd h50
    have := Nat.mod_eq_zero_of_dvd h20
    omega
  have hd1 : 10∣a (σ 1) := by
    apply Nat.dvd_of_mod_eq_zero
    have := Nat.mod_eq_zero_of_dvd h51
    have := Nat.mod_eq_zero_of_dvd h21
    omega
  have he0 := Nat.mul_div_cancel' hd0
  have he1 := Nat.mul_div_cancel' hd1
  have he2 := Nat.mul_div_cancel' h52
  let x : Fin 26 := ⟨a (σ 0)/10,by have := hbound (σ 0); omega⟩
  let y : Fin 26 := ⟨a (σ 1)/10,by have := hbound (σ 1); omega⟩
  let z : Fin 52 := ⟨a (σ 2)/5,by have := hbound (σ 2); omega⟩
  have hs : (10*x.val)^4+(10*y.val)^4+(5*z.val)^4+a (σ 3)^4=259^4 := by
    have hh := (hσ.sum_comp (fun i ↦ a i^4)).trans ha
    simpa only [Fin.sum_univ_four,x,y,z,he0,he1,he2] using hh
  have hb : (10*x.val)^4+(10*y.val)^4+(5*z.val)^4≤259^4 := by omega
  have hzero : x.val=0 ∧ y.val=0 ∧ z.val=0 := by
    rcases finite_certificate x y z hb with hz | hgap
    · exact hz
    · dsimp only at hgap
      have he : 259^4-((10*x.val)^4+(10*y.val)^4+(5*z.val)^4)=a (σ 3)^4 := by omega
      rw [he] at hgap
      have hlt := (Nat.pow_lt_pow_iff_left (by decide : (4:ℕ)≠0)).mp hgap.1
      have hgt := (Nat.pow_lt_pow_iff_left (by decide : (4:ℕ)≠0)).mp hgap.2
      omega
  have hz0 : a (σ 0)=0 := by
    have := hzero.1
    change a (σ 0)/10=0 at this
    omega
  have hz1 : a (σ 1)=0 := by
    have := hzero.2.1
    change a (σ 1)/10=0 at this
    omega
  have hz2 : a (σ 2)=0 := by
    have := hzero.2.2
    change a (σ 2)/5=0 at this
    omega
  have hh := (hσ.sum_comp (fun i ↦ a i^4)).trans ha
  norm_num only [Fin.sum_univ_four,hz0,hz1,hz2,zero_pow,zero_add] at hh
  change a (σ 3)^4=259^4 at hh
  have h259 : a (σ 3)=259 := by
    have hle := (Nat.pow_le_pow_iff_left (by decide : (4:ℕ)≠0)).mp hh.le
    have hge := (Nat.pow_le_pow_iff_left (by decide : (4:ℕ)≠0)).mp hh.ge
    omega
  refine ⟨σ 3,h259,?_⟩
  intro i hi
  obtain ⟨t,rfl⟩ := hσ.2 i
  fin_cases t
  · exact hz0
  · exact hz1
  · exact hz2
  · exact (hi rfl).elim

private def singleRep (j : Fin 4) : Fin 4 → Fin (259^4+1) := fun i ↦
  ⟨if i=j then 259 else 0,by split_ifs <;> norm_num⟩

private lemma singleRep_sum (j : Fin 4) : ∑ i, (singleRep j i : ℕ)^4=259^4 := by
  simp [singleRep]

private lemma singleRep_injective : Function.Injective singleRep := by
  intro i j h
  by_contra hij
  have hh := congrArg (fun a : Fin 4 → Fin (259^4+1) ↦ (a i : ℕ)) h
  simp [singleRep,hij] at hh

/-- Exact ordered representation count at the fourth-power target. -/
theorem count_259_fourth : representationCount 4 (259^4)=4 := by
  classical
  unfold representationCount
  have he : (Finset.univ.filter (fun a : Fin 4 → Fin (259^4+1) ↦
      ∑ i, (a i : ℕ)^4=259^4))=Finset.univ.image singleRep := by
    ext a
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
    constructor
    · intro ha
      obtain ⟨j,hj,hzero⟩ := single_coordinate_of_sum ha
      refine ⟨j,?_⟩
      funext i
      apply Fin.ext
      change (if i=j then 259 else 0)=(a i : ℕ)
      split_ifs with hij
      · subst i; exact hj.symm
      · exact (hzero i hij).symm
    · rintro ⟨j,rfl⟩
      exact singleRep_sum j
  rw [he,Finset.card_image_of_injective _ singleRep_injective]
  simp

/-- The two unordered representations give exactly eight ordered ones. -/
theorem count_259 : representationCount 4 259=8 := by
  classical
  let small := (Finset.univ : Finset (Fin 4 → Fin 5)).filter
    (fun a ↦ ∑ i, (a i : ℕ)^4=259)
  let big := (Finset.univ : Finset (Fin 4 → Fin 260)).filter
    (fun a ↦ ∑ i, (a i : ℕ)^4=259)
  let f : (Fin 4 → Fin 5) → (Fin 4 → Fin 260) := fun a i ↦
    ⟨a i,(a i).isLt.trans (by decide)⟩
  have hc : small.card=big.card := by
    apply Finset.card_nbij f
    · intro a ha
      simp only [small,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at ha
      simpa only [big,f,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] using ha
    · intro a _ b _ he
      funext i
      apply Fin.ext
      exact congrArg (fun z : Fin 4 → Fin 260 ↦ (z i : ℕ)) he
    · intro b hb
      simp only [big,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] at hb
      have hbound (i : Fin 4) : (b i : ℕ)<5 := by
        have hi := Finset.single_le_sum (f := fun j : Fin 4 ↦ (b j : ℕ)^4)
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
        rw [hb] at hi
        dsimp only at hi
        by_contra hn
        have hp := Nat.pow_le_pow_left (Nat.le_of_not_gt hn) 4
        norm_num at hp
        omega
      let a : Fin 4 → Fin 5 := fun i ↦ ⟨b i,hbound i⟩
      refine ⟨a,?_,?_⟩
      · simpa only [small,a,Finset.mem_coe,Finset.mem_filter,Finset.mem_univ,true_and] using hb
      · funext i; apply Fin.ext; rfl
  change big.card=8
  rw [←hc]
  change ((Finset.univ : Finset (Fin 4 → Fin 5)).filter
    (fun a ↦ ∑ i, (a i : ℕ)^4=259)).card=8
  decide

private lemma count_scale_sixteen_pow (n m : ℕ) :
    representationCount 4 (16^m*n)=representationCount 4 n := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ',mul_assoc,quartic_count_scale_two,ih]

/-- There are infinitely many targets whose ordered count drops from eight
 to four upon taking the fourth power. -/
theorem infinitely_many_count_decreases :
    {n : ℕ | representationCount 4 n=8 ∧ representationCount 4 (n^4)=4}.Infinite := by
  have hi : Function.Injective (fun m : ℕ ↦ 16^m*259) := by
    intro a b he
    have hp : 16^a=16^b := Nat.mul_right_cancel (by decide : 0 < 259) he
    exact Nat.pow_right_injective (by decide : 2≤16) hp
  apply (Set.infinite_range_of_injective hi).mono
  rintro n ⟨m,rfl⟩
  constructor
  · rw [count_scale_sixteen_pow,count_259]
  · rw [mul_pow,←pow_mul,count_scale_sixteen_pow,count_259_fourth]

/-- Fourth-power target amplification does not even eventually preserve
 the original representation count. -/
theorem no_eventual_fourth_power_monotonicity :
    ¬ ∃ N : ℕ, ∀ n : ℕ, N≤n → representationCount 4 n≤representationCount 4 (n^4) := by
  rintro ⟨N,hN⟩
  obtain ⟨n,hn,hlarge⟩ := infinitely_many_count_decreases.exists_gt N
  have h := hN n hlarge.le
  simp only [Set.mem_setOf_eq] at hn
  omega

end Erdos322Research.QuarticFourthPower
