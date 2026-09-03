import Submission.QuadraticEqualDiscriminant

/-! Quantitative CRT control of two distinct prime divisibility conditions
under a fixed unit head. -/
namespace Erdos1206.DualPrimeConditionalCounts
open Finset Filter QuadraticSquarefreeSieve QuadraticConditionalCounts
  QuadraticUnitResidues PrimeBoxCRT BoxDensityLimits
open scoped Classical
set_option maxHeartbeats 2000000

lemma positive_discrepancy (S : Finset ℕ) (hS : ∀ p∈S, p.Prime)
    (G : (p : ℕ) → Finset (ZMod p × ZMod p)) (N : ℕ) :
    |((positiveBox N (fun x => ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p)).card:ℝ)-
      (∏p∈S,localDensity G p)*(N:ℝ)^2| ≤
        2*(N:ℝ)*(∏p∈S,(p:ℝ))+(∏p∈S,(p:ℝ))^2+N := by
  apply trimmed_discrepancy
  have heq : box N (fun x => ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p)=
      (range N ×ˢ range N).filter (fun x => ∀ p∈S, ((x.1:ZMod p),(x.2:ZMod p))∈G p) := by
    ext x
    simp only [BoxDensityLimits.box,mem_filter]
  rw [heq,mul_comm (∏p∈S,localDensity G p)]
  exact joint_box_discrepancy S hS G N

noncomputable def jointCounts (a b c : Fin 4 → ℕ) (S : Finset ℕ)
    (i j : Fin 4) (N p q : ℕ) : Finset (ℕ × ℕ) :=
  positiveBox N (fun x => Head a b c S x ∧
    p∣quad (a i) (b i) (c i) x.1 x.2 ∧ q∣quad (a j) (b j) (c j) x.1 x.2)

noncomputable def modulus (S : Finset ℕ) : ℝ := ∏p∈S,(p:ℝ)
noncomputable def error (S : Finset ℕ) (N p q : ℕ) : ℝ :=
  2*(N:ℝ)*(modulus S*p*q)+(modulus S*p*q)^2+N

lemma joint_discrepancy (a b c : Fin 4 → ℕ) (S : Finset ℕ) (hS : ∀ r∈S, r.Prime)
    (i j : Fin 4) {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p≠q)
    (hpS : p∉S) (hqS : q∉S) (N : ℕ) :
    |((jointCounts a b c S i j N p q).card:ℝ)-
      headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p*
        localDensity (zeros (a j) (b j) (c j)) q*(N:ℝ)^2| ≤ error S N p q := by
  let U := units (fun i => (c i:ℤ)) (fun i => (b i:ℤ)) (fun i => (a i:ℤ))
  let G (r : ℕ) := if r=p then zeros (a i) (b i) (c i) r else
    if r=q then zeros (a j) (b j) (c j) r else U r
  have hpins : p∉insert q S := by simp [hpq,hpS]
  have hrest (x : ℕ × ℕ) :
      (∀ r∈S, ((x.1:ZMod r),(x.2:ZMod r))∈G r) ↔ Head a b c S x := by
    apply forall₂_congr
    intro r hr
    have hrp : r≠p := fun he => hpS (he ▸ hr)
    have hrq : r≠q := fun he => hqS (he ▸ hr)
    simp only [G,if_neg hrp,if_neg hrq]
    rfl
  have hcond (x : ℕ × ℕ) :
      (∀ r∈insert p (insert q S), ((x.1:ZMod r),(x.2:ZMod r))∈G r) ↔
        Head a b c S x ∧ p∣quad (a i) (b i) (c i) x.1 x.2 ∧
          q∣quad (a j) (b j) (c j) x.1 x.2 := by
    rw [forall_mem_insert,forall_mem_insert,hrest]
    simp only [G,if_pos rfl,if_neg hpq.symm,if_true,mem_zeros_nat _ _ _ hp,mem_zeros_nat _ _ _ hq]
    tauto
  have hcount (N : ℕ) : positiveBox N (fun x =>
      ∀ r∈insert p (insert q S), ((x.1:ZMod r),(x.2:ZMod r))∈G r)=jointCounts a b c S i j N p q := by
    ext x
    simp only [positiveBox,jointCounts,mem_filter,hcond]
  have hprod : (∏r∈insert p (insert q S),localDensity G r)=
      headDensity a b c S*localDensity (zeros (a i) (b i) (c i)) p*
        localDensity (zeros (a j) (b j) (c j)) q := by
    rw [prod_insert hpins,prod_insert hqS]
    have hpG : localDensity G p=localDensity (zeros (a i) (b i) (c i)) p := by
      simp only [localDensity,G,if_pos rfl]
    have hqG : localDensity G q=localDensity (zeros (a j) (b j) (c j)) q := by
      simp only [localDensity,G,if_neg hpq.symm,if_true]
    have hSG : (∏r∈S,localDensity G r)=headDensity a b c S := by
      apply prod_congr rfl
      intro r hr
      have hrp : r≠p := fun he => hpS (he ▸ hr)
      have hrq : r≠q := fun he => hqS (he ▸ hr)
      simp only [localDensity,G,if_neg hrp,if_neg hrq,U]
    rw [hpG,hqG,hSG]
    ring
  have hmod : (∏r∈insert p (insert q S),(r:ℝ))=modulus S*p*q := by
    rw [prod_insert hpins,prod_insert hqS]
    dsimp [modulus]
    ring
  have hprime (r : ℕ) (hr : r∈insert p (insert q S)) : r.Prime := by
    rcases mem_insert.mp hr with rfl | hr
    · exact hp
    rcases mem_insert.mp hr with rfl | hr
    · exact hq
    · exact hS r hr
  simpa only [hcount,hprod,hmod,error] using positive_discrepancy _ hprime G N

noncomputable def indicator (a b c p : ℕ) (x : ℕ × ℕ) : ℝ :=
  if p∣quad a b c x.1 x.2 then 1 else 0

lemma sum_indicator_product (a b c : Fin 4 → ℕ) (S : Finset ℕ)
    (i j : Fin 4) (N p q : ℕ) :
    (∑x∈positiveBox N (Head a b c S),
      indicator (a i) (b i) (c i) p x*indicator (a j) (b j) (c j) q x)=
        (jointCounts a b c S i j N p q).card := by
  have he (x : ℕ × ℕ) : indicator (a i) (b i) (c i) p x*indicator (a j) (b j) (c j) q x=
      if p∣quad (a i) (b i) (c i) x.1 x.2 ∧ q∣quad (a j) (b j) (c j) x.1 x.2 then (1:ℝ) else 0 := by
    dsimp only [indicator]
    split_ifs <;> simp_all
  simp_rw [he]
  rw [sum_boole]
  congr 1
  congr 1
  ext x
  simp only [jointCounts,positiveBox,mem_filter]
  tauto

#print axioms joint_discrepancy
end Erdos1206.DualPrimeConditionalCounts
