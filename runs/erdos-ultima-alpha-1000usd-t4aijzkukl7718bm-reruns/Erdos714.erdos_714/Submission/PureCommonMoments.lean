import Submission.PolynomialExceptionalDensity
import Submission.PowerQuadraticRoots

/-!
Restrictions on the special all-root model giving only zero or three
common neighbors. These results have explicit degree/codegree hypotheses;
they do not apply to arbitrary K44-free graphs or settle Erdős714.
-/
noncomputable section
open Classical Finset SimpleGraph
set_option maxHeartbeats 3000000
namespace Erdos714PureCommonMoments
open Erdos714Packing Erdos714TripleCommonDensity
variable {A B : Type*} [Fintype A] [Fintype B]

lemma star_count (S : A → Finset B) (r : ℕ) :
    (∑ b, (dual S b).card.descFactorial r) =
      ∑ f : Fin r ↪ A, (common S f).card := by
  have h := Fintype.card_congr (Erdos714Unbalanced.starEquiv (dual S) r)
  have hd : dual (dual S) = S := by
    funext a
    ext b
    simp only [mem_dual]
  simpa only [Fintype.card_sigma, Fintype.card_embedding_eq, Fintype.card_fin,
    Fintype.card_coe, hd] using h

/-- Count the same ordered K_(r,2) from both sides when all r-fold
common-neighbor counts are zero or k. -/
theorem pure_moment_identity (S : A → Finset B) (r k : ℕ)
    (hpure : ∀ f : Fin r ↪ A, (common S f).card=0 ∨ (common S f).card=k) :
    (∑ g : Fin 2 ↪ B, (common (dual S) g).card.descFactorial r) =
      (k-1) * ∑ b, (dual S b).card.descFactorial r := by
  rw [← rectangle_count S r 2, star_count S r, mul_sum]
  apply sum_congr rfl
  intro f _
  rcases hpure f with h | h <;> rw [h]
  · simp
  · simp only [Nat.descFactorial_succ, Nat.descFactorial_zero, Nat.sub_zero]
    ring

/-- The pure common-count condition forces a moment gap between column
degrees and pair codegrees. No freeness or regularity is silently assumed. -/
theorem degree_pair_budget (S : A → Finset B) (r k d t : ℕ)
    (hB : 0 < Fintype.card B)
    (hpure : ∀ f : Fin r ↪ A, (common S f).card=0 ∨ (common S f).card=k)
    (hd : ∀ b, d ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B, (common (dual S) g).card ≤ t) :
    (k-1)*d.descFactorial r ≤ (Fintype.card B-1)*t.descFactorial r := by
  have h := pure_moment_identity S r k hpure
  have hlo : Fintype.card B*d.descFactorial r ≤
      ∑ b, (dual S b).card.descFactorial r := by
    calc
      _ = ∑ _b : B, d.descFactorial r := by simp
      _ ≤ _ := sum_le_sum (fun b _ => Nat.descFactorial_le r (hd b))
  have hhi : (∑ g : Fin 2 ↪ B, (common (dual S) g).card.descFactorial r) ≤
      Fintype.card B*(Fintype.card B-1)*t.descFactorial r := by
    calc
      _ ≤ ∑ _g : Fin 2 ↪ B, t.descFactorial r :=
        sum_le_sum (fun g _ => Nat.descFactorial_le r (ht g))
      _ = _ := by
        simp only [sum_const, card_univ, Fintype.card_embedding_eq,
          Fintype.card_fin, Nat.descFactorial_succ, Nat.descFactorial_zero,
          Nat.sub_zero, mul_one, smul_eq_mul]
        ring
  have hc : Fintype.card B*((k-1)*d.descFactorial r) ≤
      Fintype.card B*((Fintype.card B-1)*t.descFactorial r) := by
    calc
      _ = (k-1)*(Fintype.card B*d.descFactorial r) := by ring
      _ ≤ (k-1)*∑ b, (dual S b).card.descFactorial r := Nat.mul_le_mul_left _ hlo
      _ = _ := h.symm
      _ ≤ _ := hhi
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hc hB

/-- A pure zero-or-three model cannot have near-q^3 column degrees and
near-q^2 pair codegrees on at most q^4 columns, once q is at least 16.
These strong regularity hypotheses are essential to the conclusion. -/
theorem zero_or_three_not_regular (S : A → Finset B) (q : ℕ) (hq : 16 ≤ q)
    (hB0 : 0 < Fintype.card B) (hB : Fintype.card B ≤ q^4)
    (hd : ∀ b, q^3-q^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B, (common (dual S) g).card ≤ q^2+q)
    (hpure : ∀ f : Fin 4 ↪ A, (common S f).card=0 ∨ (common S f).card=3) :
    False := by
  have hb := degree_pair_budget S 4 3 (q^3-q^2) (q^2+q) hB0 hpure hd ht
  norm_num only at hb
  have hp : (q^3-q^2-3)^4 ≤ (q^3-q^2).descFactorial 4 := by
    convert Nat.pow_sub_le_descFactorial (q^3-q^2) 4 using 1
  have hmain : 2*(q^3-q^2-3)^4 ≤ q^4*(q^2+q)^4 := by
    calc
      _ ≤ 2*(q^3-q^2).descFactorial 4 := Nat.mul_le_mul_left _ hp
      _ ≤ (Fintype.card B-1)*(q^2+q).descFactorial 4 := hb
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.descFactorial_le_pow _ _)
  have hq2 : 256 ≤ q^2 := by nlinarith
  have hq3 : 15*q^2+45 ≤ q^3 := by
    nlinarith [Nat.mul_le_mul_right (q^2) hq]
  have hdl : 14*q^3 ≤ 15*(q^3-q^2-3) := by omega
  have htl : 15*(q^2+q) ≤ 16*q^2 := by nlinarith
  have hh : 2*(14*q^3)^4 ≤ q^4*(16*q^2)^4 := by
    calc
      _ ≤ 2*(15*(q^3-q^2-3))^4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdl 4)
      _ = 15^4*(2*(q^3-q^2-3)^4) := by ring
      _ ≤ 15^4*(q^4*(q^2+q)^4) := Nat.mul_le_mul_left _ hmain
      _ = q^4*(15*(q^2+q))^4 := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htl 4)
  have hq0 : 0 < q := by omega
  have hpos : 0 < q^12 := by positivity
  ring_nf at hh
  omega

/-- Consequently a K44-free system satisfying these regularity bounds
must have a quadruple with exactly one or exactly two common neighbors. -/
theorem exists_one_or_two (S : A → Finset B) (q : ℕ) (hq : 16 ≤ q)
    (hB0 : 0 < Fintype.card B) (hB : Fintype.card B ≤ q^4)
    (hd : ∀ b, q^3-q^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B, (common (dual S) g).card ≤ q^2+q)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    ∃ f : Fin 4 ↪ A, (common S f).card=1 ∨ (common S f).card=2 := by
  by_contra! hn
  apply zero_or_three_not_regular S q hq hB0 hB hd ht
  intro f
  have hb := (free_iff_common_card S (by decide : 0 < 4)).mp hfree f
  have h := hn f
  omega

/-- Ordered quadruples with the intermediate common-neighbor counts. -/
def intermediateCommon (S : A → Finset B) : Finset (Fin 4 ↪ A) :=
  univ.filter (fun f => (common S f).card=1 ∨ (common S f).card=2)

/-- The exact defect from the zero-or-three moment identity counts the
quadruples having one or two common neighbors. -/
lemma intermediate_moment_identity (S : A → Finset B)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    2*(∑ b, (dual S b).card.descFactorial 4) =
      (∑ g : Fin 2 ↪ B, (common (dual S) g).card.descFactorial 4) +
        2*(intermediateCommon S).card := by
  have hterm (f : Fin 4 ↪ A) : 2*(common S f).card =
      (common S f).card.descFactorial 2 +
        2*(if (common S f).card=1 ∨ (common S f).card=2 then 1 else 0) := by
    have hb := (free_iff_common_card S (by decide : 0 < 4)).mp hfree f
    interval_cases hc : (common S f).card <;> norm_num
  rw [star_count S 4, ← rectangle_count S 4 2, mul_sum]
  simp_rw [hterm]
  rw [sum_add_distrib, ← mul_sum]
  simp [sum_boole, intermediateCommon]

/-- A positive-density number of intermediate-count tuples is forced by
the near-full column-degree and pair-codegree bounds. -/
theorem intermediate_density (S : A → Finset B) (q : ℕ) (hq : 16 ≤ q)
    (hB : Fintype.card B ≤ q^4)
    (hd : ∀ b, q^3-q^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B, (common (dual S) g).card ≤ q^2+q)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    Fintype.card B*q^12 ≤ 10*(intermediateCommon S).card := by
  let Z := (intermediateCommon S).card
  have hlo : Fintype.card B*(q^3-q^2-3)^4 ≤
      ∑ b, (dual S b).card.descFactorial 4 := by
    calc
      _ = ∑ _b : B, (q^3-q^2-3)^4 := by simp
      _ ≤ _ := sum_le_sum (fun b _ => by
        calc
          _ ≤ (q^3-q^2).descFactorial 4 := by
            convert Nat.pow_sub_le_descFactorial (q^3-q^2) 4 using 1
          _ ≤ _ := Nat.descFactorial_le 4 (hd b))
  have hhi : (∑ g : Fin 2 ↪ B, (common (dual S) g).card.descFactorial 4) ≤
      Fintype.card B*q^4*(q^2+q)^4 := by
    calc
      _ ≤ ∑ _g : Fin 2 ↪ B, (q^2+q)^4 := sum_le_sum (fun g _ =>
        (Nat.descFactorial_le_pow _ _).trans (Nat.pow_le_pow_left (ht g) 4))
      _ = Fintype.card B*(Fintype.card B-1)*(q^2+q)^4 := by
        simp only [sum_const, card_univ, Fintype.card_embedding_eq,
          Fintype.card_fin, Nat.descFactorial_succ, Nat.descFactorial_zero,
          Nat.sub_zero, mul_one, smul_eq_mul]
        ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have hmain : 2*(Fintype.card B*(q^3-q^2-3)^4) ≤
      Fintype.card B*q^4*(q^2+q)^4 + 2*Z := by
    calc
      _ ≤ 2*(∑ b, (dual S b).card.descFactorial 4) := Nat.mul_le_mul_left _ hlo
      _ = _ := intermediate_moment_identity S hfree
      _ ≤ _ := Nat.add_le_add_right hhi _
  have hq2 : 256 ≤ q^2 := by nlinarith
  have hq3 : 15*q^2+45 ≤ q^3 := by
    nlinarith [Nat.mul_le_mul_right (q^2) hq]
  have hdl : 14*q^3 ≤ 15*(q^3-q^2-3) := by omega
  have htl : 15*(q^2+q) ≤ 16*q^2 := by nlinarith
  have hh : 2*Fintype.card B*(14*q^3)^4 ≤
      Fintype.card B*q^4*(16*q^2)^4 + 2*15^4*Z := by
    calc
      _ ≤ 2*Fintype.card B*(15*(q^3-q^2-3))^4 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hdl 4)
      _ = 15^4*(2*(Fintype.card B*(q^3-q^2-3)^4)) := by ring
      _ ≤ 15^4*(Fintype.card B*q^4*(q^2+q)^4+2*Z) := Nat.mul_le_mul_left _ hmain
      _ = Fintype.card B*q^4*(15*(q^2+q))^4+2*15^4*Z := by ring
      _ ≤ _ := Nat.add_le_add_right
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htl 4)) _
  dsimp [Z] at hh
  nlinarith only [hh, Nat.zero_le (intermediateCommon S).card]

/-- With a positive proportion of the q^4 columns, this yields a positive
proportion of all q^16 ordered quadruples. -/
theorem scaled_intermediate_density (S : A → Finset B) (q D : ℕ) (hq : 16 ≤ q)
    (hB : Fintype.card B ≤ q^4) (hBlo : q^4 ≤ D*Fintype.card B)
    (hd : ∀ b, q^3-q^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B, (common (dual S) g).card ≤ q^2+q)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S)) :
    q^16 ≤ 10*D*(intermediateCommon S).card := by
  have h := intermediate_density S q hq hB hd ht hfree
  calc
    _ = q^4*q^12 := by ring
    _ ≤ (D*Fintype.card B)*q^12 := Nat.mul_le_mul_right _ hBlo
    _ = D*(Fintype.card B*q^12) := by ring
    _ ≤ D*(10*(intermediateCommon S).card) := Nat.mul_le_mul_left _ h
    _ = _ := by ring

variable {F : Type*} [Field F] [Fintype F]

/-- The sparse sextic ingredient cannot supply an exact all-root model
with the preceding regularity bounds. This does not forbid other root
models or graphs with nonuniform pair codegrees. -/
theorem sparse_sextic_not_regular (S : A → Finset B) (q : ℕ) (hq : 16 ≤ q)
    (hB0 : 0 < Fintype.card B) (hB : Fintype.card B ≤ q^4)
    (hd : ∀ b, q^3-q^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B, (common (dual S) g).card ≤ q^2+q)
    (a b : (Fin 4 ↪ A) → F) (ζ : F) (hζ : IsPrimitiveRoot ζ 3)
    (hb : ∀ f, ¬ ∃ z : F, z^3=b f)
    (hmodel : ∀ f, (common S f).card =
      (Erdos714PowerQuadraticRoots.solutions 3 (a f) (b f)).card) :
    False := by
  apply zero_or_three_not_regular S q hq hB0 hB hd ht
  intro f
  rw [hmodel f]
  exact Erdos714PowerQuadraticRoots.solution_card_zero_or_k
    3 (by decide) (a f) (b f) ζ (hb f) hζ

open Erdos714PolynomialExceptionalDensity

/-- Intermediate-count tuples cannot all lie on one bounded-degree
hypersurface under the stated near-full degree and codegree conditions. -/
theorem intermediate_polynomial_budget (S : A → Finset B) (D : ℕ)
    (hq : 16 ≤ Fintype.card F)
    (hB : Fintype.card B ≤ Fintype.card F^4)
    (hBlo : Fintype.card F^4 ≤ D*Fintype.card B)
    (hd : ∀ b, Fintype.card F^3-Fintype.card F^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B,
      (common (dual S) g).card ≤ Fintype.card F^2+Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (e : A ↪ (Fin 4 → F)) (P : MvPolynomial (Fin 16) F) (hP : P ≠ 0)
    (hvanish : ∀ f ∈ intermediateCommon S,
      MvPolynomial.eval (squareTupleEncoding 4 e f) P = 0) :
    Fintype.card F ≤ 10*D*P.totalDegree := by
  have hsub : intermediateCommon S ⊆
      univ.filter (fun f => MvPolynomial.eval (squareTupleEncoding 4 e f) P = 0) := by
    intro f hf
    exact mem_filter.mpr ⟨mem_univ _, hvanish f hf⟩
  have hZ : (intermediateCommon S).card ≤ P.totalDegree*Fintype.card F^15 :=
    (card_le_card hsub).trans (encoded_zero_card 16 (by decide) (squareTupleEncoding 4 e) P hP)
  have h := scaled_intermediate_density S (Fintype.card F) D hq hB hBlo hd ht hfree
  have hh : Fintype.card F^15*Fintype.card F ≤
      Fintype.card F^15*(10*D*P.totalDegree) := by
    calc
      _ = Fintype.card F^16 := by ring
      _ ≤ 10*D*(intermediateCommon S).card := h
      _ ≤ 10*D*(P.totalDegree*Fintype.card F^15) := Nat.mul_le_mul_left _ hZ
      _ = _ := by ring
  exact Nat.le_of_mul_le_mul_left hh (by positivity)

/-- Sparse sextic all-root models remain excluded if their failures occur
only on a bounded-degree proper hypersurface. This is conditional on the
explicit near-full degree and pair-codegree bounds. -/
theorem sparse_sextic_polynomial_budget (S : A → Finset B) (D : ℕ)
    (hq : 16 ≤ Fintype.card F)
    (hB : Fintype.card B ≤ Fintype.card F^4)
    (hBlo : Fintype.card F^4 ≤ D*Fintype.card B)
    (hd : ∀ b, Fintype.card F^3-Fintype.card F^2 ≤ (dual S b).card)
    (ht : ∀ g : Fin 2 ↪ B,
      (common (dual S) g).card ≤ Fintype.card F^2+Fintype.card F)
    (hfree : (completeBipartiteGraph (Fin 4) (Fin 4)).Free (incidence S))
    (e : A ↪ (Fin 4 → F)) (P : MvPolynomial (Fin 16) F) (hP : P ≠ 0)
    (a b : (Fin 4 ↪ A) → F) (ζ : F) (hζ : IsPrimitiveRoot ζ 3)
    (hmodel : ∀ f, MvPolynomial.eval (squareTupleEncoding 4 e f) P ≠ 0 →
      (¬ ∃ z : F, z^3=b f) ∧ (common S f).card =
        (Erdos714PowerQuadraticRoots.solutions 3 (a f) (b f)).card) :
    Fintype.card F ≤ 10*D*P.totalDegree := by
  apply intermediate_polynomial_budget S D hq hB hBlo hd ht hfree e P hP
  intro f hf
  by_contra hn
  obtain ⟨hb, hc⟩ := hmodel f hn
  have h03 := Erdos714PowerQuadraticRoots.solution_card_zero_or_k
    3 (by decide) (a f) (b f) ζ hb hζ
  have h12 := (mem_filter.mp hf).2
  omega

#print axioms intermediate_moment_identity
#print axioms intermediate_density
#print axioms scaled_intermediate_density
#print axioms intermediate_polynomial_budget
#print axioms sparse_sextic_polynomial_budget
#print axioms zero_or_three_not_regular
#print axioms exists_one_or_two
#print axioms sparse_sextic_not_regular
#print axioms pure_moment_identity
#print axioms degree_pair_budget
end Erdos714PureCommonMoments
