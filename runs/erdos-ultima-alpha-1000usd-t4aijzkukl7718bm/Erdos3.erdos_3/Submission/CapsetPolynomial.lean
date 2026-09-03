import Submission.CapsetSlice

/-! Polynomial-method cap-set development over the field of three elements.
This is a quantitative tool, not a proof of Erdős 3. -/
namespace Erdos3CapsetPolynomial

open Finset
set_option maxHeartbeats 1000000

abbrev F := ZMod 3
abbrev Vec (n : ℕ) := Fin n → F
abbrev Exps (n : ℕ) := Fin n → Fin 3
abbrev Shape (n : ℕ) := Fin n → Fin 7

def dx : Fin 7 → Fin 3 := ![0,2,0,0,1,1,0]
def dy : Fin 7 → Fin 3 := ![0,0,2,0,1,0,1]
def dz : Fin 7 → Fin 3 := ![0,0,0,2,0,1,1]
def coeff : Fin 7 → F := ![1,-1,-1,-1,1,1,1]

def degree {n : ℕ} (e : Exps n) : ℕ := ∑ i, (e i : ℕ)
def monomial {n : ℕ} (e : Exps n) (x : Vec n) : F := ∏ i, x i ^ (e i : ℕ)
abbrev lowDegree (n : ℕ) := {e : Exps n // degree e ≤ 2*n/3}

def weight {n : ℕ} (s : Shape n) : F := ∏ i, coeff (s i)
def ex {n : ℕ} (s : Shape n) : Exps n := dx ∘ s
def ey {n : ℕ} (s : Shape n) : Exps n := dy ∘ s
def ez {n : ℕ} (s : Shape n) : Exps n := dz ∘ s

lemma coord_expansion (x y z : F) :
    (if x+y+z=0 then (1 : F) else 0) =
      ∑ l : Fin 7, coeff l * x ^ (dx l : ℕ) * y ^ (dy l : ℕ) * z ^ (dz l : ℕ) := by
  have h : ∀ x y z : F, (if x+y+z=0 then (1 : F) else 0) =
      ∑ l : Fin 7, coeff l * x ^ (dx l : ℕ) * y ^ (dy l : ℕ) * z ^ (dz l : ℕ) := by
    decide +kernel
  exact h x y z

lemma degree_sum_bound {n : ℕ} (s : Shape n) :
    degree (ex s) + degree (ey s) + degree (ez s) ≤ 2*n := by
  have h : ∀ l : Fin 7, (dx l : ℕ) + (dy l : ℕ) + (dz l : ℕ) ≤ 2 := by decide
  simp only [degree, ex, ey, ez, Function.comp_apply, ← sum_add_distrib]
  calc
    _ ≤ ∑ i : Fin n, 2 := sum_le_sum (fun i _ ↦ h (s i))
    _ = 2*n := by simp [mul_comm]

lemma one_degree_low {n : ℕ} (s : Shape n) :
    degree (ex s) ≤ 2*n/3 ∨ degree (ey s) ≤ 2*n/3 ∨ degree (ez s) ≤ 2*n/3 := by
  have := degree_sum_bound s
  omega

lemma tensor_expansion {n : ℕ} (x y z : Vec n) :
    (if x+y+z=0 then (1 : F) else 0) =
      ∑ s : Shape n, weight s * monomial (ex s) x * monomial (ey s) y * monomial (ez s) z := by
  have hzero : (∀ i : Fin n, x i + y i + z i = 0) ↔ x+y+z=0 := by
    constructor
    · intro h; ext i; exact h i
    · intro h i; exact congr_fun h i
  calc
    _ = ∏ i : Fin n, (if x i + y i + z i = 0 then (1 : F) else 0) := by
      rw [prod_ite_zero]
      simp only [mem_univ, forall_true_left, prod_const_one, hzero]
    _ = ∏ i : Fin n, ∑ l : Fin 7,
        coeff l * x i ^ (dx l : ℕ) * y i ^ (dy l : ℕ) * z i ^ (dz l : ℕ) := by
      congr 1; funext i; exact coord_expansion _ _ _
    _ = _ := by
      rw [Fintype.prod_sum]
      apply sum_congr rfl
      intro s _
      simp only [prod_mul_distrib, weight, monomial, ex, ey, ez, Function.comp_apply]

lemma group_sum {K E S : Type*} [CommSemiring K] [Fintype E] [DecidableEq E]
    [Fintype S] (r : S → E) (f : E → K) (g : S → K) :
    (∑ s, f (r s) * g s) = ∑ e, f e * ∑ s, if r s=e then g s else 0 := by
  simp_rw [mul_sum, mul_ite, mul_zero]
  rw [sum_comm]
  apply sum_congr rfl
  intro s _
  simp

abbrev SX (n : ℕ) := {s : Shape n // degree (ex s) ≤ 2*n/3}
abbrev Rest (n : ℕ) := {s : Shape n // ¬ degree (ex s) ≤ 2*n/3}
abbrev SY (n : ℕ) := {s : Rest n // degree (ey s.val) ≤ 2*n/3}
abbrev SZ (n : ℕ) := {s : Rest n // ¬ degree (ey s.val) ≤ 2*n/3}

def rx {n : ℕ} (s : SX n) : lowDegree n := ⟨ex s.val, s.property⟩
def ry {n : ℕ} (s : SY n) : lowDegree n := ⟨ey s.val.val, s.property⟩
def rz {n : ℕ} (s : SZ n) : lowDegree n :=
  ⟨ez s.val.val, (one_degree_low s.val.val).resolve_left s.val.property |>.resolve_left s.property⟩

def sliceX {n : ℕ} (e : lowDegree n) (y z : Vec n) : F :=
  ∑ s : SX n, if rx s = e then
    weight s.val * monomial (ey s.val) y * monomial (ez s.val) z else 0

def sliceY {n : ℕ} (e : lowDegree n) (x z : Vec n) : F :=
  ∑ s : SY n, if ry s = e then
    weight s.val.val * monomial (ex s.val.val) x * monomial (ez s.val.val) z else 0

def sliceZ {n : ℕ} (e : lowDegree n) (x y : Vec n) : F :=
  ∑ s : SZ n, if rz s = e then
    weight s.val.val * monomial (ex s.val.val) x * monomial (ey s.val.val) y else 0

lemma tensor_low_degree_slices {n : ℕ} (x y z : Vec n) :
    (if x+y+z=0 then (1 : F) else 0) =
      (∑ e : lowDegree n, monomial e.val x * sliceX e y z) +
      (∑ e : lowDegree n, monomial e.val y * sliceY e x z) +
      (∑ e : lowDegree n, monomial e.val z * sliceZ e x y) := by
  let term (s : Shape n) :=
    weight s * monomial (ex s) x * monomial (ey s) y * monomial (ez s) z
  have hpart : (∑ s : Shape n, term s) =
      (∑ s : SX n, term s.val) + (∑ s : SY n, term s.val.val) +
      (∑ s : SZ n, term s.val.val) := by
    have h1 := Fintype.sum_subtype_add_sum_subtype
      (fun s : Shape n ↦ degree (ex s) ≤ 2*n/3) term
    have h2 := Fintype.sum_subtype_add_sum_subtype
      (fun s : Rest n ↦ degree (ey s.val) ≤ 2*n/3) (fun s ↦ term s.val)
    change (∑ s : SX n, term s.val) + (∑ s : Rest n, term s.val) = _ at h1
    change (∑ s : SY n, term s.val.val) + (∑ s : SZ n, term s.val.val) = _ at h2
    rw [← h1, ← h2, add_assoc]
  rw [tensor_expansion]
  change (∑ s : Shape n, term s) = _
  rw [hpart]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_
  · simp only [sliceX]
    rw [← group_sum rx (fun e : lowDegree n ↦ monomial e.val x)
      (fun s : SX n ↦ weight s.val * monomial (ey s.val) y * monomial (ez s.val) z)]
    apply sum_congr rfl
    intro s _
    dsimp [term, rx]
    ring
  · simp only [sliceY]
    rw [← group_sum ry (fun e : lowDegree n ↦ monomial e.val y)
      (fun s : SY n ↦ weight s.val.val * monomial (ex s.val.val) x * monomial (ez s.val.val) z)]
    apply sum_congr rfl
    intro s _
    dsimp [term, ry]
    ring
  · simp only [sliceZ]
    rw [← group_sum rz (fun e : lowDegree n ↦ monomial e.val z)
      (fun s : SZ n ↦ weight s.val.val * monomial (ex s.val.val) x * monomial (ey s.val.val) y)]
    apply sum_congr rfl
    intro s _
    dsimp [term, rz]
    ring

/-- The basic Ellenberg–Gijswijt monomial-count bound. -/
theorem capset_card_le_monomials {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (v : A → Vec n)
    (h : ∀ a b c, v a + v b + v c = 0 ↔ a = b ∧ b = c) :
    Fintype.card A ≤ 3 * Fintype.card (lowDegree n) := by
  have ht (a b c : A) := tensor_low_degree_slices (v a) (v b) (v c)
  simp only [h] at ht
  have hr := Erdos3CapsetSlice.diagonal_slice_lower_bound
      (I := lowDegree n) (J := lowDegree n) (L := lowDegree n)
      (fun e a ↦ monomial e.val (v a)) (fun e b c ↦ sliceX e (v b) (v c))
      (fun e b ↦ monomial e.val (v b)) (fun e a c ↦ sliceY e (v a) (v c))
      (fun e c ↦ monomial e.val (v c)) (fun e a b ↦ sliceZ e (v a) (v b)) ht
  omega

lemma degree_le {n : ℕ} (e : Exps n) : degree e ≤ 2*n := by
  calc
    degree e ≤ ∑ _ : Fin n, 2 := sum_le_sum (fun i _ ↦ by have := (e i).isLt; omega)
    _ = 2*n := by simp [mul_comm]

lemma sum_exp_weights (n : ℕ) :
    (∑ e : Exps n, 2 ^ (2*n-degree e)) = 7^n := by
  have he (e : Exps n) : (∏ i : Fin n, 2 ^ (2-(e i : ℕ))) = 2^(2*n-degree e) := by
    rw [prod_pow_eq_pow_sum]
    congr 1
    have hh : (∑ i : Fin n, (2 - (e i : ℕ))) + degree e = 2*n := by
      rw [degree, ← sum_add_distrib]
      calc
        _ = ∑ _ : Fin n, 2 := by
          apply sum_congr rfl
          intro i _
          have := (e i).isLt
          omega
        _ = 2*n := by simp [mul_comm]
    omega
  calc
    _ = ∑ e : Exps n, ∏ i : Fin n, 2^(2-(e i : ℕ)) := by simp only [he]
    _ = ∏ _ : Fin n, ∑ a : Fin 3, 2^(2-(a : ℕ)) := (Fintype.prod_sum (fun (_ : Fin n) (a : Fin 3) ↦ (2 : ℕ)^(2-(a : ℕ)))).symm
    _ = 7^n := by norm_num [Fin.sum_univ_succ]

lemma monomial_count_weighted (n : ℕ) :
    Fintype.card (lowDegree n) * 2^(2*n-2*n/3) ≤ 7^n := by
  calc
    _ = ∑ _ : lowDegree n, 2^(2*n-2*n/3) := by simp
    _ ≤ ∑ e : lowDegree n, 2^(2*n-degree e.val) := by
      apply sum_le_sum
      intro e _
      exact Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left e.property _)
    _ ≤ ∑ e : Exps n, 2^(2*n-degree e) := by
      have h := Fintype.sum_subtype_add_sum_subtype
        (fun e : Exps n ↦ degree e ≤ 2*n/3) (fun e ↦ 2^(2*n-degree e))
      exact (Nat.le_add_right _ _).trans_eq h
    _ = 7^n := sum_exp_weights n

/-- A convenient integral power-saving form of the cap-set bound. -/
theorem capset_card_power_bound {n : ℕ} {A : Type*} [Fintype A] [DecidableEq A]
    (v : A → Vec n)
    (h : ∀ a b c, v a + v b + v c = 0 ↔ a = b ∧ b = c) :
    (Fintype.card A)^15 ≤ 27^5 * (3^n)^14 := by
  have hmon := capset_card_le_monomials v h
  have hw := monomial_count_weighted n
  have hbase : Fintype.card A * 2^(2*n-2*n/3) ≤ 3 * 7^n := by
    calc
      _ ≤ (3 * Fintype.card (lowDegree n)) * 2^(2*n-2*n/3) := Nat.mul_le_mul_right _ hmon
      _ ≤ 3 * 7^n := by nlinarith
  have hcubed : (Fintype.card A)^3 * 16^n ≤ 27 * 343^n := by
    have hh := Nat.pow_le_pow_left hbase 3
    have hexp : 4*n ≤ (2*n-2*n/3)*3 := by omega
    have hp : (16 : ℕ)^n ≤ (2^(2*n-2*n/3))^3 := by
      calc
        (16 : ℕ)^n = 2^(4*n) := by rw [pow_mul]; rfl
        _ ≤ 2^((2*n-2*n/3)*3) := Nat.pow_le_pow_right (by decide) hexp
        _ = _ := pow_mul ..
    calc
      _ ≤ (Fintype.card A)^3 * (2^(2*n-2*n/3))^3 := Nat.mul_le_mul_left _ hp
      _ ≤ (3 * 7^n)^3 := by simpa only [mul_pow] using hh
      _ = 27 * 343^n := by rw [mul_pow, ← pow_mul, Nat.mul_comm n 3, pow_mul]; norm_num
  have hconst : (343 : ℕ)^5 ≤ 16^5 * 3^14 := by norm_num
  have hpow : (343^n : ℕ)^5 ≤ (16^n)^5 * (3^n)^14 := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm n 5, Nat.mul_comm n 14] using
      Nat.pow_le_pow_left hconst n
  apply Nat.le_of_mul_le_mul_right (c := (16^n)^5) _ (by positivity)
  calc
    (Fintype.card A)^15 * (16^n)^5 = ((Fintype.card A)^3 * 16^n)^5 := by
      simp only [mul_pow, ← pow_mul]
    _ ≤ (27 * 343^n)^5 := Nat.pow_le_pow_left hcubed 5
    _ = 27^5 * (343^n)^5 := by rw [mul_pow]
    _ ≤ 27^5 * ((16^n)^5 * (3^n)^14) := Nat.mul_le_mul_left _ hpow
    _ = (27^5 * (3^n)^14) * (16^n)^5 := by ring

lemma triple_self {n : ℕ} (x : Vec n) : x+x+x=0 := by
  ext i
  change x i + x i + x i = 0
  calc
    _ = (3 : F) * x i := by ring
    _ = 0 := by rw [show (3 : F) = 0 from rfl, zero_mul]

lemma capset_zero_iff {n : ℕ} {S : Finset (Vec n)}
    (hS : ThreeAPFree (S : Set (Vec n))) (a b c : S) :
    (a : Vec n) + b + c = 0 ↔ a=b ∧ b=c := by
  constructor
  · intro he
    have he' : (a : Vec n) + c = b+b := by
      apply add_right_cancel (b := (b : Vec n))
      calc
        ((a : Vec n)+c)+b = (a : Vec n)+b+c := by abel
        _ = 0 := he
        _ = ((b : Vec n)+b)+b := (triple_self _).symm
    have hab := hS a.property b.property c.property he'
    have hbc : (b : Vec n) = c := by
      rw [hab] at he'
      exact (add_left_cancel he').symm
    exact ⟨Subtype.ext hab, Subtype.ext hbc⟩
  · rintro ⟨rfl, rfl⟩
    exact triple_self _

theorem threeAPFree_card_power_bound {n : ℕ} (S : Finset (Vec n))
    (hS : ThreeAPFree (S : Set (Vec n))) :
    S.card^15 ≤ 27^5 * (3^n)^14 := by
  simpa using capset_card_power_bound (fun a : S ↦ (a : Vec n)) (capset_zero_iff hS)

#print axioms tensor_expansion
#print axioms capset_card_le_monomials
#print axioms capset_card_power_bound
#print axioms threeAPFree_card_power_bound
end Erdos3CapsetPolynomial
