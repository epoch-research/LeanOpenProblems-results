import Submission.InertPrimeCollision

/-!
A counterexample to a pairwise-Jacobi-symbol spin candidate. This does not
rule out arbitrary colorings or settle the positive-density conjecture.
-/
namespace Erdos1206.JacobiSpinObstruction
open Finset

/-- Multiply one Jacobi symbol for each increasingly ordered pair of distinct
prime factors. On an odd squarefree integer all factors are signs. -/
noncomputable def spin (n : ℕ) : ℤ :=
  ∏ p ∈ n.primeFactors, ∏ q ∈ n.primeFactors,
    if p < q then jacobiSym (p : ℤ) q else 1

def source (s : ℤ) : Set ℕ := {n | Odd n ∧ Squarefree n ∧ spin n = s}

lemma spin_prime {p : ℕ} (hp : p.Prime) : spin p = 1 := by
  simp [spin,hp.primeFactors]

lemma spin_three {p : ℕ} (hp : p.Prime) (hbig : 557 < p) :
    spin (13*557*p) = jacobiSym 13 557 * jacobiSym 13 p * jacobiSym 557 p := by
  have h13 : Nat.Prime 13 := by norm_num
  have h557 : Nat.Prime 557 := by norm_num
  have hfac : (13*557*p).primeFactors = {13,557,p} := by
    rw [Nat.primeFactors_mul (by norm_num) hp.ne_zero,
      Nat.primeFactors_mul (by norm_num) (by norm_num),
      h13.primeFactors,h557.primeFactors,hp.primeFactors]
    ext x
    simp only [mem_union,mem_singleton,mem_insert,or_assoc]
  have hp13 : 13 < p := by omega
  simp [spin,hfac,show 13≠p by omega,show 557≠p by omega,
    hp13,hbig,show ¬p<13 by omega,show ¬p<557 by omega]

lemma symbol_certificate :
    jacobiSym 13 557 = -1 ∧
    jacobiSym 13 26711 = 1 ∧ jacobiSym 557 26711 = 1 ∧
    jacobiSym 13 31469 = 1 ∧ jacobiSym 557 31469 = 1 ∧
    jacobiSym 13 32009 = 1 ∧ jacobiSym 557 32009 = 1 ∧
    jacobiSym 13 35543 = 1 ∧ jacobiSym 557 35543 = 1 := by
  norm_num

lemma positive_membership :
    26711 ∈ source 1 ∧ 31469 ∈ source 1 ∧
    32009 ∈ source 1 ∧ 35543 ∈ source 1 := by
  obtain ⟨h1,h2,h3,h4,_⟩ := four_inert_prime_collision
  exact ⟨⟨by norm_num,h1.squarefree,spin_prime h1⟩,
    ⟨by norm_num,h2.squarefree,spin_prime h2⟩,
    ⟨by norm_num,h3.squarefree,spin_prime h3⟩,
    ⟨by norm_num,h4.squarefree,spin_prime h4⟩⟩

lemma negative_membership :
    193414351 ∈ source (-1) ∧ 227867029 ∈ source (-1) ∧
    231777169 ∈ source (-1) ∧ 257366863 ∈ source (-1) := by
  obtain ⟨h1,h2,h3,h4,_⟩ := four_inert_prime_collision
  have hm : Squarefree (13*557 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime 13 557)).mpr
      ⟨(by norm_num : Nat.Prime 13).squarefree,(by norm_num : Nat.Prime 557).squarefree⟩
  have hs1 : Squarefree (13*557*26711 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime (13*557) 26711)).mpr ⟨hm,h1.squarefree⟩
  have hs2 : Squarefree (13*557*31469 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime (13*557) 31469)).mpr ⟨hm,h2.squarefree⟩
  have hs3 : Squarefree (13*557*32009 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime (13*557) 32009)).mpr ⟨hm,h3.squarefree⟩
  have hs4 : Squarefree (13*557*35543 : ℕ) :=
    (Nat.squarefree_mul (by norm_num : Nat.Coprime (13*557) 35543)).mpr ⟨hm,h4.squarefree⟩
  have hc1 : spin (13*557*26711) = -1 := by
    rw [spin_three h1 (by norm_num)]
    norm_num
  have hc2 : spin (13*557*31469) = -1 := by
    rw [spin_three h2 (by norm_num)]
    norm_num
  have hc3 : spin (13*557*32009) = -1 := by
    rw [spin_three h3 (by norm_num)]
    norm_num
  have hc4 : spin (13*557*35543) = -1 := by
    rw [spin_three h4 (by norm_num)]
    norm_num
  exact ⟨⟨by norm_num,hs1,hc1⟩,⟨by norm_num,hs2,hc2⟩,
    ⟨by norm_num,hs3,hc3⟩,⟨by norm_num,hs4,hc4⟩⟩

/-- Both sign fibers contain strict squarefree odd-root cube collisions. -/
theorem neither_fiber_sidon :
    ¬ IsSidon ((fun n : ℕ => n^3) '' source 1) ∧
    ¬ IsSidon ((fun n : ℕ => n^3) '' source (-1)) := by
  constructor
  · intro hs
    obtain ⟨h1,h2,h3,h4⟩ := positive_membership
    have hh := hs _ ⟨26711,h1,rfl⟩ _ ⟨31469,h2,rfl⟩
      _ ⟨35543,h4,rfl⟩ _ ⟨32009,h3,rfl⟩
      (by norm_num : (26711 : ℕ)^3+35543^3=31469^3+32009^3)
    norm_num at hh
  · intro hs
    obtain ⟨h1,h2,h3,h4⟩ := negative_membership
    have hh := hs _ ⟨193414351,h1,rfl⟩ _ ⟨227867029,h2,rfl⟩
      _ ⟨257366863,h4,rfl⟩ _ ⟨231777169,h3,rfl⟩
      (by norm_num : (193414351 : ℕ)^3+257366863^3=227867029^3+231777169^3)
    norm_num at hh

#print axioms neither_fiber_sidon
end Erdos1206.JacobiSpinObstruction
