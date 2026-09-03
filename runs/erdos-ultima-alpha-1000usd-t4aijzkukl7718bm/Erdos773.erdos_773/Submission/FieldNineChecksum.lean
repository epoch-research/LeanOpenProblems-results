import FormalConjecturesUtil

/-! An exact finite obstruction for the field-arithmetic version of the
cubic norm checksum at F_9. This does not concern arbitrary Sidon sets. -/
namespace Erdos773.FieldNineChecksum
open Polynomial Finset
set_option maxHeartbeats 2000000
noncomputable section
local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def modulus : (ZMod 3)[X] := X^2+1

lemma modulus_irreducible : Irreducible modulus := by
  have hd : modulus.natDegree=2 := by unfold modulus; compute_degree; norm_num
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide)
  have hh : ∀ x : ZMod 3, x^2+1 ≠ 0 := by decide +kernel
  intro x
  simpa only [modulus,IsRoot,eval_add,eval_pow,eval_X,eval_one] using hh x

local instance : Fact (Irreducible modulus) := ⟨modulus_irreducible⟩
abbrev K := AdjoinRoot modulus
local instance : Module.Finite (ZMod 3) K :=
  (AdjoinRoot.powerBasis modulus_irreducible.ne_zero).finite
local instance : Finite K := Module.finite_of_finite (ZMod 3)
local instance : Fintype K := Fintype.ofFinite K
local instance : CharP K 3 :=
  charP_of_injective_algebraMap (algebraMap (ZMod 3) K).injective 3

lemma field_card : Nat.card K=9 := by
  have hd : modulus.natDegree=2 := by unfold modulus; compute_degree; norm_num
  rw [Module.natCard_eq_pow_finrank (K:=ZMod 3),Nat.card_zmod,
    (AdjoinRoot.powerBasis modulus_irreducible.ne_zero).finrank,
    AdjoinRoot.powerBasis_dim,hd]
  norm_num


def theta : K := AdjoinRoot.root modulus

lemma theta_sq : theta^2 = -1 := by
  have hh : theta^2+(1:K)=0 := by
    have h := AdjoinRoot.eval₂_root modulus
    change (X^2+1 : (ZMod 3)[X]).eval₂ (AdjoinRoot.of modulus) theta=0 at h
    simpa only [eval₂_add,eval₂_pow,eval₂_X,eval₂_one] using h
  linear_combination hh

lemma three_zero : (3:K)=0 := by
  have hh : (3:ZMod 3)=0 := by decide +kernel
  have he := congrArg (algebraMap (ZMod 3) K) hh
  simpa only [map_ofNat,map_zero] using he

/-- The cubic defining the norm remains irreducible over this genuine
nine-element field. -/
lemma cubic_irreducible : Irreducible (X^3-X-1 : K[X]) := by
  have hd : (X^3-X-1 : K[X]).natDegree=3 := by compute_degree; norm_num
  apply irreducible_of_degree_le_three_of_not_isRoot (by rw [hd]; decide)
  intro x
  simp only [IsRoot,eval_sub,eval_pow,eval_X,eval_one]
  intro hx
  have hx3 : x^3=x+1 := by linear_combination hx
  have hx9 : x^9=x := by
    have hh := FiniteField.pow_card x
    simpa only [← Nat.card_eq_fintype_card,field_card] using hh
  have he := congrArg (fun y : K => y^3) hx3
  dsimp only at he
  rw [← pow_mul,show 3*3=9 from rfl,hx9,add_pow_char,one_pow,hx3] at he
  have htwo : (2:K)=0 := by linear_combination -he
  have hone : (1:K)=0 := by linear_combination three_zero-htwo
  exact one_ne_zero hone

/-- The base-three coordinate encoding, in the basis 1,theta. -/
def encode (n : ℕ) : K := (n%3 : ℕ)+(n/3 : ℕ)*theta

def cubicNorm (x y z : K) : K :=
  x^3+2*x^2*z-x*y^2-3*x*y*z+x*z^2+y^3-y*z^2+z^3

def checksum (a b c : K) : K :=
  cubicNorm (a+2+2*c) c (b+c)+2*a+2

/-- This defines the entire finite digit family without relying on a
numerical representation algorithm for the quotient field. -/
def roots : Set ℕ := {n | ∃ a b c d : ℕ,
  a<9 ∧ b<9 ∧ c<9 ∧ d<9 ∧
  encode d=checksum (encode a) (encode b) (encode c) ∧
  n=a+9*b+81*c+729*d}

lemma checksum_certificates :
    encode 3=checksum (encode 6) (encode 6) (encode 0) ∧
    encode 1=checksum (encode 0) (encode 5) (encode 0) ∧
    encode 3=checksum (encode 3) (encode 8) (encode 0) ∧
    encode 1=checksum (encode 0) (encode 0) (encode 0) := by
  have h3 : theta^3 = -theta := by
    calc theta^3 = theta*theta^2 := by ring
         _ = -theta := by rw [theta_sq]; ring
  norm_num [encode,checksum,cubicNorm]
  constructor
  · linear_combination -40*h3-64*theta_sq+three_zero*(18-theta)
  constructor
  · linear_combination -h3-8*theta_sq+three_zero*(-9*theta-11)
  constructor
  · linear_combination -17*h3-66*theta_sq+three_zero*(8-24*theta)
  · linear_combination -3*three_zero

lemma roots_members : 2247∈roots ∧ 774∈roots ∧ 2262∈roots ∧ 729∈roots := by
  refine ⟨?_,?_,?_,?_⟩
  · exact ⟨6,6,0,3,by decide,by decide,by decide,by decide,
      checksum_certificates.1,by norm_num⟩
  · exact ⟨0,5,0,1,by decide,by decide,by decide,by decide,
      checksum_certificates.2.1,by norm_num⟩
  · exact ⟨3,8,0,3,by decide,by decide,by decide,by decide,
      checksum_certificates.2.2.1,by norm_num⟩
  · exact ⟨0,0,0,1,by decide,by decide,by decide,by decide,
      checksum_certificates.2.2.2,by norm_num⟩

/-- The field-arithmetic checksum fails too; this statement uses the
actual irreducible quadratic extension of ZMod 3, not ZMod 9. -/
theorem squares_not_sidon : ¬IsSidon ((fun n : ℕ => n^2) '' roots) := by
  intro hs
  have hm {n : ℕ} (hn : n∈roots) : n^2∈((fun n : ℕ => n^2) '' roots) :=
    ⟨n,hn,rfl⟩
  have he := hs (2247^2) (hm roots_members.1)
    (2262^2) (hm roots_members.2.2.1)
    (774^2) (hm roots_members.2.1)
    (729^2) (hm roots_members.2.2.2) (by norm_num)
  norm_num at he

#print axioms field_card
#print axioms cubic_irreducible
#print axioms modulus_irreducible
#print axioms checksum_certificates
#print axioms squares_not_sidon
end
end Erdos773.FieldNineChecksum
