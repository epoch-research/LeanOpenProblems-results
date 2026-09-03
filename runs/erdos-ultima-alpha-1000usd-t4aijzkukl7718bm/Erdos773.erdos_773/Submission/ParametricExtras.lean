import FormalConjecturesUtil

/-!
An auxiliary test of a digit construction, not a settlement of Erdős 773.
The definitions below track rational rotations through affine digit words.
-/
namespace Erdos773.ParametricSphere

set_option maxHeartbeats 10000000
set_option maxRecDepth 100000
set_option Elab.async false

structure Step where
  constant : Fin 4 → ℕ
  slope : Fin 4 → ℕ
  next : ℤ × ℤ

def base (t : ℕ) : ℕ := 256 + 124160 * t

def digit (s : Step) (j : Fin 4) (t : ℕ) : ℕ :=
  2 * s.constant j + 256 * s.slope j * t

def value (ss : List Step) (j : Fin 4) (t : ℕ) : ℕ :=
  ss.foldr (fun s n => digit s j t + base t * n) 1

def ivalue (ss : List Step) (j : Fin 4) (t : ℕ) : ℤ :=
  ss.foldr (fun s n =>
    2 * (s.constant j : ℤ) + 256 * (s.slope j : ℤ) * t + (256 + 124160 * (t : ℤ)) * n) 1

lemma cast_value (ss : List Step) (j : Fin 4) (t : ℕ) :
    (value ss j t : ℤ) = ivalue ss j t := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
    simp only [value, ivalue, List.foldr_cons, digit, base, Nat.cast_add,
      Nat.cast_mul, Nat.cast_ofNat] at ih ⊢
    rw [ih]

def checkStep (s : Step) (k l : ℤ) : Bool := decide (
  485 * (s.constant 2 : ℤ) = 476 * s.constant 0 + 93 * s.constant 1 - k + 256 * s.next.1 ∧
  485 * (s.constant 3 : ℤ) = -93 * s.constant 0 + 476 * s.constant 1 - l + 256 * s.next.2 ∧
  485 * (s.slope 2 : ℤ) = 476 * s.slope 0 + 93 * s.slope 1 + 970 * s.next.1 ∧
  485 * (s.slope 3 : ℤ) = -93 * s.slope 0 + 476 * s.slope 1 + 970 * s.next.2)

def checkPath : List Step → ℤ → ℤ → Bool
  | [], k, l => decide (k = 42 ∧ l = -51)
  | s :: ss, k, l => checkStep s k l && checkPath ss s.next.1 s.next.2

lemma rotation_of_checkPath (ss : List Step) (t : ℕ) (k l : ℤ)
    (h : checkPath ss k l = true) :
    485 * ivalue ss 2 t - 476 * ivalue ss 0 t - 93 * ivalue ss 1 t = -2 * k ∧
    485 * ivalue ss 3 t + 93 * ivalue ss 0 t - 476 * ivalue ss 1 t = -2 * l := by
  induction ss generalizing k l with
  | nil =>
    have hk : k = 42 ∧ l = -51 := of_decide_eq_true h
    rcases hk with ⟨rfl, rfl⟩
    norm_num [ivalue]
  | cons s ss ih =>
    have hh : checkStep s k l = true ∧ checkPath ss s.next.1 s.next.2 = true := by
      simpa only [checkPath, Bool.and_eq_true_iff] using h
    obtain ⟨hs, ht⟩ := hh
    have hs' := of_decide_eq_true hs
    obtain ⟨h₁, h₂, h₃, h₄⟩ := hs'
    obtain ⟨hi₁, hi₂⟩ := ih _ _ ht
    simp only [ivalue, List.foldr_cons] at hi₁ hi₂ ⊢
    constructor
    · linear_combination 2 * h₁ + 256 * (t : ℤ) * h₃ +
        (256 + 124160 * (t : ℤ)) * hi₁
    · linear_combination 2 * h₂ + 256 * (t : ℤ) * h₄ +
        (256 + 124160 * (t : ℤ)) * hi₂

lemma norm_collision_of_checkPath (ss : List Step)
    (h : checkPath ss 0 0 = true) (t : ℕ) :
    value ss 0 t ^ 2 + value ss 1 t ^ 2 = value ss 2 t ^ 2 + value ss 3 t ^ 2 := by
  have hi := rotation_of_checkPath ss t 0 0 h
  have h₁ : 485 * ivalue ss 2 t = 476 * ivalue ss 0 t + 93 * ivalue ss 1 t := by
    linarith [hi.1]
  have h₂ : 485 * ivalue ss 3 t = -93 * ivalue ss 0 t + 476 * ivalue ss 1 t := by
    linarith [hi.2]
  have hsq₁ := congrArg (fun x : ℤ => x ^ 2) h₁
  have hsq₂ := congrArg (fun x : ℤ => x ^ 2) h₂
  have he : ivalue ss 0 t ^ 2 + ivalue ss 1 t ^ 2 =
      ivalue ss 2 t ^ 2 + ivalue ss 3 t ^ 2 := by nlinarith only [hsq₁, hsq₂]
  simp only [← cast_value] at he
  exact_mod_cast he

lemma sum_digits (ss : List Step) (j : Fin 4) (t : ℕ) :
    (ss.map (fun s => digit s j t)).sum =
      2 * (ss.map (fun s => s.constant j)).sum +
        256 * t * (ss.map (fun s => s.slope j)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [digit]
    ring

lemma sum_square_digits (ss : List Step) (j : Fin 4) (t : ℕ) :
    (ss.map (fun s => digit s j t ^ 2)).sum =
      4 * (ss.map (fun s => s.constant j ^ 2)).sum +
        1024 * t * (ss.map (fun s => s.constant j * s.slope j)).sum +
        65536 * t ^ 2 * (ss.map (fun s => s.slope j ^ 2)).sum := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
    simp only [List.map_cons, List.sum_cons]
    rw [ih]
    simp only [digit]
    ring


lemma mod_value (ss : List Step) (j : Fin 4) (t : ℕ) :
    value ss j t % (255 + 124160 * t) =
      ((ss.map (fun s => digit s j t)).sum + 1) % (255 + 124160 * t) := by
  have hb : base t % (255 + 124160 * t) = 1 := by
    have he : base t = (255 + 124160 * t) + 1 := by unfold base; omega
    rw [he, Nat.add_mod, Nat.mod_self, zero_add]
    simpa only [Nat.mod_mod] using (Nat.mod_eq_of_lt (show 1 < 255 + 124160 * t by omega))
  induction ss with
  | nil => simp [value]
  | cons s ss ih =>
    change (digit s j t + base t * value ss j t) % _ = _
    rw [Nat.add_mod, Nat.mul_mod, hb, one_mul, ih]
    simp only [List.map_cons, List.sum_cons, Nat.mod_mod]
    rw [← Nat.add_mod]
    congr 1

lemma bases_unbounded (B : ℕ) : B ≤ base B := by unfold base; omega

end Erdos773.ParametricSphere
