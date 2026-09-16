import Mathlib

theorem foo : 1 = 2 :=
  let eq_proof : Quot.mk (fun x y : Prop => (1:ℕ) = 2) True = Quot.mk (fun x y => (1:ℕ) = 2) False := 
    @Quot.sound Prop (fun x y => (1:ℕ) = 2) True False sorry
  sorry
