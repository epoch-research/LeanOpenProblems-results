import Submission.QuarticFiveInputDegreeFourLinear1
/-! Checked integer linear combinations for Gaussian interpolation. -/
namespace Erdos322Research.QuarticFiveInputDegreeFour
open Matrix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma coefficient21 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 21=(0 : ℤ)*a 0 := by
  have hh : 80*(a 21-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation0 a h) + (20)*(evaluation_equation2 a h) + (20)*(evaluation_equation4 a h) + (-20)*(evaluation_equation6 a h) + (20)*(evaluation_equation13 a h) + (-20)*(evaluation_equation15 a h) + (-20)*(evaluation_equation20 a h) + (20)*(evaluation_equation22 a h) + (20)*(evaluation_equation32 a h) + (-20)*(evaluation_equation34 a h) + (-20)*(evaluation_equation39 a h) + (20)*(evaluation_equation41 a h) + (-20)*(evaluation_equation48 a h) + (20)*(evaluation_equation50 a h) + (20)*(evaluation_equation53 a h) + (-20)*(evaluation_equation55 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient22 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 22=(0 : ℤ)*a 0 := by
  have hh : 80*(a 22-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation1 a h) + (-20)*(evaluation_equation4 a h) + (20)*(evaluation_equation5 a h) + (20)*(evaluation_equation11 a h) + (20)*(evaluation_equation14 a h) + (20)*(evaluation_equation20 a h) + (-20)*(evaluation_equation21 a h) + (-20)*(evaluation_equation25 a h) + (20)*(evaluation_equation33 a h) + (20)*(evaluation_equation39 a h) + (-20)*(evaluation_equation40 a h) + (-20)*(evaluation_equation44 a h) + (-20)*(evaluation_equation49 a h) + (-20)*(evaluation_equation53 a h) + (20)*(evaluation_equation54 a h) + (20)*(evaluation_equation56 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient23 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 23=(0 : ℤ)*a 0 := by
  have hh : 80*(a 23-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation1 a h) + (20)*(evaluation_equation3 a h) + (-20)*(evaluation_equation13 a h) + (10)*(evaluation_equation15 a h) + (-10)*(evaluation_equation16 a h) + (-10)*(evaluation_equation17 a h) + (10)*(evaluation_equation18 a h) + (20)*(evaluation_equation19 a h) + (20)*(evaluation_equation30 a h) + (10)*(evaluation_equation33 a h) + (-10)*(evaluation_equation35 a h) + (10)*(evaluation_equation48 a h) + (-10)*(evaluation_equation49 a h) + (-10)*(evaluation_equation50 a h) + (10)*(evaluation_equation51 a h) + (-10)*(evaluation_equation57 a h) + (10)*(evaluation_equation59 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient24 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 24=(0 : ℤ)*a 0 := by
  have hh : 80*(a 24-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation1 a h) + (20)*(evaluation_equation5 a h) + (-20)*(evaluation_equation13 a h) + (20)*(evaluation_equation14 a h) + (20)*(evaluation_equation20 a h) + (-20)*(evaluation_equation21 a h) + (20)*(evaluation_equation29 a h) + (-20)*(evaluation_equation31 a h) + (20)*(evaluation_equation33 a h) + (-20)*(evaluation_equation40 a h) + (20)*(evaluation_equation48 a h) + (-20)*(evaluation_equation49 a h) + (-20)*(evaluation_equation53 a h) + (20)*(evaluation_equation54 a h) + (-20)*(evaluation_equation57 a h) + (20)*(evaluation_equation60 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient25 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 25=(0 : ℤ)*a 0 := by
  have hh : 80*(a 25-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation1 a h) + (-20)*(evaluation_equation13 a h) + (20)*(evaluation_equation19 a h) + (20)*(evaluation_equation30 a h) + (20)*(evaluation_equation33 a h) + (20)*(evaluation_equation48 a h) + (-20)*(evaluation_equation58 a h) + (-20)*(evaluation_equation61 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient26 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 26=(0 : ℤ)*a 0 := by
  have hh : 80*(a 26-(0 : ℤ)*a 0)=0 := by
    linear_combination (5)*(evaluation_equation0 a h) + (5)*(evaluation_equation1 a h) + (-5)*(evaluation_equation2 a h) + (-15)*(evaluation_equation3 a h) + (-5)*(evaluation_equation33 a h) + (-5)*(evaluation_equation34 a h) + (10)*(evaluation_equation35 a h) + (10)*(evaluation_equation36 a h) + (-5)*(evaluation_equation37 a h) + (-5)*(evaluation_equation38 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient27 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 27=(0 : ℤ)*a 0 := by
  have hh : 80*(a 27-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation0 a h) + (40)*(evaluation_equation1 a h) + (-20)*(evaluation_equation2 a h) + (-40)*(evaluation_equation3 a h) + (-20)*(evaluation_equation5 a h) + (-10)*(evaluation_equation6 a h) + (30)*(evaluation_equation7 a h) + (30)*(evaluation_equation8 a h) + (-10)*(evaluation_equation9 a h) + (-20)*(evaluation_equation10 a h) + (-20)*(evaluation_equation12 a h) + (-20)*(evaluation_equation32 a h) + (-30)*(evaluation_equation33 a h) + (30)*(evaluation_equation35 a h) + (20)*(evaluation_equation36 a h) + (10)*(evaluation_equation39 a h) + (30)*(evaluation_equation40 a h) + (10)*(evaluation_equation41 a h) + (-30)*(evaluation_equation42 a h) + (-20)*(evaluation_equation43 a h) + (10)*(evaluation_equation44 a h) + (-10)*(evaluation_equation46 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient28 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 28=(0 : ℤ)*a 0 := by
  have hh : 80*(a 28-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation0 a h) + (40)*(evaluation_equation1 a h) + (-20)*(evaluation_equation3 a h) + (20)*(evaluation_equation4 a h) + (-20)*(evaluation_equation5 a h) + (-10)*(evaluation_equation6 a h) + (10)*(evaluation_equation7 a h) + (10)*(evaluation_equation8 a h) + (-10)*(evaluation_equation9 a h) + (-40)*(evaluation_equation10 a h) + (-20)*(evaluation_equation12 a h) + (-20)*(evaluation_equation32 a h) + (-30)*(evaluation_equation33 a h) + (10)*(evaluation_equation35 a h) + (-10)*(evaluation_equation39 a h) + (30)*(evaluation_equation40 a h) + (10)*(evaluation_equation41 a h) + (-10)*(evaluation_equation42 a h) + (10)*(evaluation_equation44 a h) + (-10)*(evaluation_equation46 a h) + (20)*(evaluation_equation47 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient29 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 29=(0 : ℤ)*a 0 := by
  have hh : 80*(a 29-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation0 a h) + (40)*(evaluation_equation1 a h) + (-20)*(evaluation_equation2 a h) + (-40)*(evaluation_equation3 a h) + (-20)*(evaluation_equation14 a h) + (-10)*(evaluation_equation15 a h) + (30)*(evaluation_equation16 a h) + (30)*(evaluation_equation17 a h) + (-10)*(evaluation_equation18 a h) + (-20)*(evaluation_equation19 a h) + (-20)*(evaluation_equation30 a h) + (-20)*(evaluation_equation32 a h) + (-30)*(evaluation_equation33 a h) + (30)*(evaluation_equation35 a h) + (20)*(evaluation_equation36 a h) + (10)*(evaluation_equation48 a h) + (30)*(evaluation_equation49 a h) + (10)*(evaluation_equation50 a h) + (-30)*(evaluation_equation51 a h) + (-20)*(evaluation_equation52 a h) + (10)*(evaluation_equation57 a h) + (-10)*(evaluation_equation59 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient30 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 30=(0 : ℤ)*a 0 := by
  have hh : 80*(a 30-(0 : ℤ)*a 0)=0 := by
    linear_combination (40)*(evaluation_equation0 a h) + (20)*(evaluation_equation1 a h) + (-20)*(evaluation_equation2 a h) + (-20)*(evaluation_equation4 a h) + (-20)*(evaluation_equation5 a h) + (20)*(evaluation_equation6 a h) + (-20)*(evaluation_equation11 a h) + (-20)*(evaluation_equation13 a h) + (-20)*(evaluation_equation14 a h) + (20)*(evaluation_equation15 a h) + (20)*(evaluation_equation21 a h) + (-20)*(evaluation_equation22 a h) + (20)*(evaluation_equation25 a h) + (-20)*(evaluation_equation29 a h) + (20)*(evaluation_equation31 a h) + (-40)*(evaluation_equation32 a h) + (-20)*(evaluation_equation33 a h) + (20)*(evaluation_equation34 a h) + (20)*(evaluation_equation39 a h) + (20)*(evaluation_equation40 a h) + (-20)*(evaluation_equation41 a h) + (20)*(evaluation_equation44 a h) + (20)*(evaluation_equation48 a h) + (20)*(evaluation_equation49 a h) + (-20)*(evaluation_equation50 a h) + (-20)*(evaluation_equation54 a h) + (20)*(evaluation_equation55 a h) + (-20)*(evaluation_equation56 a h) + (20)*(evaluation_equation57 a h) + (-20)*(evaluation_equation60 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

end Erdos322Research.QuarticFiveInputDegreeFour
