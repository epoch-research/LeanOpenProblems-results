import Submission.QuarticFiveInputDegreeFourLinear3
/-! Checked integer linear combinations for Gaussian interpolation. -/
namespace Erdos322Research.QuarticFiveInputDegreeFour
open Matrix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma coefficient41 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 41=(0 : ℤ)*a 0 := by
  have hh : 80*(a 41-(0 : ℤ)*a 0)=0 := by
    linear_combination (-40)*(evaluation_equation1 a h) + (40)*(evaluation_equation3 a h) + (40)*(evaluation_equation5 a h) + (20)*(evaluation_equation6 a h) + (-40)*(evaluation_equation7 a h) + (-20)*(evaluation_equation8 a h) + (40)*(evaluation_equation14 a h) + (20)*(evaluation_equation15 a h) + (-40)*(evaluation_equation16 a h) + (-20)*(evaluation_equation17 a h) + (-40)*(evaluation_equation21 a h) + (-20)*(evaluation_equation22 a h) + (40)*(evaluation_equation23 a h) + (20)*(evaluation_equation24 a h) + (-20)*(evaluation_equation32 a h) + (20)*(evaluation_equation34 a h) + (20)*(evaluation_equation39 a h) + (-20)*(evaluation_equation41 a h) + (20)*(evaluation_equation48 a h) + (-20)*(evaluation_equation50 a h) + (-20)*(evaluation_equation53 a h) + (20)*(evaluation_equation55 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient42 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 42=(0 : ℤ)*a 0 := by
  have hh : 80*(a 42-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation0 a h) + (-20)*(evaluation_equation1 a h) + (20)*(evaluation_equation5 a h) + (20)*(evaluation_equation10 a h) + (20)*(evaluation_equation13 a h) + (20)*(evaluation_equation14 a h) + (-20)*(evaluation_equation21 a h) + (-20)*(evaluation_equation28 a h) + (-20)*(evaluation_equation33 a h) + (-20)*(evaluation_equation39 a h) + (20)*(evaluation_equation40 a h) + (20)*(evaluation_equation44 a h) + (20)*(evaluation_equation49 a h) + (20)*(evaluation_equation53 a h) + (-20)*(evaluation_equation54 a h) + (-20)*(evaluation_equation56 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient43 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 43=(0 : ℤ)*a 0 := by
  have hh : 80*(a 43-(0 : ℤ)*a 0)=0 := by
    linear_combination (-10)*(evaluation_equation0 a h) + (-30)*(evaluation_equation1 a h) + (10)*(evaluation_equation2 a h) + (30)*(evaluation_equation3 a h) + (20)*(evaluation_equation5 a h) + (10)*(evaluation_equation6 a h) + (-30)*(evaluation_equation7 a h) + (-30)*(evaluation_equation8 a h) + (10)*(evaluation_equation9 a h) + (20)*(evaluation_equation10 a h) + (20)*(evaluation_equation12 a h) + (20)*(evaluation_equation13 a h) + (20)*(evaluation_equation14 a h) + (-20)*(evaluation_equation16 a h) + (-10)*(evaluation_equation17 a h) + (-10)*(evaluation_equation19 a h) + (-10)*(evaluation_equation20 a h) + (-30)*(evaluation_equation21 a h) + (-10)*(evaluation_equation22 a h) + (30)*(evaluation_equation23 a h) + (20)*(evaluation_equation24 a h) + (-10)*(evaluation_equation25 a h) + (10)*(evaluation_equation27 a h) + (-10)*(evaluation_equation33 a h) + (10)*(evaluation_equation35 a h) + (-10)*(evaluation_equation48 a h) + (10)*(evaluation_equation49 a h) + (10)*(evaluation_equation50 a h) + (-10)*(evaluation_equation51 a h) + (10)*(evaluation_equation57 a h) + (-10)*(evaluation_equation59 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient44 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 44=(0 : ℤ)*a 0 := by
  have hh : 80*(a 44-(0 : ℤ)*a 0)=0 := by
    linear_combination (-40)*(evaluation_equation0 a h) + (-80)*(evaluation_equation1 a h) + (20)*(evaluation_equation2 a h) + (60)*(evaluation_equation3 a h) + (-20)*(evaluation_equation4 a h) + (40)*(evaluation_equation5 a h) + (20)*(evaluation_equation6 a h) + (-40)*(evaluation_equation7 a h) + (-40)*(evaluation_equation8 a h) + (20)*(evaluation_equation9 a h) + (60)*(evaluation_equation10 a h) + (40)*(evaluation_equation12 a h) + (40)*(evaluation_equation13 a h) + (60)*(evaluation_equation14 a h) + (-40)*(evaluation_equation16 a h) + (-20)*(evaluation_equation17 a h) + (-60)*(evaluation_equation21 a h) + (-20)*(evaluation_equation22 a h) + (40)*(evaluation_equation23 a h) + (20)*(evaluation_equation24 a h) + (-20)*(evaluation_equation25 a h) + (20)*(evaluation_equation27 a h) + (-20)*(evaluation_equation28 a h) + (-20)*(evaluation_equation33 a h) + (20)*(evaluation_equation40 a h) + (-20)*(evaluation_equation48 a h) + (20)*(evaluation_equation49 a h) + (20)*(evaluation_equation53 a h) + (-20)*(evaluation_equation54 a h) + (20)*(evaluation_equation57 a h) + (-20)*(evaluation_equation60 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient45 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 45=(0 : ℤ)*a 0 := by
  have hh : 80*(a 45-(0 : ℤ)*a 0)=0 := by
    linear_combination (-40)*(evaluation_equation0 a h) + (-80)*(evaluation_equation1 a h) + (20)*(evaluation_equation2 a h) + (60)*(evaluation_equation3 a h) + (80)*(evaluation_equation5 a h) + (20)*(evaluation_equation6 a h) + (-40)*(evaluation_equation7 a h) + (-20)*(evaluation_equation8 a h) + (20)*(evaluation_equation10 a h) + (20)*(evaluation_equation11 a h) + (20)*(evaluation_equation12 a h) + (40)*(evaluation_equation13 a h) + (80)*(evaluation_equation14 a h) + (20)*(evaluation_equation15 a h) + (-60)*(evaluation_equation16 a h) + (-40)*(evaluation_equation17 a h) + (20)*(evaluation_equation20 a h) + (-80)*(evaluation_equation21 a h) + (-20)*(evaluation_equation22 a h) + (40)*(evaluation_equation23 a h) + (20)*(evaluation_equation24 a h) + (-20)*(evaluation_equation25 a h) + (-20)*(evaluation_equation26 a h) + (-20)*(evaluation_equation28 a h) + (-20)*(evaluation_equation31 a h) + (-20)*(evaluation_equation33 a h) + (-20)*(evaluation_equation48 a h) + (20)*(evaluation_equation58 a h) + (20)*(evaluation_equation61 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient46 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 46=(0 : ℤ)*a 0 := by
  have hh : 80*(a 46-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation1 a h) + (-20)*(evaluation_equation3 a h) + (-10)*(evaluation_equation5 a h) + (-10)*(evaluation_equation6 a h) + (10)*(evaluation_equation7 a h) + (10)*(evaluation_equation8 a h) + (-10)*(evaluation_equation14 a h) + (-10)*(evaluation_equation15 a h) + (10)*(evaluation_equation16 a h) + (10)*(evaluation_equation17 a h) + (-10)*(evaluation_equation32 a h) + (-20)*(evaluation_equation33 a h) + (-10)*(evaluation_equation34 a h) + (20)*(evaluation_equation35 a h) + (10)*(evaluation_equation36 a h) + (10)*(evaluation_equation38 a h) + (10)*(evaluation_equation40 a h) + (10)*(evaluation_equation41 a h) + (-10)*(evaluation_equation42 a h) + (-10)*(evaluation_equation43 a h) + (10)*(evaluation_equation49 a h) + (10)*(evaluation_equation50 a h) + (-10)*(evaluation_equation51 a h) + (-10)*(evaluation_equation52 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient47 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 47=(0 : ℤ)*a 0 := by
  have hh : 80*(a 47-(0 : ℤ)*a 0)=0 := by
    linear_combination (-40)*(evaluation_equation1 a h) + (40)*(evaluation_equation3 a h) + (40)*(evaluation_equation5 a h) + (20)*(evaluation_equation6 a h) + (-40)*(evaluation_equation7 a h) + (-20)*(evaluation_equation8 a h) + (-20)*(evaluation_equation13 a h) + (20)*(evaluation_equation15 a h) + (20)*(evaluation_equation20 a h) + (-20)*(evaluation_equation22 a h) + (40)*(evaluation_equation33 a h) + (20)*(evaluation_equation34 a h) + (-40)*(evaluation_equation35 a h) + (-20)*(evaluation_equation36 a h) + (-40)*(evaluation_equation40 a h) + (-20)*(evaluation_equation41 a h) + (40)*(evaluation_equation42 a h) + (20)*(evaluation_equation43 a h) + (20)*(evaluation_equation48 a h) + (-20)*(evaluation_equation50 a h) + (-20)*(evaluation_equation53 a h) + (20)*(evaluation_equation55 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient48 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 48=(0 : ℤ)*a 0 := by
  have hh : 80*(a 48-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation0 a h) + (-20)*(evaluation_equation1 a h) + (20)*(evaluation_equation5 a h) + (20)*(evaluation_equation10 a h) + (-20)*(evaluation_equation14 a h) + (-20)*(evaluation_equation20 a h) + (20)*(evaluation_equation21 a h) + (20)*(evaluation_equation25 a h) + (20)*(evaluation_equation32 a h) + (20)*(evaluation_equation33 a h) + (-20)*(evaluation_equation40 a h) + (-20)*(evaluation_equation47 a h) + (20)*(evaluation_equation49 a h) + (20)*(evaluation_equation53 a h) + (-20)*(evaluation_equation54 a h) + (-20)*(evaluation_equation56 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient49 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 49=(0 : ℤ)*a 0 := by
  have hh : 80*(a 49-(0 : ℤ)*a 0)=0 := by
    linear_combination (-40)*(evaluation_equation1 a h) + (40)*(evaluation_equation3 a h) + (-20)*(evaluation_equation4 a h) + (20)*(evaluation_equation6 a h) + (40)*(evaluation_equation14 a h) + (20)*(evaluation_equation15 a h) + (-40)*(evaluation_equation16 a h) + (-20)*(evaluation_equation17 a h) + (20)*(evaluation_equation20 a h) + (-20)*(evaluation_equation22 a h) + (40)*(evaluation_equation33 a h) + (20)*(evaluation_equation34 a h) + (-40)*(evaluation_equation35 a h) + (-20)*(evaluation_equation36 a h) + (20)*(evaluation_equation39 a h) + (-20)*(evaluation_equation41 a h) + (-40)*(evaluation_equation49 a h) + (-20)*(evaluation_equation50 a h) + (40)*(evaluation_equation51 a h) + (20)*(evaluation_equation52 a h) + (-20)*(evaluation_equation53 a h) + (20)*(evaluation_equation55 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient50 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 50=(0 : ℤ)*a 0 := by
  have hh : 80*(a 50-(0 : ℤ)*a 0)=0 := by
    linear_combination (-40)*(evaluation_equation0 a h) + (40)*(evaluation_equation4 a h) + (40)*(evaluation_equation13 a h) + (-40)*(evaluation_equation20 a h) + (40)*(evaluation_equation32 a h) + (-40)*(evaluation_equation39 a h) + (-40)*(evaluation_equation48 a h) + (40)*(evaluation_equation53 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

end Erdos322Research.QuarticFiveInputDegreeFour
