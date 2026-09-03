import Submission.QuarticFiveInputDegreeFourLinear0
/-! Checked integer linear combinations for Gaussian interpolation. -/
namespace Erdos322Research.QuarticFiveInputDegreeFour
open Matrix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma coefficient11 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 11=(0 : ℤ)*a 0 := by
  have hh : 80*(a 11-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation0 a h) + (40)*(evaluation_equation1 a h) + (-20)*(evaluation_equation2 a h) + (-40)*(evaluation_equation3 a h) + (-20)*(evaluation_equation5 a h) + (-10)*(evaluation_equation6 a h) + (30)*(evaluation_equation7 a h) + (30)*(evaluation_equation8 a h) + (-10)*(evaluation_equation9 a h) + (-20)*(evaluation_equation10 a h) + (-20)*(evaluation_equation12 a h) + (-20)*(evaluation_equation13 a h) + (-30)*(evaluation_equation14 a h) + (30)*(evaluation_equation16 a h) + (20)*(evaluation_equation17 a h) + (10)*(evaluation_equation20 a h) + (30)*(evaluation_equation21 a h) + (10)*(evaluation_equation22 a h) + (-30)*(evaluation_equation23 a h) + (-20)*(evaluation_equation24 a h) + (10)*(evaluation_equation25 a h) + (-10)*(evaluation_equation27 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient12 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 12=(0 : ℤ)*a 0 := by
  have hh : 80*(a 12-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation0 a h) + (40)*(evaluation_equation1 a h) + (-20)*(evaluation_equation3 a h) + (20)*(evaluation_equation4 a h) + (-20)*(evaluation_equation5 a h) + (-10)*(evaluation_equation6 a h) + (10)*(evaluation_equation7 a h) + (10)*(evaluation_equation8 a h) + (-10)*(evaluation_equation9 a h) + (-40)*(evaluation_equation10 a h) + (-20)*(evaluation_equation12 a h) + (-20)*(evaluation_equation13 a h) + (-30)*(evaluation_equation14 a h) + (10)*(evaluation_equation16 a h) + (-10)*(evaluation_equation20 a h) + (30)*(evaluation_equation21 a h) + (10)*(evaluation_equation22 a h) + (-10)*(evaluation_equation23 a h) + (10)*(evaluation_equation25 a h) + (-10)*(evaluation_equation27 a h) + (20)*(evaluation_equation28 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient13 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 13=(0 : ℤ)*a 0 := by
  have hh : 80*(a 13-(0 : ℤ)*a 0)=0 := by
    linear_combination (20)*(evaluation_equation1 a h) + (20)*(evaluation_equation13 a h) + (-20)*(evaluation_equation19 a h) + (-20)*(evaluation_equation30 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient14 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 14=(0 : ℤ)*a 0 := by
  have hh : 80*(a 14-(0 : ℤ)*a 0)=0 := by
    linear_combination (40)*(evaluation_equation0 a h) + (100)*(evaluation_equation1 a h) + (-40)*(evaluation_equation3 a h) + (-80)*(evaluation_equation5 a h) + (-20)*(evaluation_equation6 a h) + (40)*(evaluation_equation7 a h) + (20)*(evaluation_equation8 a h) + (-20)*(evaluation_equation10 a h) + (-20)*(evaluation_equation11 a h) + (-20)*(evaluation_equation12 a h) + (-20)*(evaluation_equation13 a h) + (-100)*(evaluation_equation14 a h) + (-20)*(evaluation_equation15 a h) + (40)*(evaluation_equation16 a h) + (20)*(evaluation_equation17 a h) + (-20)*(evaluation_equation20 a h) + (80)*(evaluation_equation21 a h) + (20)*(evaluation_equation22 a h) + (-40)*(evaluation_equation23 a h) + (-20)*(evaluation_equation24 a h) + (20)*(evaluation_equation25 a h) + (20)*(evaluation_equation26 a h) + (20)*(evaluation_equation28 a h) + (-20)*(evaluation_equation29 a h) + (20)*(evaluation_equation31 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient15 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 15=(1 : ℤ)*a 0 := by
  have hh : 80*(a 15-(1 : ℤ)*a 0)=0 := by
    linear_combination (-170)*(evaluation_equation0 a h) + (-422)*(evaluation_equation1 a h) + (70)*(evaluation_equation2 a h) + (302)*(evaluation_equation3 a h) + (12)*(evaluation_equation4 a h) + (223)*(evaluation_equation5 a h) + (71)*(evaluation_equation6 a h) + (-170)*(evaluation_equation7 a h) + (-110)*(evaluation_equation8 a h) + (31)*(evaluation_equation9 a h) + (95)*(evaluation_equation10 a h) + (28)*(evaluation_equation11 a h) + (60)*(evaluation_equation12 a h) + (44)*(evaluation_equation13 a h) + (246)*(evaluation_equation14 a h) + (62)*(evaluation_equation15 a h) + (-160)*(evaluation_equation16 a h) + (-90)*(evaluation_equation17 a h) + (22)*(evaluation_equation18 a h) + (60)*(evaluation_equation19 a h) + (-10)*(evaluation_equation20 a h) + (-130)*(evaluation_equation21 a h) + (-50)*(evaluation_equation22 a h) + (90)*(evaluation_equation23 a h) + (40)*(evaluation_equation24 a h) + (-30)*(evaluation_equation25 a h) + (10)*(evaluation_equation27 a h) + (-20)*(evaluation_equation28 a h) + (36)*(evaluation_equation29 a h) + (40)*(evaluation_equation30 a h) + (-20)*(evaluation_equation31 a h) + (92)*(evaluation_equation32 a h) + (243)*(evaluation_equation33 a h) + (51)*(evaluation_equation34 a h) + (-170)*(evaluation_equation35 a h) + (-90)*(evaluation_equation36 a h) + (11)*(evaluation_equation37 a h) + (15)*(evaluation_equation38 a h) + (-10)*(evaluation_equation39 a h) + (-130)*(evaluation_equation40 a h) + (-50)*(evaluation_equation41 a h) + (90)*(evaluation_equation42 a h) + (40)*(evaluation_equation43 a h) + (-30)*(evaluation_equation44 a h) + (10)*(evaluation_equation46 a h) + (-20)*(evaluation_equation47 a h) + (-10)*(evaluation_equation48 a h) + (-130)*(evaluation_equation49 a h) + (-50)*(evaluation_equation50 a h) + (90)*(evaluation_equation51 a h) + (40)*(evaluation_equation52 a h) + (20)*(evaluation_equation54 a h) + (20)*(evaluation_equation55 a h) + (-30)*(evaluation_equation57 a h) + (10)*(evaluation_equation59 a h) + (-20)*(evaluation_equation61 a h) + (28)*(evaluation_equation62 a h) + (20)*(evaluation_equation63 a h) + (-20)*(evaluation_equation64 a h) + (-20)*(evaluation_equation65 a h) + (-16)*(evaluation_equation66 a h) + (-32)*(evaluation_equation67 a h) + (-16)*(evaluation_equation68 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient16 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 16=(0 : ℤ)*a 0 := by
  have hh : 80*(a 16-(0 : ℤ)*a 0)=0 := by
    linear_combination (-5)*(evaluation_equation0 a h) + (5)*(evaluation_equation1 a h) + (5)*(evaluation_equation2 a h) + (5)*(evaluation_equation3 a h) + (-5)*(evaluation_equation33 a h) + (-5)*(evaluation_equation34 a h) + (5)*(evaluation_equation37 a h) + (5)*(evaluation_equation38 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient17 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 17=(0 : ℤ)*a 0 := by
  have hh : 80*(a 17-(0 : ℤ)*a 0)=0 := by
    linear_combination (-10)*(evaluation_equation1 a h) + (10)*(evaluation_equation3 a h) + (10)*(evaluation_equation5 a h) + (10)*(evaluation_equation6 a h) + (-10)*(evaluation_equation7 a h) + (-10)*(evaluation_equation8 a h) + (10)*(evaluation_equation33 a h) + (10)*(evaluation_equation34 a h) + (-10)*(evaluation_equation35 a h) + (-10)*(evaluation_equation36 a h) + (-10)*(evaluation_equation40 a h) + (-10)*(evaluation_equation41 a h) + (10)*(evaluation_equation42 a h) + (10)*(evaluation_equation43 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient18 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 18=(0 : ℤ)*a 0 := by
  have hh : 80*(a 18-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation1 a h) + (20)*(evaluation_equation3 a h) + (-20)*(evaluation_equation4 a h) + (10)*(evaluation_equation6 a h) + (-10)*(evaluation_equation7 a h) + (-10)*(evaluation_equation8 a h) + (10)*(evaluation_equation9 a h) + (20)*(evaluation_equation10 a h) + (20)*(evaluation_equation12 a h) + (10)*(evaluation_equation33 a h) + (-10)*(evaluation_equation35 a h) + (10)*(evaluation_equation39 a h) + (-10)*(evaluation_equation40 a h) + (-10)*(evaluation_equation41 a h) + (10)*(evaluation_equation42 a h) + (-10)*(evaluation_equation44 a h) + (10)*(evaluation_equation46 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient19 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 19=(0 : ℤ)*a 0 := by
  have hh : 80*(a 19-(0 : ℤ)*a 0)=0 := by
    linear_combination (-20)*(evaluation_equation1 a h) + (-20)*(evaluation_equation4 a h) + (20)*(evaluation_equation10 a h) + (20)*(evaluation_equation12 a h) + (20)*(evaluation_equation33 a h) + (20)*(evaluation_equation39 a h) + (-20)*(evaluation_equation45 a h) + (-20)*(evaluation_equation47 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

lemma coefficient20 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : a 20=(0 : ℤ)*a 0 := by
  have hh : 80*(a 20-(0 : ℤ)*a 0)=0 := by
    linear_combination (-10)*(evaluation_equation1 a h) + (10)*(evaluation_equation3 a h) + (10)*(evaluation_equation14 a h) + (10)*(evaluation_equation15 a h) + (-10)*(evaluation_equation16 a h) + (-10)*(evaluation_equation17 a h) + (10)*(evaluation_equation33 a h) + (10)*(evaluation_equation34 a h) + (-10)*(evaluation_equation35 a h) + (-10)*(evaluation_equation36 a h) + (-10)*(evaluation_equation49 a h) + (-10)*(evaluation_equation50 a h) + (10)*(evaluation_equation51 a h) + (10)*(evaluation_equation52 a h)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hh).resolve_left (by norm_num))

end Erdos322Research.QuarticFiveInputDegreeFour
