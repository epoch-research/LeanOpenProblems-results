import Submission.QuarticFiveInputDegreeFourData
/-! The explicit linear equations obtained from the Gaussian interpolation data. -/
namespace Erdos322Research.QuarticFiveInputDegreeFour
open Matrix
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

lemma evaluation_equation0 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(1)*a 21+(1)*a 22+(1)*a 23+(1)*a 24+(1)*a 25+(1)*a 27+(1)*a 28+(1)*a 29+(1)*a 30+(1)*a 31+(1)*a 32+(1)*a 33+(1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(1)*a 41+(1)*a 42+(1)*a 43+(1)*a 44+(1)*a 45+(1)*a 47+(1)*a 48+(1)*a 49+(1)*a 50+(1)*a 51+(1)*a 52+(1)*a 53+(1)*a 54+(1)*a 55+(1)*a 57+(1)*a 58+(1)*a 59+(1)*a 60+(1)*a 61+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 65+(1)*a 66+(1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (0 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow0,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation1 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(2)*a 6+(2)*a 7+(1)*a 8+(2)*a 10+(1)*a 11+(1)*a 13+(2)*a 16+(2)*a 17+(1)*a 18+(2)*a 20+(1)*a 21+(1)*a 23+(2)*a 26+(1)*a 27+(1)*a 29+(1)*a 32+(2)*a 36+(2)*a 37+(1)*a 38+(2)*a 40+(1)*a 41+(1)*a 43+(2)*a 46+(1)*a 47+(1)*a 49+(1)*a 52+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 62+(1)*a 66=0 := by
  have he := congrFun h (1 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow1,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation2 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(1)*a 9+(-1)*a 11+(1)*a 12+(-1)*a 13+(1)*a 14+(1)*a 15+(2)*a 16+(-1)*a 18+(1)*a 19+(-1)*a 21+(1)*a 22+(-1)*a 23+(1)*a 24+(1)*a 25+(-1)*a 27+(1)*a 28+(-1)*a 29+(1)*a 30+(1)*a 31+(-1)*a 32+(1)*a 33+(1)*a 34+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(-1)*a 41+(1)*a 42+(-1)*a 43+(1)*a 44+(1)*a 45+(-1)*a 47+(1)*a 48+(-1)*a 49+(1)*a 50+(1)*a 51+(-1)*a 52+(1)*a 53+(1)*a 54+(1)*a 55+(-1)*a 57+(1)*a 58+(-1)*a 59+(1)*a 60+(1)*a 61+(-1)*a 62+(1)*a 63+(1)*a 64+(1)*a 65+(-1)*a 66+(1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (2 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow2,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation3 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(-2)*a 3+(1)*a 4+(2)*a 6+(-2)*a 7+(1)*a 8+(-2)*a 10+(1)*a 11+(1)*a 13+(2)*a 16+(-2)*a 17+(1)*a 18+(-2)*a 20+(1)*a 21+(1)*a 23+(-2)*a 26+(1)*a 27+(1)*a 29+(1)*a 32+(2)*a 36+(-2)*a 37+(1)*a 38+(-2)*a 40+(1)*a 41+(1)*a 43+(-2)*a 46+(1)*a 47+(1)*a 49+(1)*a 52+(-2)*a 56+(1)*a 57+(1)*a 59+(1)*a 62+(1)*a 66=0 := by
  have he := congrFun h (3 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow3,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation4 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 25+(-1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 31+(1)*a 32+(1)*a 34+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(-1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 45+(-1)*a 47+(-1)*a 48+(1)*a 49+(1)*a 51+(1)*a 52+(1)*a 54+(1)*a 55+(-1)*a 57+(-1)*a 58+(1)*a 59+(1)*a 61+(1)*a 62+(1)*a 64+(1)*a 65+(1)*a 66+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (4 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow4,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation5 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(-2)*a 3+(-1)*a 4+(2)*a 6+(-1)*a 8+(-1)*a 9+(2)*a 10+(1)*a 11+(1)*a 13+(1)*a 14+(2)*a 16+(-1)*a 18+(-1)*a 19+(2)*a 20+(1)*a 21+(1)*a 23+(1)*a 24+(2)*a 26+(1)*a 27+(1)*a 29+(1)*a 30+(1)*a 32+(1)*a 33+(2)*a 36+(-1)*a 38+(-1)*a 39+(2)*a 40+(1)*a 41+(1)*a 43+(1)*a 44+(2)*a 46+(1)*a 47+(1)*a 49+(1)*a 50+(1)*a 52+(1)*a 53+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 60+(1)*a 62+(1)*a 63+(1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (5 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow5,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation6 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(2)*a 7+(1)*a 8+(-1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(2)*a 16+(2)*a 17+(1)*a 18+(-1)*a 21+(-1)*a 22+(-1)*a 23+(1)*a 25+(-1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 31+(-1)*a 32+(1)*a 34+(1)*a 35+(2)*a 36+(2)*a 37+(1)*a 38+(-1)*a 41+(-1)*a 42+(-1)*a 43+(1)*a 45+(-1)*a 47+(-1)*a 48+(-1)*a 49+(1)*a 51+(-1)*a 52+(1)*a 54+(1)*a 55+(-1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 61+(-1)*a 62+(1)*a 64+(1)*a 65+(-1)*a 66+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (6 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow6,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation7 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(2)*a 6+(-1)*a 8+(-1)*a 9+(-2)*a 10+(-1)*a 11+(1)*a 13+(1)*a 14+(2)*a 16+(-1)*a 18+(-1)*a 19+(-2)*a 20+(-1)*a 21+(1)*a 23+(1)*a 24+(-2)*a 26+(-1)*a 27+(1)*a 29+(1)*a 30+(1)*a 32+(1)*a 33+(2)*a 36+(-1)*a 38+(-1)*a 39+(-2)*a 40+(-1)*a 41+(1)*a 43+(1)*a 44+(-2)*a 46+(-1)*a 47+(1)*a 49+(1)*a 50+(1)*a 52+(1)*a 53+(-2)*a 56+(-1)*a 57+(1)*a 59+(1)*a 60+(1)*a 62+(1)*a 63+(1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (7 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow7,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation8 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-2)*a 7+(1)*a 8+(1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(2)*a 16+(-2)*a 17+(1)*a 18+(1)*a 21+(-1)*a 22+(-1)*a 23+(1)*a 25+(1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 31+(-1)*a 32+(1)*a 34+(1)*a 35+(2)*a 36+(-2)*a 37+(1)*a 38+(1)*a 41+(-1)*a 42+(-1)*a 43+(1)*a 45+(1)*a 47+(-1)*a 48+(-1)*a 49+(1)*a 51+(-1)*a 52+(1)*a 54+(1)*a 55+(1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 61+(-1)*a 62+(1)*a 64+(1)*a 65+(-1)*a 66+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (8 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow8,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation9 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(-2)*a 3+(1)*a 4+(-2)*a 6+(1)*a 8+(-1)*a 9+(2)*a 10+(-1)*a 11+(-1)*a 13+(1)*a 14+(-2)*a 16+(1)*a 18+(-1)*a 19+(2)*a 20+(-1)*a 21+(-1)*a 23+(1)*a 24+(2)*a 26+(-1)*a 27+(-1)*a 29+(1)*a 30+(-1)*a 32+(1)*a 33+(-2)*a 36+(1)*a 38+(-1)*a 39+(2)*a 40+(-1)*a 41+(-1)*a 43+(1)*a 44+(2)*a 46+(-1)*a 47+(-1)*a 49+(1)*a 50+(-1)*a 52+(1)*a 53+(2)*a 56+(-1)*a 57+(-1)*a 59+(1)*a 60+(-1)*a 62+(1)*a 63+(-1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (9 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow9,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

#eval IO.println "row 9 done"

lemma evaluation_equation10 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(2)*a 7+(-1)*a 8+(1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 25+(1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 31+(1)*a 32+(1)*a 34+(1)*a 35+(-2)*a 36+(2)*a 37+(-1)*a 38+(1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 45+(1)*a 47+(-1)*a 48+(1)*a 49+(1)*a 51+(1)*a 52+(1)*a 54+(1)*a 55+(1)*a 57+(-1)*a 58+(1)*a 59+(1)*a 61+(1)*a 62+(1)*a 64+(1)*a 65+(1)*a 66+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (10 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow10,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation11 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(-1)*a 9+(-1)*a 11+(1)*a 12+(1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(1)*a 18+(-1)*a 19+(-1)*a 21+(1)*a 22+(1)*a 23+(-1)*a 24+(1)*a 25+(-1)*a 27+(1)*a 28+(1)*a 29+(-1)*a 30+(1)*a 31+(1)*a 32+(-1)*a 33+(1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(-1)*a 39+(-1)*a 41+(1)*a 42+(1)*a 43+(-1)*a 44+(1)*a 45+(-1)*a 47+(1)*a 48+(1)*a 49+(-1)*a 50+(1)*a 51+(1)*a 52+(-1)*a 53+(1)*a 54+(1)*a 55+(-1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 60+(1)*a 61+(1)*a 62+(-1)*a 63+(1)*a 64+(1)*a 65+(1)*a 66+(-1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (11 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow11,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation12 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(2)*a 3+(-1)*a 4+(2)*a 6+(-2)*a 7+(1)*a 8+(2)*a 10+(-1)*a 11+(1)*a 13+(2)*a 16+(-2)*a 17+(1)*a 18+(2)*a 20+(-1)*a 21+(1)*a 23+(2)*a 26+(-1)*a 27+(1)*a 29+(1)*a 32+(2)*a 36+(-2)*a 37+(1)*a 38+(2)*a 40+(-1)*a 41+(1)*a 43+(2)*a 46+(-1)*a 47+(1)*a 49+(1)*a 52+(2)*a 56+(-1)*a 57+(1)*a 59+(1)*a 62+(1)*a 66=0 := by
  have he := congrFun h (12 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow12,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation13 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(-2)*a 20+(-1)*a 21+(-1)*a 23+(-1)*a 24+(1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(1)*a 32+(1)*a 33+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(-2)*a 40+(-1)*a 41+(-1)*a 43+(-1)*a 44+(1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(1)*a 52+(1)*a 53+(1)*a 55+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(1)*a 62+(1)*a 63+(1)*a 65+(1)*a 66+(1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (13 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow13,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation14 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(-2)*a 6+(1)*a 8+(1)*a 9+(-2)*a 10+(-1)*a 11+(-1)*a 13+(-1)*a 14+(2)*a 16+(2)*a 17+(1)*a 18+(1)*a 21+(1)*a 22+(-1)*a 23+(-1)*a 25+(2)*a 26+(1)*a 27+(1)*a 29+(1)*a 30+(1)*a 32+(1)*a 34+(2)*a 36+(2)*a 37+(1)*a 38+(1)*a 41+(1)*a 42+(-1)*a 43+(-1)*a 45+(2)*a 46+(1)*a 47+(1)*a 49+(1)*a 50+(1)*a 52+(1)*a 54+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 60+(1)*a 62+(1)*a 64+(1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (14 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow14,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation15 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(2)*a 7+(-1)*a 8+(1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(2)*a 16+(-1)*a 18+(1)*a 19+(2)*a 20+(-1)*a 21+(1)*a 23+(-1)*a 24+(-1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(-1)*a 32+(1)*a 33+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(2)*a 40+(-1)*a 41+(1)*a 43+(-1)*a 44+(-1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(-1)*a 52+(1)*a 53+(1)*a 55+(-1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(-1)*a 62+(1)*a 63+(1)*a 65+(-1)*a 66+(1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (15 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow15,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation16 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(-2)*a 3+(1)*a 4+(2)*a 6+(-1)*a 8+(1)*a 9+(2)*a 10+(-1)*a 11+(1)*a 13+(-1)*a 14+(2)*a 16+(-2)*a 17+(1)*a 18+(-1)*a 21+(1)*a 22+(-1)*a 23+(-1)*a 25+(-2)*a 26+(1)*a 27+(-1)*a 29+(1)*a 30+(1)*a 32+(1)*a 34+(2)*a 36+(-2)*a 37+(1)*a 38+(-1)*a 41+(1)*a 42+(-1)*a 43+(-1)*a 45+(-2)*a 46+(1)*a 47+(-1)*a 49+(1)*a 50+(1)*a 52+(1)*a 54+(-2)*a 56+(1)*a 57+(-1)*a 59+(1)*a 60+(1)*a 62+(1)*a 64+(1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (16 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow16,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation17 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-2)*a 7+(1)*a 8+(1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(2)*a 16+(-1)*a 18+(1)*a 19+(-2)*a 20+(1)*a 21+(1)*a 23+(-1)*a 24+(-1)*a 27+(1)*a 28+(1)*a 29+(-1)*a 31+(-1)*a 32+(1)*a 33+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(-2)*a 40+(1)*a 41+(1)*a 43+(-1)*a 44+(-1)*a 47+(1)*a 48+(1)*a 49+(-1)*a 51+(-1)*a 52+(1)*a 53+(1)*a 55+(-1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 61+(-1)*a 62+(1)*a 63+(1)*a 65+(-1)*a 66+(1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (17 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow17,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation18 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(2)*a 3+(-1)*a 4+(2)*a 6+(-1)*a 8+(1)*a 9+(-2)*a 10+(1)*a 11+(1)*a 13+(-1)*a 14+(-2)*a 16+(2)*a 17+(-1)*a 18+(-1)*a 21+(1)*a 22+(1)*a 23+(-1)*a 25+(2)*a 26+(-1)*a 27+(-1)*a 29+(1)*a 30+(-1)*a 32+(1)*a 34+(-2)*a 36+(2)*a 37+(-1)*a 38+(-1)*a 41+(1)*a 42+(1)*a 43+(-1)*a 45+(2)*a 46+(-1)*a 47+(-1)*a 49+(1)*a 50+(-1)*a 52+(1)*a 54+(2)*a 56+(-1)*a 57+(-1)*a 59+(1)*a 60+(-1)*a 62+(1)*a 64+(-1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (18 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow18,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation19 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(2)*a 7+(1)*a 8+(-1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(2)*a 20+(1)*a 21+(-1)*a 23+(-1)*a 24+(1)*a 27+(1)*a 28+(1)*a 29+(-1)*a 31+(1)*a 32+(1)*a 33+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(2)*a 40+(1)*a 41+(-1)*a 43+(-1)*a 44+(1)*a 47+(1)*a 48+(1)*a 49+(-1)*a 51+(1)*a 52+(1)*a 53+(1)*a 55+(1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 61+(1)*a 62+(1)*a 63+(1)*a 65+(1)*a 66+(1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (19 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow19,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

#eval IO.println "row 19 done"

lemma evaluation_equation20 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-2)*a 20+(-1)*a 21+(-1)*a 23+(-1)*a 27+(-1)*a 28+(-1)*a 29+(-1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(-2)*a 40+(-1)*a 41+(-1)*a 43+(-1)*a 47+(-1)*a 48+(-1)*a 49+(-1)*a 50+(-1)*a 51+(1)*a 52+(1)*a 55+(-1)*a 57+(-1)*a 58+(-1)*a 59+(-1)*a 60+(-1)*a 61+(1)*a 62+(1)*a 65+(1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (20 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow20,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation21 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(-2)*a 3+(-1)*a 4+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-2)*a 10+(-1)*a 11+(-1)*a 13+(2)*a 16+(-1)*a 18+(-1)*a 19+(-1)*a 21+(-1)*a 22+(-1)*a 23+(-1)*a 24+(-1)*a 25+(2)*a 26+(1)*a 27+(1)*a 29+(1)*a 32+(1)*a 33+(1)*a 34+(2)*a 36+(-1)*a 38+(-1)*a 39+(-1)*a 41+(-1)*a 42+(-1)*a 43+(-1)*a 44+(-1)*a 45+(2)*a 46+(1)*a 47+(1)*a 49+(1)*a 52+(1)*a 53+(1)*a 54+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 66+(1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (21 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow21,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation22 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(2)*a 16+(2)*a 17+(1)*a 18+(2)*a 20+(1)*a 21+(1)*a 23+(-1)*a 27+(-1)*a 28+(-1)*a 29+(-1)*a 30+(-1)*a 31+(-1)*a 32+(1)*a 35+(2)*a 36+(2)*a 37+(1)*a 38+(2)*a 40+(1)*a 41+(1)*a 43+(-1)*a 47+(-1)*a 48+(-1)*a 49+(-1)*a 50+(-1)*a 51+(-1)*a 52+(1)*a 55+(-1)*a 57+(-1)*a 58+(-1)*a 59+(-1)*a 60+(-1)*a 61+(-1)*a 62+(1)*a 65+(-1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (22 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow22,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation23 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(2)*a 6+(2)*a 7+(1)*a 8+(2)*a 10+(1)*a 11+(1)*a 13+(2)*a 16+(-1)*a 18+(-1)*a 19+(-1)*a 21+(-1)*a 22+(-1)*a 23+(-1)*a 24+(-1)*a 25+(-2)*a 26+(-1)*a 27+(-1)*a 29+(1)*a 32+(1)*a 33+(1)*a 34+(2)*a 36+(-1)*a 38+(-1)*a 39+(-1)*a 41+(-1)*a 42+(-1)*a 43+(-1)*a 44+(-1)*a 45+(-2)*a 46+(-1)*a 47+(-1)*a 49+(1)*a 52+(1)*a 53+(1)*a 54+(-2)*a 56+(-1)*a 57+(-1)*a 59+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 66+(1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (23 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow23,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation24 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(1)*a 9+(-1)*a 11+(1)*a 12+(-1)*a 13+(1)*a 14+(1)*a 15+(2)*a 16+(-2)*a 17+(1)*a 18+(-2)*a 20+(1)*a 21+(1)*a 23+(1)*a 27+(-1)*a 28+(1)*a 29+(-1)*a 30+(-1)*a 31+(-1)*a 32+(1)*a 35+(2)*a 36+(-2)*a 37+(1)*a 38+(-2)*a 40+(1)*a 41+(1)*a 43+(1)*a 47+(-1)*a 48+(1)*a 49+(-1)*a 50+(-1)*a 51+(-1)*a 52+(1)*a 55+(1)*a 57+(-1)*a 58+(1)*a 59+(-1)*a 60+(-1)*a 61+(-1)*a 62+(1)*a 65+(-1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (24 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow24,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation25 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(2)*a 7+(-1)*a 8+(1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(-1)*a 19+(-2)*a 20+(1)*a 21+(-1)*a 23+(1)*a 24+(-1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(1)*a 32+(-1)*a 33+(1)*a 35+(-2)*a 36+(1)*a 38+(-1)*a 39+(-2)*a 40+(1)*a 41+(-1)*a 43+(1)*a 44+(-1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(1)*a 52+(-1)*a 53+(1)*a 55+(-1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(1)*a 62+(-1)*a 63+(1)*a 65+(1)*a 66+(-1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (25 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow25,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation26 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(2)*a 3+(-1)*a 4+(-2)*a 6+(1)*a 8+(-1)*a 9+(-2)*a 10+(1)*a 11+(-1)*a 13+(1)*a 14+(2)*a 16+(-2)*a 17+(1)*a 18+(-1)*a 21+(1)*a 22+(-1)*a 23+(-1)*a 25+(2)*a 26+(-1)*a 27+(1)*a 29+(-1)*a 30+(1)*a 32+(1)*a 34+(2)*a 36+(-2)*a 37+(1)*a 38+(-1)*a 41+(1)*a 42+(-1)*a 43+(-1)*a 45+(2)*a 46+(-1)*a 47+(1)*a 49+(-1)*a 50+(1)*a 52+(1)*a 54+(2)*a 56+(-1)*a 57+(1)*a 59+(-1)*a 60+(1)*a 62+(1)*a 64+(1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (26 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow26,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation27 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(2)*a 16+(-1)*a 18+(-1)*a 19+(2)*a 20+(1)*a 21+(1)*a 23+(1)*a 24+(1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(-1)*a 32+(-1)*a 33+(1)*a 35+(2)*a 36+(-1)*a 38+(-1)*a 39+(2)*a 40+(1)*a 41+(1)*a 43+(1)*a 44+(1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(-1)*a 52+(-1)*a 53+(1)*a 55+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(-1)*a 62+(-1)*a 63+(1)*a 65+(-1)*a 66+(-1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (27 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow27,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation28 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(-1)*a 9+(-1)*a 11+(1)*a 12+(1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(-2)*a 20+(1)*a 21+(-1)*a 23+(1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(-2)*a 36+(2)*a 37+(-1)*a 38+(-2)*a 40+(1)*a 41+(-1)*a 43+(1)*a 47+(-1)*a 48+(-1)*a 49+(1)*a 50+(-1)*a 51+(1)*a 52+(1)*a 55+(1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 60+(-1)*a 61+(1)*a 62+(1)*a 65+(1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (28 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow28,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation29 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(-1)*a 9+(1)*a 11+(1)*a 12+(-1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(-1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 24+(-1)*a 25+(1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 30+(1)*a 31+(1)*a 32+(1)*a 33+(-1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(-1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 44+(-1)*a 45+(1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 50+(1)*a 51+(1)*a 52+(1)*a 53+(-1)*a 54+(1)*a 55+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 60+(1)*a 61+(1)*a 62+(1)*a 63+(-1)*a 64+(1)*a 65+(1)*a 66+(1)*a 67+(-1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (29 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow29,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

#eval IO.println "row 29 done"

lemma evaluation_equation30 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(-2)*a 6+(-2)*a 7+(-1)*a 8+(2)*a 10+(1)*a 11+(-1)*a 13+(2)*a 16+(2)*a 17+(1)*a 18+(-2)*a 20+(-1)*a 21+(1)*a 23+(2)*a 26+(1)*a 27+(-1)*a 29+(1)*a 32+(2)*a 36+(2)*a 37+(1)*a 38+(-2)*a 40+(-1)*a 41+(1)*a 43+(2)*a 46+(1)*a 47+(-1)*a 49+(1)*a 52+(2)*a 56+(1)*a 57+(-1)*a 59+(1)*a 62+(1)*a 66=0 := by
  have he := congrFun h (30 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow30,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation31 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(2)*a 7+(1)*a 8+(-1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(1)*a 21+(1)*a 22+(1)*a 23+(-1)*a 25+(-1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 31+(1)*a 32+(-1)*a 34+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(1)*a 41+(1)*a 42+(1)*a 43+(-1)*a 45+(-1)*a 47+(-1)*a 48+(-1)*a 49+(1)*a 51+(1)*a 52+(-1)*a 54+(1)*a 55+(-1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 61+(1)*a 62+(-1)*a 64+(1)*a 65+(1)*a 66+(-1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (31 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow31,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation32 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-2)*a 20+(-1)*a 21+(-1)*a 23+(-1)*a 27+(-1)*a 28+(-1)*a 29+(-1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(1)*a 41+(1)*a 42+(1)*a 43+(1)*a 44+(1)*a 45+(-2)*a 46+(-1)*a 47+(-1)*a 49+(-1)*a 52+(-1)*a 53+(-1)*a 54+(1)*a 57+(1)*a 58+(1)*a 59+(1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 65+(1)*a 66+(1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (32 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow32,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation33 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(2)*a 6+(2)*a 7+(1)*a 8+(2)*a 10+(1)*a 11+(1)*a 13+(-2)*a 16+(1)*a 18+(1)*a 19+(1)*a 21+(1)*a 22+(1)*a 23+(1)*a 24+(1)*a 25+(-2)*a 26+(-1)*a 27+(-1)*a 29+(-1)*a 32+(-1)*a 33+(-1)*a 34+(2)*a 36+(2)*a 37+(1)*a 38+(2)*a 40+(1)*a 41+(1)*a 43+(1)*a 47+(1)*a 48+(1)*a 49+(1)*a 50+(1)*a 51+(-1)*a 52+(-1)*a 55+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (33 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow33,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation34 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(1)*a 9+(-1)*a 11+(1)*a 12+(-1)*a 13+(1)*a 14+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(2)*a 20+(-1)*a 21+(-1)*a 23+(1)*a 27+(-1)*a 28+(1)*a 29+(-1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(-1)*a 41+(1)*a 42+(-1)*a 43+(1)*a 44+(1)*a 45+(2)*a 46+(-1)*a 47+(-1)*a 49+(1)*a 52+(-1)*a 53+(-1)*a 54+(-1)*a 57+(1)*a 58+(-1)*a 59+(1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 65+(-1)*a 66+(1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (34 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow34,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation35 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(-2)*a 3+(1)*a 4+(2)*a 6+(-2)*a 7+(1)*a 8+(-2)*a 10+(1)*a 11+(1)*a 13+(2)*a 16+(-1)*a 18+(1)*a 19+(-1)*a 21+(1)*a 22+(-1)*a 23+(1)*a 24+(1)*a 25+(2)*a 26+(-1)*a 27+(-1)*a 29+(1)*a 32+(-1)*a 33+(-1)*a 34+(2)*a 36+(-2)*a 37+(1)*a 38+(-2)*a 40+(1)*a 41+(1)*a 43+(-1)*a 47+(1)*a 48+(-1)*a 49+(1)*a 50+(1)*a 51+(-1)*a 52+(-1)*a 55+(-2)*a 56+(1)*a 57+(1)*a 59+(-1)*a 62+(1)*a 63+(1)*a 64+(1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (35 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow35,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation36 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(1)*a 9+(-1)*a 11+(1)*a 12+(-1)*a 13+(1)*a 14+(1)*a 15+(2)*a 16+(-2)*a 17+(1)*a 18+(-2)*a 20+(1)*a 21+(1)*a 23+(1)*a 27+(-1)*a 28+(1)*a 29+(-1)*a 30+(-1)*a 31+(-1)*a 32+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(-1)*a 41+(1)*a 42+(-1)*a 43+(1)*a 44+(1)*a 45+(-2)*a 46+(1)*a 47+(1)*a 49+(1)*a 52+(-1)*a 53+(-1)*a 54+(-1)*a 57+(1)*a 58+(-1)*a 59+(1)*a 60+(1)*a 61+(1)*a 62+(-1)*a 65+(-1)*a 66+(1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (36 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow36,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation37 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(2)*a 3+(-1)*a 4+(-2)*a 6+(2)*a 7+(-1)*a 8+(2)*a 10+(-1)*a 11+(-1)*a 13+(2)*a 16+(-1)*a 18+(1)*a 19+(-1)*a 21+(1)*a 22+(-1)*a 23+(1)*a 24+(1)*a 25+(-2)*a 26+(1)*a 27+(1)*a 29+(1)*a 32+(-1)*a 33+(-1)*a 34+(-2)*a 36+(2)*a 37+(-1)*a 38+(2)*a 40+(-1)*a 41+(-1)*a 43+(-1)*a 47+(1)*a 48+(-1)*a 49+(1)*a 50+(1)*a 51+(1)*a 52+(-1)*a 55+(2)*a 56+(-1)*a 57+(-1)*a 59+(-1)*a 62+(1)*a 63+(1)*a 64+(-1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (37 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow37,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation38 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(2)*a 16+(2)*a 17+(1)*a 18+(2)*a 20+(1)*a 21+(1)*a 23+(-1)*a 27+(-1)*a 28+(-1)*a 29+(-1)*a 30+(-1)*a 31+(-1)*a 32+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(1)*a 41+(1)*a 42+(1)*a 43+(1)*a 44+(1)*a 45+(2)*a 46+(1)*a 47+(1)*a 49+(-1)*a 52+(-1)*a 53+(-1)*a 54+(1)*a 57+(1)*a 58+(1)*a 59+(1)*a 60+(1)*a 61+(1)*a 62+(-1)*a 65+(1)*a 66+(1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (38 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow38,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation39 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(-2)*a 20+(-1)*a 21+(-1)*a 23+(-1)*a 24+(1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(1)*a 32+(1)*a 33+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(-1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 45+(-2)*a 46+(-1)*a 47+(-1)*a 49+(-1)*a 50+(-1)*a 52+(-1)*a 54+(-1)*a 57+(-1)*a 58+(1)*a 59+(1)*a 61+(-1)*a 62+(-1)*a 63+(-1)*a 65+(1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (39 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow39,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

#eval IO.println "row 39 done"

lemma evaluation_equation40 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(-2)*a 3+(-1)*a 4+(2)*a 6+(-1)*a 8+(-1)*a 9+(2)*a 10+(1)*a 11+(1)*a 13+(1)*a 14+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 25+(-2)*a 26+(-1)*a 27+(-1)*a 29+(-1)*a 30+(-1)*a 32+(-1)*a 34+(2)*a 36+(-1)*a 38+(-1)*a 39+(2)*a 40+(1)*a 41+(1)*a 43+(1)*a 44+(-1)*a 47+(-1)*a 48+(1)*a 49+(1)*a 51+(-1)*a 52+(-1)*a 53+(-1)*a 55+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 60+(1)*a 62+(1)*a 64+(1)*a 66+(1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (40 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow40,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation41 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(2)*a 7+(1)*a 8+(-1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(2)*a 20+(1)*a 21+(-1)*a 23+(-1)*a 24+(1)*a 27+(1)*a 28+(1)*a 29+(-1)*a 31+(1)*a 32+(1)*a 33+(1)*a 35+(2)*a 36+(2)*a 37+(1)*a 38+(-1)*a 41+(-1)*a 42+(-1)*a 43+(1)*a 45+(2)*a 46+(1)*a 47+(-1)*a 49+(-1)*a 50+(1)*a 52+(-1)*a 54+(-1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 61+(-1)*a 62+(-1)*a 63+(-1)*a 65+(-1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (41 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow41,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation42 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(2)*a 6+(-1)*a 8+(-1)*a 9+(-2)*a 10+(-1)*a 11+(1)*a 13+(1)*a 14+(2)*a 16+(2)*a 17+(1)*a 18+(-1)*a 21+(-1)*a 22+(-1)*a 23+(1)*a 25+(2)*a 26+(1)*a 27+(-1)*a 29+(-1)*a 30+(1)*a 32+(-1)*a 34+(2)*a 36+(-1)*a 38+(-1)*a 39+(-2)*a 40+(-1)*a 41+(1)*a 43+(1)*a 44+(-1)*a 47+(-1)*a 48+(-1)*a 49+(1)*a 51+(-1)*a 52+(-1)*a 53+(-1)*a 55+(-2)*a 56+(-1)*a 57+(1)*a 59+(1)*a 60+(-1)*a 62+(1)*a 64+(1)*a 66+(1)*a 67+(1)*a 69=0 := by
  have he := congrFun h (42 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow42,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation43 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-2)*a 7+(1)*a 8+(1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(2)*a 16+(-1)*a 18+(1)*a 19+(-2)*a 20+(1)*a 21+(1)*a 23+(-1)*a 24+(-1)*a 27+(1)*a 28+(1)*a 29+(-1)*a 31+(-1)*a 32+(1)*a 33+(1)*a 35+(2)*a 36+(-2)*a 37+(1)*a 38+(1)*a 41+(-1)*a 42+(-1)*a 43+(1)*a 45+(-2)*a 46+(1)*a 47+(1)*a 49+(-1)*a 50+(1)*a 52+(-1)*a 54+(1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 61+(1)*a 62+(-1)*a 63+(-1)*a 65+(-1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (43 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow43,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation44 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(-1)*a 9+(-1)*a 11+(1)*a 12+(1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(-2)*a 20+(1)*a 21+(-1)*a 23+(1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(-2)*a 36+(1)*a 38+(-1)*a 39+(-1)*a 41+(1)*a 42+(1)*a 43+(-1)*a 44+(1)*a 45+(-2)*a 46+(1)*a 47+(-1)*a 49+(-1)*a 52+(1)*a 53+(-1)*a 54+(-1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 65+(1)*a 66+(-1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (44 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow44,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation45 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(2)*a 3+(-1)*a 4+(2)*a 6+(-2)*a 7+(1)*a 8+(2)*a 10+(-1)*a 11+(1)*a 13+(-2)*a 16+(1)*a 18+(-1)*a 19+(-1)*a 21+(1)*a 22+(1)*a 23+(-1)*a 24+(1)*a 25+(-2)*a 26+(1)*a 27+(-1)*a 29+(-1)*a 32+(1)*a 33+(-1)*a 34+(2)*a 36+(-2)*a 37+(1)*a 38+(2)*a 40+(-1)*a 41+(1)*a 43+(-1)*a 47+(1)*a 48+(1)*a 49+(-1)*a 50+(1)*a 51+(-1)*a 52+(-1)*a 55+(2)*a 56+(-1)*a 57+(1)*a 59+(1)*a 62+(-1)*a 63+(1)*a 64+(1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (45 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow45,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation46 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(-1)*a 9+(1)*a 11+(1)*a 12+(-1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(2)*a 20+(1)*a 21+(-1)*a 23+(-1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(2)*a 36+(-1)*a 38+(-1)*a 39+(1)*a 41+(1)*a 42+(-1)*a 43+(-1)*a 44+(1)*a 45+(2)*a 46+(1)*a 47+(-1)*a 49+(1)*a 52+(1)*a 53+(-1)*a 54+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 65+(-1)*a 66+(-1)*a 67+(1)*a 68=0 := by
  have he := congrFun h (46 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow46,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation47 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(2)*a 7+(-1)*a 8+(1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(-1)*a 19+(-2)*a 20+(1)*a 21+(-1)*a 23+(1)*a 24+(-1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(1)*a 32+(-1)*a 33+(1)*a 35+(-2)*a 36+(2)*a 37+(-1)*a 38+(1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 45+(-2)*a 46+(1)*a 47+(-1)*a 49+(1)*a 50+(-1)*a 52+(-1)*a 54+(1)*a 57+(-1)*a 58+(1)*a 59+(1)*a 61+(-1)*a 62+(1)*a 63+(-1)*a 65+(1)*a 66+(1)*a 68=0 := by
  have he := congrFun h (47 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow47,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation48 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 25+(-1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 31+(1)*a 32+(1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(-2)*a 40+(-1)*a 41+(-1)*a 43+(-1)*a 44+(-2)*a 46+(-1)*a 47+(-1)*a 49+(-1)*a 50+(-1)*a 52+(-1)*a 53+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(-1)*a 62+(-1)*a 64+(-1)*a 65+(1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (48 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow48,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation49 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(-2)*a 6+(1)*a 8+(1)*a 9+(-2)*a 10+(-1)*a 11+(-1)*a 13+(-1)*a 14+(-2)*a 16+(1)*a 18+(1)*a 19+(-2)*a 20+(-1)*a 21+(-1)*a 23+(-1)*a 24+(-2)*a 26+(-1)*a 27+(-1)*a 29+(-1)*a 30+(-1)*a 32+(-1)*a 33+(2)*a 36+(2)*a 37+(1)*a 38+(1)*a 41+(1)*a 42+(-1)*a 43+(-1)*a 45+(1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(-1)*a 52+(-1)*a 54+(-1)*a 55+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 60+(1)*a 62+(1)*a 63+(1)*a 66+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (49 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow49,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

#eval IO.println "row 49 done"

lemma evaluation_equation50 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(2)*a 7+(-1)*a 8+(1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 25+(1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 31+(1)*a 32+(1)*a 34+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(2)*a 40+(-1)*a 41+(1)*a 43+(-1)*a 44+(2)*a 46+(-1)*a 47+(1)*a 49+(-1)*a 50+(1)*a 52+(-1)*a 53+(-1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(-1)*a 62+(-1)*a 64+(-1)*a 65+(-1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (50 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow50,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation51 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(-2)*a 3+(1)*a 4+(2)*a 6+(-1)*a 8+(1)*a 9+(2)*a 10+(-1)*a 11+(1)*a 13+(-1)*a 14+(2)*a 16+(-1)*a 18+(1)*a 19+(2)*a 20+(-1)*a 21+(1)*a 23+(-1)*a 24+(2)*a 26+(-1)*a 27+(1)*a 29+(-1)*a 30+(1)*a 32+(-1)*a 33+(2)*a 36+(-2)*a 37+(1)*a 38+(-1)*a 41+(1)*a 42+(-1)*a 43+(-1)*a 45+(-1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(-1)*a 52+(-1)*a 54+(-1)*a 55+(-2)*a 56+(1)*a 57+(-1)*a 59+(1)*a 60+(-1)*a 62+(1)*a 63+(1)*a 66+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (51 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow51,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation52 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(2)*a 6+(-2)*a 7+(1)*a 8+(1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(2)*a 16+(-2)*a 17+(1)*a 18+(1)*a 21+(-1)*a 22+(-1)*a 23+(1)*a 25+(1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 31+(-1)*a 32+(1)*a 34+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(-2)*a 40+(1)*a 41+(1)*a 43+(-1)*a 44+(-2)*a 46+(1)*a 47+(1)*a 49+(-1)*a 50+(1)*a 52+(-1)*a 53+(-1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 61+(1)*a 62+(-1)*a 64+(-1)*a 65+(-1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (52 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow52,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation53 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(1)*a 21+(1)*a 22+(1)*a 23+(1)*a 24+(1)*a 25+(1)*a 27+(1)*a 28+(1)*a 29+(1)*a 30+(1)*a 31+(1)*a 32+(1)*a 33+(1)*a 34+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(-2)*a 40+(-1)*a 41+(-1)*a 43+(-2)*a 46+(-1)*a 47+(-1)*a 49+(-1)*a 52+(-1)*a 57+(-1)*a 58+(-1)*a 59+(-1)*a 60+(-1)*a 61+(-1)*a 62+(-1)*a 63+(-1)*a 64+(-1)*a 65+(1)*a 66=0 := by
  have he := congrFun h (53 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow53,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation54 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (-2)*a 2+(-2)*a 3+(-1)*a 4+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-2)*a 10+(-1)*a 11+(-1)*a 13+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-2)*a 20+(-1)*a 21+(-1)*a 23+(-2)*a 26+(-1)*a 27+(-1)*a 29+(-1)*a 32+(2)*a 36+(-1)*a 38+(-1)*a 39+(-1)*a 41+(-1)*a 42+(-1)*a 43+(-1)*a 44+(-1)*a 45+(-1)*a 47+(-1)*a 48+(-1)*a 49+(-1)*a 50+(-1)*a 51+(-1)*a 52+(-1)*a 53+(-1)*a 54+(-1)*a 55+(2)*a 56+(1)*a 57+(1)*a 59+(1)*a 62+(1)*a 66+(1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (54 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow54,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation55 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(1)*a 21+(1)*a 22+(1)*a 23+(1)*a 24+(1)*a 25+(1)*a 27+(1)*a 28+(1)*a 29+(1)*a 30+(1)*a 31+(1)*a 32+(1)*a 33+(1)*a 34+(1)*a 35+(2)*a 36+(2)*a 37+(1)*a 38+(2)*a 40+(1)*a 41+(1)*a 43+(2)*a 46+(1)*a 47+(1)*a 49+(1)*a 52+(-1)*a 57+(-1)*a 58+(-1)*a 59+(-1)*a 60+(-1)*a 61+(-1)*a 62+(-1)*a 63+(-1)*a 64+(-1)*a 65+(-1)*a 66=0 := by
  have he := congrFun h (55 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow55,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation56 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(2)*a 7+(-1)*a 8+(1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 25+(1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 31+(1)*a 32+(1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(-1)*a 39+(-2)*a 40+(1)*a 41+(-1)*a 43+(1)*a 44+(-2)*a 46+(1)*a 47+(-1)*a 49+(1)*a 50+(-1)*a 52+(1)*a 53+(-1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(-1)*a 62+(-1)*a 64+(-1)*a 65+(1)*a 66+(-1)*a 67=0 := by
  have he := congrFun h (56 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow56,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation57 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(-1)*a 8+(-1)*a 9+(1)*a 11+(1)*a 12+(-1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(2)*a 20+(1)*a 21+(-1)*a 23+(-1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(-1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 44+(-1)*a 45+(-2)*a 46+(-1)*a 47+(1)*a 49+(-1)*a 52+(-1)*a 53+(1)*a 54+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 65+(1)*a 66+(1)*a 67+(-1)*a 68=0 := by
  have he := congrFun h (57 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow57,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation58 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(-2)*a 6+(-2)*a 7+(-1)*a 8+(2)*a 10+(1)*a 11+(-1)*a 13+(-2)*a 16+(1)*a 18+(1)*a 19+(-1)*a 21+(-1)*a 22+(1)*a 23+(1)*a 24+(-1)*a 25+(-2)*a 26+(-1)*a 27+(1)*a 29+(-1)*a 32+(-1)*a 33+(1)*a 34+(2)*a 36+(2)*a 37+(1)*a 38+(-2)*a 40+(-1)*a 41+(1)*a 43+(1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 50+(1)*a 51+(-1)*a 52+(-1)*a 55+(2)*a 56+(1)*a 57+(-1)*a 59+(1)*a 62+(1)*a 63+(-1)*a 64+(1)*a 66+(1)*a 69=0 := by
  have he := congrFun h (58 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow58,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation59 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(2)*a 2+(-1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(-1)*a 9+(-1)*a 11+(1)*a 12+(1)*a 13+(-1)*a 14+(1)*a 15+(-2)*a 16+(2)*a 17+(-1)*a 18+(-2)*a 20+(1)*a 21+(-1)*a 23+(1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 30+(-1)*a 31+(1)*a 32+(1)*a 35+(2)*a 36+(-1)*a 38+(1)*a 39+(1)*a 41+(-1)*a 42+(-1)*a 43+(1)*a 44+(-1)*a 45+(2)*a 46+(-1)*a 47+(1)*a 49+(1)*a 52+(-1)*a 53+(1)*a 54+(-1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 65+(-1)*a 66+(1)*a 67+(-1)*a 68=0 := by
  have he := congrFun h (59 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow59,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

#eval IO.println "row 59 done"

lemma evaluation_equation60 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(2)*a 7+(1)*a 8+(-1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(-2)*a 16+(1)*a 18+(1)*a 19+(2)*a 20+(1)*a 21+(-1)*a 23+(-1)*a 24+(1)*a 27+(1)*a 28+(1)*a 29+(-1)*a 31+(1)*a 32+(1)*a 33+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(1)*a 41+(1)*a 42+(1)*a 43+(-1)*a 45+(-2)*a 46+(-1)*a 47+(1)*a 49+(1)*a 50+(-1)*a 52+(1)*a 54+(-1)*a 57+(-1)*a 58+(-1)*a 59+(1)*a 61+(-1)*a 62+(-1)*a 63+(-1)*a 65+(1)*a 66+(-1)*a 68=0 := by
  have he := congrFun h (60 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow60,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation61 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(2)*a 6+(2)*a 7+(1)*a 8+(-1)*a 11+(-1)*a 12+(-1)*a 13+(1)*a 15+(-2)*a 16+(-2)*a 17+(-1)*a 18+(1)*a 21+(1)*a 22+(1)*a 23+(-1)*a 25+(-1)*a 27+(-1)*a 28+(-1)*a 29+(1)*a 31+(1)*a 32+(-1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(2)*a 40+(1)*a 41+(-1)*a 43+(-1)*a 44+(-2)*a 46+(-1)*a 47+(1)*a 49+(1)*a 50+(-1)*a 52+(-1)*a 53+(1)*a 57+(1)*a 58+(1)*a 59+(-1)*a 61+(-1)*a 62+(1)*a 64+(-1)*a 65+(1)*a 66+(1)*a 67=0 := by
  have he := congrFun h (61 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow61,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation62 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(1)*a 8+(1)*a 9+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(2)*a 16+(-1)*a 18+(-1)*a 19+(-1)*a 21+(-1)*a 22+(-1)*a 23+(-1)*a 24+(-1)*a 25+(1)*a 27+(1)*a 28+(1)*a 29+(1)*a 30+(1)*a 31+(-1)*a 32+(-1)*a 33+(-1)*a 34+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(1)*a 41+(1)*a 42+(1)*a 43+(1)*a 44+(1)*a 45+(-1)*a 47+(-1)*a 48+(-1)*a 49+(-1)*a 50+(-1)*a 51+(1)*a 52+(1)*a 53+(1)*a 54+(-1)*a 55+(1)*a 57+(1)*a 58+(1)*a 59+(1)*a 60+(1)*a 61+(-1)*a 62+(-1)*a 63+(-1)*a 64+(1)*a 65+(1)*a 66+(1)*a 67+(1)*a 68+(-1)*a 69=0 := by
  have he := congrFun h (62 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow62,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation63 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (2)*a 2+(2)*a 3+(1)*a 4+(2)*a 6+(2)*a 7+(1)*a 8+(2)*a 10+(1)*a 11+(1)*a 13+(-2)*a 16+(-2)*a 17+(-1)*a 18+(-2)*a 20+(-1)*a 21+(-1)*a 23+(2)*a 26+(1)*a 27+(1)*a 29+(-1)*a 32+(2)*a 36+(2)*a 37+(1)*a 38+(2)*a 40+(1)*a 41+(1)*a 43+(-2)*a 46+(-1)*a 47+(-1)*a 49+(1)*a 52+(2)*a 56+(1)*a 57+(1)*a 59+(-1)*a 62+(1)*a 66=0 := by
  have he := congrFun h (63 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow63,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation64 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(2)*a 16+(2)*a 17+(1)*a 18+(1)*a 21+(1)*a 22+(-1)*a 23+(-1)*a 25+(-1)*a 27+(-1)*a 28+(1)*a 29+(1)*a 31+(-1)*a 32+(-1)*a 34+(1)*a 35+(-2)*a 36+(-2)*a 37+(-1)*a 38+(-1)*a 41+(-1)*a 42+(1)*a 43+(1)*a 45+(1)*a 47+(1)*a 48+(-1)*a 49+(-1)*a 51+(1)*a 52+(1)*a 54+(-1)*a 55+(-1)*a 57+(-1)*a 58+(1)*a 59+(1)*a 61+(-1)*a 62+(-1)*a 64+(1)*a 65+(1)*a 66+(1)*a 68+(-1)*a 69=0 := by
  have he := congrFun h (64 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow64,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation65 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(-4)*a 1+(-2)*a 2+(1)*a 4+(1)*a 5+(-2)*a 6+(-2)*a 7+(-1)*a 8+(-1)*a 11+(-1)*a 12+(1)*a 13+(1)*a 15+(2)*a 16+(-1)*a 18+(-1)*a 19+(2)*a 20+(1)*a 21+(1)*a 23+(1)*a 24+(1)*a 27+(1)*a 28+(-1)*a 29+(-1)*a 31+(-1)*a 32+(-1)*a 33+(1)*a 35+(-2)*a 36+(1)*a 38+(1)*a 39+(-2)*a 40+(-1)*a 41+(-1)*a 43+(-1)*a 44+(-1)*a 47+(-1)*a 48+(1)*a 49+(1)*a 51+(1)*a 52+(1)*a 53+(-1)*a 55+(1)*a 57+(1)*a 58+(-1)*a 59+(-1)*a 61+(-1)*a 62+(-1)*a 63+(1)*a 65+(1)*a 66+(1)*a 67+(-1)*a 69=0 := by
  have he := congrFun h (65 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow65,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation66 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(1)*a 1+(1)*a 2+(-2)*a 4+(-4)*a 5+(1)*a 6+(1)*a 7+(-2)*a 9+(1)*a 10+(1)*a 11+(1)*a 13+(1)*a 14+(1)*a 15+(1)*a 16+(1)*a 17+(-2)*a 19+(1)*a 20+(1)*a 21+(1)*a 23+(1)*a 24+(1)*a 25+(1)*a 26+(1)*a 27+(1)*a 29+(1)*a 30+(1)*a 31+(1)*a 32+(1)*a 33+(1)*a 34+(1)*a 35+(1)*a 36+(1)*a 37+(-2)*a 39+(1)*a 40+(1)*a 41+(1)*a 43+(1)*a 44+(1)*a 45+(1)*a 46+(1)*a 47+(1)*a 49+(1)*a 50+(1)*a 51+(1)*a 52+(1)*a 53+(1)*a 54+(1)*a 55+(1)*a 56+(1)*a 57+(1)*a 59+(1)*a 60+(1)*a 61+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 65+(1)*a 66+(1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (66 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow66,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation67 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(1)*a 1+(1)*a 2+(1)*a 3+(1)*a 4+(1)*a 5+(1)*a 6+(1)*a 7+(1)*a 8+(1)*a 9+(-2)*a 13+(-2)*a 14+(-4)*a 15+(1)*a 16+(1)*a 17+(1)*a 18+(1)*a 19+(1)*a 20+(1)*a 21+(1)*a 22+(-2)*a 25+(1)*a 26+(1)*a 27+(1)*a 28+(1)*a 29+(1)*a 30+(1)*a 32+(1)*a 33+(1)*a 34+(1)*a 35+(1)*a 36+(1)*a 37+(1)*a 38+(1)*a 39+(1)*a 40+(1)*a 41+(1)*a 42+(-2)*a 45+(1)*a 46+(1)*a 47+(1)*a 48+(1)*a 49+(1)*a 50+(1)*a 52+(1)*a 53+(1)*a 54+(1)*a 55+(1)*a 56+(1)*a 57+(1)*a 58+(1)*a 59+(1)*a 60+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 65+(1)*a 66+(1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (67 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow67,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

lemma evaluation_equation68 (a : Fin 70 → ℤ) (h : evaluationMatrix *ᵥ a=0) : (1)*a 0+(1)*a 1+(1)*a 2+(1)*a 3+(1)*a 4+(1)*a 5+(1)*a 6+(1)*a 7+(1)*a 8+(1)*a 9+(1)*a 10+(1)*a 11+(1)*a 12+(1)*a 13+(1)*a 14+(1)*a 15+(1)*a 16+(1)*a 17+(1)*a 18+(1)*a 19+(1)*a 20+(1)*a 21+(1)*a 22+(1)*a 23+(1)*a 24+(1)*a 25+(-2)*a 32+(-2)*a 33+(-2)*a 34+(-4)*a 35+(1)*a 36+(1)*a 37+(1)*a 38+(1)*a 39+(1)*a 40+(1)*a 41+(1)*a 42+(1)*a 43+(1)*a 44+(1)*a 45+(1)*a 46+(1)*a 47+(1)*a 48+(1)*a 49+(1)*a 50+(1)*a 51+(-2)*a 55+(1)*a 56+(1)*a 57+(1)*a 58+(1)*a 59+(1)*a 60+(1)*a 61+(1)*a 62+(1)*a 63+(1)*a 64+(1)*a 66+(1)*a 67+(1)*a 68+(1)*a 69=0 := by
  have he := congrFun h (68 : Fin 69)
  norm_num [Matrix.mulVec,dotProduct,evaluationMatrix,evaluationData,evaluationRow68,Fin.sum_univ_succ] at he
  linear_combination (norm := ring_nf!) he

end Erdos322Research.QuarticFiveInputDegreeFour
