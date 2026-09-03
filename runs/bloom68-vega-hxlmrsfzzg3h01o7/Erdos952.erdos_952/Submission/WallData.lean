import Submission.WallDataPart00
import Submission.WallDataPart01
import Submission.WallDataPart02
import Submission.WallDataPart03
import Submission.WallDataPart04
import Submission.WallDataPart05
import Submission.WallDataPart06
import Submission.WallDataPart07
import Submission.WallDataPart08
import Submission.WallDataPart09
import Submission.WallDataPart10
import Submission.WallDataPart11
import Submission.WallDataPart12
import Submission.WallDataPart13
import Submission.WallDataPart14
import Submission.WallDataPart15
import Submission.WallDataPart16
import Submission.WallDataPart17
import Submission.WallDataPart18
import Submission.WallDataPart19
import Submission.WallDataPart20
import Submission.WallDataPart21
import Submission.WallDataPart22
import Submission.WallDataPart23
import Submission.WallDataPart24
import Submission.WallDataPart25
import Submission.WallDataPart26
import Submission.WallDataPart27

/-!
# Kernel-certified finite black wall in the w lattice

This is ONLY a certificate for the supplied finite path. It is not an arbitrary-D
obstruction, a Gaussian-prime path, or a solution of the Gaussian moat problem.
No existing Submission module, in particular Spec, is imported or modified.

The 1,812,224 original vertex bytes are encoded losslessly in 443 chunks,
with one overlapping vertex between consecutive chunks. Each chunk is accepted
by `decide +kernel`; exact-length path proofs are concatenated at checked endpoints.
-/

namespace Erdos952.WallData

/-- Initial vertex in w coordinates. -/
def start : GaussianInt := ⟨146, -149⟩

/-- Final vertex in w coordinates. -/
def finish : GaussianInt := ⟨576956, 95986⟩

/-- All 1,812,223 edges of the supplied path, with both endpoints black. -/
theorem wall_path_exact : BlackPath 1812223 start finish :=
  ((((Part00.path).append ((Part01.path).append (Part02.path))).append (((Part03.path).append (Part04.path)).append ((Part05.path).append (Part06.path)))).append (((Part07.path).append ((Part08.path).append (Part09.path))).append (((Part10.path).append (Part11.path)).append ((Part12.path).append (Part13.path))))).append ((((Part14.path).append ((Part15.path).append (Part16.path))).append (((Part17.path).append (Part18.path)).append ((Part19.path).append (Part20.path)))).append (((Part21.path).append ((Part22.path).append (Part23.path))).append (((Part24.path).append (Part25.path)).append ((Part26.path).append (Part27.path)))))

/-- The requested black nearest-neighbor reachability statement. -/
theorem wall_path :
    Relation.ReflTransGen
      (fun p q : GaussianInt => Black p ∧ Black q ∧ (q - p).norm = 1)
      start finish :=
  wall_path_exact.toRTC

theorem start_black : Black start := wall_path_exact.black_start

theorem finish_black : Black finish := wall_path_exact.black_end

/-- The winding displacement recorded in the original metadata. -/
theorem wall_displacement : finish - start = (⟨576810, 96135⟩ : GaussianInt) := by
  decide +kernel

end Erdos952.WallData
