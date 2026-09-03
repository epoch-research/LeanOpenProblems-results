import Submission.DoublePetersenGraph
open SimpleGraph
open scoped Classical
open Erdos184Work Erdos184Work.DoublePetersenGraph
set_option pp.explicit true in
#print PathSubstitution.Family.expandEdges
set_option pp.explicit true in
#check (Finset.card_biUnion)
