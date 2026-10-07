import OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275.StabilizedCollapse

/-!
Human review entry point. After the README's bootstrap build, run from
artifact/lean: lake env lean ../ReadStatement.lean
The proof audit is performed separately by the root verify_artifact.py.
-/

open OpenQ.Problems.AmortizationCollapseSuperchannelDivergences_148275

set_option pp.proofs false

#check referenceStabilized_collapse
#print ReferenceStabilizedMainStatement
#print referenceStabilizedOrdinaryDivergence
#print referenceStabilizedAmortizedDivergence
#print amortizedChannelDivergence
#print Channel
#print OpenQ.Problems.EqualWeightLowChoiRank_523ed7.IsCPTP
#print OpenQ.Problems.EqualWeightLowChoiRank_523ed7.IsCompletelyPositive
#print OpenQ.IsDensityMatrix
#print PhysicalSuperchannel
#print PhysicalSuperchannel.act
#print PhysicalSuperchannel.referenceRealization
#print PhysicalSuperchannel.referenceAct
#print PhysicalSuperchannel.referenceOnChannel
#print RangeIncluded
#print supportInvSqrtScalar
#print supportInvSqrt
#print hermitianPower
#print geometricMoment
#print geometricStateDivergence
#print axioms referenceStabilized_collapse
