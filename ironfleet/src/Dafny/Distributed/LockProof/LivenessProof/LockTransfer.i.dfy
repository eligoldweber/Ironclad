include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Logic/Temporal/LeadsTo.i.dfy"
include "LockNext.i.dfy"
include "Assumptions.i.dfy"
include "Defs.i.dfy"

module Lock__LivenessProof__LockTransfer_i {

import opened DistributedSystem_i
import opened Lock__LivenessProof__Assumptions_i
import opened Lock__LivenessProof__LockNext_i
import opened Lock__LivenessProof__Defs_i
import opened Temporal__LeadsTo_i

lemma LockedImpliesLockedNextPositionLemma(b:Behavior<LS_State>, i:int, epoch:int, config:Config, asp:AssumptionParameters) 
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
requires 0 <= i < |config| - 1
ensures sat(0, always(LockedImpliesLockedAtNextPositionTemporal(b, i, epoch, config)))
{
    LockEventuallyTransferToNextNode(b, i, epoch, config, asp);
}


lemma LockedImpliesLockedForAllAfterLemma(b:Behavior<LS_State>, i:int, epoch:int, config:Config, asp:AssumptionParameters) 
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
requires 0 <= i < |config| - 1
ensures sat(0, always(LockedImpliesLockedForAllAfterTemporal(b, i, epoch, config)))
{
    forall t |
           t >= 0
    ensures sat(t, LockedImpliesLockedForAllAfterTemporal(b, i, epoch, config))
    {
        reveal_or();
        if (sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config))
         || sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)))
        {
            assert LockedIthPositionWithEpoch(b[t], i, epoch, config)
                || LockedIthPositionWithHigherEpoch(b[t], i, epoch, config);

            forall j |
                   i < j < |config|
            ensures sat(t, eventual(LockedIthPositionWithHigherEpochTemporal(b, j, epoch, config)))
            {
                reveal_always();
                reveal_imply();
                reveal_eventual();
                var k := i;
                var step := t;
                while (k < j) 
                invariant i <= k <= j
                invariant sat(step, or(LockedIthPositionWithEpochTemporal(b, k, epoch, config),
                                    LockedIthPositionWithHigherEpochTemporal(b, k, epoch, config)))
                invariant i < k ==> sat(step, LockedIthPositionWithHigherEpochTemporal(b, k, epoch, config))
                invariant step >= t;
                {
                    LockedImpliesLockedNextPositionLemma(b, k, epoch, config, asp);
                    assert sat(step, LockedImpliesLockedAtNextPositionTemporal(b, k, epoch, config));
                    assert sat(step, eventual(LockedIthPositionWithHigherEpochTemporal(b, k+1, epoch, config)));
                    step := eventualStep(step, LockedIthPositionWithHigherEpochTemporal(b, k+1, epoch, config));
                    k := k + 1;
                }
            }

            assert sat(t, EventuallyLockedForAllAfterTemporal(b, i, epoch, config));
        }
        reveal_imply();
    }
    reveal_always();
}


lemma LockedLastImpliesLockedFirstLemma(b:Behavior<LS_State>, epoch:int, config:Config, asp:AssumptionParameters)
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
ensures sat(0, always(LockedLastImpliesLockedFirstTemporal(b, epoch, config)))
{
    LockEventuallyTransferToNextNode(b, |config|-1, epoch, config, asp);
}

lemma LockedForAllAfterImpliesLockedForIthPositionLemma(b:Behavior<LS_State>, t:int, i:int, j:int, epoch:int, config:Config)
requires i < j < |config|
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config| - 1
requires sat(t, EventuallyLockedForAllAfterTemporal(b, i, epoch, config))
ensures sat(t, eventual(LockedIthPositionWithHigherEpochTemporal(b, j, epoch, config)))
{
}


}



