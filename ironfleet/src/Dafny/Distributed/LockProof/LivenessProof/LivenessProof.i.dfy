include "Assumptions.i.dfy"
include "LockTransfer.i.dfy"
include "../../Common/Logic/Temporal/Rules.i.dfy"

module Lock__LivenessProof__LivenessProof_i {

import opened Lock__LivenessProof__Assumptions_i
import opened Lock__LivenessProof__LockTransfer_i
import opened Temporal__Rules_i

predicate LockedWithEpoch(ls:LS_State, x:EndPoint, epoch:int) {
    exists p :: 
           p in ls.environment.sentPackets
        && p.src == x
        && p.msg.Locked?
        && p.msg.locked_epoch == epoch
}

predicate LockedWithHigherEpoch(ls:LS_State, x:EndPoint, epoch:int) {
    exists p, epoch'::
           epoch' > epoch
        && p in ls.environment.sentPackets
        && p.src == x
        && p.msg.Locked?
        && p.msg.locked_epoch == epoch'
}

function LockedWithEpochTemporal(b:Behavior<LS_State>, x:EndPoint, epoch:int) : temporal
requires imaptotal(b)
ensures forall i {:trigger sat(i, LockedWithEpochTemporal(b, x, epoch))} ::
               sat(i, LockedWithEpochTemporal(b, x, epoch)) <==> LockedWithEpoch(b[i], x, epoch)
{
    stepmap(imap i :: LockedWithEpoch(b[i], x, epoch))
}

function LockedWithHigherEpochTemporal(b:Behavior<LS_State>, x:EndPoint, epoch:int) : temporal
requires imaptotal(b)
ensures forall i {:trigger sat(i, LockedWithHigherEpochTemporal(b, x, epoch))} ::
               sat(i, LockedWithHigherEpochTemporal(b, x, epoch)) <==> LockedWithHigherEpoch(b[i], x, epoch)
{
    stepmap(imap i :: LockedWithHigherEpoch(b[i], x, epoch))
}

function EventuallyLockedWithHigherEpochTemporal(b:Behavior<LS_State>, x:EndPoint, epoch:int) : temporal
requires imaptotal(b)
{
    eventual(LockedWithHigherEpochTemporal(b, x, epoch))
}

function EventuallyLockedAgainTemporal(b:Behavior<LS_State>, x:EndPoint, epoch:int) : temporal
requires imaptotal(b)
{
    imply(LockedWithEpochTemporal(b, x, epoch), EventuallyLockedWithHigherEpochTemporal(b, x, epoch))
}

predicate LivenessProperty(b:Behavior<LS_State>, config:Config)
requires imaptotal(b)
{
    forall epoch, x :: 
           epoch >= 0
        && x in config
       ==> sat(0, always(EventuallyLockedAgainTemporal(b, x, epoch)))
}


lemma FindPosition(x:EndPoint, config:Config) returns (t:int)
requires x in config
ensures 0 <= t < |config|
ensures x == config[t]
{
    t :| 0 <= t < |config| && config[t] == x;
}

lemma LockPositionToLockEndPoint(b:Behavior<LS_State>, x:EndPoint, i:int, epoch:int, config:Config, t:int)
requires |config| > 0
requires 0 <= i < |config|
requires config[i] == x
requires imaptotal(b)
requires sat(t, eventual(LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)))
ensures sat(t, eventual(LockedWithHigherEpochTemporal(b, x, epoch)))
{
    var step := eventualStep(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config));
    assert sat(step, LockedWithHigherEpochTemporal(b, x, epoch));
    reveal_eventual();
}

lemma LivenessProof(b:Behavior<LS_State>, config:Config, asp:AssumptionParameters) 
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
ensures LivenessProperty(b, config)
{
    reveal_always();
    forall epoch, x |
           epoch >= 0
        && x in config
    ensures sat(0, always(EventuallyLockedAgainTemporal(b, x, epoch)))
    {
        forall j |
               0 <= j
        ensures sat(j, EventuallyLockedAgainTemporal(b, x, epoch))
        {
            if (sat(j, LockedWithEpochTemporal(b, x, epoch))) {
                var t := FindPosition(x, config);
                assert sat(j, LockedIthPositionWithEpochTemporal(b, t, epoch, config));

                reveal_imply();
                if (t < |config| - 1)
                {
                    reveal_eventual();
                    LockedImpliesLockedForAllAfterLemma(b, t, epoch, config, asp);
                    assert sat(j, LockedImpliesLockedForAllAfterTemporal(b, t, epoch, config));
                    assert sat(j, EventuallyLockedForAllAfterTemporal(b, t, epoch, config));

                    LockedForAllAfterImpliesLockedForIthPositionLemma(
                        b, 
                        j,
                        t, 
                        |config|-1, 
                        epoch, 
                        config);
                    assert sat(j, eventual(LockedIthPositionWithHigherEpochTemporal(b, |config|-1, epoch, config)));

                    assert sat(j, eventual(LockedIthPositionWithHigherEpochTemporal(b, |config|-1, epoch, config)));
                    LockedLastImpliesLockedFirstLemma(b, epoch, config, asp);

                    assert sat(j, eventual(LockedIthPositionWithHigherEpochTemporal(b, 0, epoch, config)));
                } else {
                    assert t == |config| - 1;
                    LockedLastImpliesLockedFirstLemma(b, epoch, config, asp);
                    assert sat(j, eventual(LockedIthPositionWithHigherEpochTemporal(b, 0, epoch, config)));
                }

                if (t == 0) {
                    assert sat(j, eventual(LockedIthPositionWithHigherEpochTemporal(b, t, epoch, config)));
                } else {

                    reveal_imply();
                    reveal_eventual();
                    LockedImpliesLockedForAllAfterLemma(b, 0, epoch, config, asp);
                    
                    assert sat(j, EventuallyLockedForAllAfterTemporal(b, 0, epoch, config));

                    LockedForAllAfterImpliesLockedForIthPositionLemma(b, j, 0, t, epoch, config);

                    assert sat(j, eventual(LockedIthPositionWithHigherEpochTemporal(b, t, epoch, config)));
                }


                LockPositionToLockEndPoint(b, x, t, epoch, config, j);

                assert sat(j, eventual(LockedWithHigherEpochTemporal(b, x, epoch)));
            }
        }
    }
}



}
