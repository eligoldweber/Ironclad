include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Logic/Temporal/LeadsTo.i.dfy"
include "Assumptions.i.dfy"

module Lock__LivenessProof__Defs_i {

import opened DistributedSystem_i
import opened Math__mod_auto_i
import opened Temporal__LeadsTo_i
import opened Lock__LivenessProof__Assumptions_i


//================ Functions ==================

function NextNode(i:int, config:Config) : int
requires 0 <= i < |config|
requires |config| > 0
ensures 0 <= NextNode(i, config) < |config|
ensures 0 <= i < |config| - 1 ==> NextNode(i, config) == i + 1
ensures i == |config| - 1 ==> NextNode(i, config) == 0
{
    lemma_mod_auto(|config|);
    (i + 1) % |config|
}



//================ Predicates ==================



predicate ValidBehavior(b:Behavior<LS_State>, config:Config) {
    imaptotal(b)
 && LS_Init(b[0], config)
 && forall i :: i >= 0 ==> LS_Next(b[i], b[i+1])
}

predicate LockedIthPositionWithEpoch(ls:LS_State, i:int, epoch:int, config:Config) 
requires |config| > 0
requires 0 <= i < |config|
{
    exists p :: 
           p in ls.environment.sentPackets
        && p.src == config[i]
        && p.msg.Locked?
        && p.msg.locked_epoch == epoch
}

predicate LockedIthPositionWithHigherEpoch(ls:LS_State, i:int, epoch:int, config:Config) 
requires |config| > 0
requires 0 <= i < |config|
{
    exists p, epoch'::
           epoch' > epoch
        && p in ls.environment.sentPackets
        && p.src == config[i] 
        && p.msg.Locked?
        && p.msg.locked_epoch == epoch'
}

predicate EventuallyLockedForAllAfter(b:Behavior<LS_State>, t:int, i:int, epoch:int, config:Config) 
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
{
    forall j ::
           i < j < |config|
       ==> sat(t, eventual(LockedIthPositionWithHigherEpochTemporal(b, j, epoch, config)))
}

predicate NodeGrantPacket(ls:LS_State, i:int, epoch:int, config:Config)
requires 0 <= i < |config|
{
       ls.environment.nextStep.LEnvStepHostIos?
    && exists p : LockPacket ::
              LIoOpSend(p) in ls.environment.nextStep.ios
           && p.src == config[i]
           && p.dst == config[NextNode(i, config)]
           && p.msg.Transfer?
           && p.msg.transfer_epoch == epoch
}

//================== Temporals ====================



function LockedIthPositionWithEpochTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
ensures forall t {:trigger sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config))} ::
               sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config)) <==> LockedIthPositionWithEpoch(b[t], i, epoch, config)
{
    stepmap(imap t :: LockedIthPositionWithEpoch(b[t], i, epoch, config))
}

function LockedIthPositionWithHigherEpochTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
ensures forall t {:trigger sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config))} ::
               sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)) <==> LockedIthPositionWithHigherEpoch(b[t], i, epoch, config)
{
    stepmap(imap t :: LockedIthPositionWithHigherEpoch(b[t], i, epoch, config))
}

function EventuallyLockedForAllAfterTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
ensures forall t {:trigger sat(t, EventuallyLockedForAllAfterTemporal(b, i, epoch, config))} ::
               sat(t, EventuallyLockedForAllAfterTemporal(b, i, epoch, config)) <==> EventuallyLockedForAllAfter(b, t, i, epoch, config)
{
    stepmap(imap t :: EventuallyLockedForAllAfter(b, t, i, epoch, config))
}



function LockedImpliesLockedAtNextPositionTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config| - 1
{
    imply(or(LockedIthPositionWithEpochTemporal(b, i, epoch, config),
               LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)), 
            eventual(LockedIthPositionWithHigherEpochTemporal(b, i+1, epoch, config)))
}


function LockedImpliesLockedForAllAfterTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config| - 1
{
    imply(
        or(
            LockedIthPositionWithEpochTemporal(b, i, epoch, config), 
            LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)),
        EventuallyLockedForAllAfterTemporal(b, i, epoch, config))
}

function LockedLastImpliesLockedFirstTemporal(b:Behavior<LS_State>, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
{
    imply(
        or(
            LockedIthPositionWithEpochTemporal(b, |config|-1, epoch, config),
            LockedIthPositionWithHigherEpochTemporal(b, |config|-1, epoch, config)),
        eventual(LockedIthPositionWithHigherEpochTemporal(b, 0, epoch, config)))
}


function LockTransferToNextNode(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
{
    imply(or(LockedIthPositionWithEpochTemporal(b, i, epoch, config),
               LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)), 
          eventual(LockedIthPositionWithHigherEpochTemporal(b, NextNode(i, config), epoch, config)))
}


function NodeGrantPacketTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
ensures forall t {:trigger sat(t, NodeGrantPacketTemporal(b, i, epoch, config))} :: 
               sat(t, NodeGrantPacketTemporal(b, i, epoch, config)) <==> NodeGrantPacket(b[t], i, epoch, config)
{
    stepmap(imap t :: NodeGrantPacket(b[t], i, epoch, config))
}

function EventualNodeGrantPacketTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
{
    eventual(NodeGrantPacketTemporal(b, i, epoch, config))
}

function LockedImpliesGrantTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
{
    imply(LockedIthPositionWithEpochTemporal(b, i, epoch, config),
          EventualNodeGrantPacketTemporal(b, i, epoch+1, config))
}

function TransferDeliveredLeadsToLockedTemporal(b:Behavior<LS_State>, p:LockPacket, i:int, config:Config) : temporal
requires imaptotal(b)
requires 0 <= i < |config|
requires p.dst == config[i]
requires p.msg.Transfer?
{
    imply(PacketDeliveredTemporal(BehaviorToLEnvMap(b), p),
          next(LockedIthPositionWithEpochTemporal(b, i, p.msg.transfer_epoch, config)))
}

}
