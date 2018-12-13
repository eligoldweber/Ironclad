include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Logic/Temporal/LeadsTo.i.dfy"
include "../../Common/Framework/EnvironmentSynchrony.s.dfy"

module Lock__LivenessProof__Defs_i {

import opened DistributedSystem_i
import opened Math__mod_auto_i
import opened Temporal__LeadsTo_i
import opened EnvironmentSynchrony_s

datatype AssumptionParameters = AssumptionParameters()

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


predicate ValidTransferPacket(p:LockPacket, config:Config)
{
    p.msg.Transfer?
 && p.src in config
 && p.dst in config
}

predicate UsefulTransfer(p:LockPacket, node:EndPoint, config:Config, ls:LS_State)
{
    ValidTransferPacket(p, config)
 && p.dst == node
 && node in ls.servers
 && p.msg.transfer_epoch > ls.servers[node].epoch
}


predicate ValidBehavior(b:Behavior<LS_State>, config:Config) {
    imaptotal(b)
 && LS_Init(b[0], config)
 && forall i :: i >= 0 ==> LS_Next(b[i], b[i+1])
}

predicate PacketsEventuallyDeliveredForHosts(
    b:Behavior<LEnvironment<EndPoint, LockMessage>>,
    i:int,
    serverAddresses:set<EndPoint>
    )
    requires imaptotal(b)
{
    forall p {:triger PacketSentBetweenHosts(b[i], p, serverAddresses, serverAddresses)} ::
        PacketSentBetweenHosts(b[i], p, serverAddresses, serverAddresses) ==>
        sat(i, next(eventual(PacketDeliveredTemporal(b, p))))
}

predicate PacketReceived(ls:LS_State, p:LockPacket)
{
    ls.environment.nextStep.LEnvStepHostIos?
 && LIoOpReceive(p) in ls.environment.nextStep.ios
}

predicate IosStep(ls:LS_State) 
{
       ls.environment.nextStep.LEnvStepHostIos?
    && ls.environment.nextStep.actor in ls.servers
}

predicate NodeGrantOccursForServer(ls:LS_State, ls':LS_State, node:EndPoint)
{
    node in ls.servers
 && node in ls'.servers
 && ls.environment.nextStep.LEnvStepHostIos?
 && node == ls.environment.nextStep.actor
 && NodeGrant(ls.servers[node], ls'.servers[node], ls.environment.nextStep.ios)
}

predicate NodeAcceptOccursForServer(ls:LS_State, ls':LS_State, node:EndPoint)
{
    node in ls.servers
 && node in ls'.servers
 && ls.environment.nextStep.LEnvStepHostIos?
 && node == ls.environment.nextStep.actor
 && NodeAccept(ls.servers[node], ls'.servers[node], ls.environment.nextStep.ios)
}

predicate HoldLockForNode(ls:LS_State, node:EndPoint)
{
    node in ls.servers
 && ls.servers[node].held
}

predicate HoldLockForNodeWithEpoch(ls:LS_State, node:EndPoint, epoch:int)
{
    HoldLockForNode(ls, node)
 && ls.servers[node].epoch == epoch
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
       ==> sat(t, eventual(LockedIthPositionWithEpochTemporal(b, j, epoch + j - i, config)))
}

predicate NodeGrantPacket(ls:LS_State, i:int, epoch:int, config:Config)
requires 0 <= i < |config|
{
    exists p : LockPacket ::
           p in ls.environment.sentPackets
        && p.src == config[i]
        && p.dst == config[NextNode(i, config)]
        && p.msg.Transfer?
        && p.msg.transfer_epoch == epoch
}

predicate TransferSent(ls:LS_State, node:EndPoint, epoch:int)
{
    node in ls.servers
 && ls.environment.nextStep.LEnvStepHostIos?
 && var actor := ls.environment.nextStep.actor;
    var ios := ls.environment.nextStep.ios;
    |ios| == 1
 && ios[0].LIoOpSend?
 && var p := ios[0].s;
    p.msg.Transfer?
 && p.msg.transfer_epoch == epoch
}

predicate LargestEpoch(ls:LS_State, epoch:int)
{
    forall node ::
           node in ls.servers
       ==> ls.servers[node].epoch < epoch
}

predicate ReceiveStep(ls:LS_State, node:EndPoint)
{
    ls.environment.nextStep.LEnvStepHostIos?
 && node == ls.environment.nextStep.actor
 && |ls.environment.nextStep.ios| > 0
 && var ios := ls.environment.nextStep.ios;
    (ios[0].LIoOpReceive? || ios[0].LIoOpTimeoutReceive?)
}

//================== Temporals ====================


function PacketsEventuallyDeliveredForHostsTemporal(
    b:Behavior<LEnvironment<EndPoint,LockMessage>>,
    serverAddresses:set<EndPoint>
    ) : temporal 
    requires imaptotal(b)
    ensures forall i {:trigger sat(i, PacketsEventuallyDeliveredForHostsTemporal(b, serverAddresses))} ::
        sat(i, PacketsEventuallyDeliveredForHostsTemporal(b, serverAddresses)) <==> 
        PacketsEventuallyDeliveredForHosts(b, i, serverAddresses)
{
    stepmap(imap i :: PacketsEventuallyDeliveredForHosts(b, i, serverAddresses))
}

function PacketReceivedTemporal(b:Behavior<LS_State>, p:LockPacket) : temporal
requires imaptotal(b)
ensures forall i {:trigger sat(i, PacketReceivedTemporal(b, p))} :: sat(i, PacketReceivedTemporal(b, p)) <==> PacketReceived(b[i], p)
{
    stepmap(imap i :: PacketReceived(b[i], p))
}

function PacketDeliveredLeadsToReceived(b:Behavior<LS_State>, p:LockPacket) : temporal
requires imaptotal(b)
{
    imply(
        PacketDeliveredTemporal(BehaviorToLEnvMap(b), p),
        next(eventual(PacketReceivedTemporal(b, p))))
}

function BehaviorToLEnvMap(b:Behavior<LS_State>) : imap<int, LEnvironment<EndPoint, LockMessage>>
requires imaptotal(b)
ensures imaptotal(BehaviorToLEnvMap(b))
ensures forall i {:trigger BehaviorToLEnvMap(b)[i]} :: BehaviorToLEnvMap(b)[i] == b[i].environment
{
    imap i :: b[i].environment
}

function IosStepTemporal(b:Behavior<LS_State>) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, IosStepTemporal(b))} ::
               sat(t, IosStepTemporal(b)) <==> IosStep(b[t])
{
    stepmap(imap t :: IosStep(b[t]))
}


function EventuallyIosStepTemporal(b:Behavior<LS_State>) : temporal
requires imaptotal(b)
{
    eventual(IosStepTemporal(b))
}

function NodeGrantOccursForServerTemporal(b:Behavior<LS_State>, node:EndPoint) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, NodeGrantOccursForServerTemporal(b, node))} ::
               sat(t, NodeGrantOccursForServerTemporal(b, node)) <==> NodeGrantOccursForServer(b[t], b[t+1], node)
{
    stepmap(imap t :: NodeGrantOccursForServer(b[t], b[t+1], node))
}

function NodeAcceptOccursForServerTemporal(b:Behavior<LS_State>, node:EndPoint) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, NodeAcceptOccursForServerTemporal(b, node))} ::
               sat(t, NodeAcceptOccursForServerTemporal(b, node)) <==> NodeAcceptOccursForServer(b[t], b[t+1], node)
{
    stepmap(imap t :: NodeAcceptOccursForServer(b[t], b[t+1], node))
}

function HoldLockForNodeTemporal(b:Behavior<LS_State>, node:EndPoint) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, HoldLockForNodeTemporal(b, node))} :: sat(t, HoldLockForNodeTemporal(b, node)) <==> HoldLockForNode(b[t], node)
{
    stepmap(imap t :: HoldLockForNode(b[t], node))
}

function HoldLockForNodeWithEpochTemporal(b:Behavior<LS_State>, node:EndPoint, epoch:int) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, HoldLockForNodeWithEpochTemporal(b, node, epoch))} :: sat(t, HoldLockForNodeWithEpochTemporal(b, node, epoch)) <==> HoldLockForNodeWithEpoch(b[t], node, epoch)
{
    stepmap(imap t :: HoldLockForNodeWithEpoch(b[t], node, epoch))
}



function ActionOccursForServerTemporal(b:Behavior<LS_State>, node:EndPoint) : temporal
requires imaptotal(b)
{
//     and(
//         imply(HoldLockForNodeWithEpochTemporal(b, node, epoch),
//               eventual(and(HoldLockForNodeWithEpochTemporal(b, node, epoch),
//                            NodeGrantOccursForServerTemporal(b, node)))),
//         imply(not(HoldLockForNodeTemporal(b, node)),
//               eventual(and(not(HoldLockForNodeTemporal(b,node)),
//                            NodeAcceptOccursForServerTemporal(b, node)))))
    and(
        eventual(
            NodeGrantOccursForServerTemporal(b, node)),
        eventual(
            NodeAcceptOccursForServerTemporal(b, node)))
}


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

function EpochUpperBound(epoch:int, ub:int) : temporal
{
    stepmap(imap i :: epoch < ub)
}



function LockedImpliesLockedAtNextPositionTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config| - 1
{
    imply(LockedIthPositionWithEpochTemporal(b, i, epoch, config),
            eventual(LockedIthPositionWithEpochTemporal(b, i+1, epoch+1, config)))
}


function LockedImpliesLockedForAllAfterTemporal(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config| - 1
{
    imply(
        LockedIthPositionWithEpochTemporal(b, i, epoch, config), 
        EventuallyLockedForAllAfterTemporal(b, i, epoch, config))
}

function LockedLastImpliesLockedFirstTemporal(b:Behavior<LS_State>, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
{
    imply(
        LockedIthPositionWithEpochTemporal(b, |config|-1, epoch, config),
        eventual(LockedIthPositionWithEpochTemporal(b, 0, epoch+1, config)))
}


function LockTransferToNextNode(b:Behavior<LS_State>, i:int, epoch:int, config:Config) : temporal
requires imaptotal(b)
requires |config| > 0
requires 0 <= i < |config|
{
    imply(LockedIthPositionWithEpochTemporal(b, i, epoch, config),
          eventual(LockedIthPositionWithEpochTemporal(b, NextNode(i, config), epoch+1, config)))
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
          next(eventual(LockedIthPositionWithEpochTemporal(b, i, p.msg.transfer_epoch, config))))
}

function NotHeldUntilAcceptTemporal(b:Behavior<LS_State>, node:EndPoint) : temporal
requires imaptotal(b)
{
        imply(NodeAcceptOccursForServerTemporal(b, node),
                     not(HoldLockForNodeTemporal(b, node)))
            
}


function TransferSentTemporal(b:Behavior<LS_State>, node:EndPoint, epoch:int) : temporal
requires imaptotal(b) 
ensures forall t {:trigger sat(t, TransferSentTemporal(b, node, epoch))} :: sat(t, TransferSentTemporal(b, node, epoch)) <==> TransferSent(b[t], node, epoch)
{
    stepmap(imap t :: TransferSent(b[t], node, epoch))
}

function ReceiveStepTemporal(b:Behavior<LS_State>, node:EndPoint) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, ReceiveStepTemporal(b, node))} :: sat(t, ReceiveStepTemporal(b, node)) <==> ReceiveStep(b[t], node)
{
    stepmap(imap t :: ReceiveStep(b[t], node))
}


}
