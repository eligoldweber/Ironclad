include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Defs.i.dfy"

module Lock__LivenessProof__LockNext_i {

import opened DistributedSystem_i
import opened Lock__LivenessProof__Defs_i
import opened Lock__LivenessProof__Assumptions_i


// TODO
lemma EventuallyNodeGrant(b:Behavior<LS_State>, i:int, epoch:int, config:Config, asp:AssumptionParameters)
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
requires 0 <= i < |config|
ensures sat(0, always(LockedImpliesGrantTemporal(b, i, epoch, config)))
{
}

// lemma GetEpoch(b:Behavior<LS_State>, t:int, i:int, epoch:int, config:Config) 
// returns (epoch' : int)
// requires imaptotal(b)
// requires 0 <= i < |config|
// requires sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config))
// ensures epoch' > epoch
// ensures sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch', config))
// {
//     assert LockedIthPositionWithHigherEpoch(b[t], i, epoch, config);
//     var p, e :|
//            e > epoch
//         && p in b[t].environment.sentPackets
//         && p.src == config[i] 
//         && p.msg.Locked?
//         && p.msg.locked_epoch == e;
//     epoch' := e;
// }

// lemma GetTransferPacket(b:Behavior<LS_State>, t:int, i:int, epoch:int, config:Config) 
// returns (p : LockPacket)
// requires imaptotal(b)
// requires 0 <= i < |config|
// requires sat(t, NodeGrantPacketTemporal(b, i, epoch, config))
// ensures LIoOpSend(p) in b[t].environment.nextStep.ios
// ensures p.src == config[i]
// ensures p.dst == config[NextNode(i, config)]
// ensures p.msg.Transfer?
// ensures p.msg.transfer_epoch == epoch
// {
//     assert NodeGrantPacket(b[t], i, epoch, config);
//     p :|
//         LIoOpSend(p) in b[t].environment.nextStep.ios
//      && p.src == config[i]
//      && p.dst == config[NextNode(i, config)]
//      && p.msg.Transfer?
//      && p.msg.transfer_epoch == epoch;
// }

// TODO
lemma TransferDeliveredLeadsToLockedLemma(b:Behavior<LS_State>, p:LockPacket, i:int, config:Config)
requires imaptotal(b)
requires ValidBehavior(b, config)
requires p.msg.Transfer?
requires 0 <= i < |config|
requires p.dst == config[i]
ensures sat(0, always(TransferDeliveredLeadsToLockedTemporal(b, p, i, config)))
{

}

// lemma LockedWithEpochToHigherEpoch(b:Behavior<LS_State>, t:int, i:int, epoch:int, epoch':int, config:Config)
// requires imaptotal(b)
// requires 0 <= i < |config|
// requires sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config))
// requires epoch > epoch'
// ensures sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch', config))
// {
// }

// lemma LockEventuallyTransferToNextNode(b:Behavior<LS_State>, i:int, epoch:int, config:Config, asp:AssumptionParameters)
// requires ValidBehavior(b, config)
// requires LivenessAssumptions(b, asp, config)
// requires 0 <= i < |config|
// ensures sat(0, always(LockTransferToNextNode(b, i, epoch, config)))
// {
//     forall t |
//            t >= 0
//         && sat(t, or(LockedIthPositionWithEpochTemporal(b, i, epoch, config),
//                      LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config)))
//     ensures sat(t, eventual(LockedIthPositionWithHigherEpochTemporal(b, NextNode(i, config), epoch, config)))
//     {
//         var e := epoch;
//         if (sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config))) 
//         {
//             e := GetEpoch(b, t, i, epoch, config);
//         }
//         assert e >= epoch;
//         assert sat(t, LockedIthPositionWithEpochTemporal(b, i, e, config));
// 
//         EventuallyNodeGrant(b, i, e, config, asp);
//         reveal_always();
//         reveal_imply();
//         assert sat(t, eventual(NodeGrantPacketTemporal(b, i, e+1, config)));
//         var grantStep := eventualStep(t, NodeGrantPacketTemporal(b, i, e+1, config));
//         var p := GetTransferPacket(b, grantStep, i, e+1, config);
//         var serverAddresses := MapSeqToSet(config, x=>x);
//         assert forall x :: x in serverAddresses <==> x in config;
//         var bEnv := BehaviorToLEnvMap(b);
//         assert PacketSentBetweenHosts(bEnv[grantStep], p, serverAddresses, serverAddresses);
//         assert sat(grantStep, PacketsEventuallyDeliveredForHostsTemporal(bEnv, serverAddresses));
//         assert sat(grantStep, next(eventual(PacketDeliveredTemporal(bEnv, p))));
//         reveal_next();
//         reveal_eventual();
//         assert sat(grantStep, eventual(PacketDeliveredTemporal(bEnv, p)));
//         var acceptStep := eventualStep(grantStep, PacketDeliveredTemporal(bEnv, p));
//         TransferDeliveredLeadsToLockedLemma(b, p, NextNode(i, config), config);
//         assert sat(acceptStep, next(LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config)));
//         assert sat(acceptStep+1, LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config));
//         LockedWithEpochToHigherEpoch(b, acceptStep+1, NextNode(i, config), e+1, epoch, config);
//         assert sat(acceptStep+1, LockedIthPositionWithHigherEpochTemporal(b, NextNode(i, config), epoch, config));
//     }
//     reveal_always();
// }














}
