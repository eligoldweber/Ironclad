include "../../../Libraries/Math/mod_auto.i.dfy"
include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "Assumptions.i.dfy"
include "Defs.i.dfy"
include "Misc.i.dfy"
include "Invariant.i.dfy"

module Lock__LivenessProof__LockNext_i {

import opened DistributedSystem_i
import opened Lock__LivenessProof__Defs_i
import opened Lock__LivenessProof__Assumptions_i
import opened Lock__LivenessProof__Misc_i
import opened Lock__LivenessProof__Invariant_i

lemma EventuallyNodeGrant(b:Behavior<LS_State>, i:int, epoch:int, config:Config, asp:AssumptionParameters)
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
requires epoch < 0xFFFF_FFFF_FFFF_FFFF
requires 0 <= i < |config|
ensures sat(0, always(LockedImpliesGrantTemporal(b, i, epoch, config)))
{
    forall t |
           t >= 0
        && sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config))
    ensures sat(t, EventualNodeGrantPacketTemporal(b, i, epoch+1, config))
    {
        var p := GetLockPacket(b[t], i, epoch, config);
        var sendStep := GetSendStep(b, t, p, config);
        ValidBehaviorServers(b, config);
        assert b[sendStep].environment.nextStep.LEnvStepHostIos?;
        var ios := b[sendStep].environment.nextStep.ios;
        assert p.src == config[i];
        assert LEnvironment_Next(b[sendStep].environment, b[sendStep+1].environment);
        assert IsValidLEnvStep(b[sendStep].environment, b[sendStep].environment.nextStep);
        assert b[sendStep].environment.nextStep.actor == config[i];
        assert NodeAccept(b[sendStep].servers[config[i]], b[sendStep+1].servers[config[i]], ios);
        assert b[sendStep+1].servers[config[i]].held;
        
        assert sat(sendStep+1, HoldLockForNodeWithEpochTemporal(b, config[i], epoch));
        reveal_always();
        reveal_and();
        reveal_imply();
        assert sat(sendStep+1, ActionOccursForServerTemporal(b, config[i]));
        assert sat(sendStep+1, eventual(NodeGrantOccursForServerTemporal(b, config[i])));
        var grantStep := FirstEventualStep(sendStep+1, NodeGrantOccursForServerTemporal(b, config[i]));

        var k := sendStep + 1;
        assert b[k].servers[config[i]].held;
        assert b[k].servers[config[i]].epoch == epoch;
        while (k < grantStep)
        invariant sendStep + 1 <= k <= grantStep
        invariant b[k].servers[config[i]].held
        invariant b[k].servers[config[i]].epoch == epoch
        {
            if (b[k].environment.nextStep.LEnvStepHostIos?
             && config[i] == b[k].environment.nextStep.actor) {
                assert !sat(k, NodeGrantOccursForServerTemporal(b, config[i]));
                ValidBehaviorServers(b, config);
                assert config[i] in b[k].servers;
                assert config[i] in b[k+1].servers;
                assert !NodeGrant(b[k].servers[config[i]], b[k+1].servers[config[i]], b[k].environment.nextStep.ios);
                assert b[k].servers[config[i]].held;
            } else {
                assert b[k].servers[config[i]].held;
            }
            k := k + 1;
        }

        assert b[grantStep].servers[config[i]].held;
        assert  NodeGrant(b[grantStep].servers[config[i]],
                          b[grantStep+1].servers[config[i]],
                          b[grantStep].environment.nextStep.ios);
        var grantIos := b[grantStep].environment.nextStep.ios;
        assert |grantIos| == 1;
        var grantP := grantIos[0].s;
        assert grantP in b[grantStep+1].environment.sentPackets;
        assert grantP.src == config[i];
        NodeConfig(b , config);
        assert b[grantStep].servers[config[i]].config == config;
        assert b[grantStep].servers[config[i]].my_index == i;
        assert grantP.dst == config[NextNode(i, config)];
        assert grantP.msg.Transfer?;
        assert grantP.msg.transfer_epoch == epoch+1;

        assert sat(grantStep+1, NodeGrantPacketTemporal(b, i, epoch+1, config));
        SentPacketsMonotone(b, grantStep+1, i, epoch+1, config);

    }
    reveal_imply();
    reveal_always();
}

lemma GetEpoch(b:Behavior<LS_State>, t:int, i:int, epoch:int, config:Config) 
returns (epoch' : int)
requires imaptotal(b)
requires 0 <= i < |config|
requires sat(t, LockedIthPositionWithHigherEpochTemporal(b, i, epoch, config))
ensures epoch' > epoch
ensures sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch', config))
{
    assert LockedIthPositionWithHigherEpoch(b[t], i, epoch, config);
    var p, e :|
           e > epoch
        && p in b[t].environment.sentPackets
        && p.src == config[i] 
        && p.msg.Locked?
        && p.msg.locked_epoch == e;
    epoch' := e;
}

lemma GetTransferPacket(b:Behavior<LS_State>, t:int, i:int, epoch:int, config:Config) 
returns (p : LockPacket)
requires imaptotal(b)
requires 0 <= i < |config|
requires sat(t, NodeGrantPacketTemporal(b, i, epoch, config))
ensures p in b[t].environment.sentPackets
ensures p.src == config[i]
ensures p.dst == config[NextNode(i, config)]
ensures p.msg.Transfer?
ensures p.msg.transfer_epoch == epoch
{
    assert NodeGrantPacket(b[t], i, epoch, config);
    p :|
        p in b[t].environment.sentPackets
     && p.src == config[i]
     && p.dst == config[NextNode(i, config)]
     && p.msg.Transfer?
     && p.msg.transfer_epoch == epoch;
}

lemma LockedWithEpochToHigherEpoch(b:Behavior<LS_State>, t:int, i:int, epoch:int, epoch':int, config:Config)
requires imaptotal(b)
requires 0 <= i < |config|
requires sat(t, eventual(LockedIthPositionWithEpochTemporal(b, i, epoch, config)))
requires epoch > epoch'
ensures sat(t, eventual(LockedIthPositionWithHigherEpochTemporal(b, i, epoch', config)))
{
    reveal_eventual();
    var tt := eventualStep(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config));
    assert sat(tt, LockedIthPositionWithHigherEpochTemporal(b, i, epoch', config));
}

lemma EpochMonotone(b:Behavior<LS_State>, node:EndPoint, t1:int, t2:int, config:Config)
requires ValidBehavior(b, config)
requires 0 <= t1 <= t2
requires node in config
ensures node in b[t1].servers
ensures node in b[t2].servers
ensures b[t1].servers[node].epoch <= b[t2].servers[node].epoch
{
    var k := t1;
    ValidBehaviorServers(b, config);
    while (k < t2)
    invariant t1 <= k <= t2
    invariant b[t1].servers[node].epoch <= b[k].servers[node].epoch
    {
        k := k + 1;
    }
}

lemma ValidTransferHasLargestEpoch(b:Behavior<LS_State>, t:int, p:LockPacket, config:Config)
requires ValidBehavior(b, config)
requires t >= 0
requires ValidTransferPacket(p, config)
requires b[t].environment.nextStep.LEnvStepHostIos?
requires LIoOpSend(p) in b[t].environment.nextStep.ios
ensures LargestEpoch(b[t], p.msg.transfer_epoch)
{
    var lb := MapToSeq(b, t);
    var glb := LSToGLS(config, lb);
    var src := p.src;
    assert src in config;
    ValidBehaviorServers(b, config);

    assert b[t].servers[src].held;
    assert glb[t].ls.servers[src].epoch == |glb[t].history|;
    assert p.msg.transfer_epoch == |glb[t].history| + 1;

    var k := 0;

    assert forall s :: s in b[0].servers ==> b[0].servers[s].epoch <= |glb[0].history|;
    while (k < t)
    invariant 0 <= k <= t
    invariant forall s :: s in b[k].servers ==> b[k].servers[s].epoch <= |glb[k].history|
    {
        var kk := k + 1;
        forall s |
               s in b[k+1].servers
        ensures b[kk].servers[s].epoch <= |glb[kk].history|
        {
            assert s in b[k].servers;
            if (b[k].environment.nextStep.LEnvStepHostIos?
             && b[k].environment.nextStep.actor in b[k].servers) {
            
                if (s == b[k].environment.nextStep.actor) {
                    if (NodeAccept(b[k].servers[s], b[kk].servers[s], b[k].environment.nextStep.ios)) {
                        var ios := b[k].environment.nextStep.ios;
                        assert |ios| > 0;
                        if (ios[0].LIoOpTimeoutReceive?) {
                            assert b[kk].servers[s].epoch == b[k].servers[s].epoch;
                            assert |glb[kk].history| >= |glb[k].history|;
                        } else {
                            assert ios[0].LIoOpReceive?;
                            if (!b[k].servers[s].held
                             && ios[0].r.src in b[k].servers[s].config
                             && ios[0].r.msg.Transfer?
                             && ios[0].r.msg.transfer_epoch > b[k].servers[s].epoch) {
                                assert b[kk].servers[s].held;
                                assert b[kk].servers[s].epoch == |glb[k].history|;
                            } else {
                                assert b[kk].servers[s].epoch == b[k].servers[s].epoch;
                                assert |glb[kk].history| >= |glb[k].history|;
                            }
                        }
                    }
                }
            } else {
                assert b[k+1].servers[s].epoch == b[k].servers[s].epoch;
                assert |glb[k+1].history| >= |glb[k].history|;
            }
        }
        k := k + 1;
    }

    forall s |
           s in config
    ensures s in b[t].servers
    ensures p.msg.transfer_epoch > b[t].servers[s].epoch
    {
        ValidBehaviorServers(b, config);
        if (b[t].servers[s].epoch > 0) {
            assert p.msg.transfer_epoch > b[t].servers[s].epoch;
        }

    }

}



lemma FirstReceiveLeadsToLocked(b:Behavior<LS_State>, t:int, grantT:int, p:LockPacket, i:int, config:Config)
requires ValidBehavior(b, config)
requires t >= 0
requires ValidTransferPacket(p, config)
requires 0 <= i < |config|
requires 0 <= grantT < t
requires p.src in config
requires p.dst == config[i]
requires sat(t, PacketReceivedTemporal(b, p))
requires forall t' :: grantT <= t' < t ==> !sat(t', PacketReceivedTemporal(b, p))
requires config[i] in b[grantT].servers
requires !b[grantT+1].servers[config[i]].held
requires p.msg.transfer_epoch > b[grantT+1].servers[config[i]].epoch
requires p in b[grantT+1].environment.sentPackets
ensures sat(t, next(LockedIthPositionWithEpochTemporal(b, i, p.msg.transfer_epoch, config)))
{
    var ios := b[t].environment.nextStep.ios;
    var node := config[i];
    ValidBehaviorServers(b, config);
    NodeConfig(b, config);
    assert NodeAccept(b[t].servers[node], b[t+1].servers[node], ios);
    assert node == b[t].environment.nextStep.actor;


    var k := grantT+1;
    while (k < t)
    invariant node == config[i]
    invariant grantT+1 <= k <= t
    invariant node in b[k].servers
    invariant !b[k].servers[node].held
    invariant p.msg.transfer_epoch > b[k].servers[node].epoch
    {
        SentPacketsMonotoneMeta(b, grantT+1, config, p);
        assert p in b[k].environment.sentPackets;
        ValidBehaviorServers(b, config);
        if (b[k].environment.nextStep.LEnvStepHostIos?
         && b[k].environment.nextStep.actor == node
         && LS_NextOneServer(b[k], b[k+1], node, b[k].environment.nextStep.ios)
         && NodeAccept(b[k].servers[node], b[k+1].servers[node], b[k].environment.nextStep.ios)) {
            
            var kios := b[k].environment.nextStep.ios;
            assert |kios| >= 1;
            if (kios[0].LIoOpReceive?) {
                if (ValidTransferPacket(kios[0].r, config)) {
                    var pp := kios[0].r;
                    assert b[k].environment.nextStep.LEnvStepHostIos?;
                    assert LIoOpReceive(pp) in b[k].environment.nextStep.ios;
                    assert PacketReceived(b[k], pp);
                    assert sat(k, PacketReceivedTemporal(b, pp));
                    assert ValidTransferPacket(pp, config);
                    if (pp == p) {
                        assert sat(k, PacketReceivedTemporal(b, p));
                    }
                    assert pp != p;
                    assert pp.dst == node;
                    assert p.src in config;
                    assert pp.src in config;
                    if (pp.msg.transfer_epoch > b[k].servers[node].epoch) {
                        OnlyOneUsefulTransfer(b, k, p, pp, node, config);
                        assert pp == p;
                    }
                    assert p.msg.transfer_epoch > b[k+1].servers[node].epoch;
                    assert !b[k+1].servers[node].held;
                } else {
                    var pp := kios[0].r;
                    NodeConfig(b, config);
                    assert IsValidLIoOp(kios[0], b[k].environment.nextStep.actor, b[k].environment);
                    assert pp.dst == b[k].environment.nextStep.actor;
                    assert node in b[k+1].servers;
                    assert pp.dst == node;
                    ValidBehaviorServers(b, config);
                    assert pp.dst in config;
                    assert !b[k+1].servers[node].held;
                }

                assert !b[k+1].servers[node].held;
                assert p.msg.transfer_epoch > b[k+1].servers[node].epoch;
            }
        }         
        k := k + 1;
    }


    assert !b[t].servers[node].held;
    assert p.msg.transfer_epoch > b[t].servers[node].epoch;

    assert ios[1].LIoOpSend?;
    var lockedP := ios[1].s;
    assert lockedP.msg.Locked?;
    assert IsValidLIoOp(ios[1], b[t].environment.nextStep.actor, b[t].environment);
    assert lockedP.src == b[t].environment.nextStep.actor;
    assert lockedP.src == node;
    assert lockedP.msg.locked_epoch == p.msg.transfer_epoch;
    assert lockedP in b[t+1].environment.sentPackets;

    assert exists pp ::
                  pp in b[t+1].environment.sentPackets
               && pp.src == node
               && pp.msg.Locked?
               && pp.msg.locked_epoch == p.msg.transfer_epoch;
    assert sat(t+1, LockedIthPositionWithEpochTemporal(b, i, p.msg.transfer_epoch, config));
    reveal_next();
}





lemma LockEventuallyTransferToNextNode(b:Behavior<LS_State>, i:int, epoch:int, config:Config, asp:AssumptionParameters)
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
requires 0 <= i < |config|
requires epoch < 0xFFFF_FFFF_FFFF_FFFF
ensures sat(0, always(LockTransferToNextNode(b, i, epoch, config)))
{
    forall t |
           t >= 0
        && sat(t, LockedIthPositionWithEpochTemporal(b, i, epoch, config))
    ensures sat(t, eventual(LockedIthPositionWithEpochTemporal(b, NextNode(i, config), epoch+1, config)))
    {
        var e := epoch;
        EventuallyNodeGrant(b, i, e, config, asp);
        reveal_always();
        reveal_imply();
        assert sat(t, eventual(NodeGrantPacketTemporal(b, i, e+1, config)));
        var eventualGrantStep := eventualStep(t, NodeGrantPacketTemporal(b, i, e+1, config));
        var p := GetTransferPacket(b, eventualGrantStep, i, e+1, config);
        var grantStep := GetSendStep(b, eventualGrantStep, p, config);
        var serverAddresses := MapSeqToSet(config, x=>x);
        assert forall x :: x in serverAddresses <==> x in config;
        var bEnv := BehaviorToLEnvMap(b);
        assert PacketSentBetweenHosts(bEnv[grantStep], p, serverAddresses, serverAddresses);
        assert sat(grantStep, PacketsEventuallyDeliveredForHostsTemporal(bEnv, serverAddresses));
        assert sat(grantStep, next(eventual(PacketDeliveredTemporal(bEnv, p))));
        reveal_next();
        reveal_eventual();
        assert sat(grantStep, eventual(PacketDeliveredTemporal(bEnv, p)));
        var dStep := eventualStep(grantStep, PacketDeliveredTemporal(bEnv, p));
        lemma_TransferDeliveredLeadsToReceived(b, p, NextNode(i, config), config, asp);
        assert sat(dStep + 1, eventual(PacketReceivedTemporal(b, p)));
        assert sat(grantStep, eventual(PacketReceivedTemporal(b, p)));
        var acceptStep := FirstEventualStep(grantStep, PacketReceivedTemporal(b, p));
        ValidBehaviorServers(b, config);
        assert config[NextNode(i, config)] in b[grantStep+1].servers;
        ValidTransferHasLargestEpoch(b, grantStep, p, config);
        assert p.msg.transfer_epoch > b[grantStep].servers[config[NextNode(i, config)]].epoch;

        assert b[grantStep].servers[config[i]].held;
        if (i == NextNode(i, config)) {
            assert !b[grantStep+1].servers[config[NextNode(i, config)]].held;
        } else {
            OneLockedAtMost(b, config);
            assert !b[grantStep].servers[config[NextNode(i, config)]].held;
            assert !b[grantStep+1].servers[config[NextNode(i, config)]].held;
        }

        assert !b[grantStep+1].servers[config[NextNode(i, config)]].held;
        FirstReceiveLeadsToLocked(b, acceptStep, grantStep, p, NextNode(i, config), config);
        assert sat(acceptStep, next(LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config)));
        assert sat(acceptStep+1, LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config));
        assert sat(acceptStep+1, LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config));
        if (t <= acceptStep + 1) {
            assert sat(t, eventual(LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config)));
        } else {
            var pp :|
                pp in b[acceptStep+1].environment.sentPackets
             && pp.src == config[NextNode(i, config)]
             && pp.msg.Locked?
             && pp.msg.locked_epoch == e+1;

            SentPacketsMonotoneMeta(b, acceptStep+1, config, pp);
            assert pp in b[t+1].environment.sentPackets;

            assert sat(t+1, LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config));

            reveal_eventual();

            assert sat(t, eventual(LockedIthPositionWithEpochTemporal(b, NextNode(i, config), e+1, config)));
        }
    }
    reveal_always();
}














}
