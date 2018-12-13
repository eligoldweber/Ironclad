include "Defs.i.dfy"
include "Assumptions.i.dfy"
include "../proof.i.dfy"

module Lock__LivenessProof__Misc_i {

import opened Lock__LivenessProof__Defs_i
import opened Lock__LivenessProof__Assumptions_i
import opened LockProof



lemma ValidBehaviorServers(b:Behavior<LS_State>, config:Config)
requires ValidBehavior(b, config)
ensures forall t :: t >= 0 ==> forall i :: i in b[t].servers <==> i in config
{
    forall t |
           t >= 0
    ensures forall i :: i in b[t].servers <==> i in config
    {
        assert forall i :: i in b[0].servers <==> i in config;
        var k := 0;
        while (k < t) 
        invariant 0 <= k <= t
        invariant forall i :: i in b[k].servers <==> i in config
        {
            k := k + 1;
        }
    }
}

lemma FirstEventualStep(step:int, t:temporal) 
returns (step':int)
requires sat(step, eventual(t))
ensures sat(step', t)
ensures step' >= step
ensures forall i :: step <= i < step' ==> !sat(i, t)
{
    reveal_eventual();
    var es := eventualStep(step, t);
    step' := step;
    while (step' < es)
    invariant step <= step'
    invariant forall i :: step <= i < step' ==> !sat(i, t)
    {
        if (sat(step', t)) {
            break;
        } else {
            step' := step' + 1;
        }
    }
}

lemma GetLockPacket(ls:LS_State, i:int, epoch:int, config:Config) 
returns (p:LockPacket)
requires 0 <= i < |config|
requires LockedIthPositionWithEpoch(ls, i, epoch, config)
ensures p in ls.environment.sentPackets
     && p.src == config[i]
     && p.msg.Locked?
     && p.msg.locked_epoch == epoch
{
    p :| 
        p in ls.environment.sentPackets
     && p.src == config[i]
     && p.msg.Locked?
     && p.msg.locked_epoch == epoch;
}

lemma SentPacketsMonotoneMeta(b:Behavior<LS_State>, t:int, config:Config, p:LockPacket) 
requires ValidBehavior(b, config)
requires t >= 0
requires p in b[t].environment.sentPackets
ensures forall t' :: t' >= t ==> p in b[t'].environment.sentPackets
{
    forall t' |
           t' >= t
    ensures p in b[t'].environment.sentPackets
    {
        var k := t;
        while (k < t')
        invariant t <= k <= t'
        invariant p in b[k].environment.sentPackets
        {
            k := k + 1;
        }
    }
}

lemma GetSendStep(b:Behavior<LS_State>, t:int, p:LockPacket, config:Config)
returns (t':int)
requires ValidBehavior(b, config)
requires t >= 0
requires p in b[t].environment.sentPackets
ensures 0 <= t' <= t
ensures b[t'].environment.nextStep.LEnvStepHostIos?
ensures LIoOpSend(p) in b[t'].environment.nextStep.ios
ensures b[t'].environment.nextStep.actor == p.src
{
    assert !(p in b[0].environment.sentPackets);
    var k := 0;
    while (k < t && !(p in b[k+1].environment.sentPackets))
    invariant 0 <= k <= t
    invariant forall i :: 0 <= i <= k ==> !(p in b[i].environment.sentPackets)
    {
        k := k + 1;
    }
    assert !(p in b[k].environment.sentPackets);
    assert p in b[k+1].environment.sentPackets;
    t' := k;
    assert b[t'].environment.nextStep.LEnvStepHostIos?;
    assert LIoOpSend(p) in b[t'].environment.nextStep.ios;
}

lemma SentPacketsMonotone(b:Behavior<LS_State>, t:int, i:int, epoch:int, config:Config)
requires ValidBehavior(b, config)
requires t >= 0
requires 0 <= i < |config|
requires sat(t, NodeGrantPacketTemporal(b, i, epoch, config))
ensures forall x :: x >= 0 ==> sat(x, eventual(NodeGrantPacketTemporal(b, i, epoch, config)))
{
    assert NodeGrantPacket(b[t], i, epoch, config);
    var p :|
        p in b[t].environment.sentPackets
     && p.src == config[i]
     && p.dst == config[NextNode(i, config)]
     && p.msg.Transfer?
     && p.msg.transfer_epoch == epoch;
    SentPacketsMonotoneMeta(b, t, config, p);
    assert forall t' :: t' >= t ==> p in b[t'].environment.sentPackets;

    forall x |
           x >= 0
    ensures sat(x, eventual(NodeGrantPacketTemporal(b, i, epoch, config)))
    {
        var tt := t + 1;
        if (tt <= x) {
            tt := x + 1;
        }
        assert tt > x;
        assert p in b[tt].environment.sentPackets;
        assert sat(tt, NodeGrantPacketTemporal(b, i, epoch, config));
        reveal_eventual();
    }
}

lemma NodeConfig(b:Behavior<LS_State>, config:Config)
requires ValidBehavior(b, config)
ensures forall t, i ::
               t >= 0
            && i in b[t].servers
           ==> b[t].servers[i].config == config
ensures forall t, i ::
               t >= 0
            && 0 <= i < |config|
           ==> config[i] in b[t].servers 
            && b[t].servers[config[i]].my_index == i
{
    forall t |
           t >= 0
    ensures forall i ::
                   i in b[t].servers
               ==> b[t].servers[i].config == config
    {
        assert forall i :: 
                      i in b[0].servers
                  ==> b[0].servers[i].config == config;
        var k := 0;
        while (k < t)
        invariant 0 <= k <= t
        invariant forall i :: i in b[k].servers ==> b[k].servers[i].config == config
        {
            k := k + 1;
        }
    }

    forall t | 
           t >= 0
    ensures forall i ::
                   0 <= i < |config|
               ==> config[i] in b[t].servers
                && b[t].servers[config[i]].my_index == i
    {
        forall i |
               0 <= i < |config|
        ensures config[i] in b[0].servers
             && b[0].servers[config[i]].my_index == i
        {
            assert NodeInit(b[0].servers[config[i]], i, config);
        }

        var k := 0;
        while (k < t)
        invariant 0 <= k <= t
        invariant forall i ::
                         0 <= i < |config|
                     ==> config[i] in b[k].servers
        invariant forall i ::
                         0 <= i < |config|
                     ==> b[k].servers[config[i]].my_index == i
        {
            assert LS_Next(b[k], b[k+1]);

            if (b[k].environment.nextStep.LEnvStepHostIos?
             && b[k].environment.nextStep.actor in b[k].servers)
            {
                var id := b[k].environment.nextStep.actor;
                assert forall i :: 0 <= i < |config| && config[i] != id ==> b[k+1].servers[config[i]].my_index == i;
                assert forall i :: 0 <= i < |config| && config[i] == id ==> b[k+1].servers[config[i]].my_index == i;
            }

            assert forall i :: 0 <= i < |config| ==> b[k+1].servers[config[i]].my_index == i;
            k := k + 1;
        }
    }
}



lemma EventuallyReceiveStep(b:Behavior<LS_State>, node:EndPoint, config:Config, asp:AssumptionParameters)
requires ValidBehavior(b, config)
requires node in config
requires LivenessAssumptions(b, asp, config)
ensures sat(0, always(eventual(ReceiveStepTemporal(b, node))))
{
    reveal_and();
    reveal_always();
    assert sat(0, always(ActionOccursForServerTemporal(b, node)));
    assert sat(0, always(eventual(NodeAcceptOccursForServerTemporal(b, node))));
    forall t |
           t >= 0
    ensures sat(t, eventual(ReceiveStepTemporal(b, node)))
    {
        assert sat(t, eventual(NodeAcceptOccursForServerTemporal(b, node)));
        var t' := eventualStep(t, NodeAcceptOccursForServerTemporal(b, node));
        assert sat(t', NodeAcceptOccursForServerTemporal(b, node));
        assert NodeAcceptOccursForServer(b[t'], b[t'+1], node);
        assert ReceiveStep(b[t'], node);
        assert sat(t', ReceiveStepTemporal(b, node));
        reveal_eventual();
        assert sat(t, eventual(ReceiveStepTemporal(b, node)));
    }
}



lemma HostQueueDecrease(e:LockEnvironment, e':LockEnvironment, p:LockPacket, dst:EndPoint, index:int) 
returns (index':int)
requires LEnvironment_Next(e, e')
requires HostQueues_Next(e, e')
requires p.dst == dst
requires p.dst in e.hostInfo
requires 0 <= index < |e.hostInfo[dst].queue|
requires p == e.hostInfo[dst].queue[index]
requires e.nextStep.LEnvStepHostIos?
requires |e.nextStep.ios| > 0
requires e.nextStep.ios[0].LIoOpReceive?
requires HostQueue_PerformIos(e.hostInfo[dst].queue, e'.hostInfo[dst].queue, e.nextStep.ios)
ensures (index' < index 
      && 0 <= index' < |e'.hostInfo[dst].queue| 
      && p == e'.hostInfo[dst].queue[index']) 
     || (LIoOpReceive(p) in e.nextStep.ios
      && index' == -1
      && index' < index)
{
    var ios := e.nextStep.ios;
    var queue := e.hostInfo[dst].queue;
    var queue' := e'.hostInfo[dst].queue;
    index' := index;
    assert HostQueue_PerformIos(queue, queue', ios);
    if (LIoOpReceive(p) == ios[0]) {
        index' := -1;
    } else {
        ios := ios[1..];
        queue := queue[1..];
        index' := index' - 1;
        assert HostQueue_PerformIos(queue, queue', ios);
    
        while (|ios| > 0 && ios[0].LIoOpReceive?)
        decreases |ios|
        decreases index'
        invariant index' < index
        invariant |ios| >= 0
        invariant forall x :: x in ios ==> x in e.nextStep.ios
        invariant -1 <= index' < |queue|
        invariant index' != -1 ==> p == queue[index']
        invariant index' == -1 ==> (|ios| > 0 && LIoOpReceive(p) == ios[0])
        invariant HostQueue_PerformIos(queue, queue', ios)
        {
            if (LIoOpReceive(p) == ios[0]) {
                index' := -1;
                break;
            } else {
                ios := ios[1..];
                queue := queue[1..];
                index' := index' - 1;
            }
            assert index' < index;
        }
        if (index' == -1) {
            assert LIoOpReceive(p) == ios[0];
            assert LIoOpReceive(p) in e.nextStep.ios;
            assert index' < index;
        } else {
            assert 0 <= index' < |e'.hostInfo[dst].queue|;
            assert p == e'.hostInfo[dst].queue[index'];
            assert index' < index;
        }
    }
}


lemma lemma_TransferDeliveredLeadsToReceived(b:Behavior<LS_State>, p:LockPacket, i:int, config:Config, asp:AssumptionParameters)
requires ValidBehavior(b, config)
requires LivenessAssumptions(b, asp, config)
requires p.msg.Transfer?
requires 0 <= i < |config|
requires p.dst == config[i]
ensures sat(0, always(PacketDeliveredLeadsToReceived(b, p)))
{
    forall t |
           t >= 0
        && sat(t, PacketDeliveredTemporal(BehaviorToLEnvMap(b), p))
    ensures sat(t+1, eventual(PacketReceivedTemporal(b, p)))
    {
        var node := p.dst;
        reveal_always();
        assert sat(t, HostQueuesNextTemporal(BehaviorToLEnvMap(b)));
        assert HostQueues_Next(b[t].environment, b[t+1].environment);
        assert node in b[t].environment.hostInfo;
        assert p in b[t+1].environment.hostInfo[node].queue;
        var index :| 
            0 <= index < |b[t+1].environment.hostInfo[node].queue|
         && p == b[t+1].environment.hostInfo[node].queue[index];
        var k := t+1;
        while (index >= 0)
        decreases index
        invariant k >= t+1
        invariant node in b[k].environment.hostInfo
        invariant -1 <= index < |b[k].environment.hostInfo[node].queue|
        invariant index >= 0 ==> p == b[k].environment.hostInfo[node].queue[index]
        invariant index == -1  
              ==> (b[k-1].environment.nextStep.LEnvStepHostIos?
                && LIoOpReceive(p) in b[k-1].environment.nextStep.ios)
        {
            EventuallyReceiveStep(b, node, config, asp);
            reveal_always();
            assert sat(k, eventual(ReceiveStepTemporal(b, node)));
            var rStep := FirstEventualStep(k, ReceiveStepTemporal(b, node));

            var kk := k;
            while (kk < rStep)
            invariant k <= kk <= rStep
            invariant node in b[kk].environment.hostInfo
            invariant 0 <= index < |b[kk].environment.hostInfo[node].queue|
            invariant p == b[kk].environment.hostInfo[node].queue[index]
            {
                assert sat(kk, HostQueuesNextTemporal(BehaviorToLEnvMap(b)));
                if (b[kk].environment.nextStep.LEnvStepHostIos?) {
                    assert !sat(kk, ReceiveStepTemporal(b, node));
                    assert !ReceiveStep(b[kk], node);
                    assert node in b[kk+1].environment.hostInfo;
                    assert 0 <= index < |b[kk+1].environment.hostInfo[node].queue|;
                    assert p == b[kk+1].environment.hostInfo[node].queue[index];

                }

                kk := kk + 1;
            }

            assert sat(rStep, HostQueuesNextTemporal(BehaviorToLEnvMap(b)));
            var index' := HostQueueDecrease(b[rStep].environment, b[rStep+1].environment, p, node, index);

            assert index' < index;
            index := index';
            k := rStep + 1;

        }

        assert sat(k-1, PacketReceivedTemporal(b, p));
        assert k-1 >= t+1;
        reveal_eventual();
        assert sat(t+1, eventual(PacketReceivedTemporal(b, p)));
    }

    reveal_always();
    reveal_imply();
    reveal_next();
}

lemma MapToSeq(b:Behavior<LS_State>, t:int) 
returns (lb:seq<LS_State>)
requires t >= 0
requires imaptotal(b)
ensures |lb| == t + 1
ensures forall i :: 0 <= i <= t ==> lb[i] == b[i]
{
    lb := [b[0]];
    var k := 0;
    while (k < t)
    invariant 0 <= k <= t
    invariant |lb| == k + 1
    invariant forall i :: 0 <= i <= k ==> lb[i] == b[i]
    {
        lb := lb + [b[k+1]];
        k := k + 1;
    }
}

lemma OneLockedAtMost(b:Behavior<LS_State>, config:Config)
requires ValidBehavior(b, config)
ensures forall t ::
               t >= 0
           ==> forall x :: x in config <==> x in b[t].servers
ensures forall t ::
               t >= 0
           ==> (exists id ::
                       id in config
                    && forall x ::
                              x in config
                          ==> (b[t].servers[x].held <==> x == id))
            || ((forall id ::
                        id in config
                    ==> !b[t].servers[id].held))
{
    ValidBehaviorServers(b, config);
    forall t |
           t >= 0
    ensures (exists id ::
                    id in config
                 && forall x :: 
                           x in config
                       ==> (b[t].servers[x].held <==> x == id))
         || ((forall id ::
                     id in config
                 ==> !b[t].servers[id].held))
    {
        var lb := MapToSeq(b, t);
        var glb := LSToGLS(config, lb);
        assert Less_Than_One_Hold(glb[t]);
        var gls := glb[t];
        assert (forall s ::
                       s in glb[t].ls.servers
                   ==> (s == gls.history[|gls.history|-1] <==> gls.ls.servers[s].held))
            || (forall s :: s in gls.ls.servers ==> !gls.ls.servers[s].held);
        ValidBehaviorServers(b, config);
        assert gls.ls == lb[t];
        assert gls.history[|gls.history|-1] in config;
        assert (forall s ::
                       s in config
                   ==> (s == gls.history[|gls.history|-1] <==> gls.ls.servers[s].held))
            || (forall s :: s in gls.ls.servers ==> !gls.ls.servers[s].held);
        assert (forall s ::
                       s in config
                   ==> (s == gls.history[|gls.history|-1] <==> lb[t].servers[s].held))
            || (forall s :: s in config ==> !lb[t].servers[s].held);
    }
}

}
