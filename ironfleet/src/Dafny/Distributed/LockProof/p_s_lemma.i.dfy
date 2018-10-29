include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"
include "p_s_correspondence.s.dfy"


module P_S_Lemma {
import opened DistributedSystem_i
import opened Protocol_Node_i
import opened AbstractServiceLock_s
import opened P_S_Correspondence_s

lemma Incremental_Packets(ls:seq<LS_State>, config:Config)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures forall i :: 0 <= i < |ls|-1 ==> ls[i].environment.sentPackets <= ls[i+1].environment.sentPackets
{
}


lemma sameConfig(config:Config, ls:seq<LS_State>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures forall i :: 0 <= i < |ls| ==> forall j :: j in ls[i].servers ==> ls[i].servers[j].config == config
{
    assert forall j :: j in ls[0].servers ==> ls[0].servers[j].config == config;
    
    var k := 1;
    while (k < |ls|) 
    invariant 1 <= k <= |ls|
    invariant forall i :: 0 <= i < k ==> forall j :: j in ls[i].servers ==> ls[i].servers[j].config == config;
    {
        assert forall i :: 0 <= i < k ==> forall j :: j in ls[i].servers ==> ls[i].servers[j].config == config;
        assert 0 <= k-1 < |ls|-1;
        assert (ls[k-1] == ls[k] || LS_Next(ls[k-1], ls[k]));
        assert forall j :: j in ls[k].servers ==> ls[k].servers[j].config == ls[k-1].servers[j].config;
        assert forall i :: 0 <= i <= k ==> forall j :: j in ls[i].servers ==> ls[i].servers[j].config == config;
        k := k + 1;
    }
}

lemma sameServers(config:Config, ls:seq<LS_State>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures forall i :: 0 <= i < |ls| ==> (forall j :: j in config <==> j in ls[i].servers)
{
    assert forall j :: j in config <==> j in ls[0].servers;
    var k := 1;
    while (k < |ls|) 
    invariant 1 <= k <= |ls|
    invariant forall i :: 0 <= i < k ==> (forall j :: j in config <==> j in ls[i].servers)
    {
        var kk := k-1;
        assert (ls[kk+1] == ls[kk] || LS_Next(ls[kk], ls[kk+1]));
        assert forall j :: j in ls[k].servers <==> j in ls[k-1].servers;
        assert forall j :: j in config <==> j in ls[k].servers;
        k := k + 1;
    }
}


predicate LS_GLS_Correspondence(packets:set<LockPacket>, gls:GLS_State, config:Config) {
    
    forall p ::
           p in packets
        && p.src in config
        && p.dst in config
        && p.msg.Locked?
        ==> var epoch := p.msg.locked_epoch;
                0 < epoch <= |gls.history|
            && p.src == gls.history[epoch-1]
}

predicate LS_GLS_Transfer_Correspondence(packets:set<LockPacket>, gls:GLS_State, config:Config) {
    
    forall p ::
           p in packets
        && p.src in config
        && p.dst in config
        && p.msg.Transfer?
        ==> var epoch := p.msg.transfer_epoch;
                0 < epoch <= |gls.history|
            && p.src == gls.history[epoch-1]
}

predicate Transfer_Epoch_In_History(gls:GLS_State, config:Config) {
    forall p ::
           p in gls.ls.environment.sentPackets
        && p.msg.Transfer?
        && p.src in config
       ==> 2 <= p.msg.transfer_epoch <= |gls.history|
}

predicate Hold_Epoch(gls:GLS_State) {
    forall s :: s in gls.ls.servers
             && gls.ls.servers[s].held
            ==> gls.ls.servers[s].epoch == |gls.history|
}

predicate Unique_Hold(s:LS_State) {
    forall x, y :: 
           x in s.servers 
        && y in s.servers 
        && s.servers[x].held 
        && s.servers[y].held
       ==> x == y 
}

lemma History_Len(gls:seq<GLS_State>, config:Config)
requires |gls| > 0
requires GLS_Init(gls[0], config)
requires forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
ensures forall i :: 0 <= i < |gls| ==> |gls[i].history| >= 1
{}

lemma At_Most_One_Hold(config:Config, ls:seq<LS_State>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures forall i :: 0 <= i < |ls| ==> Unique_Hold(ls[i]);
{
    assert Unique_Hold(ls[0]);
    var k := 1;
    while (k < |ls|)
    invariant 1 <= k <= |ls|
    invariant forall i :: 0 <= i < k ==> Unique_Hold(ls[i])
    {
        var kk := k-1;

        if (LS_Next(ls[kk], ls[kk+1])
         && ls[kk].environment.nextStep.LEnvStepHostIos?
         && ls[kk].environment.nextStep.actor in ls[kk].servers) {
            var s := ls[kk];
            var s' := ls[kk+1];
            var id := s.environment.nextStep.actor;
            var ios := s.environment.nextStep.ios;
            assert s'.servers == s.servers[id := s'.servers[id]];
            
            forall x | x in s'.servers 
            ensures !s'.servers[x].held
            {
                if (x != id) {
                    assert s'.servers[x].held == s.servers[x] == false;
                } else {
                    assert !s'.servers[x].held;
                }
            }

            assert Unique_Hold(ls[kk+1]);
        } 
        
        k := k + 1;
    }
}

lemma Hold_Epoch_Next(s:GLS_State, s':GLS_State)
requires GLS_Next(s, s')
requires s.ls.environment.nextStep.LEnvStepHostIos?
requires s.ls.environment.nextStep.actor in s.ls.servers
requires NodeGrant(s.ls.servers[s.ls.environment.nextStep.actor], s'.ls.servers[s.ls.environment.nextStep.actor], s.ls.environment.nextStep.ios)
requires s.ls.servers[s.ls.environment.nextStep.actor].held
requires s.ls.servers[s.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
requires Hold_Epoch(s)
ensures Hold_Epoch(s')
{
    forall ss |
           ss in s'.ls.servers
        && s'.ls.servers[ss].held
    ensures s'.ls.servers[ss].epoch == |s'.history|
    {
        var id := s.ls.environment.nextStep.actor;
        if (ss == id) {
            assert !s'.ls.servers[ss].held;
        } else {
            assert s'.ls.servers[ss] == s.ls.servers[ss];
            assert s'.ls.servers[ss].epoch == |s.history|;
        }
    }

}


lemma Transfer_Epoch_In_History_Next(s:GLS_State, s':GLS_State, config:Config)
requires GLS_Next(s, s')
requires s.ls.environment.nextStep.LEnvStepHostIos?
requires s.ls.environment.nextStep.actor in s.ls.servers
requires NodeGrant(s.ls.servers[s.ls.environment.nextStep.actor], s'.ls.servers[s.ls.environment.nextStep.actor], s.ls.environment.nextStep.ios)
requires s.ls.servers[s.ls.environment.nextStep.actor].held
requires s.ls.servers[s.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
requires forall j :: j in s.ls.servers ==> s.ls.servers[j].config == config
requires forall j :: j in config <==> j in s.ls.servers
requires Transfer_Epoch_In_History(s, config)
requires s.ls.environment.nextStep.ios[0].s.msg.transfer_epoch == |s'.history|;
requires |s'.history| > 1
ensures Transfer_Epoch_In_History(s', config)
{
    var ios := s.ls.environment.nextStep.ios;
    var id := s.ls.environment.nextStep.actor;
    assert |ios| == 1;
    assert ios[0].s.msg.Transfer?;
    // sameServers(config, ls);
    // sameConfig(config, ls);
    //assert LS_Next(s.ls, s'.ls);
    //assert LEnvironment_Next(s.ls.environment, s'.ls.environment);
    assert IsValidLIoOp(s.ls.environment.nextStep.ios[0], s.ls.environment.nextStep.actor, s.ls.environment);
    assert ios[0].s.src == id;
    assert ios[0].s.src in config;
    forall p |
           p in s'.ls.environment.sentPackets
        && p.msg.Transfer?
        && p.src in config
    ensures 2 <= p.msg.transfer_epoch <= |s'.history|
    {
        if (p == ios[0].s) {
            assert p.msg.transfer_epoch == |s'.history|;
            assert 2 <= p.msg.transfer_epoch <= |s'.history|;
        }
    }
}


lemma Receive_Next(s:GLS_State, s':GLS_State, config:Config)
requires GLS_Next(s, s')
requires s.ls.environment.nextStep.LEnvStepHostIos?
requires s.ls.environment.nextStep.actor in s.ls.servers
requires s.ls.environment.nextStep.LEnvStepHostIos?
requires s.ls.environment.nextStep.actor in s.ls.servers
requires NodeAccept(s.ls.servers[s.ls.environment.nextStep.actor], s'.ls.servers[s.ls.environment.nextStep.actor], s.ls.environment.nextStep.ios)
requires s.ls.environment.nextStep.ios[0].LIoOpReceive?
requires !s.ls.servers[s.ls.environment.nextStep.actor].held
requires s.ls.environment.nextStep.ios[0].r.src in s.ls.servers[s.ls.environment.nextStep.actor].config
requires s.ls.environment.nextStep.ios[0].r.msg.Transfer?
requires s.ls.environment.nextStep.ios[0].r.msg.transfer_epoch > s.ls.servers[s.ls.environment.nextStep.actor].epoch
requires s.ls.environment.sentPackets <= s'.ls.environment.sentPackets;
requires forall j :: j in s.ls.servers ==> s.ls.servers[j].config == config
requires forall j :: j in s'.ls.servers ==> s'.ls.servers[j].config == config
requires Transfer_Epoch_In_History(s, config);
requires LS_GLS_Correspondence(s.ls.environment.sentPackets, s, config)
requires Hold_Epoch(s)
ensures LS_GLS_Correspondence(s'.ls.environment.sentPackets, s', config)
ensures Hold_Epoch(s')
ensures Transfer_Epoch_In_History(s', config)
{
    var id := s.ls.environment.nextStep.actor;
    var ios := s.ls.environment.nextStep.ios;
    assert |ios| == 2;
    assert ios[1].LIoOpSend?;

    assert Transfer_Epoch_In_History(s',config);

    assert ios[0].r in s.ls.environment.sentPackets;
    assert ios[0].r.msg.Transfer?;
    assert ios[0].r.src in s.ls.servers[id].config;

    assert exists p ::
                  p in s.ls.environment.sentPackets
               && p.msg.Transfer?
               && p.src in config
               && p.msg.transfer_epoch == ios[1].s.msg.locked_epoch;
    


    assert 2 <= ios[1].s.msg.locked_epoch <= |s'.history|; 
    assert s'.history[ios[1].s.msg.locked_epoch-1] == ios[1].s.src; //(3)



    assert LS_GLS_Correspondence(s.ls.environment.sentPackets, s', config);
    assert forall p ::
           p in (set io | io in ios && io.LIoOpSend? :: io.s)
        && p.src in config
        && p.dst in config
        && p.msg.Locked?
        ==> 0 < p.msg.locked_epoch <= |s'.history|
         && p.src == s'.history[p.msg.locked_epoch-1];
    
    assert LS_GLS_Correspondence(s'.ls.environment.sentPackets, s', config);
    assert Hold_Epoch(s'); 


}


}
