include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"
include "p_s_correspondence.s.dfy"


abstract module P_S_Lemma {
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

predicate Transfer_Epoch_In_History(gls:GLS_State, config:Config) {
    forall p ::
           p in gls.ls.environment.sentPackets
        && p.msg.Transfer?
        && p.src in config
       ==> var epoch := p.msg.transfer_epoch;
           2 <= epoch <= |gls.history|
        && gls.history[epoch-1] == p.dst
}

predicate Hold_Epoch(gls:GLS_State) {
    forall s :: s in gls.ls.servers
             && gls.ls.servers[s].held
            ==> gls.ls.servers[s].epoch == |gls.history|
}

predicate Hold_History(gls:GLS_State) {
    forall s :: s in gls.ls.servers
             && gls.ls.servers[s].held
             && |gls.history| > 0
            ==> s == gls.history[|gls.history|-1]
}

predicate Unique_Hold(s:LS_State) {
    forall x, y :: 
           x in s.servers 
        && y in s.servers 
        && s.servers[x].held 
        && s.servers[y].held
       ==> x == y 
}

predicate Less_Than_One_Hold(gls:GLS_State) {

       (|gls.history| > 0 && forall s ::   
                                    s in gls.ls.servers
                                ==> (s == gls.history[|gls.history|-1] <==> gls.ls.servers[s].held))
    || (|gls.history| > 1 && exists p :: 
                                    p in gls.ls.environment.sentPackets
                                 && p.msg.Transfer?
                                 && p.dst == gls.history[|gls.history|-1]
                                 && p.src == gls.history[|gls.history|-2]
                          && forall s :: s in gls.ls.servers ==> !gls.ls.servers[s].held)

}

predicate Epoch_History(gls:GLS_State) {

    forall s, e ::
           s in gls.ls.servers
        && 0 <= e < |gls.history|
        && gls.history[e] == s
        && (e != |gls.history| - 1 || gls.ls.servers[s].held)
       ==> gls.ls.servers[s].epoch >= e+1
}

lemma History_Len(gls:seq<GLS_State>, config:Config)
requires |gls| > 0
requires GLS_Init(gls[0], config)
requires forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
ensures forall i :: 0 <= i < |gls| ==> |gls[i].history| >= 1
{
    assert |gls[0].history| >= 1;

    var k := 1;
    while (k < |gls|) 
    invariant 1 <= k <= |gls|
    invariant forall i :: 0 <= i < k ==> |gls[i].history| >= 1
    {
        var kk := k - 1;
        if (GLS_Next(gls[k-1], gls[k])) {
            assert |gls[k].history| >= 1;
        } else {
            assert gls[kk] == gls[kk+1];
            assert |gls[k].history| >= 1;
        }
        k := k + 1;
    }
}

lemma UniqueHold(s:GLS_State)
requires Hold_History(s)
requires |s.history| > 0
ensures forall i, j :: 
               i in s.ls.servers
            && j in s.ls.servers
            && s.ls.servers[i].held
            && s.ls.servers[j].held
           ==> i == j
{
    forall i, j |
           i in s.ls.servers
        && j in s.ls.servers
        && s.ls.servers[i].held
        && s.ls.servers[j].held
    ensures i == j
    {
        assert i == s.history[|s.history|-1];
        assert j == s.history[|s.history|-1];
    }
}

lemma Hold_Epoch_Next(s:GLS_State, s':GLS_State)
requires |s.history| > 0
requires |s'.history| > 0
requires GLS_Next(s, s')
requires s.ls.environment.nextStep.LEnvStepHostIos?
requires s.ls.environment.nextStep.actor in s.ls.servers
requires NodeGrant(s.ls.servers[s.ls.environment.nextStep.actor], s'.ls.servers[s.ls.environment.nextStep.actor], s.ls.environment.nextStep.ios)
requires s.ls.servers[s.ls.environment.nextStep.actor].held
requires s.ls.servers[s.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
requires Hold_Epoch(s)
requires Hold_History(s)
requires Epoch_History(s)
requires Less_Than_One_Hold(s)
ensures Hold_Epoch(s')
ensures Epoch_History(s')
ensures Less_Than_One_Hold(s')
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

    forall ss, e | 
           ss in s'.ls.servers
        && 0 <= e < |s'.history|
        && s'.history[e] == ss
        && (e != |s'.history|-1 || s'.ls.servers[ss].held)
    ensures s'.ls.servers[ss].epoch >= e+1
    {
        assert |s'.history| == |s.history| + 1;
        if (e < |s.history|) {
            assert s'.ls.servers[ss].epoch >= e+1;
        }
    }

    var id := s.ls.environment.nextStep.actor;
    var ios := s.ls.environment.nextStep.ios;
    assert |ios| == 1;
    assert ios[0].LIoOpSend?;
    assert ios[0].s.msg.Transfer?;
    assert IsValidLIoOp(ios[0], id, s.ls.environment);
    assert ios[0].s.src == id;
    assert |s.history| > 0;
    assert |s'.history| > 1;
    assert id == s.history[|s.history|-1] == s'.history[|s'.history|-2];
    assert ios[0].s.dst == s'.history[|s'.history|-1];
    assert Less_Than_One_Hold(s');

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
requires s'.history == s.history + [s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|]];
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
    ensures p.dst == s'.history[p.msg.transfer_epoch-1]
    {
        var epoch := p.msg.transfer_epoch;
        if (p == ios[0].s) {
            assert epoch == |s'.history|;
            assert 2 <= epoch <= |s'.history|;
            assert p.dst == s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|];
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
requires Hold_History(s)
requires Less_Than_One_Hold(s)
requires Epoch_History(s)
ensures LS_GLS_Correspondence(s'.ls.environment.sentPackets, s', config)
ensures Hold_Epoch(s')
ensures Transfer_Epoch_In_History(s', config)
ensures Hold_History(s')
ensures Less_Than_One_Hold(s')
ensures Epoch_History(s')
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

    assert LEnvironment_Next(s.ls.environment, s'.ls.environment);
    assert IsValidLIoOp(ios[0], id, s.ls.environment);
    assert id == ios[0].r.dst;
    assert ios[0].r.msg.transfer_epoch >= s.ls.servers[id].epoch;

    var epoch := ios[0].r.msg.transfer_epoch;
    if (ios[0].r.msg.transfer_epoch < |s.history|) {
        assert s.history[epoch-1] == ios[0].r.dst == id;
        assert s.ls.servers[id].epoch >= epoch;
    }


    assert ios[0].r.msg.transfer_epoch == |s.history|;
    assert ios[0].r.dst == s.history[|s.history|-1];
    assert id == s.history[|s.history|-1];
    assert Less_Than_One_Hold(s');
    assert Hold_History(s');

    assert Hold_Epoch(s);
    assert s'.ls.servers[id].epoch == ios[1].s.msg.locked_epoch;
    assert s'.ls.servers[id].epoch == ios[0].r.msg.transfer_epoch;
    
    
    assert id == s.history[|s.history|-1];
    assert ios[0].r.msg.transfer_epoch > s.ls.servers[id].epoch;
    assert ios[0].r.msg.transfer_epoch == |s.history|;
    assert ios[0].r.msg.transfer_epoch == |s'.history|;
    assert Hold_Epoch(s'); 

    assert 2 <= ios[1].s.msg.locked_epoch <= |s'.history|; 
    assert s'.history[ios[1].s.msg.locked_epoch-1] == ios[1].s.src;

    assert LS_GLS_Correspondence(s.ls.environment.sentPackets, s', config);
    assert forall p ::
           p in (set io | io in ios && io.LIoOpSend? :: io.s)
        && p.src in config
        && p.dst in config
        && p.msg.Locked?
        ==> 0 < p.msg.locked_epoch <= |s'.history|
         && p.src == s'.history[p.msg.locked_epoch-1];
    
    assert LS_GLS_Correspondence(s'.ls.environment.sentPackets, s', config);

    assert Epoch_History(s');

}


}
