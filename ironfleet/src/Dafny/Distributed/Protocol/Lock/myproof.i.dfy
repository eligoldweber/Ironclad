include "Node.i.dfy"
include "Types.i.dfy"
include "RefinementProof/DistributedSystem.i.dfy"
include "RefinementProof/Refinement.i.dfy"

module My_Proof {
import opened Protocol_Node_i
import opened Native__Io_s
import opened Types_i
import opened DistributedSystem_i
import opened Refinement_i

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, LockMessage>>, serviceState:ServiceState) 
{
    forall p :: 
        p in concretePkts 
     && p.src in serviceState.hosts 
     && p.dst in serviceState.hosts 
     && p.msg.Locked?
     ==>
        1 <= p.msg.locked_epoch <= |serviceState.history|
     && p.src == serviceState.history[p.msg.locked_epoch-1]
}

predicate myService_Correspondence(concretePkts:set<LPacket<EndPoint, LockMessage>>, serviceState:ServiceState) 
{
    forall p :: 
        p in concretePkts 
     && p.src in serviceState.hosts 
     && p.dst in serviceState.hosts 
     && p.msg.Transfer?
     ==>
        1 <= p.msg.transfer_epoch <= |serviceState.history|
     && p.dst == serviceState.history[p.msg.transfer_epoch-1]
}

lemma ForInit(gls:GLS_State, s:ServiceState, config:Config)
    requires s == AbstractifyGLS_State(gls);
    requires GLS_Init(gls, config);
    ensures Service_Init(s, Collections__Maps2_s.mapdomain(gls.ls.servers));
    ensures Service_Correspondence(gls.ls.environment.sentPackets, s);
    ensures forall e :: e in gls.ls.servers && gls.ls.servers[e].held ==> gls.ls.servers[e].epoch == |s.history|;
    ensures myService_Correspondence(gls.ls.environment.sentPackets, s);
{
    assert mapdomain(gls.ls.servers) == s.hosts;
    assert config[0] in s.hosts && s.history == [config[0]];
    assert |gls.ls.environment.sentPackets| == 0;
}

lemma ForNext(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState, config: Config)
    requires s == AbstractifyGLS_State(gls);
    requires s' == AbstractifyGLS_State(gls');
    requires GLS_Next(gls, gls');
    requires forall e :: e in config <==> e in gls.ls.servers;
    requires forall e :: e in gls.ls.servers ==> gls.ls.servers[e].config == config;
    //requires forall e1, e2 :: e1 in gls.ls.servers && e2 in gls.ls.servers && gls.ls.servers[e1].held && gls.ls.servers[e2].held ==> e1 == e2;
    ensures  Service_Next(s, s') || s == s';
    ensures  forall e :: e in config <==> e in gls'.ls.servers;
    ensures  forall e :: e in gls'.ls.servers ==> gls'.ls.servers[e].config == config;
    //ensures  forall e1, e2 :: e1 in gls'.ls.servers && e2 in gls'.ls.servers && gls'.ls.servers[e1].held && gls'.ls.servers[e2].held ==> e1 == e2;
{
    assert mapdomain(gls'.ls.servers) == mapdomain(gls.ls.servers);
    //assert forall e :: e in gls'.ls.servers ==> gls'.ls.servers[e].config == gls.ls.servers[e].config;

    if   gls.ls.environment.nextStep.LEnvStepHostIos? && gls.ls.environment.nextStep.actor in gls.ls.servers
          && NodeGrant(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios)
          && gls.ls.servers[gls.ls.environment.nextStep.actor].held && gls.ls.servers[gls.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
        {
            assert gls.ls.servers == gls'.ls.servers || (gls'.ls.servers == gls.ls.servers[gls.ls.environment.nextStep.actor := gls'.ls.servers[gls.ls.environment.nextStep.actor]]);
            assert s'.hosts == s.hosts;
            assert gls'.history == gls.history + [gls.ls.servers[gls.ls.environment.nextStep.actor].config[(gls.ls.servers[gls.ls.environment.nextStep.actor].my_index + 1) % |gls.ls.servers[gls.ls.environment.nextStep.actor].config|]];
            assert mapdomain(gls.ls.servers) == s.hosts;
            assert gls.ls.servers[gls.ls.environment.nextStep.actor].config[(gls.ls.servers[gls.ls.environment.nextStep.actor].my_index + 1) % |gls.ls.servers[gls.ls.environment.nextStep.actor].config|] in config;
        }
    else
    {
        assert s == s';
    }
}

predicate lengthOfHistory(gls: GLS_State, s: ServiceState)
{
    true 
}

lemma FormyCorrespondence(gls:seq<GLS_State>, s:seq<ServiceState>, i:int, config:Config)
    requires i > 0;
    requires |gls| == |s| == i + 1;
    requires forall i:int :: 0 <= i < |gls| ==> s[i] == AbstractifyGLS_State(gls[i]);
    requires forall i:int :: 0 <= i < |gls| - 1 ==> Service_Correspondence(gls[i].ls.environment.sentPackets, s[i]);
    requires forall i:int :: 0 <= i < |gls| - 1 ==> myService_Correspondence(gls[i].ls.environment.sentPackets, s[i]);
    requires forall i:int :: 0 < i < |gls| ==> GLS_Next(gls[i-1], gls[i]);
    requires forall i:int :: 0 < i < |s| ==> s[i-1] == s[i] || Service_Next(s[i-1], s[i]);
    requires forall e :: e in gls[i-1].ls.servers && gls[i-1].ls.servers[e].held ==> gls[i-1].ls.servers[e].epoch == |s[i-1].history|;
    requires forall e1, e2 :: e1 in gls[i-1].ls.servers && e2 in gls[i-1].ls.servers && gls[i-1].ls.servers[e1].held && gls[i-1].ls.servers[e2].held ==> e1 == e2;
    requires forall j, e :: 0 <= j < |gls| ==> (e in config <==> e in gls[j].ls.servers);
    ensures  forall e :: e in gls[i].ls.servers && gls[i].ls.servers[e].held ==> gls[i].ls.servers[e].epoch == |s[i].history|;
    ensures  myService_Correspondence(gls[i].ls.environment.sentPackets, s[i]);
    
{
    if   gls[i-1].ls.environment.nextStep.LEnvStepHostIos? && gls[i-1].ls.environment.nextStep.actor in gls[i-1].ls.servers
      && NodeGrant(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i-1].ls.environment.nextStep.ios)
      && gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].held && gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
    {
        ghost var pkg := gls[i-1].ls.environment.nextStep.ios[0].s;
        assert s[i].history == s[i-1].history + [gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].config[(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].my_index + 1) % |gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].config|]]
            && gls[i-1].ls.environment.nextStep.ios[0].LIoOpSend?
            && gls[i].ls.environment.sentPackets == gls[i-1].ls.environment.sentPackets + {gls[i-1].ls.environment.nextStep.ios[0].s}
            && pkg.msg.transfer_epoch == |s[i].history|
            && s[i].history[pkg.msg.transfer_epoch-1] == pkg.dst
            && gls[i-1].ls.environment.nextStep.actor == pkg.src;
        //assert |ios| == 1;
        assert |gls[i].ls.environment.sentPackets - gls[i-1].ls.environment.sentPackets| == 1;
    }
    else
    {
        assert s[i].history == s[i-1].history;
        if gls[i-1].ls.environment.nextStep.LEnvStepHostIos? && gls[i-1].ls.environment.nextStep.actor in gls[i-1].ls.servers
        {
            if NodeAccept(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i-1].ls.environment.nextStep.ios)
            {
                assert forall e:: (e in gls[i-1].ls.environment.nextStep.ios && e.LIoOpSend?) ==> !e.s.msg.Transfer?;
                if (gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor].held)
                {

                }
            }
            else
            {
                assert forall e :: e in gls[i].ls.environment.sentPackets - gls[i-1].ls.environment.sentPackets ==> !(e.msg.Locked?);
            }
        }
        else
        {
            assert forall e :: e in gls[i].ls.environment.sentPackets - gls[i-1].ls.environment.sentPackets ==> !(e.src in s[i].hosts);
        }   
    }
}

lemma ForCorrospondence(gls:seq<GLS_State>, s:seq<ServiceState>, i:int, config:Config)
    requires i > 0;
    requires |gls| == |s| == i + 1;
    requires forall i:int :: 0 <= i < |gls| ==> s[i] == AbstractifyGLS_State(gls[i]);
    requires forall i:int :: 0 <= i < |gls| - 1 ==> Service_Correspondence(gls[i].ls.environment.sentPackets, s[i]);
    requires forall i:int :: 0 <= i < |gls| ==> myService_Correspondence(gls[i].ls.environment.sentPackets, s[i]);
    requires forall i:int :: 0 < i < |gls| ==> GLS_Next(gls[i-1], gls[i]);
    requires forall i:int :: 0 < i < |s| ==> s[i-1] == s[i] || Service_Next(s[i-1], s[i]);
    requires forall e1, e2 :: e1 in gls[i-1].ls.servers && e2 in gls[i-1].ls.servers && gls[i-1].ls.servers[e1].held && gls[i-1].ls.servers[e2].held ==> e1 == e2;
    requires forall j, e :: 0 <= j < |gls| ==> (e in config <==> e in gls[j].ls.servers);
    ensures  Service_Correspondence(gls[i].ls.environment.sentPackets, s[i]);
{
    if   gls[i-1].ls.environment.nextStep.LEnvStepHostIos? && gls[i-1].ls.environment.nextStep.actor in gls[i-1].ls.servers
      && NodeGrant(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i-1].ls.environment.nextStep.ios)
      && gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].held && gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
    {
        assert s[i].history == s[i-1].history + [gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].config[(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].my_index + 1) % |gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor].config|]]
            && gls[i-1].ls.environment.nextStep.ios[0].LIoOpSend?
            && gls[i].ls.environment.sentPackets == gls[i-1].ls.environment.sentPackets + {gls[i-1].ls.environment.nextStep.ios[0].s}
            && var pkg := gls[i-1].ls.environment.nextStep.ios[0].s;
                   pkg.msg.transfer_epoch == |s[i].history|
                && s[i].history[pkg.msg.transfer_epoch-1] == pkg.dst
                && gls[i-1].ls.environment.nextStep.actor == pkg.src;
        assert forall e :: e in gls[i].ls.servers ==> ! gls[i].ls.servers[e].held;
    }
    else
    {
        assert s[i].history == s[i-1].history;
        if gls[i-1].ls.environment.nextStep.LEnvStepHostIos? && gls[i-1].ls.environment.nextStep.actor in gls[i-1].ls.servers
        {
            assert NodeNext(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i-1].ls.environment.nextStep.ios);
            if NodeAccept(gls[i-1].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor], gls[i-1].ls.environment.nextStep.ios)
            {
                ghost var ios := gls[i-1].ls.environment.nextStep.ios;
                ghost var actor := gls[i-1].ls.environment.nextStep.actor;
                if |ios| == 2
                {
                    assert gls[i].ls.servers[actor].epoch == ios[0].r.msg.transfer_epoch;
                    assert ios[0].r in gls[i-1].ls.environment.sentPackets;
                    assert exists j :: 0 <= j < i && gls[j].ls.environment.nextStep.LEnvStepHostIos?
                                                    && ios[0].r in gls[j+1].ls.environment.sentPackets
                                                    //&& gls[j].ls.environment.nextStep.actor in config
                                                    //&& gls[j].ls.servers[gls[j].ls.environment.nextStep.actor].held
                                                    //&& gls[j].ls.servers[gls[j].ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
                                                    //&& NodeGrant(gls[j].ls.servers[gls[j].ls.environment.nextStep.actor], gls[j+1].ls.servers[gls[j].ls.environment.nextStep.actor], gls[j].ls.environment.nextStep.ios)
                                                    && ios[0].r in (set x|x in gls[j].ls.environment.nextStep.ios && x.LIoOpSend? :: x.s);
                    //assert exists
                    //assert gls[i].ls.servers[gls[i-1].ls.environment.nextStep.actor].epoch == |s'.history|;
                }
                else
                {
                    assert forall e :: e in gls[i].ls.environment.sentPackets - gls[i-1].ls.environment.sentPackets ==> !(e.msg.Locked?);
                }
            }
            else
            {
                assert forall e :: e in gls[i].ls.environment.sentPackets - gls[i-1].ls.environment.sentPackets ==> !(e.msg.Locked?);
            }
        }   
        else
        {
            assert forall e :: e in gls[i].ls.environment.sentPackets - gls[i-1].ls.environment.sentPackets ==> !(e.src in s[i].hosts);
        }   
    }
}

lemma RefinementProof(config:Config, db:seq<GLS_State>) returns (sb:seq<ServiceState>)
    requires |db| > 0;
    requires GLS_Init(db[0], config);
    requires forall i {:trigger GLS_Next(db[i-1], db[i])} :: 0 < i < |db| ==> GLS_Next(db[i-1], db[i]);
    ensures  |db| == |sb|;
    ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].ls.servers));
    ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
    ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]);
{
    sb:=[AbstractifyGLS_State(db[0])];
    ForInit(db[0], sb[0], config);
    assert  forall e :: e in config <==> e in db[0].ls.servers;

    var i := 1;
    while (i < |db|)
      invariant  |sb| == i;
     invariant  0 < i <= |db|;
     invariant  forall j, e :: 0 <= j < i ==> (e in config <==> e in db[j].ls.servers);
     invariant  forall e :: e in db[i-1].ls.servers ==> db[i-1].ls.servers[e].config == config;
     invariant  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].ls.servers));
     invariant  forall i :: 0 <= i < |sb| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]);
     invariant  forall i:int :: 0 < i < |sb| ==> sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);//
     invariant  forall i:int :: 0 <= i < |sb| ==> sb[i] == AbstractifyGLS_State(db[i]);//
     invariant  forall e :: e in db[i-1].ls.servers && db[i-1].ls.servers[e].held ==> db[i-1].ls.servers[e].epoch == |sb[i-1].history|;
    {
        sb := sb + [AbstractifyGLS_State(db[i])];
        
        ForNext(db[i-1], db[i], sb[i-1], sb[i], config);

        assert forall j :: 0 < j <= i ==> sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
        assert sb[.. i+1] == sb;
        FormyCorrespondence(db[.. i+1], sb[.. i+1], i, config);
        ForCorrospondence(db[.. i+1], sb[.. i+1], i, config);

        i := i+1;
    }
    assert i == |db|;
}
}


