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

lemma ForInit(gls:GLS_State, s:ServiceState, config:Config)
    requires s == AbstractifyGLS_State(gls);
    requires GLS_Init(gls, config);
    ensures Service_Init(s, Collections__Maps2_s.mapdomain(gls.ls.servers));
    ensures Service_Correspondence(gls.ls.environment.sentPackets, s);
    ensures forall e :: e in gls.ls.servers && gls.ls.servers[e].held ==> gls.ls.servers[e].epoch == |s.history|;
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
    ensures  Service_Next(s, s') || s == s';
    ensures  forall e :: e in config <==> e in gls'.ls.servers;
    ensures  forall e :: e in gls'.ls.servers ==> gls'.ls.servers[e].config == config;
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

lemma ForCorrospondence(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState)
    requires s == AbstractifyGLS_State(gls);
    requires s' == AbstractifyGLS_State(gls');
    requires Service_Correspondence(gls.ls.environment.sentPackets, s);
    requires GLS_Next(gls, gls');
    requires forall e :: e in gls.ls.servers && gls.ls.servers[e].held ==> gls.ls.servers[e].epoch == |s.history|;
    ensures  Service_Correspondence(gls'.ls.environment.sentPackets, s');
    ensures  forall e :: e in gls'.ls.servers && gls'.ls.servers[e].held ==> gls'.ls.servers[e].epoch == |s'.history|;
{
    if   gls.ls.environment.nextStep.LEnvStepHostIos? && gls.ls.environment.nextStep.actor in gls.ls.servers
      && NodeGrant(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios)
      && gls.ls.servers[gls.ls.environment.nextStep.actor].held && gls.ls.servers[gls.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
    {
        assert s'.history == s.history + [gls.ls.servers[gls.ls.environment.nextStep.actor].config[(gls.ls.servers[gls.ls.environment.nextStep.actor].my_index + 1) % |gls.ls.servers[gls.ls.environment.nextStep.actor].config|]]
            && gls.ls.environment.nextStep.ios[0].LIoOpSend?
            && gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets + {gls.ls.environment.nextStep.ios[0].s}
            && var pkg := gls.ls.environment.nextStep.ios[0].s;
                   pkg.msg.transfer_epoch == |s'.history|
                && s'.history[pkg.msg.transfer_epoch-1] == pkg.dst
                && gls.ls.environment.nextStep.actor == pkg.src;
    }
    else
    {
        assert s'.history == s.history;
        if gls.ls.environment.nextStep.LEnvStepHostIos? && gls.ls.environment.nextStep.actor in gls.ls.servers
        {
            assert NodeNext(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios);
            if NodeAccept(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios)
            {
                ghost var ios := gls.ls.environment.nextStep.ios;
                ghost var actor := gls.ls.environment.nextStep.actor;
                if |ios| == 2
                {
                    assert gls'.ls.servers[actor].epoch == ios[0].r.msg.transfer_epoch;
                    //assert exists
                    //assert gls'.ls.servers[gls.ls.environment.nextStep.actor].epoch == |s'.history|;
                }
                else
                {
                    assert forall e :: e in gls'.ls.environment.sentPackets - gls.ls.environment.sentPackets ==> !(e.msg.Locked?);
                }
            }
            else
            {
                assert forall e :: e in gls'.ls.environment.sentPackets - gls.ls.environment.sentPackets ==> !(e.msg.Locked?);
            }
        }   
        else
        {
            assert forall e :: e in gls'.ls.environment.sentPackets - gls.ls.environment.sentPackets ==> !(e.src in s'.hosts);
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
      invariant  forall e :: e in config <==> e in db[i-1].ls.servers;
      invariant  forall e :: e in db[i-1].ls.servers ==> db[i-1].ls.servers[e].config == config;
      invariant  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].ls.servers));
      invariant  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
      invariant  forall i :: 0 <= i < |sb| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]);
      invariant  sb[i-1] == AbstractifyGLS_State(db[i-1]);
      invariant  forall e :: e in db[i-1].ls.servers && db[i-1].ls.servers[e].held ==> db[i-1].ls.servers[e].epoch == |sb[i-1].history|;
      //invariant  GLS_Next(db[i-1], db[i]);
    {
        sb := sb + [AbstractifyGLS_State(db[i])];
        
        ForNext(db[i-1], db[i], sb[i-1], sb[i], config);
        
        ForCorrospondence(db[i-1], db[i], sb[i-1], sb[i]);

        i := i+1;
    }
    assert i == |db|;
}
}


