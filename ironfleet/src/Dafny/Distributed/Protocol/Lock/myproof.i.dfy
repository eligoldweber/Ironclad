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

predicate Service_Correspondence(concretePkts:set<LPacket<EndPoint, seq<byte>>>, serviceState:ServiceState) 
{
    forall p, epoch :: 
        p in concretePkts 
     && p.src in serviceState.hosts 
     && p.dst in serviceState.hosts 
     && p.msg == MarshallLockMsg(epoch) 
     ==>
        1 <= epoch <= |serviceState.history|
     && p.src == serviceState.history[epoch-1]
}

lemma ForInit(gls:GLS_State, s:ServiceState, config:Config)
    requires s == AbstractifyGLS_State(gls);
    requires GLS_Init(gls, config);
    ensures Service_Init(s, Collections__Maps2_s.mapdomain(gls.ls.servers));
    ensures Service_Correspondence(gls.ls.environment.sentPackets, s);
{
    assert mapdomain(gls.ls.servers) == s.hosts;
    assert config[0] in s.hosts && s.history == [config[0]];
    assert |gls.ls.environment.sentPackets| == 0;
}

lemma ForNext(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState, id:EndPoint)
    requires s == AbstractifyGLS_State(gls);
    requires s' == AbstractifyGLS_State(gls');
    requires id in gls.ls.servers;
    requires GLS_Next(gls, gls');
    ensures  Service_Next(s, s');
{
    assert gls.ls.servers == gls'.ls.servers || (gls'.ls.servers == gls.ls.servers[gls.ls.environment.nextStep.actor := s'.servers[gls.ls.environment.nextStep.actor]]);
    assert s'.hosts == s.hosts;
    assert s'.history == s.history + [s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|]];
}

lemma ForCorrospondence(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState)
    requires s == AbstractifyGLS_State(gls);
    requires s' == AbstractifyGLS_State(gls');
    requires Service_Correspondence(gls.environment.sentPackets, s);
    requires GLS_Next(gls, gls');
    ensures  Service_Correspondence(gls'.environment.sentPackets, s');
{
    assert if    gls.ls.environment.nextStep.LEnvStepHostIos? && gls.ls.environment.nextStep.actor in gls.ls.servers
              && NodeGrant(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios)
              && gls.ls.servers[gls.ls.environment.nextStep.actor].held && gls.ls.servers[s.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF then
                     s'.history == s.history + [s.ls.servers[s.ls.environment.nextStep.actor].config[(s.ls.servers[s.ls.environment.nextStep.actor].my_index + 1) % |s.ls.servers[s.ls.environment.nextStep.actor].config|]]
                  && gls.ls.environment.nextStep.ios.LIoOpSend?
                  && gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets + {gls.ls.environment.nextStep.ios.s}
                  && var pkg := gls.ls.environment.nextStep.ios.s;
                        s'.history[pkg.epoch-2] == s.ls.servers[s.ls.environment.nextStep.actor]
                     && s.ls.servers[s.ls.environment.nextStep.actor] == pkg.src
            else s'.history == s.history && gls.environment.sentPackets == gls'.environment.sentPackets;
}

lemma RefinementProof(config:Config, db:seq<GLS_State>) returns (sb:seq<ServiceState>)
    requires |db| > 0;
    requires GLS_Init(db[0], config);
    requires forall i {:trigger GLS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> GLS_Next(db[i], db[i+1]);
    ensures  |db| == |sb|;
    ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].ls.servers));
    ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
    ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
{
    sb:=[AbstractifyGLS_State(db[0])];
    ForInit(db[0], sb[0], config);

    var i := 1;
    while (i < |db|)
      invariant  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
      invariant  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
      invariant  forall i :: 0 <= i < |sb| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i]);
      invariant  |sb| == i;
    {
        sb := sb + [AbstractifyGLS_State(db[i])];
        
        assert if db[i-1].environment.nextStep.LEnvStepHostIos? && db[i-1].environment.nextStep.actor in s.servers then
                    ForNext(db[i-1], db[i], sb[i-1], sb[i], db[i-1].environment.nextStep.actor)
                else sb[i-1] == sb[i];
        ForCorrospondence(db[i-1], db[i], sb[i-1], sb[i]);

        i := i+1;
    }

}
}


