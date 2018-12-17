include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "p_s_correspondence.s.dfy"
include "p_s_lemma.i.dfy"


module LockProof {
import opened DistributedSystem_i
import opened Protocol_Node_i
import opened AbstractServiceLock_s
import opened P_S_Correspondence_s
import opened P_S_Lemma

lemma LSToGLS(config:Config, ls:seq<LS_State>) returns (gls:seq<GLS_State>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures |ls| == |gls|
ensures GLS_Init(gls[0], config)
ensures forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
ensures forall i :: 0 <= i < |ls| ==> LS_GLS_Correspondence(ls[i].environment.sentPackets, gls[i], config)
ensures forall i :: 0 <= i < |gls|-1 ==> gls[i].history == gls[i+1].history || exists new_holder :: new_holder in config && gls[i+1].history == gls[i].history + [new_holder]
ensures forall i :: 0 <= i < |gls| ==> Less_Than_One_Hold(gls[i])
ensures forall i :: 0 <= i < |gls| ==> (forall x :: x in gls[i].history ==> x in config)
ensures forall i :: 0 <= i < |gls| ==> gls[i].ls == ls[i]
ensures forall i :: 0 <= i < |gls| ==> Hold_Epoch(gls[i])
ensures forall i :: 0 <= i < |gls| ==> |gls[i].history| > 0
ensures forall i :: 0 <= i < |gls| ==> Epoch_History(gls[i])
ensures forall i :: 0 <= i < |gls| ==> Transfer_Epoch_In_History(gls[i], config)
{
    var k := 1;
    gls := [GLS_State(ls[0], [config[0]])];
    assert forall j :: j in ls[0].servers && ls[0].servers[j].held ==> ls[0].servers[j].epoch == |gls[0].history| && gls[0].history[|gls[0].history|-1] == j;


    assert |gls[0].history| == 1;
    assert |gls[0].history| == 1 ==> Epoch_History(gls[0]);
    assert Epoch_History(gls[0]);
    assert Less_Than_One_Hold(gls[0]);

    while (k < |ls|)
    invariant 1 <= k <= |ls|
    invariant |gls| == k
    invariant GLS_Init(gls[0], config)
    invariant forall i :: 0 <= i < k-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
    invariant forall i :: 0 <= i < k ==> ls[i] == gls[i].ls
    invariant forall i :: 0 <= i < k ==> LS_GLS_Correspondence(ls[i].environment.sentPackets, gls[i], config)
    invariant forall i :: 0 <= i < k ==> Transfer_Epoch_In_History(gls[i], config)
    invariant forall i :: 0 <= i < k ==> Hold_Epoch(gls[i])
    invariant forall i :: 0 <= i < k-1 ==> gls[i].history == gls[i+1].history || exists new_holder :: new_holder in config && gls[i+1].history == gls[i].history + [new_holder]
    invariant forall i :: 0 <= i < k ==> Hold_History(gls[i])
    invariant forall i :: 0 <= i < k ==> Epoch_History(gls[i])
    invariant forall i :: 0 <= i < k ==> Less_Than_One_Hold(gls[i])
    invariant forall i :: 0 <= i < k ==> (forall x :: x in gls[i].history ==> x in config)
    {

        var kk := k-1;
        var s  := ls[kk];
        var s' := ls[kk+1];
        var history := gls[kk].history;
        var packets := s.environment.sentPackets;
        var packets':= s'.environment.sentPackets;

        if (LS_Next(s, s')) {

            if (s.environment.nextStep.LEnvStepHostIos?) {

                var id := s.environment.nextStep.actor;
                var ios:= s.environment.nextStep.ios;

                if (s.environment.nextStep.actor in s.servers) {

                    if (NodeGrant(s.servers[id], s'.servers[id], ios)) {

                        if (s.servers[id].held && s.servers[id].epoch < 0xFFFF_FFFF_FFFF_FFFF) {

                            history := history + [s.servers[id].config[(s.servers[id].my_index + 1) % |s.servers[id].config|]];
                            gls := gls + [GLS_State(s', history)];
                            assert GLS_Next(gls[kk], gls[kk+1]);
                            assert gls[kk+1].ls == s';

                            assert s'.environment.sentPackets == s.environment.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
                            assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                            assert ios[0].s.msg.transfer_epoch == |gls[kk+1].history|;
                            sameServers(config, ls);
                            sameConfig(config, ls);
                            History_Len(gls, config);
                            Transfer_Epoch_In_History_Next(gls[kk], gls[kk+1], config);
                            assert Transfer_Epoch_In_History(gls[kk+1], config);
                            assert Hold_Epoch(gls[kk]);
                            Hold_Epoch_Next(gls[kk], gls[kk+1]);
                            assert Hold_Epoch(gls[kk+1]);
                            assert Epoch_History(gls[kk+1]);
                            assert Less_Than_One_Hold(gls[kk+1]);
                        } else {

                            gls := gls + [GLS_State(s', history)];
                            assert GLS_Next(gls[kk], gls[kk+1]);
                            assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                        }


                        assert Epoch_History(gls[kk+1]);
                    } else { // NodeAccept(s.servers[id], s'.servers[id], ios)

                        gls := gls + [GLS_State(s', history)];
                        assert NodeAccept(s.servers[id], s'.servers[id], ios);
                        assert |ios| >= 1;

                        if (ios[0].LIoOpReceive?) {
                        
                            if (   !s.servers[id].held
                                && ios[0].r.src in s.servers[id].config
                                && ios[0].r.msg.Transfer?
                                && ios[0].r.msg.transfer_epoch > s.servers[id].epoch) {

                                    Incremental_Packets(ls, config);
                                    sameConfig(config, ls);
                                    Receive_Next(gls[kk], gls[kk+1], config);
                                } else {
                                
                                    assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                                    assert Transfer_Epoch_In_History(gls[kk+1], config);
                                }
                                assert Transfer_Epoch_In_History(gls[kk+1], config);
                        } else {

                            assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                        }
                        assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                    }

                } else { // ???

                    gls := gls + [GLS_State(s', history)];
                    sameServers(config, ls);
                    assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                    assert GLS_Next(gls[kk], gls[kk+1]);
                }

            } else { // s.environment.sentPackets == s'.environment.sentPackets
                gls := gls + [GLS_State(s', history)];
            }
            
        } else { // s == s'
            
            gls := gls + [GLS_State(s', history)];
        }

        k := k + 1;
    }
}

lemma RefinementProof(config:Config, ls:seq<LS_State>) returns (ss:seq<ServiceState>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures |ls| == |ss|
ensures Service_Init(ss[0], ss[0].hosts)
ensures forall i :: 0 <= i < |ss|-1 ==> Service_Next(ss[i], ss[i+1]) || ss[i] == ss[i+1]
ensures forall i :: 0 <= i < |ss| ==> Protocol_Service_Correspondence(ls[i].environment.sentPackets, ss[i])
ensures forall i :: 0 <= i < |ss| ==> ss[i].hosts == mapdomain(ls[0].servers)
{
    var gls := LSToGLS(config, ls);
    var serverAddresses := set k | 0 <= k < |config| :: config[k];
    ss := [];
    var k := 0;
    while (k < |gls|)
    invariant |ss| == k
    invariant 0 <= k <= |gls|
    invariant forall i :: 0 <= i < k ==> ss[i].hosts == serverAddresses
    invariant k > 0 ==> Service_Init(ss[0], serverAddresses)
    invariant forall i :: 0 <= i < k ==> ss[i].history == gls[i].history
    invariant forall i :: 0 <= i < k-1 ==> ss[i].hosts == ss[i+1].hosts
    invariant forall i :: 0 <= i < k-1 ==> ss[i].history == ss[i+1].history || exists new_holder :: new_holder in config && ss[i+1].history == ss[i].history + [new_holder]
    invariant forall i :: 0 <= i < k-1 ==> ss[i] == ss[i+1] || Service_Next(ss[i], ss[i+1])
    invariant forall i :: 0 <= i < k ==> ss[i].hosts == mapdomain(ls[0].servers)
    {
        ss := ss + [ServiceState'(serverAddresses, gls[k].history)];
        assert(ss[k].history == gls[k].history);
        k := k + 1;
    }
}

}
