include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"
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
{
    var k := 1;
    gls := [GLS_State(ls[0], [config[0]])];
    assert forall j :: j in ls[0].servers && ls[0].servers[j].held ==> ls[0].servers[j].epoch == |gls[0].history| && gls[0].history[|gls[0].history|-1] == j;

    while (k < |ls|)
    invariant 1 <= k <= |ls|
    invariant |gls| == k
    invariant GLS_Init(gls[0], config)
    invariant forall i :: 0 <= i < k-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
    invariant forall i :: 0 <= i < k ==> ls[i] == gls[i].ls
    invariant forall i :: 0 <= i < k ==> LS_GLS_Correspondence(ls[i].environment.sentPackets, gls[i], config)
    invariant forall i :: 0 <= i < k ==> Transfer_Epoch_In_History(gls[i], config)
    invariant forall i :: 0 <= i < k ==> Hold_Epoch(gls[i])
    //invariant forall i :: 0 <= i < k ==> LS_GLS_Transfer_Correspondence(ls[i].environment.sentPackets, gls[i], config)
    // invariant forall i :: 0 <= i < k ==> forall j :: j in ls[i].servers && ls[i].servers[j].held ==> ls[i].servers[j].epoch == |gls[i].history| && gls[i].history[|gls[i].history|-1] == j
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
                            Transfer_Epoch_In_History_Next(gls[kk], gls[kk+1], config);
                            assert Transfer_Epoch_In_History(gls[kk+1], config);
                            assert Hold_Epoch(gls[kk]);
                            Hold_Epoch_Next(gls[kk], gls[kk+1]);
                            assert Hold_Epoch(gls[kk+1]);
                        } else {

                            gls := gls + [GLS_State(s', history)];
                            assert GLS_Next(gls[kk], gls[kk+1]);
                            assert LS_GLS_Correspondence(s'.environment.sentPackets, gls[kk+1], config);
                        }


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
                                    assert Hold_Epoch(gls[kk+1]); 
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


}
