include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"
include "p_s_correspondence.s.dfy"


module LockProof {
import opened DistributedSystem_i
import opened Protocol_Node_i
import opened AbstractServiceLock_s
import opened P_S_Correspondence_s

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

lemma LSToGLS(config:Config, ls:seq<LS_State>) returns (gls:seq<GLS_State>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures |ls| == |gls|
ensures GLS_Init(gls[0], config)
ensures forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
ensures forall i :: 0 <= i < |gls|-1 ==> (gls[i].history == gls[i+1].history || exists new_holder :: new_holder in config && gls[i+1].history == gls[i].history + [new_holder])
ensures gls[|gls|-1].ls == ls[|ls|-1]
ensures forall i :: 0 <= i < |ls| ==> gls[i].ls == ls[i]
ensures forall i :: 0 <= i < |ls|-1 ==> (ls[i] == ls[i+1] ==> gls[i] == gls[i+1])
ensures forall i :: 0 <= i < |ls| ==> LS_GLS_Correspondence(ls[i].environment.sentPackets, gls[i], config)
{
    if (|ls| == 1) {
        gls := [GLS_State(ls[0], [config[0]])];
        assert gls[|gls|-1].ls == ls[|ls|-1];
    } else {
        assert(|ls| > 1);
        gls := LSToGLS(config, ls[0..|ls|-1]);
        assert(|gls| == |ls|-1);
        var history := gls[|gls|-1].history;

        assert forall i :: 0 <= i < |ls|-1 ==> (!LS_Next(ls[i], ls[i+1]) ==> ls[i] == ls[i+1]);
        var xxx := |ls|-2;
        assert(0 <= xxx < |ls|-1);
        assert !LS_Next(ls[xxx], ls[xxx+1]) ==> ls[xxx] == ls[xxx+1];



        if (LS_Next(ls[|ls|-2], ls[|ls|-1])
         && ls[|ls|-2].environment.nextStep.LEnvStepHostIos? 
         && ls[|ls|-2].environment.nextStep.actor in ls[|ls|-2].servers)
        {
            if (NodeGrant(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor], ls[|ls|-1].servers[ls[|ls|-2].environment.nextStep.actor], ls[|ls|-2].environment.nextStep.ios)
             && ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].held
             && ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF) 
            {
                assert |ls| > 0;
                assert LS_Init(ls[0], config);
                assert forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1];

                sameConfig(config, ls);

                assert forall i :: 0 <= i < |ls| ==> forall j :: j in ls[i].servers ==> ls[i].servers[j].config == config;

                assert forall j :: j in ls[|ls|-2].servers ==> ls[|ls|-2].servers[j].config == config;
                assert ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config == config;
                assert ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config[(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].my_index + 1) % |ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config|] in config;

//                 history := history + [ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config[(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].my_index + 1) % |ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config|]];
//                 gls := gls + [GLS_State(ls[|ls|-1], history)];

                var s := ls[|ls|-2];
                var s' := ls[|ls|-1];
                var id := s.environment.nextStep.actor;
                var ios := s.environment.nextStep.ios;
                var packets := s.environment.sentPackets;
                var packets' := s'.environment.sentPackets;

                history := history + [s.servers[id].config[(s.servers[id].my_index + 1) % |s.servers[id].config|]];
                gls := gls + [GLS_State(s', history)];

                if (NodeGrant(s.servers[id], s'.servers[id], ios)) {
                    if (s.servers[id].held && s.servers[id].epoch < 0xFFFF_FFFF_FFFF_FFFF) {
                        assert |ios| == 1;
                        assert ios[0].LIoOpSend?;
                        assert ios[0].s.msg.Transfer?;
                        assert forall p ::
                                      p in packets
                                   && p.src in s.servers
                                   && p.dst in s.servers
                                   && p.msg.Locked?
                                 <==> p in packets'
                                  && p.src in s'.servers
                                  && p.dst in s'.servers
                                  && p.msg.Locked?;
                    } else {
                    }
                }




            } else {

                gls := gls + [GLS_State(ls[|ls|-1], history)];
            }
        } else 
        {
            gls := gls + [GLS_State(ls[|ls|-1], history)];
            if (!LS_Next(ls[|ls|-2], ls[|ls|-1])) {
                assert(ls[|ls|-2] == ls[|ls|-1]);
                assert(history == gls[|gls|-2].history);
                assert(gls[|gls|-2] == GLS_State(ls[|ls|-2], history));
                assert(gls[|gls|-2] == gls[|gls|-1]);
            }
            assert(gls[|gls|-1] == gls[|gls|-2] || GLS_Next(gls[|gls|-2], gls[|gls|-1]));
        }

        assert LS_GLS_Correspondence(ls[|ls|-1].environment.sentPackets, gls[|gls|-1], config);

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


// lemma LSToGLS_extended(config:Config, ls:seq<LS_State>) returns (gls:seq<GLS_State>)
// requires |ls| > 0
// requires LS_Init(ls[0], config)
// requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
// ensures |ls| == |gls|
// ensures GLS_Init(gls[0], config)
// ensures forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
// ensures forall i :: 0 <= i < |gls|-1 ==> (gls[i].history == gls[i+1].history || exists new_holder :: new_holder in config && gls[i+1].history == gls[i].history + [new_holder])
// ensures gls[|gls|-1].ls == ls[|ls|-1]
// ensures forall i :: 0 <= i < |ls| ==> gls[i].ls == ls[i]
// ensures forall i :: 0 <= i < |ls|-1 ==> (ls[i] == ls[i+1] ==> gls[i] == gls[i+1])
// ensures forall i :: 0 <= i < |ls| ==> LS_GLS_Correspondence(ls[i].environment.sentPackets, gls[i])
// {
//     gls := LSToGLS(config, ls);
//     
//     assert LS_GLS_Correspondence(ls[0].environment.sentPackets, gls[0]);
//     var k := 1;
//     while (k < |ls|)
//     invariant 1 <= k <= |ls|
//     invariant forall i :: 0 <= i < k ==> LS_GLS_Correspondence(ls[i].environment.sentPackets, gls[i]);
//     {
//         if (ls[k-1] == ls[k]) {
//             var kk := k-1;
//             assert gls[kk] == gls[kk+1];
//             assert LS_GLS_Correspondence(ls[k].environment.sentPackets, gls[k]);
//         } else {
//             var packets := ls[k-1].environment.sentPackets;
//             var packets' := ls[k].environment.sentPackets;
//             if (ls[k-1].environment.nextStep.LEnvStepHostIos?
//              && ls[k-1].environment.nextStep.actor in ls[k-1].servers) {
// 
//              // must be the case that LS_NextOneServer(ls[k-1], ls[k], ls[k-1].environment.nextStep.actor, ls[k-1].environment.nextStep.ios)
//                 var s := ls[k-1];
//                 var s' := ls[k];
//                 var id := s.environment.nextStep.actor;
//                 var ios := s.environment.nextStep.ios;
// 
//                 assert gls[k-1].ls == s;
//                 assert gls[k].ls == s';
//                 assert forall i :: i in s.servers <==> i in s'.servers;
//                 assert packets' == packets + (set io | io in ios && io.LIoOpSend? :: io.s);
// 
//                 // Then I have id in s'.servers
//                 // I also have s'.servers == s.servers[id := s'servers[id]]
// 
//                 // Now it's either NodeGrant(s, s', ios) or NodeAccept(s, s', ios)
// 
//                 if (NodeGrant(s.servers[id], s'.servers[id], ios)) {
//                     if (s.servers[id].held && s.servers[id].epoch < 0xFFFF_FFFF_FFFF_FFFF) {
//                         assert |ios| == 1;
//                         assert ios[0].LIoOpSend?;
//                         assert ios[0].s.msg.Transfer?;
//                         assert forall p ::
//                                       p in packets
//                                    && p.src in s.servers
//                                    && p.dst in s.servers
//                                    && p.msg.Locked?
//                                  <==> p in packets'
//                                   && p.src in s'.servers
//                                   && p.dst in s'.servers
//                                   && p.msg.Locked?;
//                     } else {
//                     }
//                 }
// 
//                 assert LS_GLS_Correspondence(ls[k].environment.sentPackets, gls[k]);
//             } else {
//                 assert false;
//                 // Should be something like same valid locked messages in packets and packets'
//             }
//         }
//         assert LS_GLS_Correspondence(ls[k].environment.sentPackets, gls[k]);
//         k := k + 1;
//     }
// }



lemma GLSToSS(config:Config, gls:seq<GLS_State>) returns (ss:seq<ServiceState>)
requires |gls| > 0
requires GLS_Init(gls[0], config)
requires forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
requires forall i :: 0 <= i < |gls|-1 ==> (gls[i].history == gls[i+1].history || exists new_holder :: new_holder in config && gls[i+1].history == gls[i].history + [new_holder])
ensures |ss| == |gls|
ensures exists serverAddresses :: Service_Init(ss[0], serverAddresses)
ensures forall i :: 0 <= i < |ss|-1 ==> Service_Next(ss[i], ss[i+1]) || ss[i] == ss[i+1]
ensures forall i :: 0 <= i < |ss| ==> ss[i].history == gls[i].history
{
    var i := 0;
    ss := [];
    var serverAddresses := set k | 0 <= k < |config| :: config[k];
    while i < |gls| 
    invariant |ss|==i
    invariant 0 <= i <= |gls|
    invariant forall j :: 0 <= j < i ==> ss[j].hosts == serverAddresses 
    invariant i > 0 ==> Service_Init(ss[0], serverAddresses)
    invariant forall j :: 0 <= j < i ==> ss[j].history == gls[j].history
    invariant forall j :: 0 <= j < i-1 ==> ss[j].hosts == ss[j+1].hosts
    invariant forall j :: 0 <= j < i-1 ==> ss[j].history == ss[j+1].history || exists new_holder :: new_holder in config && ss[j+1].history == ss[j].history + [new_holder]
    invariant forall j :: 0 <= j < i-1 ==> ss[j] == ss[j+1] || Service_Next(ss[j], ss[j+1])
    {
        ss := ss + [ServiceState'(serverAddresses, gls[i].history)];
        assert(ss[i].history == gls[i].history);
        i := i + 1;
    }
}


// lemma sameHosts(ss:seq<ServiceState>) 
// requires |ss| > 0
// requires exists serverAddresses :: Service_Init(ss[0], serverAddresses)
// requires forall i :: 0 <= i < |ss|-1 ==> Service_Next(ss[i], ss[i+1]) || ss[i] == ss[i+1]
// ensures forall i :: 0 <= i < |ss| ==> ss[i].hosts == ss[0].hosts
// {
//     assert ss[0].hosts == ss[0].hosts;
//     var k := 1;
//     while (k < |ss|)
//     invariant 1 <= k <= |ss|
//     invariant forall i :: 0 <= i < k ==> ss[i].hosts == ss[0].hosts
//     {
//         assert forall i :: 0 <= i < |ss|-1 ==> Service_Next(ss[i], ss[i+1]) || ss[i] == ss[i+1];
//         var kk := k-1;
//         assert Service_Next(ss[kk], ss[kk+1]) || ss[kk] == ss[kk+1];
//         assert ss[k] == ss[k-1] || Service_Next(ss[k-1], ss[k]);
//         assert ss[k].hosts == ss[k-1].hosts;
//         assert forall i :: 0 <= i <= k ==> ss[i].hosts == ss[0].hosts;
//         k := k + 1;
//     }
// }



lemma RefinementProof(config:Config, ls:seq<LS_State>) returns (ss:seq<ServiceState>)
requires |ls| > 0
requires LS_Init(ls[0], config)
requires forall i :: 0 <= i < |ls|-1 ==> LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]
ensures |ss| == |ls|
ensures exists serverAddresses :: Service_Init(ss[0], serverAddresses)
ensures forall i :: 0 <= i < |ss|-1 ==> Service_Next(ss[i], ss[i+1]) || ss[i] == ss[i+1]
ensures forall i :: 0 <= i < |ls| ==> Protocol_Service_Correspondence(ls[i].environment.sentPackets, ss[i])
{
    var gls := LSToGLS(config, ls);
    ss := GLSToSS(config, gls);

    assert Protocol_Service_Correspondence(ls[0].environment.sentPackets, ss[0]);

    var    k := 0;
    while (k < |ls|-1)
    invariant 0 <= k <= |ls|-1
    invariant forall i :: 0 <= i <= k ==> Protocol_Service_Correspondence(ls[i].environment.sentPackets, ss[i])
    {
        assert forall i :: 0 <= i <= k ==> Protocol_Service_Correspondence(ls[i].environment.sentPackets, ss[i]);
        if (ls[k] == ls[k+1]) {
            // assert gls[k+1] == gls[k];
            assert ss[k+1] == ss[k];
            assert ls[k+1] == ls[k] ==> Protocol_Service_Correspondence(ls[k+1].environment.sentPackets, ss[k+1]);
        } else {
            assert LS_Next(ls[k], ls[k+1]);

            assert Protocol_Service_Correspondence(ls[k+1].environment.sentPackets, ss[k+1]);
        }
        k := k + 1;
    }
}





}
