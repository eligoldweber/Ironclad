
include "./RefinementProof/DistributedSystem.i.dfy"
include "./RefinementProof/Refinement.i.dfy"
include "../../Services/Lock/AbstractService.s.dfy"
include "./Node.i.dfy"
include "Types.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "./helper.i.dfy"
include "./correspondsProof.i.dfy"


module FullRefinementProof{
     import opened DistributedSystem_i
     import opened AbstractServiceLock_s
     import opened Protocol_Node_i
     import opened Types_i
     import opened Refinement_i
     import opened Concrete_NodeIdentity_i
     import opened refinementHelper
     import opened fullCoresponds


//////////////////////////////////////////////////////////////////////////////////////////////////
lemma glsHistorySize(gls:seq<GLS_State>, config:Config, i:int)
        requires validGLS(gls, config);
        requires 0 <= i < |gls|;
        ensures  1 <= |gls[i].history| <= i + 1;
    {
        if i > 0 {
            glsHistorySize(gls, config, i - 1);
            assert GLS_Next(gls[i-1], gls[i]);
        }
    }

lemma ServiceNextOrEqual(gls:seq<GLS_State>, config:Config, i:int)
        requires validGLS(gls, config);
        requires 0 <= i < |gls| - 1;
        ensures  Service_Next(glsToSs(gls[i]), glsToSs(gls[i+1])) || glsToSs(gls[i]) == glsToSs(gls[i+1]);
    {
        // GlsServerConsistent(gls, config, i+1);
        sameServers(config,gls);
        assert GLS_Next(gls[i], gls[i+1]);
        if i == 0 {
            assert gls[i].ls.servers[config[0]].held;
        } else {
            glsHistorySize(gls, config, i);
            assert |gls[i].history| > 0;
        }
    }


    lemma {:timeLimitMultiplier 2} GLS_To_SS(config:ConcreteConfiguration, gls:seq<GLS_State>) returns (sb:seq<ServiceState>)
        requires |gls| > 0;
        requires GLS_Init(gls[0], config);
        requires forall i {:trigger GLS_Next(gls[i], gls[i+1])} :: 0 <= i < |gls| - 1 ==> GLS_Next(gls[i], gls[i+1]);
        ensures  |sb| == |gls|;
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(gls[0].ls.servers));
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb|-1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
        ensures  forall i :: 0 <= i < |gls| ==> sb[i] == glsToSs(gls[i]);
        ensures  forall i :: 0 <= i < |sb| ==> sb[i].hosts == sb[0].hosts;
        ensures  forall i :: 0 <= i < |sb| ==> GLS_Correspondence(gls[i].ls.environment.sentPackets, sb[i]);

        {
            sb := [glsToSs(gls[0])];
            assert Service_Init(sb[0], Collections__Maps2_s.mapdomain(gls[0].ls.servers));
            assert glsToSs(gls[0]) == sb[0];

            assert Epoch_Inc_History(gls[0]);
            assert LockedOrTransfer(gls[0]);


            assert Transfer_Correspondence(gls[0],config);
            assert GLS_Correspondence(gls[0].ls.environment.sentPackets,sb[0]);


            if(|gls| == 1){
                return sb;
            }else{
                var i := |sb|;
                while i < |gls|
                invariant i == |sb|
                invariant 1 <= i <= |gls|
                invariant Service_Init(sb[0], Collections__Maps2_s.mapdomain(gls[0].ls.servers));
                invariant forall j :: 0 <= j < |sb| ==> glsToSs(gls[j]) == sb[j];
                invariant forall j :: 0 <= j < |sb|-1 ==> Service_Next(glsToSs(gls[j]), glsToSs(gls[j+1])) || glsToSs(gls[j]) == glsToSs(gls[j+1]);
                invariant forall j :: 0 <= j < |sb|-1 ==> sb[j] == sb[j+1] || Service_Next(sb[j], sb[j+1]);
                invariant forall j :: 0 <= j < |sb| ==> sb[j].hosts == sb[0].hosts;
                invariant forall j :: 0 <= j < |sb| ==> sb[j].history == gls[j].history;
                invariant forall j :: 0 <= j < |sb|-1 ==> sb[j].history == sb[j+1].history || exists new_holder :: new_holder in config && sb[j+1].history == sb[j].history + [new_holder];
                invariant forall j :: 0 <= j < |sb| ==> sb[j].hosts == mapdomain(gls[0].ls.servers);

                invariant forall j :: 0 <= j < |sb| ==> GLS_Correspondence(gls[j].ls.environment.sentPackets, sb[j]);
                invariant forall j :: 0 <= j < |sb| ==> Transfer_Correspondence(gls[j], config);
                invariant forall j :: 0 <= j < |sb| ==> Epoch_Inc_History(gls[j]);
                invariant forall j :: 0 <= j < |sb| ==> LockedOrTransfer(gls[j]);


                {
                    sb := sb + [glsToSs(gls[i])];
                    ServiceNextOrEqual(gls,config,i-1);
                    assert Service_Next(glsToSs(gls[i-1]), glsToSs(gls[i])) || glsToSs(gls[i-1]) == glsToSs(gls[i]);

                    if(glsToSs(gls[i-1]) == glsToSs(gls[i])){
                        assert sb[i-1] == sb[i];
                    }else{
                        assert  Service_Next(sb[i-1], sb[i]);
                    }
                    assert sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
                    assert sb[i-1].hosts == sb[i].hosts;
                    assert sb[i].hosts == sb[0].hosts;


                    if( Transfer_Correspondence(gls[i-1],config)
                    && GLS_Correspondence(gls[i-1].ls.environment.sentPackets,sb[i-1])
                    && Epoch_Inc_History(gls[i-1])
                    && LockedOrTransfer(gls[i-1])){
                        Corresponds(gls,gls[i-1],gls[i],sb[i-1],sb[i],config);
                        assert Transfer_Correspondence(gls[i],config);
                        assert GLS_Correspondence(gls[i].ls.environment.sentPackets,sb[i]);
                        assert Epoch_Inc_History(gls[i]);
                        assert LockedOrTransfer(gls[i]);
                    }
                    i := i + 1;
                }
            }

        }


        lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
            requires |db| > 0;
            requires DS_Init(db[0], config);
            requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
            ensures  |db| == |sb|;
            ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));
            ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb|-1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1]);
            ensures forall j :: 0 <= j < |db| ==>  Service_Correspondence(db[j].environment.sentPackets, sb[j]);



             {
                 var ls := DS_To_LS(config,db);
                 var gls := LS_To_GLS(config,ls);
                 sb := GLS_To_SS(config,gls);

                 assert mapdomain(db[0].servers) == MapSeqToSet(config, x=>x);
                 assert mapdomain(db[0].servers) == sb[0].hosts;
                 forall i | 0 <= i < |db|
                   ensures Service_Correspondence(db[i].environment.sentPackets, sb[i])

                 {
                     assert ls[i] == dsTols(db[i]);
                     ShowDemarshallable(db, config);
                     assert GLS_Correspondence(ls[i].environment.sentPackets,sb[i]);
                     showCorr(db[i],sb[i]);
                     assert Service_Correspondence(db[i].environment.sentPackets, sb[i]);

                 }

             }

//
// lemma GlsNextValid(glb:seq<GLS_State>, config:Config, i:int)
//     requires validGLS(glb, config);
//     requires 0 <= i < |glb| - 1;
//     ensures  GLS_Next(glb[i], glb[i+1]);
// {
// }
// lemma GlsServerConsistent(glb:seq<GLS_State>, config:Config, i:int)
//     requires validGLS(glb, config);
//     requires 0 <= i < |glb|;
//     ensures  forall e :: e in config <==> e in glb[i].ls.servers;
//     ensures  forall id :: id in config ==> glb[0].ls.servers[id].config == glb[i].ls.servers[id].config;
// {
//
//     if i > 0 {
//         GlsNextValid(glb, config, i - 1);
//         GlsServerConsistent(glb, config, i - 1);
//     }
// }


// //type LockPacket = LPacket<EndPoint, LockMessage>
//
// lemma lemma_PacketSentByServerIsDemarshallable(
//     config:ConcreteConfiguration,
//     db:seq<DS_State>,
//     i:int,
//     p:LPacket<EndPoint, seq<byte>>
//     )
//     requires validDB(config, db);
//     requires 0 <= i < |db|;
//     requires p.src in config;
//     requires p in db[i].environment.sentPackets;
//     ensures  Demarshallable(p.msg, CMessageGrammar());
// {
//     if i == 0 {
//         return;
//     }
//
//     if p in db[i-1].environment.sentPackets {
//         lemma_PacketSentByServerIsDemarshallable(config, db, i-1, p);
//         return;
//     }
//
//     dsNextValid(config, db, i-1);
//     lemma_DsConsistency(config, db, i-1);
// }
// lemma lemma_DsConsistency(config:ConcreteConfiguration, db:seq<DS_State>, i:int)
//         requires validDB(config, db);
//         requires 0 <= i < |db|;
//         ensures  db[i].config == config;
//         ensures  Collections__Maps2_s.mapdomain(db[i].servers) == Collections__Maps2_s.mapdomain(db[0].servers);
//     {
//         if i == 0 {
//         } else {
//             lemma_DsConsistency(config, db, i-1);
//             dsNextValid(config, db, i-1);
//
//             assert forall server :: server in db[i-1].servers ==> server in db[i].servers;
//             assert forall server :: server in db[i].servers ==> server in db[i-1].servers;
//
//             forall server | server in Collections__Maps2_s.mapdomain(db[i-1].servers)
//                 ensures server in Collections__Maps2_s.mapdomain(db[i].servers)
//             {
//                 assert server in db[i-1].servers;
//                 assert server in db[i].servers;
//
//             }
//
//             forall server | server in Collections__Maps2_s.mapdomain(db[i].servers)
//                 ensures server in Collections__Maps2_s.mapdomain(db[i-1].servers)
//             {
//                 assert server in db[i].servers;
//                 assert server in db[i-1].servers;
//             }
//         }
//     }

}
