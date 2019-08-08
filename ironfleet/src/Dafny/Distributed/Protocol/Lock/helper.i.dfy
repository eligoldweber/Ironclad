
include "./RefinementProof/DistributedSystem.i.dfy"
include "./RefinementProof/Refinement.i.dfy"
include "../../Services/Lock/AbstractService.s.dfy"
include "./Node.i.dfy"
include "Types.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "./LS_helper.i.dfy"


module refinementHelper{
    import opened DistributedSystem_i
    import opened AbstractServiceLock_s
    import opened Protocol_Node_i
    import opened Types_i
    import opened Refinement_i
    import opened Concrete_NodeIdentity_i
    import opened refinementLSHelper


////// ----------------LS TO GLS--------------------------- /////////


    predicate validLS(config:ConcreteConfiguration, sb:seq<LS_State>)
    reads *;
    {
        |sb| > 0
    && LS_Init(sb[0], config)
    && forall i {:trigger LS_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> LS_Next(sb[i], sb[i+1])
    }

    lemma lsNextValid(
             config:Config,
             sb:seq<LS_State>,
             i:int
             )
             requires validLS(config, sb);
             requires 0 <= i < |sb| - 1;
             ensures  LS_Next(sb[i], sb[i+1]);
         {
         }


         predicate Transfer_Epoch_In_History(concretePkts:set<LockPacket>,gls:GLS_State, config:Config) {
             forall p ::
                    p in concretePkts
                 && p.msg.Transfer?
                 && p.src in config
                ==> 2 <= p.msg.transfer_epoch <= |gls.history|
                 && gls.history[p.msg.transfer_epoch-1] == p.dst
         }


    lemma {:timeLimitMultiplier 2} LS_To_GLS(config:ConcreteConfiguration, sb:seq<LS_State>) returns (gsb:seq<GLS_State>)
    requires |sb| > 0;
    requires LS_Init(sb[0], config);
    requires forall i {:trigger LS_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> LS_Next(sb[i], sb[i+1]);
    ensures  |sb| == |gsb|;
    ensures  GLS_Init(gsb[0],config);
    ensures  forall i {:trigger GLS_Next(gsb[i], gsb[i+1])} :: 0 <= i < |gsb| - 1 ==> GLS_Next(gsb[i], gsb[i+1]);
    ensures forall i :: 0 <= i < |sb| ==> gsb[i].ls == sb[i];

    // ensures forall j :: 0 <= j < |sb| ==> Transfer_Epoch_In_History(gsb[j].ls.environment.sentPackets,gsb[j], config);
    // ensures  forall i :: 0 <= i < |sb| ==>(forall j :: j in config <==> j in gsb[i].ls.servers);

    {
        gsb := [GLS_State(sb[0],[config[0]])];
        assert GLS_Init(gsb[0],config);
        assert gsb[0].ls == sb[0];
        assert forall j :: j in config <==> j in gsb[0].ls.servers;
        assert Transfer_Epoch_In_History(gsb[0].ls.environment.sentPackets,gsb[0], config);
        if (|sb| == 1){
            return gsb;
        }else{
            var i := |gsb|;
            while i < |sb|
            invariant i == |gsb|
            invariant 1 <= i <= |sb|
            invariant  GLS_Init(gsb[0],config);
            invariant forall j :: 0 <= j < |gsb| ==> gsb[j].ls == sb[j];
            invariant forall j :: 0 <= j < |gsb|-1 ==> GLS_Next(gsb[j], gsb[j+1]);
            // invariant forall j :: 0 <= j < |gsb| ==> (forall k :: k in config <==> k in gsb[j].ls.servers)
            {
                var mostRecentHistory := last(gsb).history;
                var ls := sb[i-1];
                if ls.environment.nextStep.LEnvStepHostIos? && ls.environment.nextStep.actor in ls.servers {
                    var id := ls.environment.nextStep.actor;
                    var ios := ls.environment.nextStep.ios;
                    lsNextValid(config, sb, i-1);
                    assert LS_Next(sb[i-1], sb[i]);
                    assert LS_NextOneServer(sb[i-1], sb[i], id, ios);
                    var node := ls.servers[id];
                    var node' := sb[i].servers[id];
                    assert NodeNext(node, node', ios);
                    var new_history:seq<EndPoint>;
                    if NodeGrant(node, node', ios) && node.held && node.epoch < 0xFFFF_FFFF_FFFF_FFFF{
                        new_history := mostRecentHistory + [node.config[(node.my_index+1) % |node.config|]];
                    } else {
                        new_history := mostRecentHistory;
                    }
                    gsb := gsb + [GLS_State(sb[i], new_history)];
                    assert GLS_Next(gsb[i-1], gsb[i]);
                    // assert (gsb[i].ls == gsb[i-1].ls || LS_Next(gsb[i-1].ls, gsb[i].ls));
                    assert forall j :: j in gsb[i].ls.servers <==> j in gsb[i-1].ls.servers;

                }else {
                    gsb := gsb + [GLS_State(sb[i], mostRecentHistory)];
                    assert gsb[i-1].history ==  gsb[i].history;
                    // assert forall j :: j in gsb[i].ls.servers <==> j in gsb[i-1].ls.servers;

                }
                // assert forall j :: j in config <==> j in sb[i].servers ;
                // assert Transfer_Epoch_In_History(gsb[i].ls.environment.sentPackets,gsb[i], config);

                assert gsb[i].ls == sb[i];
                i := i + 1;
            }

        }
    }




    predicate validGLS(glb:seq<GLS_State>, config:Config)
    {
        |glb| > 0
        && GLS_Init(glb[0], config)
        && (forall i {:trigger GLS_Next(glb[i], glb[i+1])} :: 0 <= i < |glb| - 1 ==> GLS_Next(glb[i], glb[i+1]))
    }

    function glsToSs(gls:GLS_State) : ServiceState
    {
        ServiceState'(mapdomain(gls.ls.servers),gls.history)
    }




}
