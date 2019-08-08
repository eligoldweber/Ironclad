include "./RefinementProof/DistributedSystem.i.dfy"
include "./RefinementProof/Refinement.i.dfy"
include "../../Services/Lock/AbstractService.s.dfy"
include "./Node.i.dfy"
include "Types.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "./helper.i.dfy"
include "correspondsMarshall.i.dfy"


module fullCoresponds{
     import opened DistributedSystem_i
     import opened AbstractServiceLock_s
     import opened Protocol_Node_i
     import opened Types_i
     import opened Refinement_i
     import opened Concrete_NodeIdentity_i
     import opened refinementHelper
     import opened correspondsMarshal


    predicate GLS_Correspondence(concretePkts:set<LockPacket>, serviceState:ServiceState)
    {
         forall p ::
                p in concretePkts
             && p.src in serviceState.hosts
             && p.dst in serviceState.hosts
             && p.msg.Locked?
             ==> 1 <= p.msg.locked_epoch <= |serviceState.history|
                 && p.src == serviceState.history[p.msg.locked_epoch-1]
    }

    predicate Transfer_Correspondence(gls:GLS_State, config:Config)
    {
        forall p ::
               p in gls.ls.environment.sentPackets
            && p.msg.Transfer?
            && p.src in config
            ==> 1 < p.msg.transfer_epoch <= |gls.history|
            && gls.history[p.msg.transfer_epoch-1] == p.dst
            && gls.history[p.msg.transfer_epoch-2] == p.src
    }


    predicate OnlyTransfer(gls:GLS_State)
    {

        |gls.history| > 1
        && exists p :: p in gls.ls.environment.sentPackets
            && p.msg.Transfer?
            && p.dst == gls.history[|gls.history|-1]
            && p.src == gls.history[|gls.history|-2]
            && forall s :: s in gls.ls.servers ==> !gls.ls.servers[s].held

    }
    predicate OneLocked(gls:GLS_State)
    {

        |gls.history| > 0
        && forall s :: s in gls.ls.servers ==>
            (s == gls.history[|gls.history|-1] <==> gls.ls.servers[s].held)
            && (gls.ls.servers[s].held ==> gls.ls.servers[s].epoch == |gls.history|)
            && (s != gls.history[|gls.history|-1] ==>  !gls.ls.servers[s].held)

    }

    predicate LockedOrTransfer(gls:GLS_State)
    {
        OneLocked(gls) || OnlyTransfer(gls)
    }

    predicate Epoch_Inc_History(gls:GLS_State)
    {
        forall s, i ::
            s in gls.ls.servers
            && 0 <= i < |gls.history|
            && gls.history[i] == s
            && i != |gls.history| - 1
            ==> gls.ls.servers[s].epoch > i
    }


    lemma correspondsAccept(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState, config:ConcreteConfiguration)
             requires s == glsToSs(gls);
             requires s' == glsToSs(gls');
             requires GLS_Next(gls,gls');
             requires s == s' || Service_Next(s, s');
             requires gls.ls.environment.nextStep.LEnvStepHostIos?;
             requires gls.ls.environment.nextStep.actor in gls.ls.servers;
             requires NodeAccept(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios);
             requires GLS_Correspondence(gls.ls.environment.sentPackets,s);
             requires gls.ls.environment.nextStep.ios[0].LIoOpReceive?;
             requires !gls.ls.servers[gls.ls.environment.nextStep.actor].held;
             requires gls.ls.environment.nextStep.ios[0].r.src in gls.ls.servers[gls.ls.environment.nextStep.actor].config;
             requires gls.ls.environment.nextStep.ios[0].r.msg.Transfer?;
             requires gls.ls.environment.nextStep.ios[0].r.msg.transfer_epoch > gls.ls.servers[gls.ls.environment.nextStep.actor].epoch;

             requires Transfer_Correspondence(gls,config);
             requires LockedOrTransfer(gls)
             requires Epoch_Inc_History(gls)
             requires forall j :: j in gls.ls.servers ==> gls.ls.servers[j].config == config;

             ensures GLS_Correspondence(gls'.ls.environment.sentPackets,s);
             ensures Transfer_Correspondence(gls',config);
             ensures Epoch_Inc_History(gls');
             ensures LockedOrTransfer(gls');

        {
                  var id := gls.ls.environment.nextStep.actor;
                  var ios := gls.ls.environment.nextStep.ios;

                  assert |gls.ls.environment.nextStep.ios| == 2;
                  assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets + {gls.ls.environment.nextStep.ios[1].s};
                  assert gls.ls.environment.nextStep.ios[1].LIoOpSend? && gls.ls.environment.nextStep.actor == gls.ls.environment.nextStep.ios[1].s.src;
                  assert gls.ls.environment.nextStep.ios[1].s.msg.Locked?;
                  assert gls.ls.environment.nextStep.ios[1].s.src in s'.hosts;
                  assert  gls'.ls.servers[gls.ls.environment.nextStep.actor].held;
                  assert gls'.ls.servers[gls.ls.environment.nextStep.actor].epoch == gls.ls.environment.nextStep.ios[1].s.msg.locked_epoch;
                  assert gls.ls.servers[gls.ls.environment.nextStep.actor].config ==  gls'.ls.servers[gls.ls.environment.nextStep.actor].config;

                  assert (gls.ls.environment.nextStep.ios[1].s.msg.locked_epoch > gls.ls.servers[gls.ls.environment.nextStep.actor].epoch);

                  assert  gls.ls.servers[gls.ls.environment.nextStep.actor].epoch <= gls'.ls.servers[gls.ls.environment.nextStep.actor].epoch-1;

                  assert IsValidLIoOp(gls.ls.environment.nextStep.ios[0], gls.ls.environment.nextStep.actor, gls.ls.environment);

                  assert forall s :: s in gls'.ls.servers  ==> (s == gls'.history[|gls'.history|-1] <==> gls'.ls.servers[s].held);
                  assert forall s :: s in gls'.ls.servers  && s != gls'.history[|gls'.history|-1] ==>  !gls'.ls.servers[s].held;

                  assert GLS_Correspondence(gls.ls.environment.sentPackets,s');
                  assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');

        }


        lemma Corresponds(glsb:seq<GLS_State>,gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState, config:ConcreteConfiguration)
            requires |glsb| > 0;
            requires GLS_Init(glsb[0], config);
            requires forall i {:trigger GLS_Next(glsb[i], glsb[i+1])} :: 0 <= i < |glsb| - 1 ==> GLS_Next(glsb[i], glsb[i+1]);
            requires gls in glsb;
            requires s == glsToSs(gls);
            requires s' == glsToSs(gls');
            requires GLS_Next(gls,gls');
            requires s == s' || Service_Next(s, s');

            requires Epoch_Inc_History(gls);
            requires LockedOrTransfer(gls);

            requires Transfer_Correspondence(gls,config);
            requires GLS_Correspondence(gls.ls.environment.sentPackets,s);

            ensures Epoch_Inc_History(gls');
            ensures LockedOrTransfer(gls');
            ensures GLS_Correspondence(gls'.ls.environment.sentPackets,s');
            ensures Transfer_Correspondence(gls',config);


            {
                 if  (gls.ls.environment.nextStep.LEnvStepHostIos? && gls.ls.environment.nextStep.actor in gls.ls.servers){
                    if (NodeGrant(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios)){
                        if (gls.ls.servers[gls.ls.environment.nextStep.actor].held && gls.ls.servers[gls.ls.environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF){

                            assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets + {gls.ls.environment.nextStep.ios[0].s};
                            assert s'.history != s.history ;
                            assert gls.ls.environment.nextStep.ios[0].s.msg.Transfer?;

                            assert |gls.ls.environment.nextStep.ios| > 0;
                            assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');

                            assert gls.ls.environment.nextStep.ios[0].s.msg.transfer_epoch == |gls'.history|;
                            forall p | p in gls'.ls.environment.sentPackets
                                && p.msg.Transfer?
                                && p.src in config
                            ensures 1 < p.msg.transfer_epoch <= |gls'.history|
                            ensures gls'.history[p.msg.transfer_epoch-1] == p.dst
                            {
                                if (p == gls.ls.environment.nextStep.ios[0].s) {
                                    assert p.msg.Transfer?;
                                    assert p.msg.transfer_epoch == |gls'.history|;
                                    assert p.msg.transfer_epoch == gls.ls.servers[gls.ls.environment.nextStep.actor].epoch+1;
                                    assert 1 < p.msg.transfer_epoch <= |gls'.history|;
                                    assert p.dst == gls.ls.servers[gls.ls.environment.nextStep.actor].config[(gls.ls.servers[gls.ls.environment.nextStep.actor].my_index + 1) % |gls.ls.servers[gls.ls.environment.nextStep.actor].config|];
                                    assert (forall x :: x in gls'.ls.servers ==> !gls'.ls.servers[x].held);
                                }
                            }
                            assert IsValidLIoOp(gls.ls.environment.nextStep.ios[0], gls.ls.environment.nextStep.actor, gls.ls.environment);

                         }else{
                              assert s' == s ;
                              assert |gls.ls.environment.nextStep.ios| == 0;
                              assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');

                         }
                          // assert Epoch_Inc_History(gls');
                     }else{
                         assert gls'.history == gls.history  && s == s' && s'.history == s.history ;
                         assert |s'.history| == |s.history|;
                         assert gls'.ls.servers == gls.ls.servers[gls.ls.environment.nextStep.actor := gls'.ls.servers[gls.ls.environment.nextStep.actor]];
                         assert NodeAccept(gls.ls.servers[gls.ls.environment.nextStep.actor], gls'.ls.servers[gls.ls.environment.nextStep.actor], gls.ls.environment.nextStep.ios);
                          assert |gls.ls.environment.nextStep.ios| >= 1;
                          if(gls.ls.environment.nextStep.ios[0].LIoOpTimeoutReceive?){
                               assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets;
                               assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');
                          }else{
                              assert gls.ls.environment.nextStep.ios[0].LIoOpReceive?;
                              if(!gls.ls.servers[gls.ls.environment.nextStep.actor].held && gls.ls.environment.nextStep.ios[0].r.src in gls.ls.servers[gls.ls.environment.nextStep.actor].config
                                  && gls.ls.environment.nextStep.ios[0].r.msg.Transfer?  && gls.ls.environment.nextStep.ios[0].r.msg.transfer_epoch > gls.ls.servers[gls.ls.environment.nextStep.actor].epoch ){

                                       sameConfig(config,glsb,gls);
                                       assert forall j :: j in gls.ls.servers ==> gls.ls.servers[j].config == config;
                                       correspondsAccept(gls,gls',s,s',config);
                                       assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');
                                       assert Transfer_Correspondence(gls',config);
                                       assert (forall x :: x in gls.ls.servers ==> !gls.ls.servers[x].held);
                                       assert gls'.ls.servers[gls.ls.environment.nextStep.actor].held;
                                  }else{
                                       assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');
                                       assert Transfer_Correspondence(gls', config);
                                  }
                          }

                     }

                 }else{
                      assert gls'.history == gls.history && s'.history == s.history && gls.ls.servers ==  gls'.ls.servers && s == s';
                      if(gls.ls.environment.nextStep.LEnvStepStutter? || gls.ls.environment.nextStep.LEnvStepAdvanceTime? || gls.ls.environment.nextStep.LEnvStepDeliverPacket?){
                          assert gls'.ls.environment.sentPackets == gls.ls.environment.sentPackets;
                          assert GLS_Correspondence(gls'.ls.environment.sentPackets,s');
                      }else{
                          assert gls.ls.environment.nextStep.LEnvStepHostIos?;
                          assert !(gls.ls.environment.nextStep.actor in gls.ls.servers);
                          assert |gls.ls.environment.nextStep.ios| >= 0;

                          sameServers(config, glsb);
                          assert Transfer_Correspondence(gls',config);

                      }
                  }

        }




    lemma sameServers(config:Config, gls:seq<GLS_State>)
            requires |gls| > 0
            requires GLS_Init(gls[0], config)
            requires forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
            ensures forall i :: 0 <= i < |gls| ==> (forall j :: j in config <==> j in gls[i].ls.servers)
            ensures forall i :: 0 <= i < |gls| ==>(forall id :: id in config ==> gls[0].ls.servers[id].config == gls[i].ls.servers[id].config);

    {
                assert forall j :: j in config <==> j in gls[0].ls.servers;
                var k := 1;
                while (k < |gls|)
                invariant 1 <= k <= |gls|
                invariant forall i :: 0 <= i < k ==> (forall j :: j in config <==> j in gls[i].ls.servers)
                invariant forall i :: 0 <= i < k ==> (forall id :: id in config ==> gls[0].ls.servers[id].config == gls[i].ls.servers[id].config)

                {
                    var kk := k-1;
                    assert (gls[kk+1] == gls[kk] || GLS_Next(gls[kk], gls[kk+1]));
                    assert forall j :: j in gls[k].ls.servers <==> j in gls[k-1].ls.servers;
                    assert forall id :: id in config ==> gls[0].ls.servers[id].config == gls[k-1].ls.servers[id].config;
                    k := k + 1;
                }
    }

    lemma sameConfig(config:Config, gls:seq<GLS_State>,g:GLS_State)
        requires |gls| > 0
        requires GLS_Init(gls[0], config)
        requires g in gls
        requires forall i :: 0 <= i < |gls|-1 ==> GLS_Next(gls[i], gls[i+1]) || gls[i] == gls[i+1]
        ensures forall i :: 0 <= i < |gls| ==> forall j :: j in gls[i].ls.servers ==> gls[i].ls.servers[j].config == config
        ensures forall j :: j in g.ls.servers ==> g.ls.servers[j].config == config;

    {
        assert forall j :: j in gls[0].ls.servers ==> gls[0].ls.servers[j].config == config;

        var k := 1;
        while (k < |gls|)
        invariant 1 <= k <= |gls|
        invariant forall i :: 0 <= i < k ==> forall j :: j in gls[i].ls.servers ==> gls[i].ls.servers[j].config == config;

        {
            assert forall i :: 0 <= i < k ==> forall j :: j in gls[i].ls.servers ==> gls[i].ls.servers[j].config == config;
            assert 0 <= k-1 < |gls|-1;
            assert (gls[k-1] == gls[k] || GLS_Next(gls[k-1], gls[k]));
            assert forall j :: j in gls[k].ls.servers ==> gls[k].ls.servers[j].config == gls[k-1].ls.servers[j].config;
            k := k + 1;
        }
        assert forall j :: j in g.ls.servers ==> g.ls.servers[j].config == config;

    }
/////////////////////////////////////////

    predicate SentDemarshallable(ps:set<LPacket<EndPoint, seq<byte>>>, config:ConcreteConfiguration)
    {
            forall p ::
                   p in ps
                && p.src in config
               ==> Demarshallable(p.msg, CMessageGrammar())
    }

    lemma ShowDemarshallable(db:seq<DS_State>, config:ConcreteConfiguration)
        requires |db| > 0
        requires DS_Init(db[0], config)
        requires forall i :: 0 <= i < |db|-1 ==> DS_Next(db[i], db[i+1])
        ensures forall i :: 0 <= i < |db| ==> forall j :: j in db[i].servers <==> j in config
        ensures forall i :: 0 <= i < |db| ==> SentDemarshallable(db[i].environment.sentPackets, config)
    {
        assert SentDemarshallable(db[0].environment.sentPackets, config);

        var k := 1;
        while (k < |db|)
        invariant 0 <= k <= |db|
        invariant forall i :: 0 <= i < k ==> SentDemarshallable(db[i].environment.sentPackets, config)
        invariant forall i :: 0 <= i < k ==> forall j :: j in db[i].servers <==> j in config
        {
            var kk := k - 1;
            assert DS_Next(db[kk], db[kk+1]);
            assert forall i :: i in db[kk].servers <==> i in config;
            if (db[kk].environment.nextStep.LEnvStepHostIos?
             && db[kk].environment.nextStep.actor in db[kk].servers) {
                var id := db[kk].environment.nextStep.actor;
                var ios := db[kk].environment.nextStep.ios;
                assert OnlySentMarshallableData(db[kk].environment.nextStep.ios);
                assert SentDemarshallable(db[kk+1].environment.sentPackets, config);
            } else {

                assert SentDemarshallable(db[kk+1].environment.sentPackets, config);
            }

            assert mapdomain(db[kk].servers) == mapdomain(db[kk+1].servers);


            k := k + 1;
        }

    }


    lemma showCorr(ds:DS_State, serviceState:ServiceState)
        requires forall i :: i in ds.config ==> i in ds.servers;
        requires ValidConfig(ds.config);
        requires GLS_Correspondence(dsTols(ds).environment.sentPackets,serviceState);
        requires forall p :: (p in ds.environment.sentPackets && p.src in serviceState.hosts) ==> Demarshallable(p.msg, CMessageGrammar());
        ensures Service_Correspondence(ds.environment.sentPackets, serviceState)
    {
        forall p, epoch |
            p in ds.environment.sentPackets
            && p.src in serviceState.hosts
            && p.dst in serviceState.hosts
            && p.msg == MarshallLockMsg(epoch)
            ensures 1 <= epoch <= |serviceState.history|
            ensures p.src == serviceState.history[epoch-1]
            {
                var ls := dsTols(ds);
                var lockP := AbstractifyUdpPacket(p);
                assert lockP in ls.environment.sentPackets;
                assert Demarshallable(p.msg, CMessageGrammar());
                MarshallLockedMsg(lockP.msg, p.msg, epoch);

                assert lockP.msg.Locked?;
                assert lockP.src in serviceState.hosts;
                assert lockP.dst in serviceState.hosts;
                assert 1 <= lockP.msg.locked_epoch <= |serviceState.history|;
                assert epoch == lockP.msg.locked_epoch;
            }

    }



    // sameConfig(config,glsb,gls);
    // sameServers(config, glsb);
    // History_Larger_Than_1(glsb,config);
    // Transfer_Epoch_In_History_Next(gls,gls',config);

    // predicate Held_Epoch_Last(gls:GLS_State)
    // {
    //     |gls.history| > 0 && forall s :: s in gls.ls.servers
    //         && gls.ls.servers[s].held ==> gls.ls.servers[s].epoch == |gls.history|
    // }

    // predicate Epoch_Inc_History1(gls:GLS_State)
    // {
    //     forall s, e ::
    //         s in gls.ls.servers
    //         && 0 <= e < |gls.history|
    //         && gls.history[e] == s
    //         && (e != |gls.history| - 1 || gls.ls.servers[s].held)
    //         ==> gls.ls.servers[s].epoch >= e+1
    // }

        // predicate OneHold_Or_OnyTransfer(gls:GLS_State)
        // {
        //
        //     (|gls.history| > 0 && forall s :: s in gls.ls.servers
        //                         ==> (s == gls.history[|gls.history|-1] <==> gls.ls.servers[s].held)
        //                         && (gls.ls.servers[s].held ==> gls.ls.servers[s].epoch == |gls.history|))
        //     || (|gls.history| > 1 && exists p :: p in gls.ls.environment.sentPackets
        //                         && p.msg.Transfer?
        //                         && p.dst == gls.history[|gls.history|-1]
        //                         && p.src == gls.history[|gls.history|-2]
        //                         && forall s :: s in gls.ls.servers ==> !gls.ls.servers[s].held)
        //
        // }
    //
    // predicate Epoch_Inc_History2(gls:GLS_State)
    // {
    //     forall s, e ::
    //         s in gls.ls.servers
    //         && 0 <= e < |gls.history|
    //         && gls.history[e] == s
    //         && e == |gls.history| - 1
    //         ==> gls.ls.servers[s].epoch == e + 91
    // }


}
