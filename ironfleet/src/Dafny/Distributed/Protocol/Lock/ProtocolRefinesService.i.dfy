//include "Types.i.dfy"
//include "Node.i.dfy"
include "Types.i.dfy"
//include "RefinementProof/DistributedSystem.i.dfy"
include "RefinementProof/Refinement.i.dfy"

module Protocol_Refines_Service {
    // import opened Types_i
    //import opened Protocol_Node_i
    //import opened Native__Io_s
    import opened Types_i
    //import opened DistributedSystem_i
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

    lemma RefineNext(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState, config:Config)
        requires GLS_Next(gls, gls');
        requires s == AbstractifyGLS_State(gls);
        requires s' == AbstractifyGLS_State(gls');
        requires forall holder :: holder in gls.history ==> holder in gls.ls.servers;
        requires forall e :: e in config <==> e in gls.ls.servers;
        requires forall n :: n in gls.ls.servers ==> gls.ls.servers[n].config == config;
        ensures  Service_Next(s, s') || s == s';
        ensures forall holder :: holder in gls'.history ==> holder in gls'.ls.servers;
        ensures forall e :: e in config <==> e in gls'.ls.servers;
        ensures forall n :: n in gls'.ls.servers ==> gls'.ls.servers[n].config == config;
    {
        assert mapdomain(gls.ls.servers) == mapdomain(gls'.ls.servers);
    }

    lemma RefineCorrespondence(gls:GLS_State, gls':GLS_State, s:ServiceState, s':ServiceState, config:Config)
    requires GLS_Next(gls, gls');
    requires s == AbstractifyGLS_State(gls);
    requires s' == AbstractifyGLS_State(gls'); 
    requires Service_Next(s, s') || s == s';
    requires gls.history == s.history;
    requires |config| > 0;
    requires mapdomain(gls.ls.servers) == s.hosts;
    requires forall n :: n in gls.ls.servers ==> gls.ls.servers[n].config == config;
    requires |gls.history| >= 1;
    ensures |gls'.history| >= 1;
    requires forall n :: n in gls.ls.servers ==> |config| > gls.ls.servers[n].my_index >= 0;
    ensures  forall n :: n in gls'.ls.servers ==> |config| > gls'.ls.servers[n].my_index >= 0;
    requires forall e :: e in config <==> e in gls.ls.servers;
    ensures forall e :: e in config <==> e in gls'.ls.servers;
    ensures gls'.history == s'.history;
    
    //Safety invariant : 1 & 2 implies safety
    requires Service_Correspondence(gls.ls.environment.sentPackets, s);
    ensures Service_Correspondence(gls'.ls.environment.sentPackets, s');

    //1. For all valid Locked messages, There exist a valid corresponding transfer messages
    requires forall p :: p in gls.ls.environment.sentPackets 
            && p.src in s.hosts && p.dst in s.hosts && p.msg.Locked? 
            ==> exists q :: q in gls.ls.environment.sentPackets && q.msg.Transfer? 
            && q.dst == p.src && p.msg.locked_epoch == q.msg.transfer_epoch;
    ensures forall p :: p in gls'.ls.environment.sentPackets 
            && p.src in s'.hosts && p.dst in s'.hosts && p.msg.Locked? 
            ==> exists q :: q in gls'.ls.environment.sentPackets && q.msg.Transfer? 
            && q.dst == p.src && p.msg.locked_epoch == q.msg.transfer_epoch;

    //2. All valid transfer messages satisfy the correspondence : 11 implies 2
    requires forall p :: p in gls.ls.environment.sentPackets && p.msg.Transfer? && p.src in gls.ls.servers && p.dst in gls.ls.servers
                        ==> 2 <= p.msg.transfer_epoch <= |gls.history| && gls.history[p.msg.transfer_epoch-1] == p.dst;
    ensures forall p :: p in gls'.ls.environment.sentPackets && p.msg.Transfer? && p.src in gls'.ls.servers && p.dst in gls'.ls.servers
                        ==> 2 <= p.msg.transfer_epoch <= |gls'.history| && gls'.history[p.msg.transfer_epoch-1] == p.dst;

    //3. There is at most one holder and its epoch is the maximum
    requires forall n1 , n2:: n1 in gls.ls.servers && gls.ls.servers[n1].held && n2 in gls.ls.servers  && n1 != n2 
                                ==> !gls.ls.servers[n2].held && gls.ls.servers[n1].epoch > gls.ls.servers[n2].epoch;
    ensures forall n1, n2 :: n1 in gls'.ls.servers && gls'.ls.servers[n1].held && n2 in gls'.ls.servers  && n1 != n2 
                        ==> !gls'.ls.servers[n2].held && gls'.ls.servers[n1].epoch >= gls'.ls.servers[n2].epoch;

    //4. there is no two transfer message with the same transfer epoch
    // requires forall t1, t2 :: t1 in gls.ls.environment.sentPackets && t1.msg.Transfer? && t2 in gls.ls.environment.sentPackets && t2.msg.Transfer? 
    //                 && t1.msg.transfer_epoch == t2.msg.transfer_epoch && t1.src in gls.ls.servers && t2.src in gls.ls.servers
    //                 ==> t1 == t2;
    // ensures forall t1, t2 :: t1 in gls'.ls.environment.sentPackets && t1.msg.Transfer? && t2 in gls'.ls.environment.sentPackets && t2.msg.Transfer? 
    //                 && t1.msg.transfer_epoch == t2.msg.transfer_epoch && t1.src in gls'.ls.servers && t2.src in gls'.ls.servers
    //                 ==> t1 == t2;

    //5. Epoch of the holding node is greater than or equal to all existing valid Transfer packages
    requires forall n, t :: n in gls.ls.servers && t in gls.ls.environment.sentPackets && gls.ls.servers[n].held && t.msg.Transfer? 
                    && t.src in gls.ls.servers ==> gls.ls.servers[n].epoch >= t.msg.transfer_epoch;
    ensures forall n, t :: n in gls'.ls.servers && t in gls'.ls.environment.sentPackets && gls'.ls.servers[n].held && t.msg.Transfer? 
                    && t.src in gls'.ls.servers ==> gls'.ls.servers[n].epoch >= t.msg.transfer_epoch;


    //6. If there is a transfer message for a node with higher epoch, this epoch is equals to length of history
    requires forall n, t :: n in gls.ls.servers && t in gls.ls.environment.sentPackets && t.msg.Transfer? && t.src in gls.ls.servers
                    && t.dst == gls.ls.servers[n].config[gls.ls.servers[n].my_index] && t.msg.transfer_epoch > gls.ls.servers[n].epoch
                        ==> t.msg.transfer_epoch == |gls.history|;
    ensures forall n, t :: n in gls'.ls.servers && t in gls'.ls.environment.sentPackets && t.msg.Transfer? && t.src in gls'.ls.servers
                    && t.dst == gls'.ls.servers[n].config[gls'.ls.servers[n].my_index] && t.msg.transfer_epoch > gls'.ls.servers[n].epoch
                        ==> t.msg.transfer_epoch == |gls'.history|;

    //7. If there is a transfer message with an equal epoch to history length, this is transfer package with maximum length. (It is also unique by 4)
    // requires forall t1, t2 :: t1 in gls.ls.environment.sentPackets && t1.msg.Transfer? && t1.msg.transfer_epoch == |gls.history| 
    //                 && t1.src in gls.ls.servers && t2 in gls.ls.environment.sentPackets && t2.msg.Transfer? && t2.src in gls.ls.servers
    //                 ==> t1.msg.transfer_epoch >= t2.msg.transfer_epoch;
    // ensures forall t1, t2 :: t1 in gls'.ls.environment.sentPackets && t1.msg.Transfer? && t1.msg.transfer_epoch == |gls'.history| 
    //                 && t1.src in gls'.ls.servers && t2 in gls'.ls.environment.sentPackets && t2.msg.Transfer? && t2.src in gls'.ls.servers
    //                 ==> t1.msg.transfer_epoch >= t2.msg.transfer_epoch;

    //8. The message is in 7 also has greater than or equal to all nodes' epoch
    // requires forall n, t :: t in gls.ls.environment.sentPackets && t.msg.Transfer? && t.msg.transfer_epoch == |gls.history| 
    //                 && t.src in gls.ls.servers && n in gls.ls.servers ==> t.msg.transfer_epoch >= gls.ls.servers[n].epoch;
    // ensures forall n, t :: t in gls'.ls.environment.sentPackets && t.msg.Transfer? && t.msg.transfer_epoch == |gls'.history| 
    //                 && t.src in gls'.ls.servers && n in gls'.ls.servers ==> t.msg.transfer_epoch >= gls'.ls.servers[n].epoch;

    //9. If a node's epoch is equal to a valid transfer's epoch, destination of this transfer message is the same node
    // requires forall n, t :: t in gls.ls.environment.sentPackets && t.msg.Transfer? && n in gls.ls.servers && t.src in gls.ls.servers
    //                 && gls.ls.servers[n].epoch == t.msg.transfer_epoch ==> t.dst == gls.ls.servers[n].config[gls.ls.servers[n].my_index];
    // ensures forall n, t :: t in gls'.ls.environment.sentPackets && t.msg.Transfer? && n in gls'.ls.servers && t.src in gls'.ls.servers
    //                 && gls'.ls.servers[n].epoch == t.msg.transfer_epoch ==> t.dst == gls'.ls.servers[n].config[gls'.ls.servers[n].my_index];

    //10. If two node's my_index are the same, they are the same nodes -> I think I don't need this anymore after the change in NodeInit
    // requires forall n1, n2 :: n1 in gls.ls.servers && n2 in gls.ls.servers 
    //                 && config[gls.ls.servers[n1].my_index] == config[gls.ls.servers[n2].my_index]
    //                 ==> n1 == n2;
    // ensures forall n1, n2 :: n1 in gls'.ls.servers && n2 in gls'.ls.servers 
    //                 && config[gls'.ls.servers[n1].my_index] == config[gls'.ls.servers[n2].my_index]
    //                 ==> n1 == n2;

    //11. If there is a holder, its epoch is equal to length of history :: 5 & 6 implies 11
    requires forall n :: n in gls.ls.servers && gls.ls.servers[n].held ==> gls.ls.servers[n].epoch == |gls.history|;
    ensures forall n :: n in gls'.ls.servers && gls'.ls.servers[n].held ==> gls'.ls.servers[n].epoch == |gls'.history|;

    // // ensures forall p :: p in gls'.ls.environment.sentPackets 
    // //                     && p.src in s'.hosts && p.dst in s'.hosts && p.msg.Locked?
    // //                     ==> 1 <= p.msg.locked_epoch <= |s'.history| && p.src == s'.history[p.msg.locked_epoch-1];
    ensures mapdomain(gls'.ls.servers) == s'.hosts;
    {
        ghost var ls := gls.ls;
        ghost var ls' := gls'.ls;
        ghost var environment := ls.environment;
        ghost var environment' := ls'.environment;
        ghost var nextStep := environment.nextStep;

        if nextStep.LEnvStepHostIos?
        {
            if nextStep.actor in ls.servers && NodeGrant(ls.servers[nextStep.actor], ls'.servers[nextStep.actor], nextStep.ios)
            {
                if ls.servers[nextStep.actor].held && ls.servers[nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF
                {
                    // assert |nextStep.ios| == 1;
                    assert nextStep.ios[0].LIoOpSend? && nextStep.ios[0].s.msg.Transfer?
                            && environment'.sentPackets == environment.sentPackets + {nextStep.ios[0].s};
                    // assert nextStep.ios[0].s.msg.transfer_epoch == |gls'.history|;
                    // assert |gls'.history| == |gls.history| + 1;
                    // assert |gls'.history| >= 2;
                    // assert 2 <= nextStep.ios[0].s.msg.transfer_epoch <= |gls'.history|;
                    // assert gls'.history[nextStep.ios[0].s.msg.transfer_epoch-1] == nextStep.ios[0].s.dst;
                    // assert forall n :: n in gls.ls.servers && !gls.ls.servers[n].held ==> !gls'.ls.servers[n].held;
                    // assert forall n1, n2 :: n1 in gls.ls.servers && n2 in  gls.ls.servers && gls.ls.servers[n1].held && gls.ls.servers[n2].held
                    //         ==> n1 == n2;
                    // assert forall n :: n in gls.ls.servers && gls.ls.servers[n].held  ==> gls.ls.servers[n].epoch == 
                    // //history degistigi icin baska tutan varsa siki tuttuk diyo
                    // assert forall n :: n in gls.ls.servers && !gls.ls.servers[n].held ==> gls'.ls.servers[n].held == false;
                    
                    // assert gls.ls.servers[nextStep.actor].my_index == gls'.ls.servers[nextStep.actor].my_index; //I add smt in Node.i for this
                    // assert forall n :: n in gls'.ls.servers ==> |config| > gls'.ls.servers[n].my_index >= 0;

                }
                else {
                    assert environment.sentPackets == environment'.sentPackets;
                    assert gls'.history == gls.history;
                }
      
            }
            else if nextStep.actor in ls.servers && NodeAccept(ls.servers[nextStep.actor], ls'.servers[nextStep.actor], nextStep.ios)
            {
    // requires forall n, t :: n in gls.ls.servers && t in gls.ls.environment.sentPackets && t.msg.Transfer? && t.src in gls.ls.servers
    //                 && t.dst == gls.ls.servers[n].config[gls.ls.servers[n].my_index] && t.msg.transfer_epoch > gls.ls.servers[n].epoch
    //                     ==> t.msg.transfer_epoch == |gls.history|;/node'un kendinden daha buyuk bir epoch u varsa history'e esittir.
    // requires forall t1, t2 :: t1 in gls.ls.environment.sentPackets && t1.msg.Transfer? && t1.msg.transfer_epoch == |gls.history| 
    //                 && t1.src in gls.ls.servers && t2 in gls.ls.environment.sentPackets && t2.msg.Transfer? && t2.src in gls.ls.servers
    //                 ==> t1.msg.transfer_epoch >= t2.msg.transfer_epoch; //history'e esitse o en buyuktur

    //                    ensures forall p :: p in gls'.ls.environment.sentPackets 
    //         && p.src in s'.hosts && p.dst in s'.hosts && p.msg.Locked? 
    //         ==> exists q :: q in gls'.ls.environment.sentPackets && q.msg.Transfer? 
    //         && q.dst == p.src && p.msg.locked_epoch == q.msg.transfer_epoch;

//  ensures forall n, t :: n in gls'.ls.servers && t in gls'.ls.environment.sentPackets && gls'.ls.servers[n].held && t.msg.Transfer? 
//                     && t.src in gls'.ls.servers ==> gls'.ls.servers[n].epoch >= t.msg.transfer_epoch;//if a node holds, it has the bigger epoch than any transfer message
//     ensures forall n1 :: n1 in gls'.ls.servers && gls'.ls.servers[n1].held //holder varsa bunun epoch'u en buyuk
//                             ==> (forall n2 :: n2 in gls'.ls.servers  && n1 != n2 
//                                     ==> !gls'.ls.servers[n2].held && gls'.ls.servers[n1].epoch > gls'.ls.servers[n2].epoch);
                
                // n, t :: t in gls.ls.environment.sentPackets && t.msg.Transfer? && t.msg.transfer_epoch == |gls.history| 
                //     && t.src in gls.ls.servers && n in gls.ls.servers ==> t.msg.transfer_epoch >= gls.ls.servers[n].epoch;
                if  nextStep.ios[0].LIoOpReceive? && nextStep.ios[0].r.src in ls.servers[nextStep.actor].config
                    && nextStep.ios[0].r.msg.Transfer? && !ls.servers[nextStep.actor].held
                    && nextStep.ios[0].r.msg.transfer_epoch > ls.servers[nextStep.actor].epoch
                    && nextStep.ios[0].r.dst == ls.servers[nextStep.actor].config[ls.servers[nextStep.actor].my_index]
                {
                    // assert forall e :: e in config <==> e in gls.ls.servers;
                    // assert exists t :: t in gls.ls.environment.sentPackets && t.msg.Transfer?
                    //     && t.dst ==  nextStep.ios[0].r.dst && t.msg.transfer_epoch == nextStep.ios[0].r.msg.transfer_epoch
                    //     && t.src == nextStep.ios[0].r.src;
                    // assert nextStep.ios[0].r.msg.transfer_epoch == |s.history|;
                    
                    // assert forall n :: n in gls.ls.servers && nextStep.ios[0].r.msg.transfer_epoch == gls.ls.servers[n].epoch 
                    // ==> nextStep.ios[0].r.dst == gls.ls.servers[n].config[gls.ls.servers[n].my_index];
                    // assert nextStep.ios[0].r.dst == ls.servers[nextStep.actor].config[ls.servers[nextStep.actor].my_index]
                    //         && nextStep.ios[0].r.msg.transfer_epoch > ls.servers[nextStep.actor].epoch;
                    // assert forall n :: n in gls.ls.servers && nextStep.ios[0].r.dst == gls.ls.servers[n].config[gls.ls.servers[n].my_index]
                    // ==> nextStep.ios[0].r.msg.transfer_epoch > gls.ls.servers[n].epoch;
                    // assert forall n :: n in gls.ls.servers ==> nextStep.ios[0].r.msg.transfer_epoch > gls.ls.servers[n].epoch;//>= inaniyor, esit olamaz cunku ayni
                    // assert !(exists n :: n in gls.ls.servers && gls.ls.servers[n].epoch >= nextStep.ios[0].r.msg.transfer_epoch);

                    assert |nextStep.ios| == 2;
                    assert nextStep.ios[1].LIoOpSend? && nextStep.ios[1].s.msg.Locked?
                        && environment'.sentPackets == environment.sentPackets + {nextStep.ios[1].s};
                    // assert s.history == s'.history;
                    // assert nextStep.ios[0].r.msg.transfer_epoch == nextStep.ios[1].s.msg.locked_epoch;
                }
                else
                {
                    assert environment.sentPackets == environment'.sentPackets;
                }

            }
            else {
                assert s.hosts == s'.hosts;
                assert mapdomain(ls.servers) == s'.hosts;
                assert !(nextStep.actor in ls.servers); 
                assert forall p :: p in nextStep.ios ==> !(p.LIoOpSend? && p.s.src in ls.servers);
                assert forall p :: p in environment'.sentPackets - environment.sentPackets ==> !(p.src in ls.servers);
            }
        }
        else {
            assert environment.sentPackets == environment'.sentPackets;
        }
    }

    lemma RefinementProof(config:Config, db:seq<GLS_State>) returns (sb:seq<ServiceState>)
    requires |db| > 0;
    requires GLS_Init(db[0], config);
    requires forall i {:trigger GLS_Next(db[i-1], db[i])} :: 0 < i < |db| ==> GLS_Next(db[i-1], db[i]);
    ensures  |db| == |sb|;
    ensures  Service_Init(sb[0], mapdomain(db[0].ls.servers));
    ensures  forall i {:trigger Service_Next(sb[i-1], sb[i])} :: 0 < i < |sb| ==> sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
    //ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]);
    {
        sb:=[AbstractifyGLS_State(db[0])];

        // assert forall n :: n in db[0].ls.servers ==> NodeInit(db[0].ls.servers)
        // assert forall n :: n in db[0].ls.servers ==> |config| > db[0].ls.servers[n].my_index >= 0;
        // assume forall n1, n2 :: n1 in db[0].ls.servers && n2 in db[0].ls.servers 
        //             && config[db[0].ls.servers[n1].my_index] == config[db[0].ls.servers[n2].my_index]
        //             ==> n1 == n2;
        // assume  forall n :: n in db[0].ls.servers ==> db[0].ls.servers[n].config == config;

        // requires s == AbstractifyGLS_State(gls);
        // requires s' == AbstractifyGLS_State(gls');
        // requires forall holder :: holder in gls.history ==> holder in gls.ls.servers;
        // requires forall n :: n in gls.ls.servers ==> (forall e :: e in gls.ls.servers[n].config <==> e in mapdomain(gls.ls.servers));

        var i := 1;
        while(i < |db|)
            invariant |sb| == i;
            invariant 0 < i <= |db|;
            invariant Service_Init(sb[0], mapdomain(db[0].ls.servers));
            invariant forall i :: 0 < i < |sb| ==> sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
            invariant forall i :: 0 <= i < |sb| ==> sb[i] == AbstractifyGLS_State(db[i]);
            invariant |db[i-1].history| >= 1;

            invariant forall e :: e in config <==> e in db[i-1].ls.servers;
            invariant forall n :: n in db[i-1].ls.servers ==> db[i-1].ls.servers[n].config == config;
            invariant forall holder :: holder in db[i-1].history ==> holder in db[i-1].ls.servers;
            invariant forall n :: n in db[i-1].ls.servers ==> |config| > db[i-1].ls.servers[n].my_index >= 0;

            invariant forall i :: 0 <= i < |sb| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]); //Invariant for safety
            invariant forall p :: p in db[i-1].ls.environment.sentPackets && p.src in sb[i-1].hosts && p.dst in sb[i-1].hosts && p.msg.Locked? 
                                ==> exists q :: q in db[i-1].ls.environment.sentPackets && q.msg.Transfer? 
                                    && q.dst == p.src && p.msg.locked_epoch == q.msg.transfer_epoch;//Invariant for 1
            invariant forall p :: p in db[i-1].ls.environment.sentPackets && p.msg.Transfer? && p.src in db[i-1].ls.servers && p.dst in db[i-1].ls.servers
                                ==> 2 <= p.msg.transfer_epoch <= |db[i-1].history| && db[i-1].history[p.msg.transfer_epoch-1] == p.dst;//Invariant for 2
            invariant forall n :: n in db[i-1].ls.servers && db[i-1].ls.servers[n].held ==> db[i-1].ls.servers[n].epoch == |db[i-1].history|;//Invariant for 11
            invariant forall n, t :: n in db[i-1].ls.servers && t in db[i-1].ls.environment.sentPackets && db[i-1].ls.servers[n].held && t.msg.Transfer? 
                    && t.src in db[i-1].ls.servers ==> db[i-1].ls.servers[n].epoch >= t.msg.transfer_epoch; //Invariant for 5
            invariant forall n, t :: n in db[i-1].ls.servers && t in db[i-1].ls.environment.sentPackets && t.msg.Transfer? && t.src in db[i-1].ls.servers
                    && t.dst == db[i-1].ls.servers[n].config[db[i-1].ls.servers[n].my_index] && t.msg.transfer_epoch > db[i-1].ls.servers[n].epoch
                        ==> t.msg.transfer_epoch == |db[i-1].history|;//Invariant for 6

            // invariant forall n :: n in db[i-1].ls.servers ==> (forall e :: e in db[i-1].ls.servers[n].config <==> e in mapdomain(db[i-1].ls.servers));
          

            // invariant forall t1, t2 :: t1 in db[i-1].ls.environment.sentPackets && t1.msg.Transfer? && t2 in db[i-1].ls.environment.sentPackets && t2.msg.Transfer? 
            //         && t1.msg.transfer_epoch == t2.msg.transfer_epoch && t1.src in db[i-1].ls.servers && t2.src in db[i-1].ls.servers ==> t1 == t2;

            
            // invariant forall n1, n2 :: n1 in db[i-1].ls.servers && n2 in db[i-1].ls.servers 
            //         && config[db[i-1].ls.servers[n1].my_index] == config[db[i-1].ls.servers[n2].my_index]
            //         ==> n1 == n2;
            // invariant forall t1, t2 :: t1 in db[i-1].ls.environment.sentPackets && t1.msg.Transfer? && t1.msg.transfer_epoch == |db[i-1].history| 
            //         && t1.src in db[i-1].ls.servers && t2 in db[i-1].ls.environment.sentPackets && t2.msg.Transfer? && t2.src in db[i-1].ls.servers
            //         ==> t1.msg.transfer_epoch >= t2.msg.transfer_epoch;
            // invariant forall n, t :: t in db[i-1].ls.environment.sentPackets && t.msg.Transfer? && n in db[i-1].ls.servers && t.src in db[i-1].ls.servers
            //         && db[i-1].ls.servers[n].epoch == t.msg.transfer_epoch ==> t.dst == db[i-1].ls.servers[n].config[db[i-1].ls.servers[n].my_index];
            // invariant forall n, t :: t in db[i-1].ls.environment.sentPackets && t.msg.Transfer? && t.msg.transfer_epoch == |db[i-1].history| 
            //         && t.src in db[i-1].ls.servers && n in db[i-1].ls.servers ==> t.msg.transfer_epoch >= db[i-1].ls.servers[n].epoch;
            // invariant forall n1, n2 :: n1 in db[i-1].ls.servers && db[i-1].ls.servers[n1].held && n2 in db[i-1].ls.servers  && n1 != n2 
            //                                 ==> !db[i-1].ls.servers[n2].held && db[i-1].ls.servers[n1].epoch > db[i-1].ls.servers[n2].epoch;
        {
            sb := sb + [AbstractifyGLS_State(db[i])];
            RefineNext(db[i-1], db[i], sb[i-1], sb[i], config);
            RefineCorrespondence(db[i-1], db[i] , sb[i-1], sb[i], config);
            i := i + 1;
        }
    }
}