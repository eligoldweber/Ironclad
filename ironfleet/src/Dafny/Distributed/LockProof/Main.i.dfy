include "../Common/Framework/Main.s.dfy"
include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"
include "../Impl/Lock/Host.i.dfy"
include "../Impl/lock/Node.i.dfy"
include "../Impl/Lock/NodeImpl.i.dfy"
include "../Common/Collections/Seqs.s.dfy"
include "../Common/Framework/DistributedSystem.s.dfy"
include "proof.i.dfy"

abstract module Main_i refines Main_s {
    import opened DS_s = DistributedSystem_i  
    import opened LockProof
    import opened AS_s = AbstractServiceLock_s
    import opened Host_i 

    type RealMsg = seq<byte>;
    // function ConstructLockMessage(msg:RealMsg) : LockMessage
    // {
    //     AbstractifyCMessage(DemarshallData(msg))
    // }

    // function AbstractifyUdpPacket(p:LPacket<EndPoint, RealMsg>) : LPacket<EndPoint, LockMessage>
    // {
    //     LPacket(p.src, p.dst, ConstructLockMessage(p.msg))
    // }

    function ConstructSentPackets(ps:set<LPacket<EndPoint, RealMsg>>) : set<LPacket<EndPoint, LockMessage>>
    {
        set p | p in ps :: AbstractifyUdpPacket(p)
    }

    function ConstructNextStep(nextStep:LEnvStep<EndPoint, RealMsg>) : LEnvStep<EndPoint, LockMessage> 
    {
        match nextStep {
            case LEnvStepHostIos(actor, ios) => LEnvStepHostIos(actor, AbstractifyRawLogToIos(ios))
            case LEnvStepDeliverPacket(p) => LEnvStepDeliverPacket(AbstractifyUdpPacket(p))
            case LEnvStepAdvanceTime => LEnvStepAdvanceTime()
            case LEnvStepStutter => LEnvStepStutter()
        }
    }

    function ConstructLEnv(env:LEnvironment<EndPoint, RealMsg>) : LockEnvironment
    {
        var step := ConstructNextStep(env.nextStep);

        LEnvironment(env.time, ConstructSentPackets(env.sentPackets), map [], step)
    }

    function ConstructServers(servers:map<EndPoint, Host_i.HostState>) : map<EndPoint, Node>
    {
        map i | i in servers :: servers[i].node
    }

    function Construct_LS_State(ds:DS_State) : LS_State
    {
        var environment := ConstructLEnv(ds.environment);
        var servers := ConstructServers(ds.servers);
        LS_State(environment, servers)
    }

    lemma ValidLEnvTransfer(de:LEnvironment<EndPoint, RealMsg>)
    requires IsValidLEnvStep(de, de.nextStep)
    ensures IsValidLEnvStep(ConstructLEnv(de), ConstructLEnv(de).nextStep)
    {
        var le := ConstructLEnv(de);
        var step := le.nextStep;
        if (step.LEnvStepHostIos?) {
            var actor := step.actor;
            var ios := step.ios;
            assert de.nextStep.LEnvStepHostIos?;
            var dactor := de.nextStep.actor;
            var dios := de.nextStep.ios;
            assert actor == dactor;
            forall i |
                   0 <= i < |ios|
            ensures IsValidLIoOp(ios[i], actor, le)
            {   
                assert ios[i] == AstractifyUdpEventToLockIo(dios[i]);
                match ios[i] {
                    case LIoOpSend(s) => {
                        assert dios[i].LIoOpSend?;
                        assert s.src == dios[i].s.src;
                        assert IsValidLIoOp(dios[i], dactor, de);
                        assert dios[i].s.src == dactor;
                        assert s.src == actor;
                    }
                    case LIoOpReceive(r) => {
                        assert dios[i].LIoOpReceive?;
                        assert r.dst == dios[i].r.dst;
                        assert IsValidLIoOp(dios[i], dactor, de);
                        assert dios[i].r.dst == dactor;
                        assert r.dst == actor;
                    }
                    case LIoOpTimeoutReceive => assert true;
                    case LIoOpReadClock(t) => assert true;
                }
                assert IsValidLIoOp(ios[i], actor, le);
            }
        } 
    }


    lemma DS_Next_Implies_LEnv_Next(ds:DS_State, ds':DS_State)
    requires DS_Next(ds, ds')
    ensures LEnvironment_Next(Construct_LS_State(ds).environment, Construct_LS_State(ds').environment)
    {
        var ls := Construct_LS_State(ds);
        var ls':= Construct_LS_State(ds');
        assert IsValidLEnvStep(ds.environment, ds.environment.nextStep);
        ValidLEnvTransfer(ds.environment);
        assert IsValidLEnvStep(ls.environment, ls.environment.nextStep);
        match ls.environment.nextStep {
            case LEnvStepHostIos(actor, ios) => 
                assert LEnvironment_PerformIos(ds.environment, 
                                               ds'.environment, 
                                               ds.environment.nextStep.actor, 
                                               ds.environment.nextStep.ios);

                var de := ds.environment;
                var de':= ds'.environment;
                var le := ls.environment;
                var le':= ls'.environment;
                assert de.nextStep.LEnvStepHostIos?;
                var dactor := de.nextStep.actor;
                var dios := de.nextStep.ios;


                assert de'.sentPackets == de.sentPackets + (set io | io in dios && io.LIoOpSend? :: io.s);

                var dsent := set io | io in dios && io.LIoOpSend? :: io.s;
                var lsent := set io | io in ios && io.LIoOpSend? :: io.s;
                assert ios == AbstractifyRawLogToIos(dios);

                forall i |
                       0 <= i < |ios|
                ensures ios[i].LIoOpSend? == dios[i].LIoOpSend?
                ensures ios[i].LIoOpSend? ==> (ios[i].s == AbstractifyUdpPacket(dios[i].s))
                {}

                assert lsent == ConstructSentPackets(dsent);
                assert le'.sentPackets == le.sentPackets + (set io | io in ios && io.LIoOpSend? :: io.s);
                forall i |
                       0 <= i < |ios|
                    && ios[i].LIoOpReceive?
                ensures ios[i].r in le.sentPackets
                {
                    assert dios[i].r in de.sentPackets;
                    assert le.sentPackets == set p | p in de.sentPackets :: AbstractifyUdpPacket(p);
                    assert ios[i] == AstractifyUdpEventToLockIo(dios[i]);
                    assert ios[i].r == AbstractifyUdpPacket(dios[i].r);
                    assert ios[i].r in le.sentPackets;
                }

                assert LEnvironment_PerformIos(ls.environment, ls'.environment, actor, ios);
            case LEnvStepDeliverPacket(p) => 
                assert LEnvironment_Stutter(ls.environment, ls'.environment);
            case LEnvStepAdvanceTime => 
                assert LEnvironment_AdvanceTime(ls.environment, ls'.environment);
            case LEnvStepStutter => 
                assert LEnvironment_Stutter(ls.environment, ls'.environment);
        }
    }

    lemma DS_Next_Implies_LS_Next(ds:DS_State, ds':DS_State)
    requires DS_Next(ds, ds')
    ensures LS_Next(Construct_LS_State(ds), Construct_LS_State(ds'))
    {
        var ls := Construct_LS_State(ds);
        var ls':= Construct_LS_State(ds');

        DS_Next_Implies_LEnv_Next(ds, ds');
        assert LEnvironment_Next(ls.environment, ls'.environment);
    }


    lemma BoundedEpoch(lmsg:LockMessage, dmsg:RealMsg, epoch:int) 
    requires MarshallLockMsg(epoch) == dmsg;
    requires lmsg == AbstractifyCMessage(DemarshallData(dmsg))
    requires Demarshallable(dmsg, CMessageGrammar())
    ensures 0 <= epoch < 0x1_0000_0000_0000_0000
    {
        // var g := CMessageGrammar();
        // var pv := parse_Val(dmsg, g);
        // assert !parse_Val(dmsg, g).0.None?;
        reveal_parse_Val();
        // var (v, rest) := parse_Val(dmsg, g);

    }


    lemma parse_Val_to_parse_Case(parsed:(Option<V>, seq<byte>), dmsg:RealMsg, grammar:G)
    requires |dmsg| < 0x1_0000_0000_0000_0000
    requires ValidGrammar(grammar)
    requires parsed == parse_Val(dmsg, grammar)
    requires grammar.GTaggedUnion?;
    ensures parsed == parse_Case(dmsg, grammar.cases)
    {
        reveal_parse_Val();
    }

    lemma IntToBytesParsedBack(rest:seq<byte>, vv:Option<V>, rest2:seq<byte>, epoch:int)
    requires 0 <= epoch < 0x1_0000_0000_0000_0000
    requires rest == Uint64ToBytes(uint64(epoch))
    requires (vv, rest2) == parse_Uint64(rest)
    ensures int(vv.v.u) == epoch
    {
        assert rest == Uint64ToSeqByte(uint64(epoch));
        assert rest == BEUintToSeqByte(epoch, 8);
        lemma_2toX();
        calc {
            power2(8*8);
        }
        assert 0 <= epoch < power2(8*8);
        lemma_BEUintToSeqByte_invertability(rest, epoch, 8);
        assert BEByteSeqToInt(rest) == epoch;
        assert SeqByteToUint64(rest) == uint64(epoch);
    }


    lemma DemarshallMessageResultsInCorrectEpoch(dmsg:RealMsg, val:V, g:G, epoch:int, caseID:Option<V>, rest1:seq<byte>, vv:Option<V>, rest2:seq<byte>)
    requires 0 <= epoch < 0x1_0000_0000_0000_0000
    requires MarshallLockMsg(epoch) == dmsg
    requires Demarshallable(dmsg, g)
    requires g == CMessageGrammar()
    requires g.GTaggedUnion?
    requires val == DemarshallFunc(dmsg, g)
    requires val.val.VUint64?
    requires (caseID, rest1) == parse_Uint64(dmsg)
    requires (vv, rest2) == parse_Uint64(rest1)
    requires val.val == vv.v
    ensures int(val.val.u) == epoch
    {
        // assert dmsg[8..] == rest1;
        // assert dmsg == [0,0,0,0,0,0,0,1] + rest1;
        assert rest1 == Uint64ToBytes(uint64(epoch));
        // assert dmsg[8..] == Uint64ToBytes(uint64(epoch));

        IntToBytesParsedBack(rest1, vv, rest2, epoch);
        assert int(vv.v.u) == epoch;
    }

    lemma DemarshallMessageResultsInCLocked(dmsg:RealMsg, val:V, g:G, epoch:int)
    requires 0 <= epoch < 0x1_0000_0000_0000_0000
    requires MarshallLockMsg(epoch) == dmsg
    requires Demarshallable(dmsg, g)
    requires g == CMessageGrammar()
    requires g.GTaggedUnion?
    requires val == DemarshallFunc(dmsg, g)
    ensures val.c == 1
    ensures val.val.VUint64?
    ensures int(val.val.u) == epoch
    {
        reveal_parse_Val();
        assert val == parse_Case(dmsg, g.cases).0.v;


        var (caseID, rest1) := parse_Uint64(dmsg);
        assert !caseID.None?;
        assert caseID.v.u < uint64(|g.cases|);
        var (vv, rest2) := parse_Val(rest1, g.cases[caseID.v.u]);
        assert !vv.None?;
        assert val.c == caseID.v.u;
        assert val.val == vv.v;
        assert caseID.v.u == 1;
        assert g.cases[caseID.v.u] == CMessageLockedGrammar();
        assert vv.v.VUint64?;

        DemarshallMessageResultsInCorrectEpoch(dmsg, val, g, epoch, caseID, rest1, vv, rest2);
    }


    lemma MarshallLockedMsg(lmsg:LockMessage, dmsg:RealMsg, epoch:int) 
    requires MarshallLockMsg(epoch) == dmsg;
    requires lmsg == AbstractifyCMessage(DemarshallData(dmsg))
    requires Demarshallable(dmsg, CMessageGrammar())
    ensures lmsg.Locked?
    ensures lmsg.locked_epoch == epoch
    {   

        BoundedEpoch(lmsg, dmsg, epoch);
        assert 0 <= epoch < 0x1_0000_0000_0000_0000;

        // var cmsg := DemarshallData(dmsg);
        // var val := DemarshallFunc(dmsg, CMessageGrammar());
        var grammar := CMessageGrammar();
        assert grammar.GTaggedUnion?;

        var val := DemarshallFunc(dmsg, grammar);
        DemarshallMessageResultsInCLocked(dmsg, val, grammar, epoch);
        assert val.c == 1;
        assert int(val.val.u) == epoch;

    }


    lemma ServiceCorrespondenceTransfer(ds:DS_State, ss:ServiceState)
    requires Protocol_Service_Correspondence(
                Construct_LS_State(ds).environment.sentPackets,
                ss)
    requires forall p :: 
                    p in ds.environment.sentPackets 
                 && p.src in ss.hosts
                ==> Demarshallable(p.msg, CMessageGrammar())
    ensures Service_Correspondence(ds.environment.sentPackets, ss)
    {
        var ps := ds.environment.sentPackets;
        forall p, epoch |
               p in ps
            && p.src in ss.hosts
            && p.dst in ss.hosts
            && p.msg == MarshallLockMsg(epoch)
        ensures 1 <= epoch <= |ss.history|
        ensures p.src == ss.history[epoch-1]
        {
            var ls := Construct_LS_State(ds);
            var lps:= ls.environment.sentPackets;
            var lp := AbstractifyUdpPacket(p);
            var c := DemarshallData(p.msg);
            assert lp in lps;
            assert Demarshallable(p.msg, CMessageGrammar());
            MarshallLockedMsg(lp.msg, p.msg, epoch);
            assert lp.msg.Locked?;
            assert 1 <= lp.msg.locked_epoch <= |ss.history|;
            assert epoch == lp.msg.locked_epoch;
        }
    }


    lemma InitTransfer(ds:DS_State, config:ConcreteConfiguration)
    requires DS_Init(ds, config)
    ensures LS_Init(Construct_LS_State(ds), config)
    {
        var ls := Construct_LS_State(ds);
        assert LEnvironment_Init(ls.environment);
        assert |config| > 0;
        assert SeqIsUnique(config);
        assert forall e :: e in config <==> e in ls.servers;
        forall index |
               0 <= index < |config|
        ensures NodeInit(ls.servers[config[index]], index, config)
        {
            assert mapdomain(ds.servers) == MapSeqToSet(config, x=>x);
            assert config[index] in config;
            assert forall xx :: xx in config <==> xx in MapSeqToSet(config, x=>x);
            assert config[index] in MapSeqToSet(config, x=>x);
            assert config[index] in ds.servers;
            assert HostInit(ds.servers[config[index]], config, config[index]);
            var host_state := ds.servers[config[index]];
            assert config[host_state.node_impl.node.my_index] == config[index];
            assert SeqIsUnique(config);
            reveal_SeqIsUnique();
            assert forall i, j :: 
                   0 <= i < |config|
                && 0 <= j < |config|
                && config[i] == config[j]
               ==> i == j;
            assert host_state.node_impl.node.my_index == uint64(index);
        }
                    
    }

    predicate SentDemarshallable(ps:set<LPacket<EndPoint, RealMsg>>, config:ConcreteConfiguration)
    {
        forall p ::
               p in ps
            && p.src in config
           ==> Demarshallable(p.msg, CMessageGrammar())
    }


    lemma Valid_Db_Implies_Demarshallable(db:seq<DS_State>, config:ConcreteConfiguration)
    requires |db| > 0
    requires DS_Init(db[0], config)
    requires forall i :: 0 <= i < |db|-1 ==> DS_Next(db[i], db[i+1])
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
                assert HostNext(db[kk].servers[id], db[kk+1].servers[id], ios);
                assert OnlySentMarshallableData(db[kk].environment.nextStep.ios);
                assert SentDemarshallable(db[kk+1].environment.sentPackets, config);
            } else {

                assert SentDemarshallable(db[kk+1].environment.sentPackets, config);
            }

            assert mapdomain(db[kk].servers) == mapdomain(db[kk+1].servers);


            k := k + 1;
        }

    }
  

    lemma RefinementProof(config:ConcreteConfiguration, db:seq<DS_State>) returns (sb:seq<ServiceState>)
    /*
        requires |db| > 0
        requires DS_Init(db[0], config)
        requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);
        ensures  |db| == |sb|
        ensures  Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers))
        ensures  forall i {:trigger Service_Next(sb[i], sb[i+1])} :: 0 <= i < |sb| - 1 ==> sb[i] == sb[i+1] || Service_Next(sb[i], sb[i+1])
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].environment.sentPackets, sb[i])
    */
    {

        var lb := [Construct_LS_State(db[0])];
        InitTransfer(db[0], config);
        assert LS_Init(lb[0], config);

        var k := 1;
        while (k < |db|)
        invariant 1 <= k <= |db|
        invariant |lb| == k
        invariant LS_Init(lb[0], config)
        invariant forall i :: 0 <= i < k - 1 ==> LS_Next(lb[i], lb[i+1]) || lb[i] == lb[i+1]
        invariant forall i :: 0 <= i < k ==> lb[i] == Construct_LS_State(db[i])
        {
            var servers := ConstructServers(db[k].servers);
            var lenv := ConstructLEnv(db[k].environment);
            var kk := k-1;
            lb := lb + [Construct_LS_State(db[k])];
            DS_Next_Implies_LS_Next(db[kk], db[kk+1]);
            assert lb[kk] == Construct_LS_State(db[kk]);
            assert LS_Next(lb[kk], lb[kk+1]);
            k := k + 1;
        }

        sb := LockProof.RefinementProof(config, lb);
        assert mapdomain(db[0].servers) == MapSeqToSet(config, x=>x);
        assert mapdomain(db[0].servers) == sb[0].hosts;
        assert Service_Init(sb[0], Collections__Maps2_s.mapdomain(db[0].servers));

        Valid_Db_Implies_Demarshallable(db, config);

        forall i |
               0 <= i < |db|
        ensures Service_Correspondence(db[i].environment.sentPackets, sb[i])
        {
            assert lb[i] == Construct_LS_State(db[i]);
            assert Protocol_Service_Correspondence(lb[i].environment.sentPackets, sb[i]);
            Valid_Db_Implies_Demarshallable(db, config);
            assert forall x :: x in sb[i].hosts <==> x in lb[0].servers;
            assert forall x :: x in config <==> x in sb[i].hosts;
            ServiceCorrespondenceTransfer(db[i], sb[i]);
        }
    }

}
