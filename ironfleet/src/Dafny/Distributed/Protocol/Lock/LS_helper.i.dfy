
include "./RefinementProof/DistributedSystem.i.dfy"
include "./RefinementProof/Refinement.i.dfy"
include "../../Services/Lock/AbstractService.s.dfy"
include "./Node.i.dfy"
include "Types.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"

module refinementLSHelper{
    import opened DistributedSystem_i
    import opened AbstractServiceLock_s
    import opened Protocol_Node_i
    import opened Types_i
    import opened Refinement_i
    import opened Concrete_NodeIdentity_i

    /////// ----------------DS TO LS--------------------------- /////////

       function byteToLockPacket(p:LPacket<EndPoint,seq<byte>>) : LPacket<NodeIdentity, LockMessage>
       {
           LPacket(p.dst, p.src, AbstractifyCMessage(DemarshallData(p.msg)))
       }

        function ConvertSentPackets(sent:set<LPacket<EndPoint,seq<byte>>>) : set<LPacket<NodeIdentity, LockMessage>>
        {
            set p | p in sent :: byteToLockPacket(p)
        }



        function byteToLockNextStep(step:LEnvStep<EndPoint,seq<byte>>) : LEnvStep<NodeIdentity, LockMessage>
          {
              match step {
                  case LEnvStepHostIos(actor, ios) => LEnvStepHostIos(actor, AbstractifyRawLogToIos(ios))
                  case LEnvStepDeliverPacket(p) => LEnvStepDeliverPacket(byteToLockPacket(p))
                  case LEnvStepAdvanceTime => LEnvStepAdvanceTime()
                  case LEnvStepStutter => LEnvStepStutter()
              }
          }

        function dsEnv_to_lsEnv(dsEnv:LEnvironment<EndPoint,seq<byte>>) : LockEnvironment
           {
               LEnvironment(dsEnv.time,
                            ConvertSentPackets(dsEnv.sentPackets),
                            map [],
                            byteToLockNextStep(dsEnv.nextStep))
           }


           function dsServer_to_lsServer(replicas:map<EndPoint,HostState>, replica_order:seq<EndPoint>) : map<EndPoint,Node>
               requires forall i :: 0 <= i < |replica_order| ==> replica_order[i] in replicas;
               requires SeqIsUnique(replica_order);
               ensures  forall i :: 0 <= i < |replica_order| ==> replica_order[i] in dsServer_to_lsServer(replicas, replica_order);
               ensures  forall i :: 0 <= i < |replica_order| ==>
                        dsServer_to_lsServer(replicas, replica_order)[replica_order[i]] == replicas[replica_order[i]].node;
               ensures forall e :: e in dsServer_to_lsServer(replicas, replica_order) <==> e in replica_order;
           {
               if |replica_order| == 0 then map[]
               else
                   reveal_SeqIsUnique();
                   var rest := dsServer_to_lsServer(replicas, replica_order[1..]);
                   rest[replica_order[0] := replicas[replica_order[0]].node]
           }

        function dsTols(ds:DS_State) : LS_State
           requires forall i :: i in ds.config ==> i in ds.servers;
           requires ValidConfig(ds.config);
          {
              LS_State(dsEnv_to_lsEnv(ds.environment),dsServer_to_lsServer(ds.servers,ds.config))

          }

          predicate validDB(config:ConcreteConfiguration, db:seq<DS_State>)
          reads *;
          {
              |db| > 0
          && DS_Init(db[0], config)
          && forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1])
          }

          lemma dsNextValid(config:ConcreteConfiguration,db:seq<DS_State>,i:int)
               requires 0 <= i < |db| - 1;
               requires validDB(config,db);
               ensures DS_Next(db[i],db[i+1]);
          {}

          lemma serverConsistent(config:ConcreteConfiguration,db:seq<DS_State>,i:int)
               requires validDB(config,db);
               requires 0 <= i < |db|;
               ensures db[i].config == config;
               ensures mapdomain(db[i].servers) == mapdomain(db[0].servers);

          {
              if (i > 0){
                  serverConsistent(config,db,i-1);
                  dsNextValid(config,db,i-1);
              }
          }
          lemma lemma_IsValidEnvStep(de:LEnvironment<EndPoint, seq<byte>>, le:LEnvironment<NodeIdentity, LockMessage>)
                  requires IsValidLEnvStep(de, de.nextStep);
                  requires de.nextStep.LEnvStepHostIos?;
                  requires dsEnv_to_lsEnv(de) == le;
                  ensures  IsValidLEnvStep(le, le.nextStep);
              {
                  var id := de.nextStep.actor;
                  var ios := de.nextStep.ios;
                  var r_ios := le.nextStep.ios;


                  forall io | io in r_ios
                      ensures IsValidLIoOp(io, id, le);
                  {
                      var j :| 0 <= j < |r_ios| && r_ios[j] == io;
                      assert IsValidLIoOp(ios[j], id, de);
                  }
              }

              lemma lemma_IosRelations(ios:seq<LIoOp<EndPoint, seq<byte>>>, r_ios:seq<LIoOp<NodeIdentity, LockMessage>>)
                  returns (sends:set<LPacket<EndPoint, seq<byte>>>, r_sends:set<LPacket<NodeIdentity, LockMessage>>)
                  requires r_ios == AbstractifyRawLogToIos(ios);
                  ensures    sends == (set io | io in ios && io.LIoOpSend? :: io.s);
                  ensures  r_sends == (set io | io in r_ios && io.LIoOpSend? :: io.s);
                  ensures  r_sends == ConvertSentPackets(sends);
              {
                    sends := (set io | io in ios && io.LIoOpSend? :: io.s);
                  r_sends := (set io | io in r_ios && io.LIoOpSend? :: io.s);
                  var refined_sends := ConvertSentPackets(sends);

                  forall r | r in refined_sends
                      ensures r in r_sends;
                  {
                      var send :| send in sends && byteToLockPacket(send) == r;
                      var io :| io in ios && io.LIoOpSend? && io.s == send;
                      assert AstractifyUdpEventToLockIo(io) in r_ios;
                  }

                  forall r | r in r_sends
                      ensures r in refined_sends;
                  {
                      var r_io :| r_io in r_ios && r_io.LIoOpSend? && r_io.s == r;
                      var j :| 0 <= j < |r_ios| && r_ios[j] == r_io;
                      assert AstractifyUdpEventToLockIo(ios[j]) == r_io;
                      assert ios[j] in ios;
                      assert ios[j].s in sends;
                  }
              }

              lemma lemma_LEnvironmentNextHost(de :LEnvironment<EndPoint, seq<byte>>, le :LEnvironment<NodeIdentity, LockMessage>,
                                                de':LEnvironment<EndPoint, seq<byte>>, le':LEnvironment<NodeIdentity, LockMessage>)
                  requires dsEnv_to_lsEnv(de)  == le;
                  requires dsEnv_to_lsEnv(de') == le';
                  requires de.nextStep.LEnvStepHostIos?;
                  requires LEnvironment_Next(de, de');
                  ensures  LEnvironment_Next(le, le');
              {
                  lemma_IsValidEnvStep(de, le);
                  var id := de.nextStep.actor;
                  var ios := de.nextStep.ios;
                  var r_ios := le.nextStep.ios;


                  var sends, r_sends := lemma_IosRelations(ios, r_ios);
                  assert le.sentPackets + r_sends == le'.sentPackets;

              }

              predicate DsStateIsValid(ds:DS_State)
              {
                  ValidConfig(ds.config)
                  && (forall r :: r in ds.config ==> r in ds.servers)
              }

          lemma {:timeLimitMultiplier 2} DS_To_LS(config:ConcreteConfiguration, db:seq<DS_State>) returns (lsb:seq<LS_State>)
                requires |db| > 0;
                requires DS_Init(db[0], config);
                requires forall i {:trigger DS_Next(db[i], db[i+1])} :: 0 <= i < |db| - 1 ==> DS_Next(db[i], db[i+1]);

                ensures |lsb| == |db|;
                // ensures forall i :: 0 <= i < |lsb| ==> (forall j :: j in config <==> j in lsb[i].servers);

                ensures  LS_Init(lsb[0], db[0].config);
                ensures  forall i {:trigger LS_Next(lsb[i], lsb[i+1])} :: 0 <= i < |lsb| - 1 ==> LS_Next(lsb[i], lsb[i+1]);
                ensures forall i :: 0 <= i < |db| ==> DsStateIsValid(db[i]) && lsb[i] == dsTols(db[i]);




                {
                    lsb := [dsTols(db[0])];
                    reveal_SeqIsUnique ();
                    assert LS_Init(lsb[0],config);
                    assert forall j :: j in config <==> j in lsb[0].servers;
                    if (|db| == 1){
                        return lsb;
                    }else{

                        var i := |lsb|;
                        while i < |db|
                        invariant i == |lsb|
                        invariant 1 <= i <= |db|;
                        invariant  LS_Init(lsb[0],config);
                        invariant forall j :: 0 <= j < |lsb|-1 ==> LS_Next(lsb[j], lsb[j+1]);
                        invariant forall j :: 0 <= j < |lsb| ==> DsStateIsValid(db[j]) && lsb[j] == dsTols(db[j]);
                        invariant forall j :: 0 <= j < |lsb| ==> (forall k :: k in config <==> k in lsb[j].servers)


                        {
                            dsNextValid(config,db,i-1);
                            serverConsistent(config,db,i);
                            lsb := lsb + [dsTols(db[i])];

                            if db[i-1].environment.nextStep.LEnvStepHostIos? {

                                lemma_LEnvironmentNextHost(db[i-1].environment, lsb[i-1].environment, db[i].environment, lsb[i].environment);
                                assert LS_Next(lsb[i-1], lsb[i]);
                            }else{
                                assert LS_Next(lsb[i-1], lsb[i]);
                            }
                            assert forall j :: j in lsb[i].servers <==> j in lsb[i-1].servers;
                            assert forall j :: j in config <==> j in lsb[i].servers;

                            i := i + 1;
                        }



                    }

                }

}
