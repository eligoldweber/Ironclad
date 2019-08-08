include "./RefinementProof/DistributedSystem.i.dfy"
include "./RefinementProof/Refinement.i.dfy"
include "../../Services/Lock/AbstractService.s.dfy"
include "./Node.i.dfy"
include "Types.i.dfy"
include "../../Protocol/Common/NodeIdentity.i.dfy"
include "./helper.i.dfy"


module correspondsMarshal{
     import opened DistributedSystem_i
     import opened AbstractServiceLock_s
     import opened Protocol_Node_i
     import opened Types_i
     import opened Refinement_i
     import opened Concrete_NodeIdentity_i
     import opened refinementHelper

    lemma DemarshallMessageResultsInCorrectEpoch(dmsg:seq<byte>, val:V, g:G, epoch:int, caseID:Option<V>, rest1:seq<byte>, vv:Option<V>, rest2:seq<byte>)
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
    
        assert rest1 == Uint64ToBytes(uint64(epoch));

        IntToBytesParsedBack(rest1, vv, rest2, epoch);
        assert int(vv.v.u) == epoch;
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

    lemma DemarshallMessageResultsInCLocked(dmsg:seq<byte>, val:V, g:G, epoch:int)
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


    lemma MarshallLockedMsg(lmsg:LockMessage, dmsg:seq<byte>, epoch:int)
        requires MarshallLockMsg(epoch) == dmsg;
        requires lmsg == AbstractifyCMessage(DemarshallData(dmsg))
        requires Demarshallable(dmsg, CMessageGrammar())
        ensures lmsg.Locked?
        ensures lmsg.locked_epoch == epoch
    {

        reveal_parse_Val();
        assert 0 <= epoch < 0x1_0000_0000_0000_0000;

        var grammar := CMessageGrammar();
        assert grammar.GTaggedUnion?;

        var val := DemarshallFunc(dmsg, grammar);
        DemarshallMessageResultsInCLocked(dmsg, val, grammar, epoch);
        assert val.c == 1;
        assert int(val.val.u) == epoch;

    }

}
