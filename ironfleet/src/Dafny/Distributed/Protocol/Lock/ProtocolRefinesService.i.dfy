include "Types.i.dfy"
include "RefinementProof/Refinement.i.dfy"

module Protocol_Refines_Service {
    import opened Types_i
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
    requires forall n :: n in gls.ls.servers ==> |config| > gls.ls.servers[n].my_index >= 0;
    requires forall e :: e in config <==> e in gls.ls.servers;
    requires forall n :: n in gls.ls.servers ==> n == gls.ls.servers[n].config[gls.ls.servers[n].my_index];
    ensures forall n :: n in gls'.ls.servers ==> n == gls'.ls.servers[n].config[gls'.ls.servers[n].my_index];
    ensures |gls'.history| >= 1;
    ensures  forall n :: n in gls'.ls.servers ==> |config| > gls'.ls.servers[n].my_index >= 0;
    ensures forall e :: e in config <==> e in gls'.ls.servers;
    ensures gls'.history == s'.history;
    ensures mapdomain(gls'.ls.servers) == s'.hosts;

    //Safety invariant : 1 implies safety
    requires Service_Correspondence(gls.ls.environment.sentPackets, s);
    ensures Service_Correspondence(gls'.ls.environment.sentPackets, s');

    //1. All valid transfer messages satisfy the correspondence : 4 implies 1
    requires forall p :: p in gls.ls.environment.sentPackets && p.msg.Transfer? && p.src in gls.ls.servers && p.dst in gls.ls.servers
                        ==> 2 <= p.msg.transfer_epoch <= |gls.history| && gls.history[p.msg.transfer_epoch-1] == p.dst;
    ensures forall p :: p in gls'.ls.environment.sentPackets && p.msg.Transfer? && p.src in gls'.ls.servers && p.dst in gls'.ls.servers
                        ==> 2 <= p.msg.transfer_epoch <= |gls'.history| && gls'.history[p.msg.transfer_epoch-1] == p.dst;

    //2. If a node holds, it is the last element in the history : 2 & 3 implies 2
    requires forall n :: n in gls.ls.servers && gls.ls.servers[n].held ==> gls.history[|gls.history| - 1] == n;
    ensures forall n :: n in gls'.ls.servers && gls'.ls.servers[n].held ==> gls'.history[|gls'.history| - 1] == n;

    requires forall h,j :: h in gls.ls.servers && 0 <= j < |gls.history|-1 && gls.history[j] == h ==> j+1 <= gls.ls.servers[h].epoch;

    ensures forall h,j :: h in gls'.ls.servers && 0 <= j < |gls'.history|-1 && gls'.history[j] == h ==> j+1 <= gls'.ls.servers[h].epoch;

    //3. If there is a transfer message sent to a node with higher epoch, this epoch equals to length of history// 1 & 2 & 4 implies 3
    // requires forall n, t :: n in gls.ls.servers && t in gls.ls.environment.sentPackets && t.msg.Transfer? && t.src in gls.ls.servers
    //                 && t.dst == n && t.msg.transfer_epoch > gls.ls.servers[n].epoch
    //                     ==> t.msg.transfer_epoch == |gls.history|;
    // ensures forall n, t :: n in gls'.ls.servers && t in gls'.ls.environment.sentPackets && t.msg.Transfer? && t.src in gls'.ls.servers
    //                 && t.dst == n && t.msg.transfer_epoch > gls'.ls.servers[n].epoch
    //                     ==> t.msg.transfer_epoch == |gls'.history|;

    //4. If there is a holder, its epoch is equal to length of history : 2 and 3 implies 4
    requires forall n :: n in gls.ls.servers && gls.ls.servers[n].held ==> gls.ls.servers[n].epoch == |gls.history|;
    ensures forall n :: n in gls'.ls.servers && gls'.ls.servers[n].held ==> gls'.ls.servers[n].epoch == |gls'.history|;
    {
    }

    lemma RefinementProof(config:Config, db:seq<GLS_State>) returns (sb:seq<ServiceState>)
        requires |db| > 0;
        requires GLS_Init(db[0], config);
        requires forall i {:trigger GLS_Next(db[i-1], db[i])} :: 0 < i < |db| ==> GLS_Next(db[i-1], db[i]);
        ensures  |db| == |sb|;
        ensures  Service_Init(sb[0], mapdomain(db[0].ls.servers));
        ensures  forall i {:trigger Service_Next(sb[i-1], sb[i])} :: 0 < i < |sb| ==> sb[i-1] == sb[i] || Service_Next(sb[i-1], sb[i]);
        ensures  forall i :: 0 <= i < |db| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]);
    {
        sb:=[AbstractifyGLS_State(db[0])];

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
            invariant forall n :: n in db[i-1].ls.servers ==> n == db[i-1].ls.servers[n].config[db[i-1].ls.servers[n].my_index];

            invariant forall h,j :: h in db[i-1].ls.servers && 0 <= j < |db[i-1].history|-1 && db[i-1].history[j] == h ==> j+1 <= db[i-1].ls.servers[h].epoch;

            invariant forall i :: 0 <= i < |sb| ==> Service_Correspondence(db[i].ls.environment.sentPackets, sb[i]); //Invariant for safety
            invariant forall p :: p in db[i-1].ls.environment.sentPackets && p.msg.Transfer? && p.src in db[i-1].ls.servers && p.dst in db[i-1].ls.servers
                                ==> 2 <= p.msg.transfer_epoch <= |db[i-1].history| && db[i-1].history[p.msg.transfer_epoch-1] == p.dst;//Invariant for 1
            invariant forall n :: n in db[i-1].ls.servers && db[i-1].ls.servers[n].held ==> db[i-1].ls.servers[n].epoch == |db[i-1].history|;//Invariant for 4
            invariant forall n :: n in db[i-1].ls.servers && db[i-1].ls.servers[n].held ==> db[i-1].history[|db[i-1].history| - 1] == n;//Invariant for 2
            // invariant forall n, t :: n in db[i-1].ls.servers && t in db[i-1].ls.environment.sentPackets && t.msg.Transfer? && t.src in db[i-1].ls.servers
            //         && t.dst == db[i-1].ls.servers[n].config[db[i-1].ls.servers[n].my_index] && t.msg.transfer_epoch > db[i-1].ls.servers[n].epoch
            //             ==> t.msg.transfer_epoch == |db[i-1].history|;//Invariant for 3
        {
            sb := sb + [AbstractifyGLS_State(db[i])];
            RefineNext(db[i-1], db[i], sb[i-1], sb[i], config);
            RefineCorrespondence(db[i-1], db[i] , sb[i-1], sb[i], config);
            i := i + 1;
        }
    }
}