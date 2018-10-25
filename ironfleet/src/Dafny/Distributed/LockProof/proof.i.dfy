include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"

module LockProof {
import opened DistributedSystem_i
import opened Protocol_Node_i
import opened AbstractServiceLock_s


lemma sameServers(s:LS_State, s':LS_State)
requires LS_Next(s, s')
ensures forall e :: e in s.servers <==> e in s'.servers

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
{
    if (|ls| == 1) {
        gls := [GLS_State(ls[0], [config[0]])];
        assert gls[|gls|-1].ls == ls[|ls|-1];
    } else {
        assert(|ls| > 1);
        gls := LSToGLS(config, ls[0..|ls|-1]);
        assert(|gls| == |ls|-1);
        var history := gls[|gls|-1].history;

        assert forall i :: 0 <= i < |ls|-1 ==> (LS_Next(ls[i], ls[i+1]) || ls[i] == ls[i+1]);
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
                // I have a lemma for this large chunk of proof. But Dafny does not use it!


                assert forall i :: 0 <= i < |ls| ==> forall j :: j in ls[i].servers ==> ls[i].servers[j].config == config;

                assert forall j :: j in ls[|ls|-2].servers ==> ls[|ls|-2].servers[j].config == config;
                assert ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config == config;
                assert ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config[(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].my_index + 1) % |ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config|] in config;

                history := history + [ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config[(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].my_index + 1) % |ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config|]];
                gls := gls + [GLS_State(ls[|ls|-1], history)];
            } else 
            {
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

        //assert(forall i :: i in ls ==> forall j :: j in i.servers ==> i.servers[j].config == config);
        //assert(forall i :: i in ls[|ls|-2].servers ==> ls[|ls|-2].servers[i].config == config);

        // if (ls[|ls|-2].environment.nextStep.LEnvStepHostIos? 
        //         && ls[|ls|-2].environment.nextStep.actor in ls[|ls|-2].servers
        //         && NodeGrant(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor], ls[|ls|-1].servers[ls[|ls|-2].environment.nextStep.actor], ls[|ls|-2].environment.nextStep.ios)
        //         && ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].held 
        //         && ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].epoch < 0xFFFF_FFFF_FFFF_FFFF) {
        //         assert(false);
        //     history := history + [ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config[(ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].my_index + 1) % |ls[|ls|-2].servers[ls[|ls|-2].environment.nextStep.actor].config|]];
        //     gls := gls + [GLS_State(ls[|ls|-1], history)];
        //     assert(GLS_Next(gls[|gls|-2], gls[|gls|-1]));
        // } else {
        //     gls := gls + [GLS_State(ls[|ls|-1], history)];
        // }

            

        //assert(gls[|gls|-1] == gls[|gls|-2] || GLS_Next(gls[|gls|-2], gls[|gls|-1]));
    }
}


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
//    assert(ss[0].hosts == serverAddresses);
//    assert(exists e :: e in serverAddresses && ss[0].history == [e]);
//    assert(Service_Init(ss[0], serverAddresses));
}


}
