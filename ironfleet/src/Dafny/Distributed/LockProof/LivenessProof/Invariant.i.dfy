include "Defs.i.dfy"
include "Misc.i.dfy"



module Lock__LivenessProof__Invariant_i {

import opened Lock__LivenessProof__Defs_i
import opened Lock__LivenessProof__Misc_i


lemma OnlyOneUsefulTransfer(b:Behavior<LS_State>, t:int, p:LockPacket, p':LockPacket, node:EndPoint, config:Config)
requires ValidBehavior(b, config)
requires t >= 0
requires UsefulTransfer(p, node, config, b[t])
requires UsefulTransfer(p', node, config, b[t])
requires p in b[t].environment.sentPackets
requires p' in b[t].environment.sentPackets
requires p.src in config
requires p'.src in config
ensures p == p'
{
    var lb := MapToSeq(b, t);
    var glb := LSToGLS(config, lb);
    var e := p.msg.transfer_epoch;
    var e' := p'.msg.transfer_epoch;

    assert glb[t].history[e-1] == node;
    assert glb[t].history[e'-1] == node;
    
    assert 2 <= e <= |glb[t].history|;
    assert 2 <= e' <= |glb[t].history|;

    if (e != |glb[t].history|) {
        assert glb[t].ls.servers[node].epoch >= e;
    }
    if (e' != |glb[t].history|) {
        assert glb[t].ls.servers[node].epoch >= e;
    }
    assert e == e';

    var dst_index :| 0 <= dst_index < |config| && config[dst_index] == node;
    var dst_index' :| 0 <= dst_index' < |config| && config[dst_index'] == node;
    var src_index :| 0 <= src_index < |config| && config[src_index] == p.src;
var src_index' :| 0 <= src_index' < |config| && config[src_index'] == p'.src;
    
    assert dst_index == dst_index';


    var sendStep := GetSendStep(b, t, p, config);
    ValidBehaviorServers(b, config);
    assert b[sendStep].environment.nextStep.actor in config;
    assert NodeGrant(b[sendStep].servers[p.src], b[sendStep+1].servers[p.src], b[sendStep].environment.nextStep.ios);
    NodeConfig(b, config);
    assert dst_index == NextNode(src_index, config);
    assert src_index == GetSrcIndex(dst_index, config);
 
    var sendStep' := GetSendStep(b, t, p', config);
    ValidBehaviorServers(b, config);
    assert b[sendStep'].environment.nextStep.actor in config;
    assert NodeGrant(b[sendStep'].servers[p'.src], b[sendStep'+1].servers[p'.src], b[sendStep'].environment.nextStep.ios);
    NodeConfig(b, config);
    assert dst_index' == NextNode(src_index', config);
    assert src_index' == GetSrcIndex(dst_index', config);

    assert src_index == src_index';
    assert p.src == p'.src;
}

function{:opaque} GetSrcIndex(dst_index:int, config:Config) : int
requires 0 <= dst_index < |config|
ensures 0 <= GetSrcIndex(dst_index, config) < |config|
ensures dst_index == NextNode(GetSrcIndex(dst_index, config), config)
ensures forall i :: 0 <= i < |config| && i != GetSrcIndex(dst_index, config) ==> NextNode(i, config) != dst_index
{
    lemma_mod_auto(|config|);
    (dst_index + |config| - 1) % |config|
}

}
