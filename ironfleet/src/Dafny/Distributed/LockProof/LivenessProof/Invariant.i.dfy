include "Defs.i.dfy"
include "Misc.i.dfy"



module Lock__LivenessProof__Invariant_i {

import opened Lock__LivenessProof__Defs_i
import opened Lock__LivenessProof__Misc_i

// TODO
lemma OnlyOneUsefulTransfer(b:Behavior<LS_State>, t:int, p:LockPacket, p':LockPacket, node:EndPoint, config:Config)
requires ValidBehavior(b, config)
requires t >= 0
requires UsefulTransfer(p, node, config, b[t])
requires UsefulTransfer(p', node, config, b[t])
ensures p == p'
{

}

}
