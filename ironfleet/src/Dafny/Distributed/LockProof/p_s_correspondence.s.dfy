include "../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../Protocol/Lock/Node.i.dfy"
include "../Services/Lock/AbstractService.s.dfy"

module P_S_Correspondence_s {
import opened DistributedSystem_i
import opened Protocol_Node_i
import opened AbstractServiceLock_s

predicate Protocol_Service_Correspondence(packets:set<LockPacket>, serviceState:ServiceState) {
    
    forall p :: 
           p in packets
        && p.src in serviceState.hosts
        && p.dst in serviceState.hosts
        && p.msg.Locked?
        ==> var epoch := p.msg.locked_epoch;
                0 < epoch <= |serviceState.history|
            && p.src == serviceState.history[epoch-1]
}

}
