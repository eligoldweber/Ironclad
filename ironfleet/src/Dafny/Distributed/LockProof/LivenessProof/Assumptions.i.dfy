include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Framework/EnvironmentSynchrony.s.dfy"
include "Defs.i.dfy"


module Lock__LivenessProof__Assumptions_i {

import opened DistributedSystem_i
import opened Lock__LivenessProof__Defs_i
import EnvironmentSynchrony_s


predicate LivenessAssumptions(
    b:Behavior<LS_State>,
    asp:AssumptionParameters,
    config:Config)
    requires imaptotal(b)
    requires SeqIsUnique(config)
{
    var serverAddresses := MapSeqToSet(config, x=>x);
       sat(0, always(PacketsEventuallyDeliveredForHostsTemporal(BehaviorToLEnvMap(b), serverAddresses)))
    && HostQueuesLive<EndPoint, LockMessage>(BehaviorToLEnvMap(b))
    && forall node ::
              node in config
          ==> sat(0, always(ActionOccursForServerTemporal(b, node)))
}

}
