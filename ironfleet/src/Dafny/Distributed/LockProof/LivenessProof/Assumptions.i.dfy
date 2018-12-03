include "../../Protocol/Lock/RefinementProof/DistributedSystem.i.dfy"
include "../../Common/Framework/EnvironmentSynchrony.s.dfy"


module Lock__LivenessProof__Assumptions_i {

import opened DistributedSystem_i
import opened EnvironmentSynchrony_s

datatype AssumptionParameters = AssumptionParameters()

predicate PacketsEventuallyDeliveredForHosts(
    b:Behavior<LEnvironment<EndPoint, LockMessage>>,
    i:int,
    serverAddresses:set<EndPoint>
    )
    requires imaptotal(b)
{
    forall p {:triger PacketSentBetweenHosts(b[i], p, serverAddresses, serverAddresses)} ::
        PacketSentBetweenHosts(b[i], p, serverAddresses, serverAddresses) ==>
        sat(i, next(eventual(PacketDeliveredTemporal(b, p))))
}

predicate IosStep(ls:LS_State) 
{
       ls.environment.nextStep.LEnvStepHostIos?
    && ls.environment.nextStep.actor in ls.servers
}


function PacketsEventuallyDeliveredForHostsTemporal(
    b:Behavior<LEnvironment<EndPoint,LockMessage>>,
    serverAddresses:set<EndPoint>
    ) : temporal 
    requires imaptotal(b)
    ensures forall i {:trigger sat(i, PacketsEventuallyDeliveredForHostsTemporal(b, serverAddresses))} ::
        sat(i, PacketsEventuallyDeliveredForHostsTemporal(b, serverAddresses)) <==> 
        PacketsEventuallyDeliveredForHosts(b, i, serverAddresses)
{
    stepmap(imap i :: PacketsEventuallyDeliveredForHosts(b, i, serverAddresses))
}

function BehaviorToLEnvMap(b:Behavior<LS_State>) : imap<int, LEnvironment<EndPoint, LockMessage>>
requires imaptotal(b)
ensures imaptotal(BehaviorToLEnvMap(b))
ensures forall i {:trigger BehaviorToLEnvMap(b)[i]} :: BehaviorToLEnvMap(b)[i] == b[i].environment
{
    imap i :: b[i].environment
}

function IosStepTemporal(b:Behavior<LS_State>) : temporal
requires imaptotal(b)
ensures forall t {:trigger sat(t, IosStepTemporal(b))} ::
               sat(t, IosStepTemporal(b)) <==> IosStep(b[t])
{
    stepmap(imap t :: IosStep(b[t]))
}


function EventuallyIosStepTemporal(b:Behavior<LS_State>) : temporal
requires imaptotal(b)
{
    eventual(IosStepTemporal(b))
}


predicate LivenessAssumptions(
    b:Behavior<LS_State>,
    asp:AssumptionParameters,
    config:Config)
    requires imaptotal(b)
    requires SeqIsUnique(config)
{
    var serverAddresses := MapSeqToSet(config, x=>x);
       sat(0, always(PacketsEventuallyDeliveredForHostsTemporal(BehaviorToLEnvMap(b), serverAddresses)))
    && sat(0, always(EventuallyIosStepTemporal(b)))
}

}
