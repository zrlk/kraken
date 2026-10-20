# Inventory of the LockFree theorems. `gen_md.py` reads it to
# write Kraken/Examples/LockFree/THEOREMS.md; running this file directly writes
# the #check files .lake/docs/check_{aarch64,x64}.lean. Run both from the
# repository root (see THEOREMS.md, "Regenerating").
import sys, os

P = "Kraken.Promising."
E = "Kraken.Examples.LockFree."

def t(name, f):
    """A theorem: full name (P-relative unless it starts with Kraken.) and a
    file relative to Kraken/."""
    if not name.startswith("Kraken."):
        name = P + name
    if not f.startswith("Examples/") and not f.startswith("AArch64/") and not f.startswith("X64/"):
        f = "Promising/" + f
    return (name, f)

E_ = "SLR/EnvG/"

# Columns: whole, runner, nf0 (decls = {}), nfd (decls = ds), ff (Config.FaultFree),
# sff (runner-exact safety ∧ Config.FaultFree), reach, live, verdict,
# open (text), extra (other theorems about the program).
A = {}

def lockA(prog, n, whole, wholeC, runner, runnerC, nf0, nfd, extra=()):
    A[prog] = dict(whole=[whole] + ([wholeC] if wholeC else []), runner=[runner, runnerC],
                   nf0=nf0, nfd=nfd, extra=list(extra))

A["spinlock2"] = dict(verdict=[t(E + "spinlock2_aarch64", "Examples/LockFree/TheoremsAArch64.lean")],
    open="LL/SC (`LDAXR`/`STXR`) is deferred in the Stage 2/3 logic (`Promising/EnvWP.md`, \"LL/SC\"): no safety theorem, no runner-exact theorem")
A["spinlock3"] = dict(open=A["spinlock2"]["open"])
A["spinlock_relaxed2"] = dict(reach=[t("Reach.SpinlockRelaxed2.spinlock_relaxed2_reachable", "ReachA64SpinlockRelaxed2.lean")],
    verdict=[t(E + "spinlock2_relaxed_aarch64", "Examples/LockFree/TheoremsAArch64.lean")])
A["spinlock_relaxed_acq2"] = dict(reach=[t("Reach.SpinlockRelaxedAcq2.spinlock_relaxed_acq2_reachable", "ReachA64SpinlockRelaxedAcq2.lean")])
for k, conc in (("spinlock_swp2", True), ("spinlock_swp3", False)):
    A[k] = dict(whole=[t("SLR.SwpInv.swp_counter_armv8", "SLR/SwpFinal.lean"),
                       t("SLR.SwpPublic.swp_counter_public", "SLR/SwpPublic.lean")]
                + ([t("SLR.SwpConcrete.swp_counter_2", "SLR/SwpConcrete.lean")] if conc else [])
                + [t("SLR.EnvG.SwpEnvG.swp_counter_envG", E_ + "SwpEnvGPublic.lean")],
                # The EnvG proof closes the runner-exact and decls = ds gaps.
                runner=[t("SLR.EnvG.SwpEnvG.swp_counter_envG_runner", E_ + "A64SwpRunner.lean"),
                        t("SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_concrete" + k[-1], E_ + "A64SwpRunner.lean")],
                nf0=[t("SLR.SwpInv.swpRuleX_noFault", "SLR/SwpNoFault.lean"),
                     t("SLR.EnvG.SwpEnvG.swpRule_envGC_noFault", E_ + "SwpEnvGPublic.lean")],
                nfd=[t("SLR.EnvG.SwpEnvG.swp_counter_envG_runner_noFault", E_ + "A64SwpNoFault.lean"),
                     t("SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_noFault_concrete", E_ + "A64SwpNoFault.lean")],
                ff=[t("SLR.EnvG.SwpEnvG.swp_counter_envG_runner_faultFree", E_ + "A64SwpNoFault.lean"),
                    t("SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_faultFree_concreteN", E_ + "A64SwpNoFault.lean")],
                extra=[t("Kraken.AArch64.Examples.InvEnv.swp_reachable", "AArch64/Examples/InvEnv.lean"),
                       t("SLR.EnvG.SwpEnvG.swp_counter_envG_type_eq", E_ + "SwpEnvGPublic.lean")])
for k, c0, cr in (("spinlock_swpl2", "concrete2", "runner_concrete2"), ("spinlock_swpl3", "concreteN", "runner_concrete3")):
    A[k] = dict(whole=[t("SLR.EnvG.SwplLock.swpl_counter_envG", E_ + "SwplLockPublic.lean"),
                       t("SLR.EnvG.ConcreteSwpl.swpl_counter_envG_" + c0, E_ + "ConcreteSwpl.lean")],
                runner=[t("SLR.EnvG.SwplLock.swpl_counter_envG_runner", E_ + "A64SwplRunner.lean"),
                        t("SLR.EnvG.ConcreteSwpl.swpl_counter_envG_" + cr, E_ + "A64SwplRunner.lean")],
                nf0=[t("SLR.EnvG.SwplLock.swplRule_envGC_noFault", E_ + "SwplLockPublic.lean")],
                nfd=[t("SLR.EnvG.SwplLock.swpl_counter_envG_runner_noFault", E_ + "A64NoFaultDLocks.lean"),
                     t("SLR.EnvG.ConcreteSwpl.swpl_counter_envG_runner_noFault_concrete", E_ + "A64NoFaultDLocks.lean")])
for k, c0, cr in (("spinlock_cas2", "concrete2", "runner_concrete2"), ("spinlock_cas3", "concreteN", "runner_concrete3")):
    A[k] = dict(whole=[t("SLR.EnvG.CasSmoke.cas_counter_envG", E_ + "CasPublic.lean"),
                       t("SLR.EnvG.ConcreteCas.cas_counter_envG_" + c0, E_ + "ConcreteCas.lean")],
                runner=[t("SLR.EnvG.CasSmoke.cas_counter_envG_runner", E_ + "A64CasRunner.lean"),
                        t("SLR.EnvG.ConcreteCas.cas_counter_envG_" + cr, E_ + "A64CasRunner.lean")],
                nf0=[t("SLR.EnvG.CasSmoke.casRule_envG_noFault", E_ + "CasLink.lean")],
                nfd=[t("SLR.EnvG.CasSmoke.cas_counter_envG_runner_noFault", E_ + "A64NoFaultDLocks.lean"),
                     t("SLR.EnvG.ConcreteCas.cas_counter_envG_runner_noFault_concrete", E_ + "A64NoFaultDLocks.lean")])
for k, cr in (("ticketlock2", "runner_concrete2"), ("ticketlock3", "runner_concrete3")):
    A[k] = dict(whole=[t("SLR.EnvG.TicketLock.ticket_counter_envG", E_ + "TicketLockPublic.lean")],
                runner=[t("SLR.EnvG.TicketLock.ticket_counter_envG_runner", E_ + "A64TicketRunner.lean"),
                        t("SLR.EnvG.ConcreteTicketD.ticket_counter_envG_" + cr, E_ + "A64TicketRunner.lean")],
                nf0=[t("SLR.EnvG.TicketLock.tkRule_noFault", E_ + "TicketLockPublic.lean")],
                nfd=[t("SLR.EnvG.TicketLock.ticket_counter_envG_runner_noFault", E_ + "A64NoFaultDLocks.lean"),
                     t("SLR.EnvG.ConcreteTicketD.ticket_counter_envG_runner_noFault_concrete", E_ + "A64NoFaultDLocks.lean")],
                live=[t("Live.Ticket.ticketLivePF_of_live", "LiveTicket.lean")])
LIVEPF = [t("Live.TicketPF.ticket_live_pf", "LiveTicketPF.lean"), t("Live.TicketPF.ticket_live_pf_concrete", "LiveTicketPF.lean")]
A["ticketlock2"]["live"] = LIVEPF + [t("Live.TicketCexG.ticketLiveWF_false", "LiveTicketCexG.lean"),
                            t("Live.TicketCex.ticket_not_live_weakFair", "LiveTicketCex.lean"),
                            t("Live.TicketCex.ticket_fair_exists", "LiveTicketCex.lean"),
                            t("Live.TicketZero.ticket_live_zero", "LiveTicketZero.lean"),
                            t("Live.TicketSem.ticket_live_sem", "LiveTicketSem.lean"),
                            t("Live.TicketSem.ticket_live_sem_concrete", "LiveTicketSem.lean")]
A["ticketlock3"]["live"] = LIVEPF + A["ticketlock3"]["live"]
A["ticketlock2"]["verdict"] = [t(E + "ticketlock2_aarch64", "Examples/LockFree/TheoremsAArch64.lean")]
LIVEOPEN = "liveness: `Live.Ticket.TicketLive` (weak + memory fairness, the official Stage 3 statement, promises allowed) is open for fuel ≥ 1 (proved at fuel 0, and for every fuel with semantic certification as `TicketLiveSem`); its promise-free fragment `TicketLivePF` is proved on a valid layout only (`Litmus/KNOWN_GAPS.md`, \"Liveness (LIVEPF)\")"
A["ticketlock2"]["open"] = LIVEOPEN
A["ticketlock3"]["open"] = LIVEOPEN
for k, c0, cr in (("ticketlock_al2", "concrete2", "runner_concrete2"), ("ticketlock_al3", "concrete3", "runner_concrete3")):
    A[k] = dict(whole=[t("SLR.EnvG.TicketLock.ticket_al_counter_envG", E_ + "TicketAlPublic.lean"),
                       t("SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_" + c0, E_ + "ConcreteTicketAl.lean")],
                runner=[t("SLR.EnvG.TicketLock.ticket_al_counter_envG_runner", E_ + "A64TicketRunner.lean"),
                        t("SLR.EnvG.ConcreteTicketAl.ticket_al_counter_envG_" + cr, E_ + "A64TicketRunner.lean")],
                nf0=[t("SLR.EnvG.TicketLock.tkRuleAl_noFault", E_ + "TicketAlPublic.lean")],
                nfd=[t("SLR.EnvG.TicketLock.ticket_al_counter_envG_runner_noFault", E_ + "A64NoFaultDLocks.lean"),
                     t("SLR.EnvG.ConcreteTicketD.ticket_al_counter_envG_runner_noFault_concrete", E_ + "A64NoFaultDLocks.lean")])
A["ticketlock_relaxed2"] = dict(reach=[t("Reach.TicketlockRelaxed2.ticketlock_relaxed2_reachable", "ReachA64TicketlockRelaxed2.lean")])
PTR_OPEN = "`decls = ds` no-fault: the accessed addresses depend on values (`Litmus/KNOWN_GAPS.md`, \"Declarations in the AArch64 whole-image theorems\", \"Still open: the pointer programs\")"
A["treiber_pp"] = dict(
    whole=[t("SLR.EnvG.Treiber.treiber_pp_envG_whole", E_ + "A64WholeTreiberPublic.lean"),
           t("SLR.EnvG.Treiber.treiber_pp_envG_whole_concrete", E_ + "A64WholeTreiberConcrete.lean")],
    runner=[t("SLR.EnvG.Treiber.treiber_pp_envG_runner", E_ + "A64WholeTreiberRunner.lean"),
            t("SLR.EnvG.Treiber.treiber_pp_envG_runner_concrete", E_ + "A64WholeTreiberRunner.lean")],
    nf0=[t("SLR.EnvG.Treiber.treiberImageA_noFault", E_ + "A64WholeTreiberPublic.lean"),
         t("SLR.EnvG.Treiber.pushRuleW_noFault", E_ + "A64WholeTreiberPublic.lean"),
         t("SLR.EnvG.Treiber.popRuleW_noFault", E_ + "A64WholeTreiberPublic.lean")],
    extra=[t("SLR.EnvG.Treiber.treiber_pp_envG", E_ + "TreiberPublic.lean"),
           t("SLR.EnvG.ConcreteTreiber.treiber_pp_envG_concrete", E_ + "ConcreteTreiber.lean")],
    open=PTR_OPEN)
A["treiber_pp_relaxed"] = dict(reach=[t("Reach.TreiberPpRelaxed.treiber_pp_relaxed_reachable", "ReachA64TreiberPpRelaxed.lean")],
    verdict=[t(E + "treiber_pp_relaxed_aarch64", "Examples/LockFree/TheoremsAArch64.lean")])
A["treiber2"] = dict(
    whole=[t("SLR.EnvG.Treiber2.treiber2_envG_whole", E_ + "A64WholeTreiber2.lean"),
           t("SLR.EnvG.Treiber2.treiber2_envG_whole_concrete", E_ + "A64WholeTreiber2.lean")],
    runner=[t("SLR.EnvG.Treiber2.treiber2_envG_runner", E_ + "A64WholeTreiber2Runner.lean"),
            t("SLR.EnvG.Treiber2.treiber2_envG_runner_concrete", E_ + "A64WholeTreiber2Runner.lean")],
    nf0=[t("SLR.EnvG.Treiber2.wRuleD_noFault", E_ + "Treiber2DataPublic.lean")],
    extra=[t("SLR.EnvG.Treiber2.treiber2_envG", E_ + "Treiber2DataPublic.lean"),
           t("SLR.EnvG.ConcreteTreiber2Data.treiber2_envG_concrete", E_ + "ConcreteTreiber2Data.lean")],
    open=PTR_OPEN)
A["treiber2_nodes"] = dict(
    whole=[t("SLR.EnvG.Treiber2.treiber2_nodes_envG_whole", E_ + "A64WholeTreiber2Nodes.lean"),
           t("SLR.EnvG.Treiber2.treiber2_nodes_envG_whole_concrete", E_ + "A64WholeTreiber2Nodes.lean")],
    runner=[t("SLR.EnvG.Treiber2.treiber2_nodes_envG_runner", E_ + "A64WholeTreiber2NodesRunner.lean"),
            t("SLR.EnvG.Treiber2.treiber2_nodes_envG_runner_concrete", E_ + "A64WholeTreiber2NodesRunner.lean")],
    nf0=[t("SLR.EnvG.Treiber2.treiber2NImage_noFault", E_ + "A64WholeTreiber2Nodes.lean"),
         t("SLR.EnvG.Treiber2.wRuleN_noFault", E_ + "A64WholeTreiber2Nodes.lean")],
    extra=[t("SLR.EnvG.Treiber2.treiber2_nodes_envG", E_ + "Treiber2Public.lean"),
           t("SLR.EnvG.ConcreteTreiber2.treiber2_nodes_envG_concrete", E_ + "ConcreteTreiber2.lean")],
    open=PTR_OPEN)
A["treiber2_arm"] = dict(
    whole=[t("SLR.EnvG.Treiber2Arm.treiber2_arm_envG_whole", E_ + "A64Treiber2ArmWhole.lean"),
           t("SLR.EnvG.Treiber2Arm.treiber2_arm_envG_whole_concrete", E_ + "A64Treiber2ArmWhole.lean")],
    runner=[t("SLR.EnvG.Treiber2Arm.treiber2_arm_envG_runner", E_ + "A64Treiber2ArmRunner.lean"),
            t("SLR.EnvG.Treiber2Arm.treiber2_arm_envG_runner_concrete", E_ + "A64Treiber2ArmRunner.lean")],
    nf0=[t("SLR.EnvG.Treiber2Arm.wRuleA_noFault", E_ + "Treiber2ArmPublic.lean")],
    extra=[t("SLR.EnvG.Treiber2Arm.treiber2_arm_envG", E_ + "Treiber2ArmPublic.lean")],
    open=PTR_OPEN)
A["treiber2_relaxed"] = dict(reach=[t("Reach.Treiber2Relaxed.treiber2_relaxed_reachable", "ReachA64Treiber2Relaxed.lean")])
A["spsc_queue"] = dict(
    whole=[t("SLR.EnvG.SpscA.a64_spsc_envG_whole", E_ + "A64SpscWholePublic.lean"),
           t("SLR.EnvG.SpscA.a64_spsc_envG_whole_concrete", E_ + "A64SpscWholeConcrete.lean")],
    runner=[t("SLR.EnvG.SpscA.a64_spsc_envG_runner", E_ + "A64SpscWholeRunner.lean"),
            t("SLR.EnvG.SpscA.a64_spsc_envG_runner_concrete", E_ + "A64SpscWholeRunner.lean")],
    nf0=[t("SLR.EnvG.SpscA.spscImageA_noFault", E_ + "A64SpscWholePublic.lean"),
         t("SLR.EnvG.SpscA.prodRuleW_noFault", E_ + "A64SpscWholePublic.lean"),
         t("SLR.EnvG.SpscA.consRuleW_noFault", E_ + "A64SpscWholePublic.lean")],
    nfd=[t("SLR.EnvG.SpscA.a64_spscP_envG_runner_noFault", E_ + "A64NoFaultDSpsc.lean"),
         t("SLR.EnvG.SpscA.a64_spscC_envG_runner_noFault", E_ + "A64NoFaultDSpsc.lean"),
         t("SLR.EnvG.SpscA.a64_spsc_envG_runner_noFault_concrete", E_ + "A64NoFaultDSpsc.lean")],
    extra=[t("SLR.EnvG.SpscA.a64_spsc_envG", E_ + "A64SpscPublic.lean"),
           t("SLR.EnvG.SpscA.a64_spsc_envG_concrete", E_ + "A64SpscConcrete.lean")],
    verdict=[t(E + "spsc_queue_aarch64", "Examples/LockFree/TheoremsAArch64.lean")])
A["spsc_queue_relaxed2"] = dict(reach=[t("Reach.SpscQueueRelaxed2.spsc_queue_relaxed2_reachable", "ReachA64SpscQueueRelaxed2.lean")])
A["spsc_queue_relaxed3"] = dict(reach=[t("Reach.SpscQueueRelaxed3.spsc_queue_relaxed3_reachable", "ReachA64SpscQueueRelaxed3.lean")])
for n in (1, 2, 3):
    k = "msqueue%d" % n
    pub = {1: "MsQueuePublic.lean", 2: "MsQueue2Public.lean", 3: "MsQueue3Public.lean"}[n]
    conc = {1: ("ConcreteMsQueue", "ConcreteMsQueue.lean"), 2: ("ConcreteMsQueue2", "ConcreteMsQueue2.lean"),
            3: ("ConcreteMsQueue3", "ConcreteMsQueue3.lean")}[n]
    rules = {1: ["enqRuleQ1", "deqRuleQ1"], 2: ["enqRuleQ2", "deqRuleQ2"], 3: ["enqRuleQ3", "deqARuleQ3", "deqBRuleQ3"]}[n]
    A[k] = dict(
        whole=[t("SLR.EnvG.MsQueue.%s_envG_whole" % k, E_ + "A64WholeMsQueue%d.lean" % n),
               t("SLR.EnvG.MsQueue.%s_envG_whole_concrete" % k, E_ + "A64WholeMsQueue%dConcrete.lean" % n)],
        runner=[t("SLR.EnvG.MsQueue.%s_envG_runner" % k, E_ + "A64WholeMsQueue%dRunner.lean" % n),
                t("SLR.EnvG.MsQueue.%s_envG_runner_concrete" % k, E_ + "A64WholeMsQueue%dRunner.lean" % n)],
        nf0=[t("SLR.EnvG.MsQueue.msq%dImage_noFault" % n, E_ + "A64WholeMsQueue%d.lean" % n)]
            + [t("SLR.EnvG.MsQueue.%s_noFault" % r, E_ + "A64WholeMsQueue%d.lean" % n) for r in rules],
        extra=[t("SLR.EnvG.MsQueue.%s_envG" % k, E_ + pub),
               t("SLR.EnvG.%s.%s_envG_concrete" % (conc[0], k), E_ + conc[1])],
        open=PTR_OPEN)
A["msqueue1"]["verdict"] = [t(E + "msqueue1_aarch64", "Examples/LockFree/TheoremsAArch64.lean")]
A["msqueue_relaxed1"] = dict(reach=[t("Reach.MsqueueRelaxed1.msqueue_relaxed1_reachable", "ReachA64MsqueueRelaxed1.lean")],
    verdict=[t(E + "msqueue1_relaxed_aarch64", "Examples/LockFree/TheoremsAArch64.lean")])
A["msqueue_relaxed2"] = dict(reach=[t("Reach.MsqueueRelaxed2.msqueue_relaxed2_reachable", "ReachA64MsqueueRelaxed2.lean")])
A["mp_relay3"] = dict(
    whole=[t("SLR.EnvG.Relay.mp_relay3_envG_whole", E_ + "A64WholeRelayPublic.lean"),
           t("SLR.EnvG.Relay.mp_relay3_envG_whole_concrete", E_ + "A64WholeRelayConcrete.lean")],
    runner=[t("SLR.EnvG.Relay.mp_relay3_envG_runner", E_ + "A64WholeRelayRunner.lean"),
            t("SLR.EnvG.Relay.mp_relay3_envG_runner_concrete", E_ + "A64WholeRelayRunner.lean")],
    nf0=[t("SLR.EnvG.Relay.relay3Img_noFault", E_ + "A64WholeRelayPublic.lean")]
        + [t("SLR.EnvG.Relay.relayRule%s3_noFault" % r, E_ + "A64WholeRelayPublic.lean") for r in "WYD"],
    nfd=[t("SLR.EnvG.Relay.mp_relay3%s_envG_runner_noFault" % r, E_ + "A64NoFaultDRelay.lean") for r in "WYD"]
        + [t("SLR.EnvG.Relay.mp_relay3_envG_runner_noFault_concrete", E_ + "A64NoFaultDRelay.lean")],
    extra=[t("SLR.EnvG.Relay.mp_relay3_envG", E_ + "RelayPublic.lean")])
A["mp_relay3_swpl"] = dict(
    whole=[t("SLR.EnvG.Relay.mp_relay3_swpl_envG_whole", E_ + "A64WholeRelaySwpl.lean"),
           t("SLR.EnvG.Relay.mp_relay3_swpl_envG_whole_concrete", E_ + "A64WholeRelaySwplConcrete.lean")],
    runner=[t("SLR.EnvG.Relay.mp_relay3_swpl_envG_runner", E_ + "A64WholeRelaySwplRunner.lean"),
            t("SLR.EnvG.Relay.mp_relay3_swpl_envG_runner_concrete", E_ + "A64WholeRelaySwplRunner.lean")],
    nf0=[t("SLR.EnvG.Relay.relaySwpl3Img_noFault", E_ + "A64WholeRelaySwpl.lean")]
        + [t("SLR.EnvG.Relay.relayRule%sS3_noFault" % r, E_ + "A64WholeRelaySwpl.lean") for r in "WYD"],
    nfd=[t("SLR.EnvG.Relay.mp_relay3_swpl%s_envG_runner_noFault" % r, E_ + "A64NoFaultDRelay.lean") for r in "WYD"]
        + [t("SLR.EnvG.Relay.mp_relay3_swpl_envG_runner_noFault_concrete", E_ + "A64NoFaultDRelay.lean")],
    extra=[t("SLR.EnvG.Relay.mp_relay3_swpl_envG", E_ + "RelaySwplPublic.lean")])

# Program-level Config.FaultFree at the runner's declarations.
FF_ = E_ + "A64FaultFreeFixed.lean"
for k, g, c in (("spinlock_cas2", "CasSmoke.cas_counter", "ConcreteCas.cas_counter"),
                ("spinlock_cas3", "CasSmoke.cas_counter", "ConcreteCas.cas_counter"),
                ("spinlock_swpl2", "SwplLock.swpl_counter", "ConcreteSwpl.swpl_counter"),
                ("spinlock_swpl3", "SwplLock.swpl_counter", "ConcreteSwpl.swpl_counter"),
                ("ticketlock2", "TicketLock.ticket_counter", "ConcreteTicketD.ticket_counter"),
                ("ticketlock3", "TicketLock.ticket_counter", "ConcreteTicketD.ticket_counter"),
                ("ticketlock_al2", "TicketLock.ticket_al_counter", "ConcreteTicketD.ticket_al_counter"),
                ("ticketlock_al3", "TicketLock.ticket_al_counter", "ConcreteTicketD.ticket_al_counter")):
    A[k]["ff"] = [t("SLR.EnvG.%s_envG_runner_faultFree" % g, FF_),
                  t("SLR.EnvG.%s_envG_runner_faultFree_concreteN" % c, FF_)]
for k, g in (("mp_relay3", "Relay.mp_relay3"), ("mp_relay3_swpl", "Relay.mp_relay3_swpl"),
             ("spsc_queue", "SpscA.a64_spsc")):
    A[k]["ff"] = [t("SLR.EnvG.%s_envG_runner_faultFree" % g, FF_),
                  t("SLR.EnvG.%s_envG_runner_faultFree_concrete" % g, FF_)]
for k, g, f in (("treiber_pp", "Treiber.treiber_pp", "MemValsA64TreiberPP.lean"),
                ("treiber2", "Treiber2.treiber2", "MemValsA64Treiber2.lean"),
                ("treiber2_nodes", "Treiber2.treiber2_nodes", "MemValsA64Treiber2Nodes.lean"),
                ("msqueue1", "MsQueue.msqueue1", "MemValsA64MsQueue.lean"),
                ("msqueue2", "MsQueue.msqueue2", "MemValsA64MsQueue23.lean"),
                ("msqueue3", "MsQueue.msqueue3", "MemValsA64MsQueue23.lean"),
                ("treiber2_arm", "Treiber2Arm.treiber2_arm", "MemValsA64Treiber2Arm.lean")):
    A[k]["ff"] = [t("SLR.EnvG.%s_envG_runner_faultFree" % g, E_ + f),
                  t("SLR.EnvG.%s_envG_runner_faultFree_concrete" % g, E_ + f)]
PTR_OPEN_FF = ("rule-level `decls = ds` no-fault (`NoFaultRule`): the accessed addresses depend on values, "
               "which the threads' invariants do not bound; program-level `Config.FaultFree` at `decls = ds` "
               "is proved (A64FF, table below) (`Litmus/KNOWN_GAPS.md`, \"Declarations in the AArch64 "
               "whole-image theorems\")")
for k in A:
    if A[k].get("open") == PTR_OPEN:
        A[k]["open"] = PTR_OPEN_FF

# Runner-exact safety ∧ Config.FaultFree, one theorem each
# (`RunnerSafeFFA64.lean`); the concrete is in the namespace of the program's
# other concretes.
SFF_ = E_ + "RunnerSafeFFA64.lean"
for k, g, c in (("spinlock_cas2", "CasSmoke.cas_counter", "ConcreteCas.cas_counter"),
                ("spinlock_cas3", "CasSmoke.cas_counter", "ConcreteCas.cas_counter"),
                ("spinlock_swpl2", "SwplLock.swpl_counter", "ConcreteSwpl.swpl_counter"),
                ("spinlock_swpl3", "SwplLock.swpl_counter", "ConcreteSwpl.swpl_counter"),
                ("ticketlock2", "TicketLock.ticket_counter", "ConcreteTicketD.ticket_counter"),
                ("ticketlock3", "TicketLock.ticket_counter", "ConcreteTicketD.ticket_counter"),
                ("ticketlock_al2", "TicketLock.ticket_al_counter", "ConcreteTicketAl.ticket_al_counter"),
                ("ticketlock_al3", "TicketLock.ticket_al_counter", "ConcreteTicketAl.ticket_al_counter")):
    A[k]["sff"] = [t("SLR.EnvG.%s_envG_runner_safe_faultFree" % g, SFF_),
                   t("SLR.EnvG.%s_envG_runner_safe_faultFree_concreteN" % c, SFF_)]
for k, g in (("mp_relay3", "Relay.mp_relay3"), ("mp_relay3_swpl", "Relay.mp_relay3_swpl"),
             ("spsc_queue", "SpscA.a64_spsc"), ("treiber_pp", "Treiber.treiber_pp"),
             ("treiber2", "Treiber2.treiber2"), ("treiber2_nodes", "Treiber2.treiber2_nodes"),
             ("treiber2_arm", "Treiber2Arm.treiber2_arm"), ("msqueue1", "MsQueue.msqueue1"),
             ("msqueue2", "MsQueue.msqueue2"), ("msqueue3", "MsQueue.msqueue3")):
    A[k]["sff"] = [t("SLR.EnvG.%s_envG_runner_safe_faultFree" % g, SFF_),
                   t("SLR.EnvG.%s_envG_runner_safe_faultFree_concrete" % g, SFF_)]
# The SWP family, `RunnerSafeFFSwp.lean`.
for k in ("spinlock_swp2", "spinlock_swp3"):
    A[k]["sff"] = [t("SLR.EnvG.SwpEnvG.swp_counter_envG_runner_safe_faultFree", E_ + "RunnerSafeFFSwp.lean"),
                   t("SLR.EnvG.A64SwpRunner.swp_counter_envG_runner_safe_faultFree_concreteN",
                     E_ + "RunnerSafeFFSwp.lean")]
# Promise-free deadlock-freedom of the CAS spinlock, and per-thread
# liveness of its one-shot workers, on a valid layout.
LIVESPIN = [t("Live.SpinCasPF.spin_cas_live_pf", "LiveSpinCasPF.lean"),
            t("Live.SpinCasPF.spin_cas_live_pf_concrete", "LiveSpinCasPF.lean"),
            t("Live.SpinCasPF.spin_cas_live_oneShot_pf", "LiveSpinCasPF.lean"),
            t("Live.SpinCasPF.spin_cas_live_oneShot_pf_concrete", "LiveSpinCasPF.lean"),
            t("Live.Spin.casSpinLivePF_of_live", "LiveSpin.lean")]
for k in ("spinlock_cas2", "spinlock_cas3"):
    A[k]["live"] = LIVESPIN
    A[k]["open"] = ("liveness: `Live.Spin.CasSpinLive` (deadlock-freedom under weak + memory fairness, "
                    "promises allowed) is open; its promise-free fragment `CasSpinLivePF` is proved on a valid "
                    "layout only (`Litmus/KNOWN_GAPS.md`, \"Liveness: spinlocks (LIVESPIN)\")")
# Deadlock-freedom of the CAS spinlock with promises on the
# machine with semantic certification (every fuel), and the one-shot corollary.
LIVESPINSEM = [t("Live.SpinSemCas.spin_cas_live_sem", "LiveSpinSemCas.lean"),
               t("Live.SpinSemCas.spin_cas_live_sem_concrete", "LiveSpinSemCas.lean"),
               t("Live.SpinSemCas.spin_cas_live_oneShot_sem", "LiveSpinSemCas.lean"),
               t("Live.SpinSemCas.spin_cas_live_oneShot_sem_concrete", "LiveSpinSemCas.lean")]
for k in ("spinlock_cas2", "spinlock_cas3"):
    A[k]["live"] = LIVESPINSEM + A[k]["live"]
    A[k]["open"] = ("liveness: `Live.Spin.CasSpinLive` (deadlock-freedom under weak + memory fairness, "
                    "promises allowed, over `succs`) is open (incomplete `certify` search); proved with "
                    "semantic certification for every fuel as `CasSpinLiveSem`, and promise-free as "
                    "`CasSpinLivePF`, on a valid layout only (`Litmus/KNOWN_GAPS.md`, \"Liveness: spinlocks "
                    "(LIVESPIN)\")")
# Promise-free deadlock-freedom of the SWP spinlocks (SWPA/STLR,
# SWPA/SWPL), and per-thread liveness of their one-shot workers, on a valid layout.
for ks, fam, Fam in ((("spinlock_swp2", "spinlock_swp3"), "swp", "Swp"),
                     (("spinlock_swpl2", "spinlock_swpl3"), "swpl", "Swpl")):
    live = [t("Live.SpinSwpFam.spin_%s_live_pf" % fam, "LiveSpinSwpFam.lean"),
            t("Live.SpinSwpFam.spin_%s_live_pf_concrete" % fam, "LiveSpinSwpFam.lean"),
            t("Live.SpinSwpFam.spin_%s_live_oneShot_pf" % fam, "LiveSpinSwpFam.lean"),
            t("Live.SpinSwpFam.spin_%s_live_oneShot_pf_concrete" % fam, "LiveSpinSwpFam.lean"),
            t("Live.SpinSwp.%sSpinLivePF_of_live" % fam, "LiveSpinSwp.lean")]
    for k in ks:
        A[k]["live"] = live
        A[k]["open"] = ("liveness: `Live.SpinSwp.%sSpinLive` (deadlock-freedom under weak + memory fairness, "
                        "promises allowed) is open; its promise-free fragment `%sSpinLivePF` is proved on a valid "
                        "layout only (`Litmus/KNOWN_GAPS.md`, \"Liveness: spinlocks (LIVESPIN)\")" % (Fam, Fam))
# Deadlock-freedom of the SWP spinlocks with promises on the
# machine with semantic certification (every fuel), and the one-shot corollary.
for ks, fam, Fam in ((("spinlock_swp2", "spinlock_swp3"), "swp", "Swp"),
                     (("spinlock_swpl2", "spinlock_swpl3"), "swpl", "Swpl")):
    sem = [t("Live.SpinSemSwpLive.spin_%s_live_sem" % fam, "LiveSpinSemSwpLive.lean"),
           t("Live.SpinSemSwpLive.spin_%s_live_sem_concrete" % fam, "LiveSpinSemSwpLive.lean"),
           t("Live.SpinSemSwpLive.spin_%s_live_oneShot_sem" % fam, "LiveSpinSemSwpLive.lean"),
           t("Live.SpinSemSwpLive.spin_%s_live_oneShot_sem_concrete" % fam, "LiveSpinSemSwpLive.lean")]
    for k in ks:
        A[k]["live"] = sem + A[k]["live"]
        A[k]["open"] = ("liveness: `Live.SpinSwp.%sSpinLive` (deadlock-freedom under weak + memory fairness, "
                        "promises allowed, over `succs`) is open (incomplete `certify` search); proved with "
                        "semantic certification for every fuel as `%sSpinLiveSem`, and promise-free as "
                        "`%sSpinLivePF`, on a valid layout only (`Litmus/KNOWN_GAPS.md`, \"Liveness: spinlocks "
                        "(LIVESPIN)\")" % (Fam, Fam, Fam))
# Fair traces exist from the start configurations, on both machines
# (the liveness hypotheses are satisfiable; generic part `LiveSemWitness.lean`).
FW = "LiveSemWitnessA64.lean"
for ks, nm in ((("ticketlock2", "ticketlock3"), "tk"), (("spinlock_cas2", "spinlock_cas3"), "cas"),
               (("spinlock_swp2", "spinlock_swp3"), "swpWorker"), (("spinlock_swpl2", "spinlock_swpl3"), "swplWorker")):
    for k in ks:
        A[k].setdefault("extra", []).extend([t("Live.WitnessA64.%s_fair_exists" % nm, FW),
                                             t("Live.WitnessA64.%s_fairSem_exists" % nm, FW)])

# ---------------------------------------------------------------- x64
X = {}
XE = "X64.EnvG."
TX = "Examples/LockFree/TheoremsX64.lean"
for k, vc, rc in (("spinlock2", "verbatim_concrete2", "runner_concrete2"), ("spinlock3", "verbatim_concreteN", "runner_concrete3")):
    X[k] = dict(
        whole=[t(XE + "SpinAbs.x64_spin_counter_envG_verbatim", E_ + "X64SpinAbsPublic.lean"),
               t(XE + "SpinAbs.Concrete.x64_spin_counter_envG_" + vc, E_ + "X64SpinAbsConcrete.lean")],
        runner=[t(XE + "SpinAbs.x64_spin_counter_envG_runner", E_ + "X64SpinAbsRunner.lean"),
                t(XE + "SpinAbs.Concrete.x64_spin_counter_envG_" + rc, E_ + "X64SpinAbsRunner.lean")],
        nf0=[t(XE + "SpinAbs.spinRuleV_envG_noFault", E_ + "X64SpinAbsPublic.lean")],
        nfd=[t(XE + "SpinAbs.x64_spin_counter_envG_runner_noFault", E_ + "X64NoFaultDLocks.lean"),
             t(XE + "SpinAbs.Concrete.x64_spin_counter_envG_runner_noFault_concrete", E_ + "X64NoFaultDLocks.lean")],
        ff=[t(XE + "SpinAbs.x64_spin_counter_envG_runner_faultFree", E_ + "X64FaultFreeFixed.lean"),
            t(XE + "SpinAbs.Concrete.x64_spin_counter_envG_runner_faultFree_concreteN", E_ + "X64FaultFreeFixed.lean")],
        extra=[t(XE + "SpinPublicG.x64_spin_counter_envG", E_ + "X64SpinPublicG.lean"),
               t("SLR.X64SpinInv.x64_counter_spin", "SLR/X64SpinFinalX.lean"),
               t("SLR.X64SpinPublic.x64_counter_public", "SLR/X64SpinPublic.lean")])
X["spinlock2"]["extra"].append(t("SLR.X64SpinConcrete.x64_counter_2", "SLR/X64SpinConcrete.lean"))
X["spinlock2"]["verdict"] = [t(E + "spinlock2_x64", TX)]
for k, vc, rc in (("spinlock_cmpxchg2", "verbatim_concrete2", "runner_concrete2"), ("spinlock_cmpxchg3", "verbatim_concreteN", "runner_concrete3")):
    X[k] = dict(
        whole=[t(XE + "CmpxAbs.x64_cmpx_counter_envG_verbatim", E_ + "X64CmpxAbsPublic.lean"),
               t(XE + "CmpxAbs.Concrete.x64_cmpx_counter_envG_" + vc, E_ + "X64CmpxAbsConcrete.lean")],
        runner=[t(XE + "CmpxAbs.x64_cmpx_counter_envG_runner", E_ + "X64CmpxAbsRunner.lean"),
                t(XE + "CmpxAbs.Concrete.x64_cmpx_counter_envG_" + rc, E_ + "X64CmpxAbsRunner.lean")],
        nf0=[t(XE + "CmpxAbs.cmpxRuleV_envGF_noFault", E_ + "X64CmpxAbsPublic.lean")],
        nfd=[t(XE + "CmpxAbs.x64_cmpx_counter_envG_runner_noFault", E_ + "X64NoFaultDLocks.lean"),
             t(XE + "CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_noFault_concrete", E_ + "X64NoFaultDLocks.lean")],
        ff=[t(XE + "CmpxAbs.x64_cmpx_counter_envG_runner_faultFree", E_ + "X64FaultFreeFixed.lean"),
            t(XE + "CmpxAbs.Concrete.x64_cmpx_counter_envG_runner_faultFree_concreteN", E_ + "X64FaultFreeFixed.lean")],
        extra=[t(XE + "CmpxPublic.x64_cmpx_counter_envG'", E_ + "X64CmpxFinal.lean")])
X["ticketlock2"] = dict(verdict=[t(E + "ticketlock2_x64", TX)],
    whole=[t(XE + "TicketX2.ticket2_counter_envG_verbatim", E_ + "X64Ticket2Public.lean")],
    runner=[t(XE + "TicketX2.ticket2_counter_envG_runner", E_ + "X64Ticket2Public.lean"),
            t(XE + "TicketX2.Concrete.ticket2_counter_envG_runner_concrete2", E_ + "X64Ticket2Runner.lean")],
    ff=[t(XE + "TicketX2.ticket2_counter_envG_runner_faultFree", E_ + "X64Ticket2FaultFree.lean"),
        t(XE + "TicketX2.Concrete.ticket2_counter_envG_runner_faultFree_concreteN", E_ + "X64Ticket2FaultFree.lean")],
    sff=[t(XE + "TicketX2.ticket2_counter_envG_runner_safe_faultFree", E_ + "X64Ticket2FaultFree.lean"),
         t(XE + "TicketX2.Concrete.ticket2_counter_envG_runner_safe_faultFree_concreteN", E_ + "X64Ticket2FaultFree.lean")],
    extra=[t(XE + "xaddTake_phase1R", E_ + "TicketRX64Link.lean"), t(XE + "xaddTake_noFault", E_ + "TicketRX64Link.lean")])
X["ticketlock3"] = dict(
    whole=[t(XE + "TicketX.ticket3_counter_envG_verbatim", E_ + "TicketXPublic.lean")],
    runner=[t(XE + "TicketX.ticket3_counter_envG_runner", E_ + "TicketXPublic.lean"),
            t(XE + "TicketX.Concrete.ticket3_counter_envG_runner_concrete3", E_ + "TicketXRunner.lean")],
    nf0=[t(XE + "TicketX.ruleTk3_noFault", E_ + "TicketXPublic.lean")],
    nfd=[t(XE + "TicketX.ticket3_counter_envG_runner_noFault", E_ + "X64NoFaultDLocks.lean"),
         t(XE + "TicketX.Concrete.ticket3_counter_envG_runner_noFault_concrete", E_ + "X64NoFaultDLocks.lean")],
    ff=[t(XE + "TicketX.ticket3_counter_envG_runner_faultFree", E_ + "X64FaultFreeFixed.lean"),
        t(XE + "TicketX.Concrete.ticket3_counter_envG_runner_faultFree_concreteN", E_ + "X64FaultFreeFixed.lean")])
X["dekker_broken"] = dict(reach=[t("Reach.DekkerBroken.dekker_broken_reachable", "ReachX64DekkerBroken.lean")],
    verdict=[t(E + "dekker_broken_x64", TX)])
X["dekker_mfence"] = dict(
    whole=[t(XE + "DekkerAbs.x64_dekker_public_verbatim", E_ + "DekkerAbsPublic.lean"),
           t(XE + "DekkerAbs.Concrete.x64_dekker_public_verbatim_concrete", E_ + "DekkerAbsConcrete.lean")],
    runner=[t(XE + "DekkerAbs.x64_dekker_public_runner", E_ + "DekkerAbsRunner.lean"),
            t(XE + "DekkerAbs.Concrete.x64_dekker_public_runner_concrete", E_ + "DekkerAbsRunner.lean")],
    nf0=[t(XE + "DekkerAbs.dkRuleV_noFault", E_ + "DekkerAbsPublic.lean")],
    nfd=[t(XE + "DekkerAbs.x64_dekker_public_runner_noFault", E_ + "X64NoFaultDLocks.lean"),
         t(XE + "DekkerAbs.Concrete.x64_dekker_public_runner_noFault_concrete", E_ + "X64NoFaultDLocks.lean")],
    ff=[t(XE + "DekkerAbs.x64_dekker_public_runner_faultFree", E_ + "X64FaultFreeFixed.lean"),
        t(XE + "DekkerAbs.Concrete.x64_dekker_public_runner_faultFree_concrete", E_ + "X64FaultFreeFixed.lean")],
    extra=[t(XE + "Dekker.x64_dekker_public", E_ + "DekkerPublicX.lean")],
    verdict=[t(E + "dekker_mfence_x64", TX)])
X["treiber2"] = dict(
    whole=[t(XE + "Treiber2X.x64_treiber2_envG_verbatim", E_ + "X64Treiber2Public.lean"),
           t(XE + "Treiber2X.Concrete.x64_treiber2_envG_verbatim_concrete", E_ + "X64Treiber2Concrete.lean")],
    runner=[t(XE + "Treiber2X.x64_treiber2_envG_runner", E_ + "X64Treiber2Runner.lean"),
            t(XE + "Treiber2X.Concrete.x64_treiber2_envG_runner_concrete", E_ + "X64Treiber2Runner.lean")],
    nf0=[t(XE + "Treiber2X.wRuleV_noFault", E_ + "X64Treiber2Public.lean")],
    ff=[t(XE + "Treiber2X.x64_treiber2_envG_runner_faultFree", E_ + "MemValsTreiber2.lean"),
        t(XE + "Treiber2X.Concrete.x64_treiber2_envG_runner_faultFree_concrete", E_ + "MemValsTreiber2.lean")],
    verdict=[t(E + "treiber2_x64", TX)])
X["spsc_queue"] = dict(
    whole=[t(XE + "SpscAbs.x64_spsc_envG_verbatim", E_ + "X64SpscAbsPublic.lean"),
           t(XE + "SpscAbs.Concrete.x64_spsc_envG_verbatim_concrete", E_ + "X64SpscAbsConcrete.lean")],
    runner=[t(XE + "SpscAbs.x64_spsc_envG_runner", E_ + "X64SpscAbsRunner.lean"),
            t(XE + "SpscAbs.Concrete.x64_spsc_envG_runner_concrete", E_ + "X64SpscAbsRunner.lean")],
    nf0=[t(XE + "SpscAbs.prodRuleA_noFault", E_ + "X64SpscAbsPublic.lean"),
         t(XE + "SpscAbs.consRuleA_noFault", E_ + "X64SpscAbsPublic.lean")],
    nfd=[t(XE + "SpscAbs.x64_spsc_envG_runner_noFault", E_ + "X64NoFaultDMp.lean"),
         t(XE + "SpscAbs.Concrete.x64_spsc_envG_runner_noFault_concrete", E_ + "X64NoFaultDMp.lean")],
    extra=[t(XE + "SpscX.x64_spsc_envG", E_ + "X64SpscPublic.lean"),
           t(XE + "SpscX.x64_spsc_envG_concrete", E_ + "X64SpscConcrete.lean")],
    ff=[t(XE + "SpscAbs.x64_spsc_envG_runner_faultFree", E_ + "MemValsX64Spsc.lean"),
        t(XE + "SpscAbs.Concrete.x64_spsc_envG_runner_faultFree_concrete", E_ + "MemValsX64Spsc.lean")],
    verdict=[t(E + "spsc_queue_x64", TX)])
X["spsc_queue_early"] = dict(reach=[t("Reach.SpscQueueEarly.spsc_queue_early_reachable", "ReachX64SpscQueueEarly.lean")])
X["msqueue2"] = dict(
    whole=[t(XE + "MsQueueX.x64_msqueue2_envG_verbatim", E_ + "X64MsQueue2Public.lean"),
           t(XE + "MsQueueX.Concrete.x64_msqueue2_envG_verbatim_concrete", E_ + "X64MsQueue2Concrete.lean")],
    runner=[t(XE + "MsQueueX.x64_msqueue2_envG_runner", E_ + "X64MsQueue2Runner.lean"),
            t(XE + "MsQueueX.Concrete.x64_msqueue2_envG_runner_concrete", E_ + "X64MsQueue2Runner.lean")],
    nf0=[t(XE + "MsQueueX.enqRuleV_noFault", E_ + "X64MsQueue2Public.lean"),
         t(XE + "MsQueueX.deqRuleV_noFault", E_ + "X64MsQueue2Public.lean")],
    ff=[t(XE + "MsQueueX.x64_msqueue2_envG_runner_faultFree", E_ + "MemValsMsQueue.lean"),
        t(XE + "MsQueueX.Concrete.x64_msqueue2_envG_runner_faultFree_concrete", E_ + "MemValsMsQueue.lean")])
X["msqueue3"] = dict(
    whole=[t(XE + "MsQueue3X.x64_msqueue3_envG_verbatim", E_ + "X64MsQueue3Public.lean"),
           t(XE + "MsQueue3X.Concrete.x64_msqueue3_envG_verbatim_concrete", E_ + "X64MsQueue3Concrete.lean")],
    runner=[t(XE + "MsQueue3X.x64_msqueue3_envG_runner", E_ + "X64MsQueue3Runner.lean"),
            t(XE + "MsQueue3X.Concrete.x64_msqueue3_envG_runner_concrete", E_ + "X64MsQueue3Runner.lean")],
    nf0=[t(XE + "MsQueue3X.enqRule3_noFault", E_ + "X64MsQueue3Public.lean"),
         t(XE + "MsQueue3X.deqRule3_noFault", E_ + "X64MsQueue3Public.lean")],
    ff=[t(XE + "MsQueueX.x64_msqueue3_envG_runner_faultFree", E_ + "MemValsMsQueue.lean"),
        t(XE + "MsQueue3X.Concrete.x64_msqueue3_envG_runner_faultFree_concrete", E_ + "MemValsMsQueue.lean")])
X["publish_movdqa"] = dict(
    whole=[t(XE + "VecPublish.x64_publish_movdqa_verbatim", E_ + "X64VecPublish.lean")],
    runner=[t(XE + "VecPublish.Concrete.x64_publish_movdqa_verbatim_concrete", E_ + "X64VecPublishConcrete.lean")],
    ff=[t(XE + "VecPublish.x64_publish_movdqa_verbatim_faultFree", E_ + "X64VecPublish.lean"),
        t(XE + "VecPublish.Concrete.x64_publish_movdqa_verbatim_concrete_faultFree", E_ + "X64VecPublishConcrete.lean")])
X["publish_movups"] = dict(reach=[t("Reach.PublishMovups.publish_movups_reachable", "ReachX64PublishMovups.lean")])
X["treiber_aba_tagged"] = dict(
    whole=[t(XE + "VecABA.x64_treiber_aba_tagged_never", E_ + "X64VecTreiberABA.lean")],
    ff=[t(XE + "VecABA.x64_treiber_aba_tagged_runner_faultFree", E_ + "MemValsX64ABA.lean"),
        t(XE + "VecABA.Concrete.x64_treiber_aba_tagged_runner_faultFree_concrete", E_ + "MemValsX64ABAConcrete.lean")],
    # The safety theorem at the runner instance, and safe ∧ FaultFree.
    runner=[t(XE + "VecABA.Concrete.x64_treiber_aba_tagged_runner_concrete", E_ + "RunnerSafeFFX64ABA.lean")],
    sff=[t(XE + "VecABA.x64_treiber_aba_tagged_runner_safe_faultFree", E_ + "RunnerSafeFFX64ABA.lean"),
         t(XE + "VecABA.Concrete.x64_treiber_aba_tagged_runner_safe_faultFree_concrete", E_ + "RunnerSafeFFX64ABA.lean")])
X["treiber_aba_untagged"] = dict(reach=[t("Reach.TreiberAbaUntagged.treiber_aba_untagged_reachable", "ReachX64TreiberAbaUntagged.lean")])
X["mp_relay3_xchg"] = dict(
    whole=[t(XE + "RelayAbs.mp_relay3_xchg_envG_verbatim", E_ + "X64RelayAbsPublic.lean"),
           t(XE + "RelayAbs.Concrete.mp_relay3_xchg_envG_verbatim_concrete", E_ + "X64RelayAbsConcrete.lean")],
    runner=[t(XE + "RelayAbs.mp_relay3_xchg_envG_runner", E_ + "X64RelayAbsRunner.lean"),
            t(XE + "RelayAbs.Concrete.mp_relay3_xchg_envG_runner_concrete", E_ + "X64RelayAbsRunner.lean")],
    nf0=[t(XE + "RelayAbs.relayRule%sV_noFault" % r, E_ + "X64RelayAbsPublic.lean") for r in "WYD"],
    nfd=[t(XE + "RelayAbs.mp_relay3_xchg_envG_runner_noFault", E_ + "X64NoFaultDMp.lean"),
         t(XE + "RelayAbs.Concrete.mp_relay3_xchg_envG_runner_noFault_concrete", E_ + "X64NoFaultDMp.lean")],
    ff=[t(XE + "RelayAbs.mp_relay3_xchg_envG_runner_faultFree", E_ + "X64FaultFreeFixed.lean"),
        t(XE + "RelayAbs.Concrete.mp_relay3_xchg_envG_runner_faultFree_concrete", E_ + "X64FaultFreeFixed.lean")],
    extra=[t(XE + "RelayX.mp_relay3_xchg_envG", E_ + "X64RelayXchgPublic.lean"),
           t(XE + "Concrete.mp_relay3_xchg_envG_concrete", E_ + "X64RelayXchgConcrete.lean")])
X["mp_incl"] = dict(
    whole=[t(XE + "MpInclAbs.x64_mp_incl_envGV_verbatim", E_ + "X64MpInclAbsPublic.lean"),
           t(XE + "MpInclAbs.Concrete.x64_mp_incl_envGV_verbatim_concrete", E_ + "X64MpInclAbsConcrete.lean")],
    runner=[t(XE + "MpInclAbs.x64_mp_incl_envGV_runner", E_ + "X64MpInclAbsRunner.lean"),
            t(XE + "MpInclAbs.Concrete.x64_mp_incl_envGV_runner_concrete", E_ + "X64MpInclAbsRunner.lean")],
    nf0=[t(XE + "MpInclAbs.mpInclRuleWM_noFault", E_ + "X64MpInclAbsPublic.lean"),
         t(XE + "MpInclAbs.mpInclRuleRM_noFault", E_ + "X64MpInclAbsPublic.lean")],
    nfd=[t(XE + "MpInclAbs.x64_mp_incl_envGV_runner_noFault", E_ + "X64NoFaultDMpIncl.lean"),
         t(XE + "MpInclAbs.Concrete.x64_mp_incl_envGV_runner_noFault_concrete", E_ + "X64NoFaultDMpIncl.lean")],
    ff=[t(XE + "MpInclAbs.x64_mp_incl_envGV_runner_faultFree", E_ + "X64FaultFreeFixed.lean"),
        t(XE + "MpInclAbs.Concrete.x64_mp_incl_envGV_runner_faultFree_concrete", E_ + "X64FaultFreeFixed.lean")],
    extra=[t(XE + "MpInc.x64_mp_incl_envG", E_ + "X64MpIncPublic.lean"),
           t(XE + "MpIncV.x64_mp_incl_envGV", E_ + "LRValMpIncPublic.lean"),
           t(XE + "Concrete.x64_mp_incl_envG_concrete", E_ + "X64MpIncConcrete.lean")])
X["mp_incl_early"] = dict(reach=[t("Reach.MpInclEarly.mp_incl_early_reachable", "ReachX64MpInclEarly.lean")])
X["treiber_pp"] = dict(
    whole=[t(XE + "TreiberAbs.x64_treiber_pp_envG_verbatim", E_ + "X64TreiberAbsPublic.lean"),
           t(XE + "TreiberAbs.Concrete.x64_treiber_pp_envG_verbatim_concrete", E_ + "X64TreiberAbsConcrete.lean")],
    runner=[t(XE + "TreiberAbs.x64_treiber_pp_envG_runner", E_ + "X64TreiberAbsRunner.lean"),
            t(XE + "TreiberAbs.Concrete.x64_treiber_pp_envG_runner_concrete", E_ + "X64TreiberAbsRunner.lean")],
    nf0=[t(XE + "TreiberAbs.pushRuleV_noFault", E_ + "X64TreiberAbsPublic.lean"),
         t(XE + "TreiberAbs.popRuleV_noFault", E_ + "X64TreiberAbsPublic.lean")],
    nfd=[t(XE + "TreiberAbs.x64_treiber_pp_pusher_runner_noFault", E_ + "X64NoFaultDMp.lean"),
         t(XE + "TreiberAbs.Concrete.x64_treiber_pp_pusher_runner_noFault_concrete", E_ + "X64NoFaultDMp.lean")],
    ff=[t(XE + "TreiberAbs.x64_treiber_pp_envG_runner_faultFree", E_ + "MemValsTreiberPP.lean"),
        t(XE + "TreiberAbs.Concrete.x64_treiber_pp_envG_runner_faultFree_concrete", E_ + "MemValsTreiberPP.lean")],
    extra=[t(XE + "TreiberX.x64_treiber_pp_envG", E_ + "X64TreiberPublic.lean"),
           t(XE + "ConcreteTreiberX.x64_treiber_pp_envG_concrete", E_ + "X64TreiberConcrete.lean")])
X["treiber_pp_late"] = dict(reach=[t("Reach.TreiberPpLate.treiber_pp_late_reachable", "ReachX64TreiberPpLate.lean")])

# Runner-exact safety ∧ Config.FaultFree (`RunnerSafeFFX64.lean`);
# the concrete is `<namespace>.Concrete.<generic>_<suffix>`.
SFFX_ = E_ + "RunnerSafeFFX64.lean"
for k, ns, g, suf in (("spinlock2", "SpinAbs", "x64_spin_counter_envG", "concreteN"),
                      ("spinlock3", "SpinAbs", "x64_spin_counter_envG", "concreteN"),
                      ("spinlock_cmpxchg2", "CmpxAbs", "x64_cmpx_counter_envG", "concreteN"),
                      ("spinlock_cmpxchg3", "CmpxAbs", "x64_cmpx_counter_envG", "concreteN"),
                      ("dekker_mfence", "DekkerAbs", "x64_dekker_public", "concrete"),
                      ("ticketlock3", "TicketX", "ticket3_counter_envG", "concreteN"),
                      ("mp_relay3_xchg", "RelayAbs", "mp_relay3_xchg_envG", "concrete"),
                      ("mp_incl", "MpInclAbs", "x64_mp_incl_envGV", "concrete"),
                      ("spsc_queue", "SpscAbs", "x64_spsc_envG", "concrete"),
                      ("treiber_pp", "TreiberAbs", "x64_treiber_pp_envG", "concrete"),
                      ("treiber2", "Treiber2X", "x64_treiber2_envG", "concrete"),
                      ("msqueue2", "MsQueueX", "x64_msqueue2_envG", "concrete"),
                      ("msqueue3", "MsQueue3X", "x64_msqueue3_envG", "concrete")):
    X[k]["sff"] = [t("%s%s.%s_runner_safe_faultFree" % (XE, ns, g), SFFX_),
                   t("%s%s.Concrete.%s_runner_safe_faultFree_%s" % (XE, ns, g, suf), SFFX_)]

# Promise-free deadlock-freedom of the x64 `lock cmpxchg` spinlock,
# and per-thread liveness of its one-shot workers, on a valid layout of the verbatim image.
LIVESPINX = [t("Live.SpinX64CmpxPF.spin_cmpx_live_pf", "LiveSpinX64CmpxPF.lean"),
             t("Live.SpinX64CmpxPF.spin_cmpx_live_pf_concrete", "LiveSpinX64CmpxPF.lean"),
             t("Live.SpinX64CmpxPF.spin_cmpx_live_pf_runnerN", "LiveSpinX64CmpxPF.lean"),
             t("Live.SpinX64CmpxPF.spin_cmpx_live_oneShot_pf", "LiveSpinX64CmpxPF.lean"),
             t("Live.SpinX64CmpxPF.spin_cmpx_live_oneShot_pf_concrete", "LiveSpinX64CmpxPF.lean"),
             t("Live.SpinX64.cmpxSpinLivePF_of_live", "LiveSpinX64.lean")]
for k in ("spinlock_cmpxchg2", "spinlock_cmpxchg3"):
    X[k]["live"] = LIVESPINX
    X[k]["open"] = ("liveness: `Live.SpinX64.CmpxSpinLive` (deadlock-freedom under weak + memory fairness, "
                    "promises allowed) is open; its promise-free fragment `CmpxSpinLivePF` is proved on a valid "
                    "layout of the image (`Litmus/KNOWN_GAPS.md`, \"Liveness: spinlocks, x64 (LIVESPINX)\")")
# The same for the x64 `xchg` (test-and-test-and-set) spinlock.
LIVESPINX2 = [t("Live.SpinX64XchgPF.spin_xchg_live_pf", "LiveSpinX64XchgPF.lean"),
              t("Live.SpinX64XchgPF.spin_xchg_live_pf_concrete", "LiveSpinX64XchgPF.lean"),
              t("Live.SpinX64XchgPF.spin_xchg_live_pf_runnerN", "LiveSpinX64XchgPF.lean"),
              t("Live.SpinX64XchgPF.spin_xchg_live_oneShot_pf", "LiveSpinX64XchgPF.lean"),
              t("Live.SpinX64XchgPF.spin_xchg_live_oneShot_pf_concrete", "LiveSpinX64XchgPF.lean"),
              t("Live.SpinX64Xchg.xchgSpinLivePF_of_live", "LiveSpinX64Xchg.lean")]
for k in ("spinlock2", "spinlock3"):
    X[k]["live"] = LIVESPINX2
    X[k]["open"] = ("liveness: `Live.SpinX64Xchg.XchgSpinLive` (deadlock-freedom under weak + memory fairness, "
                    "promises allowed) is open; its promise-free fragment `XchgSpinLivePF` is proved on a valid "
                    "layout of the image (`Litmus/KNOWN_GAPS.md`, \"Liveness: spinlocks, x64 (LIVESPINX)\")")
# Deadlock-freedom of the x64 `lock cmpxchg` spinlock with promises on the machine with
# semantic certification (every fuel, `WeakFairSem ∧ MemFair`), and the one-shot corollary.
LIVESPINXSEM = [t("Live.SpinX64SemCmpx.spin_cmpx_live_sem", "LiveSpinX64SemCmpx.lean"),
                t("Live.SpinX64SemCmpx.spin_cmpx_live_sem_concrete", "LiveSpinX64SemCmpx.lean"),
                t("Live.SpinX64SemCmpx.spin_cmpx_live_oneShot_sem", "LiveSpinX64SemCmpx.lean"),
                t("Live.SpinX64SemCmpx.spin_cmpx_live_oneShot_sem_concrete", "LiveSpinX64SemCmpx.lean")]
for k in ("spinlock_cmpxchg2", "spinlock_cmpxchg3"):
    X[k]["live"] = LIVESPINXSEM + X[k]["live"]
    X[k]["open"] = ("liveness: `Live.SpinX64.CmpxSpinLive` (deadlock-freedom under weak + memory fairness, "
                    "promises allowed, over `succs`) is open (incomplete `certify` search); proved with "
                    "semantic certification for every fuel as `CmpxSpinLiveSem`, and promise-free as "
                    "`CmpxSpinLivePF`, on a valid layout of the image (`Litmus/KNOWN_GAPS.md`, \"Liveness: "
                    "spinlocks, x64 (LIVESPINX)\")")
# Deadlock-freedom of the x64 `xchg` spinlock with promises on the machine with
# semantic certification (`CertOkN`, `WeakFairSem ∧ MemFair`), for every fuel, and the one-shot corollary.
LIVESPINXSEM2 = [t("Live.SpinX64SemXchgLive.spin_xchg_live_sem", "LiveSpinX64SemXchgLive.lean"),
                 t("Live.SpinX64SemXchgLive.spin_xchg_live_sem_concrete", "LiveSpinX64SemXchgLive.lean"),
                 t("Live.SpinX64SemXchgLive.spin_xchg_live_sem_runnerN", "LiveSpinX64SemXchgLive.lean"),
                 t("Live.SpinX64SemXchgLive.spin_xchg_live_oneShot_sem", "LiveSpinX64SemXchgLive.lean"),
                 t("Live.SpinX64SemXchgLive.spin_xchg_live_oneShot_sem_concrete", "LiveSpinX64SemXchgLive.lean")]
for k in ("spinlock2", "spinlock3"):
    X[k]["live"] = LIVESPINXSEM2 + X[k]["live"]
    X[k]["open"] = ("liveness: `Live.SpinX64Xchg.XchgSpinLive` (deadlock-freedom under weak + memory fairness, "
                    "promises allowed, over `succs`) is open (incomplete `certify` search); proved with semantic "
                    "certification for every fuel as `SpinX64Sem.XchgSpinLiveSem`, and promise-free as "
                    "`XchgSpinLivePF`, on a valid layout of the image (`Litmus/KNOWN_GAPS.md`, \"Liveness: "
                    "spinlocks, x64 (LIVESPINX)\")")

# Promise-free liveness of the x64 ticket lock `ticketlock3` (store release) on a valid
# layout of the verbatim image, and the weak-fairness-only refutation (kernel-checked lasso).
X["ticketlock3"]["live"] = [t("Live.TicketX64PF.ticket3_x64_live_pf", "LiveX64TicketPF.lean"),
                            t("Live.TicketX64PF.ticket3_x64_live_pf_concrete", "LiveX64TicketPF.lean"),
                            t("Live.TicketX64Cex.ticketX64LiveWF_false", "LiveX64TicketCex.lean"),
                            t("Live.TicketX64.ticketX64LivePF_of_live", "LiveX64Ticket.lean")]
X["ticketlock3"]["open"] = ("liveness: `Live.TicketX64.TicketX64Live` (weak + memory fairness, promises allowed) is "
                            "open; its promise-free fragment `TicketX64LivePF` is proved on a valid layout of the image "
                            "(`Litmus/KNOWN_GAPS.md`, \"Liveness: ticket lock, x64 (LIVEX64A)\")")
# Liveness of `ticketlock3` with promises on the machine with semantic certification
# (`CertOkN`), for every fuel, on a valid layout of the image (the x64 counterpart of `ticket_live_sem`).
X["ticketlock3"]["live"] = X["ticketlock3"]["live"] + [
    t("Live.X64SemTicket.ticket3_x64_live_sem", "LiveX64SemTicket.lean"),
    t("Live.X64SemTicket.ticket3_x64_live_sem_concrete", "LiveX64SemTicket.lean")]
X["ticketlock3"]["open"] = ("liveness: `Live.TicketX64.TicketX64Live` (weak + memory fairness, promises allowed, "
                            "stated over `succs`, whose certification search `certify` is incomplete) is open; it is "
                            "proved for every fuel with semantic certification as `X64Sem.TicketX64LiveSem`, and its "
                            "promise-free fragment `TicketX64LivePF` is proved on a valid layout of the image "
                            "(`Litmus/KNOWN_GAPS.md`, \"Liveness: ticket lock, x64 (LIVEX64A)\")")

# Promise-free liveness of the x64 ticket lock `ticketlock2` (unlocked `incl` release) on a valid
# layout of the verbatim image; the weak-fairness-only refutation (kernel-checked lasso).
X["ticketlock2"]["live"] = [t("Live.Ticket2X64PF.ticket2_x64_live_pf", "LiveX64Ticket2PF.lean"),
                            t("Live.Ticket2X64PF.ticket2_x64_live_pf_concrete", "LiveX64Ticket2PF.lean"),
                            t("Live.Ticket2X64Cex.ticket2X64LiveWF_false", "LiveX64Ticket2Cex.lean"),
                            t("Live.Ticket2X64.ticket2X64LivePF_of_live", "LiveX64Ticket2.lean")]
X["ticketlock2"]["open"] = ("liveness: `Live.Ticket2X64.Ticket2X64Live` (weak + memory fairness, promises allowed) is "
                            "open; its promise-free fragment `Ticket2X64LivePF` is proved on a valid layout of the image "
                            "(`Litmus/KNOWN_GAPS.md`, \"Liveness: ticket lock, x64 (LIVEX64A)\")")
# Liveness of `ticketlock2` with promises on the machine with semantic certification
# (`CertOkN`), for every fuel, on a valid layout of the image (the unlocked `incl` counterpart of the `ticketlock3` theorem).
X["ticketlock2"]["live"] = X["ticketlock2"]["live"] + [
    t("Live.X64Sem2Ticket.ticket2_x64_live_sem", "LiveX64Sem2Ticket.lean"),
    t("Live.X64Sem2Ticket.ticket2_x64_live_sem_concrete", "LiveX64Sem2Ticket.lean")]
X["ticketlock2"]["open"] = ("liveness: `Live.Ticket2X64.Ticket2X64Live` (weak + memory fairness, promises allowed, "
                            "stated over `succs`, whose certification search `certify` is incomplete) is open; it is "
                            "proved for every fuel with semantic certification as `X64Sem2.Ticket2X64LiveSem`, and its "
                            "promise-free fragment `Ticket2X64LivePF` is proved on a valid layout of the image "
                            "(`Litmus/KNOWN_GAPS.md`, \"Liveness: ticket lock, x64 (LIVEX64A)\")")

# The x64 promise-free liveness theorems above lifted from `decls = {}` to the runner's
# declarations (`decls = ds`, `ds` resolving the image's words to themselves, `Decls.AgreesAt`), at the
# runner's layout and N-worker configuration (`Live.RunnerSim.progressFrom_transfer`).
RR_ = "Live.RunnerX64"
for k, ns, f, g in (("ticketlock3", "Ticket", "LiveRunnerX64Ticket.lean", "ticket3_x64_live_pf"),
                    ("ticketlock2", "Ticket2", "LiveRunnerX64Ticket2.lean", "ticket2_x64_live_pf"),
                    ("spinlock_cmpxchg2", "Spin", "LiveRunnerX64Spin.lean", "spin_cmpx_live_pf"),
                    ("spinlock_cmpxchg3", "Spin", "LiveRunnerX64Spin.lean", "spin_cmpx_live_pf"),
                    ("spinlock2", "Spin", "LiveRunnerX64Spin.lean", "spin_xchg_live_pf"),
                    ("spinlock3", "Spin", "LiveRunnerX64Spin.lean", "spin_xchg_live_pf")):
    X[k]["live"] = X[k]["live"] + [t("%s%s.%s_runner%s" % (RR_, ns, g, s), f)
                                   for s in ("", "_concrete", "N")]
    X[k]["open"] = X[k]["open"] + ("; the promise-free fragment is also proved with the runner's declarations "
                                   "and N-worker configuration (`Litmus/KNOWN_GAPS.md`, \"Liveness: runner "
                                   "declarations (LIVERUN)\")")
# The AArch64 promise-free liveness theorems lifted to the runner's declarations
# (`decls = ds` agreeing at the lock words, `Decls.AgreesAt`), at the runner's layout and N-worker
# configuration, through the dynamic-invariant bridge `Live.RunnerA64.execSimA`.
RA_ = "Live.RunnerA64"
for ks, ns, f, gs in ((("ticketlock2", "ticketlock3"), "Ticket", "LiveRunnerA64Ticket.lean", ("ticket_live_pf",)),
                      (("spinlock_cas2", "spinlock_cas3"), "Cas", "LiveRunnerA64Cas.lean",
                       ("spin_cas_live_pf", "spin_cas_live_oneShot_pf")),
                      (("spinlock_swp2", "spinlock_swp3"), "Swp", "LiveRunnerA64Swp.lean",
                       ("spin_swp_live_pf", "spin_swp_live_oneShot_pf")),
                      (("spinlock_swpl2", "spinlock_swpl3"), "Swp", "LiveRunnerA64Swp.lean",
                       ("spin_swpl_live_pf", "spin_swpl_live_oneShot_pf"))):
    for k in ks:
        A[k]["live"] = A[k]["live"] + [t("%s%s.%s_runner%s" % (RA_, ns, g, s), f)
                                       for g in gs for s in ("", "_concrete", "N")]
        A[k]["open"] = A[k]["open"] + ("; the promise-free fragment is also proved with the runner's "
                                       "declarations and N-worker configuration (`Litmus/KNOWN_GAPS.md`, "
                                       "\"Liveness: runner declarations (LIVERUN)\")")
# The x64 one-shot per-thread spinlock forms lifted the same way
# (`Live.RunnerSim.liveFrom_transfer`, same start structures as the runner spinlock theorems).
for k, g in (("spinlock_cmpxchg2", "spin_cmpx_live_oneShot_pf"), ("spinlock_cmpxchg3", "spin_cmpx_live_oneShot_pf"),
             ("spinlock2", "spin_xchg_live_oneShot_pf"), ("spinlock3", "spin_xchg_live_oneShot_pf")):
    X[k]["live"] = X[k]["live"] + [t("Live.RunnerX64One.%s_runner%s" % (g, s), "LiveRunnerX64One.lean")
                                   for s in ("", "_concrete", "N")]
# The with-promises liveness theorems (semantic certification, `WeakFairSem ∧ MemFair`)
# lifted to the runner's declarations (same start structures and `Decls.AgreesAt` hypotheses as the
# promise-free runner forms), through `Live.RunnerSemSim.liveFromSem_transfer` / `progressFromSem_transfer`.
RS_ = "Live.RunnerSem"
for D, ks, ns, f, gs in ((A, ("ticketlock2", "ticketlock3"), "A64Ticket", "LiveRunnerSemA64Ticket.lean",
                          ("ticket_live_sem",)),
                         (A, ("spinlock_cas2", "spinlock_cas3"), "A64Cas", "LiveRunnerSemA64Cas.lean",
                          ("spin_cas_live_sem", "spin_cas_live_oneShot_sem")),
                         (X, ("ticketlock3",), "X64Ticket", "LiveRunnerSemX64Ticket.lean",
                          ("ticket3_x64_live_sem",)),
                         (A, ("spinlock_swp2", "spinlock_swp3"), "A64Swp", "LiveRunnerSemA64Swp.lean",
                          ("spin_swp_live_sem", "spin_swp_live_oneShot_sem")),
                         (A, ("spinlock_swpl2", "spinlock_swpl3"), "A64Swp", "LiveRunnerSemA64Swp.lean",
                          ("spin_swpl_live_sem", "spin_swpl_live_oneShot_sem")),
                         (X, ("ticketlock2",), "X64Ticket2", "LiveRunnerSemX64Ticket2.lean",
                          ("ticket2_x64_live_sem",)),
                         # The x64 `lock cmpxchg` spinlock (`CmpxStartD ds`, `execSimD`).
                         (X, ("spinlock_cmpxchg2", "spinlock_cmpxchg3"), "X64Cmpx", "LiveRunnerSemX64Cmpx.lean",
                          ("spin_cmpx_live_sem", "spin_cmpx_live_oneShot_sem")),
                         # The x64 `xchg` spinlock (`XchgStartD ds`, `execSimD`).
                         (X, ("spinlock2", "spinlock3"), "X64Xchg", "LiveRunnerSemX64Xchg.lean",
                          ("spin_xchg_live_sem", "spin_xchg_live_oneShot_sem"))):
    for k in ks:
        D[k]["live"] = D[k]["live"] + [t("%s%s.%s_runner%s" % (RS_, ns, g, s), f)
                                       for g in gs for s in ("", "_concrete", "N")]
        D[k]["open"] = D[k]["open"] + ("; the with-promises (semantic certification) theorem is also proved with "
                                       "the runner's declarations and N-worker configuration "
                                       "(`Litmus/KNOWN_GAPS.md`, \"Liveness: runner declarations (LIVERUN)\")")

# The `ldaddal` ticket lock's liveness table (explicit statements in
# `LiveTicketAlThm.lean`; proofs by `#ticket_al_clone` of the `ldadda` chain).
for k in ("ticketlock_al2", "ticketlock_al3"):
    A[k]["live"] = A[k].get("live", []) + [t("Live.TicketAl.%s" % g, "LiveTicketAlThm.lean") for g in (
        "ticket_al_live_pf", "ticket_al_live_pf_concrete", "ticket_al_live_sem", "ticket_al_live_sem_concrete",
        "ticketAlLiveWF_false", "ticket_al_live_pf_runner", "ticket_al_live_pf_runner_concrete",
        "ticket_al_live_pf_runnerN", "ticket_al_live_sem_runner", "ticket_al_live_sem_runner_concrete",
        "ticket_al_live_sem_runnerN")]
    A[k]["open"] = ((A[k]["open"] + "; ") if A[k].get("open") else "") + (
        "liveness: `Live.TicketAl.TicketAlLive` (weak + memory fairness, promises allowed, executable machine) "
        "is open for fuel ≥ 1, as for `ticketlock2`; proved for every fuel with semantic certification and "
        "promise-free on a valid layout (`Litmus/KNOWN_GAPS.md`, \"Liveness (LIVEPF)\", update TICKETAL)")

# Fair traces from the x64 and `ldaddal` start configurations, and
# `Progressive` at the runner starts (`*_progressive_runner`, via `progressive_of_mapC`).
FWX = "LiveSemWitnessX64.lean"
for ks, nm in ((("spinlock_cmpxchg2", "spinlock_cmpxchg3"), "cmpx"), (("spinlock2", "spinlock3"), "xchg"),
               (("ticketlock3",), "tkX"), (("ticketlock2",), "tk2X")):
    for k in ks:
        X[k].setdefault("extra", []).extend([t("Live.WitnessX64.%s_fair_exists" % nm, FWX),
                                             t("Live.WitnessX64.%s_fairSem_exists" % nm, FWX),
                                             t("Live.WitnessX64.%s_progressive_runner" % nm, FWX)])
FWA = "LiveSemWitnessTicketAl.lean"
for k in ("ticketlock_al2", "ticketlock_al3"):
    A[k].setdefault("extra", []).extend([t("Live.WitnessTicketAl.%s" % g, FWA) for g in (
        "tkAl_fair_exists", "tkAl_fairSem_exists", "tkAl_progressive_runner")])
FWR = "LiveSemWitnessA64Runner.lean"
for ks, nm in ((("ticketlock2", "ticketlock3"), "tk"), (("spinlock_cas2", "spinlock_cas3"), "cas"),
               (("spinlock_swp2", "spinlock_swp3", "spinlock_swpl2", "spinlock_swpl3"), "swp")):
    for k in ks:
        A[k]["extra"].append(t("Live.WitnessA64.%s_progressive_runner" % nm, FWR))

# Bounded termination on the semantic machine under every schedule, no fairness
# (`TermBoundSem`, generic part `LiveTerm.lean`; statements in `LiveTermTreiber2Thm.lean`).
TM = "LiveTermTreiber2Thm.lean"
A["treiber2"].setdefault("extra", []).extend([t("Live.TermTreiber2.treiber2_term_sem", TM),
                                              t("Live.TermTreiber2.treiber2_term_sem_concrete", TM),
                                              t("Live.TermTreiber2.treiber2_term_sem_gen", "LiveTermTreiber2.lean")])
A["treiber2_arm"].setdefault("extra", []).extend([t("Live.TermTreiber2Arm.treiber2_arm_term_sem", TM),
                                                  t("Live.TermTreiber2Arm.treiber2_arm_term_sem_concrete", TM),
                                                  t("Live.TermTreiber2Arm.treiber2_arm_term_sem_all", TM)])
A["treiber2_relaxed"].setdefault("extra", []).extend([t("Live.TermTreiber2Relaxed.treiber2_relaxed_term_sem", TM),
                                                      t("Live.TermTreiber2Relaxed.treiber2_relaxed_term_sem_all", TM)])
# `treiber2_nodes`, by the position-parametric form `LiveTermTreiber2P.lean`.
TN = "LiveTermTreiber2Nodes.lean"
A["treiber2_nodes"].setdefault("extra", []).extend([t("Live.TermTreiber2Nodes.treiber2_nodes_term_sem", TN),
                                                    t("Live.TermTreiber2Nodes.treiber2_nodes_term_sem_concrete", TN),
                                                    t("Live.TermTreiber2Nodes.treiber2_nodes_term_sem_all", TN)])

# Repeated-acquire ticket lock (k rounds per thread). Safety: bounded run.sh check
# only (loop3 is `# slow`, no verdict). Liveness: the full statements on the semantic machine,
# promises included (`LiveTicketLoopSem.lean`); the promise-free fragment
# (`LiveTicketLoopPF.lean`) and F3 (`holder_nacert'`) are listed as extras (KNOWN_GAPS.md,
# "Liveness: repeated acquisition (LOOP)").
LP = "LiveTicketLoopPF.lean"; LW = "LiveTicketLoopWitness.lean"; LS = "LiveTicketLoopSem.lean"
for k in ("ticketlock_loop2", "ticketlock_loop3"):
    A[k] = dict(live=[t("Live.TicketLoopSem.ticket_loop_starve_sem", LS),
                      t("Live.TicketLoopSem.ticket_loop_finish_sem", LS),
                      t("Live.TicketLoopSem.ticket_loop_live_sem", LS),
                      t("Live.TicketLoopSem.ticket_loop_live_sem_concrete", LS)],
                extra=[t("Live.TicketLoopSem.ticket_loop_term_sem", LS),
                       t("Live.TicketLoopInvP.holder_nacert'", "LiveTicketLoopInvP.lean"),
                       t("Live.TicketLoopPF.ticket_loop_starve_pf", LP),
                       t("Live.TicketLoopPF.ticket_loop_finish_pf", LP),
                       t("Live.TicketLoopPF.ticket_loop_live_pf", LP),
                       t("Live.TicketLoopPF.ticket_loop_live_pf_concrete", LP),
                       t("Live.TicketLoopWitness.tk_loop_fairSem_exists", LW),
                       t("Live.TicketLoopWitness.tk_loop_fairSemPF_exists", LW)],
                open="safety: only the bounded run.sh check (loop3 `# slow`, no verdict); liveness is proved "
                     "(`TicketLoopStarveSem`/`TicketLoopFinishSem`/`TicketLoopTermSem`, WeakFairSem ∧ MemFair, "
                     "promises allowed) for every valid layout, fuel, N and k with N*k+1 < 2^32 (KNOWN_GAPS.md, "
                     "\"Liveness: repeated acquisition (LOOP)\")")

# Programs with no theorem yet. The `# expect:` verdict of
# each `.kl` (checked by run.sh / run_x64.sh only, no `native_decide` theorem) and the gap.
CL_CORE = ("the memory-level core is `Promising/SLR/EnvG/ChaseLevCore.lean` (CHASE, ISA-neutral), "
           "not yet a whole-program theorem")
A["chaselev2"] = dict(open="explorer verdict `Always` (Chase–Lev deque with the owner's `DMB ISH`); no theorem: " + CL_CORE)
A["chaselev2_nofence"] = dict(open="explorer verdict `Sometimes` (no owner fence: store buffering, the duplicate "
                                   "outcome `0:X10=2, 1:X10=1, 1:X11=2`); no reachability theorem")
A["flatmap2"] = dict(open="explorer verdict `Always` (flat hash map: `CASAL` key, `STLR` value, `LDAR` lookups); no theorem")
A["flatmap2_relaxed"] = dict(open="explorer verdict `Sometimes` (plain reader loads: only the causality clause fails); "
                                  "no reachability theorem")
A["flatmap_pair2"] = dict(open="explorer verdict `Sometimes` with `-lse2` (torn `{key, value}` pair; Kraken weaker than "
                               "hardware: `CASP` is two per-half `rmw` events and `LDP` on two 8-byte cells is two loads; "
                               "the CASP decision K1, `Litmus/KNOWN_GAPS.md` CASP paragraph); no theorem")
A["flatmap_pair2_casp"] = dict(open="explorer verdict `Sometimes` with `-lse2` (only `CASPAL` accesses: the torn pair comes "
                                    "from the two-event `CASP` alone; Always with `CASP` as one 16-byte `rmw`, K1); no theorem")
X["chaselev2"] = dict(open="explorer verdict `Always` at fuel 300 (owner's `mfence`); no theorem: " + CL_CORE)
X["chaselev2_nofence"] = dict(open="explorer verdict `Sometimes` at fuel 300 (no owner `mfence`: store buffering, the "
                                   "duplicate outcome `0:r12=2, 1:r12=1, 1:r13=2`); no reachability theorem")
X["flatmap2"] = dict(open="explorer verdict `Always` at fuel 300 (`lock cmpxchgq` key, plain `movq` publication); no theorem")
X["flatmap_pair2"] = dict(open="explorer verdict `Always` at fuel 300 (`lock cmpxchg16b` is one `rmw`, `movdqa` one "
                               "16-byte access; the x64 side of the pair-atomicity evidence); no theorem")

# TWINS: the `ReachableSem` twin `n_sem` of every listed theorem `n` that has one
# (`ChainK/SemTwin.lean`, `#sem_twin`) goes to the program's "extra" column. The twins
# are read from the generated listing `SEM_TWINS.md` (`tools/sem_twins.py`).
def _sem_twins():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "SEM_TWINS.md")
    tw = {}
    if not os.path.exists(path):
        return tw
    side = None
    for l in open(path):
        if l.startswith("## "):
            side = l[3:].strip()
        elif l.startswith("- `") and "(twin of `" in l:
            twin = l[3:l.index("`", 3)]
            orig = l[l.index("(twin of `") + 10:]
            orig = orig[:orig.index("`")]
            f = ("SLR/ChainK/TicketA64Demo.lean" if twin == "SLR.EnvG.TicketLock.ticket_counter_envG_sem"
                 else "SLR/ChainK/SemTwins%s.lean" % ("A64" if side == "AArch64" else "X64"))
            tw[t(orig, f)[0]] = t(twin, f)
    return tw

SEM_TWINS = _sem_twins()
for D in (A, X):
    for d in D.values():
        tws = [SEM_TWINS[n] for c in ("whole", "runner", "nf0", "nfd", "ff", "sff", "reach", "live", "verdict", "extra")
               for n, _ in d.get(c, []) if n in SEM_TWINS]
        if tws:
            d["extra"] = d.get("extra", []) + [x for i, x in enumerate(tws) if x not in tws[:i]]

COLS = ("whole", "runner", "nf0", "nfd", "ff", "sff", "reach", "live", "verdict", "extra")

def names(D):
    for prog, d in D.items():
        for c in COLS:
            for n, f in d.get(c, []):
                yield prog, c, n, f

def module(f):
    return "Kraken." + f[:-5].replace("/", ".")

def checkfile(D):
    mods = sorted({module(f) for _, _, _, f in names(D)})
    out = ["import " + m for m in mods] + [""]
    for _, _, n, _ in names(D):
        out.append("#check @" + n)
    return "\n".join(out) + "\n"

if __name__ == "__main__":
    import glob
    os.makedirs(".lake/docs", exist_ok=True)
    for isa, D in (("AArch64", A), ("X64", X)):
        kls = sorted(os.path.basename(p)[:-3] for p in glob.glob("Kraken/Examples/LockFree/%s/*.kl" % isa))
        missing = set(kls) - set(D); extra = set(D) - set(kls)
        print(isa, "missing", sorted(missing), "extra", sorted(extra))
        for _, _, n, f in names(D):
            if not os.path.exists("Kraken/" + f):
                print("NOFILE", n, f)
        open(".lake/docs/check_%s.lean" % isa.lower(), "w").write(checkfile(D))
