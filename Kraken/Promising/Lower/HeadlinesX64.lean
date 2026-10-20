/-
**Machine-checked index of the x64 lowering headlines.**
Imported by nothing (built by the `Kraken.*` glob of the default
`lake build`). The AArch64 twin, and the conventions of both files, are in
`Lower/Headlines.lean`; the guide is `Lower/README.md`; the table is the "Lowering" section of
`Examples/LockFree/THEOREMS.md`.

Each name gets `#check @Name` (output dropped by `#guard_msgs (drop info)`); the headlines also
get `#print axioms Name` under `#guard_msgs`. All are `[propext, Classical.choice, Quot.sound]`.

Machine: the executable machine `Reachable Arch.tso fuel` of the x64 `isa`. Hypotheses:
`PilotXR.pilotXR_promising` assumes start states only (`StartXR`, `top = 0`) and
`PilotXR.Concrete.pilotXR_concrete` nothing beyond reachability; the x64 pilot's
`PilotX.pilotX_promising` assumes start states only (`StartPX`, `top = 0`, initial memory in
`GV P`), via `Vals.envGValsBridgeX_ofPure`, and `PilotX.Concrete.pilotX_concrete` nothing beyond
reachability; its conditional form
`PilotX.pilotX_promising_of_bridge_pure` (on `hbridge`, `hsp`, `hvals`) is kept. The x64 MS queue pilot (`MsqXR.msqXR_promising`, `Concrete.msqXR_concrete`) is at the end.
-/
import Kraken.Promising.Lower.KitX64Treiber2
import Kraken.Promising.Lower.PilotXRConcrete
import Kraken.Promising.Lower.PilotX64Link
import Kraken.Promising.Lower.PilotX64Whole
import Kraken.Promising.Lower.PilotX64Concrete
import Kraken.Promising.Lower.EventsX64Fence
import Kraken.Promising.Lower.EventsX64LockBin
import Kraken.Promising.Lower.FetchOpX64
import Kraken.Promising.Lower.MsqAllocXWhole
import Kraken.Promising.Lower.FragKitMsqX
import Kraken.Promising.Lower.FragSpecPilotX64
import Kraken.Promising.Lower.FragSpecLoopCallsX64Demo
import Kraken.Promising.Lower.MsqXRWhole
import Kraken.Promising.Lower.MsqXRConcrete
import Kraken.Promising.Lower.PilotsX64Sem
import Kraken.Promising.SLR.EnvG.X64MsQueueWFinal
import Kraken.Promising.SLR.EnvG.X64MsQueueWVC
import Kraken.Promising.Lower.WcMsqXConcrete
import Kraken.Promising.Lower.FragSpecProcX64
import Kraken.Promising.Lower.WcMsqXForms
import Kraken.Promising.Lower.KitX64ValsSem
import Kraken.Promising.Lower.FlatLookupX64

/-! ### Kit (the x64 kit, `KitX64.lean`) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64_vals
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_vals
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.safely_of_partialTripleEnvX
/-- info: 'Kraken.Promising.Lower.KitX.safely_of_partialTripleEnvX' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.safely_of_partialTripleEnvX
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.LowerThreadX.rule_noFault
/-- info: 'Kraken.Promising.Lower.KitX.LowerThreadX.rule_noFault' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.LowerThreadX.rule_noFault

/-! ### the x64 register-link pilot and the x64 pilot with a `dmem` stack -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotXR.pilotXR_promising
/-- info: 'Kraken.Promising.Lower.PilotXR.pilotXR_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotXR.pilotXR_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotXR.Concrete.pilotXR_concrete
/-- info: 'Kraken.Promising.Lower.PilotXR.Concrete.pilotXR_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotXR.Concrete.pilotXR_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pilotX_promising
/-- info: 'Kraken.Promising.Lower.PilotX.pilotX_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pilotX_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.Concrete.pilotX_concrete
/-- info: 'Kraken.Promising.Lower.PilotX.Concrete.pilotX_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.Concrete.pilotX_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure
/-- info: 'Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pilotX_promising_of_bridge_pure
/--
info: 'Kraken.Promising.Lower.PilotX.pilotX_promising_of_bridge_pure' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pilotX_promising_of_bridge_pure
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pilotX_final
/-- info: 'Kraken.Promising.Lower.PilotX.pilotX_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pilotX_final

/-! ### Kit instance -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.Treiber2.x64_treiber2_envG_verbatim_viaKit
/--
info: 'Kraken.Promising.Lower.KitX.Treiber2.x64_treiber2_envG_verbatim_viaKit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.KitX.Treiber2.x64_treiber2_envG_verbatim_viaKit

/-! ### Value bridge (the value bridge, x64) -/

#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofSpecs
/-- info: 'Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofSpecs' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofSpecs
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.envGValsBridgeX_true
/-- info: 'Kraken.Promising.Lower.PilotX.envGValsBridgeX_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.envGValsBridgeX_true

/-! ### Fragment-spec rules (`FragSpec*X64.lean`) -/

#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_cfg
/-- info: 'MachineWP.FragSpecEnv.of_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.of_cfg
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_placed
/-- info: 'MachineWP.FragSpecEnv.of_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.of_placed
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.mono
/-- info: 'MachineWP.FragSpecEnv.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.mono
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.of_placed
/-- info: 'MachineWP.FragSpecEnvL.of_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.of_placed
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.tail
/-- info: 'MachineWP.FragSpecEnvL.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.tail
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.callLink
/-- info: 'MachineWP.FragSpecEnvL.callLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.callLink
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.of_cfgP
/-- info: 'MachineWP.FragSpecEnvL.of_cfgP' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.of_cfgP
#guard_msgs (drop info) in #check @MachineWP.PartialWpEnvS.jmpCall
/-- info: 'MachineWP.PartialWpEnvS.jmpCall' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.PartialWpEnvS.jmpCall
#guard_msgs (drop info) in #check @MachineWP.PartialWpEnvS.callLink
/-- info: 'MachineWP.PartialWpEnvS.callLink' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.PartialWpEnvS.callLink
#guard_msgs (drop info) in #check @MachineWP.PartialWpEnvS.call_triples
/-- info: 'MachineWP.PartialWpEnvS.call_triples' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.PartialWpEnvS.call_triples
#guard_msgs (drop info) in #check @MachineWP.cfgEnv_partial_funS
/-- info: 'MachineWP.cfgEnv_partial_funS' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.cfgEnv_partial_funS

/-! ### Fragment-spec plumbing (x64; `#check` only) -/

#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_layout
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.at
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.toL
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.toFrag
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.at_sub
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.mono

/-! ### Fragment specs (x64) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pushFragX_spec
/-- info: 'Kraken.Promising.Lower.PilotX.pushFragX_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pushFragX_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.popFragX_spec
/-- info: 'Kraken.Promising.Lower.PilotX.popFragX_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.popFragX_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.push_specX_viaFrag
/-- info: 'Kraken.Promising.Lower.PilotX.push_specX_viaFrag' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.push_specX_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pop_specX_viaFrag
/-- info: 'Kraken.Promising.Lower.PilotX.pop_specX_viaFrag' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pop_specX_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.LoopCallsX.popFragXR_pure
/-- info: 'Kraken.Promising.Lower.LoopCallsX.popFragXR_pure' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.LoopCallsX.popFragXR_pure
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.LoopCallsX.popwX_spec
/-- info: 'Kraken.Promising.Lower.LoopCallsX.popwX_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.LoopCallsX.popwX_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.LoopCallsX.popwX_spec_at
/-- info: 'Kraken.Promising.Lower.LoopCallsX.popwX_spec_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.LoopCallsX.popwX_spec_at

/-! ### x64 Michael–Scott queue, stackless register-link (the x64 MS queue pilot): `Lower/MsqXR*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.msqXR_promising
/-- info: 'Kraken.Promising.Lower.MsqXR.msqXR_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqXR.msqXR_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.enq_fragXR
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.deq_fragXR
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.mainE_specXR
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.mainD_specXR
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.msqXR_pureE
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.msqXR_pureD
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.Concrete.msqXR_concrete
/-- info: 'Kraken.Promising.Lower.MsqXR.Concrete.msqXR_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqXR.Concrete.msqXR_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.Concrete.msqXR_noFault

/-! ### x64 event gaps (the x64 event lemmas): `Lower/EventsX64Fence.lean`, `EventsX64LockBin.lean`, `FetchOpX64.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Tso.reachableSemInf_ldFold
/-- info: 'Kraken.Promising.Lower.Tso.reachableSemInf_ldFold' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Tso.reachableSemInf_ldFold
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Tso.instrSemInf_fence_ld_stutter
/-- info: 'Kraken.Promising.Lower.Tso.instrSemInf_fence_ld_stutter' depends on axioms: [propext, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Tso.instrSemInf_fence_ld_stutter
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.X64.instrSemInf_lfence_stutter
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.X64.instrSemInf_lockBin
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FetchOpX.fetchOpFragX_spec
/-- info: 'Kraken.Promising.Lower.FetchOpX.fetchOpFragX_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.FetchOpX.fetchOpFragX_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FetchOpX.fetchOrFragX_spec

/-! ### x64 MS queue, enqueuer bump-allocates (the x64 allocating MS queue pilot): `Lower/MsqAllocX{Prog,Main,Whole}.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAllocX.msqAllocX_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAllocX.allocFragX_spec

/-! ### x64 fragment-spec kit bridge (the x64 fragment kit): `Lower/KitFragX.lean`, `FragKitMsqX.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.safely_of_fragL
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.LowerThreadX.ofFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.LowerStaticX.ofFragPure
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FragKitX.msqXR_promising_viaFragKitX

/-! ### x64 kit and pilots on the semantic machines (the x64 semantic-machine kit): `Lower/KitX64Sem.lean`, `KitX64ValsPureSem.lean`, `PilotsX64Sem.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64K
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64K' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64K
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64_sem
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64_semInf
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotXR.pilotXR_promising_sem
/-- info: 'Kraken.Promising.Lower.PilotXR.pilotXR_promising_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotXR.pilotXR_promising_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotXR.pilotXR_promising_semInf
/-- info: 'Kraken.Promising.Lower.PilotXR.pilotXR_promising_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotXR.pilotXR_promising_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.msqXR_promising_sem
/-- info: 'Kraken.Promising.Lower.MsqXR.msqXR_promising_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqXR.msqXR_promising_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqXR.msqXR_promising_semInf
/-- info: 'Kraken.Promising.Lower.MsqXR.msqXR_promising_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqXR.msqXR_promising_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_sem
/-- info: 'Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_semInf
/-- info: 'Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqAllocX.msqAllocX_promising_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_sem
/-- info: 'Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_sem
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_semInf
/--
info: 'Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_semInf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.X64.EnvG.Vals.envGValsBridgeX_ofPure_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pilotX_promising_sem
/-- info: 'Kraken.Promising.Lower.PilotX.pilotX_promising_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pilotX_promising_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.PilotX.pilotX_promising_semInf
/-- info: 'Kraken.Promising.Lower.PilotX.pilotX_promising_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.PilotX.pilotX_promising_semInf

/-! ### x64 MS queue protocol for try-once dequeuers without a `tail` check: `SLR/EnvG/X64MsQueueW*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.MsQueueX.final_valuesW
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.MsQueueX.vc_w_pop
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.MsQueueX.erase_initW

/-! ### x64 twin of WeakCore's MS queue (try-once dequeuer): `Lower/WcMsqX*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsqX.wcMsqX_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsqX.Concrete.wcMsqX_concrete

/-! ### Sequential `ProcSpec` to fragment spec, x64: `Lower/FragSpecProcX64.lean` -/

#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.ofProcSpec
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.ofProcSpec
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.ofProcSpecLe

/-! ### x64 twin of WeakCore's MS queue, semantic forms: `Lower/WcMsqXForms.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsqX.wcMsqX_promising_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsqX.wcMsqX_promising_semInf

/-! ### x64 value-restricted kit on the semantic machines: `Lower/KitX64ValsSem.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64_vals_sem
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64_vals_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_vals_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitX.lower_promising_x64_vals_semInf
/-- info: 'Kraken.Promising.Lower.KitX.lower_promising_x64_vals_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitX.lower_promising_x64_vals_semInf

/-! ### FlatHashMap portable `lookup`, sequential, x64: `Lower/FlatGroupMatchX64.lean`, `FlatLookupX64.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.groupMatchX_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.lookup_specX
/-- info: 'Kraken.Promising.Lower.Flat.lookup_specX' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Flat.lookup_specX
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.lookup_tbl1X
#guard_msgs (drop info) in #check @MachineWP.tzcnt_reg_spec

/-! ### Generic lemmas hoisted from the x64 MS queue (try-once protocol) -/

#guard_msgs (drop info) in #check @Safely.blockAtT
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.MsQueueX.stW_fence
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.MsQueueX.yokW_kept

/-! ### Generic x64 helpers: `SLR/EnvG/X64EnvRefine.lean`, `MachineWPALU.lean`, `WordLemmas.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.Safely.refine
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.relInvX
#guard_msgs (drop info) in #check @Kraken.Promising.X64.EnvG.Safely.relInvX_inv
#guard_msgs (drop info) in #check @MachineWP.triple_of_pointwise
#guard_msgs (drop info) in #check @MachineData.retAddr_congr
#guard_msgs (drop info) in #check @CondCode.z_interp_from_result
#guard_msgs (drop info) in #check @Mem.loadInt_isSome_storeInt
