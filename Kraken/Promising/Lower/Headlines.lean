/-
**Machine-checked index of the AArch64 lowering headlines.**
Imported by nothing (built by the `Kraken.*` glob of the default
`lake build`). The guide is `Lower/README.md`; the table is the "Lowering" section of
`Examples/LockFree/THEOREMS.md`. The x64 headlines are in `Lower/HeadlinesX64.lean`: the
AArch64 and x64 semantics cannot be imported together (the fragment-spec rules even have the
same names, `MachineWP.FragSpecEnv.*`, on both ISAs).

Each name gets `#check @Name` (the name exists; the statement is dropped from the build output
by `#guard_msgs (drop info)`); the headlines also get `#print axioms Name` under `#guard_msgs`,
so a change in their axioms fails the build. All are `[propext, Classical.choice, Quot.sound]`.

Machines (conclusions hold at every reachable final configuration): `X_promising` and
`X_concrete` are on the executable machine `Reachable Arch.armv8 fuel` of `isa`; `X_lse2` on
the executable machine of `isaLSE2`, `X_lse2_sem` on `ReachableSem`, `X_lse2_semInf` on the
fuel-free `Live.Inf.ReachableSemInf` (all three of `isaLSE2`, read back through `ofL`).
Hypotheses: the pilots assume start states only, except the kept **conditional**
`Pilot2.pilot2_promising_of_envGValsBridge` and `Pilot2.pilot2_promising_concrete`
(`EnvGValsBridge (treiber2GA …)`, `Pilot2ValsReach`); their unconditional replacements are
`Pilot2.pilot2_promising` and `Pilot2.pilot2_promising_concrete'`. The kits are generic
(one `LowerThread`/`LowerThreadV` record per thread, `hfin`; `_vals` adds `MemInv G`).
Each `_viaKit` theorem is `rfl`-equal to its hand-assembled headline (checked in its file).
-/
import Kraken.Promising.Lower.KitLSE2
import Kraken.Promising.Lower.KitMsqLSE2
import Kraken.Promising.Lower.KitPilot2
import Kraken.Promising.Lower.AllocLSE2
import Kraken.Promising.Lower.Pilot2LSE2
import Kraken.Promising.Lower.PilotLSE2
import Kraken.Promising.Lower.MsqPilotLSE2
import Kraken.Promising.Lower.Pilot2Whole
import Kraken.Promising.Lower.FragSpecUniClients
import Kraken.Promising.Lower.FragSpecClients
import Kraken.Promising.Lower.FragSpecMsq
import Kraken.Promising.Lower.FragSpecLoopCallsDemo
import Kraken.Promising.Lower.LowerablePilots
import Kraken.Promising.Lower.MsqAllocWhole
import Kraken.Promising.Lower.PublishWhole
import Kraken.Promising.Lower.FragKitPublish
import Kraken.Promising.Lower.PublishForms
import Kraken.Promising.Lower.MsqAllocForms
import Kraken.Promising.Lower.FragKitPublish2
import Kraken.Promising.Lower.FlatLookup
import Kraken.Promising.Lower.FlatTake
import Kraken.Promising.Lower.FlatInsert
import Kraken.Promising.Lower.FlatWhole
import Kraken.Promising.Lower.FlatMixMain
import Kraken.Promising.Lower.WcEnqWhole
import Kraken.Promising.Lower.WcMsqForms
import Kraken.Promising.Lower.WcMsqBWhole
import Kraken.Promising.Lower.FlatGrow
import Kraken.Promising.Lower.KitVals
import Kraken.Promising.Lower.FlatMixWhole
import Kraken.Promising.Lower.FlatMixForms
import Kraken.Promising.Lower.KitValsLSE2
import Kraken.Promising.Lower.EventsA64Pair
import Kraken.Promising.EnvLSE2AArch64

/-! ### Kits (the lowering kit, `Kit.lean`, `KitLSE2.lean`) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_vals
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_vals' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_vals
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_lse2
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_lse2_semInf
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_lse2_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_vals_lse2
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_vals_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_vals_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_sem
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_semInf
/-- info: 'Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.lower_promising_vals_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.LowerThread.rule_noFault
/-- info: 'Kraken.Promising.Lower.Kit.LowerThread.rule_noFault' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.LowerThread.rule_noFault
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitPilot.treiber2DFinal_of_hB
/-- info: 'Kraken.Promising.Lower.KitPilot.treiber2DFinal_of_hB' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitPilot.treiber2DFinal_of_hB

/-! ### FEAT_LSE2 transfer (`LSE2Transfer.lean`, `LSE2Final.lean`) -/

#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.agreeLSE2
/-- info: 'Kraken.Promising.AArch64.agreeLSE2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.agreeLSE2
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.noLSE2Pairs_apply
/-- info: 'Kraken.Promising.AArch64.noLSE2Pairs_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.noLSE2Pairs_apply
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.reachableK_of_reachable_lse2
/-- info: 'Kraken.Promising.AArch64.reachableK_of_reachable_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.reachableK_of_reachable_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.final_lse2_of_K
/-- info: 'Kraken.Promising.AArch64.final_lse2_of_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.final_lse2_of_K
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.final_lse2_sem_of_K
/-- info: 'Kraken.Promising.AArch64.final_lse2_sem_of_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.final_lse2_sem_of_K
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.final_lse2_semInf_of_K
/-- info: 'Kraken.Promising.AArch64.final_lse2_semInf_of_K' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.final_lse2_semInf_of_K

/-! ### the first lowering pilot -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_promising
/-- info: 'Kraken.Promising.Lower.Pilot.pilot_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pilot_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_promising_concrete
/-- info: 'Kraken.Promising.Lower.Pilot.pilot_promising_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pilot_promising_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_promising_lse2
/-- info: 'Kraken.Promising.Lower.Pilot.pilot_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.Pilot.pilot_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_promising_lse2_semInf
/-- info: 'Kraken.Promising.Lower.Pilot.pilot_promising_lse2_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_promising_lse2_concrete
/-- info: 'Kraken.Promising.Lower.Pilot.pilot_promising_lse2_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pilot_promising_lse2_concrete

/-! ### the stack-frame pilot (conditional) and the unconditional stack-frame pilot (unconditional) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_of_envGValsBridge
/--
info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_of_envGValsBridge' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_of_envGValsBridge
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete
/-- info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising
/-- info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete'
/-- info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete'' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_concrete'
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2
/-- info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_semInf
/-- info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_concrete
/--
info: 'Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pilot2_promising_lse2_concrete

/-! ### the MS queue pilot -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.msqPilot_promising
/-- info: 'Kraken.Promising.Lower.MsqPilot.msqPilot_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.msqPilot_promising_concrete
/-- info: 'Kraken.Promising.Lower.MsqPilot.msqPilot_promising_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2
/-- info: 'Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_semInf
/--
info: 'Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_semInf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_concrete
/--
info: 'Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.msqPilot_promising_lse2_concrete

/-! ### the allocation pilot -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_promising
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_promising_concrete
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_promising_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_promising_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_promising_lse2
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_promising_lse2_semInf
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_promising_lse2_semInf' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_promising_lse2_concrete
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_promising_lse2_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_promising_lse2_concrete

/-! ### Kit instances (`_viaKit`, each `rfl`-equal to its hand-assembled headline) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitPilot.pilot_promising_viaKit
/-- info: 'Kraken.Promising.Lower.KitPilot.pilot_promising_viaKit' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitPilot.pilot_promising_viaKit
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitPilot.pilot_promising_lse2_viaKit
/-- info: 'Kraken.Promising.Lower.KitPilot.pilot_promising_lse2_viaKit' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitPilot.pilot_promising_lse2_viaKit
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitPilot2.pilot2_promising_viaKit
/-- info: 'Kraken.Promising.Lower.KitPilot2.pilot2_promising_viaKit' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitPilot2.pilot2_promising_viaKit
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitMsq.msqPilot_promising_viaKit
/-- info: 'Kraken.Promising.Lower.KitMsq.msqPilot_promising_viaKit' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.KitMsq.msqPilot_promising_viaKit
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitMsq.msqPilot_promising_lse2_viaKit
/--
info: 'Kraken.Promising.Lower.KitMsq.msqPilot_promising_lse2_viaKit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.KitMsq.msqPilot_promising_lse2_viaKit

/-! ### Value bridge (the value bridge) and its K-world clones -/

#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJ
/-- info: 'Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJ
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecs
/-- info: 'Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecs' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecs
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJK
/-- info: 'Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJK' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridgeJK
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecsK
/-- info: 'Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecsK' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.AArch64.EnvG.Vals.envGValsBridge_ofSpecsK
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.envGValsBridge_true
/-- info: 'Kraken.Promising.Lower.Pilot2.envGValsBridge_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.envGValsBridge_true

/-! ### Fragment-spec rules (`FragSpec*.lean`, AArch64) -/

#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_cfg
/-- info: 'MachineWP.FragSpecEnv.of_cfg' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.of_cfg
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_cfgRank
/-- info: 'MachineWP.FragSpecEnv.of_cfgRank' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.of_cfgRank
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_placed
/-- info: 'MachineWP.FragSpecEnv.of_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.of_placed
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.mono
/-- info: 'MachineWP.FragSpecEnv.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnv.mono
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.of_placed
/-- info: 'MachineWP.FragSpecEnvL.of_placed' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.of_placed
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.of_block
/-- info: 'MachineWP.FragSpecEnvL.of_block' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.of_block
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.call
/-- info: 'MachineWP.FragSpecEnvL.call' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.call
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.callr
/-- info: 'MachineWP.FragSpecEnvL.callr' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.callr
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.tail
/-- info: 'MachineWP.FragSpecEnvL.tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.tail
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.of_cfgP
/-- info: 'MachineWP.FragSpecEnvL.of_cfgP' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.FragSpecEnvL.of_cfgP
#guard_msgs (drop info) in #check @MachineWP.PartialWpEnvS.call_triples
/-- info: 'MachineWP.PartialWpEnvS.call_triples' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.PartialWpEnvS.call_triples
#guard_msgs (drop info) in #check @MachineWP.cfgEnv_partial_funS
/-- info: 'MachineWP.cfgEnv_partial_funS' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms MachineWP.cfgEnv_partial_funS
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Uni.FragSpecEnv.of_vals_top
/-- info: 'Kraken.Promising.Lower.Uni.FragSpecEnv.of_vals_top' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Uni.FragSpecEnv.of_vals_top

/-! ### Fragment-spec plumbing (AArch64; `#check` only) -/

#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.of_layout
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.at
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.sub
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.at_sub
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnv.toL
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.toFrag
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.at_sub
#guard_msgs (drop info) in #check @MachineWP.FragSpecEnvL.mono

/-! ### Fragment specs (AArch64) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pushFrag_spec
/-- info: 'Kraken.Promising.Lower.Pilot.pushFrag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.pushFrag_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.popFrag_spec
/-- info: 'Kraken.Promising.Lower.Pilot.popFrag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.popFrag_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Uni.pushFrag_specU
/-- info: 'Kraken.Promising.Lower.Uni.pushFrag_specU' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Uni.pushFrag_specU
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Uni.popFrag_specU
/-- info: 'Kraken.Promising.Lower.Uni.popFrag_specU' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Uni.popFrag_specU
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Uni.pushFrag_pureU
/-- info: 'Kraken.Promising.Lower.Uni.pushFrag_pureU' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Uni.pushFrag_pureU
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Uni.popFrag_pureU
/-- info: 'Kraken.Promising.Lower.Uni.popFrag_pureU' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Uni.popFrag_pureU
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.allocFrag_spec
/-- info: 'Kraken.Promising.Lower.Alloc.allocFrag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.allocFrag_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.enqFrag_spec
/-- info: 'Kraken.Promising.Lower.MsqPilot.enqFrag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.enqFrag_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.deqFrag_spec
/-- info: 'Kraken.Promising.Lower.MsqPilot.deqFrag_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.deqFrag_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Calls.pushw_spec
/-- info: 'Kraken.Promising.Lower.Calls.pushw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Calls.pushw_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.LoopCalls.popw_spec
/-- info: 'Kraken.Promising.Lower.LoopCalls.popw_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.LoopCalls.popw_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.LoopCalls.popw_spec_at
/-- info: 'Kraken.Promising.Lower.LoopCalls.popw_spec_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.LoopCalls.popw_spec_at

/-! ### Fragment specs (AArch64; `#check` only) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Calls.pusht_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Calls.pushi_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Calls.pushww_spec

/-! ### `_viaFrag` / `_viaUni` (per-program specs re-derived from fragment specs; sample) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.push_spec_viaFrag
/-- info: 'Kraken.Promising.Lower.Pilot.push_spec_viaFrag' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.push_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.alloc_spec_viaFrag
/-- info: 'Kraken.Promising.Lower.Alloc.alloc_spec_viaFrag' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Alloc.alloc_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.enq_spec_viaFrag
/-- info: 'Kraken.Promising.Lower.MsqPilot.enq_spec_viaFrag' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqPilot.enq_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.push_spec_viaUni
/-- info: 'Kraken.Promising.Lower.Pilot.push_spec_viaUni' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot.push_spec_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pop_spec2_viaUni
/-- info: 'Kraken.Promising.Lower.Pilot2.pop_spec2_viaUni' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Pilot2.pop_spec2_viaUni

/-! ### `_viaFrag` / `_viaUni` (the rest; `#check` only) -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pop_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.push_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pop_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.push_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.pop_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.push_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.pop_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.push_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pop_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.push_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pop_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.enq_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.deq_spec_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.deq_pure_viaFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pushFrag_spec_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.popFrag_spec_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pushFrag_pure_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.popFrag_pure_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pop_spec_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.push_pure_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pop_pure_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pushFrag_spec2_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.popFrag_spec2_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pushFrag_pure2_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.popFrag_pure2_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.push_spec2_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.push_pure2_viaUni
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pop_pure2_viaUni

/-! ### WeakCore-lowerable instruction forms (the lowerability check): `Lower/Lowerable.lean`, `Lower/LowerablePilots.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot.pilot_wcLowerable
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Pilot2.pilot2_wcLowerable
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.progE_wcLowerable
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.progD_wcLowerable
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Alloc.allocP_wcLowerable
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Calls.callsDemo_wcLowerable
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.LoopCalls.loopDemo_wcLowerable
#guard_msgs (drop info) in #check @Program.WCLowerable.lse2Free

/-! ### MS queue with bump-allocated nodes (the allocating MS queue pilot): `Lower/MsqAlloc*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising
/-- info: 'Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2
/-- info: 'Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqA_wcLowerable

/-! ### Treiber push with WeakCore's `publish` barrier, `dmb ishst` (the publish pilot): `Lower/Publish*.lean`, `Lower/FenceMono.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publish_promising
/-- info: 'Kraken.Promising.Lower.Publish.publish_promising' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Publish.publish_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publish_promising_lse2
/-- info: 'Kraken.Promising.Lower.Publish.publish_promising_lse2' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.pushp_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publishP_wcLowerable
#guard_msgs (drop info) in #check @Kraken.SharedEnv.FenceMono.ok_fence
#guard_msgs (drop info) in #check @Kraken.SharedEnv.FenceMono.le_of_fence_step

/-! ### Fragment-spec kit bridge (the fragment kit): `Lower/KitFrag.lean`, `FragKitMain.lean`, `FragKitPublish.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.partialTripleEnv_of_fragL
/-- info: 'Kraken.Promising.Lower.Kit.partialTripleEnv_of_fragL' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Kit.partialTripleEnv_of_fragL
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.LowerThread.ofFrag
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FragKit.main_fragL
/-- info: 'Kraken.Promising.Lower.FragKit.main_fragL' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.FragKit.main_fragL

/-! ### Semantic-machine and concrete forms of the publish pilot and the allocating MS queue pilot (the semantic-machine forms): `Lower/PublishForms.lean`, `Lower/MsqAllocForms.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publish_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.Publish.publish_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publish_promising_lse2_semInf
/--
info: 'Kraken.Promising.Lower.Publish.publish_promising_lse2_semInf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publish_promising_concrete
/-- info: 'Kraken.Promising.Lower.Publish.publish_promising_concrete' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.Publish.publish_promising_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Publish.publish_promising_lse2_concrete
/--
info: 'Kraken.Promising.Lower.Publish.publish_promising_lse2_concrete' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.Publish.publish_promising_lse2_concrete
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_sem
/-- info: 'Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_sem' depends on axioms: [propext, Classical.choice, Quot.sound] -/ #guard_msgs in #print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_semInf
/--
info: 'Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_semInf' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs in #print axioms Kraken.Promising.Lower.MsqAlloc.msqAlloc_promising_lse2_semInf

/-! ### relPure `main` spec once (the purity kit): `Lower/FragKitPure.lean`, `FragKitPublish2.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FragKit.main_pure_fragL
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FragKit.publish_promising_viaFragKit2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.FragKit.alloc_promising_viaFragKit2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Kit.LowerStatic.ofFragPure

/-! ### FlatHashMap portable `lookup`, sequential (the FlatHashMap `lookup` lowering): `Lower/FlatGroupMatch.lean`, `FlatLookup.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.groupMatch_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.lookup_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.lookup_tbl1

/-! ### FlatHashMap portable `take`, sequential (the FlatHashMap `take` lowering): `Lower/FlatTake.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Take.take_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Take.take_tbl1_hit
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Take.take_tbl1_miss

/-! ### FlatHashMap portable `insert` (no growth), sequential (the FlatHashMap `insert` lowering): `Lower/FlatInsert.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.insert_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.insert_tbl1_replace
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.insert_tbl1_fresh
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.lookup_tbl1Mem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.tbl1_inMem

/-! ### FlatHashMap `take` then `lookup` in one thread, on the Promising machine: `Lower/FlatWhole*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Whole.main_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Whole.flatWhole_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Whole.flatWhole_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Whole.flatWhole_tbl1

/-! ### MS queue `enq` with a private-memory frame; a FlatHashMap lookup feeding the queue (`main`'s fragment spec): `Lower/MsqPilotEnqFrame.lean`, `Lower/FlatMixMain.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.enqFrag_specF
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.enqFrag_spec_viaF
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.MsqPilot.enqFrag_pureF
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Mix.mixMain_fragL

/-! ### WeakCore's MS queue (`deq` without a head = tail check, plain-`ldr` `enq`), shapes A and B: `Lower/WcMsq*.lean`, `Lower/WcEnq*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wdeq_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcEnqFrag_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsq_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsq_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsqF_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsqF_promising_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsq_promising_lse2_sem
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsqF_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsqB_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.WcMsq.wcMsqB_promising_lse2_semInf

/-! ### FlatHashMap growth on caller-provided zeroed buffers (sequential, total): `Lower/FlatGrow.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Grow.grow_spec
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Grow.full1_hyps
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Grow.full1_grow

/-! ### The lowering kit over value-restricted environments, with purity under private data: `Lower/KitVals*.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.SLR.promisePure_of_relWritesV
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitVals.envGValsBridge_ofSpecsP
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitVals.final_of_relPureSafelyFVP
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitVals.lower_promising_valsW
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitVals.lower_promising_vals_viaW

/-! ### One-event 16-byte `CASP` under FEAT_LSE2: `Lower/EventsA64.lean`, `Lower/EventsA64Pair.lean`, `EnvLSE2AArch64.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.A64.exec_casp16
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.A64.instrSemInf_casp16
#guard_msgs (drop info) in #check @Kraken.Promising.AArch64.execLSE2_of_codeAt_casp

/-! ### FlatHashMap `lookup` feeding the MS queue, whole program: `Lower/FlatMixVals.lean`, `Lower/FlatMixWhole.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Mix.mixMain_fragG
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Mix.mixProg_promising
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Mix.mixProg_promising_tblD

/-! ### Value-restricted kit on FEAT_LSE2 and infinite runs; lookup-to-queue forms: `Lower/KitValsLSE2.lean`, `Lower/FlatMixForms.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitVals.lower_promising_valsW_lse2
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.KitVals.lower_promising_valsW_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Mix.mixProg_promising_lse2_semInf
#guard_msgs (drop info) in #check @Kraken.Promising.Lower.Flat.Mix.mixProg_promising_tblD_lse2_semInf

/-! ### Generic invariant-link lemmas (ISA-free): `LiveSemInf.lean`, `SLR/PromisePureVals.lean` -/

#guard_msgs (drop info) in #check @Kraken.Promising.configInv_reachableSemInf
#guard_msgs (drop info) in #check @Kraken.Promising.EvTree.AllInv.of_all_writes
