/-
Re-export shim for the simulation prototype. The prototype has been
promoted to the simulation library `Kraken.Promising.SLR.Sim.*`
(`Sim.Rel`, `Sim.Event`, `Sim.Run`, `Sim.Instances`, namespace
`Kraken.Promising.Sim`); this file keeps every old public name
`Kraken.Promising.SimSpike.X` as an alias of `Kraken.Promising.Sim.X`, so code
written against the prototype still elaborates. New code should import the
library modules and use the `Sim` namespace directly.
-/
import Kraken.Promising.SLR.Sim.Instances

namespace Kraken.Promising

namespace SimSpike

export Kraken.Promising.Sim (
  AtomGap CtxRel CtxRel.fresh CtxRel.loadViews CtxRel.mem CtxRel.memExt CtxRel.mk CtxRel.prom
  CtxRel.rmwWrote CtxRel.stores CtxRel.succView CtxRel.views Ext Ext.refl Ext.trans FgnSep
  FgnSep.atom FgnSep.gap Foreign FwdLe GapFree GapFree.memExt IVLe IVLe.addrR IVLe.addrW IVLe.condW
  IVLe.dataPer IVLe.dataR IVLe.dataW IVLe.forStore IVLe.lift IVLe.mk IVLe.self_idUpTo MemRel
  MemRel.dom_le MemRel.f_le MemRel.get MemRel.init MemRel.mk NoForeign NoForeign.atom
  NoForeign.fgnSep NoForeign.gap PromRel PromRel.append PromRel.drop PromRel.erase PromRel.keep
  PromRel.lift PromRel.mem PromRel.nil PromRel.self_idUpTo Rel2 Rel2.append Rel2.cons
  Rel2.foldl_max Rel2.get? Rel2.getLastD Rel2.length_eq Rel2.nil SimInv SimInv.bnd SimInv.domAll
  SimInv.fence SimInv.fenceOpt SimInv.fgn SimInv.ivb SimInv.ivr SimInv.memExt SimInv.mk SimInv.nle
  SimInv.post SimInv.promDom SimInv.read SimInv.rel SimInv.write StaleFree TMap TMap.dom TMap.dom0
  TMap.extend TMap.f TMap.f0 TMap.f_inj TMap.f_le_iff TMap.f_lt_fv TMap.f_lt_iff TMap.fv
  TMap.fv_dom TMap.fv_floor TMap.fv_max TMap.fv_mono TMap.fv_zero TMap.idUpTo TMap.le_of_f_le_fv
  TMap.mk TMap.strict ThreadNP.toSF ThreadRel ThreadRel.lift ThreadRel.mk ThreadRel.prom
  ThreadRel.rsize ThreadRel.rv ThreadRel.setRegView ThreadRel.st ThreadRel.views ThreadRel.wsize
  ThreadRel.wv ThreadSF ThreadSF.refl ThreadSF.step TrRel ViewsLe ViewsLe.coh ViewsLe.fwd
  ViewsLe.mk ViewsLe.vCAP ViewsLe.vRel ViewsLe.vrNew ViewsLe.vrOld ViewsLe.vrOldNR ViewsLe.vwNew
  ViewsLe.vwOld ViewsLe.vwOldNT ViewsLe.xclb XclLe afterWrite_rel arr_le atomic_intro atomic_sim
  certOk_memExt fenceStep_sim finishInstr_sim freshMap freshMap_agree freshMap_fv freshMap_mem
  freshMap_new fv_le_last fv_lt_f get?_some_le get?_some_le' getElem!_set! getLastD_le
  instrViews_le' joinViews_le' read?_rel readPre_le readSuccs_memExt readSuccs_memExt_sim
  readSuccs_sim readView_le runTree_memExt runTree_sim runTree_sim_noForeign size_set!
  staleFree_bot stepOne_sim threadNP_env threadNP_memExt threadSF_sim writePre_le writeSuccs_break
  writeSuccs_sim zip_fold_le)

end SimSpike

end Kraken.Promising
