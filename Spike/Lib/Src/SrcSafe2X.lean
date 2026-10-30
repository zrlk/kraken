import Spike.Lib.Src.SrcSafe2
import Spike.Lib.Src.SrcSafe2P
import Spike.Lib.X64ConsumerS

/-!
**The source safety of an `Accepted2` program** (x64): `SrcSafeS` from the
starts before the setup block, with no hook or WeakCore's, for every frame invariant `I`
(`srcSafeS_of_accepted2X`); `hello1L.w`'s (`hello1o_srcSafeSX`).
-/

namespace Spike.Lib.LowerNode

open CoreLang CoreTerm A9NoSpawn TermRun Scc.Sem

/-- **The source safety of an `Accepted2` program** (x64), for every frame invariant. -/
theorem srcSafeS_of_accepted2X {P : SrcSem.SrcParams} {p : Prog} (hacc : Scc.Lower.Accepted2 p = true)
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    (hinit : ∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW)
    (I : X64ConsumerS.InvS) : X64ConsumerS.SrcSafeS P p I where
  cell := fun _ _ _ hr h0 _ _ _ _ _ _ _ _ _ _ _ ht _ _ =>
    (noAcq_cell (progNoS_acq_of_accepted2 hacc) hH (fun c hc => setupInit_noAcq (hinit c hc)) hr h0 ht).elim
  xchg := fun _ _ _ hr h0 _ _ _ _ _ _ _ _ _ _ hs => (reach_cfgB_accepted2 hacc hH hinit hr).1.xchg h0 hs
  box := fun _ _ hr => BoxCount.reach_boxLe hH (fun c hc => by
    obtain ⟨meW, rfl⟩ := hinit c hc; exact BoxCount.setupStart_boxLe _ meW) hr

/-- **`hello1L.w`'s source safety** (x64). -/
theorem hello1o_srcSafeSX {P : SrcSem.SrcParams}
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P Spike.Test.Hello1MainSrc.hello1o)
    (hinit : ∀ c, P.init c → ∃ meW, c = Scc.Sem.SrcSem.setupStart P.cap meW)
    (I : X64ConsumerS.InvS) : X64ConsumerS.SrcSafeS P Spike.Test.Hello1MainSrc.hello1o I :=
  srcSafeS_of_accepted2X hello1o_accepted2 hH hinit I

/-- **`SrcSafeS` from starts with the invariant and their boxes counted** (x64), for every frame
invariant. -/
theorem srcSafeS_of_initB_X {P : SrcSem.SrcParams} {p : Prog} (hacc : Scc.Lower.Accepted2 p = true)
    (hH : P.hooks = SrcSem.SrcHooks.none ∨ SrcOutProto.UsesWc P p)
    (hinit : ∀ c, P.init c → CfgB c ∧ CfgNoS AcqOp c) (hbox : ∀ c, P.init c → boxCount c ≤ allocCount c)
    (I : X64ConsumerS.InvS) : X64ConsumerS.SrcSafeS P p I where
  cell := fun _ _ _ hr h0 _ _ _ _ _ _ _ _ _ _ _ ht _ _ =>
    (noAcq_cell (progNoS_acq_of_accepted2 hacc) hH (fun c hc => (hinit c hc).2) hr h0 ht).elim
  xchg := fun _ _ _ hr h0 _ _ _ _ _ _ _ _ _ _ hs =>
    (reach_cfgB (blocksB_of_accepted2 hacc) (progNoS_acq_of_accepted2 hacc) hH hinit hr).1.xchg h0 hs
  box := fun _ _ hr => BoxCount.reach_boxLe hH hbox hr

/-- **The source safety of an `Accepted2` program at WeakCore's output
hooks** (x64), at every start, for every frame invariant. -/
theorem srcSafeS_srcP1oX {p : Prog} (hacc : Scc.Lower.Accepted2 p = true) (arch : WeakMem.Arch)
    (I : X64ConsumerS.InvS) : X64ConsumerS.SrcSafeS (SrcSem.srcP1o arch p) p I :=
  srcSafeS_of_initB_X hacc (.inr (usesWc_srcP1o arch p)) (fun _ hc => progInit_cfgB hacc hc)
    (fun _ hc => BoxCount.progInit_boxLe hc) I

/--
info: 'Spike.Lib.LowerNode.srcSafeS_srcP1oX' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms srcSafeS_srcP1oX

end Spike.Lib.LowerNode
