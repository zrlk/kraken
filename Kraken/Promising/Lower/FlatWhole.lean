/-
A thread that calls the lowered FlatHashMap `take` and then `lookup`, proved
on the executable Promising machine (`Reachable Arch.armv8`) through the
AArch64 lowering kit (`Kit.lower_promising`). ISA: AArch64 (`isa`).

One thread runs `flatWhole` (`FlatWholeProg.lean`): `main` takes key `k` out
of a table held in the thread's private `dmem`, keeps the result in
`x25`/`x26`, then looks `k` up again. The kit's two fragment specs (the
`main` triple in `counted (EnvGCAdjA …)` and the purity triple in
`counted (relPure …)`) are both `main_spec`, lifted by
`FragSpecEnvL.ofProcSpec`: the sequential spec already proves that every
access is a mapped `dmem` access, so the shared environments are never
consulted. The ghost is `initGhost (fun _ => Pred.emp) [] []` and every
thread resource is `Res.unit`: there is no shared location.

* `flatWhole_promising`: every final configuration reachable from a start in
  `StartW` has thread `0` with `take`'s model answer in `x25`/`x26`
  (`TakeRes`), `lookup`'s model answer on the table `take` left in `x0`/`x1`
  (`ResRegs`), and that table in `dmem`.
* `flatWhole_promising_lse2_semInf`: the same on `isaLSE2`, fuel-free
  semantic machine (the text has no LSE2 pair).
* `flatWhole_tbl1`: at `tbl1`, `take 5` then `lookup 5`: `x25 = 1`,
  `x26 = 55` (the hit) and `x0 = 0` (the miss).
-/
import Kraken.Promising.Lower.FlatWholeProg
import Kraken.Promising.Lower.FragKitPure
import Kraken.Promising.Lower.KitFrag
import Kraken.Promising.Lower.KitLSE2
import Kraken.Promising.SLR.InitGhost

namespace Kraken.Promising.Lower.Flat.Whole

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.AArch64.EnvG
open Kraken.Promising.SLR Kraken.Promising.SLR.EnvG Kraken.Promising.Lower.Kit
open Kraken.Promising.Lower.Flat Kraken.Promising.Lower.Flat.Take MachineWP

/-! ## The thread -/

/-- The ghost: no release predicate, no acquire predicate. -/
abbrev wGhost : Ghost := initGhost (fun _ => Pred.emp) [] []

/-- The final reading of thread `0`'s registers and `dmem`. -/
def FinalRegs (x : WX) (s : MachineData) : Prop :=
  TakeRes x.r1 s ∧ (∃ r, lookupN x.T1 x.k = some r ∧ ResRegs r s) ∧ x.T1.InMem s.dmem

/-- The shared postcondition: thread `0` exists and reads `FinalRegs`. -/
def WB (x : WX) (c : Config isa) (_ : Res) (_ : Ghost) : Prop :=
  ∃ t, c.threads[0]? = some t ∧ FinalRegs x t.st.st.1

set_option maxRecDepth 8000 in
/-- No step from the end of the text (the trailing label `done`). -/
theorem flatWhole_stuck [layout : _root_.Layout] [Executable.ValidLayout (layout flatWhole)] (env : SharedEnv) :
    ∀ x R, x.1.2 = (layout flatWhole).addrOf flatWhole.length → ¬ (layout flatWhole).instrStepEnv env x R :=
  not_instrStepEnv_of_end_labels env 1

/-- The static fields at layout `l` (empty plan: no shared access). -/
noncomputable def flatS (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] (x : WX) :
    LowerStatic Arch.armv8 0 (WB x) where
  l := l
  p := flatWhole
  valid := inferInstance
  pl := ⟨[]⟩
  hpl := Plan.valid_nil
  live := flatWhole_rmwLive (layout := l)
  shape := flatWhole_phase1F (layout := l)
  stuck := flatWhole_stuck (layout := l)
  Q s _ := FinalRegs x s
  hB := by
    rintro c t r g cl σ hpost - hrel -
    obtain ⟨-, -, hQ⟩ := hpost.resolve_right id
    exact ⟨t, hrel.ht, hQ⟩

/-- `main`'s spec as a fragment spec in `env`, over the three fragments. -/
theorem main_fragL (env : SharedEnv) (hI : env.FenceInv (fun _ => True)) (x : WX) :
    FragSpecEnvL env [mainFrag, flatTake, flatLookup] "main" (fun ra t _ => MainPre x ra t)
      (fun ra t _ t' _ => MainPost x ra t t') :=
  FragSpecEnvL.ofProcSpec (fun hpl => main_spec (hpl _ (by simp)) (hpl _ (by simp)) (hpl _ (by simp))) env hI x

/-- **`flatWhole` as a lowered thread**: `main` and `pure` both from
`main_spec`. -/
noncomputable def flatT (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] (x : WX) :
    LowerThread Arch.armv8 0 wGhost.rel (WB x) :=
  LowerThread.ofFrag
    ((flatS l x).ofFragPure _ (main_fragL _ (fenceInv_true_relPure _ _) x) flatWhole_wf rfl flatWhole_ne
      flatWhole_hs (fun s _ => MainPre x ((l flatWhole).addrOf flatWhole.length) s) (fun _ _ => True)
      (fun _ _ h => h) (fun _ _ _ _ _ _ => trivial))
    (main_fragL _ (fenceInv_true_of_mono _) x) flatWhole_wf rfl flatWhole_ne flatWhole_hs
    (fun s _ => MainPre x ((l flatWhole).addrOf flatWhole.length) s) (fun _ _ h => h)
    (fun _ _ _ _ _ h => ⟨h.1, h.2.1, h.2.2.1⟩)

/-- **The start**: `flatWhole`'s code at layout `l`, no declarations, at the
start of the text returning to its end, with `main`'s precondition for that
return address. -/
structure StartW (l : _root_.Layout) (x : WX) (s : isa.State) : Prop where
  exe : s.exe = l flatWhole
  decls : s.decls = {}
  endPc : s.endPc = (l flatWhole).addrOf flatWhole.length
  pc : s.st.2 = (l flatWhole).addrOf 0
  pre : MainPre x ((l flatWhole).addrOf flatWhole.length) s.st.1

theorem flatT_start (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] {x : WX} {s : isa.State}
    (hS : StartW l x s) (σ : EStateA) : (flatT l x).Start σ s :=
  ⟨⟨hS.exe, hS.decls, hS.endPc, hS.pc, 0, hS.pre⟩, 0, hS.pre⟩

/-- **Initial erasure**: unit resources, the empty ghost. -/
theorem erase_w {s : isa.State} {initMem : List (Loc × Val)} :
    Erase (fun _ => Res.unit) wGhost (fun _ => False) (Config.init [s] initMem) := by
  have ht : total (fun _ => Res.unit) wGhost (Config.init [s] initMem) = Res.unit := by
    simp [total, Config.init_size, threadsRes, Ghost.slotsRes, wGhost, initGhost, Res.op_unit]
  refine erase_initGhost _ List.nodup_nil (by rw [ht]; exact Res.valid_unit)
    (fun x ι h => by rw [ht] at h; simp [Res.unit] at h) (fun x v m V r h => h)
    (fun x hpos p => by rw [ht] at hpos; simp [Res.unit, Perm.unit] at hpos)
    (fun x _ => Pred.emp_pure _) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)

/-! ## The whole program -/

/-- The one-thread family. -/
noncomputable abbrev flatTs (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] (x : WX) {s : isa.State} :
    ∀ tid, tid < [s].length → LowerThread Arch.armv8 tid wGhost.rel (WB x) :=
  fun tid h => match tid, h with
    | 0, _ => flatT l x
    | _ + 1, h => absurd h (by simp)

theorem flatTs_start (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] {x : WX} {s : isa.State}
    {initMem : List (Loc × Val)} (hS : StartW l x s) :
    ∀ tid (h : tid < [s].length), (flatTs l x tid h).Start
      (σInit (Config.init [s] initMem) Res.unit wGhost) [s][tid] := by
  intro tid h
  rcases tid with _ | _
  · exact flatT_start l hS _
  · simp at h

theorem flatWhole_final {x : WX} {n : Nat} {c : Config isa} (hf : c.final = true) {rF' : Nat → Res}
    {g' : Ghost} (hsz : c.threads.size = n + 1) (hB : ∀ tid, c.Done tid → WB x c (rF' tid) g') :
    WB x c (rF' 0) g' :=
  hB 0 (Config.final_done hf (by rw [hsz]; omega))

/-- **Take then lookup, on the Promising machine**: every final
configuration reachable under `Arch.armv8` from a start in `StartW` has
thread `0` with `take`'s model answer in `x25`/`x26`, `lookup`'s model
answer on the table `take` left in `x0`/`x1`, and that table in `dmem`. -/
theorem flatWhole_promising {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] (x : WX)
    {s : isa.State} {initMem : List (Loc × Val)} (hS : StartW l x s) {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [s] initMem) c) (hf : c.final = true) :
    WB x c Res.unit wGhost :=
  lower_promising (rF := fun _ => Res.unit) (Φ := fun c => WB x c Res.unit wGhost) Arch.armv8 fuel
    (fun _ hc' => Config.ntFree_armv8 hc') erase_w rfl (flatTs l x) (flatTs_start l hS) hc hf
    (fun _ _ _ _ hsz hB => flatWhole_final hf hsz hB)

set_option maxRecDepth 8000 in
/-- `flatWhole` has no LSE2 pair. -/
theorem flatWhole_lse2Free : ∀ d ∈ flatWhole, d.LSE2Free := by decide

/-- **`flatWhole_promising` on `isaLSE2`**, fuel-free semantic machine
(`ReachableSemInf`); the conclusion read through `ofL`. -/
theorem flatWhole_promising_lse2_semInf (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)] (x : WX)
    {s : isa.State} {initMem : List (Loc × Val)} (hS : StartW l x s) {cfg : Config isaLSE2}
    (hc : Live.Inf.ReachableSemInf Arch.armv8 (Config.init [s] initMem : Config isaLSE2) cfg)
    (hf : cfg.final = true) : WB x (ofL cfg) Res.unit wGhost :=
  lower_promising_lse2_semInf (rF := fun _ => Res.unit) (Φ := fun c => WB x c Res.unit wGhost) Arch.armv8
    (fun _ hc' => Config.ntFree_armv8K hc') erase_w rfl (flatTs l x) (flatTs_start l hS)
    (fun tid h => match tid, h with | 0, _ => flatWhole_lse2Free | _ + 1, h => absurd h (by simp))
    (fun _ hf' _ _ _ _ hsz hB => flatWhole_final hf' hsz hB) hc hf

/-! ## Non-vacuity: `tbl1`, take `5`, then lookup `5` -/

/-- `take 5` on `tbl1` hits raw slot `2`. -/
theorem tbl1_rf5 : Rf tbl1 5 = some (some 2) := by decide +kernel

/-- The logical variable: `tbl1`, key `5`, `gl = 3`, `n = 1`, and `take`'s
answer at the hit (raw slot `2`). -/
def w1 : WX :=
  ⟨tbl1, 5, 3, 1, (takeHitN tbl1 3 1 2).1, (takeHitN tbl1 3 1 2).2.1, (takeHitN tbl1 3 1 2).2.2.1,
    (takeHitN tbl1 3 1 2).2.2.2⟩

theorem w1_take : takeN tbl1 3 1 5 = some (w1.T1, w1.gl1, w1.n1, w1.r1) := by
  rw [takeN_hit tbl1_rf5]; rfl

theorem w1_r1 : w1.r1 = some 55 := by decide +kernel

theorem w1_lookup : lookupN w1.T1 5 = some none := by decide +kernel

theorem w1_bounded : w1.T1.Bounded 5 :=
  ⟨by decide +kernel, by decide +kernel, fun s => tbl1_bounded.key s,
   fun s => by
     show (if s = bandN 2 tbl1.cv then 0 else tbl1.val s) < W64
     split
     · decide
     · exact tbl1_bounded.val s,
   fun g => by
     show (if g = _ then _ else tbl1.ctrl g) < W64
     split
     · decide +kernel
     · exact tbl1_bounded.ctrl g,
   by decide⟩

theorem w1_probeEnds : ProbeEnds w1.T1 5 := by
  show (lookupN w1.T1 5).isSome = true
  rw [w1_lookup]; rfl

/-- **Non-vacuity**: started at `tbl1` with key `5`, `gl = 3`, `n = 1`
(arguments in `x0`–`x4`, `x10`, `x11`, the return address the end of the
text, `tbl1` in `dmem`), every final configuration has thread `0` with
`x25 = 1`, `x26 = 55` (`take 5` hit, value `55`) and `x0 = 0` (`lookup 5`
then misses). -/
theorem flatWhole_tbl1 {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l flatWhole)]
    {s : isa.State} {initMem : List (Loc × Val)} (he : s.exe = l flatWhole) (hd : s.decls = {})
    (hend : s.endPc = (l flatWhole).addrOf flatWhole.length) (hpc : s.st.2 = (l flatWhole).addrOf 0)
    (ha : Args tbl1 5 ((l flatWhole).addrOf flatWhole.length) s.st.1)
    (h10 : rv s.st.1.regs.X10.toBitVec = 3) (h11 : rv s.st.1.regs.X11.toBitVec = 1)
    (hm : tbl1.InMem s.st.1.dmem) {c : Config isa}
    (hc : Reachable Arch.armv8 fuel (Config.init [s] initMem) c) (hf : c.final = true) :
    ∃ t, c.threads[0]? = some t ∧ t.st.st.1.regs.X25 = 1 ∧ t.st.st.1.regs.X26.toNat = 55
      ∧ t.st.st.1.regs.X0 = 0 := by
  obtain ⟨t, ht, hT, ⟨r, hr, hres⟩, -⟩ := flatWhole_promising l w1 (initMem := initMem)
    ⟨he, hd, hend, hpc, takePre_of ha h10 h11 hm tbl1_hyps5, w1_take, w1_bounded, w1_probeEnds⟩ hc hf
  rw [show w1.k = 5 from rfl, w1_lookup] at hr
  cases hr
  rw [w1_r1] at hT
  exact ⟨t, ht, hT.1, hT.2, hres⟩

end Kraken.Promising.Lower.Flat.Whole
