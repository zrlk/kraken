/-
**`hello.w` on x86-64: level 0's context and counter-add landing at the self words, closed**

The closed forms of `Spike/Test/HelloRootL0XInh.lean`'s two conditional results at the checked-in executable's
layout `Λe`, the root's table `i0 := X64.HelloImms.i0M Λe`, the Linux entry, `rd := fun _ => True`,
`ls := fun _ => 0`:

- `ctxU_OX_closed`: a run of the loaded program from the load reaches a configuration whose thread 0 is in
  `CtxU (CtxRdHg … OX)` at the frames `[FR]` (the root's level-0 context, `RootLit`'s `CR`);
- `landRdUg_OX_closed`: at the same state the counter add's row lands in `HLandRdUg … OX`'s antecedent
  (`HelloRootL0XInh.landRdUg_OX_inh` at the facts the context supplies).

The one hypothesis is the loader's parse `hparse` (`Parse`). The run, its state and its shared memory are exact:
283 instructions of thread 0 (`HelloRootL0XClosedC1` … `C8`), the shared memory the write chain `M233` (the
`lock xadd` at step 64, the header store at 103, the stack lock's `xchg`/load/store at 160–177, the pool's `xadd`
at 182, the take at 202, the TCB stores at 218–233) and the kernel state `X1` (the take's range held). The state
`s283` is `scc_rt_alloc`'s `lock xaddq %rax, (%rcx)` on the counter `scc_rt_heap_use` (`4225760`) for
`wc_rodata`'s buffer.

**How the context is derived** (not assumed): `hello_root_final` (the root's obligations at `layoutEX_e`) gives
the step-wise simulation `wake_stepSimR`, so every reachable configuration is related (`Rx`). At `s283`:
- `Post` (after the spawn) is excluded: its kernel relation (`X64HelloWriteK.KRH`) has slot 1 not dormant, and
  in `X1` it is dormant (no `clone` yet).
- So `Pre`, whose one-thread relation is `R1OH`, i.e. `RSAH`: `PostSAH` (after the exit) is excluded since `X1`
  has not exited; so `PreJAH` gives the thread in `I3 ar L0 ls0 inv0 inv1 inv2` (`ODataH.IH`).
- Each disjunct is a greatest fixed point inside a level (`GfpS`/`GfpSP`), so the state is in the level's
  `Wf`, whose clause `WrAt s ar.ctrLoc → Ctx s c fs` fires: `s283` writes the counter (`wrAt283`).
  - `inv0` (`inv0Hg`, inside `W0Hg`): `Ctx` is `CR = CtxU (CtxRdHg … OX)`, the result; its `GcRdH` fixes the
    frames to `[FR]`.
  - `inv1 l b n` (`inv1RU (inv1G …)`, inside `W1Rg`): `Ctx` is `CtxR1H l b n`, refuted at `s283`: its box-store
    disjunct (`StAt`) is a store, not the `rmw` at `s283`; its counter disjunct (`GcM1H`) returns to
    `.Lwc_main.x0`, while `s283`'s return-address slot (`%rbp + 8`, read through the node's `Abs` at `oI`) holds
    `.Lwc_rodata.x0`.
  - `inv2 …` (`inv2H`, inside `W2Ig`, i.e. `WakeWf.W1`): `Ctx` is empty (`False`).

**Cost**: this module imports `Spike.Lib.X64HelloRootFinal`, whose closure takes about 2 h to build from cold
(`LEAN_NUM_THREADS=1`); the run chunks take seconds each.

The names `s283`, `run283`, `M233`, … are the step and write indices of the reference run (283 steps, last
shared write at step 233); they hold at the current hello layout too.

**Regeneration**: the run chunks are generated (`Spike/Tools/fwdgen/`); the numerals here (`s283`'s address and
registers, the return-address slot `72039096` and its value `4203222`, the counter `4225760`, `.Lwc_main.x0`'s
address) are the reference run's and move with the layout.
-/
import Spike.Test.HelloRootL0XClosedC8
import Spike.Test.HelloRootL0XInh
import Spike.Lib.X64HelloRootFinal

namespace Spike.Test.HelloRootL0XClosed

open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Test.HelloLinkedX64 (Λe layoutEX_e linux_ok_e)
open Spike.Lib.Fwd
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (WrAt)

set_option maxRecDepth 100000

/-! ## The setting -/

set_option hygiene false in
/-- The placement at `Λe`. -/
local notation "HP" => layoutEX_e.hp

set_option hygiene false in
/-- The root's table. -/
local notation "I0" => Spike.Lib.X64.HelloImms.i0M Λe

set_option hygiene false in
local notation "Ly" => RuntimeLayout.ofPlaceWX HP (Spike.Lib.X64.HelloImms.immsH Λe I0)

set_option hygiene false in
/-- main's owned words before the spawn, both TCB self words included. -/
local notation "OX" => Spike.Lib.X64.HelloPh.ownGHXW (Ly) (Spike.Lib.X64.Rt.Reserve.ntA (Ly).lab)

set_option hygiene false in
/-- main's frame. -/
local notation "FR" => Spike.Lib.X64HelloRdCf.frH Spike.Lib.X64.HelloPh.C0S.c0S.env

set_option hygiene false in
/-- The root's reference memory side at `OX`. -/
local notation "REF" => Spike.Lib.X64.HelloPh.LandRU.refHg (asm := SccCode.helloAsm) HP I0 Entry.linux
  (fun _ => True) (fun _ => 0) (OX)

set_option hygiene false in
/-- The root's level-0 context at `OX` (`RootLit`'s `CR`). -/
local notation "CTX" => Spike.Lib.X64.HelloPh.RootUL.CtxU HP I0
  (Spike.Lib.X64.HelloPh.LandRU.CtxRdHg (asm := SccCode.helloAsm) HP I0 Entry.linux (fun _ => True) (fun _ => 0)
    (OX))

/-- A budget with the allocator's cells (`hello_root_final`'s `hB`, by `rfl`). -/
abbrev Bud : Budget := ⟨Scc.Cert.PlaceOK.allocCells, 2, 0⟩

/-! ## The run to the counter add -/

/-- The state before step 283: `scc_rt_alloc`'s counter add for `wc_rodata`'s buffer. -/
abbrev s283 : State := mk R283 F_100010 (stores B2 N280) 4198726

/-- **The run**: from the load, thread 0 runs alone to `s283`, the shared memory the write chain `M233`, the
kernel state `X1`. -/
theorem run283 (hparse : Parse) :
    ∃ d : T.M.Cfg, T.M.Run μ0 t0 [] d ∧ Solo d 0 s283 ∧ d.1.mem = M233 ∧ d.2 = X1 := by
  obtain ⟨s', d, hP, hr, hs, hm, hx, -⟩ :=
    (((((((c1 hparse).trans (c2 hparse)).trans (c3 hparse)).trans (c4 hparse)).trans (c5 hparse)).trans
      (c6 hparse)).trans ((c7 hparse).trans (c8 hparse))).run rfl solo0 t0_mem t0_ext
  subst hP
  exact ⟨d, hr, hs, hm, hx⟩

/-- **`s283`'s instruction**: `lock xaddq %rax, (%rcx)`, a locked read-modify-write of the counter word
`⟨4225760, 8⟩` (`%rcx = 4225760`, unmapped in private memory). -/
theorem exec283 : ∃ (k : Kraken.RmwKind) (op : Val → Option Val) (g : Val → State),
    isa.exec s283 = some (.rmw k false ⟨4225760#64, 8⟩ op fun v => .done (g v)) := by
  have he := exec_xadd (cellM 104 4198726 rfl rfl (by decide +kernel) R283 F_100010 (stores B2 N280))
    (a := 4225760#64) ((eaddr_reg_disp _ _ _ _).trans (by decide))
    ((loadInt_look_none (B := B2) (L := N280) (b := 4225760#64) (by decide) (by decide) (by decide)).trans
      ((copy_out (by decide) (by decide) (by decide)).trans
        ((loadInt_look_none (B := Ent) (L := Llast) (b := 4225760#64) (by decide) (by decide)
          (by decide)).trans (ent_none (by decide)))))
  rw [access_agrees (Spike.Lib.X64.agrees_of_decls (decls_mk _ _ _ _) _ 8)] at he
  exact ⟨_, _, _, he⟩

/-- **`s283` writes the counter word.** -/
theorem wrAt283 : WrAt s283 ⟨4225760#64, 8⟩ :=
  let ⟨_, _, _, he⟩ := exec283
  .inr ⟨_, _, _, he⟩

/-- `s283`'s return-address slot (`%rbp + 8`) holds `.Lwc_rodata.x0` (`4203222`). -/
theorem ra283 : Mem.loadInt (stores B2 N280) 72039096#64 8 = some ((4203222#64).toNat : Int) :=
  loadInt_look (by decide) (by decide) (by decide)

/-- `.Lwc_main.x0`, `wc_main`'s return from its box allocation. -/
theorem lab__Lwc_main_x0 :
    (_root_.Executable.labels st0.exe).label ".Lwc_main.x0" = Int64.ofNat 4203741 :=
  Scc.Cert.Rt.X64.label_threadAt_of_codeLabel habove (by decide +kernel)

/-- The arena's counter word is `scc_rt_heap_use`'s (`4225760`). -/
theorem ctrLoc_eq : (Spike.Lib.X64.WakeOD.arW HP (Spike.Lib.X64.HelloImms.immsH Λe I0)).ctrLoc =
    ⟨4225760#64, 8⟩ := by
  decide +kernel

/-- The load and the marks do not read the layout's immediates. -/
theorem load_imms (i : CoreTerm.Expr → String → Nat → Option Nat) :
    T.load SccCode.helloAsm { Λe with imms := i } = T.load SccCode.helloAsm Λe := rfl

theorem marks_imms (i : CoreTerm.Expr → String → Nat → Option Nat) :
    T.marks SccCode.helloAsm { Λe with imms := i } = μ0 := rfl

/-! ## The context at `s283` -/

/-- `Wf`'s counter clause. -/
theorem wf_ctr {Λ : Scc.Sem.Layout} {μ : Marks} {own : Spike.Lib.X64Consumer.Own} {ar : Spike.Lib.Arena}
    {p : CoreTerm.Prog} {Dt Ab Cl Ac : State → Prop} {Ctx : Spike.Lib.FragS isa} {lbl : Spike.Lib.X64Consumer.Lbl}
    {lsize : Spike.Lib.X64Consumer.Lsize} {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : Spike.Lib.X64.WakeWf.Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs) (hw : WrAt s ar.ctrLoc) :
    Ctx s c fs :=
  h.2.2.2.2.2.2.2.1 hw

/-- **The root's level-0 context at the run's state** (see the module doc for the derivation). -/
theorem reach283 (hparse : Parse) :
    ∃ d : T.M.Cfg, T.M.Run μ0 t0 [] d ∧ Solo d 0 s283 ∧ d.1.mem = M233 ∧ d.2 = X1 ∧
      ∃ c, CTX s283 c [FR] := by
  obtain ⟨d, hr, hs, hm, hx⟩ := run283 hparse
  refine ⟨d, hr, hs, hm, hx, ?_⟩
  have O := Spike.Lib.X64.HelloPh.RootFinal.hello_root_final layoutEX_e (arch := .tso) (B := Bud)
    (E := Entry.linux) (ls := fun _ => 0) hparse rfl linux_ok_e
  have h0 := (load_imms (Spike.Lib.X64.HelloImms.iRdM Λe)).trans (hload hparse)
  have hr' := (marks_imms (Spike.Lib.X64.HelloImms.iRdM Λe)).symm ▸ hr
  obtain ⟨src, -, -, hR⟩ := (Spike.Lib.X64WakeA64.wake_stepSimR O).reach h0 hr'
  have hWr : WrAt s283 (Spike.Lib.X64.WakeOD.arW HP (Spike.Lib.X64.HelloImms.immsH Λe I0)).ctrLoc :=
    ctrLoc_eq ▸ wrAt283
  rcases hR with ⟨d', u, hdu, -, -, -, hR1⟩ | ⟨hP, -⟩
  · obtain ⟨⟨hpre | hpost, -⟩, -⟩ := hR1
    · obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, -, -, -, -, -, -, -, -, hJ, -⟩ := hpre
      -- the related thread is the run's thread 0
      obtain ⟨t', ht', hst', -⟩ := hs.thread
      rw [hdu] at ht'
      simp only [Spike.Lib.TwoSlot.up, Spike.Lib.TwoSlot.upC, hth] at ht'
      have hth' : th = t' := Option.some.inj ht'
      subst hth'
      rw [hst'] at hJ
      rcases hJ with ⟨-, -, h0⟩ | ⟨l, b, n, -, -, -, -, h1⟩ | ⟨l, b, n, l', b', n', -, -, -, -, -, -, h2⟩
      · -- level 0: the context
        obtain ⟨inv, hS, hi⟩ := h0
        obtain ⟨-, -, hWf⟩ := (hS _ _ _ hi).1
        have hC := wf_ctr hWf hWr
        obtain ⟨ms0, R, F, q, -, hGc, -⟩ := hC.1.1
        rw [hGc.1] at hC
        exact ⟨_, hC⟩
      · -- level 1: `CtxR1H` is refuted at `s283`
        exfalso
        obtain ⟨⟨inv, hS, hi⟩, -⟩ := h1
        obtain ⟨-, -, hWf⟩ := (Spike.Lib.X64.HelloWf.w1Hg_def _ _ _ _ _ _).mp (hS _ _ _ hi).1.1
        rcases wf_ctr hWf hWr with
          ⟨⟨ms0, R, F, q, -, ⟨-, -, σC, m1, σ1, -, hR, -, hra⟩, -, hAt⟩, -⟩ |
            ⟨-, Lnd, -, kr, A, V, s', x, a, ty, e, w, wold, old, -, hex, -⟩
        · obtain ⟨hexe, -, -, -, σ, hA, -, ⟨-, ⟨hs0, -⟩, -⟩, -⟩ := hAt
          have hrbp : R.addr (-8) = 72039088#64 := by
            rw [← hA.so .rbp (-8) rfl, ← hA.regs]; rfl
          have h8 : R.addr 0 = 72039096#64 := by
            have := Spike.Lib.Region.addr_add8 R (-8)
            rw [hrbp] at this
            exact this.symm.trans (by decide)
          have hoff : R.Off 0 := by subst hR; exact ⟨rfl, by decide, by decide⟩
          obtain ⟨j, hj, hjv⟩ := hA.slot 0 hoff
          rw [h8] at hj
          change Mem.loadInt (stores B2 N280) 72039096#64 8 = some j at hj
          rw [ra283] at hj
          cases hj
          have hexe' : st0.exe = (Ly).exe := hexe
          have hra' : q.ra = ((_root_.Executable.labels st0.exe).label ".Lwc_main.x0").toBitVec := by
            rw [hexe']; exact hra
          rw [lab__Lwc_main_x0, ← hs0, ← hjv] at hra'
          exact absurd hra' (by decide)
        · obtain ⟨k, op, g, he⟩ := exec283
          rw [he] at hex
          simp at hex
      · -- level 2: the context is empty
        obtain ⟨inv, hS, hi⟩ := h2
        obtain ⟨-, hW2⟩ := (hS _ _ _ hi).1.1
        exact (wf_ctr hW2 hWr).elim
    · -- after the exit: `X1` has not exited
      exfalso
      obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, o, -, ⟨E', hk⟩, -⟩ := hpost
      have h1 : d'.2.exited = none := by
        have := congrArg Kernel.KState.exited hx
        rw [hdu] at this
        exact this
      rw [hk] at h1
      simp at h1
  · -- after the spawn: slot 1 is still dormant in `X1`
    exfalso
    obtain ⟨w, -, hK⟩ := hP
    have hd : d.2.slots[1]? = some .dormant := by rw [hx]; rfl
    exact hK.1.2.2.1 hd

/-! ## The closed results -/

/-- **Non-vacuity, closed: the root's level-0 context at `OX` is reached.** From the load of `helloAsm` at `Λe`,
a run of the target reaches a configuration with shared memory `M233` and kernel state `X1` whose thread 0 is at
`s283`, in `CtxU (CtxRdHg … OX)` at the frames `[FR]`. The one hypothesis is the loader's parse. -/
theorem ctxU_OX_closed (hparse : Parse) :
    ∃ (t0' : T.M.Cfg) (tr : List Ev) (t : T.M.Cfg) (s : State) (c : Spike.Lib.Ctl),
      T.load SccCode.helloAsm Λe = some t0' ∧ T.M.Run (T.marks SccCode.helloAsm Λe) t0' tr t ∧
      t.1.threads[0]?.map Thread.st = some s ∧ s = s283 ∧ t.1.mem = M233 ∧ t.2 = X1 ∧ CTX s c [FR] := by
  obtain ⟨d, hr, hs, hm, hx, c, hC⟩ := reach283 hparse
  obtain ⟨t', ht', hst', -⟩ := hs.thread
  exact ⟨t0, [], d, s283, c, hload hparse, hr, Option.map_eq_some_iff.mpr ⟨t', ht', hst'⟩, rfl, hm, hx, hC⟩

set_option hygiene false in
/-- `HLandRdUg … OX`'s antecedent at the frames `fs` (`HelloRootL0XInh`'s `ANT`). -/
local notation "ANT" => fun (fs : List TermRun.Frame) (s : State) (c : Spike.Lib.Ctl) =>
  ∃ (ms0 : Spike.Lib.MemSide isa) (R : Spike.Lib.Region) (F : MachineData → Prop) (q : Spike.Lib.X64.Alloc.Call),
    ms0 = { Spike.Lib.X64.HelloPh.LandRU.refHg (asm := SccCode.helloAsm) HP I0 Entry.linux (fun _ => True)
      (fun _ => 0) (OX) fs with xa := ms0.xa } ∧ Spike.Lib.X64.HelloPh.Land.GcRdH HP I0 fs ms0 R F q ∧
      Spike.Lib.X64.HelloPh.Land.CtrOkS ms0 (_root_.Executable.labels (Ly).exe).label R F q ∧
      Spike.Lib.X64.At (Ly).exe (Ly).endPc R F
        (Spike.Lib.X64.Alloc.N (_root_.Executable.labels (Ly).exe).label ms0 q .c2) s c ∧
      Spike.Lib.X64.KeepUn.U (Spike.Lib.X64.Rt.PreChild.r1Of (Ly).lab) s ∧
      Spike.Lib.X64.KeepTP.TP (Spike.Lib.X64.Flow.Ret0.tpOf (Spike.Lib.X64.WakePh.MainGlue.tcbS (Ly))) s

/-- **Non-vacuity, closed: the counter add's landing in `HLandRdUg … OX`'s antecedent.** At the same run and
state as `ctxU_OX_closed`, the counter add's row (`RootUL.ctrRow_ofFTU`) lands in states satisfying the
antecedent (`HelloRootL0XInh.landRdUg_OX_inh` at the facts `CtxU (CtxRdHg … OX)` supplies). -/
theorem landRdUg_OX_closed (hparse : Parse) :
    ∃ (t0' : T.M.Cfg) (tr : List Ev) (t : T.M.Cfg) (s : State) (c : Spike.Lib.Ctl),
      T.load SccCode.helloAsm Λe = some t0' ∧ T.M.Run (T.marks SccCode.helloAsm Λe) t0' tr t ∧
      t.1.threads[0]?.map Thread.st = some s ∧ s = s283 ∧ t.1.mem = M233 ∧ t.2 = X1 ∧
      Spike.Lib.X64ConsumerA.CtrRow (REF [FR])
        (fun s' c' => Spike.Lib.X64ConsumerA.PendA Spike.Lib.X64HelloSrc.helloSrc
          (fun _ _ s c fs => (ANT) fs s c)
          (Spike.Lib.X64WakeLoadT.L0T (Ly).Λ) (Spike.Lib.X64WakeLoadT.ls0T (fun _ => 0)) s' c' [FR]) s c := by
  obtain ⟨t0', tr, t, s, c, hl, hr, ht, hs, hm, hx, ⟨hC, htp⟩, hu⟩ := ctxU_OX_closed hparse
  have hpa := (Scc.Cert.Link.X64.parsed_of_parsesTo hparse).1
  exact ⟨t0', tr, t, s, c, hl, hr, ht, hs, hm, hx,
    Spike.Test.HelloRootL0XInh.landRdUg_OX_inh HP I0 Entry.linux (fun _ => True) (fun _ => 0) hpa hpa hC htp hu⟩

end Spike.Test.HelloRootL0XClosed

/-- info: 'Spike.Test.HelloRootL0XClosed.run283' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.run283

/-- info: 'Spike.Test.HelloRootL0XClosed.exec283' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.exec283

/-- info: 'Spike.Test.HelloRootL0XClosed.wrAt283' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.wrAt283

/-- info: 'Spike.Test.HelloRootL0XClosed.reach283' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.reach283

/-- info: 'Spike.Test.HelloRootL0XClosed.ctxU_OX_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.ctxU_OX_closed

/-- info: 'Spike.Test.HelloRootL0XClosed.landRdUg_OX_closed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Test.HelloRootL0XClosed.landRdUg_OX_closed
