/-
**`hello1.w`'s `scc_rt_main` up to the allocator's return at depth**
(x86-64): `hello1_main_pre_segW` (`Spike/Lib/X64Hello1Main.lean`) over
segments with frames (`SegWS`, `Spike/Lib/SegS.lean`), from a source that
has not yet entered the setup block. The x86-64 twin of
`Spike/Lib/A64Hello1SetupPre.lean`.

From the start before the setup block the source reaches `scc_rt_main`'s
entry at `let r = call rodata u in …` with no frame. `rodata`'s call is a
frame step (`FrameStep.call`): it pushes the frame returning into `r`. The
source takes it, with `rodata`'s first two local steps up to its buffer
allocation, as a pending frame run at the entry (`SegWS.pre_run`), so the
frameless segment holds at the pushed frame unchanged (`SegWS.liftS`): its
pairs are `hello1_main_pre_segW`'s, at the frames `fs1`, under the memory
side `ms fs1`.

- `hello1_main_pre_segWS`: from `scc_rt_main`'s entry (invariant `J`, no
  frame) to `wc_rodata`'s exits at `fs1`, given a frame run from each
  entry control to one of `J'` at `fs1` (`hrun`) and
  `hello1_main_pre_segW`'s premises at `J'` and `ms fs1`.
- `setupCall`, `setupFrame`: the call `let r = call rodata u in e` and the
  frame it pushes, returning into `r` and then `e` in the caller's
  environment `env` (source-side, restated here as the AArch64 modules are
  not imported next to the x86-64 ones).
- `setupCall_run`: from `setupCall e env` (with `u` the unit in `env`),
  `rodata` of `hello1Src` in `p`, a frame run to `rodata`'s buffer
  allocation (`rdCN`) under the pushed frame.

Where x86-64 differs from AArch64: `hello1_main_pre_segW`'s premises are
x86-64's (`%rsp`/`%fs` base in the limit words, `8 ≤ R.hi`, no alignment,
`mNC` naming the region).
-/
import Spike.Lib.X64Hello1Main
import Spike.Lib.Hello1RodataSrc
import Spike.Lib.SegS

namespace Spike.Lib.X64.Flow.Hello1

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Spike.Lib.X64.Flow.Ret0 (LimOk)
open Spike.Lib.X64.Alloc (Call Ea)
open Scc.Cert.Rt.X64 (Lays endOf)

section MainPreS

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`scc_rt_main` up to `wc_rodata`'s allocator's return at depth**: from
its entry with no frame (invariant `J`) to `wc_rodata`'s exits at the
frames `fs1`, when every entry control has a frame run to one of `J'` at
`fs1` (`hrun`: e.g. the setup block's call and its first local steps).
`hello1_main_pre_segW` at `J'` and `ms fs1` (its states inside `W` at
`fs1`, `hW`), lifted at `fs1` (`SegWS.liftS`), the run taken at the entry
(`SegWS.pre_run`, the entry's pairs inside `W` with no frame, `hWe`). -/
theorem hello1_main_pre_segWS {W : FragS isa} {K : State → State → Prop} {fs1 : List TermRun.Frame}
    (hp : Lays exe SccCode.hello1Cells) (hend : endPc = endOf exe SccCode.hello1Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -288) (hhi : 8 ≤ R.hi)
    {J J' : AS → Ctl → Prop}
    (hrun : ∀ σ c, J σ c → ∃ c', FrameRun p (c, []) (c', fs1) ∧ J' σ c')
    (hWe : ∀ s c, At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩ s c → W s c [])
    (hW : MainPreW (fun s c => W s c fs1) K exe endPc R F (ms fs1) J')
    (hlimM : ∀ σ c, J' σ c → LimOk (ms fs1) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - (64 : Int64).toBitVec))
    (hlimR : ∀ σ c, J' σ c → LimOk (ms fs1) F (σ.regs.fsBase.toBitVec + (8 : Int64).toBitVec)
      (σ.regs.rsp.toBitVec - 8#64 - 64#64 - 8#64 - 8#64 - (32 : Int64).toBitVec))
    (hq : ∀ σ c, J' σ c → ∃ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label ∧ q.c0 = c ∧
      q.h = 257#64 ∧ q.k = 2#64 ∧ q.u (ms fs1) = 3#64)
    (hmem : ∀ q : Call, q.OK (ms fs1) (_root_.Executable.labels exe).label → ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 (ms fs1).ctr ∨
        ∃ o, o + (ms fs1).units q.n q.τ ≤ (ms fs1).cells ∧ a.toNat = q.hdrAt (ms fs1) o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none)
    (hxa : ∀ m0 σC, ∀ q : AG (ms fs1) (_root_.Executable.labels exe).label, ∀ F' : MachineData → Prop,
      (∀ m, F' m → mF R F m0 σC m) →
      (∀ m, F' m → ∃ mC σ c, Abs (mR R) ⟨-48, []⟩ mC σ ∧
        (rN (_root_.Executable.labels exe).label (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label R J').J σC) .call).J σ c ∧
        (Alloc.N (_root_.Executable.labels exe).label (ms fs1) q.1 .e).J (enter (-48) σ) c ∧
        CKept (mR R) (-48) (-160) 8 mC m) →
      ∀ l b w s c, lbl l = none → At exe endPc (aR (mR R)) F' (Ea (ms fs1) q.1 l b w) s c →
        (ms fs1).xa l b w s c) :
    SegWS W K p lbl ms ((At exe endPc R F ⟨(_root_.Executable.labels exe).label "scc_rt_main", ⟨0, []⟩, J⟩).at [])
      (Frag.at (fun s c => ∃ m0 σC y, At exe endPc (mR R) (mF R F m0 σC)
        (rX (ms fs1) (_root_.Executable.labels exe).label lbl (mR R)
          (mRdJ0 (mNC (_root_.Executable.labels exe).label R J').J σC) y) s c) fs1) := by
  refine SegWS.pre_run (SegWS.liftS fs1
    (hello1_main_pre_segW hp hend hF hR hlo hhi hW hlimM hlimR hq hmem hxa) fun _ _ h => h) ?_
  rintro s c fs ⟨⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, rfl⟩
  obtain ⟨c', hr, hJ'⟩ := hrun σ c hJ
  exact ⟨hWe s c ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩, c', fs1, hr, ⟨he, hn, hdc, hpc, σ, hA, hD, hJ'⟩, rfl⟩

end MainPreS

/-! ## The setup block's call -/

open Spike.Lib.Hello1Src (hello1Src sliceTy)
open Spike.Lib.Hello1RodataSrc (rdC0 rdCN rdC0_run)

/-- **The setup block's call** `let r = call rodata u in e`. -/
def setupCall (e : Expr) : Expr := .let_ "r" (.call "rodata" [] (.var "u")) e

/-- **The frame `rodata`'s call pushes**: returning into `r` and then `e`
in the caller's environment `env`, at `rodata`'s return type. -/
def setupFrame (e : Expr) (env : TermRun.Env) : TermRun.Frame := ⟨"r", e, env, [], .iex sliceTy⟩

/-- **From the setup block's call to `rodata`'s allocation**: the call
(`FrameStep.call`, `u` the unit in `env`, `rodata` of `hello1Src` in `p`)
and `rodata`'s first two local steps (`rdC0_run`), under the pushed
frame. -/
theorem setupCall_run {p : Prog} {e : Expr} {env : TermRun.Env} {fs : List TermRun.Frame}
    (hd : p.find? (·.name == "rodata") = hello1Src[1]?)
    (hu : TermRun.evalAt env (.var "u") = some (.unit, [])) :
    FrameRun p (⟨setupCall e, env, none⟩, fs) (rdCN, setupFrame e env :: fs) :=
  .step (FrameStep.call (x := "r") (f := "rodata") (a := .var "u") (e := e) rfl hd hu)
    (FrameRun.ofLocal rdC0_run _)

end Spike.Lib.X64.Flow.Hello1
