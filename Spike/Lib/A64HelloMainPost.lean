/-
**hello.w on AArch64: main after its `clone`, to its `exit_group`** (main's rows after the spawn):
the twin of `Spike/Lib/A64WakeMainPost.lean` at hello.w's listing (`SccCode.helloProg`). Back from the clone with the
child's id (`Hello.Parent.pN … .cb`), main runs

    Hello.Parent.seg_parent      -- the tests, the frame of 144 left, `b wc_waitLoop`
    WaitLoop.seg_waitLoopP       -- the acquire-load loop (prefix `.L21_wc_waitLoop`), its park calls
    ret                          -- to `scc_rt_main`'s `.sp1`, `x0 = 0`
    .L1_scc_rt_main.sp1: str x0, [sp, #40]; ldr x0, [sp, #40]; movz x8, #94; svc #0

and does not come back: the `exit_group(0)` there is main's exit (`hexit`). Unlike wake's (`.sp0`, spill at `8`),
hello's `scc_rt_main` calls `wc_rodata` first, so `wc_main` returns to `.sp1` and the spill is at `40`: the ghost
regions reach `48` above their base (`hhi`), and `wc_main`'s frame of 144 below it (`hlo`, for `seg_parent`).

- `mainSp1`: `scc_rt_main`'s return point after `bl wc_main`; `hello_exitIn`: the `exit_group` tail there, its spill
  at `40`.
- `seg_waitExitH`: from the loop's return (`WaitLoop.E … .ret`, at `ra`) to nothing: `exitTail_seg_of`.
- `seg_mainPostH`: from `pN .cb` to nothing.

What stays a hypothesis, as in wake's: the regions' facts, the loop's and the park's code and labels
(`Hello.LoopCode.waitCode_hello`, `parkCode_hello`, `loopLabs_hello` discharge them), the source's tail call
(`hrun`), the thread-pointer load (`htls`), the return address `ra` at `.sp1` (`hra`), and main's exit at the `svc`
for every control past the load (`hexit`).
-/
import Spike.Lib.A64WakeMainPost
import Spike.Lib.A64HelloParent
import Spike.Lib.A64HelloLabels

namespace Spike.Lib.A64.Flow.Worker.Hello.MainPost

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (pN seg_parent)
open SccCode (helloProg)
open Scc.Sem (ValRep)

/-- `scc_rt_main`'s return point after `bl wc_main` (after `.sp0`'s call of `wc_rodata`). -/
abbrev mainSp1 : Label := ".L1_scc_rt_main.sp1"

/-- **The `exit_group` tail at `scc_rt_main`'s return point** in hello's program, the value spilled at `40`. -/
theorem hello_exitIn : exitIn helloProg mainSp1 40 = true := by decide +kernel

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A ra tp : BitVec 64}
  {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

/-- **The loop's return does not come back**: at `ra = .sp1` with `x0 = 0`, `scc_rt_main`'s `exit_group` tail
(`exitTail_seg_of`), the spill cell at offset `40` in the region (`hhi`), main's exit at the `svc` for the control
past the load (`hexit`). -/
theorem seg_waitExitH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {R : Spike.Lib.Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {x29 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 48 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1)
    (hexit : ∀ s c, WaitLoop.Past c0 x e ty Rd c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (x' : WaitLoop.PX) :
    Seg p lbl ms (At exe endPc R F (WaitLoop.E c0 x e ty Rd A x29 ra tp x')) (fun _ _ => False) := by
  cases x'
  refine exitTail_seg_of hp hend hello_exitIn hra hK hF hR hal (lo := 0) (hi := 48) hlo hhi rfl rfl
    fun s c σ0 hJ hAt => ?_
  obtain ⟨hP, h0, -⟩ := hJ
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
  have hv : σ0.regs.X0.toNat = 0 := by
    show σ0.regs.X0.toBitVec.toNat = 0
    rw [h0]; rfl
  rw [hv]
  refine SysOk.exitGroup_main fun hab => hexit s c hP ⟨he, hn, hdc, ?_, σ, hA, hD, ?_⟩ hab
  · rw [hpc]; show Int64.ofBitVec ra + 4 + 4 + 4 = _; rw [hra]
  · show σ.regs.X0.toBitVec = 0#64
    rw [hx]; exact h0

/-- **main after its `clone` does not come back** (a `SegL` to the empty fragment): `seg_parent` from `pN .cb` (in
the ghost region `Rg g0`, `x29` the ghost's `fp g0`) to the loop's entry, `seg_waitLoopP` at hello's prefix, then
`seg_waitExitH` at every ghost. -/
theorem seg_mainPostH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {cP : Ctl} (g0 : γ)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -144) (hhi : ∀ g, 48 ≤ (Rg g).hi)
    (hrun : LocalRun p cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hcode : ∀ g, WaitLoop.Code HelloLabels.pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra
      tp exe endPc)
    (hentry : (_root_.Executable.labels exe).label (HelloLabels.pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0) {c0' : Ctl} {x29' ra' tp' : BitVec 64}
    (hpcode : Park.Code c0' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hsp3 : (_root_.Executable.labels exe).label (HelloLabels.pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (HelloLabels.pfx ++ ".2_else2") + 4)
    (htls : ∀ g,
      SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (WaitLoop.N (_root_.Executable.labels exe).label HelloLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (WaitLoop.N (_root_.Executable.labels exe).label HelloLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1)
    (hexit : ∀ g s c, WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0) :
    SegL p lbl ms (At exe endPc (Rg g0) (Fg g0) (pN pfxM (_root_.Executable.labels exe).label cP A (fp g0) ra tp .cb))
      (fun _ _ => False) :=
  ((seg_parent hp hend (hF g0) (hR g0) (hal g0) (hlo g0) (by have := hhi g0; omega) hrun).toL.seq
    (WaitLoop.seg_waitLoopP hF hR hal (fun g => by have := hlo g; omega) (fun g => by have := hhi g; omega) hterm
      hev hval htag hdm hcode hentry hK hS htp4 hpcode hpentry hsp3 htls g0)).seq
    (SegL.exists_pre fun g => SegL.exists_pre fun x' =>
      (seg_waitExitH hp hend (hF g) (hR g) (hal g) (by have := hlo g; omega) (hhi g) hK hra (hexit g) x').toL)

end Seg

end Spike.Lib.A64.Flow.Worker.Hello.MainPost

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.MainPost.hello_exitIn' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.MainPost.hello_exitIn

/-- info: 'Spike.Lib.A64.Flow.Worker.Hello.MainPost.seg_mainPostH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.Flow.Worker.Hello.MainPost.seg_mainPostH
