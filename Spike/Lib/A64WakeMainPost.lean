/-
**wake.w on AArch64: main after its `clone`, to its `exit_group`** (hello
plan 1.6, main's rows after the spawn): back from the clone
with the child's id (`Parent.pN … .cb`), main runs

    Parent.seg_parent            -- the tests, the frame left, `b wc_waitLoop`
    WaitLoop.seg_waitLoopP       -- the acquire-load loop, its park calls
    ret                          -- to `scc_rt_main`'s `.sp0`, `x0 = 0`
    .L1_scc_rt_main.sp0: str x0, [sp, #8]; ldr x0, [sp, #8]; movz x8, #94; svc #0

and does not come back: the `exit_group(0)` there is main's exit
(`hexit`). The whole path is one `SegL` (the load-or-stutter row of the
loop's `ldar`) to the empty fragment, so `WakeM0.closed_of_segL` gives
main's invariant `MSide.Mi`.

- `mainSp0`: `scc_rt_main`'s return point; `wake_exitIn`: the `exit_group`
  tail there, its spill at `8`.
- `seg_waitExit`: from the loop's return (`WaitLoop.E … .ret`, at `ra`) to
  nothing: `exitTail_seg_of`.
- `seg_mainPost`: from `pN .cb` to nothing.

What stays a hypothesis: the regions' facts (the ghost regions `Rg g` of
the loop hold its frame and the park's below (`-96`) and the spill cell of
`scc_rt_main` above (`16`)); the loop's and the park's code and labels (as
in `seg_waitLoopP`; `WakeLabels.hentry` etc. discharge the labels); the
source's tail call (`hrun`); the return address `ra` at `.sp0` (`hra`);
and main's exit at the `svc` for every control past the load (`hexit`).
-/
import Spike.Lib.A64WakeParent
import Spike.Lib.A64CodeSegs

namespace Spike.Lib.A64.Flow.Worker.Wake.MainPost

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (pN seg_parent)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Sem (ValRep)

/-- `scc_rt_main`'s return point after `bl wc_main`. -/
abbrev mainSp0 : Label := ".L1_scc_rt_main.sp0"

/-- **The `exit_group` tail at `scc_rt_main`'s return point** in wake's
program, the value spilled at `8`. -/
theorem wake_exitIn : exitIn wakeProg mainSp0 8 = true := by decide +kernel

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A ra tp : BitVec 64}
  {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

/-- **The loop's return does not come back**: at `ra = .sp0` with `x0 = 0`,
`scc_rt_main`'s `exit_group` tail (`exitTail_seg_of`), the spill cell at
offset `8` in the region (`hhi`), main's exit at the `svc` for the control
past the load (`hexit`). -/
theorem seg_waitExit (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {R : Spike.Lib.Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {x29 : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 16 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.A64.abi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hexit : ∀ s c, WaitLoop.Past c0 x e ty Rd c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (x' : WaitLoop.PX) :
    Seg p lbl ms (At exe endPc R F (WaitLoop.E c0 x e ty Rd A x29 ra tp x')) (fun _ _ => False) := by
  cases x'
  refine exitTail_seg_of hp hend wake_exitIn hra hK hF hR hal (lo := 0) (hi := 16) hlo hhi rfl rfl
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

/-- **main after its `clone` does not come back** (a `SegL` to the empty
fragment): `seg_parent` from `pN .cb` (in the ghost region `Rg g0`, `x29`
the ghost's `fp g0`) to the loop's entry, `seg_waitLoopP`, then
`seg_waitExit` at every ghost. -/
theorem seg_mainPost (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {cP : Ctl} (g0 : γ)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -96) (hhi : ∀ g, 16 ≤ (Rg g).hi)
    (hrun : LocalRun p cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hcode : ∀ g, WaitLoop.Code WakeLabels.pfx c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp
      exe endPc)
    (hentry : (_root_.Executable.labels exe).label (WakeLabels.pfx ++ ".0_entry") =
      (_root_.Executable.labels exe).label "wc_waitLoop" + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0) {c0' : Ctl} {x29' ra' tp' : BitVec 64}
    (hpcode : Park.Code c0' x29' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".L10_scc_rt_park.0_entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 4 + 4 + 4 + 4)
    (hsp3 : (_root_.Executable.labels exe).label (WakeLabels.pfx ++ ".sp3") =
      (_root_.Executable.labels exe).label (WakeLabels.pfx ++ ".2_else2") + 4)
    (htls : ∀ g,
      SegW (Spike.Lib.A64AbOffL.TlsW (_root_.Executable.labels exe).label A c0) (fun _ _ => False) p lbl ms (At exe endPc (Rg g) (Fg g)
          (WaitLoop.N (_root_.Executable.labels exe).label WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (WaitLoop.N (_root_.Executable.labels exe).label WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hexit : ∀ g s c, WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0) :
    SegL p lbl ms (At exe endPc (Rg g0) (Fg g0) (pN pfxM (_root_.Executable.labels exe).label cP A (fp g0) ra tp .cb))
      (fun _ _ => False) :=
  ((seg_parent hp hend (hF g0) (hR g0) (hal g0) (by have := hlo g0; omega) (by have := hhi g0; omega)
      hrun).toL.seq
    (WaitLoop.seg_waitLoopP hF hR hal hlo (fun g => by have := hhi g; omega) hterm hev hval htag hdm hcode hentry
      hK hS htp4 hpcode hpentry hsp3 htls g0)).seq
    (SegL.exists_pre fun g => SegL.exists_pre fun x' =>
      (seg_waitExit hp hend (hF g) (hR g) (hal g) (by have := hlo g; omega) (hhi g) hK hra (hexit g) x').toL)

end Seg

end Spike.Lib.A64.Flow.Worker.Wake.MainPost
