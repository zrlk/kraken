/-
**wake.w on x86-64: main after its `clone`, to its `exit_group`** (the x64 twin of
`Spike/Lib/A64WakeMainPost.lean`): back from the
clone with the child's id (`Parent.pN … .ts`), main runs

    Parent.seg_parent            -- the tests, the frame left, `jmp wc_waitLoop`
    WaitLoop.seg_waitLoopP       -- the acquire-load loop, its park calls
    ret                          -- to `scc_rt_main`'s `.x2`, `%rax = 0`
    .Lscc_rt_main.x0: movq %rax, -16(%rbp); movq -16(%rbp), %rdi; movl $231, %eax; syscall

and does not come back: the `exit_group(0)` there is main's exit
(`hexit`). The whole path is one `SegL` (the load-or-stutter row of the
loop's `movq (%rcx), %rax`) to the empty fragment.

**The regions.** `seg_parent` is stated on main's region `R` (`wc_main`'s
frame, offset `0` its saved `%rbp`, the return address into `scc_rt_main`
at `8`; `WcClone.oW`); `wc_waitLoop` (`X64WaitLoop`) on a region whose
offset `0` is the return address's cell. The tail call `jmp wc_waitLoop`
hands over at `%rsp = R.addr 8`, so the loop runs on `R.fp 8` (the same
cells, based 8 bytes higher: `Region.fp`, `At.rebase`). `scc_rt_main`'s
`%rbp` is `40` above `wc_main`'s return address cell (its saved `%rbp`,
its frame of 32, the call's push): `fp = R.addr 48` (`hfp`), i.e.
`(R.fp 8).addr 40`, and its spill cell `-16(%rbp)` is at `R.fp 8`'s
offset `24` (`hhi : 40 ≤ R.hi`).

- `mainX2`: `scc_rt_main`'s return point; `wake_exitIn`: the `exit_group`
  tail there, its spill at `-16(%rbp)`.
- `At.withRsp`: a node's invariant with `%rsp` at its static offset.
- `pE_rebase`: the parent's exit `pE` on `R` is the loop's entry
  `WaitLoop.N … .e` on `R.fp 8` (`At.rebase`, `d = 8`).
- `seg_waitExit`: from the loop's return (`WaitLoop.E … .ret`, at `ra`) to
  nothing: `exitTail_seg_of`.
- `seg_mainPost`: from `pN .ts` to nothing.

What stays a hypothesis: the region's facts; the code checks (`hpin`,
`hwin`, `hxin`: `wake_parentIn`, `wake_waitIn`, `wake_exitIn` on
`SccCode.wakeCells`); the loop's and the park's facts (as in
`seg_waitLoopP`); the source's tail call (`hrun`); `scc_rt_main`'s `%rbp`
(`hfp`) and the return address `ra` at `.x2` (`hra`); and main's exit at
the `syscall` for every control past the load (`hexit`).
-/
import Spike.Lib.X64WakeParent
import Spike.Lib.X64WaitLoop
import Spike.Lib.X64AtRebase

namespace Spike.Lib.X64.WakePh.MainPost

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.WakePh.Parent (pN pE parentIn seg_parent)
open Spike.Lib.X64.WaitLoop (waitIn RdOne Past seg_waitLoopP)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Scc.Sem (ValRep)

/-- `scc_rt_main`'s return point after `call wc_main`. -/
abbrev mainX2 : Label := ".Lscc_rt_main.x0"

/-- **The `exit_group` tail at `scc_rt_main`'s return point** in wake's
cells, the value spilled at `-16(%rbp)`. -/
theorem wake_exitIn : exitIn SccCode.wakeCells mainX2 (-16) 4 4 5 = true := by decide +kernel

section Seg

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`%rsp` at its static offset**, added to a node's invariant (from the
pair's `Abs`). -/
theorem At.withRsp {R : Region} {F : MachineData → Prop} {n : ND} {s : State} {c : Ctl}
    (h : At exe endPc R F n s c) :
    At exe endPc R F ⟨n.pc, n.o, fun σ c => n.J σ c ∧ σ.regs.get64 .rsp = R.addr n.o.sp⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, hJ, hA.so .rsp _ (SO.get_rsp _)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The parent's exit is the loop's entry, re-based**: `pE` on main's
region `R` (`%rsp` at offset `8`, the return address there) is
`WaitLoop.N … .e` on `R.fp 8` (`%rsp` at offset `0`, the return address
there). `At.rebase` at `d = 8`: the base shifts from `wc_main`'s saved
`%rbp` cell (`R`'s offset `0`) up to its return address cell (`R`'s offset
`8`), where `jmp wc_waitLoop` hands the frame over. -/
theorem pE_rebase {R : Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A fp ra tp) s c) :
    At exe endPc (R.fp 8) F
      (WaitLoop.N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp ((R.fp 8).addr 0) .e) s c := by
  refine At.rebase (d := 8)
    (n := ⟨_, _, fun σ c => (pE (_root_.Executable.labels exe).label c0 A fp ra tp).J σ c ∧
      σ.regs.get64 .rsp = R.addr 8⟩)
    (n' := WaitLoop.N (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp ((R.fp 8).addr 0) .e)
    (by decide) rfl (fun r k hk => ?_) (fun σ c hJ => ?_) (At.withRsp h)
  · show SO.get ⟨8, []⟩ r = some (8 + k)
    change SO.get ⟨0, []⟩ r = some k at hk
    unfold SO.get at hk ⊢
    split at hk
    · cases hk; simp_all
    · simp [lk] at hk
  · obtain ⟨⟨rfl, hdi, hbp, h8, htp⟩, hsp⟩ := hJ
    refine ⟨rfl, hdi, hbp, by simpa [enter] using h8, ?_, htp⟩
    show σ.regs.rsp.toBitVec = (R.fp 8).addr 0
    rw [Region.fp_addr]; exact hsp

/-- **The loop's return does not come back**: at `ra = .x2` with
`%rax = 0` and `%rbp = fp` (`scc_rt_main`'s, at offset `40`: `hfp`),
`scc_rt_main`'s `exit_group` tail (`exitTail_seg_of`), the spill cell at
offset `24` in the region (`hhi`), main's exit at the `syscall` for the
control past the load (`hexit`). -/
theorem seg_waitExit (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hin : exitIn cells mainX2 (-16) 4 4 5 = true)
    {R : Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {sp : BitVec 64}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ 0) (hhi : 32 ≤ R.hi)
    (hK : ms.K = some Scc.Sem.X64.abi) (hfp : fp = R.addr 40)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hexit : ∀ s c, Past c0 x e ty Rd c →
      At exe endPc R F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (y : WaitLoop.PX) :
    Seg p lbl ms (At exe endPc R F (WaitLoop.E c0 x e ty Rd A fp ra tp sp y)) (fun _ _ => False) := by
  cases y
  refine (exitTail_seg_of (lo := 0) (hi := 32) hp hend hin
    (n := ⟨Int64.ofBitVec ra, ⟨8, [(.rbp, 40)]⟩, (WaitLoop.E c0 x e ty Rd A fp ra tp sp .ret).J⟩) hra rfl hK hF hR
    hlo hhi (by decide) fun s c σ0 hJ hAt => ?_).mono_pre
    fun s c h => WaitLoop.At.rbpOf h fun σ c hJ => by
      show σ.regs.rbp.toBitVec = _; rw [hJ.2.2.1, hfp]
  obtain ⟨hP, h0, -⟩ := hJ
  have hv : σ0.regs.rax.toNat = 0 := by
    show σ0.regs.rax.toBitVec.toNat = 0
    rw [h0]; rfl
  rw [hv]
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hx⟩ := hAt
  refine SysOk.exitGroup_main fun hab => hexit s c hP ⟨he, hn, hdc, ?_, σ, hA, hD, ?_⟩ hab
  · rw [hpc]; show Int64.ofBitVec ra + _ + _ + _ = _; rw [hra]; rfl
  · show σ.regs.rdi.toBitVec = 0#64
    rw [hx]; exact h0

/-- **main after its `clone` does not come back** (a `SegL` to the empty
fragment): `seg_parent` from `pN .ts` on main's region `R` to `pE`, the
hand-over to the loop's region `R.fp 8` (`pE_rebase`, `At.rebase` at
`d = 8`: the base shifts from `wc_main`'s saved `%rbp` cell to its return
address cell), `seg_waitLoopP` there, then `seg_waitExit`. -/
theorem seg_mainPost (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp)
    (hpin : parentIn cells = true) (hwin : waitIn cells = true) (hxin : exitIn cells mainX2 (-16) 4 4 5 = true)
    {R : Region} {F : MachineData → Prop} {cP : Ctl}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -80) (hhi : 40 ≤ R.hi)
    (hrun : LocalRun p cP c0)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    {c0' : Ctl} {rbp0' ra' tp' : BitVec 64} (hpcode : Park.Code c0' rbp0' ra' tp' exe endPc)
    (hpentry : (_root_.Executable.labels exe).label ".Lscc_rt_park.entry" =
      (_root_.Executable.labels exe).label "scc_rt_park" + 8)
    (hfp : fp = R.addr 48)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX2)
    (hexit : ∀ s c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX2 + 4 + 4 + 5, ⟨8, [(.rbp, 40)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0) :
    SegL p lbl ms (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (fun _ _ => False) := by
  have h1 : R.lo ≤ 8 := by omega
  have h2 : (8 : Int) < R.hi := by omega
  have hF' := FStable.fp hR h1 h2 hF
  have hR' := Region.fp_ok hR h1 h2
  have hlo' : (R.fp 8).lo ≤ -88 := by show R.lo - 8 ≤ -88; omega
  have hhi' : (8 : Int) ≤ (R.fp 8).hi := by show 8 ≤ R.hi - 8; omega
  have hfp' : fp = (R.fp 8).addr 40 := by rw [Region.fp_addr]; exact hfp
  exact ((seg_parent hp hend hpin hF hR (by omega) (by omega) hrun).toL.seq
    ((seg_waitLoopP hp hend hwin hF' hR' hlo' hhi' hlim hterm hev hval htag hdm hK hT hown hS htp4 hpcode
      hpentry).mono_pre fun _ _ h => pE_rebase h)).seq
    (SegL.exists_pre fun y =>
      (seg_waitExit hp hend hxin hF' hR' (by show R.lo - 8 ≤ 0; omega) (by show 32 ≤ R.hi - 8; omega) hK hfp'
        hra hexit y).toL)

end Seg

end Spike.Lib.X64.WakePh.MainPost

/-- info: 'Spike.Lib.X64.WakePh.MainPost.pE_rebase' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPost.pE_rebase

/-- info: 'Spike.Lib.X64.WakePh.MainPost.seg_waitExit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPost.seg_waitExit

/-- info: 'Spike.Lib.X64.WakePh.MainPost.seg_mainPost' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPost.seg_mainPost
