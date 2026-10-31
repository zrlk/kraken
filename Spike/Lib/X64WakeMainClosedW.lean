/-
**main's invariant after its `clone` inside `mainW`** (x86-64): the x64 twin of
`Spike/Lib/A64WakeMainClosedW.lean`, over
`W := X64WakeInst.mainW lab exe Λ lbl` (the `mainWR` conjuncts, `relW`,
`ctl`, `sys`, `flag`, come with the x64 `MainR`/`MainL`/`MainS`/`MainF`).
main's post-spawn path (`MainPost.seg_mainPost`) as a `SegLW`:

    seg_parentW                        -- `parentW_main`, on main's region `R`
    WaitLoop.seg_waitLoopW             -- `loopW_main`, on `R.fp 8`; the park call
      WaitLoop.seg_parkCallW           --   `parkGW_main`
    seg_waitExitW                      -- `exitW0_main`, `exitW1_main`, on `R.fp 8`

**The regions.** As in `MainPost.seg_mainPost`: the parent runs on main's
region `R` (`wc_main`'s frame, offset `0` its saved `%rbp`); `jmp
wc_waitLoop` hands over at `%rsp = R.addr 8`, so the loop, the park call and
the `exit_group` tail run on `R.fp 8`. The hand-over is
`MainPost.pE_rebase` (`At.rebase` at `d = 8`: the base shifts from
`wc_main`'s saved `%rbp` cell up to its return address cell) applied to the
loop's `SegLW` by `SegLW.mono_pre`; the `W` obligations of those segments
are stated on `R.fp 8`.

- `mainRuns`: the pcs of the path (the loop's, the park's, the parent's and
  the `exit_group` tail's runs); `wake_mainRuns_offA`: off the exits in
  wake's cells.
- `seg_mainPostW`: from `pN .ts` to nothing inside `mainW`.
- `main_closed_of_cloneW`: from main's `ClonePre` and a `SegLW W` from
  `pN .ts` to nothing, an invariant closed under the rows inside `W` holds
  at the parent (the body of `WakeInst.mainInv`; the x64 `mainInv` is not
  yet defined).
- `main_closed_wakeW`: the whole, at wake's cells.

What stays a hypothesis beyond `MainPost.seg_mainPost`'s: every state wide
(`hwide`) and the source facts placing `cv` (`cP` and `c0` read only `cv`,
bound to the flag's locative `w` with base `A`; past the load only `x` and
`cv`; neither at `wlRet`). The pcs off the exits are discharged at wake's
cells (`wake_mainRuns_offA`).
-/
import Spike.Lib.X64WakeMainSegW
import Spike.Lib.X64WakeRunsOffPark
import Spike.Lib.X64WakeSpawnAt
import Spike.Lib.X64WakeA64

namespace Spike.Lib.X64WakeMainClosedW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.WakePh (wake_parentIn)
open Spike.Lib.X64.WakePh.WcClone (oW)
open Spike.Lib.X64.WakePh.Parent (pN JS parent_at_preR)
open Spike.Lib.X64.WakePh.MainPost (mainX2 wake_exitIn pE_rebase)
open Spike.Lib.X64.WaitLoop (RdOne Past wake_waitIn seg_waitLoopW seg_parkCallW)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64WakePreA (ClonePre cloneAt)
open Spike.Lib.X64WakeOff (RunsOffA runsOffA_append)
open Spike.Lib.X64WakeInst (mainW)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64.WakeRunsOff (waitRuns parentRuns exitRuns wake_waitRuns_offA wake_parkRuns_offA
  wake_parentRuns_offA wake_exitRuns_offA)
open Spike.Lib.X64WakeMainW (loopW_main parkGW_main)
open Spike.Lib.X64WakeMainSegW (seg_parentW parentW_main seg_waitExitW exitW0_main exitW1_main)

/-- **main's post-spawn pcs**: the loop's, the park's, the parent's and the
`exit_group` tail's runs. -/
def mainRuns : List (String × Nat × Nat) :=
  waitRuns ++ Spike.Lib.X64.Flow.Park.parkRuns ++ parentRuns ++ exitRuns

/-- **main's post-spawn pcs are off the exits** in wake's cells. -/
theorem wake_mainRuns_offA {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.wakeCells kp) : RunsOffA (_root_.Executable.labels exe).label mainRuns :=
  runsOffA_append (runsOffA_append (runsOffA_append (wake_waitRuns_offA hp) (wake_parkRuns_offA hp))
    (wake_parentRuns_offA hp)) (wake_exitRuns_offA hp)

/-- **main's invariant after its `clone`, inside `W`**: from main's state at
the clone (`h`, its thread in `At` of the clone's node with `JS`: `hat`),
main's post-spawn region `R` (base `%rsp + 64`: `hRb`; offsets `[-80, 40)`,
`wc_main`'s frame with the 16 bytes below it and `scc_rt_main`'s frame
above: `hRlo`, `hRhi`), the kernel returning the child's id
`0 < r < pidMax`, and main's path from `pN .ts` to nothing inside `W` in a
frame condition `F` containing the parent's memory outside `R` (`hseg`,
`hF`), an invariant closed under the rows inside `W` holds at the parent
(`WakeInst.mainInv`'s body). -/
theorem main_closed_of_cloneW {W : Frag isa} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isa}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    {R : Region} {F F0 : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64)
    (hRlo : R.lo = -80) (hRhi : R.hi = 40) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hF : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hseg : SegLW W Spike.Lib.X64WakeT1.wakeSrc lbl ms
      (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)) (fun _ _ => False)) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧ ∃ inv : Frag isa,
      (∀ s c, inv s c → OutL Spike.Lib.X64WakeT1.wakeSrc lbl ms inv s c) ∧ (∀ s c, inv s c → W s c) ∧
      inv (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  obtain ⟨th', hth', hsp, hsz⟩ := h.spTop
  have hb := hRb th' hth'
  obtain ⟨th, hth, hAt⟩ := parent_at_preR hp hend h hat
    (by refine ⟨?_, ?_⟩ <;> omega) (by omega) hR htop hr0 hrm
  obtain ⟨inv, hP, hW, hi⟩ := hseg.closed
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  exact ⟨th, hth, inv, hi, hW, hP _ _ ⟨he, hn, hdc, hpc, σ, hA, hF th hth _ hD, hJ⟩⟩

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {Λ : Scc.Sem.Layout}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

/-- **main after its `clone` inside `mainW`** (`MainPost.seg_mainPost` as a
`SegLW` inside `mainW`): the parent's node obligations on `R`, the loop's,
the park's and the tail's on `R.fp 8` (the hand-over `pE_rebase`, `At.rebase`
at `d = 8`: the base shifts from `wc_main`'s saved `%rbp` cell up to its
return address cell). -/
theorem seg_mainPostW (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {R : Region} {F : MachineData → Prop} {cP : Ctl} {cv : String} {tyP tyv : Ty}
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
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv) :
    SegLW (mainW (_root_.Executable.labels exe).label exe Λ lbl) p lbl ms
      (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (fun _ _ => False) := by
  have h1 : R.lo ≤ 8 := by omega
  have h2 : (8 : Int) < R.hi := by omega
  have hF' := FStable.fp hR h1 h2 hF
  have hR' := Region.fp_ok hR h1 h2
  have hlo' : (R.fp 8).lo ≤ -88 := by show R.lo - 8 ≤ -88; omega
  have hhi' : (8 : Int) ≤ (R.fp 8).hi := by show 8 ≤ R.hi - 8; omega
  have hfp' : fp = (R.fp 8).addr 40 := by rw [Region.fp_addr]; exact hfp
  have h16 : R.Off (-16) := ⟨by decide, by omega, by omega⟩
  have h16' : (R.fp 8).Off (-16) := ⟨by decide, by show R.lo - 8 ≤ -16; omega, by show -16 + 8 ≤ R.hi - 8; omega⟩
  have h24' : (R.fp 8).Off (-24) := ⟨by decide, by show R.lo - 8 ≤ -24; omega, by show -24 + 8 ≤ R.hi - 8; omega⟩
  -- the parent on `R`, then the loop on `R.fp 8` (`pE_rebase`: `At.rebase` at `d = 8`), then the tail
  refine ((SegLW.ofSegW (seg_parentW hp hend wake_parentIn (c0 := c0) hF hR (by omega) (by omega) hrun
      (parentW_main (wake_parentRuns_offA hp) hwide h16 hcP hfvP hlP hloc))).seq
    ((seg_waitLoopW hp hend wake_waitIn hF' hR' hlo' hhi' hlim hterm hev hval htag hdm
      (loopW_main (wake_waitRuns_offA hp) hwide hlo' hhi' hc0 hE hfv0 hfvE hxc hl hloc)
      (seg_parkCallW hp wake_waitIn hF' hR' hlo' hhi' hK hT hown hS htp4 hpcode hpentry
        (parkGW_main (wake_parkRuns_offA hp) hwide hR' hlo' hhi' hc0 hfv0 hl hloc))).mono_pre
      fun _ _ h => pE_rebase h)).seq
    (SegLW.exists_pre fun y => ?_)
  cases y
  exact SegLW.ofSegW (seg_waitExitW hp hend wake_exitIn hF' hR' (by show R.lo - 8 ≤ 0; omega)
    (by show 32 ≤ R.hi - 8; omega) hK hfp' hra hexit
    (exitW0_main (wake_exitRuns_offA hp) hra hwide h16' h24' hE hfvE hxc hl hloc)
    (exitW1_main (wake_exitRuns_offA hp) hra hwide h16' h24' hE hfvE hxc hl hloc))

end Post

/-- **main's invariant after its `clone` in wake's cells, inside `mainW`**:
`main_closed_of_cloneW` with `seg_mainPostW` on main's region `R` and a
frame condition `F` stable on it containing the parent's memory outside `R`
(`hFR`): an invariant closed under the rows inside `mainW` holds at the
parent. -/
theorem main_closed_wakeW {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isa}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePre Λ r0 r1 X lbl t s)
    {R : Region} {F F0 : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt exe, oW, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 64)
    (hRlo : R.lo = -80) (hRhi : R.hi = 40) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hFR : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hF : FStable R F)
    {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    (hrun : LocalRun Spike.Lib.X64WakeT1.wakeSrc cP c0)
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
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s →
        MainExit Spike.Lib.X64WakeT1.wakeSrc ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    {cv : String} {tyP tyv : Ty}
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧ ∃ inv : Frag isa,
      (∀ s c, inv s c → OutL Spike.Lib.X64WakeT1.wakeSrc lbl ms inv s c) ∧
      (∀ s c, inv s c → mainW (_root_.Executable.labels exe).label exe Λ' lbl s c) ∧
      inv (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP :=
  main_closed_of_cloneW hp hend h hat hRb hRlo hRhi hR htop hr0 hrm hFR
    (seg_mainPostW (Λ := Λ') hp hend hF hR (by omega) (by omega) hrun hlim hterm hev hval htag hdm hK hT hown hS
      htp4 hpcode hpentry hfp hra hexit hwide hcP hfvP hlP hc0 hfv0 hl hloc hE hfvE hxc)

end Spike.Lib.X64WakeMainClosedW

/-- info: 'Spike.Lib.X64WakeMainClosedW.seg_mainPostW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainClosedW.seg_mainPostW

/-- info: 'Spike.Lib.X64WakeMainClosedW.main_closed_of_cloneW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainClosedW.main_closed_of_cloneW

/-- info: 'Spike.Lib.X64WakeMainClosedW.main_closed_wakeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainClosedW.main_closed_wakeW

/-- info: 'Spike.Lib.X64WakeMainClosedW.wake_mainRuns_offA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeMainClosedW.wake_mainRuns_offA
