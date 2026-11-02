/-
**hello's main after its `clone`: the invariant inside `mainWRH`** (x86-64; the twin of
`Spike/Lib/A64HelloMainClosedW.lean`, at hello.w's listing `SccCode.helloCells`): back from the clone at
`Hello.Parent.pN … .ts` (`Hello.Parent.parent_at_preH`, main's region based 128 above `%rsp`), main's path to
its `exit_group` is one `SegLW` to nothing inside `X64HelloMainInv.mainWRH` (hello's parent, frame 128;
`wc_waitLoop` with the park's return at `.Lwc_waitLoop.x20` and `scc_rt_park`; the exit tail at `.x3`), so
main's invariant `X64HelloMainInv.mainInvP p … (mainWRH …)` holds at the parent.

- `mainRunsH`: the pcs of the path (the loop's, the park's, the parent's and the exit tail's runs);
  `mainRunsH_off`: off every abort exit and the transfer sites in any layout of `helloCells`.
- `main_closed_of_cloneWH`: from `ClonePreH` and a `SegLW W` from `pN .ts`, `mainInvP p lbl ms W` at the
  parent.
- `pE_rebaseH`: the parent's exit on main's region is the loop's entry `NX waitXL … .e` on `R.fp 8`.
- `seg_mainPostWH`: hello's post-spawn path as a `SegLW` inside `mainWRH`.
- `main_closed_helloW`: the whole, at hello's code and labels (the loop's and the park's code, their labels
  and the flag check decided on `helloCells`).

## Differences from the AArch64 version

- One region `R` (offsets `[-128, 40)`), the loop and the exit tail on `R.fp 8`, as in x86-64 wake's
  `X64WakeInst.seg_mainPostWR`: no ghost family `Rg`/`Fg`/`fp`, no alignment premise and no `htls` premise
  (the x86-64 limit load is inside `X64WaitLoopWX.seg_waitLoopWX`, premise `hlim`). The parent's exit `pE` is
  re-based onto the loop's entry by `pE_rebaseH` (x86-64 wake's `X64WakeMainPost.pE_rebase` at `NX waitXL`).
- The park's thread pointer facts `tp ≠ A`, `tp + 8 ≠ A` (x86-64 only: the park reads `%fs:0`, the prologue
  `%fs:8`) come from `hT`/`hlim` under `X64WakeInst.RtOff` (`hms`); the park's ownership premises `hT`,
  `hown` are x86-64 wake's.
- The parent is at `pN .ts` (x86-64's node after the `syscall`), not `.cb`.
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none.
-/
import Spike.Lib.X64HelloLoopWX
import Spike.Lib.X64HelloMainSF
import Spike.Lib.X64HelloParentAt
import Spike.Lib.X64HelloMainInv

namespace Spike.Lib.X64HelloMainClosedW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf)
open Spike.Lib.X64.Flow.Worker.Hello.Parent (pN pE parent_at_preH JS oP hello_parentIn)
open Spike.Lib.X64.Flow.Worker.Hello.MainPost (mainX3 hello_exitIn)
open Spike.Lib.X64HelloPreA (cloneAtH ClonePreH)
open Spike.Lib.X64.Hello.LoopCode (waitXL hello_waitIn parkCode_hello parkEntry_hello)
open Spike.Lib.X64.HelloRunsOff (waitRunsH exitRunsH wait_off park_off exit_off hello_flag_ne)
open Spike.Lib.X64WakeOff (RunsOffA runsOffA_append)
open Spike.Lib.X64HelloMainInv (mainInvP mainInvP_of mainWRH)
open Spike.Lib.X64.WideKeep (WideX)
open Spike.Lib.X64.WaitLoop (RdOne Past)
open Spike.Lib.X64.WaitLoopX (NX seg_waitLoopWX seg_parkCallWX)
open Spike.Lib.X64.Flow.Ret0 (LimOk StOk LdOk)
open Spike.Lib.X64.WakePh.MainPost (At.withRsp)
open Spike.Lib.X64WakeInst (RtOff htp_of_ldOk htp8_of_limOk)
open Spike.Lib.X64WakeMainW (parkGW_main)
open Spike.Lib.X64WakeMainR (ParkGW.and)
open Spike.Lib.X64HelloLoopWX (LoopWX.and loopWX_main loopWX_relW loopWX_ctl loopWX_sys loopWX_flag parkGWX_flag)
open Spike.Lib.X64HelloMainSegW (parentRunsH seg_parentW parentW_main seg_waitExitW exitW0_main exitW1_main
  parent_off)
open Spike.Lib.X64HelloMainSF (ParentW.and)

/-- **main's post-spawn pcs at hello**: the loop's, the park's, the
parent's and the `exit_group` tail's runs. -/
def mainRunsH : List (String × Nat × Nat) :=
  waitRunsH ++ Spike.Lib.X64.Flow.Park.parkRuns ++ parentRunsH ++ exitRunsH

/-- **main's post-spawn pcs are off every abort exit and the transfer
sites**, in any executable laying out `helloCells`. -/
theorem mainRunsH_off {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe SccCode.helloCells kp) : RunsOffA (_root_.Executable.labels exe).label mainRunsH :=
  runsOffA_append (runsOffA_append (runsOffA_append (wait_off hp) (park_off hp)) (parent_off hp)) (exit_off hp)

/-- **main's invariant after its `clone`, inside `W`**: from main at its
clone (`ClonePreH`) the parent is at `pN .ts` (`parent_at_preH`, any frame
condition containing the parent's memory outside the region, `hF`), where
`hseg`'s closed invariant holds. -/
theorem main_closed_of_cloneWH {W : Frag isa} {p : Prog} {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isa}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH Λ r0 r1 X lbl t s)
    {R : Region} {F F0 : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH exe, oP, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 128)
    (hRlo : -128 ≤ R.lo) (hRhi : R.hi ≤ 96) (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hF : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hseg : SegLW W p lbl ms
      (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts)) (fun _ _ => False)) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧
      mainInvP p lbl ms W (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  obtain ⟨th, hth, hAt⟩ := parent_at_preH hp hend h hat hRb hRlo hRhi hlh hR htop hr0 hrm
  obtain ⟨inv, hP, hW, hi⟩ := hseg.closed
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  exact ⟨th, hth, mainInvP_of hW hi (hP _ _ ⟨he, hn, hdc, hpc, σ, hA, hF th hth _ hD, hJ⟩)⟩

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : MemSide isa} {Λ : Scc.Sem.Layout}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A fp ra tp : BitVec 64}

omit [Kraken.Executable.ValidLayout exe] in
/-- **The parent's exit is the loop's entry, re-based**: `pE` on main's
region `R` (`%rsp` at offset `8`, the return address there) is
`NX waitXL … .e` on `R.fp 8` (`%rsp` at offset `0`); `At.rebase` at
`d = 8`, as x86-64 wake's `pE_rebase`. -/
theorem pE_rebaseH {R : Region} {F : MachineData → Prop} {Rd : TermRun.Word → Prop} {s : State} {c : Ctl}
    (h : At exe endPc R F (pE (_root_.Executable.labels exe).label c0 A fp ra tp) s c) :
    At exe endPc (R.fp 8) F
      (NX waitXL (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp ((R.fp 8).addr 0) .e) s c := by
  refine At.rebase (d := 8)
    (n := ⟨_, _, fun σ c => (pE (_root_.Executable.labels exe).label c0 A fp ra tp).J σ c ∧
      σ.regs.get64 .rsp = R.addr 8⟩)
    (n' := NX waitXL (_root_.Executable.labels exe).label c0 x e ty Rd A fp ra tp ((R.fp 8).addr 0) .e)
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

/-- **main after its `clone` inside `mainWRH`**: the parent on `R`, the
loop (`NX waitXL`) and the park call on `R.fp 8`, the exit tail; each
segment's obligations are `mainW`'s, `RelWS`'s, `LabMapped`'s, `MainSys`'s
and `FlagW`'s combined with the `.and` lemmas, the loop's and the park's
code and labels and the flag check decided on `helloCells`; `hms`: the
runtime words outside the labels, so neither `tp` nor `tp + 8` is the
flag's word. -/
theorem seg_mainPostWH (hp : Lays exe SccCode.helloCells kp) (hend : endPc = endOf exe SccCode.helloCells kp)
    {R : Region} {F : MachineData → Prop} {cP : Ctl} {cv : String} {tyP tyv : Ty}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 40 ≤ R.hi)
    (hrun : LocalRun p cP c0)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hfp : fp = R.addr 80)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3)
    (hexit : ∀ s c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX3 + 4 + 4 + 5, ⟨8, [(.rbp, 72)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ) wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) cP)
    (hmE : ∀ c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ) c)
    (hwb : c0.term = Spike.Lib.X64WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.X64WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.X64WakeM0.wlIf)
    (hms : RtOff lbl lsize ms) :
    SegLW (mainWRH (_root_.Executable.labels exe).label exe Λ lbl lsize) p lbl ms
      (At exe endPc R F (pN (_root_.Executable.labels exe).label cP A fp ra tp .ts))
      (fun _ _ => False) := by
  have h1 : R.lo ≤ 8 := by omega
  have h2 : (8 : Int) < R.hi := by omega
  have hF' := FStable.fp hR h1 h2 hF
  have hR' := Region.fp_ok hR h1 h2
  have hlo' : (R.fp 8).lo ≤ -88 := by show R.lo - 8 ≤ -88; omega
  have hhi' : (8 : Int) ≤ (R.fp 8).hi := by show 8 ≤ R.hi - 8; omega
  have hfp' : fp = (R.fp 8).addr 72 := by rw [Region.fp_addr]; exact hfp
  have h48 : R.Off (-48) := ⟨by decide, by omega, by omega⟩
  have h16' : (R.fp 8).Off (-16) := ⟨by decide, by show R.lo - 8 ≤ -16; omega, by show -16 + 8 ≤ R.hi - 8; omega⟩
  have h24' : (R.fp 8).Off (-24) := ⟨by decide, by show R.lo - 8 ≤ -24; omega, by show -24 + 8 ≤ R.hi - 8; omega⟩
  have hm0 := Spike.Lib.X64WakeMainL.labMapped_c0 hterm hev hval htag hmA
  have h0 := Spike.Lib.X64WakeMainF.flag0_of (lsize := lsize) hwb hterm hev hloc hin
  have hflag := hello_flag_ne hp
  have htp := htp_of_ldOk hms hT hloc hin
  have htp8 := htp8_of_limOk hms hlim hloc hin
  have hpcode := parkCode_hello hp hend (c0 := c0) (rbp0 := 0) (ra := 0) (tp := 0)
  -- the parent on `R`, then the loop on `R.fp 8` (`pE_rebaseH`: `At.rebase` at `d = 8`), then the tail
  refine ((SegLW.ofSegW (seg_parentW hp hend hello_parentIn (c0 := c0) hF hR hlo (by omega) hrun
      (ParentW.and (parentW_main (parent_off hp) hwide h48 hcP hfvP hlP hloc)
        (ParentW.and (Spike.Lib.X64HelloMainSF.parentW_relW hp hend hR hlo (by omega))
          (ParentW.and (Spike.Lib.X64HelloMainSF.parentW_ctl hmP)
            (ParentW.and (Spike.Lib.X64HelloMainSF.parentW_sys hp hend hR hlo (by omega))
              (Spike.Lib.X64HelloMainSF.parentW_flag hcPf))))))).seq
    ((seg_waitLoopWX hp hend hello_waitIn hF' hR' hlo' hhi' hlim hterm hev hval htag hdm
      (LoopWX.and (loopWX_main (wait_off hp) hwide hlo' hhi' hc0 hE hfv0 hfvE hxc hl hloc)
        (LoopWX.and (loopWX_relW hp hend hello_waitIn hR' hlo' hhi')
          (LoopWX.and (loopWX_ctl hm0 hmE)
            (LoopWX.and (loopWX_sys hp hend hello_waitIn hR' hlo' hhi')
              (loopWX_flag hp hend hello_waitIn hR' hlo' hhi' rfl hflag hwb hterm hev hloc hin htp8)))))
      (seg_parkCallWX hp hello_waitIn hF' hR' hlo' hhi' hK hT hown hS htp4 hpcode (parkEntry_hello hp)
        (fun R' F' hR'e hR'' hFF hm g' hg' => ParkGW.and
          (parkGW_main (x := x) (e := e) (ty := ty) (Rd := RdOne (ms := ms) lbl) (park_off hp) hwide hR' hlo'
            hhi' hc0 hfv0 hl hloc R' F' hR'e hR'' hFF hm g' hg')
          (ParkGW.and
            (Spike.Lib.X64WakeMainR.parkGW_relW hR'' (by rw [hR'e]; exact Int.le_refl _)
              (by rw [hR'e]; exact Int.le_refl _) (parkCode_hello hp hend))
            (ParkGW.and (by obtain rfl := hg'; exact Spike.Lib.X64WakeMainL.parkGW_ctl hm0)
              (ParkGW.and
                (Spike.Lib.X64WakeMainS.parkGW_sys hR'' (by rw [hR'e]; exact Int.le_refl _)
                  (by rw [hR'e]; exact Int.le_refl _) (parkCode_hello hp hend))
                (by
                  obtain rfl := hg'
                  exact parkGWX_flag hR'' (by rw [hR'e]; exact Int.le_refl _)
                    (by rw [hR'e]; exact Int.le_refl _) (parkCode_hello hp hend) hflag h0 htp))))))).mono_pre
      fun _ _ h => pE_rebaseH h)).seq
    (SegLW.exists_pre fun y => ?_)
  cases y
  exact SegLW.ofSegW (seg_waitExitW hp hend hello_exitIn hF' hR' (by show R.lo - 8 ≤ 0; omega)
    (by show 32 ≤ R.hi - 8; omega) hK hfp' hra hexit
    ((exitW0_main (exit_off hp) hra hwide h16' h24' hE hfvE hxc hl hloc).and
      ((Spike.Lib.X64HelloMainSF.exitW0_relW hp hend hR' (by show R.lo - 8 ≤ 0; omega)
          (by show 32 ≤ R.hi - 8; omega) hra).and
        ((Spike.Lib.X64HelloMainSF.exitW0_ctl hmE).and
          ((Spike.Lib.X64HelloMainSF.exitW0_sys hp hend hR' (by show R.lo - 8 ≤ 0; omega)
              (by show 32 ≤ R.hi - 8; omega) hra).and
            (Spike.Lib.X64HelloMainSF.exitW0_flag hwb hterm)))))
    ((exitW1_main (exit_off hp) hra hwide h16' h24' hE hfvE hxc hl hloc).and
      ((Spike.Lib.X64HelloMainSF.exitW1_relW hp hend hra).and
        ((Spike.Lib.X64HelloMainSF.exitW1_ctl hmE).and
          (Spike.Lib.X64HelloMainSF.exitW1_sys.and (Spike.Lib.X64HelloMainSF.exitW1_flag hwb hterm))))))

end Post

/-- **main's invariant after its `clone` in hello's cells, inside
`mainWRH`**: `main_closed_of_cloneWH` with `seg_mainPostWH` on main's
region `R` (offsets `[-128, 40)`) and a frame condition `F` stable on it
containing the parent's memory outside `R` (`hFR`). -/
theorem main_closed_helloW {p : Prog} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {endPc : Int64} {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isa}
    {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH Λ r0 r1 X lbl t s)
    {R : Region} {F F0 : MachineData → Prop} {cP : Ctl} {A fp ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH exe, oP, JS cP A fp ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isa, t.1.threads = #[th] →
      (R.base.toNat : Int) = (th.st.st.1.regs.get64 .rsp).toNat + 128)
    (hRlo : R.lo = -128) (hRhi : R.hi = 40) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hFR : ∀ th : Thread isa, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hF : FStable R F)
    {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    (hrun : LocalRun p cP c0)
    (hlim : LimOk ms F (tp + (8 : Int64).toBitVec) ((R.fp 8).addr 0 - 8#64 - (16 : Int64).toBitVec))
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ m, F m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.X64.abi) (hT : LdOk ms F tp)
    (hown : OwnAt ms exe endPc ((_root_.Executable.labels exe).label ".Lscc_rt_park.entry") tp tp)
    (hS : StOk ms F (tp + 16#64) 0#64) (htp4 : (tp + 16#64).toNat % 4 = 0)
    (hfp : fp = R.addr 80)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3)
    (hexit : ∀ s c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      At exe endPc (R.fp 8) F ⟨(_root_.Executable.labels exe).label mainX3 + 4 + 4 + 5, ⟨8, [(.rbp, 72)]⟩,
        fun σ _ => σ.regs.rdi.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    {cv : String} {tyP tyv : Ty}
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (tyv, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.X64Consumer.K0 Λ') wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') cP)
    (hmE : ∀ c, Past c0 x e ty (RdOne (ms := ms) lbl) c →
      Spike.Lib.X64WakeMappedRow.LabMapped lbl (Spike.Lib.X64Consumer.K0 Λ') c)
    (hwb : c0.term = Spike.Lib.X64WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.X64WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.X64WakeM0.wlIf)
    (hms : RtOff lbl lsize ms) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧
      mainInvP p lbl ms (mainWRH (_root_.Executable.labels exe).label exe Λ' lbl lsize)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP :=
  main_closed_of_cloneWH hp hend h hat hRb (by omega) (by omega) (by omega) hR htop hr0 hrm hFR
    (seg_mainPostWH (Λ := Λ') hp hend hF hR (by omega) (by omega) hrun hlim hterm hev hval htag hdm hK hT hown
      hS htp4 hfp hra hexit hwide hcP hfvP hlP hc0 hfv0 hl hloc hE hfvE hxc hmA hmP hmE hwb hin hcPf hms)

end Spike.Lib.X64HelloMainClosedW

/-- info: 'Spike.Lib.X64HelloMainClosedW.mainRunsH_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainClosedW.mainRunsH_off

/--
info: 'Spike.Lib.X64HelloMainClosedW.main_closed_helloW' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainClosedW.main_closed_helloW
