/-
**hello's main after its `clone`: the invariant inside `mainWRH`**
(AArch64; the twin of `A64WakeMainAfter.main_closed_of_clone` and
`A64WakeMainClosedW` at hello.w's listing `SccCode.helloProg`): back from
the clone at `Hello.Parent.pN … .cb` (`Hello.Parent.parent_at_preH`, main's
region based 144 above `sp`), main's path to its `exit_group` is one
`SegLW` to nothing inside `HelloMainInv.mainWRH` (hello's parent, frame
144; `wc_waitLoop` at prefix `.L21_wc_waitLoop` and `scc_rt_park`, wake's
generic segments and node lemmas; the exit tail at `.sp1`), so main's
invariant `HelloMainInv.mainInvP p … (mainWRH …)` holds at the parent.

- `mainRunsH`: the pcs of the path (the loop's, the park's, the parent's
  and the exit tail's runs); `mainRunsH_off`: off every abort exit and the
  transfer sites in any layout of `helloProg`.
- `main_closed_of_cloneWH`: from `ClonePreH` and a `SegLW W` from `pN .cb`,
  `mainInvP p lbl ms W` at the parent.
- `seg_mainPostWH`: hello's `seg_mainPostH` as a `SegLW` inside `mainWRH`.
- `main_closed_helloW`: the whole, at hello's code and labels (the loop's
  and the park's code, their labels and the flag check decided on
  `helloProg`).
-/
import Spike.Lib.A64HelloMainSF
import Spike.Lib.A64HelloParentAt
import Spike.Lib.A64HelloLoopCode
import Spike.Lib.A64HelloRunsOff
import Spike.Lib.A64WakeRunsOff

namespace Spike.Lib.A64HelloMainClosedW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent (pN parent_at_preH JS oP)
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1)
open Spike.Lib.HelloPreA (cloneAtH ClonePreH)
open Scc.Cert.Rt.A64 (Lays endOf)
open SccCode (helloProg)
open Spike.Lib.A64WakeOff (RunsOffA)
open Spike.Lib.HelloMainInv (mainInvP mainInvP_of mainWRH)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.A64WakeMainW (waitRuns loopW_main parkGW_main)
open Spike.Lib.A64HelloMainSegW (parentRunsH exitRunsH seg_parentW parentW_main seg_waitExitW exitW0_main
  exitW1_main)
open Spike.Lib.A64.HelloLabels (pfx)

/-- **main's post-spawn pcs at hello**: the loop's, the park's, the
parent's and the `exit_group` tail's runs. -/
def mainRunsH : List (String × Nat × Nat) :=
  waitRuns pfx ++ Spike.Lib.A64.Flow.Park.parkRuns ++ parentRunsH ++ exitRunsH

/-- **main's post-spawn pcs are off every abort exit and the transfer
sites**, in any executable laying out `helloProg`. -/
theorem mainRunsH_off {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe helloProg kp) : RunsOffA (_root_.Executable.labels exe).label mainRunsH :=
  Spike.Lib.A64.WakeRunsOff.runsOffA_append
    (Spike.Lib.A64.WakeRunsOff.runsOffA_append
      (Spike.Lib.A64.WakeRunsOff.runsOffA_append (Spike.Lib.A64.HelloRunsOff.wait_off hp)
        (Spike.Lib.A64.HelloRunsOff.park_off hp))
      (Spike.Lib.A64HelloMainSegW.parent_off hp))
    (Spike.Lib.A64HelloMainSegW.exit_off hp)

/-- **main's invariant after its `clone`, inside `W`**: from main at its
clone (`ClonePreH`) the parent is at `pN .cb` (`parent_at_preH`, any frame
condition containing the parent's memory outside the region, `hF`), where
`hseg`'s closed invariant holds. -/
theorem main_closed_of_cloneWH {W : Frag isaLSE2} {p : Prog} {exe : _root_.Executable}
    [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 144)
    (hRlo : -144 ≤ R.lo) (hRhi : R.hi ≤ 80) (hlh : R.lo ≤ R.hi) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hF : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hseg : SegLW W p lbl ms
      (At exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)) (fun _ _ => False)) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      mainInvP p lbl ms W (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  obtain ⟨th, hth, hAt⟩ := parent_at_preH hp hend h hat hRb hRlo hRhi hlh hR htop hr0 hrm
  obtain ⟨inv, hP, hW, hi⟩ := hseg.closed
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  exact ⟨th, hth, mainInvP_of hW hi (hP _ _ ⟨he, hn, hdc, hpc, σ, hA, hF th hth _ hD, hJ⟩)⟩

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {ms : MemSide isaLSE2} {Λ : Scc.Sem.Layout}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A ra tp : BitVec 64}
  {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

set_option linter.unusedSimpArgs false in
/-- **main after its `clone` inside `mainWRH`** (`seg_mainPostH` as a
`SegLW` inside `mainWRH`): the node obligations of each segment at
`mainWRH`, the loop's and the park's code and labels and the flag check
decided on `helloProg`. -/
theorem seg_mainPostWH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {cP : Ctl}
    {cv : String} {tyP : Ty} (g0 : γ)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -144) (hhi : ∀ g, 48 ≤ (Rg g).hi)
    (hrun : LocalRun p cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0)
    (htls : ∀ g,
      SegW (mainWRH (_root_.Executable.labels exe).label exe Λ lbl lsize) (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1)
    (hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ) wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) cP)
    (hmE : ∀ c, Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c)
    (hwb : c0.term = Spike.Lib.WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.WakeM0.wlIf) :
    SegLW (mainWRH (_root_.Executable.labels exe).label exe Λ lbl lsize) p lbl ms
      (At exe endPc (Rg g0) (Fg g0) (pN pfxM (_root_.Executable.labels exe).label cP A (fp g0) ra tp .cb))
      (fun _ _ => False) := by
  obtain ⟨hentry, -, hs3, hpe⟩ := Spike.Lib.A64.Flow.Worker.Hello.LoopCode.loopLabs_hello hp
  have hflag := Spike.Lib.A64.HelloRunsOff.hello_flag_ne hp
  have hruns := mainRunsH_off hp
  have hsub : ∀ l (hl : ∀ q ∈ l, q ∈ mainRunsH), RunsOffA (_root_.Executable.labels exe).label l :=
    fun l hl => hruns.mono hl
  have hrW := hsub (waitRuns pfx) fun q hq => by simp only [mainRunsH, List.mem_append, hq, true_or, or_true]
  have hrK := hsub Spike.Lib.A64.Flow.Park.parkRuns fun q hq => by
    simp only [mainRunsH, List.mem_append, hq, true_or, or_true]
  have hrP := hsub parentRunsH fun q hq => by simp only [mainRunsH, List.mem_append, hq, true_or, or_true]
  have hrX := hsub exitRunsH fun q hq => by simp only [mainRunsH, List.mem_append, hq, true_or, or_true]
  have hoff : ∀ g, (Rg g).Off (-32) := fun g => ⟨by decide, by have := hlo g; omega, by have := hhi g; omega⟩
  have hoff104 : ∀ g, (Rg g).Off (-104) := fun g => ⟨by decide, by have := hlo g; omega, by have := hhi g; omega⟩
  have hm0 := Spike.Lib.A64WakeMainL.labMapped_c0 hterm hev hval htag hmA
  have h0 := Spike.Lib.A64WakeMainF.flag0_of (lsize := lsize) hwb hterm hev hloc hin
  have hwc := fun {g : γ} => Spike.Lib.A64.Flow.Worker.Hello.LoopCode.waitCode_hello hp hend (c0 := c0) (x := x)
    (e := e) (ty := ty) (Rd := fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) (A := A) (x29 := fp g) (ra := ra) (tp := tp)
  refine ((SegLW.ofSegW (seg_parentW (c0 := c0) hp hend (hF g0) (hR g0) (hal g0) (hlo g0)
      (by have := hhi g0; omega) hrun (Spike.Lib.A64HelloMainSF.ParentW.and
        (parentW_main hrP hwide (hoff104 g0) hcP hfvP hlP hloc)
        (Spike.Lib.A64HelloMainSF.ParentW.and
          (Spike.Lib.A64HelloMainSF.parentW_relW hp hend (hR g0) (hal g0) (hlo g0) (by have := hhi g0; omega))
          (Spike.Lib.A64HelloMainSF.ParentW.and (Spike.Lib.A64HelloMainSF.parentW_ctl hmP)
            (Spike.Lib.A64HelloMainSF.ParentW.and
              (Spike.Lib.A64HelloMainSF.parentW_sys hp hend (hR g0) (hal g0) (hlo g0) (by have := hhi g0; omega))
              (Spike.Lib.A64HelloMainSF.parentW_flag hcPf))))))).seq
    (Spike.Lib.A64.WaitLoop.seg_waitLoopW hF hR hal (fun g => by have := hlo g; omega)
      (fun g => by have := hhi g; omega) hterm hev hval htag hdm (fun g => hwc (g := g)) hentry
      (fun g => Spike.Lib.A64WakeMainR.LoopW.and (loopW_main hrW hentry hwide (hoff g) hc0 hE hfv0 hfvE hxc hl hloc)
        (Spike.Lib.A64WakeMainR.LoopW.and
          (Spike.Lib.A64WakeMainR.loopW_relW (hR g) (hal g) (by have := hlo g; omega) (by have := hhi g; omega)
            (hwc (g := g)))
          (Spike.Lib.A64WakeMainR.LoopW.and (Spike.Lib.A64WakeMainL.loopW_ctl hm0 hmE)
            (Spike.Lib.A64WakeMainR.LoopW.and
              (Spike.Lib.A64WakeMainS.loopW_sys (hR g) (hal g) (by have := hlo g; omega) (by have := hhi g; omega)
                (hwc (g := g)))
              (Spike.Lib.A64WakeMainF.loopW_flag (hR g) (hal g) (by have := hlo g; omega)
                (by have := hhi g; omega) (hwc (g := g)) rfl hflag hwb hterm hev hloc hin)))))
      htls
      (fun g => (Spike.Lib.A64.WaitLoop.seg_parkCallW (hF g) (hR g) (hal g) (by have := hlo g; omega)
        (by have := hhi g; omega) hK (hS g) htp4
        (Spike.Lib.A64.Flow.Worker.Hello.LoopCode.parkCode_hello hp hend (c0 := cP) (x29 := 0) (ra := 0) (tp := 0))
        hpe hs3
        (fun R' F' hR'e hR' hal' hFF hm g' hg' => Spike.Lib.A64WakeMainR.ParkGW.and
          (parkGW_main hrK hwide (hR g) (hoff g) hc0 hfv0 hl hloc R' F' hR'e hR' hal' hFF hm g' hg')
          (Spike.Lib.A64WakeMainR.ParkGW.and
            (Spike.Lib.A64WakeMainR.parkGW_relW hR' hal' (by rw [hR'e]; exact Int.le_refl _)
              (by rw [hR'e]; exact Int.le_refl _)
              (Spike.Lib.A64.Flow.Worker.Hello.LoopCode.parkCode_hello hp hend))
            (Spike.Lib.A64WakeMainR.ParkGW.and (by obtain rfl := hg'; exact Spike.Lib.A64WakeMainL.parkGW_ctl hm0)
              (Spike.Lib.A64WakeMainR.ParkGW.and
                (Spike.Lib.A64WakeMainS.parkGW_sys hR' hal' (by rw [hR'e]; exact Int.le_refl _)
                  (by rw [hR'e]; exact Int.le_refl _)
                  (Spike.Lib.A64.Flow.Worker.Hello.LoopCode.parkCode_hello hp hend))
                (by
                  obtain rfl := hg'
                  exact Spike.Lib.A64WakeMainF.parkGW_flag (pfx := pfx) hR' hal'
                    (by rw [hR'e]; exact Int.le_refl _) (by rw [hR'e]; exact Int.le_refl _)
                    (Spike.Lib.A64.Flow.Worker.Hello.LoopCode.parkCode_hello hp hend) hflag h0)))))).mono_post
        fun s c h => ⟨g, h⟩) g0)).seq
    (SegLW.exists_pre fun g => SegLW.exists_pre fun x' => ?_)
  cases x'
  exact SegLW.ofSegW (seg_waitExitW hp hend (hF g) (hR g) (hal g) (by have := hlo g; omega) (hhi g) hK hra
    (hexit g) ((exitW0_main hrX hra hwide (hoff g) hE hfvE hxc hl hloc).and
      ((Spike.Lib.A64HelloMainSF.exitW0_relW hp hend (hR g) (hal g) (by have := hlo g; omega) (hhi g) hra).and
        ((Spike.Lib.A64HelloMainSF.exitW0_ctl hmE).and
          ((Spike.Lib.A64HelloMainSF.exitW0_sys hp hend (hR g) (hal g) (by have := hlo g; omega) (hhi g) hra).and
            (Spike.Lib.A64HelloMainSF.exitW0_flag hwb hterm)))))
    ((exitW1_main hrX hra hwide (hoff g) hE hfvE hxc hl hloc).and
      ((Spike.Lib.A64HelloMainSF.exitW1_relW hp hend hra).and ((Spike.Lib.A64WakeMainL.exitW1_ctl hmE).and
        (Spike.Lib.A64WakeMainS.exitW1_sys.and (Spike.Lib.A64WakeMainF.exitW1_flag hwb hterm))))))

end Post

/-- **main's invariant after its `clone` in hello's program, inside
`mainWRH`**: `main_closed_of_cloneWH` with `seg_mainPostWH` at the ghost
`g0` whose region is `R` (`hRg`), frame pointer `x29` (`hfp`) and frame
condition contains the parent's memory outside `R` (`hFg`). -/
theorem main_closed_helloW {p : Prog} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : ClonePreH pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAtH pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 144)
    (hRlo : R.lo = -144) (hRhi : R.hi = 48) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64} (g0 : γ)
    (hRg : Rg g0 = R) (hfp : fp g0 = x29)
    (hFg : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → Fg g0 m)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hRo : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -144) (hhi : ∀ g, 48 ≤ (Rg g).hi)
    (hrun : LocalRun p cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0)
    (htls : ∀ g,
      SegW (mainWRH (_root_.Executable.labels exe).label exe Λ' lbl lsize) (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1)
    (hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp1 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → WideX exe s)
    {cv : String} {tyP : Ty}
    (hcP : cP.term ≠ WakeMLive.wlRet) (hfvP : ∀ y ∈ Scc.Sem.exprFv cP.term, y = cv)
    (hlP : TermRun.lookupE cP.env cv = some (tyP, [w]))
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hE : e ≠ WakeMLive.wlRet) (hfvE : ∀ y ∈ Scc.Sem.exprFv e, y = x ∨ y = cv) (hxc : x ≠ cv)
    (hmA : ∀ wr, Scc.Sem.Kernel.mapped (Spike.Lib.A64Consumer.K0 Λ') wr ⟨A, 8⟩ = true)
    (hmP : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') cP)
    (hmE : ∀ c, Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ') c)
    (hwb : c0.term = Spike.Lib.WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.WakeM0.wlIf) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      mainInvP p lbl ms (mainWRH (_root_.Executable.labels exe).label exe Λ' lbl lsize)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hseg := seg_mainPostWH (Λ := Λ') (exe := exe) (Rg := Rg) (Fg := Fg) (fp := fp) hp hend (cP := cP) g0 hF hRo
    hal hlo hhi hrun hterm hev hval htag hdm hK hS htp4 htls hra hexit hwide hcP hfvP hlP hc0 hfv0 hl hloc
    hE hfvE hxc hmA hmP hmE hwb hin hcPf
  rw [hRg, hfp] at hseg
  exact main_closed_of_cloneWH hp hend h hat hRb (by omega) (by omega) (by omega) hR htop hr0 hrm hFg hseg

end Spike.Lib.A64HelloMainClosedW

/-- info: 'Spike.Lib.A64HelloMainClosedW.mainRunsH_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainClosedW.mainRunsH_off

/-- info: 'Spike.Lib.A64HelloMainClosedW.main_closed_helloW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainClosedW.main_closed_helloW
