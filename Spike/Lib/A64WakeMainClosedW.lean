/-
**main's invariant after its `clone` inside `mainW`** (AArch64): `MainAfter.main_closed_wake` with main's post-spawn path a `SegLW`
inside `W := WakeInst.mainW lab exe Λ lbl`, so the invariant at the parent
is `WakeInst.mainInv … (mainW …)`, main's side `Mi` at the instance.

    seg_parentW                        -- `parentW_main`
    Spike.Lib.A64.WaitLoop.seg_waitLoopW             -- `loopW_main`; the park call
      seg_parkCallW                    --   `parkGW_main`
    seg_waitExitW                      -- `exitW0_main`, `exitW1_main`

- `mainRuns`: the pcs of the path (the loop's, the park's, the parent's and
  the `exit_group` tail's runs); `RunsOffA lab mainRuns` is the one pc
  obligation.
- `seg_mainPostW`: from `pN .cb` to nothing inside `mainW`.
- `main_closed_of_cloneW`: `main_closed_of_clone` over `SegLW W`, to
  `mainInv`.
- `main_closed_wakeW`: the whole, at wake's code and labels.

What stays a hypothesis beyond `main_closed_wake`'s: the pcs off the exits
(`hruns`), every state wide (`hwide`), and the source facts placing `cv`
(`cP` and `c0` read only `cv`, bound to the flag's locative `w` with base
`A`; past the load only `x` and `cv`; neither at `wlRet`), and for
`mainWR`'s `LabMapped` conjunct the flag's word mapped in `K0` (`hmA`) and
`LabMapped` at `cP` and past the load (`hmP`, `hmE`), and for its `FlagW`
conjunct the listing fact `hflag`, the loop's control at `wlBody` with its
flag word inside its label (`hwb`, `hin`) and the parent's at neither
`wlBody` nor `wlIf` (`hcPf`; `htls` takes `tp + 8` outside every placed
label, `A64WakeMainS.tlsW_mainR`'s `hrt8`). The
thread-pointer load's segment `htls` is now inside `mainW` (`seg_waitTlsW` with `A64WakeMainW.tlsW_main`).
-/
import Spike.Lib.A64WakeMainSegW
import Spike.Lib.A64WakeMainAfter
import Spike.Lib.A64WakeMainS

namespace Spike.Lib.A64WakeMainClosedW

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel Spike.Lib.Handover
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Wake.Child (pfxM)
open Spike.Lib.A64.Flow.Worker.Wake.Parent (pN parent_at_preR JS oP)
open Spike.Lib.A64.Flow.Worker.Wake.MainPost (mainSp0)
open Spike.Lib.WakePreA (cloneAt)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.WakeLabels (wakeProg)

open Spike.Lib.A64WakeOff (RunsOffA)
open Spike.Lib.WakeInst (mainW mainWR mainInv mainInv_of)
open Spike.Lib.A64.WideKeep (WideX)
open Spike.Lib.A64WakeMainW (waitRuns loopW_main parkGW_main)
open Spike.Lib.A64WakeMainSegW (parentRuns exitRuns seg_parentW parentW_main seg_waitExitW exitW0_main
  exitW1_main)

/-- **main's post-spawn pcs**: the loop's, the park's, the parent's and the
`exit_group` tail's runs. -/
def mainRuns : List (String × Nat × Nat) :=
  waitRuns Spike.Lib.A64.WakeLabels.pfx ++ Spike.Lib.A64.Flow.Park.parkRuns ++ parentRuns ++ exitRuns

/-- **main's invariant after its `clone`, inside `W`**: `main_closed_of_clone`
with `hseg` a `SegLW W`; the invariant at the parent is `mainInv … W`. -/
theorem main_closed_of_cloneW {W : Frag isaLSE2} {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe]
    {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80)
    (hRlo : R.lo = -96) (hRhi : R.hi = 16) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    (hF : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → F m)
    (hseg : SegLW W Spike.Lib.WakeT1.wakeSrc lbl ms
      (At exe endPc R F (pN pfxM (_root_.Executable.labels exe).label cP A x29 ra tp .cb)) (fun _ _ => False)) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      mainInv lbl ms W (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  obtain ⟨th', hth', hsp⟩ := Spike.Lib.WakeCloneSp.clone_sp_in_r0 h.spTop
  have hb := hRb th' hth'
  obtain ⟨th, hth, hAt⟩ := parent_at_preR hp hend h hat
    (by refine ⟨?_, ?_⟩ <;> omega) (by omega) hR htop hr0 hrm
  obtain ⟨inv, hP, hW, hi⟩ := hseg.closed
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ⟩ := hAt
  exact ⟨th, hth, mainInv_of hW hi (hP _ _ ⟨he, hn, hdc, hpc, σ, hA, hF th hth _ hD, hJ⟩)⟩

section Post

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isaLSE2} {Λ : Scc.Sem.Layout}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {kp : Nat}
  {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word} {A ra tp : BitVec 64}
  {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64}

set_option linter.unusedSimpArgs false in
/-- **main after its `clone` inside `mainW`** (`seg_mainPost` as a `SegLW`
inside `mainW`): the node obligations of each segment at `mainW`. -/
theorem seg_mainPostW (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp) {cP : Ctl} {cv : String}
    {tyP : Ty} (g0 : γ)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hR : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -96) (hhi : ∀ g, 16 ≤ (Rg g).hi)
    (hrun : LocalRun p cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0)
    (htls : ∀ g,
      SegW (mainWR (_root_.Executable.labels exe).label exe Λ lbl lsize) (fun _ _ => False) p lbl ms
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit p ms s c 0)
    (hruns : RunsOffA (_root_.Executable.labels exe).label mainRuns)
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
    -- `mainWR`'s `FlagW` conjunct: a listing fact (discharged at the instance), the
    -- loop's control at `wlBody` with its flag word inside its label, the
    -- parent's at neither `wlBody` nor `wlIf`
    (hflag : Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".0_entry") + 4 + 4)
      (Spike.Lib.A64WakeMainF.flagRuns Spike.Lib.A64.WakeLabels.pfx))
    (hwb : c0.term = Spike.Lib.WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.WakeM0.wlIf) :
    SegLW (mainWR (_root_.Executable.labels exe).label exe Λ lbl lsize) p lbl ms
      (At exe endPc (Rg g0) (Fg g0) (pN pfxM (_root_.Executable.labels exe).label cP A (fp g0) ra tp .cb))
      (fun _ _ => False) := by
  obtain ⟨hentry, -, hs3, hpe⟩ := Spike.Lib.A64.Flow.Worker.Wake.LoopCode.loopLabs_wake hp
  have hsub : ∀ l (hl : ∀ q ∈ l, q ∈ mainRuns), RunsOffA (_root_.Executable.labels exe).label l :=
    fun l hl => hruns.mono hl
  have hrW := hsub (waitRuns Spike.Lib.A64.WakeLabels.pfx) fun q hq => by simp only [mainRuns, List.mem_append, hq, true_or, or_true]
  have hrK := hsub Spike.Lib.A64.Flow.Park.parkRuns fun q hq => by simp only [mainRuns, List.mem_append, hq, true_or, or_true]
  have hrP := hsub parentRuns fun q hq => by simp only [mainRuns, List.mem_append, hq, true_or, or_true]
  have hrX := hsub exitRuns fun q hq => by simp only [mainRuns, List.mem_append, hq, true_or, or_true]
  have hoff : ∀ g, (Rg g).Off (-32) := fun g => ⟨by decide, by have := hlo g; omega, by have := hhi g; omega⟩
  have hoff72 : ∀ g, (Rg g).Off (-72) := fun g => ⟨by decide, by have := hlo g; omega, by have := hhi g; omega⟩
  have hm0 := Spike.Lib.A64WakeMainL.labMapped_c0 hterm hev hval htag hmA
  have h0 := Spike.Lib.A64WakeMainF.flag0_of (lsize := lsize) hwb hterm hev hloc hin
  refine ((SegLW.ofSegW (seg_parentW (c0 := c0) hp hend (hF g0) (hR g0) (hal g0) (by have := hlo g0; omega)
      (by have := hhi g0; omega) hrun (Spike.Lib.A64WakeMainR.ParentW.and
        (parentW_main hrP hwide (hoff72 g0) hcP hfvP hlP hloc)
        (Spike.Lib.A64WakeMainR.ParentW.and
          (Spike.Lib.A64WakeMainR.parentW_relW hp hend (hR g0) (hal g0) (by have := hlo g0; omega)
            (by have := hhi g0; omega))
          (Spike.Lib.A64WakeMainR.ParentW.and (Spike.Lib.A64WakeMainL.parentW_ctl hmP)
            (Spike.Lib.A64WakeMainR.ParentW.and
              (Spike.Lib.A64WakeMainS.parentW_sys hp hend (hR g0) (hal g0) (by have := hlo g0; omega)
                (by have := hhi g0; omega)) (Spike.Lib.A64WakeMainF.parentW_flag hcPf))))))).seq
    (Spike.Lib.A64.WaitLoop.seg_waitLoopW hF hR hal (fun g => by have := hlo g; omega) (fun g => by have := hhi g; omega)
      hterm hev hval htag hdm (fun _ => Spike.Lib.A64.Flow.Worker.Wake.LoopCode.waitCode_wake hp hend) hentry
      (fun g => Spike.Lib.A64WakeMainR.LoopW.and (loopW_main hrW hentry hwide (hoff g) hc0 hE hfv0 hfvE hxc hl hloc)
        (Spike.Lib.A64WakeMainR.LoopW.and
          (Spike.Lib.A64WakeMainR.loopW_relW (hR g) (hal g) (by have := hlo g; omega) (by have := hhi g; omega)
            (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.waitCode_wake hp hend))
          (Spike.Lib.A64WakeMainR.LoopW.and (Spike.Lib.A64WakeMainL.loopW_ctl hm0 hmE)
            (Spike.Lib.A64WakeMainR.LoopW.and
              (Spike.Lib.A64WakeMainS.loopW_sys (hR g) (hal g) (by have := hlo g; omega) (by have := hhi g; omega)
                (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.waitCode_wake hp hend))
              (Spike.Lib.A64WakeMainF.loopW_flag (hR g) (hal g) (by have := hlo g; omega) (by have := hhi g; omega)
                (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.waitCode_wake hp hend) rfl hflag hwb hterm hev hloc
                hin)))))
      htls
      (fun g => (Spike.Lib.A64.WaitLoop.seg_parkCallW (hF g) (hR g) (hal g) (hlo g) (by have := hhi g; omega) hK (hS g) htp4
        (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.parkCode_wake hp hend (c0 := cP) (x29 := 0) (ra := 0) (tp := 0)) hpe hs3
        (fun R' F' hR'e hR' hal' hFF hm g' hg' => Spike.Lib.A64WakeMainR.ParkGW.and
          (parkGW_main hrK hwide (hR g) (hoff g) hc0 hfv0 hl hloc R' F' hR'e hR' hal' hFF hm g' hg')
          (Spike.Lib.A64WakeMainR.ParkGW.and
            (Spike.Lib.A64WakeMainR.parkGW_relW hR' hal' (by rw [hR'e]; exact Int.le_refl _)
              (by rw [hR'e]; exact Int.le_refl _)
              (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.parkCode_wake hp hend))
            (Spike.Lib.A64WakeMainR.ParkGW.and (by obtain rfl := hg'; exact Spike.Lib.A64WakeMainL.parkGW_ctl hm0)
              (Spike.Lib.A64WakeMainR.ParkGW.and
                (Spike.Lib.A64WakeMainS.parkGW_sys hR' hal' (by rw [hR'e]; exact Int.le_refl _)
                  (by rw [hR'e]; exact Int.le_refl _)
                  (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.parkCode_wake hp hend))
                (by
                  obtain rfl := hg'
                  exact Spike.Lib.A64WakeMainF.parkGW_flag (pfx := Spike.Lib.A64.WakeLabels.pfx) hR' hal'
                    (by rw [hR'e]; exact Int.le_refl _) (by rw [hR'e]; exact Int.le_refl _)
                    (Spike.Lib.A64.Flow.Worker.Wake.LoopCode.parkCode_wake hp hend) hflag h0)))))).mono_post
        fun s c h => ⟨g, h⟩) g0)).seq
    (SegLW.exists_pre fun g => SegLW.exists_pre fun x' => ?_)
  cases x'
  exact SegLW.ofSegW (seg_waitExitW hp hend (hF g) (hR g) (hal g) (by have := hlo g; omega) (hhi g) hK hra
    (hexit g) ((exitW0_main hrX hra hwide (hoff g) hE hfvE hxc hl hloc).and
      ((Spike.Lib.A64WakeMainR.exitW0_relW hp hend (hR g) (hal g) (by have := hlo g; omega) (hhi g) hra).and
        ((Spike.Lib.A64WakeMainL.exitW0_ctl hmE).and
          ((Spike.Lib.A64WakeMainS.exitW0_sys hp hend (hR g) (hal g) (by have := hlo g; omega) (hhi g) hra).and
            (Spike.Lib.A64WakeMainF.exitW0_flag hwb hterm)))))
    ((exitW1_main hrX hra hwide (hoff g) hE hfvE hxc hl hloc).and
      ((Spike.Lib.A64WakeMainR.exitW1_relW hp hend hra).and ((Spike.Lib.A64WakeMainL.exitW1_ctl hmE).and
        (Spike.Lib.A64WakeMainS.exitW1_sys.and (Spike.Lib.A64WakeMainF.exitW1_flag hwb hterm))))))

end Post

/-- **main's invariant after its `clone` in wake's program, inside
`mainW`**: `main_closed_of_cloneW` with `seg_mainPostW` at the ghost `g0`
whose region is `R` (`hRg`), frame pointer `x29` (`hfp`) and frame
condition contains the parent's memory outside `R` (`hFg`): main's side
`Mi` at the instance (`mainInv … (mainW …)`) holds at the parent. -/
theorem main_closed_wakeW {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {kp : Nat} (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    {Λ Λ' : Scc.Sem.Layout} {r0 r1 : Range} {X : State → Prop} {lbl : WeakMem.AllocLabel → Option Nat}
    {lsize : WeakMem.AllocLabel → Nat}
    {ms : MemSide isaLSE2}
    {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg} (h : Spike.Lib.WakePreA.ClonePre pfxM Λ r0 r1 X lbl t s)
    {R : Spike.Lib.Region} {F0 : MachineData → Prop} {cP : Ctl} {A x29 ra tp : BitVec 64}
    (hat : ∀ th, t.1.threads = #[th] → At exe endPc R F0 ⟨cloneAt pfxM exe, oP, JS cP A x29 ra tp⟩ th.st cP)
    (hRb : ∀ th : Thread isaLSE2, t.1.threads = #[th] → (R.base.toNat : Int) = th.st.st.1.regs.SP.toNat + 80)
    (hRlo : R.lo = -96) (hRhi : R.hi = 16) (hR : R.OK)
    (htop : r1.lo + r1.size ≤ 2 ^ 64) {r : BitVec 64} (hr0 : 0 < r.toNat) (hrm : r.toNat < Scc.Sem.Kernel.pidMax)
    {c0 : Ctl} {x : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {γ : Sort _} {Rg : γ → Spike.Lib.Region} {Fg : γ → MachineData → Prop} {fp : γ → BitVec 64} (g0 : γ)
    (hRg : Rg g0 = R) (hfp : fp g0 = x29)
    (hFg : ∀ th : Thread isaLSE2, t.1.threads = #[th] → ∀ m,
      DFrame R (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st.st.1 m → Fg g0 m)
    (hF : ∀ g, FStable (Rg g) (Fg g)) (hRo : ∀ g, (Rg g).OK)
    (hal : ∀ g, (Rg g).base.toNat % 16 = 0) (hlo : ∀ g, (Rg g).lo ≤ -96) (hhi : ∀ g, 16 ≤ (Rg g).hi)
    (hrun : LocalRun Spike.Lib.WakeT1.wakeSrc cP c0)
    (hterm : c0.term = .let_ x (.load true a) e) (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hval : ValRep lbl w.val A.toNat) (htag : ∃ sa, w.val = .loc sa 0)
    (hdm : ∀ g m, Fg g m → Mem.loadInt m.dmem A 8 = none)
    (hK : ms.K = some Scc.Sem.A64.abi) (hS : ∀ g, Ret0.StOk ms (Fg g) exe endPc (tp + 16#64) 0#64)
    (htp4 : (tp + 16#64).toNat % 4 = 0)
    (htls : ∀ g,
      SegW (mainWR (_root_.Executable.labels exe).label exe Λ' lbl lsize) (fun _ _ => False) Spike.Lib.WakeT1.wakeSrc lbl ms
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .tls))
        (At exe endPc (Rg g) (Fg g)
          (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label Spike.Lib.A64.WakeLabels.pfx c0 x e ty
            (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A (fp g) ra tp .n1)))
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp0)
    (hexit : ∀ g s c, Spike.Lib.A64.WaitLoop.Past c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) c →
      At exe endPc (Rg g) (Fg g) ⟨(_root_.Executable.labels exe).label mainSp0 + 4 + 4 + 4, ⟨0, []⟩,
        fun σ _ => σ.regs.X0.toBitVec = 0#64⟩ s c → ¬ ms.abortAt s → MainExit Spike.Lib.WakeT1.wakeSrc ms s c 0)
    (hruns : RunsOffA (_root_.Executable.labels exe).label mainRuns)
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
    (hflag : Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (Spike.Lib.A64.WakeLabels.pfx ++ ".0_entry") + 4 + 4)
      (Spike.Lib.A64WakeMainF.flagRuns Spike.Lib.A64.WakeLabels.pfx))
    (hwb : c0.term = Spike.Lib.WakeM0.wlBody) (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label)
    (hcPf : cP.term ≠ Spike.Lib.WakeM0.wlBody ∧ cP.term ≠ Spike.Lib.WakeM0.wlIf) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      mainInv lbl ms (mainWR (_root_.Executable.labels exe).label exe Λ' lbl lsize)
        (Kernel.retThread abi (parentPre abi t.2 0 th (r1.lo + r1.size)) r).st cP := by
  have hseg := seg_mainPostW (Λ := Λ') (exe := exe) (Rg := Rg) (Fg := Fg) (fp := fp) hp hend (cP := cP) g0 hF hRo
    hal hlo hhi hrun hterm hev hval htag hdm hK hS htp4 htls hra hexit hruns hwide hcP hfvP hlP hc0 hfv0 hl hloc
    hE hfvE hxc hmA hmP hmE hflag hwb hin hcPf
  rw [hRg, hfp] at hseg
  exact main_closed_of_cloneW hp hend h hat hRb hRlo hRhi hR htop hr0 hrm hFg hseg

/-- info: 'Spike.Lib.A64WakeMainClosedW.main_closed_wakeW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms main_closed_wakeW

end Spike.Lib.A64WakeMainClosedW
