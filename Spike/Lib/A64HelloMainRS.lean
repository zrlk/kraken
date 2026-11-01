/-
**hello's main after its `clone`: the parent's, the exit tail's and the limit load's `mainWRH` conjuncts**
(AArch64): the hello twins of the listing-fixed pieces of `A64WakeMainR` (`RelWS`), `A64WakeMainS`
(`MainSys`), `A64WakeMainL` (controls) and `A64WakeMainF` (`FlagW`), at hello's listing (`SccCode.helloProg`):
the parent's blocks (`Hello.Parent`, frame `[-144, 0)`), the `exit_group` tail at `.sp1` (`exitTail 40`, frame
`[0, 48)`) and `wc_waitLoop`'s limit load at `.L21_wc_waitLoop`. The loop's and the park's conjuncts and the tail's
`svc` node's (`exitW1_sys`, `exitW1_ctl`, `exitW1_flag`) are wake's (generic in the prefix and the program).

- `ParentWH.and` (on `A64HelloMainSegW.ParentW`); `parentW_relWH`, `parentW_sysH`, `parentW_ctlH`, `parentW_flagH`.
- `exitW0_relWH`, `exitW1_relWH`, `exitW0_sysH`, `exitW0_ctlH`, `exitW0_flagH`.
- `tlsW_relWH`, `tlsW_sysH`, `tlsW_flagH`, `tlsW_mainRH` (`seg_waitTlsW`'s `hW` inside `HelloMainInv.mainWRH`).

Superseded by `A64HelloMainSF` (same statements without the `H` suffix, on hello-l2's
`A64HelloMainSegW.ParentW`); kept building, use `A64HelloMainSF`.
-/
import Spike.Lib.A64WakeMainS
import Spike.Lib.A64HelloMainSegW
import Spike.Lib.A64HelloAbOffL
import Spike.Lib.HelloMainInv

namespace Spike.Lib.A64HelloMainRS

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem (ValRep LocRep)
open Scc.Cert.Rt.A64 (Lays endOf)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1 hello_exitIn)
open SccCode (helloProg)
open Spike.Lib.A64WakeMainSegW (exitNP)
open Spike.Lib.A64HelloMainSegW (ParentW)
open Spike.Lib.WakeInst (MainSys FlagW)
open Spike.Lib.WakeM0 (wlBody wlIf)
open Spike.Lib.A64WakeOff (RunsNe)
open Spike.Lib.A64WakeMainF (Flag0 FlagOff flagRuns blkW_off nodeW_off nodeW_flag runsNe_at flagOff_past)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## The parent -/

section Parent

variable {cP : Ctl} {A x29 ra tp : BitVec 64}

/-- **Two predicates' `ParentWH` combine.** -/
theorem ParentWH.and {W₁ W₂ : Frag isaLSE2} (h₁ : ParentW W₁ exe endPc R F cP A x29 ra tp)
    (h₂ : ParentW W₂ exe endPc R F cP A x29 ra tp) :
    ParentW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F cP A x29 ra tp where
  wcb := h₁.wcb.and h₂.wcb
  wcl := h₁.wcl.and h₂.wcl
  wbs := h₁.wbs.and h₂.wbs
  wsp := h₁.wsp.and h₂.wsp

variable [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **The parent's states are in `RelWS`**, in any valid layout of `helloProg`. -/
theorem parentW_relWH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) :
    ParentW (fun s _ => RelWS s) exe endPc R F cP A x29 ra tp := by
  have hin := hello_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, -⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  exact {
    wcb := blkW_relW cbP_ok hR hal hlo hhi (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero]))
    wcl := blkW_relW cl_ok hR hal hlo hhi (code_of hp hend hcl (ofNat4_zero _))
    wbs := blkW_relW bs_ok hR hal hlo hhi (code_of hp hend hbs rfl)
    wsp := blkW_relW spB_ok hR hal hlo hhi (code_of hp hend hsp (ofNat4_zero _)) }

/-- **The parent's states are at no system call**, in any valid layout of `helloProg`. -/
theorem parentW_sysH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) :
    ParentW (fun s _ => MainSys s) exe endPc R F cP A x29 ra tp := by
  have hin := hello_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, -⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  exact {
    wcb := Spike.Lib.A64WakeMainS.blkW_sys cbP_ok hR hal hlo hhi
      (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero]))
    wcl := Spike.Lib.A64WakeMainS.blkW_sys cl_ok hR hal hlo hhi (code_of hp hend hcl (ofNat4_zero _))
    wbs := Spike.Lib.A64WakeMainS.blkW_sys bs_ok hR hal hlo hhi (code_of hp hend hbs rfl)
    wsp := Spike.Lib.A64WakeMainS.blkW_sys spB_ok hR hal hlo hhi (code_of hp hend hsp (ofNat4_zero _)) }

omit [Kraken.Executable.ValidLayout exe] in
/-- **The parent's controls satisfy `P`**: each is `cP`. -/
theorem parentW_ctlH {P : Ctl → Prop} (hP : P cP) : ParentW (fun _ c => P c) exe endPc R F cP A x29 ra tp where
  wcb := Spike.Lib.A64WakeMainL.blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wcl := Spike.Lib.A64WakeMainL.blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wbs := Spike.Lib.A64WakeMainL.blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
  wsp := Spike.Lib.A64WakeMainL.blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP

omit [Kraken.Executable.ValidLayout exe] in
/-- **The parent's states are in `FlagW`**: its control `cP` is at neither `wlBody` nor `wlIf` (`hcPf`). -/
theorem parentW_flagH {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64}
    (hcPf : cP.term ≠ wlBody ∧ cP.term ≠ wlIf) :
    ParentW (fun s c => FlagW lbl lsize q s c) exe endPc R F cP A x29 ra tp :=
  have hP : FlagOff lbl cP := ⟨hcPf.1, fun h => absurd h hcPf.2⟩
  { wcb := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wcl := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wbs := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
    wsp := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP }

end Parent

/-! ## The `exit_group` tail -/

section Exit

open Spike.Lib.A64.WaitLoop (E Past)

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64}

/-- **The tail block's controls satisfy `P`**: past the load. -/
theorem exitW0_ctlH {P : Ctl → Prop} (hP : ∀ c, Past c0 x e ty Rd c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F (E c0 x e ty Rd A x29 ra tp .ret) (exitTail 40) :=
  Spike.Lib.A64WakeMainL.blkW_ctl fun _ c hJ => by obtain ⟨hp, -⟩ := hJ; exact hP c hp

/-- **The tail block is in `FlagW`**: past the load. -/
theorem exitW0_flagH {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64}
    {a : At} {ms : MemSide isaLSE2} (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret) (exitTail 40) :=
  blkW_off fun _ _ hJ => flagOff_past hwb hterm hJ.1

variable [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **The tail block's states are in `RelWS`.** -/
theorem exitW0_relWH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 48 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F (E c0 x e ty Rd A x29 ra tp .ret) (exitTail 40) := by
  have hin := hello_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact blkW_relW (exitTail_ok (lo := 0) (hi := 48) rfl rfl) hR hal hlo hhi
    (code_of hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]))

/-- **The tail's `svc` state is in `RelWS`.** -/
theorem exitW1_relWH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F (exitNP (E c0 x e ty Rd A x29 ra tp .ret)) := by
  have hin := hello_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact nodeW_relW (code_of hp hend hin.2 (by
    show _ = Int64.ofBitVec ra + 4 + 4 + 4; rw [hra]; simp only [ofNat4_succ, ofNat4_zero]))
    fun _ hc => relWS_svc hc

/-- **The tail block is at no system call.** -/
theorem exitW0_sysH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 48 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F (E c0 x e ty Rd A x29 ra tp .ret)
      (exitTail 40) := by
  have hin := hello_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact Spike.Lib.A64WakeMainS.blkW_sys (exitTail_ok (lo := 0) (hi := 48) rfl rfl) hR hal hlo hhi
    (code_of hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]))

end Exit

/-! ## The limit load (`.tls`) -/

section Tls

open Spike.Lib.A64.WaitLoop (N)

variable [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **`wc_waitLoop`'s limit load is in `RelWS`** (a plain `ldr`), at any node at its pc. -/
theorem tlsW_relWH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {n : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (Spike.Lib.A64.HelloLabels.pfx ++ ".stack_check") +
      Int64.ofNat (4 * 2)) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n :=
  nodeW_relW (code_of hp hend Spike.Lib.A64.Flow.Worker.Hello.AbOffAt.wait_tlsCode hpc.symm)
    fun _ hc => relWS_ldr hc

/-- **The limit load is at no system call** (a plain `ldr`). -/
theorem tlsW_sysH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {n : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (Spike.Lib.A64.HelloLabels.pfx ++ ".stack_check") +
      Int64.ofNat (4 * 2)) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n :=
  Spike.Lib.A64WakeMainS.nodeW_sysCell
    (code_of hp hend Spike.Lib.A64.Flow.Worker.Hello.AbOffAt.wait_tlsCode hpc.symm) fun _ h => by cases h

variable {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64} {c0 : Ctl}
  {x : String} {e : Expr} {ty : Ty} {ms : MemSide isaLSE2} {A x29 ra tp : BitVec 64}

/-- **`wc_waitLoop`'s limit load is in `FlagW`**: it loads `tp + 8`, not the flag's word (`htp8`), at a pc off
`q`. -/
theorem tlsW_flagH (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hpc : (N (_root_.Executable.labels exe).label Spike.Lib.A64.HelloLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls).pc =
      (_root_.Executable.labels exe).label (Spike.Lib.A64.HelloLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hflag : RunsNe (_root_.Executable.labels exe).label q (flagRuns Spike.Lib.A64.HelloLabels.pfx))
    (htp8 : tp + 8#64 ≠ A) (h0 : Flag0 lbl lsize c0 A) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label Spike.Lib.A64.HelloLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls) := by
  refine nodeW_flag h0 (fun _ _ hJ => .inl hJ.1.1) (fun s ⟨he, hn, hdc, hs, σ, hA, _, hJ⟩ kl k' hx => ?_)
    fun s ⟨_, _, _, hs, _⟩ hq' => absurd hq' <| runsNe_at hflag (p := s.st.2) (l := "wc_waitLoop") (lo := 0)
      (hi := 10) (c := 2) (by simp [flagRuns]) (by omega) (by omega)
      (by rw [hs]; simp only [N, Int64.add_assoc]; first | rfl | simp)
  have hcell : CellAt s (ldrDir .X10 .X10 8) 4 :=
    (code_of hp hend Spike.Lib.A64.Flow.Worker.Hello.AbOffAt.wait_tlsCode hpc.symm s he hn).cell (j := 0) rfl rfl
      rfl (by rw [hs]; simp)
  have ha : rAddr s.st.1.regs .X10 8 = tp + 8#64 := by
    rw [hA.regs]; exact Spike.Lib.A64.Flow.Ret0.rAddr_x10 hJ.2 8
  cases hm : Mem.loadInt s.st.1.dmem (tp + 8#64) 8 with
  | some j => rw [exec_ldr_mapped hcell ha hm] at hx; cases hx
  | none =>
    rw [exec_ldr_agrees hcell ha hm (agrees_of_decls hdc _ _)] at hx
    injection hx with hx
    injection hx with _ _ hL
    injection hL with hA
    exact (htp8 hA).elim

/-- **`wc_waitLoop`'s limit load inside `mainWRH`** (`seg_waitTlsW`'s `hW` at hello): `A64WakeMainW.tlsW_main`,
`tlsW_relWH`, `A64WakeMainL.tlsW_ctl` at `LabMapped` (`hm0`), `tlsW_sysH` and `tlsW_flagH` (the loop's control at
`wlBody`, `hwb`; its flag word inside its label, `hin`; `tp + 8` outside every placed label, `hrt8`; `hflag`). -/
theorem tlsW_mainRH {Λ : Scc.Sem.Layout} {cv : String} {a : CoreTerm.At} {w : TermRun.Word}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hpc : (N (_root_.Executable.labels exe).label Spike.Lib.A64.HelloLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls).pc =
      (_root_.Executable.labels exe).label (Spike.Lib.A64.HelloLabels.pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hruns : Spike.Lib.A64WakeOff.RunsOffA (_root_.Executable.labels exe).label
      (Spike.Lib.A64WakeMainW.waitRuns Spike.Lib.A64.HelloLabels.pfx))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → Spike.Lib.A64.WideKeep.WideX exe s)
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hm0 : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c0)
    (hflag : RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (Spike.Lib.A64.HelloLabels.pfx ++ ".0_entry") + 4 + 4)
      (flagRuns Spike.Lib.A64.HelloLabels.pfx))
    (hrt8 : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains (tp + 8#64).toNat)
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    NodeW (Spike.Lib.HelloMainInv.mainWRH (_root_.Executable.labels exe).label exe Λ lbl lsize) (fun _ _ => False)
      exe endPc R F (N (_root_.Executable.labels exe).label Spike.Lib.A64.HelloLabels.pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls) :=
  (Spike.Lib.A64WakeMainW.tlsW_main hruns hwide hc0 hfv0 hl hloc).and
    ((tlsW_relWH hp hend hpc).and
      ((Spike.Lib.A64WakeMainL.tlsW_ctl hm0).and ((tlsW_sysH hp hend hpc).and
        (tlsW_flagH hp hend hpc hflag (Spike.Lib.A64WakeMainF.tp8_ne hrt8 hloc hin)
          (Spike.Lib.A64WakeMainF.flag0_of hwb hterm hev hloc hin)))))

end Tls

end Spike.Lib.A64HelloMainRS

/-- info: 'Spike.Lib.A64HelloMainRS.parentW_relWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainRS.parentW_relWH
/-- info: 'Spike.Lib.A64HelloMainRS.parentW_sysH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainRS.parentW_sysH
/-- info: 'Spike.Lib.A64HelloMainRS.exitW1_relWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainRS.exitW1_relWH
/-- info: 'Spike.Lib.A64HelloMainRS.exitW0_sysH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainRS.exitW0_sysH
/-- info: 'Spike.Lib.A64HelloMainRS.tlsW_mainRH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainRS.tlsW_mainRH
