/-
**hello's main after the spawn: the listing-bound node obligations**
(AArch64; the twins at hello.w's listing `SccCode.helloProg` of the lemmas
of `A64WakeMainR`, `A64WakeMainL`, `A64WakeMainS`, `A64WakeMainF` that read
wake's listing, its frame of 80 or its exit tail at `.sp0`): main's
post-spawn segments' node obligations at `RelWS`, at a control predicate,
at `MainSys` and at `FlagW`, for hello's parent (`A64HelloMainSegW.ParentW`,
frame 144), its exit tail (`exitTail 40` at `.sp1`) and `wc_waitLoop`'s
limit load (at hello's prefix `.L21_wc_waitLoop`). The loop's and the park's
obligations are wake's (generic over the prefix and the code).

- `ParentW.and`; `parentW_relW`, `parentW_ctl`, `parentW_sys`,
  `parentW_flag`.
- `exitW0_relW`, `exitW1_relW`, `exitW0_ctl`, `exitW0_sys`, `exitW0_flag`
  (the `svc` node's `exitW1_ctl`/`_sys`/`_flag` are wake's: `exitNP` is
  generic).
- `tlsW_relW`, `tlsW_sys`, `tlsW_flag`; `tlsW_mainR`: the limit load inside
  `HelloMainInv.mainWRH`.
-/
import Spike.Lib.A64HelloMainSegW
import Spike.Lib.A64WakeMainS
import Spike.Lib.A64HelloAbOffL
import Spike.Lib.HelloMainInv

namespace Spike.Lib.A64HelloMainSF

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Cert.Rt.A64 (Lays endOf)
open Scc.Sem (ValRep LocRep)
open Spike.Lib.A64.Flow
open Spike.Lib.A64.Flow.Worker.Hello.Child (cb pfxM)
open Spike.Lib.A64.Flow.Worker.Hello.Parent
open Spike.Lib.A64.Flow.Worker.Hello.MainPost (mainSp1 hello_exitIn)
open SccCode (helloProg)
open Spike.Lib.A64HelloMainSegW (ParentW)
open Spike.Lib.A64WakeMainSegW (exitNP)
open Spike.Lib.WakeInst (MainSys FlagW)
open Spike.Lib.WakeM0 (wlBody wlIf)
open Spike.Lib.A64WakeMainF (FlagOff Flag0 flagRuns blkW_off nodeW_off nodeW_flag flagOff_past runsNe_at)
open Spike.Lib.A64WakeMainS (blkW_sys nodeW_sysCell)
open Spike.Lib.A64WakeMainL (blkW_ctl)
open Spike.Lib.A64.HelloLabels (pfx)

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-! ## The parent -/

section Parent

variable {cP : Ctl} {A x29 ra tp : BitVec 64}

/-- **Two predicates' `ParentW` combine.** -/
theorem ParentW.and {W₁ W₂ : Frag isaLSE2} (h₁ : ParentW W₁ exe endPc R F cP A x29 ra tp)
    (h₂ : ParentW W₂ exe endPc R F cP A x29 ra tp) :
    ParentW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F cP A x29 ra tp where
  wcb := h₁.wcb.and h₂.wcb
  wcl := h₁.wcl.and h₂.wcl
  wbs := h₁.wbs.and h₂.wbs
  wsp := h₁.wsp.and h₂.wsp

/-- **The parent's states are in `RelWS`**, in any valid layout of
`helloProg`. -/
theorem parentW_relW [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe helloProg kp)
    (hend : endPc = endOf exe helloProg kp) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144)
    (hhi : 0 ≤ R.hi) : ParentW (fun s _ => RelWS s) exe endPc R F cP A x29 ra tp := by
  have hin := hello_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, -⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  exact {
    wcb := blkW_relW cbP_ok hR hal hlo hhi (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero]))
    wcl := blkW_relW cl_ok hR hal hlo hhi (code_of hp hend hcl (ofNat4_zero _))
    wbs := blkW_relW bs_ok hR hal hlo hhi (code_of hp hend hbs rfl)
    wsp := blkW_relW spB_ok hR hal hlo hhi (code_of hp hend hsp (ofNat4_zero _)) }

/-- **The parent's controls satisfy `P`**: each is `cP`. -/
theorem parentW_ctl {P : Ctl → Prop} (hP : P cP) :
    ParentW (fun _ c => P c) exe endPc R F cP A x29 ra tp where
  wcb := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wcl := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wbs := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
  wsp := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP

/-- **The parent's states are at no system call**, in any valid layout of
`helloProg`. -/
theorem parentW_sys [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -144) (hhi : 0 ≤ R.hi) :
    ParentW (fun s _ => MainSys s) exe endPc R F cP A x29 ra tp := by
  have hin := hello_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨hcb, -⟩, hcl⟩, hbs⟩, hsp⟩ := hin
  exact {
    wcb := blkW_sys cbP_ok hR hal hlo hhi (code_of hp hend hcb (by simp only [pN, ofNat4_succ, ofNat4_zero]))
    wcl := blkW_sys cl_ok hR hal hlo hhi (code_of hp hend hcl (ofNat4_zero _))
    wbs := blkW_sys bs_ok hR hal hlo hhi (code_of hp hend hbs rfl)
    wsp := blkW_sys spB_ok hR hal hlo hhi (code_of hp hend hsp (ofNat4_zero _)) }

/-- **The parent's states are in `FlagW`**: its control `cP` is at neither
`wlBody` nor `wlIf` (`hcPf`). -/
theorem parentW_flag {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64}
    (hcPf : cP.term ≠ wlBody ∧ cP.term ≠ wlIf) :
    ParentW (fun s c => FlagW lbl lsize q s c) exe endPc R F cP A x29 ra tp :=
  have hP : FlagOff lbl cP := ⟨hcPf.1, fun h => absurd h hcPf.2⟩
  { wcb := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wcl := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wbs := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
    wsp := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP }

end Parent

/-! ## The `exit_group` tail at `.sp1` -/

section Exit

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A x29 ra tp : BitVec 64}
  [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **The tail block's states are in `RelWS`.** -/
theorem exitW0_relW (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 48 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret) (exitTail 40) := by
  have hin := hello_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact blkW_relW (exitTail_ok (lo := 0) (hi := 48) rfl rfl) hR hal hlo hhi
    (code_of hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]))

/-- **The tail's `svc` state is in `RelWS`.** -/
theorem exitW1_relW (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F
      (exitNP (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret)) := by
  have hin := hello_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact nodeW_relW (code_of hp hend hin.2 (by
    show _ = Int64.ofBitVec ra + 4 + 4 + 4; rw [hra]; simp only [ofNat4_succ, ofNat4_zero]))
    fun _ hc => relWS_svc hc

omit [Kraken.Executable.ValidLayout exe] in
/-- **The exit tail's block's controls satisfy `P`**: past the load. -/
theorem exitW0_ctl {P : Ctl → Prop} (hP : ∀ c, Spike.Lib.A64.WaitLoop.Past c0 x e ty Rd c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret) (exitTail 40) :=
  blkW_ctl fun _ c hJ => by obtain ⟨hp, -⟩ := hJ; exact hP c hp

/-- **The exit tail's block is at no system call.** -/
theorem exitW0_sys (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) (hR : R.OK)
    (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ 0) (hhi : 48 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainSp1) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty Rd A x29 ra tp .ret) (exitTail 40) := by
  have hin := hello_exitIn
  simp only [exitIn, Bool.and_eq_true] at hin
  exact blkW_sys (exitTail_ok (lo := 0) (hi := 48) rfl rfl) hR hal hlo hhi
    (code_of hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat4_zero]))

omit [Kraken.Executable.ValidLayout exe] in
/-- **The exit tail's block is in `FlagW`**: past the load. -/
theorem exitW0_flag {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64}
    {a : At} {ms : MemSide isaLSE2} (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (Spike.Lib.A64.WaitLoop.E c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .ret)
      (exitTail 40) :=
  blkW_off fun _ _ hJ => flagOff_past hwb hterm hJ.1

end Exit

/-! ## The limit load (`.tls`) at hello's prefix -/

section Tls

variable [Kraken.Executable.ValidLayout exe] {kp : Nat}

/-- **`wc_waitLoop`'s limit load is in `RelWS`** (a plain `ldr`). -/
theorem tlsW_relW (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {n : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (pfx ++ ".stack_check") + Int64.ofNat (4 * 2)) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F n :=
  nodeW_relW (code_of hp hend Spike.Lib.A64.Flow.Worker.Hello.AbOffAt.wait_tlsCode hpc.symm)
    fun _ hc => relWS_ldr hc

/-- **The limit load is at no system call** (a plain `ldr`). -/
theorem tlsW_sys (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp) {n : ND}
    (hpc : n.pc = (_root_.Executable.labels exe).label (pfx ++ ".stack_check") + Int64.ofNat (4 * 2)) :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F n :=
  nodeW_sysCell (code_of hp hend Spike.Lib.A64.Flow.Worker.Hello.AbOffAt.wait_tlsCode hpc.symm) fun _ h => by
    cases h

open Spike.Lib.A64.WaitLoop in
/-- **`wc_waitLoop`'s limit load is in `FlagW`**: it loads `tp + 8`, not the
flag's word (`htp8`), at a pc off `q`. -/
theorem tlsW_flag {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64}
    {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {ms : MemSide isaLSE2} {A x29 ra tp : BitVec 64}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hpc : (N (_root_.Executable.labels exe).label pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls).pc =
      (_root_.Executable.labels exe).label (pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hflag : Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label q (flagRuns pfx))
    (htp8 : tp + 8#64 ≠ A) (h0 : Flag0 lbl lsize c0 A) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (N (_root_.Executable.labels exe).label pfx c0 x e ty
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

/-- **`wc_waitLoop`'s limit load inside `mainWRH`** (`seg_waitTlsW`'s `hW`
at hello): `A64WakeMainW.tlsW_main`, `tlsW_relW`, `A64WakeMainL.tlsW_ctl`
at `LabMapped` (`hm0`), `tlsW_sys` and `tlsW_flag` (the loop's control at
`wlBody`, `hwb`; its flag word inside its label, `hin`; `tp + 8` outside
every placed label, `hrt8`; `hflag`). -/
theorem tlsW_mainR {Λ : Scc.Sem.Layout}
    {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isaLSE2}
    {c0 : Ctl} {x cv : String} {a : CoreTerm.At} {e : Expr} {ty : Ty} {w : TermRun.Word}
    {A x29 ra tp : BitVec 64}
    (hp : Lays exe helloProg kp) (hend : endPc = endOf exe helloProg kp)
    (hpc : (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls).pc =
      (_root_.Executable.labels exe).label (pfx ++ ".stack_check") + Int64.ofNat (4 * 2))
    (hruns : Spike.Lib.A64WakeOff.RunsOffA (_root_.Executable.labels exe).label
      (Spike.Lib.A64WakeMainW.waitRuns pfx))
    (hwide : ∀ s : State, s.exe = exe → s.decls = {} → Spike.Lib.A64.WideKeep.WideX exe s)
    (hc0 : c0.term ≠ WakeMLive.wlRet) (hfv0 : ∀ y ∈ Scc.Sem.exprFv c0.term, y = cv)
    (hl : TermRun.lookupE c0.env cv = some (ty, [w])) (hloc : LocRep lbl w.val A.toNat 0)
    (hm0 : Spike.Lib.WakeMappedRow.LabMapped lbl (Spike.Lib.A64Consumer.K0 Λ) c0)
    (hflag : Spike.Lib.A64WakeOff.RunsNe (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label (pfx ++ ".0_entry") + 4 + 4) (flagRuns pfx))
    (hrt8 : ¬ ∃ l b, lbl l = some b ∧ (Scc.Sem.lrange lsize l b).contains (tp + 8#64).toNat)
    (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e)
    (hev : TermRun.evalAt c0.env a = some (ty, [w]))
    (hin : ∃ sa, w.val = .loc sa 0 ∧ sa.offset < lsize sa.label) :
    NodeW (HelloMainInv.mainWRH (_root_.Executable.labels exe).label exe Λ lbl lsize) (fun _ _ => False) exe
      endPc R F (Spike.Lib.A64.WaitLoop.N (_root_.Executable.labels exe).label pfx c0 x e ty
        (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A x29 ra tp .tls) :=
  (Spike.Lib.A64WakeMainW.tlsW_main hruns hwide hc0 hfv0 hl hloc).and
    ((tlsW_relW hp hend hpc).and
      ((Spike.Lib.A64WakeMainL.tlsW_ctl hm0).and ((tlsW_sys hp hend hpc).and
        (tlsW_flag hp hend hpc hflag (Spike.Lib.A64WakeMainF.tp8_ne hrt8 hloc hin)
          (Spike.Lib.A64WakeMainF.flag0_of hwb hterm hev hloc hin)))))

end Tls

end Spike.Lib.A64HelloMainSF

/-- info: 'Spike.Lib.A64HelloMainSF.parentW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainSF.parentW_relW
/-- info: 'Spike.Lib.A64HelloMainSF.parentW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainSF.parentW_sys
/-- info: 'Spike.Lib.A64HelloMainSF.exitW0_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainSF.exitW0_sys
/-- info: 'Spike.Lib.A64HelloMainSF.exitW1_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainSF.exitW1_relW
/-- info: 'Spike.Lib.A64HelloMainSF.tlsW_mainR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64HelloMainSF.tlsW_mainR
