/-
**hello's main after the spawn: the listing-bound node obligations** (x86-64; twin of
`Spike/Lib/A64HelloMainSF.lean`): the hello twins, at hello.w's cells `SccCode.helloCells`, of the lemmas of
`X64WakeMainR`, `X64WakeMainL`, `X64WakeMainS`, `X64WakeMainF` that read wake's cells, its frame or its exit
tail's node: main's post-spawn segments' node obligations at `RelWS`, at a control predicate, at `MainSys` and
at `FlagW`, for hello's parent (`X64HelloMainSegW.ParentW`, frame 128) and its exit tail
(`xExit (-48) 4 4 5` at `.x3`, the node `X64HelloMainSegW.exitNH`). The park's obligations are wake's (generic
over the code).

- `ParentW.and`; `parentW_relW`, `parentW_ctl`, `parentW_sys`, `parentW_flag`.
- `exitW0_relW`, `exitW1_relW`, `exitW0_ctl`, `exitW1_ctl`, `exitW0_sys`, `exitW1_sys`, `exitW0_flag`,
  `exitW1_flag`.

## Differences from the AArch64 version

- The parent's `ParentW` is x86-64's (`X64HelloMainSegW`): a `NodeW` field for the clone's result test (`wts`,
  a `testq`, `X64WakeMainR.relWS_test`) and the fields `wje`, `wx26` (AArch64: `wcb`, `wcl`); its bounds are
  seg_parentW's (`R.lo ≤ -128`, `16 ≤ R.hi`), with no alignment premise.
- The exit tail's node is `exitNH` (`%rbp` at offset `72`), not wake's `exitN` (`40`), so the `syscall` node's
  obligations `exitW1_ctl`, `exitW1_sys`, `exitW1_flag` are twinned here too (AArch64's are wake's, its `exitNP`
  being generic). The tail's bounds are `seg_waitExitW`'s (`R.lo ≤ 0`, `32 ≤ R.hi`).
- There are no `tlsW_relW`, `tlsW_sys`, `tlsW_flag`, `tlsW_mainR`: x86-64's limit load is the loop prologue's
  `w2` node (a `movq %fs:8`), covered by the loop's prologue obligations (as wake's `X64WakeMainS`,
  `X64WakeMainF`).
- Not twinned (unreachable from the AArch64 root, so twins only live constants): none (all 14 are live; the
  four `tls` ones have no x86-64 node, above).
-/
import Spike.Lib.X64HelloMainSegW
import Spike.Lib.X64WakeMainF

namespace Spike.Lib.X64HelloMainSF

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib (Region)
open Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Cert.Rt.X64 (Lays endOf blockAt codeAt_blockAt_lays code_field)
open Scc.Sem (ValRep)
open Spike.Lib.X64.Flow.Worker.Hello.Parent
open Spike.Lib.X64.Flow.Worker.Hello.MainPost (mainX3 hello_exitIn)
open Spike.Lib.X64HelloMainSegW (ParentW exitNH)
open Spike.Lib.X64WakeMainSegW (exitNP)
open Spike.Lib.X64WakeMainR (relWS_test)
open Spike.Lib.X64WakeMainS (MainSys blkW_sys nodeW_sysCell nodeW_sysNr)
open Spike.Lib.X64WakeMainL (blkW_ctl nodeW_ctl)
open Spike.Lib.X64WakeMainF (FlagW FlagOff blkW_off nodeW_off flagOff_past)
open Spike.Lib.X64WakeM0 (wlBody wlIf)

variable {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-! ## The parent -/

section Parent

variable {cP : Ctl} {A fp ra tp : BitVec 64}

/-- **Two predicates' `ParentW` combine.** -/
theorem ParentW.and {W₁ W₂ : Frag isa} (h₁ : ParentW W₁ exe endPc R F cP A fp ra tp)
    (h₂ : ParentW W₂ exe endPc R F cP A fp ra tp) :
    ParentW (fun s c => W₁ s c ∧ W₂ s c) exe endPc R F cP A fp ra tp where
  wts := h₁.wts.and h₂.wts
  wje := h₁.wje.and h₂.wje
  wx26 := h₁.wx26.and h₂.wx26
  wbs := h₁.wbs.and h₂.wbs
  wsp := h₁.wsp.and h₂.wsp

/-- **The parent's states are in `RelWS`**, in any valid layout of `helloCells` (the test row a
`testq`). -/
theorem parentW_relW [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    ParentW (fun s _ => RelWS s) exe endPc R F cP A fp ra tp := by
  have hin := hello_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, -⟩, b26⟩, bbs⟩, bsp⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)},
      blockAt SccCode.helloCells l k off b = true → ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)},
      blockAt SccCode.helloCells l k 0 b = true → ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l) b :=
    fun h s he hn => by simpa using code h s he hn
  exact {
    wts := nodeW_relW (fun s he hn => code bts s he hn) fun _ hc => relWS_test hc
    wje := blkW_relW jeB_ok hR hlo hhi (fun s he hn => code bje s he hn)
    wx26 := blkW_relW x26B_ok hR hlo hhi (fun s he hn => code0 b26 s he hn)
    wbs := blkW_relW bsB_ok hR hlo hhi (fun s he hn => code bbs s he hn)
    wsp := blkW_relW spB_ok hR hlo hhi (fun s he hn => code0 bsp s he hn) }

/-- **The parent's controls satisfy `P`**: each is `cP`. -/
theorem parentW_ctl {P : Ctl → Prop} (hP : P cP) :
    ParentW (fun _ c => P c) exe endPc R F cP A fp ra tp where
  wts := nodeW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wje := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wx26 := blkW_ctl fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
  wbs := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
  wsp := blkW_ctl fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP

/-- **The parent's states are at no system call**, in any valid layout of `helloCells`. -/
theorem parentW_sys [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) (hR : R.OK) (hlo : R.lo ≤ -128) (hhi : 16 ≤ R.hi) :
    ParentW (fun s _ => MainSys s) exe endPc R F cP A fp ra tp := by
  have hin := hello_parentIn
  simp only [parentIn, Bool.and_eq_true] at hin
  obtain ⟨⟨⟨⟨⟨bts, bje⟩, -⟩, b26⟩, bbs⟩, bsp⟩ := hin
  have code : ∀ {l : Label} {k off : Nat} {b : List (Directive × Nat)},
      blockAt SccCode.helloCells l k off b = true → ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l + Int64.ofNat off) b :=
    fun h s he hn => codeAt_blockAt_lays hp he (hn.trans hend) h
  have code0 : ∀ {l : Label} {k : Nat} {b : List (Directive × Nat)},
      blockAt SccCode.helloCells l k 0 b = true → ∀ s : State, s.exe = exe → s.endPc = endPc →
        CodeAt s ((_root_.Executable.labels exe).label l) b :=
    fun h s he hn => by simpa using code h s he hn
  exact {
    wts := nodeW_sysCell (fun s he hn => code bts s he hn) fun _ _ h => by cases h
    wje := blkW_sys jeB_ok hR hlo hhi (fun s he hn => code bje s he hn)
    wx26 := blkW_sys x26B_ok hR hlo hhi (fun s he hn => code0 b26 s he hn)
    wbs := blkW_sys bsB_ok hR hlo hhi (fun s he hn => code bbs s he hn)
    wsp := blkW_sys spB_ok hR hlo hhi (fun s he hn => code0 bsp s he hn) }

/-- **The parent's states are in `FlagW`**: its control `cP` is at neither `wlBody` nor `wlIf`
(`hcPf`). -/
theorem parentW_flag {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64}
    (hcPf : cP.term ≠ wlBody ∧ cP.term ≠ wlIf) :
    ParentW (fun s c => FlagW lbl lsize q s c) exe endPc R F cP A fp ra tp :=
  have hP : FlagOff lbl cP := ⟨hcPf.1, fun h => absurd h hcPf.2⟩
  { wts := nodeW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wje := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wx26 := blkW_off fun _ _ hJ => by obtain ⟨⟨rfl, -⟩, -⟩ := hJ; exact hP
    wbs := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP
    wsp := blkW_off fun _ _ hJ => by obtain ⟨rfl, -⟩ := hJ; exact hP }

end Parent

/-! ## The `exit_group` tail at `.x3` -/

section Exit

variable {c0 : Ctl} {x : String} {e : Expr} {ty : Ty} {Rd : TermRun.Word → Prop} {A fp ra tp sp : BitVec 64}

/-- **The tail block's states are in `RelWS`** (`%rbp` at offset `72`, the spill cell `24`). -/
theorem exitW0_relW [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) (hR : R.OK) (hlo : R.lo ≤ 0) (hhi : 32 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3) :
    BlkW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F (exitNH c0 x e ty Rd A fp ra tp sp)
      (xExit (-48) 4 4 5) := by
  have hin := hello_exitIn
  rw [exitIn, Bool.and_eq_true] at hin
  exact blkW_relW (xExit_ok (lo := 0) (hi := 32) (-48) 4 4 5 (by decide)) hR hlo hhi
    (code_field hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat_zero']))

/-- **The tail's `syscall` state is in `RelWS`.** -/
theorem exitW1_relW [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3) :
    NodeW (fun s _ => RelWS s) (fun _ _ => False) exe endPc R F (exitNP (exitNH c0 x e ty Rd A fp ra tp sp)) := by
  have hin := hello_exitIn
  rw [exitIn, Bool.and_eq_true] at hin
  exact nodeW_relW (code_field hp hend hin.2 (by
    show _ = Int64.ofBitVec ra + _ + _ + _; rw [ofNat_add', ofNat_add', hra]))
    fun _ hc => relWS_syscall hc

/-- **The exit tail's block's controls satisfy `P`**: past the load. -/
theorem exitW0_ctl {P : Ctl → Prop} (hP : ∀ c, WaitLoop.Past c0 x e ty Rd c → P c) :
    BlkW (fun _ c => P c) (fun _ _ => False) exe endPc R F (exitNH c0 x e ty Rd A fp ra tp sp)
      (xExit (-48) 4 4 5) :=
  blkW_ctl fun _ c hJ => by obtain ⟨hp, -⟩ := hJ; exact hP c hp

/-- **The exit tail's `syscall` control satisfies `P`**: past the load. -/
theorem exitW1_ctl {P : Ctl → Prop} (hP : ∀ c, WaitLoop.Past c0 x e ty Rd c → P c) :
    NodeW (fun _ c => P c) (fun _ _ => False) exe endPc R F (exitNP (exitNH c0 x e ty Rd A fp ra tp sp)) :=
  nodeW_ctl fun _ c hJ => by obtain ⟨-, -, ⟨hp, -⟩, -⟩ := hJ; exact hP c hp

/-- **The exit tail's block is at no system call.** -/
theorem exitW0_sys [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe SccCode.helloCells kp)
    (hend : endPc = endOf exe SccCode.helloCells kp) (hR : R.OK) (hlo : R.lo ≤ 0) (hhi : 32 ≤ R.hi)
    (hra : Int64.ofBitVec ra = (_root_.Executable.labels exe).label mainX3) :
    BlkW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F (exitNH c0 x e ty Rd A fp ra tp sp)
      (xExit (-48) 4 4 5) := by
  have hin := hello_exitIn
  rw [exitIn, Bool.and_eq_true] at hin
  exact blkW_sys (xExit_ok (lo := 0) (hi := 32) (-48) 4 4 5 (by decide)) hR hlo hhi
    (code_field hp hend hin.1 (by show _ = Int64.ofBitVec ra; rw [hra, ofNat_zero']))

/-- **The tail's `syscall` is `exit_group`** (`%rax = 231`). -/
theorem exitW1_sys :
    NodeW (fun s _ => MainSys s) (fun _ _ => False) exe endPc R F (exitNP (exitNH c0 x e ty Rd A fp ra tp sp)) :=
  nodeW_sysNr fun _ _ hJ => .inr hJ.1

variable {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {q : Int64} {a : At}
  {ms : MemSide isa}

/-- **The exit tail's block is in `FlagW`**: past the load. -/
theorem exitW0_flag (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    BlkW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (exitNH c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A fp ra tp sp) (xExit (-48) 4 4 5) :=
  blkW_off fun _ _ hJ => flagOff_past hwb hterm hJ.1

/-- **The exit tail's `syscall` state is in `FlagW`**: past the load. -/
theorem exitW1_flag (hwb : c0.term = wlBody) (hterm : c0.term = .let_ x (.load true a) e) :
    NodeW (fun s c => FlagW lbl lsize q s c) (fun _ _ => False) exe endPc R F
      (exitNP (exitNH c0 x e ty (fun w' => ms.rd w' ∧ ValRep lbl w'.val 1) A fp ra tp sp)) :=
  nodeW_off fun _ _ ⟨_, _, hJ, _⟩ => flagOff_past hwb hterm hJ.1

end Exit

end Spike.Lib.X64HelloMainSF

/-- info: 'Spike.Lib.X64HelloMainSF.parentW_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainSF.parentW_relW
/-- info: 'Spike.Lib.X64HelloMainSF.parentW_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainSF.parentW_sys
/-- info: 'Spike.Lib.X64HelloMainSF.exitW0_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainSF.exitW0_sys
/-- info: 'Spike.Lib.X64HelloMainSF.exitW1_relW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloMainSF.exitW1_relW
