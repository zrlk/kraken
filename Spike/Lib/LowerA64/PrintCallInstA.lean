/-
**An output call, assembled, the per-call premises discharged** (AArch64;
the twin of `Spike/Lib/LowerX64/PrintCallInstA.lean`): `printCallC_instJ`,
`printCallCH_instJ` (`Spike/Lib/LowerA64/PrintCallInstJ.lean`) over
`printCallC_ofA`, `printCallCH_ofA`, which give `print`'s states the
caller's slots along the argument block (`PrintSlotsA`) and the count's
bound (`PrintLen`). The frames along the block follow from those slots
(`printArgW_framesJ`: the block writes only its fresh registers' slots,
`printArgs_take`), `PrintCallOkR` at the call states from the region, the
count's bound and the return address after the `bl` (`printCallOkR_of`:
in the phase of `print`'s `done` `hraP`, off the write abort `hraAb`, both per
`bl print`; `hraP_of_blC2`, `hraAb_of_blC2` from `BlC2`). What stays:
the continuation free of `ZBad` (`hNoS`) and the write tail at `print`'s
system-call states (`hDtP`, trivial at `Dt := fun _ => True`).

- `framesPlaced_ofSlotRep`: the frames with the caller's placed at a state
  whose abstract slots place the caller's control (`framesPlaced_ofSlotRepS`:
  at any slot file the state's cells hold);
- `printArgW_framesJ`: `hfpJ` from `PrintSlotsA`;
- `printCallOkR_of`: `hcall`, `hcallE` from `PrintLen`, `hraP`, `hraAb`;
- `printW_hPWA`, `printWE_hPWEA`: `printCallC_ofA`'s `hPW`, `hPWE` inside
  `W2`;
- `printCallC_instA`, `printCallCH_instA`: at `PrintCallC`, `PrintCallCH`.
-/
import Spike.Lib.LowerA64.PrintCallInstJ
import Spike.Lib.LowerA64.PrintStepK
import Spike.Lib.LowerA64.AllocRa
import Spike.Lib.LowerA64.PrintCallOkF

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At okBlk FStable AI AS Abs SO)
open Spike.Lib.A64.Rt (InstOk)
open Spike.Lib.A64.Flow.Ret0 (StackOff)
open Spike.Lib.A64.Flow.Ret0.Inst (stackOff_callee)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0 SlotRepAt)
open Spike.Lib.LowerShape (printInsts)
open Spike.Lib.A64.Flow.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.PrintSrc (printLD)
open Spike.Lib.A64.StubW (printPhOk)
open Spike.Lib.A64.PrintG (printPhOkF)
open Spike.Lib.ByteOut (ByteOut)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **The caller's frame placed at a slot file the state holds**: `R`'s
cells at the frame's slots holding `sl` (`hsl`), `sl` holding the caller's
control `c1` with `x` bound to `` before `e` (`SlotRepAt`), on frames `fs`
placed (as `framesPlaced_ofSlotRep`, the cells given directly). -/
theorem framesPlaced_ofSlotRepS {cx : FnCtx} {s : State} {sl : Int → BitVec 64} {x : String}
    {e : Expr} {c1 : Ctl}
    (hsl : ∀ r k, rsOf cx r = some k → ∃ j, Mem.loadInt s.st.1.dmem (R.addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k)
    (hsr : SlotRepAt (fun _ => Λ.imms e) lbl (rsOf cx) sl { c1 with term := .let_ x (.atom .unit) e })
    {A2 : Nat → Prop} (h2 : FramesPlacedInI Λ lbl s fs A2) :
    ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := by
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf cx r = some k ∧ a = (R.addr k).toNat
  have hsp : SlotPlacedI Λ lbl s { c1 with term := .let_ x (.atom .unit) e } A1 e := by
    refine slotPlacedI_of_slotRepAt (addr := R.addr) hsr ?_ (fun r k hk => ⟨r, k, hk, rfl⟩)
    intro r k hk
    obtain ⟨jj, hl, hv⟩ := hsl r k hk
    show (s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64) = _
    rw [hl, Option.map_some, hv]
  have h1 : FramesPlacedInI Λ lbl s [printFrame x e c1] A1 :=
    FramesPlacedInI.push hsp (FramesPlacedInI.nil A1) rfl rfl rfl rfl
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

/-- **The frames with the caller's placed** at a state whose abstract slots
`σ` (`Abs`) place the caller's control `c1` with `x` bound to `` before
`e`, on the frames `fs` placed there (`framesPlaced_printFJ` without the
call's `CKept`). -/
theorem framesPlaced_ofSlotRep {cx : FnCtx} (hf : FrameOk cx) (hlo : R.lo ≤ -(cx.frame : Int) - 48)
    (hhi : 0 ≤ R.hi) {x : String} {e : Expr} {c1 : Ctl} {s : State} {o : SO} {σ : AS}
    (hA : Abs R o s.st.1 σ)
    (hsr : SlotRepAt (fun _ => Λ.imms e) lbl (rsOf cx) σ.slot { c1 with term := .let_ x (.atom .unit) e })
    (hFP : ∃ A, FramesPlacedInI Λ lbl s fs A) :
    ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := by
  obtain ⟨A2, h2⟩ := hFP
  have hout : ∀ r k, rsOf cx r = some k → R.Off k := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3, -⟩ := rsOf_cell hf hk
    exact (frame_outA (D := 48) hlo hhi (by decide) hk1 hk2 (by omega)).1
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf cx r = some k ∧ a = (R.addr k).toNat
  have hsp : SlotPlacedI Λ lbl s { c1 with term := .let_ x (.atom .unit) e } A1 e := by
    refine slotPlacedI_of_slotRepAt (addr := R.addr) hsr ?_ (fun r k hk => ⟨r, k, hk, rfl⟩)
    intro r k hk
    obtain ⟨jj, hl, hv⟩ := hA.slot k (hout r k hk)
    show (s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64) = _
    rw [hl, Option.map_some, hv]
  have h1 : FramesPlacedInI Λ lbl s [printFrame x e c1] A1 :=
    FramesPlacedInI.push hsp (FramesPlacedInI.nil A1) rfl rfl rfl rfl
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The frames along `print`'s argument block** (`printWE_w2J`'s,
`printW_w2BJ`'s `hfpJ`): at each state of the block the slots off the fresh
registers' are the entry's (`printArgs_take`), so the caller's control is
placed there (`PrintSlotsA`); the frames below by `hFP` under `F`, kept by
the block's frame writes (`hFS`). -/
theorem printArgW_framesJ {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095)
    (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi) (hFS : FStable R F)
    (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand} {Jn : AS → Ctl → Prop}
    {x : String} {e : Expr} {c1 : Ctl} (hS : PrintSlotsA lbl Λ.imms cx n Jn x e c1) :
    ∀ L, PrintCode cx n b o m cw L →
      BlkW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
        R F ⟨pc, oF cx, Jn⟩ (directives L ++ blPrintD) := by
  rintro L ⟨i1, i2, i3, i4, l1, l2, l3, l4, l5, q1, q2, q3, q4, q5, rfl⟩
  intro s σ c _ _ _ _ _ hF hJ k _ m' hAk hD
  refine ⟨?_, fun _ h => h⟩
  obtain ⟨-, hkeep⟩ := printArgs_take hf h1 q1 q2 q3 q4 q5 (_root_.Executable.labels exe).label k pc σ
  exact framesPlaced_ofSlotRep hf hlo hhi hAk
    (hS σ c hJ _ fun r j hr hne => hkeep j fun q hq => by have := rsOf_inj hq hr; subst this; exact hne)
    (hFP _ (hFS _ _ hF hD))

/-- **`PrintCallOkR` at the call states** (`printWE_w2J`'s, `printW_w2BJ`'s
`hcall`): `print`'s region and frame condition from the caller's
(`Region.callee_ok`, `Region.callee_base`, `stackOff_callee` with `pF`'s
caller cells), the count by `PrintLen`, the return address the `bl`'s
fall-through (the block's run, `arun_bl`), in the phase of `print`'s
`done` (`hraP`) and off the write abort (`hraAb`). -/
theorem printCallOkR_of {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hFO : ∀ m, F m → StackOff rS R m)
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    {kk n : Nat} {pc pc' : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    (hi : InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc')
    {lab' : Label → Int64} {Jn : AS → Ctl → Prop} (hlen : PrintLen cx lab' pc n b o m cw Jn) :
    ∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN lab' cx pc L Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(cx.frame : Int)) R) (pF (-(cx.frame : Int)) R F) σC.regs.X30.toBitVec
        σC.regs.X1.toBitVec.toNat := by
  intro L hL σC c hc
  have hg := frame_ge16 hf
  obtain ⟨l1, l2, l3, l4, l5, hL', -, -, -, -, -, k', hb⟩ := print_chunks hi
  have e := printCode_unique hL hL'
  subst e
  have hlo' : R.lo ≤ -(cx.frame : Int) + -48 := by omega
  have hkc : -(cx.frame : Int) < R.hi := by omega
  have hcb := Region.callee_base (hi' := 0) hR hlo' (by decide) hkc
  -- the return address: the `bl`'s fall-through
  have hX30 : σC.regs.X30.toBitVec =
      (pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length) + 4).toBitVec := by
    obtain ⟨σ0, -, rfl⟩ := hc
    obtain ⟨i1, i2, i3, i4, m1, m2, m3, m4, m5, q1, q2, q3, q4, q5, hq⟩ := hL'
    have hok := printCode_okBlk hf h1 h16 hL
    have hlt : (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length <
        (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD).length := by simp [blPrintD_eq]
    have htk : (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) ++ blPrintD).take
        (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length = directives (l1 ++ l2 ++ l3 ++ l4 ++ l5) :=
      List.take_left' rfl
    have hpc := Spike.Lib.A64.Flow.arun_pc lab' (am := ⟨pc, oF cx, σ0⟩) hok hlt
    rw [htk] at hpc
    have hso := (printArgs_take hf h1 q1 q2 q3 q4 q5 lab'
      (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length pc σ0).1
    rw [← hq, htk] at hso
    unfold callSt
    rw [arun_append]
    generalize hA : Spike.Lib.A64.Flow.arun lab' (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)) ⟨pc, oF cx, σ0⟩ = am
      at hpc hso
    obtain ⟨pcA, oA, σA⟩ := am
    simp only at hpc hso
    subst hpc hso
    rw [arun_bl]
    simp [Reg64s.setRegOrZr, Reg64s.setRegOrZr64, Reg64s.setXReg]
  have hpcb : pc + Int64.ofNat (4 * (directives (l1 ++ l2 ++ l3 ++ l4 ++ l5)).length) =
      pc + Int64.ofNat (4 * (directives l1).length) + Int64.ofNat (4 * (directives l2).length) +
        Int64.ofNat (4 * (directives l3).length) + Int64.ofNat (4 * (directives l4).length) +
        Int64.ofNat (4 * (directives l5).length) := by
    simp only [directives_append, List.length_append, Nat.mul_add, Int64.ofNat_add, Int64.add_assoc]
  have hra : Int64.ofBitVec σC.regs.X30.toBitVec = pc + Int64.ofNat (4 * (directives l1).length) +
      Int64.ofNat (4 * (directives l2).length) + Int64.ofNat (4 * (directives l3).length) +
      Int64.ofNat (4 * (directives l4).length) + Int64.ofNat (4 * (directives l5).length) + 4 := by
    rw [hX30, int64_ofBitVec_toBitVec, hpcb]
  refine ⟨Region.callee_ok hR hlo' (by decide) hkc (by omega), ?_, Int.le_refl _, Int.le_refl _,
    by show (-48 : Int) % 8 = 0; decide, by show (0 : Int) % 8 = 0; decide, fun m' hm' => ?_,
    hlen _ hL σC c hc, ?_, ?_⟩
  · show (R.addr (-(cx.frame : Int))).toNat % 16 = 0
    have : ((R.addr (-(cx.frame : Int))).toNat : Int) = R.base.toNat + -(cx.frame : Int) := hcb
    omega
  · exact stackOff_callee hR (by omega) hl hh hlo' (by decide) hkc (by omega) (hFO m' hm'.1) hm'.2
  · rw [hra]; exact hraP _ _ hb
  · rw [hra]; exact hraAb _ _ hb

omit [Kraken.Executable.ValidLayout exe] in
/-- **`hraAb` from calls at `BlC2`**: each `bl print`'s fall-through is
its return label's, none of the write abort's pcs (`blC2_notAb`), for a
caller other than the runtime's functions 9, 12 and 16. -/
theorem hraAb_of_blC2 [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Scc.Cert.Rt.A64.Lays exe prog kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {cx : FnCtx} (hfi : cx.fi ≠ 9 ∧ cx.fi ≠ 12 ∧ cx.fi ≠ 16) {ra0 : Int64} {Bl : Int64 → Label → Nat → Prop}
    (hBl2 : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      BlC2 prog okPc ph (_root_.Executable.labels exe).label cx ra0 pc Scc.Lower.Names.print k) :
    ∀ pc k, Bl pc Scc.Lower.Names.print k →
      pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs (_root_.Executable.labels exe).label :=
  fun _ _ h => blC2_notAb hp hpr habI hfi (hBl2 _ _ h)

/-- **`hraP` from calls at `BlC2`**: each `bl print`'s fall-through is in
the phase of `print`'s `done` (`printRa_ph`). -/
theorem hraP_of_blC2 {kp : Nat} (hp : Scc.Cert.Rt.A64.Lays exe prog kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hph : printPhOkF okPc ph (_root_.Executable.labels exe).label = true)
    {cx : FnCtx} {ra0 : Int64} {Bl : Int64 → Label → Nat → Prop}
    (hBl2 : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      BlC2 prog okPc ph (_root_.Executable.labels exe).label cx ra0 pc Scc.Lower.Names.print k) :
    ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph ((_root_.Executable.labels exe).label ".L9_scc_rt_print.7_done").toBitVec.toNat :=
  fun _ _ h => printRa_ph hp rfl hpr hph (hBl2 _ _ h)

/-- **`printCallC_ofA`'s `hPW` inside `W2`** (`printW_w2BJ` at `msOfAB`):
the frames along the block by `printArgW_framesJ`, `PrintCallOkR` by
`printCallOkR_of`, the frames inside `print` by `framesPlaced_printFJ`, the
write tail by `hDtP`. -/
theorem printW_hPWA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      (∀ L, PrintCode cx n b o m cw L → ∀ σC c, (callN (_root_.Executable.labels exe).label cx pc L
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some σC.regs.X0.toBitVec.toNat) →
      PrintSlotsA lbl Λ.imms cx n (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 (printTop0 pw wn mv)) x e c1 →
      PrintLen cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) →
      PrintSlots lbl Λ.imms cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
        (printFrame x e c1 :: fs)) K exe endPc R F
        (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize (printFrame x e c1 :: fs))
        cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk pc' hG0 hT hi hpw hSA hLen hS
  exact printW_w2BJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl hi
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs (printArgW_framesJ hf h1 hlo hhi hFS hFP hSA)
    (printCallOkR_of hf h1 h16 hR hal hlo hhi hl hh hFO hraP hraAb hi hLen)
    (framesPlaced_printFJ hf hlo hhi hS hFP) (fun _ _ _ _ _ _ _ _ _ hAt => hDtP _ _ _ _ _ _ _ hAt) rfl rfl hpw hrg hb32

/-- **`printCallC_ofA`'s `hPWE` inside `W2`** (`printWE_w2J`): as
`printW_hPWA` at `print`'s `ret `. -/
theorem printWE_hPWEA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 cx Cd Bl kk pc (printInsts n b (.reg o) m cw) pc' →
      PrintSlotsA lbl Λ.imms cx n (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs
        bufs c1 ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintLen cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) →
      PrintSlots lbl Λ.imms cx (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c
        (printFrame x e c1 :: fs)) K exe endPc R F cx pc n b o m cw
        (printJ p lbl lsize cx fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩ := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk pc' hG0 hT hi hSA hLen hS
  have hlo' : R.lo ≤ -(cx.frame : Int) := by omega
  exact printWE_w2J hI hpr habI hph hf h1 h16 hR hal hlo' hhi hl hh hsub hfit hFO hp hCd hBl hi
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs (printArgW_framesJ hf h1 hlo hhi hFS hFP hSA)
    (printCallOkR_of hf h1 h16 hR hal hlo hhi hl hh hFO hraP hraAb hi hLen)
    (framesPlaced_printFJ hf hlo hhi hS hFP)

/-- **An output call at `PrintCallC`, assembled, the per-call premises
discharged** (`printCallC_ofA` inside `W2` at `msOfAB`, its `hWL` by `printWL_w2`,
its `hPW`, `hPWE` by `printW_hPWA`, `printWE_hPWEA`): `printCallC_instJ` with `hfpJ`,
`hcall`, `hcallE` replaced by the return address's phase and position
(`hraP`, `hraAb`). -/
theorem printCallC_instA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallC_ofA hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hrg hb32
      hfs hFP fp ra tp hNoS hDtP)
    (printWE_hPWEA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hfs hFP
      fp ra tp hNoS)
    hAb

/-- **An output call at `PrintCallCH`, assembled, the per-call premises
discharged** (`printCallCH_ofA` inside `W2` at `msOfAB`, its `hWL` by `printWL_w2`,
its `hPW`, `hPWE` by `printW_hPWA`, `printWE_hPWEA`): `printCallCH_instJ` with `hfpJ`,
`hcall`, `hcallE` replaced by the return address's phase and position
(`hraP`, `hraAb`). -/
theorem printCallCH_instA {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (habI : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOkF okPc ph lab = true)
    {cx : FnCtx} (hf : FrameOk cx) (h1 : cx.frame ≤ 4095) (h16 : cx.frame % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(cx.frame : Int) - 48) (hhi : 0 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F)
    {ra0 : Int64}
    {Cd : Int64 → List Directive → Prop} {Bl : Int64 → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL prog okPc ph lab ra0 pc blk)
    (hBl : ∀ pc g k, Bl pc g k → BlC prog okPc ph lab cx ra0 pc g k ∧ PosOff prog lab pc)
    (hraP : ∀ pc k, Bl pc Scc.Lower.Names.print k →
      ph (pc + 4).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : ∀ pc k, Bl pc Scc.Lower.Names.print k → pc + 4 ∉ Spike.Lib.A64.WriteAb.abPcs lab)
    {lcx : Scc.Lower.Ctx} (hpd : p.find? (·.name == "print") = some Scc.Frontend.printExtD)
    (hd : p.find? (·.name == "printL") = some printLD) (hprog : lcx.prog = p)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} (hG0F : ∀ c0, G0 c0 → FrOk2 c0 fs) {T : Expr → Prop}
    (hTp : ∀ x g is a ts e xe, T (.let_ x (.call g is a ts) e) → lcx.externs.find? (·.1 == g) = some xe →
      g = "print" ∧ ts = [])
    (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc σC .svc) s c' → Dt s)
    {Ax : FragS isaLSE2} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label cx lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx cx Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Spike.Lib.A64.WriteAb.Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallCH_ofA hf h1 h16 hFS hR hal hlo hhi (fun _ _ h => cdOf_of_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ h => cdOf_of_blC hI (hBl _ _ _ h).1) hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isaLSE2) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 h16 hR hal (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k, -⟩ := rsOf_cell hf hk; exact ⟨h1k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hrg hb32
      hfs hFP fp ra tp hNoS hDtP)
    (printWE_hPWEA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hraP hraAb hfs hFP
      fp ra tp hNoS)
    hAb

end Spike.Lib.LowerA64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerA64.framesPlaced_ofSlotRepS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.framesPlaced_ofSlotRepS

/-- info: 'Spike.Lib.LowerA64.framesPlaced_ofSlotRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.framesPlaced_ofSlotRep

/-- info: 'Spike.Lib.LowerA64.printArgW_framesJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printArgW_framesJ

/-- info: 'Spike.Lib.LowerA64.printCallOkR_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallOkR_of

/-- info: 'Spike.Lib.LowerA64.printW_hPWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printW_hPWA

/-- info: 'Spike.Lib.LowerA64.printWE_hPWEA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printWE_hPWEA

/-- info: 'Spike.Lib.LowerA64.printCallC_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallC_instA

/-- info: 'Spike.Lib.LowerA64.printCallCH_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.printCallCH_instA

/-- info: 'Spike.Lib.LowerA64.hraP_of_blC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hraP_of_blC2

/-- info: 'Spike.Lib.LowerA64.hraAb_of_blC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerA64.hraAb_of_blC2
