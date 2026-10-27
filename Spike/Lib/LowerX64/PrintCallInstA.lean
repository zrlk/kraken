/-
**An output call, assembled with the frames and the call facts from the
block** (x86-64): `printCallC_instJ`, `printCallCH_instJ`
(`Spike/Lib/LowerX64/PrintCallInstJ.lean`) over `printCallC_ofA`,
`printCallCH_ofRA` (`Spike/Lib/LowerX64/PrintCallC2.lean`,
`Spike/Lib/LowerX64/PrintCallC2H.lean`), whose caller's slots along the
argument block (`PrintSlotsA`) and count's bound (`PrintLen`) give the
frames along the block and `PrintCallOkR` with no premise per call.

- `framesPlaced_ofSlotRep`: the caller's frame `printFrame x e c1` placed at
  an abstract state's slots holding its control, on frames `fs` placed
  (`framesPlaced_ofSlotRepS`: at any slot file the state's cells hold);
- `printArgW_framesJ`: the frames at the argument block's four pieces'
  states (the block writes only its fresh registers' slots, `preD_take`,
  `postD_take`).
-/
import Spike.Lib.LowerX64.PrintCallInstJ
import Spike.Lib.LowerX64.PrintStepK
import Spike.Lib.LowerX64.AllocRa

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Lower.InvX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND AS At FStable Abs DFrame arun)
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.Flow.Ret0 (StackOff)
open Spike.Lib.LowerNode (FrOk2 ZBad printFrame LblRange printTop0 SlotRepAt)
open Spike.Lib.X64.PrintCall (pN pR pF pcS pFJ)
open Spike.Lib.X64.PrintG (printPhOk)
open Spike.Lib.X64.WriteAb (Ab)
open Spike.Lib.ByteOut (ByteOut)
open Spike.Lib.LowerShape (printInsts)
open Scc.Lower.Inv (regName)
open Spike.Lib.PrintSrc (printLD)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range}
  {R : Region} {F : MachineData → Prop}
  {p : Prog} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {ar : Arena} {J : InvS}
  {Dt : State → Prop} {lbl : Lbl} {lsize : Lsize} {fs : List TermRun.Frame}

/-- **The caller's frame placed at a slot file the state holds**: `R`'s
cells at the frame's slots holding `sl` (`hsl`), `sl` holding the caller's
control `c1` with `x` bound to `()` before `e` (`SlotRepAt`), on frames `fs`
placed (as `framesPlaced_ofSlotRep`, the cells given directly). -/
theorem framesPlaced_ofSlotRepS {fr : Scc.Emit.X64.Frame} {s : State} {sl : Int → BitVec 64} {x : String}
    {e : Expr} {c1 : Ctl}
    (hsl : ∀ r k, rsOf fr r = some k → ∃ j, Mem.loadInt s.st.1.dmem (R.addr k) 8 = some j ∧ BitVec.ofInt 64 j = sl k)
    (hsr : SlotRepAt (fun _ => Λ.imms e) lbl (rsOf fr) sl { c1 with term := .let_ x (.atom .unit) e })
    {A2 : Nat → Prop} (h2 : FramesPlacedInI Λ lbl s fs A2) :
    ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := by
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf fr r = some k ∧ a = (R.addr k).toNat
  obtain ⟨envm, hrep, htot', hpl, himm'⟩ := placedPf_of_slotRep (s := s)
    (pf := fun k => .slot (R.addr k).toNat) hsr fun r k hk => by
      obtain ⟨jj, hl, hv⟩ := hsl r k hk
      show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      show ((s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
      rw [hl, Option.map_some, hv]; rfl
  have hsp : SlotPlacedI Λ lbl s { c1 with term := .let_ x (.atom .unit) e } A1 e := by
    refine ⟨envm, hrep, htot', fun y k wp hem qq hq => ?_, himm'⟩
    obtain ⟨r, k', hk', rfl⟩ := hpl y k wp hem qq hq
    exact ⟨_, rfl, r, k', hk', rfl⟩
  have h1 : FramesPlacedInI Λ lbl s [printFrame x e c1] A1 :=
    Spike.Lib.X64ConsumerS.FramesPlacedInI.push hsp (Spike.Lib.X64ConsumerS.FramesPlacedInI.nil A1) rfl rfl rfl rfl
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The caller's frame placed at an abstract state's slots**: the machine
data at `σ` in `R` (`Abs`), `σ`'s slots holding the caller's control `c1`
with `x` bound to `()` before `e` (`SlotRepAt`), on frames `fs` placed
(`placedPf_of_slotRep`, as `framesPlaced_printFJ` at the state itself). -/
theorem framesPlaced_ofSlotRep {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (hlo : R.lo ≤ -(fr.size : Int) - 8)
    (hhi : 0 ≤ R.hi) {o : Spike.Lib.X64.SO} {s : State} {σ : AS} {x : String} {e : Expr} {c1 : Ctl}
    (hA : Abs R o s.st.1 σ)
    (hsr : SlotRepAt (fun _ => Λ.imms e) lbl (rsOf fr) σ.slot { c1 with term := .let_ x (.atom .unit) e })
    {A2 : Nat → Prop} (h2 : FramesPlacedInI Λ lbl s fs A2) :
    ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := by
  have hoff : ∀ r k, rsOf fr r = some k → R.Off k := by
    intro r k hk
    obtain ⟨hk1, hk2, hk3⟩ := rsOf_bounds hf hk
    simp only [Region.Off]
    omega
  let A1 : Nat → Prop := fun a => ∃ r k, rsOf fr r = some k ∧ a = (R.addr k).toNat
  obtain ⟨envm, hrep, htot', hpl, himm'⟩ := placedPf_of_slotRep (s := s)
    (pf := fun k => .slot (R.addr k).toNat) hsr fun r k hk => by
      obtain ⟨jj, hl, hv⟩ := hA.slot k (hoff r k hk)
      show (Scc.Sem.X64.privLoad s (BitVec.ofNat 64 (R.addr k).toNat)).map (·.toNat) = _
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      show ((s.st.1.dmem.loadInt (R.addr k) 8).map (BitVec.ofInt 64)).map (·.toNat) = _
      rw [hl, Option.map_some, hv]; rfl
  have hsp : SlotPlacedI Λ lbl s { c1 with term := .let_ x (.atom .unit) e } A1 e := by
    refine ⟨envm, hrep, htot', fun y k wp hem qq hq => ?_, himm'⟩
    obtain ⟨r, k', hk', rfl⟩ := hpl y k wp hem qq hq
    exact ⟨_, rfl, r, k', hk', rfl⟩
  have h1 : FramesPlacedInI Λ lbl s [printFrame x e c1] A1 :=
    Spike.Lib.X64ConsumerS.FramesPlacedInI.push hsp (Spike.Lib.X64ConsumerS.FramesPlacedInI.nil A1) rfl rfl rfl rfl
  exact ⟨fun a => A1 a ∨ A2 a, FramesPlacedInI.cons1 (h1.mono fun _ h => .inl h) (h2.mono fun _ h => .inr h)⟩

omit [Kraken.Executable.ValidLayout exe] in
/-- **The frames at the argument block's four pieces' states**: every
prefix of the block writes only its fresh registers' slots (`preD_take`,
`postD_take`; the multiply none), so each piece's state has the slots of
the block's entry state off them, where the caller's control is placed
(`PrintSlotsA`); the caller's frame there (`framesPlaced_ofSlotRep`) on the
frames `fs` placed under `F` (`hFP`, kept off the region, `hFS`). -/
theorem printArgW_framesJ {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 0 ≤ R.hi) (hFS : FStable R F)
    (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {Jn : AS → Ctl → Prop} {x : String} {e : Expr} {c1 : Ctl}
    (hS : PrintSlotsA lbl Λ.imms fr n Jn x e c1) {B : PBlk} (hB : PrintCodeC fr Cd Bl kk pc n b o m cw B) :
    PrintArgW (fun s _ => ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A) (fun _ _ => False) exe endPc
      R F fr B Jn := by
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, zs1, zs2, zM, zc, hlo1, hs1, hcap1, hk1,
    hO, hBo, hL, hM, h8', hN, hC, hN', hC', hSo, hKk, hz1, hz2, rfl⟩ := hB.toPrintCode
  have hag : ∀ (σ0 : AS) (sl : Int → BitVec 64),
      (∀ j, j ≠ olo → j ≠ os → j ≠ ocap → j ≠ okk → sl j = σ0.slot j) →
      ∀ r j, rsOf fr r = some j → r ≠ regName "lo" n ∧ r ≠ regName "s" (n + 1) ∧ r ≠ regName "cap" (n + 2) ∧
        r ≠ regName "k" (n + 3) → sl j = σ0.slot j := by
    intro σ0 sl h r j hr ⟨n1, n2, n3, n4⟩
    exact h j (fun he => n1 (rsOf_inj hf hr (by rw [he]; exact hlo1)))
      (fun he => n2 (rsOf_inj hf hr (by rw [he]; exact hs1)))
      (fun he => n3 (rsOf_inj hf hr (by rw [he]; exact hcap1)))
      (fun he => n4 (rsOf_inj hf hr (by rw [he]; exact hk1)))
  have hfr : ∀ (s : State) (o' : Spike.Lib.X64.SO) (σ0 σ' : AS) c, Jn σ0 c → Abs R o' s.st.1 σ' → F s.st.1 →
      (∀ j, j ≠ olo → j ≠ os → j ≠ ocap → j ≠ okk → σ'.slot j = σ0.slot j) →
      ∃ A, FramesPlacedInI Λ lbl s (printFrame x e c1 :: fs) A := fun s o' σ0 σ' c hJ hA hF hk =>
    framesPlaced_ofSlotRep hf hlo hhi hA (hS σ0 c hJ σ'.slot (hag σ0 σ'.slot hk)) (hFP s hF).choose_spec
  let lab' := (_root_.Executable.labels exe).label
  have hpre : ∀ (q : Int64) (σ0 : AS) j, j ≠ olo → j ≠ os →
      (arun lab' ((preD lO lB lL lM l8 olo os).zip zs1) ⟨q, oB fr, σ0⟩).σ.slot j = σ0.slot j := by
    intro q σ0 j ha hb
    obtain ⟨pc', σ', e', hk⟩ := preD_take hf h1 lab' hlo1 hs1 hO hBo hL hM h8' zs1
      ((preD lO lB lL lM l8 olo os).zip zs1).length q σ0
    rw [List.take_length] at e'
    rw [e']
    exact hk j ha hb
  have hpost : ∀ (q : Int64) (σ0 : AS) j, j ≠ ocap → j ≠ okk →
      (arun lab' ((postD lN lC lN' lC' lS lK ocap okk).zip zs2) ⟨q, oB fr, σ0⟩).σ.slot j = σ0.slot j := by
    intro q σ0 j ha hb
    obtain ⟨pc', σ', e', hk⟩ := postD_take hf h1 lab' hcap1 hk1 hN hC hN' hC' hSo hKk zs2
      ((postD lN lC lN' lC' lS lK ocap okk).zip zs2).length q σ0
    rw [List.take_length] at e'
    rw [e']
    exact hk j ha hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s σ c _ _ _ _ _ hF hJ k _ mm hA' hD
    obtain ⟨pc', σ', e', hk⟩ := preD_take hf h1 lab' hlo1 hs1 hO hBo hL hM h8' zs1 k pc σ
    change Abs R (arun lab' (List.take k ((preD lO lB lL lM l8 olo os).zip zs1)) ⟨pc, oB fr, σ⟩).so mm
      (arun lab' (List.take k ((preD lO lB lL lM l8 olo os).zip zs1)) ⟨pc, oB fr, σ⟩).σ at hA'
    rw [e'] at hA'
    exact ⟨hfr _ _ σ σ' c hJ hA' (hFS _ _ hF hD) fun j ha hb _ _ => hk j ha hb, fun _ h => h⟩
  · rintro s c ⟨-, -, -, -, σ, hA, hF, σ0, hJ0, rfl⟩
    exact ⟨hfr s _ σ0 _ c hJ0 hA hF fun j ha hb _ _ => hpre pc σ0 j ha hb, fun _ h => h⟩
  · rintro s σ c - - - - - hF ⟨σ0, fl, hJ0, rfl⟩ k - mm hA' hD
    obtain ⟨pc', σ', e', hk⟩ := postD_take hf h1 lab' hcap1 hk1 hN hC hN' hC' hSo hKk zs2 k
      (pc + Int64.ofNat zs1.sum + Int64.ofNat zM)
      (mulFI.step (arun lab' ((preD lO lB lL lM l8 olo os).zip zs1) ⟨pc, oB fr, σ0⟩).σ fl)
    change Abs R (arun lab' (List.take k ((postD lN lC lN' lC' lS lK ocap okk).zip zs2))
      ⟨pc + Int64.ofNat zs1.sum + Int64.ofNat zM, oB fr,
        mulFI.step (arun lab' ((preD lO lB lL lM l8 olo os).zip zs1) ⟨pc, oB fr, σ0⟩).σ fl⟩).so mm
      (arun lab' (List.take k ((postD lN lC lN' lC' lS lK ocap okk).zip zs2))
      ⟨pc + Int64.ofNat zs1.sum + Int64.ofNat zM, oB fr,
        mulFI.step (arun lab' ((preD lO lB lL lM l8 olo os).zip zs1) ⟨pc, oB fr, σ0⟩).σ fl⟩).σ at hA'
    rw [e'] at hA'
    exact ⟨hfr _ _ σ0 σ' c hJ0 hA' (hFS _ _ hF hD) fun j ha hb hc hd => (hk j hc hd).trans (hpre pc σ0 j ha hb),
      fun _ h => h⟩
  · rintro s σ c - - - - - hF ⟨σ0, fl, hJ0, rfl⟩ k hk mm hA' hD
    obtain rfl : k = 0 := by simp at hk; omega
    exact ⟨hfr _ _ σ0 _ c hJ0 hA' (hFS _ _ hF hD) fun j ha hb hc hd =>
      (hpost _ _ j hc hd).trans (hpre pc σ0 j ha hb), fun _ h => h⟩

/-- **The return address at `print`'s entry** is the block's `call`'s
fall-through, `pc3 + zc`, in the slot below the frame. -/
theorem PBlk.stC_ra (lab' : String → Int64) (fr : Scc.Emit.X64.Frame) (B : PBlk) (σ0 : AS) (fl : StatusFlags) :
    (B.stC lab' fr σ0 fl).slot (-(fr.size : Int) - 8) = (B.pc3 + Int64.ofNat B.zc).toBitVec := by
  simp only [PBlk.stC, arun_callD]
  simp [Spike.Lib.upd_apply, oB]

/-- **The block's `call` is at `pc3`** (`PrintCodeC`'s `Bl` chunk at the
block's cells). -/
theorem PrintCodeC.bl {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk : Nat} {pc : Int64} {n : Nat} {b : Scc.IR.Operand}
    {o : Scc.IR.Reg} {m c : Scc.IR.Operand} {B : PBlk} (h : PrintCodeC fr Cd Bl kk pc n b o m c B) :
    Bl B.pc3 B.zc Scc.Lower.Names.print kk := by
  obtain ⟨olo, os, ocap, okk, lO, lB, lL, lM, l8, lN, lC, lN', lC', lS, lK, dO, dB, dL, dM, d8, dN, dC, dN', dC',
    dS, dK, a1, a2, a3, b1, b2, b3, b4, c1, c2, c3, c4, d1, d2, d3, d4, d5, d6, d7, d8', e1, e2, zc,
    -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, -, hbl, rfl⟩ := h
  simp only [pblk, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc] at hbl ⊢
  exact hbl

omit [Kraken.Executable.ValidLayout exe] in
/-- **`PrintCallOkR` at every call state** with no premise per call:
`print`'s region `pR` inside `R` from `R`'s bounds, its words of `rS` off it
from `F`'s (`stackOff_callee`, the caller's cells under `pF`), the count's
bound (`PrintLen`), and the return address, the block's `call`'s
fall-through (`PBlk.stC_ra`, `PrintCodeC.bl`), in `ra0`'s phase (`BlC`)
and so `done`'s (`hraP`), off the write abort (`hraAb`). -/
theorem printCallOkR_of {fr : Scc.Emit.X64.Frame} (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hFO : ∀ m, F m → StackOff rS R m) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    (hraP : ph ra0.toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    {kk n : Nat} {pc : Int64} {b : Scc.IR.Operand} {o : Scc.IR.Reg} {m cw : Scc.IR.Operand}
    {Jn : AS → Ctl → Prop}
    (hlen : PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw Jn) :
    ∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr Jn).J σC c →
      PrintCallOkR ph lab rS (pR (-(fr.size : Int) - 8 - 8) R) (pF (-(fr.size : Int) - 8 - 8) R F)
        (σC.slot (-(fr.size : Int) - 8)) (σC.regs.get64 .rsi).toNat := by
  intro B hB σC c hc
  have hlen' := hlen B hB σC c hc
  obtain ⟨σ0, fl, -, rfl⟩ := hc
  have hbl := hB.bl
  obtain ⟨⟨-, -, -, -, -, -, -, hph⟩, -⟩ := hBl _ _ _ _ hbl
  have hra : Int64.ofBitVec ((B.stC (_root_.Executable.labels exe).label fr σ0 fl).slot (-(fr.size : Int) - 8)) =
      B.pc3 + Int64.ofNat B.zc := by
    rw [PBlk.stC_ra]; rfl
  have hcb := Region.callee_base (hi' := 16) hR (kc := -(fr.size : Int) - 8 - 8) (lo' := -40) (by omega)
    (by omega) (by omega)
  refine ⟨Region.callee_ok hR (by omega) (by omega) (by omega) (by omega), ?_, by simp [Region.callee],
    by simp [Region.callee], by simp [Region.callee], by simp [Region.callee], ?_, hlen', ?_, ?_⟩
  · show (R.callee (-(fr.size : Int) - 8 - 8) (-40) 16).base.toNat % 8 = 0
    omega
  · rintro md ⟨hF, hcc⟩
    exact Spike.Lib.X64.Rt.stackOff_callee hR (by omega) hl hh (by omega) (by omega) (by omega) (by omega)
      (hFO md hF) hcc
  · rw [hra, hph, hraP]
  · rw [hra]; exact hraAb _ _ _ hbl

omit [Kraken.Executable.ValidLayout exe] in
/-- **`hraAb` from calls at `BlC2`**: each `call print`'s fall-through is
its return label's, none of the write abort's pcs (`blC2_notAb`). -/
theorem hraAb_of_blC2 [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Scc.Cert.Rt.X64.Lays exe cells kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} {ra0 : Int64} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hBl2 : ∀ pc z k, Bl pc z Scc.Lower.Names.print k →
      BlC2 cells okPc ph (_root_.Executable.labels exe).label fr ra0 pc z Scc.Lower.Names.print k) :
    ∀ pc z k, Bl pc z Scc.Lower.Names.print k →
      pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs (_root_.Executable.labels exe).label :=
  fun _ _ _ h => blC2_notAb hp hpr habI (hBl2 _ _ _ h)

/-- **`printCallC_ofA`'s `hPW` inside `W2`** (`printW_w2BJ` at `printJ`):
the frames along the block from the caller's slots there
(`printArgW_framesJ`), `PrintCallOkR` from the count's bound and the code
(`printCallOkR_of`), the frames inside `print` (`framesPlaced_printFJ`) and
the write tail at `print`'s system-call states, whatever the call
(`hDtP`). -/
theorem printW_hPWA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    {ownA : OwnS} {IA : InvS}
    (hrg : LblRange Λ lbl lsize) (hb32 : ∀ r ∈ Λ.rodata :: Λ.regions, r.lo + r.size ≤ 2 ^ 32)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hraP : ph ra0.toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (pw wn : TermRun.Word) (nv mv : Nat)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      (∀ B, PrintCodeC fr Cd Bl kk pc n b o m cw B → ∀ σC c, (B.nC (_root_.Executable.labels exe).label fr
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv))).J σC c →
        ∃ l, pw.val = .loc ⟨l, 0⟩ 0 ∧ lbl l = some (σC.regs.get64 .rdi).toNat) →
      PrintSlotsA lbl Λ.imms fr n (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits
        cs bufs c1 (printTop0 pw wn mv)) x e c1 →
      PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) x e c1 →
      PrintW' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize (printFrame x e c1 :: fs)) fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          (printTop0 pw wn mv)) pw wn nv mv := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 pw wn nv mv kk kk' pc' hG0 hT hi hpw hSA hlen hS
  exact printW_w2BJ hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hCd hBl
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs (fun _ hB => printArgW_framesJ hf h1 (by omega) (by omega) hFS hFP hSA hB)
    (printCallOkR_of h16 hR hal hlo hhi hl hh hFO hBl hraP hraAb hlen)
    (framesPlaced_printFJ hf hlo hhi hS hFP) (fun _ _ _ _ _ _ _ s c' hAt => hDtP _ _ _ _ _ _ s c' hAt) rfl rfl hpw
    hrg hb32

/-- **`printCallC_ofA`'s `hPWE` inside `W2`** (`printWE_w2J` at `printJ` at
`print`'s `ret ()`), as `printW_hPWA`. -/
theorem printWE_hPWEA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
    (hfs : ∀ fr ∈ fs, NoS ZBad fr.body) (hFP : ∀ s : State, F s.st.1 → ∃ A, FramesPlacedInI Λ lbl s fs A)
    {G0 : Ctl → Prop} {T : Expr → Prop} (fp ra : BitVec 64) (tp : UInt64)
    (hNoS : ∀ x is a e, T (.let_ x (.call "print" is a []) e) → NoS ZBad e)
    (hraP : ph ra0.toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab) :
    ∀ (c0 : Ctl) (pc : Int64) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (n : Nat) (x : String) (is : List String) (a : At) (e : Expr)
      (b : Scc.IR.Operand) (o : Scc.IR.Reg) (m cw : Scc.IR.Operand) (c1 : Ctl) (envR : TermRun.Env)
      (kk kk' : Nat) (pc' : Int64),
      G0 c0 → T (.let_ x (.call "print" is a []) e) → InstsC2 fr Cd Bl kk pc (printInsts n b (.reg o) m cw) kk' pc' →
      PrintSlotsA lbl Λ.imms fr n (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits
        cs bufs c1 ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintLen fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) →
      PrintSlots lbl Λ.imms fr Cd Bl kk (_root_.Executable.labels exe).label pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) x e c1 →
      PrintWE' (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c (printFrame x e c1 :: fs)) K exe
        endPc R F fr Cd Bl kk pc n b o m cw
        (printJ p lbl lsize fr fp ra tp c0 (.let_ x (.call "print" is a []) e) env lits cs bufs c1
          ⟨.ret .unit, envR, none⟩) ⟨.ret .unit, envR, none⟩ := by
  intro c0 pc env lits cs bufs n x is a e b o m cw c1 envR kk kk' pc' hG0 hT hi hSA hlen hS
  have hR8 : R.base.toNat % 8 = 0 := by omega
  have hlo' : R.lo ≤ -(fr.size : Int) - 8 := by omega
  exact printWE_w2J hI hpr habI hph hf h1 hR hR8 hlo' hhi hl hh hsub hfit hFO hp hCd hBl
    (fun _ _ h => h.1) (hNoS x is a e hT) hfs (fun _ hB => printArgW_framesJ hf h1 (by omega) (by omega) hFS hFP hSA hB)
    (printCallOkR_of h16 hR hal hlo hhi hl hh hFO hBl hraP hraAb hlen)
    (framesPlaced_printFJ hf hlo hhi hS hFP)

/-- **An output call at `PrintCallC`, assembled with no premise per call**
(`printCallC_ofA`, its `hPW`, `hPWE` by `printW_hPWA`, `printWE_hPWEA`):
`printCallC_instJ`'s premises with the frames along the block and
`PrintCallOkR` derived; left: the continuation free of `ZBad` (`hNoS`), the
return address's phase and write-abort facts at the function's return
address and `call`s (`hraP`, `hraAb`), the write tail (`hDtP`). -/
theorem printCallC_instA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
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
    (hraP : ph ra0.toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallC p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallC_ofA hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs hFP
      fp ra tp hNoS hraP hraAb hDtP)
    (printWE_hPWEA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra tp hNoS
      hraP hraAb)
    hAb

/-- **An output call at `PrintCallCH`, assembled with no premise per call**
(`printCallCH_ofRA`; the premises of `printCallC_instA`). -/
theorem printCallCH_instA {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habI : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (h16 : fr.size % 16 = 0)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -(fr.size : Int) - 56) (hhi : 16 ≤ R.hi)
    (hl : R.lo % 8 = 0) (hh : R.hi % 8 = 0) (hsub : rS.Sub Λ.stackPool) (hfit : rS.lo + rS.size ≤ 2 ^ 64)
    (hFO : ∀ m, F m → StackOff rS R m) (hp : ProgNoS ZBad p) (hFS : FStable R F) {ra0 : Int64}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdCL cells okPc ph lab ra0 pc blk)
    (hBl : ∀ pc z g k, Bl pc z g k → BlC cells okPc ph lab fr ra0 pc z g k ∧ PosOff cells lab pc)
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
    (hraP : ph ra0.toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : ∀ pc z k, Bl pc z Scc.Lower.Names.print k → pc + Int64.ofNat z ∉ Spike.Lib.X64.WriteAb.abPcs lab)
    (hDtP : ∀ (R' : Region) (F' : MachineData → Prop) (Pc Qc : AS → Nat → Ctl → Prop) (ko : Int) (σC : AS) s c',
      At exe endPc R' F' (pN (_root_.Executable.labels exe).label Pc Qc ko σC .sys) s c' → Dt s)
    {Ax : FragS isa} (hAb : ∀ c0 x is a e c1 s c, G0 c0 → T (.let_ x (.call "print" is a []) e) →
      At exe endPc R F (printNAS (_root_.Executable.labels exe).label fr lbl Λ.imms x e c1) s c →
      Ax s c (printFrame x e c1 :: fs)) :
    PrintCallCH p lbl lsize lcx fr Cd Bl exe endPc R F
      (fun s c fs' => W2 Λ μ p rd G own rS Tk ar J Dt (Ab lab) lbl lsize s c fs') K
      (msOfAB Λ μ p rd G ownA ar IA (Ab lab) lbl lsize) fp ra tp fs G0 Λ.imms T Ax :=
  printCallCH_ofRA hf h1 hFS hR hlo hhi (fun _ _ h => codeAt_cdC hI (hCd _ _ h).toCdC)
    (fun _ _ _ _ h => by
      obtain ⟨L, j, off, hpc, hb, -⟩ := (hBl _ _ _ _ h).1
      intro s hs hn
      have := Scc.Cert.Rt.X64.codeAt_blockAt_lays hI.lays hs (hn.trans hI.endOk) hb
      rwa [hI.labOk, hpc] at this)
    hI.lays hI.endOk hpr hpd hd hprog (fun _ => rfl)
    (fun _ s _ _ _ _ _ hr h hΦ => ByteOut.closed (I := isa) (s := s) hr h hΦ) hTp
    (printWL_w2 hI hpr habI hf h1 hR (by omega) (by omega) hhi hl hh hsub hfit hFO hp hCd hBl
      (fun _ _ hk => by obtain ⟨h1k, h2k, h3k⟩ := rsOf_bounds hf hk; exact ⟨h2k, by omega, by omega⟩) hFP
      (fun _ _ h => h) hG0F fp ra tp)
    (printW_hPWA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hrg hb32 hfs hFP
      fp ra tp hNoS hraP hraAb hDtP)
    (printWE_hPWEA hI hpr habI hph hf h1 h16 hR hal hlo hhi hl hh hsub hfit hFO hp hFS hCd hBl hfs hFP fp ra tp hNoS
      hraP hraAb)
    hAb

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.framesPlaced_ofSlotRepS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.framesPlaced_ofSlotRepS

/-- info: 'Spike.Lib.LowerX64.framesPlaced_ofSlotRep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.framesPlaced_ofSlotRep

/-- info: 'Spike.Lib.LowerX64.printArgW_framesJ' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printArgW_framesJ

/-- info: 'Spike.Lib.LowerX64.PBlk.stC_ra' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.PBlk.stC_ra

/-- info: 'Spike.Lib.LowerX64.PrintCodeC.bl' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.PrintCodeC.bl

/-- info: 'Spike.Lib.LowerX64.printCallOkR_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallOkR_of

/-- info: 'Spike.Lib.LowerX64.hraAb_of_blC2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.hraAb_of_blC2

/-- info: 'Spike.Lib.LowerX64.printW_hPWA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printW_hPWA

/-- info: 'Spike.Lib.LowerX64.printWE_hPWEA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printWE_hPWEA

/-- info: 'Spike.Lib.LowerX64.printCallC_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallC_instA

/-- info: 'Spike.Lib.LowerX64.printCallCH_instA' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.printCallCH_instA
