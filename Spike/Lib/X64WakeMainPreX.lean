/-
**`scc_rt_main` up to `call wc_main` inside the start's level at `ownGXW`**
(x86-64): `MainWf.mainPreWW_W0S`'s `MainPreWW` inside `StartWf.WS` (at
`ownG`) is inside `OwnImp.WSX` (at `ownGXW`). `scc_rt_main`'s prologue and
`.entry`'s call block run on the new stack, from `scc_rt_main` (past `.x1`)
to `wc_main`'s entry, in none of `InT`, `InC`, `InAb` (`QP`), the frame's
band `[-48, 8]` on the pool (`hb`): every state holds main's TCB word only
(`cls_pool`), and the limit's `%fs` load writes nothing (`hw_fsld`).

- `main_labs`: the labels the pcs are decided from.
- `blkLB`, `nodeLB`: `Lft` on a covered block / at a node, by the pc and
  `%rsp`'s band (`blkL2`, `nodeL2` at `Lft`).
- `proLM`, `callLM`: the prologue's and the call block's nodes inside `Lft`.
- `mainPreWWX`: `MainPreWW` inside `WSX`.

Where x86-64 differs from AArch64: AArch64's start level owns `ownG`
throughout, so `mainPreWW_W0S` is used as is there; x86-64's main also holds
its own TCB word from `.x1` on (`ownS`), so its prefix is lifted to `WSX`.
-/
import Spike.Lib.X64WakeOwnWcPreX
import Spike.Lib.X64WakeMainWf

namespace Spike.Lib.X64.WakePh.MainPreX

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks Range WriteTree)
open Scc.Sem.X64 (codeLabel pcOf abi)
open Scc.Cert.Rt.X64 (codeT_eq code_field label_labelGapB blockAtB)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs)
open Spike.Lib.X64 (ND BlkW NodeW At fsDir okBlk arun cellOff)
open Spike.Lib.X64.Flow (XProW xProN1 xProN2 xProN3 xProN4 xHead xLea xCmp xFr xHead_ok xLea_ok xCmp_ok xFr_ok
  xHead_run xLea_run xCmp_run xFr_run xS1 xS2 hdRegs prologueIn ofNat_add' ofNat_zero')
open Spike.Lib.X64.Flow.WakeM (MainPreWW wN0 wB0)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64.WakePh.OwnWc (keep_fsld hw_fsld)
open Spike.Lib.X64.WakePh.StartWf (WS)
open Kraken.Promising.Lower.X64 (CellAt fsAddr eaddr)
open Spike.Lib (Region Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

variable {L : RuntimeLayout} {a : BitVec 64} {R : Region} {F : MachineData → Prop}
  {ar : Arena} {p : Prog} {Dt Cl : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}
  {frM : TermRun.Frame} {X0 : State → Prop}

/-- The labels `scc_rt_main`'s pcs are decided from, at the canonical base. -/
theorem main_labs (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    L.lab "scc_rt_main" = Int64.ofNat 4198540 ∧ L.lab ".Lscc_rt_main.stk" = Int64.ofNat 4198601 ∧
    L.lab ".Lscc_rt_main.entry" = Int64.ofNat 4198571 ∧ L.lab "wc_main" = Int64.ofNat 4203265 := by
  refine ⟨hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_, hlab _ _ ?_⟩ <;> (rw [← codeT_eq]; decide +kernel)

/-- `hso` of a block at offsets `o`, decided. -/
local macro "soM " b:term:max o:term:max : term =>
  `(fun k hk => (show ∀ k ≤ ($b).length, -48 ≤ (soRun (($b).take k) $o).sp ∧ (soRun (($b).take k) $o).sp ≤ 8
    by decide +kernel) k hk)

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hsep ha hW

/-- **`Lft` on a covered block of wakeCells**, by the pc and `%rsp`'s band
(`blkL2` at `Lft`). -/
theorem blkLB {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P Q : Nat → Prop}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200277)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hclsQ : ∀ s : State, Q (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (h1 : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hso : ∀ j ≤ blk.length, slo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → Q (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat) :
    BlkW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lft (blkW_cstOkB hsep ha hW (fun s hs' hn => code_field L.lays rfl (hp ▸ hb) he s hs' hn) hok hR hlo
    hhi ?_ hcls h1 hso ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteV hlab]; exact hP _ (h1 j hj)
  · intro σ c hJ s m hA _ _ hs'
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hclsQ s (by unfold pcOf; rw [hs']; exact hfin σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA

omit hp hlab hsite in
/-- **`Lft` at a node** whose successors keep `%rsp` and `%rbp` `sz` bytes
on (`nodeL2` at `Lft`). -/
theorem nodeLB {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n :=
  NodeW.lft (nodeW_cstOkK hsep ha hW hcls hk hpc hso hw)

variable (hb : BandOnP L R (-48) 8)
include hb

set_option maxHeartbeats 1600000 in
/-- **`scc_rt_main`'s prologue inside `Lft`**: the limit's load at the
thread pointer `tp` (`htp`), its word unmapped under `F` (`hun`). -/
theorem proLM (hR : R.OK) (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {ms : Spike.Lib.MemSide isa} {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none) :
    XProW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F ms
      (L.lab "scc_rt_main") 32 8 ".Lscc_rt_main.stk" 5 9 3 2 4 [(.rdi, -8, 4)] J := by
  obtain ⟨eM, eK, -, -⟩ := main_labs hlab (L := L)
  have h := Spike.Lib.X64.Flow.WakeM.wake_mainIn
  simp only [Spike.Lib.X64.Flow.WakeM.wakeMainIn, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hgap, bHd⟩, bLea⟩, bLd⟩, bCmp⟩, bFr⟩, -⟩, -⟩, -⟩ := h
  have esc : L.lab ".Lscc_rt_main.chk" = L.lab "scc_rt_main" + Int64.ofNat 4 :=
    label_labelGapB L.lays (by rw [hp]; exact hgap)
  have h4 : L.lab "scc_rt_main" + 1 + 3 = L.lab ".Lscc_rt_main.chk" := by rw [esc, Int64.add_assoc]; rfl
  have e14 : L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 =
      L.lab ".Lscc_rt_main.chk" + Int64.ofNat 14 := by
    rw [h4, ← ofNat_add']
  have e19 : L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 =
      L.lab ".Lscc_rt_main.chk" + Int64.ofNat 19 := by
    rw [e14, ← ofNat_add', ← ofNat_add']
  have hxs : (xS2 32 · |>.regs.fsBase) = fun σ : Spike.Lib.X64.AS => σ.regs.fsBase := by
    funext σ; simp [xS2, xS1, hdRegs, Reg64s.set64]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine blkLB hp hlab hsite hsep ha hW (P := PP) (Q := QP) bHd (ofNat_zero' _)
      (xHead_ok (lo := -40) (hi := 0) (by decide) (Int.le_refl _)) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soM xHead (⟨0, []⟩ : Spike.Lib.X64.SO))
      (fun σ c _ => ?_)
    · intro k hk; show PP (L.lab "scc_rt_main" + Int64.ofNat (cellOff xHead k)).toBitVec.toNat
      rw [eM]; revert k; decide +kernel
    · rw [xHead_run]; show QP (L.lab "scc_rt_main" + 1 + 3).toBitVec.toNat; rw [eM]; decide +kernel
  · refine blkLB hp hlab hsite hsep ha hW (P := PP) (Q := QP) bLea
      (by show _ = L.lab "scc_rt_main" + 1 + 3; rw [h4, ofNat_zero'])
      (xLea_ok (lo := -40) (hi := 0) _ _) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_ (soM (xLea 32 5) Spike.Lib.X64.Flow.oH)
      (fun σ c _ => ?_)
    · intro k hk; show PP (L.lab "scc_rt_main" + 1 + 3 + _).toBitVec.toNat; rw [eM]; revert k; decide +kernel
    · show QP (arun _ (xLea 32 5) ⟨L.lab "scc_rt_main" + 1 + 3, Spike.Lib.X64.Flow.oH, σ⟩).pc.toBitVec.toNat
      rw [xLea_run (Z := 32) _ _ _ (by decide)]
      show QP (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eM]; decide +kernel
  · have hE : ∀ s c, At L.exe L.endPc R F (xProN2 (L.lab "scc_rt_main") 5 32 J) s c →
        CellAt s (fsDir .r11 8) 9 ∧
        fsAddr s 9 { base := none, idx := none, disp := .int64 8 } = Spike.Lib.X64.Flow.Ret0.limA tp ∧
        Mem.loadInt s.st.1.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none ∧ s.decls = {} := by
      rintro s c ⟨he, hn, hd, hp', σ2, hA, hF, σ0, hJ0, rfl⟩
      refine ⟨(code_field L.lays rfl (hp ▸ bLd) (by show _ = L.lab "scc_rt_main" + 1 + 3 + _; rw [h4]) s he hn).cell0
        rfl rfl hp', ?_, hun _ hF, hd⟩
      rw [show Spike.Lib.X64.Flow.Ret0.limA tp = (xS2 32 σ0).regs.fsBase.toBitVec + (8 : Int64).toBitVec by
        rw [congrFun hxs σ0, htp _ _ hJ0]; rfl]
      simp [fsAddr, eaddr, AddrExpr.interp, ConstExpr.interp, hA.regs]
    refine nodeLB hsep ha hW (sz := 9) (P := QP) (cls_pool hlab hb) (fun s c hAt s' hs => ?_) ⟨?_, ?_⟩
      (by dsimp only [xProN2]; decide) (hw_fsld hE)
    · obtain ⟨hc, hea, hun', hd⟩ := hE s c hAt
      have hK : Keep s s' := keep_fsld hc hd hea hun' hs
      exact ⟨hK, by rw [keep_pc hc hK, hAt.2.2.2.1]⟩
    · show QP (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5).toBitVec.toNat; rw [eM]; decide +kernel
    · show QP (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9).toBitVec.toNat; rw [eM]; decide +kernel
  · refine blkLB hp hlab hsite hsep ha hW (P := PP) (Q := QP) bCmp
      (by show _ = L.lab "scc_rt_main" + 1 + 3 + _ + _; rw [e14])
      (xCmp_ok (lo := -40) (hi := 0) _ _ _ _) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
      (soM (xCmp ".Lscc_rt_main.stk" 3 2) (Spike.Lib.X64.Flow.oL 32)) (fun σ c _ => ?_)
    · intro k hk; show PP (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + _).toBitVec.toNat
      rw [eM]; revert k; decide +kernel
    · show QP (arun _ (xCmp ".Lscc_rt_main.stk" 3 2)
        ⟨L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9, Spike.Lib.X64.Flow.oL 32, σ⟩).pc.toBitVec.toNat
      rw [(xCmp_run _ _ _ _ _ _ _).1]
      split
      · rw [eM]; decide +kernel
      · show QP (L.lab ".Lscc_rt_main.stk").toBitVec.toNat; rw [eK]; decide +kernel
  · refine blkLB hp hlab hsite hsep ha hW (P := PP) (Q := QP) bFr
      (by show _ = L.lab "scc_rt_main" + 1 + 3 + _ + _ + _ + _; rw [e19])
      (xFr_ok (lo := -40) (hi := 0) _ _ _ (by decide)) hR (by omega) hhi (fun _ h => h.2)
      (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
      (soM (xFr 32 4 [(.rdi, -8, 4)]) (Spike.Lib.X64.Flow.oL 32)) (fun σ c _ => ?_)
    · intro k hk
      show PP (L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2 +
        _).toBitVec.toNat
      rw [eM]; revert k; decide +kernel
    · show QP (arun _ (xFr 32 4 [(.rdi, -8, 4)])
        ⟨L.lab "scc_rt_main" + 1 + 3 + Int64.ofNat 5 + Int64.ofNat 9 + Int64.ofNat 3 + Int64.ofNat 2,
          Spike.Lib.X64.Flow.oL 32, σ⟩).pc.toBitVec.toNat
      rw [(xFr_run _ _ _ _ _ _).1, eM]; decide +kernel

/-- **`.entry`'s call block inside `Lft`**: it ends at `wc_main`'s entry. -/
theorem callLM (hR : R.OK) (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} :
    BlkW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F
      (wN0 (_root_.Executable.labels L.exe).label J) wB0 := by
  obtain ⟨-, -, eE, eW⟩ := main_labs hlab (L := L)
  have h := Spike.Lib.X64.Flow.WakeM.wake_mainIn
  simp only [Spike.Lib.X64.Flow.WakeM.wakeMainIn, prologueIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, b0⟩, -⟩ := h
  refine blkLB hp hlab hsite hsep ha hW (P := PP) (Q := QP) (l := ".Lscc_rt_main.entry") (k := 0) b0
    (ofNat_zero' _) Spike.Lib.X64.Flow.WakeM.wB0_ok hR hRlo hhi (fun _ h => h.2)
    (fun s h => cls_pool hlab hb s h.1) (cls_pool hlab hb) ?_
    (soM wB0 (⟨-40, [(.rbp, -8)]⟩ : Spike.Lib.X64.SO)) (fun σ c _ => ?_)
  · intro k hk
    show PP (L.lab ".Lscc_rt_main.entry" + Int64.ofNat (cellOff wB0 k)).toBitVec.toNat
    rw [eE]; revert k; decide +kernel
  · dsimp only [wN0]
    rw [Spike.Lib.X64.Flow.WakeM.wB0_run]
    show QP (L.lab "wc_main").toBitVec.toNat
    rw [eW]; decide +kernel

end L

/-- **`scc_rt_main` up to `call wc_main` inside `WSX`**: `h` (inside `WS`,
`MainWf.mainPreWW_W0S`) and every node inside `Lft` (`proLM`, `callLM`),
the frame's band on the pool (`hb`). -/
theorem mainPreWWX (hp : L.prog = wakeCells)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
    (hsep : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hb : BandOnP L R (-48) 8) (hR : R.OK) (hRlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    {rS : Range} {ms : Spike.Lib.MemSide isa} {J : Spike.Lib.X64.AS → Spike.Lib.Ctl → Prop} {tp : UInt64}
    (htp : ∀ σ c, J σ c → σ.regs.fsBase = tp)
    (hun : ∀ m, F m → Mem.loadInt m.dmem (Spike.Lib.X64.Flow.Ret0.limA tp) 8 = none)
    (h : MainPreWW (WS L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J) :
    MainPreWW (WSX L a ar p Dt Cl Ctx lbl lsize frM X0) (Spike.Lib.X64.PhRec.K L rS) L.exe L.endPc R F ms J :=
  ⟨Spike.Lib.X64.Flow.XProW.imp h.pro (proLM hp hlab hsite hsep ha hW hb hR hRlo hhi htp hun)
      fun _ _ h1 h2 => h2 h1,
    Spike.Lib.X64.AllocG.BlkW.imp h.call (callLM hp hlab hsite hsep ha hW hb hR hRlo hhi)
      fun _ _ h1 h2 => h2 h1⟩

end Spike.Lib.X64.WakePh.MainPreX

/-- info: 'Spike.Lib.X64.WakePh.MainPreX.blkLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPreX.blkLB

/-- info: 'Spike.Lib.X64.WakePh.MainPreX.nodeLB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPreX.nodeLB

/-- info: 'Spike.Lib.X64.WakePh.MainPreX.proLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPreX.proLM

/-- info: 'Spike.Lib.X64.WakePh.MainPreX.callLM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPreX.callLM

/-- info: 'Spike.Lib.X64.WakePh.MainPreX.mainPreWWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.MainPreX.mainPreWWX
