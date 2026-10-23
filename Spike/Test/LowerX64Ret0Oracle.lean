/-
**The symbolic body segment at `ret0.w`** (x86-64); the twin of
`Spike/Test/LowerA64Ret0Oracle.lean`.

`body_seg` (`Spike/Lib/LowerX64/Body.lean`) instantiated at `ret0.w`'s
`main` (the frame `mainFr`, `ret0_lower0`), its code discharged from
`ret0Cells`'s listing (`ret0_bodyIn`), against the hand segment
`ret0_wc_body_segW` (`Spike/Lib/X64Ret0Segs.lean`):

- the same entry: `.Lwc_main.entry`, offsets `⟨-24, [(%rbp, -8)]⟩` in the
  region based at the entry `%rsp` (the generic body runs in that region
  rebased at the frame record, `rbR`, at `oB mainFr = ⟨-16, [(%rbp, 0)]⟩`;
  `at_rbR` moves the node across);
- the same exit: the saved return address, offsets `⟨8, []⟩`, with
  `%rax = 42` and `%rbp` restored (`ret0_oracle`): the generic exit `retN`
  (`⟨16, []⟩` in `rbR`, moved back by `at_of_rbR`) gives `%rax`
  representing the source's returned word, and the source from `main`'s
  body (`k1`) reaches `ret y` with `y = 42` only;
- the generic segment keeps the overflow abort exit (`abortN`), which the
  hand segment refutes by evaluation; the generic source steps (the hand's
  stays put);
- the generic checks (`proInC`, `bodyIn`) hold of `ret0Cells` and are the
  hand checks (`wcPro`, `wcBodyIn`'s blocks), and `fn0_seg` gives `wc_main`
  from its label from them alone (`ret0_fn0_segW`).
-/
import Spike.Lib.LowerX64.Fn
import Spike.Lib.X64Ret0Segs
import Spike.Test.LowerX64Construct
import Spike.Test.X64Ret0Negative

namespace Spike.Test.LowerX64Ret0Oracle

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Lower.InvX64
open Scc.Cert.Rt.X64 (Lays endOf blockAtB)
open Spike.Lib.Form (NodeJ SEnv lookupS)
open Spike.Lib.LowerNode Spike.Lib.LowerX64
open Scc.Lower.Inv (lower0 Res)
open Spike.Test.LowerInvX64 (mainFr)
open Spike.Test.LowerX64Construct (mainFr_ok mainFr_small la lb ly getOp_a getOp_b getOp_y rsOf_y)
open Spike.Test.X64Ret0Negative (k1 k3 reach_run)

set_option linter.unusedSimpArgs false

/-! ## `main`'s lowering (ISA-neutral) -/

/-- `ret0.w`'s `main`. -/
def main0 : CoreTerm.Decl :=
  { name := "main", idx := [], arg := "u", argTy := .unit, retTy := .int, body := Spike.Lib.Ret0Src.ret0Body }

/-- The closed form of `main`'s body. -/
def ret0Res : Res :=
  { insts := [.addChk "y%0" (Scc.Lower.imm 40) (Scc.Lower.imm 2)], ret := [.reg "y%0"], next := 1,
    marked := ["y%0"],
    here := ([("y", .int, [.reg "y%0"]), ("x", .intS (.lit 40), [Scc.Lower.imm 40]), ("u", .unit, [])],
      .ret (.var "y")) }

theorem ret0_lower0 : lower0 [(main0.arg, .unit, [])] 0 main0.body = some ret0Res := by
  rfl

/-- The environment's registers are fresh (it places no word). -/
theorem ret0_fresh : Fresh [(main0.arg, .unit, [])] 0 :=
  fun v hv => by simp at hv; subst hv; intro o ho; cases ho

/-! ## `main`'s frame -/

#guard mainFr.size == 16 && mainFr.maps && Scc.Emit.X64.labelOf mainFr.fn "chk" == ".Lwc_main.chk" &&
  proL mainFr == ".Lwc_main.stk" && ovfL mainFr == ".Lwc_main.ovf"

theorem mainFr_size : mainFr.size = 16 := by decide +kernel

/-! ## The generic checks on `ret0Cells` -/

#guard proInC SccCode.ret0Cells mainFr "wc_main" ".Lwc_main.entry" 5 9 3 2 4

/-- `wc_main`'s prologue in `ret0Cells`, every label and constant from `mainFr`. -/
theorem ret0_proInC : proInC SccCode.ret0Cells mainFr "wc_main" ".Lwc_main.entry" 5 9 3 2 4 = true := by
  decide +kernel

/-- It is the hand check `wcPro`. -/
theorem ret0_proInC_eq : proInC SccCode.ret0Cells mainFr "wc_main" ".Lwc_main.entry" 5 9 3 2 4 =
    Spike.Lib.X64.Flow.wcPro := by
  decide +kernel

#guard bodyIn SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret

theorem ret0_bodyIn : bodyIn SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret = true := by
  decide +kernel

/-- The sizes `bodyIn` reads: the add's `[7, 7, 3, 2]`, the store's `4`
at `19`, the return's `[4, 3, 1, 1]` at `23`. -/
theorem ret0_sizes : sizesAt SccCode.ret0Cells ".Lwc_main.entry" 0 4 = [7, 7, 3, 2] ∧
    sizesAt SccCode.ret0Cells ".Lwc_main.entry" 19 1 = [4] ∧
    sizesAt SccCode.ret0Cells ".Lwc_main.entry" 23 4 = [4, 3, 1, 1] := by
  decide +kernel

/-- `bodyIn`'s blocks are the hand blocks: the add is `wcAdd`, the store and
the return `wcRet`. -/
theorem ret0_blocks_eq : (addDirs mainFr la lb).zip [7, 7, 3, 2] = Spike.Lib.X64.Flow.wcAdd ∧
    [(stDir (-8), 4)] ++ (retDirs ly).zip [4, 3, 1, 1] = Spike.Lib.X64.Flow.wcRet := by
  decide +kernel

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- **`main`'s lowered body's code in any valid layout of `ret0Cells`.** -/
theorem ret0_bodyCode (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells) :
    BodyCode mainFr (CdOf exe endPc) ((_root_.Executable.labels exe).label ".Lwc_main.entry")
      ret0Res.insts ret0Res.ret := by
  have := bodyCode_of hp hend _ 0 _ ret0_bodyIn
  rwa [Spike.Lib.X64.Flow.ofNat_zero'] at this

/-- **The symbolic body segment at `ret0.w`'s `main`**: from `.entry`
(`main`'s body, `u` bound to the unit) to the saved return address or the
overflow abort label. -/
theorem ret0_generic_body_segW {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -16) (hhi : 16 ≤ R.hi)
    {fp ra : BitVec 64} {c0 : Ctl}
    (hW : ∀ pc t s blk, CdOf exe endPc pc blk → BlkW W K exe endPc R F (bodyN p lbl mainFr fp ra c0 pc t s) blk)
    (hWp : ∀ pc t s k blk, CdOf exe endPc pc blk →
      BlkW W K exe endPc R F (pendN p lbl mainFr fp ra c0 pc t s k) blk) :
    SegW W K p lbl ms
      (At exe endPc R F (bodyN p lbl mainFr fp ra c0 ((_root_.Executable.labels exe).label ".Lwc_main.entry")
        main0.body (ofEnv [(main0.arg, .unit, [])])))
      (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
        At exe endPc R F (abortN (immsOf main0) (InWalk main0) p
          lbl mainFr (_root_.Executable.labels exe).label fp ra c0) s c) :=
  body_seg mainFr_ok mainFr_small hF hR (by rw [mainFr_size]; exact hlo) hhi (fun _ _ h => h) hW hWp _ _ 0 _ _
    ret0_lower0 ret0_fresh (ret0_bodyCode hp hend) (walk_immsOf main0)

end Fn

/-! ## Against the hand segment -/

/-- **The hand entry's source gives the generic entry**: at `main`'s body
(`k1`) with the saved pair, the body node's invariant (ghost entry `k1`). -/
theorem bodyN_of_k1 {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {pc : Int64} {σ : AS}
    (h : FrJ fp ra σ.slot) :
    (bodyN Spike.Lib.Ret0Src.ret0Src lbl mainFr fp ra k1 pc main0.body (ofEnv [(main0.arg, .unit, [])])).J σ k1 := by
  refine ⟨NJ.of_nodeJ ⟨rfl, rfl, ?_⟩ ?_, h, .refl _⟩
  · intro x t pls hl
    simp only [ofEnv, List.map, lookupS, main0] at hl
    by_cases hx : x = "u"
    · subst hx
      simp at hl
      obtain ⟨rfl, rfl⟩ := hl
      exact ⟨[], rfl, trivial⟩
    · simp [Ne.symm hx] at hl
  · intro b hb
    simp only [k1, Spike.Lib.X64.Flow.Ret0.Inst.mainEnv, List.mem_singleton] at hb
    subst hb
    intro w hw; cases hw

/-- **The generic exit gives the hand exit's facts**: the return's exit
reached from `main`'s body has `%rax = 42` and `%rbp` restored. -/
theorem retN_hand {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {σ : AS} {c : Ctl}
    (h : (retN Spike.Lib.Ret0Src.ret0Src lbl fp ra k1).J σ c) :
    σ.regs.rax.toBitVec = 42#64 ∧ σ.regs.rbp.toBitVec = fp := by
  obtain ⟨⟨a, t, w, ht, -, he, -, hv, hbp⟩, hr⟩ := h
  refine ⟨?_, hbp⟩
  rcases reach_run hr (.inr (.inl rfl)) with rfl | rfl | rfl | rfl
  · cases ht
  · cases ht
  · cases ht
  · simp only [k3, Expr.ret.injEq] at ht
    subst ht
    simp only [k3, Spike.Lib.X64.Flow.Ret0.Inst.exitEnv, TermRun.evalAt, TermRun.lookupE, List.find?,
      Option.map, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at he
    obtain ⟨-, rfl⟩ := he
    have := hv.2
    apply BitVec.eq_of_toNat_eq
    rw [← Reg64s.get64_rax, this]; rfl

/-- **The oracle**: the symbolic body segment, from the hand entry node
(`main`'s body, the saved `%rbp` at `-8` and the return address at `0`),
reaches the hand exit's pc and offsets with `%rax = 42` and `%rbp`
restored, or the overflow abort label. -/
theorem ret0_oracle {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {F : MachineData → Prop}
    (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    {fp ra : BitVec 64} :
    SegW (fun _ _ => True) (fun _ _ => False) Spike.Lib.Ret0Src.ret0Src lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".Lwc_main.entry", Spike.Lib.X64.Flow.oB,
        fun σ c => c = k1 ∧ σ.slot (-8) = fp ∧ σ.slot 0 = ra⟩)
      (fun s c => At exe endPc R F ⟨Int64.ofBitVec ra, ⟨8, []⟩, fun σ _ =>
          σ.regs.rax.toBitVec = 42#64 ∧ σ.regs.rbp.toBitVec = fp⟩ s c ∨
        At exe endPc (rbR R) F
          (abortN (immsOf main0) (InWalk main0) Spike.Lib.Ret0Src.ret0Src
            lbl mainFr (_root_.Executable.labels exe).label fp ra k1) s c) := by
  have hent : ∀ (σ : AS) (c : Ctl), (c = k1 ∧ σ.slot (-8) = fp ∧ σ.slot 0 = ra) →
      (bodyN Spike.Lib.Ret0Src.ret0Src lbl mainFr fp ra k1 ((_root_.Executable.labels exe).label ".Lwc_main.entry")
        main0.body (ofEnv [(main0.arg, .unit, [])])).J { σ with slot := shSl σ.slot } c := by
    rintro σ c ⟨rfl, h8, h0⟩
    exact bodyN_of_k1 ⟨h8, h0⟩
  refine ((ret0_generic_body_segW (c0 := k1) hp hend (rbR_fstable hR (by omega) (by omega) hF)
    (rbR_ok hR (by omega) (by omega)) (by simp only [rbR, Region.callee]; omega)
    (by simp only [rbR, Region.callee]; omega) (fun _ _ _ _ _ => BlkW.triv)
    (fun _ _ _ _ _ _ => BlkW.triv)).mono_pre
      fun s c h => at_rbR (fr := mainFr) (by rw [mainFr_size]; rfl) (by simp [SO.get, lk]) hent h).mono_post
    fun s c h => h.imp (fun h => at_of_rbR (fun σ c hJ => retN_hand (ra := ra) hJ) h) id

/-! ## The whole function from the generic checks -/

/-- The regions the segments ask for exist: one based at `2 ^ 20` from
`-24` to `8` (the ret0 call's), and the frame condition of the memory
outside it, stable there. -/
example : (⟨2 ^ 20, -24, 8⟩ : Region).OK ∧ (rbR ⟨2 ^ 20, -24, 8⟩).OK := by
  refine ⟨⟨by decide, by decide⟩, rbR_ok ⟨by decide, by decide⟩ (by decide) (by decide)⟩

example (m0 : MachineData) : FStable (⟨2 ^ 20, -24, 8⟩ : Region) (DFrame ⟨2 ^ 20, -24, 8⟩ m0) :=
  FStable.dframe _ m0

/-- **`wc_main` is one segment from the generic checks alone**
(`fn0_seg` at `mainFr`, `ret0_proInC`, `ret0_bodyIn`): from `wc_main`'s
label to the saved return address or the overflow abort label. -/
theorem ret0_fn0_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
    (hp : Lays exe SccCode.ret0Cells) (hend : endPc = endOf exe SccCode.ret0Cells)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 8 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl}
    (hWp : Spike.Lib.X64.Flow.XProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main")
      (Int64.ofInt mainFr.size) (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL mainFr) 5 9 3 2 4 [] J)
    (hWb : ∀ pc t s blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
        ret0Res.ret pc blk →
      BlkW W K exe endPc (rbR R) F (bodyN p lbl mainFr fp ra c0 pc t s) blk)
    (hWs : ∀ pc t s k blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts
        ret0Res.ret pc blk →
      BlkW W K exe endPc (rbR R) F (pendN p lbl mainFr fp ra c0 pc t s k) blk)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec).toNat ∧
        ms.mp ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec) 8
          = none) ∧
        ∀ v : Val, ms.G ⟨σ.regs.fsBase.toBitVec + (Int64.ofNat Scc.IR.Tcb.stackLimit).toBitVec, 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.rsp.toBitVec - 8#64 - (Int64.ofInt mainFr.size).toBitVec).toNat) ∧
      σ.regs.rbp.toBitVec = fp ∧ σ.slot 0 = ra ∧
      (∀ sl, NJ p lbl (rsOf mainFr) main0.body (ofEnv [(main0.arg, .unit, [])]) sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc (rbR R) F (retN p lbl fp ra c0) s c ∨
        At exe endPc (rbR R) F (abortN (immsOf main0) (InWalk main0) p
          lbl mainFr (_root_.Executable.labels exe).label fp ra c0) s c) :=
  fn0_seg mainFr_ok mainFr_small hp hend ret0_proInC ret0_lower0 ret0_fresh ret0_bodyIn (walk_immsOf main0)
    hF hR (by rw [mainFr_size]; exact hlo) hhi hWp hWb hWs hedge

/-- info: 'Spike.Test.LowerX64Ret0Oracle.ret0_fn0_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ret0_fn0_segW

/-- info: 'Spike.Test.LowerX64Ret0Oracle.ret0_oracle' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms ret0_oracle

/-- info: [(0, 4, 19), (19, 1, 4), (23, 4, 9)] -/
#guard_msgs in -- `ret0.w`'s body blocks (`InBody`'s): the add, its store, the return; byte offsets, lengths, bytes
#eval (bodyBlks SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret).map
  (fun x => (x.1, x.2.length, (x.2.map (·.2)).sum))

/-- Every body block is `InBody` at its offset (`hWb`'s premise is satisfiable). -/
example (lab : String → Int64) : ∀ x ∈ bodyBlks SccCode.ret0Cells mainFr ".Lwc_main.entry" 0 ret0Res.insts ret0Res.ret,
    InBody lab SccCode.ret0Cells mainFr ".Lwc_main.entry" ret0Res.insts ret0Res.ret
      (lab ".Lwc_main.entry" + Int64.ofNat x.1) x.2 :=
  fun x hx => ⟨x.1, rfl, hx⟩

end Spike.Test.LowerX64Ret0Oracle
