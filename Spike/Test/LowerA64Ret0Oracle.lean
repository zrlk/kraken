/-
**H3 oracle: the symbolic body segment at `ret0.w`** (AArch64).

`body_seg` (`Spike/Lib/LowerA64/Body.lean`) instantiated at `ret0.w`'s
`main` (`mainCtx`, `ret0_lower0`), its code discharged from `ret0Prog`'s
listing (`ret0_bodyCode`), against the hand segment `ret0_wc_body_segW`
(`Spike/Lib/A64Ret0Segs.lean`):

- the same entry: `.L18_wc_main.0_entry`, offsets `⟨-32, []⟩`;
- the same exit: the saved return address, offsets `⟨0, []⟩`, with
  `x0 = 42` and `x29`/`x30` restored (`ret0_oracle`): the generic exit
  `retN` gives `x0` representing the source's returned word, and the source
  from `main`'s body (`k1`) reaches `ret y` with `y = 42` only;
- the generic segment keeps the overflow abort exit (`abortN`), which the
  hand segment refutes by evaluation; the generic source steps (the hand's
  stays at `g.c0`).
-/
import Spike.Lib.LowerA64.Body
import Spike.Lib.LowerA64.ProIn
import Spike.Lib.LowerA64.BodyIn
import Spike.Lib.LowerA64.Fn
import Spike.Test.LowerInv
import Spike.Test.A64Ret0Negative

namespace Spike.Test.LowerA64Ret0Oracle

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Spike.Lib.A64 (CodeAt)
open Scc.Emit.A64 Scc.Lower.InvA64
open Scc.Cert.Rt.A64 (Lays endOf blockAt)
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Spike.Lib.LowerNode Spike.Lib.LowerA64
open Spike.Test.LowerInv (mainCtx mainCtx_frameOk mainCtx_y main0 ret0Res ret0_lower0)
open Spike.Test.A64Ret0Negative (k1 k3 reach_run Reach)

/-! ## `main`'s frame -/

#guard mainCtx.frame == 32 && mainCtx.out == 0 && mainCtx.local "abort_overflow" == ".L18_wc_main.abort_overflow"

theorem mainCtx_frame : mainCtx.frame = 32 := by decide +kernel
theorem mainCtx_out : mainCtx.out = 0 := by decide +kernel
theorem mainCtx_abort : mainCtx.local "abort_overflow" = ".L18_wc_main.abort_overflow" := by decide +kernel

theorem slotY : mainCtx.slotOff "y%0" = .ok 0 := by rw [mainCtx_y, mainCtx_out]; rfl

theorem getOp40 : mainCtx.getOp .X9 (Scc.Lower.imm 40) = .ok (movImm .X9 40) := rfl
theorem getOp2 : mainCtx.getOp .X10 (Scc.Lower.imm 2) = .ok (movImm .X10 2) := rfl
theorem getOpY : mainCtx.getOp .X0 (.reg "y%0") =
    .ok [ins (.LDR (rz .W64 .X0) (.addr ⟨spW64, .imm ⟨i64 0, none⟩⟩))] :=
  getReg_eq mainCtx_frameOk (by rw [mainCtx_frame]; decide) slotY .X0

/-! ## The code -/

/-- The add's block is the listing's `wcAdd`. -/
theorem add_eq : directives (movImm .X9 40 ++ movImm .X10 2 ++
    addChecked .X9 .X9 .X10 (mainCtx.local "abort_overflow")) = wcAdd := by
  rw [mainCtx_abort]; decide

/-- The return's block is the listing's `retBlk 32 [.slot 0]`. -/
theorem ret_eq : directives ([ins (.LDR (rz .W64 .X0) (.addr ⟨spW64, .imm ⟨i64 0, none⟩⟩))] ++ mainCtx.leave ++
    [ret]) = retBlk 32 [.slot 0] := by
  rw [directives_ret_slot mainCtx_frameOk (by rw [mainCtx_frame]; decide) slotY getOpY, mainCtx_frame]; rfl

/-- The store and the return block in `ret0Prog`, after the add. -/
theorem ret0_strIn : blockAt SccCode.ret0Prog ".L18_wc_main.0_entry" 4
    (directives [ins (.STR (rz .W64 .X9) ⟨spW64, .imm ⟨i64 0, none⟩⟩)]) = true := by decide +kernel
theorem ret0_retIn : blockAt SccCode.ret0Prog ".L18_wc_main.0_entry" 5 (retBlk 32 [.slot 0]) = true := by
  decide +kernel

section Fn

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`main`'s lowered body's code in any valid layout of `ret0Prog`.** -/
theorem ret0_bodyCode (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog) :
    BodyCode mainCtx (CdOf exe endPc) ((_root_.Executable.labels exe).label ".L18_wc_main.0_entry")
      ret0Res.insts ret0Res.ret := by
  have hin := ret0_wcBodyIn
  simp only [wcBodyIn, Bool.and_eq_true] at hin
  have hlen : (wcAdd).length = 4 := rfl
  refine ⟨movImm .X9 40, movImm .X10 2, 0, getOp40, getOp2, slotY, ?_, ?_, _, getOpY, ?_⟩
  · rw [add_eq]; exact code_of hp hend hin.1 (ofNat4_zero _)
  · rw [add_eq, hlen]; exact code_of hp hend ret0_strIn rfl
  · rw [add_eq, hlen, ret_eq, ← ofNat4_succ]; exact code_of hp hend ret0_retIn rfl

/-- **The symbolic body segment at `ret0.w`'s `main`**: from
`.0_entry` (`main`'s body, `u` bound to the unit) to the saved return
address or the overflow abort label. -/
theorem ret0_generic_body_segW {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} {c0 : Ctl}
    (hW : ∀ pc t s blk, CdOf exe endPc pc blk → BlkW W K exe endPc R F (bodyN p lbl mainCtx fp ra c0 pc t s) blk)
    (hWp : ∀ pc t s k blk, CdOf exe endPc pc blk →
      BlkW W K exe endPc R F (pendN p lbl mainCtx fp ra c0 pc t s k) blk) :
    SegW W K p lbl ms
      (At exe endPc R F (bodyN p lbl mainCtx fp ra c0 ((_root_.Executable.labels exe).label ".L18_wc_main.0_entry")
        main0.body (ofEnv [(main0.arg, .unit, [])])))
      (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
        At exe endPc R F (abortN (immsOf main0) (InWalk main0) p
          lbl mainCtx (_root_.Executable.labels exe).label fp ra c0) s c) :=
  body_seg mainCtx_frameOk (by simp [mainCtx_frame]) (by simp [mainCtx_frame]) hF hR hal
    (by rw [mainCtx_frame]; exact hlo) hhi (fun _ _ h => h) hW hWp _ _ 0 _ _ ret0_lower0
    (fun v hv => by simp at hv; subst hv; intro o ho; cases ho) (ret0_bodyCode hp hend) (walk_immsOf main0)

end Fn

/-! ## Against the hand segment -/

/-- **The hand entry's source gives the generic entry**: at `main`'s body
(`k1`) with the saved pair, the body node's invariant (ghost entry `k1`). -/
theorem bodyN_of_k1 {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {pc : Int64} {σ : AS}
    (h : FrJ fp ra σ.slot) :
    (bodyN Spike.Lib.Ret0Src.ret0Src lbl mainCtx fp ra k1 pc main0.body (ofEnv [(main0.arg, .unit, [])])).J σ k1 := by
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
    simp only [k1, Spike.Lib.A64.Flow.Ret0.Inst.mainEnv, List.mem_singleton] at hb
    subst hb
    intro w hw; cases hw

/-- **The generic exit gives the hand exit's facts**: the return's exit
reached from `main`'s body has `x0 = 42` and the saved pair restored. -/
theorem retN_hand {lbl : WeakMem.AllocLabel → Option Nat} {fp ra : BitVec 64} {σ : AS} {c : Ctl}
    (h : (retN Spike.Lib.Ret0Src.ret0Src lbl fp ra k1).J σ c) :
    σ.regs.X0.toBitVec = 42#64 ∧ σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra := by
  obtain ⟨⟨a, t, w, ht, -, he, -, hv, h29, h30⟩, hr⟩ := h
  refine ⟨?_, h29, h30⟩
  rcases reach_run hr (.inr (.inl rfl)) with rfl | rfl | rfl | rfl
  · cases ht
  · cases ht
  · cases ht
  · simp only [k3, Expr.ret.injEq] at ht
    subst ht
    simp only [k3, Spike.Lib.A64.Flow.Ret0.Inst.exitEnv, TermRun.evalAt, TermRun.lookupE, List.find?,
      Option.map, Option.some.injEq, Prod.mk.injEq, List.cons.injEq, and_true] at he
    obtain ⟨-, rfl⟩ := he
    have := hv.2
    apply BitVec.eq_of_toNat_eq
    rw [this]; rfl

/-- **The oracle**: the symbolic body segment, from the hand entry node
(`main`'s body, the saved pair), reaches the hand exit's pc and offsets with
`x0 = 42` and `x29`/`x30` restored, or the overflow abort label. -/
theorem ret0_oracle {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {fp ra : BitVec 64} :
    SegW (fun _ _ => True) (fun _ _ => False) Spike.Lib.Ret0Src.ret0Src lbl ms
      (At exe endPc R F ⟨(_root_.Executable.labels exe).label ".L18_wc_main.0_entry", ⟨-32, []⟩,
        fun σ c => c = k1 ∧ FrJ fp ra σ.slot⟩)
      (fun s c => At exe endPc R F ⟨Int64.ofBitVec ra, ⟨0, []⟩, fun σ _ =>
          σ.regs.X0.toBitVec = 42#64 ∧ σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra⟩ s c ∨
        At exe endPc R F (abortN (immsOf main0) (InWalk main0) Spike.Lib.Ret0Src.ret0Src
          lbl mainCtx (_root_.Executable.labels exe).label fp ra k1)
          s c) := by
  refine ((ret0_generic_body_segW (c0 := k1) hp hend hF hR hal hlo hhi (fun _ _ _ _ _ => BlkW.triv)
    (fun _ _ _ _ _ _ => BlkW.triv)).mono_pre
    fun s c ⟨he, hn, hd, hpc, σ, hA, hFm, hc, hfj⟩ => by
      subst hc
      refine ⟨he, hn, hd, hpc, σ, ?_, hFm, bodyN_of_k1 hfj⟩
      simpa [bodyN, oF, mainCtx_frame] using hA).mono_post
    fun s c h => h.imp (fun ⟨he, hn, hd, hpc, σ, hA, hFm, hJ⟩ => ⟨he, hn, hd, hpc, σ, hA, hFm, retN_hand hJ⟩) id

/-! ### The prologue's placement from `mainCtx` -/

#guard proInC SccCode.ret0Prog mainCtx "wc_main" ".L18_wc_main.0_entry"

/-- `wc_main`'s prologue in `ret0Prog`, every label and constant from `mainCtx`. -/
theorem ret0_proInC : proInC SccCode.ret0Prog mainCtx "wc_main" ".L18_wc_main.0_entry" = true := by
  decide +kernel

/-- It is the hand check `wcPro`. -/
theorem ret0_proInC_eq : proInC SccCode.ret0Prog mainCtx "wc_main" ".L18_wc_main.0_entry" =
    prologueIn SccCode.ret0Prog "wc_main" ".L18_wc_main.stack_check" ".L18_wc_main.0_entry" 32 8
      ".L18_wc_main.stack_grow" [] := by
  decide +kernel

/-! ### The body's placement from `mainCtx` -/

#guard bodyIn SccCode.ret0Prog mainCtx ".L18_wc_main.0_entry" 0 ret0Res.insts ret0Res.ret

theorem ret0_bodyIn : bodyIn SccCode.ret0Prog mainCtx ".L18_wc_main.0_entry" 0 ret0Res.insts ret0Res.ret = true := by
  decide +kernel

/-- `ret0_bodyCode` again, from the generic check. -/
theorem ret0_bodyCode' {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog) :
    BodyCode mainCtx (CdOf exe endPc) ((_root_.Executable.labels exe).label ".L18_wc_main.0_entry")
      ret0Res.insts ret0Res.ret := by
  have := bodyCode_of hp hend _ 0 _ ret0_bodyIn
  rwa [ofNat4_zero] at this

/-! ### The whole function from the generic checks -/

/-- **`wc_main` is one segment from the generic checks alone**
(`fn0_seg` at `mainCtx`, `ret0_proInC`, `ret0_bodyIn`): from `wc_main`'s
label to the saved return address or the overflow abort label. -/
theorem ret0_fn0_segW {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {W : Frag isaLSE2} {K : State → State → Prop}
    (hp : Lays exe SccCode.ret0Prog) (hend : endPc = endOf exe SccCode.ret0Prog)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -32) (hhi : 0 ≤ R.hi)
    {J : AS → Ctl → Prop} {fp ra : BitVec 64} {c0 : Ctl}
    (hWp : ProW W K exe endPc R F ms ((_root_.Executable.labels exe).label "wc_main") (Int64.ofInt mainCtx.frame)
      (Int64.ofNat Scc.IR.Tcb.stackLimit) (proL mainCtx) [] J)
    (hWb : ∀ pc t s blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret pc blk →
      BlkW W K exe endPc R F (bodyN p lbl mainCtx fp ra c0 pc t s) blk)
    (hWs : ∀ pc t s k blk, CdOf exe endPc pc blk →
      InBody (_root_.Executable.labels exe).label mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret pc blk →
      BlkW W K exe endPc R F (pendN p lbl mainCtx fp ra c0 pc t s k) blk)
    (hedge : ∀ σ c, J σ c →
      (ms.rt (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)).toNat ∧
        ms.mp ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ false ∧
        (∀ m, F m → Mem.loadInt m.dmem (tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit)) 8 = none) ∧
        ∀ v : Val, ms.G ⟨tcbA σ.regs (Int64.ofNat Scc.IR.Tcb.stackLimit), 8⟩ v →
          (v.setWidth 64).toNat ≤ (σ.regs.SP.toBitVec - (Int64.ofInt mainCtx.frame).toBitVec).toNat) ∧
      σ.regs.X29.toBitVec = fp ∧ σ.regs.X30.toBitVec = ra ∧
      (∀ sl, NJ p lbl (rsOf mainCtx) main0.body (ofEnv [(main0.arg, .unit, [])]) sl c) ∧ LocalRun p c0 c) :
    SegW W K p lbl ms (At exe endPc R F ⟨(_root_.Executable.labels exe).label "wc_main", ⟨0, []⟩, J⟩)
      (fun s c => At exe endPc R F (retN p lbl fp ra c0) s c ∨
        At exe endPc R F (abortN (immsOf main0) (InWalk main0) p
          lbl mainCtx (_root_.Executable.labels exe).label fp ra c0) s c) :=
  fn0_seg mainCtx_frameOk (by simp [mainCtx_frame]) (by simp [mainCtx_frame]) hp hend ret0_proInC
    ret0_lower0 (fun v hv => by simp at hv; subst hv; intro o ho; cases ho) ret0_bodyIn (walk_immsOf main0)
    hF hR hal (by rw [mainCtx_frame]; exact hlo) hhi hWp hWb hWs hedge

/-- info: [(0, 4), (4, 1), (5, 5)] -/
#guard_msgs in -- `ret0.w`'s body blocks (`InBody`'s): the add, its store, the return; offsets and lengths
#eval (bodyBlks mainCtx 0 ret0Res.insts ret0Res.ret).map (fun x => (x.1, x.2.length))

/-- Every body block is `InBody` at its offset (`hWb`'s premise is satisfiable). -/
example (lab : Label → Int64) : ∀ x ∈ bodyBlks mainCtx 0 ret0Res.insts ret0Res.ret,
    InBody lab mainCtx ".L18_wc_main.0_entry" ret0Res.insts ret0Res.ret
      (lab ".L18_wc_main.0_entry" + Int64.ofNat (4 * x.1)) x.2 :=
  fun x hx => ⟨x.1, rfl, hx⟩

end Spike.Test.LowerA64Ret0Oracle
