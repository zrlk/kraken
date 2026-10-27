/-
**`main`'s `ret b` block inside `W2` at the held frames** (x86-64): the twin
of `Spike/Lib/LowerA64/RetHeldW.lean` and `Spike/Lib/LowerA64/RetHeldAb.lean`.
The block `(retDirs lw).zip zs` (the result's loads, the epilogue
`movq %rbp, %rsp`, `popq %rbp`, `ret`) at a node whose invariant holds the
held pair (`HeldTail`), the frame's result in a region cell (`RetSlot`) and
the block's run landing at the frame's return address `ra`: its states
inside `W2` by `blkW_heldTail`, `HeldS` by `blkW_heldS` from the abort
phase's facts (`blkW_abSt_subCdLR`), `Ret0` from the frame's result cell
(`blkW_ret0_slot`, the block stores nothing), no write (`blkW_noWr'`) and no
system call (`blkW_noSys'`).

The node is any: its invariant's facts are premises, so the held node of
the block's `bodyN2` gets them from `retSlot_bodyN2` and `retDirs_pc_bodyN2`
past the held pair's run.

- `RetI`, `RetD`: an instruction of the return block (a load, a `pop`, a
  register operation, `ret`); `retD_getOp`, `retD_getOps`, `retD_retDirs`:
  every directive of the return block is one;
- `dstep_slot_of_retD`, `retDirs_slot`: the return block stores nothing;
- `retDirs_last`: its last cell is the `ret`;
- `retDirs_pc_bodyN2`: its run from `bodyN2` lands at the frame's `ra`;
- `retSlot_bodyN2`: `RetSlot` at a held pair whose run lands at `bodyN2`;
- `retHeld_hab`: the return block keeps the write abort's phase;
- `retHeld_hW`: the return block's states inside `W2` at the held frames.
-/
import Spike.Lib.LowerX64.HeldTailSlot
import Spike.Lib.LowerX64.UserAbR
import Spike.Lib.LowerX64.W2Body
import Spike.Lib.LowerX64.RetSL

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm A9NoSpawn
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Scc.Sem Scc.Sem.X64
open Spike.Lib (Region FrameRun)
open Spike.Lib.X64 (ND BlkW AS AM SO AI arun dstep okBlk CodeAt epi retBlk RW wordDirs)
open Scc.Emit.X64 (Item)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64.Rt (InstOk)
open Spike.Lib.X64.WriteAb (Ab)

/-! ## The return block's instructions -/

/-- **An instruction of the return block**: a load, a `pop`, a register
operation or `ret`; none stores. -/
def RetI : AI → Bool
  | .ld .. | .pop .. | .reg .. | .ret => true
  | _ => false

/-- **A directive of the return block**: classified, an instruction of the
return block. -/
def RetD (d : Directive) : Prop := ∀ a, Spike.Lib.X64.classify d = some a → RetI a = true

/-- **A step of the return block keeps the cells.** -/
theorem dstep_slot_of_retD (lab : String → Int64) (am : AM) {d : Directive} (h : RetD d) (z : Nat) :
    (dstep lab am (d, z)).σ.slot = am.σ.slot := by
  rcases hc : Spike.Lib.X64.classify d with _ | a
  · simp [dstep, hc]
  · have := h a hc
    cases a <;> simp only [RetI, Bool.false_eq_true] at this <;> simp [dstep, hc, Spike.Lib.X64.AI.step]

theorem arun_slot_of_retD (lab : String → Int64) :
    ∀ (blk : List (Directive × Nat)) (am : AM), (∀ dz ∈ blk, RetD dz.1) → (arun lab blk am).σ.slot = am.σ.slot
  | [], _, _ => rfl
  | (d, z) :: blk, am, h => by
    show (arun lab blk (dstep lab am (d, z))).σ.slot = _
    rw [arun_slot_of_retD lab blk _ fun dz hd => h dz (List.mem_cons_of_mem _ hd)]
    exact dstep_slot_of_retD lab am (h (d, z) List.mem_cons_self) z

/-- An operand's load is an instruction of the return block. -/
theorem retD_getOp {fr : Scc.Emit.X64.Frame} {t : Reg64} {a : Scc.IR.Operand} {l : List Item}
    (ha : getOp fr t a = .ok l) : ∀ d ∈ dirs l, RetD d := by
  rcases getOp_cases ha with ⟨r, off, -, -, hl⟩ | ⟨v, -, hl⟩ <;> rw [hl] <;> intro d hd b hb <;>
    simp only [List.mem_singleton] at hd <;> subst hd
  · simp [AI.toDir, Spike.Lib.X64.classify, op64] at hb; subst hb; rfl
  · have hc : Spike.Lib.X64.classify (Scc.Emit.X64.i64 (.mov (Scc.Emit.X64.xr t) (.imm (.int64 v.toInt64)))) =
        some (.reg .W64 (.mov (Scc.Emit.X64.xr t) (.imm (.int64 v.toInt64)))) := rfl
    rw [hc] at hb; cases hb; rfl

/-- The result's loads are instructions of the return block. -/
theorem retD_getOps {fr : Scc.Emit.X64.Frame} :
    ∀ (ps : List (Scc.IR.Operand × Reg64)) {lw : List Item}, getOps fr ps = .ok lw → ∀ d ∈ dirs lw, RetD d
  | [], lw, h => by
    cases h
    simp [dirs]
  | (a, r) :: ps, lw, h => by
    simp only [getOps] at h
    obtain ⟨la, ha, h⟩ := exc_bind_ok h
    obtain ⟨lr, hr, h⟩ := exc_bind_ok h
    cases h
    intro d hd
    rw [dirs_append] at hd
    rcases List.mem_append.mp hd with hd | hd
    · exact retD_getOp ha d hd
    · exact retD_getOps ps hr d hd

/-- **Every directive of the return block is one of its instructions.** -/
theorem retD_retDirs {fr : Scc.Emit.X64.Frame} {ps : List (Scc.IR.Operand × Reg64)} {lw : List Item}
    (hl : getOps fr ps = .ok lw) : ∀ d ∈ retDirs lw, RetD d := by
  intro d hd
  rw [retDirs, dirs_append, dirs_epiItems] at hd
  rcases List.mem_append.mp hd with hd | hd
  · exact retD_getOps ps hl d hd
  · intro b hb
    simp only [epi, List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl <;>
      simp [AI.toDir, Spike.Lib.X64.classify, op64, Spike.Lib.X64.RegOnly] at hb <;>
      subst hb <;> rfl

/-- **The return block keeps the cells before each instruction.** -/
theorem retDirs_slot {fr : Scc.Emit.X64.Frame} {ps : List (Scc.IR.Operand × Reg64)} {lw : List Item}
    (hl : getOps fr ps = .ok lw) (zs : List Nat) (lab : String → Int64) (am : AM) (k : Nat) :
    (arun lab (((retDirs lw).zip zs).take k) am).σ.slot = am.σ.slot :=
  arun_slot_of_retD lab _ am fun _ hd => retD_retDirs hl _ (List.of_mem_zip (List.mem_of_mem_take hd)).1

/-- **The return block's last cell is the `ret`.** -/
theorem retDirs_last (lw : List Item) {zs : List Nat} (hz : zs.length = (retDirs lw).length) :
    ∃ hne : (retDirs lw).zip zs ≠ [], Spike.Lib.X64.classify (((retDirs lw).zip zs).getLast hne).1 = some .ret := by
  have hd : retDirs lw = (dirs lw ++ [epi[0], epi[1]]) ++ [AI.ret.toDir] := by
    simp [retDirs, dirs_append, dirs_epiItems, epi]
  have hzl : zs.length = (dirs lw ++ [epi[0], epi[1]]).length + 1 := by rw [hz, hd]; simp
  obtain ⟨zs', z, rfl⟩ : ∃ zs' z, zs = zs' ++ [z] := by
    refine ⟨zs.dropLast, zs.getLast (by intro h; simp [h] at hzl), (List.dropLast_concat_getLast _).symm⟩
  have hl' : zs'.length = (dirs lw ++ [epi[0], epi[1]]).length := by simp at hzl ⊢; omega
  have he : (retDirs lw).zip (zs' ++ [z]) = (dirs lw ++ [epi[0], epi[1]]).zip zs' ++ [(AI.ret.toDir, z)] := by
    rw [hd, List.zip_append hl'.symm]; rfl
  refine ⟨by rw [he]; simp, ?_⟩
  simp only [he]
  rw [List.getLast_append_of_ne_nil _ (by simp)]
  rfl

/-! ## At a node of `bodyN2` -/

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
  {fs : List TermRun.Frame}

/-- **The return block's run from `bodyN2` lands at the frame's `ra`**
(`FrJ`, `retBlk_run`). -/
theorem retDirs_pc_bodyN2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {vs : List Scc.IR.Operand} {lw : List Item} (hl : getOps fr (vs.zip Scc.Emit.X64.retRegs) = .ok lw)
    (hn : vs.length ≤ Scc.Emit.X64.retRegs.length) {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    (lab : String → Int64) {i : Expr → String → Nat → Option Nat} {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64}
    {t : Expr} {s : Spike.Lib.Form.SEnv} {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    {σ : AS} {c : Ctl} (hJ : (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).J σ c) :
    (arun lab ((retDirs lw).zip zs) ⟨pc, oB fr, σ⟩).pc = Int64.ofBitVec ra := by
  have hrr : Scc.Emit.X64.retRegs = Spike.Lib.X64.retRegs := rfl
  rw [hrr] at hl hn
  obtain ⟨rws, -, hd, -, -⟩ := getOps_rw hf h1 hl hn
  have hblk : retDirs lw = retBlk rws := by
    rw [retDirs, dirs_append, dirs_epiItems, hd]; rfl
  rw [hblk] at hz ⊢
  show (arun lab ((retBlk rws).zip zs) ⟨pc, Spike.Lib.X64.oR (-(fr.size : Int)), σ⟩).pc = _
  rw [(Spike.Lib.X64.retBlk_run lab pc (-(fr.size : Int)) σ rws hz).1, hJ.2.1.2]

/-- **`RetSlot` at a held pair whose run lands at `bodyN2`**: the held
pair's run to depth 0 lands at `cR`, of `bodyN2`'s invariant, whose
symbolic environment `s` places the frame's result `f.x` as a register
operand at a region cell (`hx`). -/
theorem retSlot_bodyN2 {lbl : Lbl} {R : Region} {fr : Scc.Emit.X64.Frame} {i : Expr → String → Nat → Option Nat}
    {fp ra : BitVec 64} {c0 : Ctl} {pc : Int64} {t : Expr} {s : Spike.Lib.Form.SEnv}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (hx : ∀ f, fs = [f] → ∃ t r, Spike.Lib.Form.lookupS s f.x = some (t, [.one (.reg r)]) ∧
      ∃ k, rsOf fr r = some k ∧ R.Off k)
    {σ : AS} {c cR : Ctl} (hH : HeldTail c fs) (hr : FrameRun p (c, fs) (cR, []))
    (hJ : (bodyN2 p lbl lsize i fr fp ra c0 pc t s lits cs bufs).J σ cR) : RetSlot p lbl R σ c := by
  obtain ⟨⟨L, sm, B, c', hloc, hJ', -⟩, -⟩ := hJ
  exact retSlot_of_heldRun hH hr hloc hJ' hx

/-! ## The return block at the held frames -/

/-- **`main`'s `ret b` block keeps the write abort's phase**
(`blkW_abSt_subCdLR`; `retHeld_hW`'s `hab`): the block a part of the code
off the write abort's labels at the return address `ra` (`hcd`), covered
(`hok`), its run from the node landing at `ra` (`hpc`, e.g.
`retDirs_pc_bodyN2`); `ra` a position off the write abort (`hpos`, e.g.
`posOff_mainRetS` at `scc_rt_main`'s return point). -/
theorem retHeld_hab {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat}
    (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (habt : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {fr : Scc.Emit.X64.Frame} {ps : List (Scc.IR.Operand × Reg64)} {lw : List Item}
    (hl : getOps fr ps = .ok lw) {zs : List Nat} (hz : zs.length = (retDirs lw).length)
    {R : Region} {F : MachineData → Prop} {n : ND} {lo hi : Int} {ra : Int64}
    (hcd : SubCd (CdCL cells okPc ph lab ra) n.pc ((retDirs lw).zip zs))
    (hok : okBlk lo hi n.o ((retDirs lw).zip zs) = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ σ c, n.J σ c → (arun lab ((retDirs lw).zip zs) ⟨n.pc, n.o, σ⟩).pc = ra)
    (hpos : PosOff cells lab ra) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n ((retDirs lw).zip zs) := by
  refine blkW_abSt_subCdLR hI hpr habt hcd hok hR hlo hhi (hret_of_run hok hpc) (.inl (retDirs_last lw hz)) ?_
  intro σ c _ k hk a ha t ht hc
  have hra := retD_retDirs hl _ (List.of_mem_zip (List.getElem_mem hk)).1 a ha
  cases a <;> simp only [RetI, Bool.false_eq_true] at hra <;> simp only [aiTgts, List.mem_singleton] at ht
  all_goals first
    | exact .inl (ht ▸ hpos)
    | (rcases hc with hc | hc
       · exact absurd ht hc
       · cases hc)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop}
  {own : Own} {rS : Range} {Tk : State → Prop} {ar : Arena} {J : InvS} {Dt Ab : State → Prop} {lbl0 : Lbl}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-- **`main`'s `ret b` block inside `W2` at the held frames**
(`blkW_heldTail`): at a node whose invariant holds the held pair (`hH`) and
the frame's result in a region cell (`hJ`, e.g. `retSlot_bodyN2`), `HeldS`
by `blkW_heldS` from the abort phase's facts (`hab`, e.g. `retHeld_hab`),
`Ret0` from the result cell (`blkW_ret0_slot`, `retDirs_slot`), no write and
no system call (the block covered, `hok`); `SFacts` at the source start's
control (`hS`). -/
theorem retHeld_hW {lbl : Lbl} (hp : ProgNoS ZBad p) {fr : Scc.Emit.X64.Frame}
    {ps : List (Scc.IR.Operand × Reg64)} {lw : List Item} (hl : getOps fr ps = .ok lw) {zs : List Nat}
    {n : ND} {lo hi : Int}
    (hcode : ∀ st : State, st.exe = exe → st.endPc = endPc → CodeAt st n.pc ((retDirs lw).zip zs))
    (hok : okBlk lo hi n.o ((retDirs lw).zip zs) = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hS : BlkW (fun s c => SFacts Λ μ own rS Tk lbl0 s c) K exe endPc R F (Spike.Lib.X64.AllocG.dumN n)
      ((retDirs lw).zip zs))
    (hH : ∀ σ c, n.J σ c → HeldTail c fs) (hJ : ∀ σ c, n.J σ c → RetSlot p lbl R σ c)
    (hab : BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n ((retDirs lw).zip zs)) :
    BlkW (fun s c => W2 Λ μ p rd G own rS Tk ar J Dt Ab lbl lsize s c fs) K exe endPc R F n
      ((retDirs lw).zip zs) :=
  blkW_heldTail hp hS hH
    (blkW_heldS hab (blkW_ret0_slot hJ fun _ k _ => retDirs_slot hl zs _ _ k)
      (blkW_noWr' hcode hok hR hlo hhi) (blkW_noSys' hcode hok))

end Spike.Lib.LowerX64

/-- info: 'Spike.Lib.LowerX64.retDirs_slot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retDirs_slot

/-- info: 'Spike.Lib.LowerX64.retHeld_hab' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retHeld_hab

/-- info: 'Spike.Lib.LowerX64.retHeld_hW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.retHeld_hW
