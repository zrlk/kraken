/-
**A call's nodes, the callee's interface and the straight-line steps**
(x86-64): the pieces of a plain call's walk (`Spike/Lib/LowerX64/CallC.lean`).

- the call's nodes: `brN` (a node at the frame's offsets with the source
  exactly at a term, the `%fs` base, the call's own facts `P`), `callN`
  (after `callq g`, `%rsp` 8 lower), `exN` (the callee's exit seen from its
  region);
- the callee's interface: `CallG`, `calleeR`, `calleeN`, `ArgV`, `CalleeF`,
  with `calleeR_ok`, `calleeR_room`, `calleeN_tp`, `ArgV.envNum`,
  `ArgV.envSmall`, `CalleeF.inF`, `CalleeF.callerCells`, `CalleeF.caller`,
  `CalleeF.callerI`, `CalleeF.framesKept`;
- pieces of the code predicate: `SubCdTo`, `SubCdTo.split`, `subCdTo_of`,
  `subCdTo_zs`, `subCdTo_one`, `zip_ne_nil`, `pcAdd`;
- steps between the nodes: `seg_blk1` (a straight block to one node),
  `getOp_seg` (an operand's load), `callq_seg` (`arun_callq`,
  `okBlk_callq`), the store to an IR register's cell (`okBlk_stDir`,
  `arun_stDir`), `brN_hit`, `brN_upd`, `at_brN_rbp`, `at_rbp_addr`;
- cells: `nodeJ_upd`, `frJ_upd`, `rsOf_ne`, `opdVal_reg`, `oB_kill_rax`,
  `frame_mod8B`, `so_le_oB8`, `opdVal_upd_out`, `nodeJ_upd_out`,
  `frJ_upd_out`, `frame_out` (`fresh_callC1` is in `Spike/Lib/LowerX64/BodyC.lean`).
-/
import Spike.Lib.LowerX64.BodyC
import Spike.Lib.X64CallSA
import Spike.Lib.X64FramesPlacedI

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (Item emitInst labelOf i64 rel xr or_ cc)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ SEnv opdVal_upd)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Scc.Lower.Inv (regName labName)
open Spike.Lib.X64.Flow.Ret0 (CallerCells)

set_option linter.unusedSimpArgs false

/-! ## The bracket's nodes and the callee's interface -/

/-- **A node of the bracket** at `pc`: the source exactly at `t` (the
environment `s` placed in the frame's cells), its words numbers, the saved
pair, the source control reached from the caller's ghost (`Rn`), the `%fs`
base `tp`, and the bracket's own facts `P` (the values it stored in its
cells and registers). -/
def brN (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (Rn : Ctl → Prop) (pc : Int64) (t : Expr) (s : SEnv) (P : AS → Prop) : ND :=
  ⟨pc, oB fr, fun σ c => NodeJ lbl (rsOf fr) t s σ.slot c ∧ EnvNum c.env ∧ FrJ fp ra σ.slot ∧ Rn c ∧
    σ.regs.fsBase = tp ∧ P σ⟩

/-- **The callee's ghost at a call**: the caller's frame pointer, the return
address, the argument in `%rdi`, the callee's entry control. -/
structure CallG where
  fp : BitVec 64
  ra : BitVec 64
  v : BitVec 64
  cE : Ctl

/-- **The callee's region** below a frame of `size` bytes with room `D`:
based at the call node's `%rsp` (the return address pushed), from `-D` to
`8` (the return address's cell). -/
def calleeR (R : Region) (size : Nat) (D : Int) : Region := R.callee (-(size : Int) - 8) (-D) 8

/-- **The callee's entry** at `g`'s label (`%rsp` at the callee's region's
offset `0`, `FnSpecC`'s entry): the source at the callee's entry control,
`%rbp` the caller's frame pointer, the return address in slot `0`, `%rdi`
the argument, the `%fs` base `tp`. -/
def calleeN (lab : Label → Int64) (g : String) (tp : UInt64) (q : CallG) : ND :=
  ⟨lab (Scc.Lower.Names.user g), ⟨0, []⟩, fun σ c => c = q.cE ∧ σ.regs.rbp.toBitVec = q.fp ∧
    σ.slot 0 = q.ra ∧ σ.regs.rdi.toBitVec = q.v ∧ σ.regs.fsBase = tp⟩

/-- **The callee's argument**: the entry control binds one variable to one
word, a number below `2^64` represented by `%rdi`'s value `q.v`. -/
def ArgV (lbl : WeakMem.AllocLabel → Option Nat) (q : CallG) : Prop :=
  ∃ x t w, q.cE.env = [(x, t, [w])] ∧ ValRep lbl w.val q.v.toNat ∧ ∃ k, w.val = .num k ∧ k < 2 ^ 64

/-- **The callee's frame condition at a call** (`call_ndSF`'s): the
caller's `F`, the caller's cells outside the callee's region holding values
(`CallerCells`), and the caller's state at the call (`mC`, `σC` at the
call node's offsets, the frame's with `%rsp` 8 lower after `callq`'s push,
the cells outside the callee's region kept from `mC`), its
source control `c` calling `q.cE` with the frame `frm` pushed, at a term in
`T` whose environment `s` the frame's cells place, numeric, the saved pair
in its cells, the continuation `frm.body`'s free variables but the result
`frm.x` bound in `s`, its immediates but `frm.x`'s the table `i`'s at
`frm.body`. -/
def CalleeF (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (R : Region)
    (F : MachineData → Prop) (D : Int) (fp ra : BitVec 64) (i : Expr → String → Nat → Option Nat)
    (T : Expr → Prop) (q : CallG) (frm : TermRun.Frame) (F' : MachineData → Prop) : Prop :=
  ∀ m, F' m → F m ∧ CallerCells R (-(fr.size : Int) - 8) (-D) 8 m ∧
    ∃ mC σC c t s, Abs R { oB fr with sp := (oB fr).sp - 8 } mC σC ∧ CKept R (-(fr.size : Int) - 8) (-D) 8 mC m ∧
      CallTo p c q.cE frm ∧ T t ∧ NodeJ lbl (rsOf fr) t s σC.slot c ∧ EnvNum c.env ∧ FrJ fp ra σC.slot ∧
      (∀ y ∈ Scc.Sem.exprFv frm.body, y ≠ frm.x → (Spike.Lib.Form.lookupS s y).isSome) ∧
      ∀ y k v, y ≠ frm.x → (Spike.Lib.Form.lookupS s y).bind (·.2[k]?) = some (.one (.imm v)) →
        i frm.body y k = some v.toNat


/-! ## The code predicate's call arm -/

/-- **A non-call instruction's arm of `CodeC`**: its items at `pc` (`Cd`),
then the rest at the pc past them. -/
theorem codeC_inst {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {k : Nat} {pc : Int64} {i : Scc.IR.Inst} {is : List Scc.IR.Inst}
    {tm : Scc.IR.Term} (h : CodeC fr Cd Bl k pc (i :: is) tm) (hc : Spike.Lib.LowerShape.isCall i = false) :
    ∃ l zs, Emits (emitInst fr none i) l ∧ zs.length = (dirs l).length ∧ Cd pc ((dirs l).zip zs) ∧
      CodeC fr Cd Bl k (pc + Int64.ofNat zs.sum) is tm := by
  rcases h with ⟨-, h⟩ | ⟨d, g, w, lw, off, zs, zc, z, rfl, -⟩
  · exact h
  · simp [Spike.Lib.LowerShape.isCall] at hc

/-- **A one-word user call's arm of `CodeC`**: the argument's load into
`%rdi` at `pc` (`Cd`), `callq g` with the return label `.L<fn>.x<k>` after
it (`Bl`), the result's store (`Cd`), then the rest from `k + 1`. -/
theorem codeC_call {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {k : Nat} {pc : Int64} {d : Scc.IR.Reg} {g : String}
    {w : Scc.IR.Operand} {is : List Scc.IR.Inst} {tm : Scc.IR.Term}
    (h : CodeC fr Cd Bl k pc (.call [d] (Scc.Lower.Names.user g) [w] :: is) tm) :
    ∃ lw off zs zc z, getOp fr .rdi w = .ok lw ∧ rsOf fr d = some off ∧ zs.length = (dirs lw).length ∧
      Cd pc ((dirs lw).zip zs) ∧ Bl (pc + Int64.ofNat zs.sum) zc (Scc.Lower.Names.user g) k ∧
      Cd (pc + Int64.ofNat zs.sum + Int64.ofNat zc) [(stDir off, z)] ∧
      CodeC fr Cd Bl (k + 1) (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) is tm := by
  rcases h with ⟨hc, -⟩ | ⟨d', g', w', lw, off, zs, zc, z, he, hw, hd, hz, h1, h2, h3, h4⟩
  · simp [Spike.Lib.LowerShape.isCall] at hc
  · have hu : Scc.Lower.Names.user g = Scc.Lower.Names.user g' ∧ d = d' ∧ w = w' := by
      simp only [Scc.IR.Inst.call.injEq, List.cons.injEq, and_true] at he
      exact ⟨he.2.1, he.1, he.2.2⟩
    obtain ⟨hg, rfl, rfl⟩ := hu
    rw [← hg] at h2
    exact ⟨lw, off, zs, zc, z, hw, hd, hz, h1, h2, h3, h4⟩

/-! ## Steps between the nodes -/

section Edges

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop} {K : State → State → Prop}

/-- **A sized piece `ds` of a block of `Cd` from `pc` to `pc'`**: at some
cell sizes `zs`, a sub-block (`SubCd`) at `pc`, `pc'` past it. -/
def SubCdTo (Cd : Int64 → List (Directive × Nat) → Prop) (pc : Int64) (ds : List Directive) (pc' : Int64) :
    Prop :=
  ∃ zs : List Nat, zs.length = ds.length ∧ SubCd Cd pc (ds.zip zs) ∧ pc' = pc + Int64.ofNat zs.sum

/-- **A piece splits** at the end of `A`. -/
theorem SubCdTo.split {Cd : Int64 → List (Directive × Nat) → Prop} {pc pc'' : Int64} {A B : List Directive}
    (h : SubCdTo Cd pc (A ++ B) pc'') : ∃ pc', SubCdTo Cd pc A pc' ∧ SubCdTo Cd pc' B pc'' := by
  obtain ⟨zs, hz, hs, rfl⟩ := h
  obtain ⟨zs1, zs2, rfl, h1, h2, s1, s2⟩ := subCd_split hz hs
  refine ⟨_, ⟨zs1, h1, s1, rfl⟩, zs2, h2, s2, ?_⟩
  rw [List.sum_append, Int64.ofNat_add, Int64.add_assoc]

/-- **A block of `Cd` is a piece**, its directives as `ds`. -/
theorem subCdTo_of {Cd : Int64 → List (Directive × Nat) → Prop} {pc : Int64} {l : List Item} {zs : List Nat}
    {ds : List Directive} (hz : zs.length = (dirs l).length) (hc : Cd pc ((dirs l).zip zs)) (he : dirs l = ds) :
    SubCdTo Cd pc ds (pc + Int64.ofNat zs.sum) := by
  subst he
  exact ⟨zs, hz, SubCd.whole hc, rfl⟩

/-- **A straight block's segment to one node**: `BlkEdge.seg` with one
internal node and no exit. -/
theorem seg_blk1 {ms0 : MemSide isa} {W₀ : Frag isa} {lo hi : Int} {n n' : ND} {blk : List (Directive × Nat)}
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : CdOf exe endPc n.pc blk) (hW : BlkW W₀ K exe endPc R F n blk)
    (hne : blk ≠ []) (hok : okBlk lo hi n.o blk = true)
    (h : ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧
      Hit n' (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩) c') :
    SegW W₀ K p lbl ms0 (At exe endPc R F n) (At exe endPc R F n') :=
  (BlkEdge.seg (N := fun _ : Unit => n') (E := fun e : Empty => e.elim)
    ⟨hne, hok, fun σ c hJ => let ⟨c', hr, hh⟩ := h σ c hJ; ⟨c', hr, .inl ⟨(), hh⟩⟩⟩
    hF hR hlo hhi hcode hW).mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-- **A write to a fresh register's cell keeps the node's environment.** -/
theorem nodeJ_upd {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {y : String} {m : Nat} (hm : n ≤ m) {off : Int} (ho : rsOf fr (regName y m) = some off) {t : Expr}
    {sl : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl (rsOf fr) t (ofEnv env) sl c) (v : BitVec 64) :
    NodeJ lbl (rsOf fr) t (ofEnv env) (upd sl off v) c := by
  refine ⟨h.1, h.2.1, h.2.2.congr fun b hb pl hpl o hoo => opdVal_upd fun r k hr hk => ?_⟩
  have hne := Fresh.ofEnv (hfr.mono hm) y b hb pl hpl o hoo r hr
  rw [upd_apply]
  split
  · next hk' => subst hk'; exact absurd (rsOf_inj hf hk ho) hne
  · rfl

/-- A write to an IR register's cell keeps the saved pair. -/
theorem frJ_upd {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {fp ra : BitVec 64} {sl : Int → BitVec 64}
    (h : FrJ fp ra sl) {r : Scc.IR.Reg} {k : Int} (hk : rsOf fr r = some k) (v : BitVec 64) :
    FrJ fp ra (upd sl k v) := by
  obtain ⟨h8, -, -⟩ := rsOf_bounds hf hk
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩ <;> rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))] <;> assumption

/-- Different bracket registers have different cells. -/
theorem rsOf_ne {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {y y' : String} {m m' : Nat} (hm : m ≠ m')
    {o o' : Int} (ho : rsOf fr (regName y m) = some o) (ho' : rsOf fr (regName y' m') = some o') : o ≠ o' :=
  fun h => Scc.Lower.Inv.regName_ne hm (rsOf_inj hf ho (h ▸ ho'))

theorem pcAdd (pc : Int64) (a b : Nat) : pc + Int64.ofNat a + Int64.ofNat b = pc + Int64.ofNat (a + b) := by
  rw [Int64.add_assoc, ← Int64.ofNat_add]

/-- **A piece of `Cd` in closed form**: its cell sizes. -/
theorem subCdTo_zs {Cd : Int64 → List (Directive × Nat) → Prop} {pc pc' : Int64} {ds : List Directive}
    (h : SubCdTo Cd pc ds pc') :
    ∃ zs : List Nat, zs.length = ds.length ∧ SubCd Cd pc (ds.zip zs) ∧ pc' = pc + Int64.ofNat zs.sum := h

/-- A one-directive piece: its cell size `z`. -/
theorem subCdTo_one {Cd : Int64 → List (Directive × Nat) → Prop} {pc pc' : Int64} {d : Directive}
    (h : SubCdTo Cd pc [d] pc') : ∃ z, SubCd Cd pc [(d, z)] ∧ pc' = pc + Int64.ofNat z := by
  obtain ⟨zs, hz, hs, rfl⟩ := h
  obtain ⟨z, rfl⟩ := length_one hz
  exact ⟨z, hs, by simp⟩

theorem zip_ne_nil {ds : List Directive} {zs : List Nat} (hz : zs.length = ds.length) (h : ds ≠ []) :
    ds.zip zs ≠ [] := by
  cases ds with
  | nil => exact absurd rfl h
  | cons d ds => cases zs with
    | nil => simp at hz
    | cons z zs => simp

theorem oB_kill_rax (fr : Scc.Emit.X64.Frame) : (oB fr).kill .rax = oB fr := by simp [oB, SO.kill, rm]

/-- **A step of the bracket's nodes**: a run from a bracket node ending at
`pc'` at the frame's offsets, the `%fs` base kept, the source's cells and
the saved pair kept (`hsl`), the bracket's facts from `P` to `P'`. -/
theorem brN_hit {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64} {Rn : Ctl → Prop}
    {pc pc' : Int64} {t : Expr} {s : SEnv} {P P' : AS → Prop} {am : AM} {σ : AS} {c : Ctl}
    (h : (brN lbl fr fp ra tp Rn pc t s P).J σ c) (hpc : am.pc = pc') (hso : am.so = oB fr)
    (hfs : am.σ.regs.fsBase = σ.regs.fsBase)
    (hsl : NodeJ lbl (rsOf fr) t s σ.slot c → FrJ fp ra σ.slot →
      NodeJ lbl (rsOf fr) t s am.σ.slot c ∧ FrJ fp ra am.σ.slot)
    (hP : P σ → P' am.σ) : Hit (brN lbl fr fp ra tp Rn pc' t s P') am c := by
  obtain ⟨hj, hn, hfj, hr, htp, hp⟩ := h
  obtain ⟨hj', hfj'⟩ := hsl hj hfj
  exact ⟨hpc.symm, by rw [hso]; exact so_le_oB fr, hj', hn, hfj', hr, hfs.trans htp, hP hp⟩

/-- A store to a fresh bracket register's cell keeps the source's cells and
the saved pair. -/
theorem brN_upd {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {env : Scc.Lower.Env} {n : Nat} (hfr : Fresh env n)
    {y : String} {m : Nat} (hm : n ≤ m) {o : Int} (ho : rsOf fr (regName y m) = some o) {t : Expr}
    {fp ra : BitVec 64} {sl : Int → BitVec 64} {c : Ctl} (v : BitVec 64)
    (hj : NodeJ lbl (rsOf fr) t (ofEnv env) sl c) (hfj : FrJ fp ra sl) :
    NodeJ lbl (rsOf fr) t (ofEnv env) (upd sl o v) c ∧ FrJ fp ra (upd sl o v) :=
  ⟨nodeJ_upd hf hfr hm ho hj v, frJ_upd hf hfj ho v⟩

/-- A register operand's value is its cell's. -/
theorem opdVal_reg {fr : Scc.Emit.X64.Frame} {r : Scc.IR.Reg} {o : Int} (ho : rsOf fr r = some o)
    {sl : Int → BitVec 64} {v : BitVec 64} (h : opdVal (rsOf fr) sl (.reg r) = some v.toNat) : v = sl o := by
  simp only [opdVal, ho, Option.map_some, Option.some.injEq] at h
  exact (BitVec.eq_of_toNat_eq h).symm

/-- The store `movq %rax, off(%rbp)` to an IR register's cell is covered in
the frame's region. -/
theorem okBlk_stDir {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Scc.IR.Reg}
    {off : Int} (hd : rsOf fr d = some off) (z : Nat) :
    okBlk (-(fr.size : Int)) 16 (oB fr) [(stDir off, z)] = true := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : X64.classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  simp only [okBlk, hc, AI.ok, AI.isTerm, AI.so, oB, SO.get, lk, ho, offOk]
  simp
  omega

/-- **The store's run**: the cell `off` gets `%rax`. -/
theorem arun_stDir {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Scc.IR.Reg}
    {off : Int} (hd : rsOf fr d = some off) (lab : String → Int64) (pc : Int64) (σ : AS) (z : Nat) :
    arun lab [(stDir off, z)] ⟨pc, oB fr, σ⟩ =
      ⟨pc + Int64.ofNat z, oB fr, { σ with slot := upd σ.slot off (σ.regs.get64 .rax) }⟩ := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : X64.classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  simp [arun, dstep, hc, AI.tgt, AI.so, AI.step, oB, SO.get, lk, ho]

/-- **An operand's load between bracket nodes**: `getOp`'s block from `pc`
to `pc'`, the temporary `tr` getting the operand's value, the bracket's
facts from `P` to `P'` (`hP`). -/
theorem getOp_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {G0 Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c)
    (hWB : ∀ (n : ND) blk, SubCd Cd n.pc blk → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n blk)
    {tr : Reg64} (ht : tr ≠ .rsp) (ht' : tr ≠ .rbp) {a : Scc.IR.Operand} {l : List Scc.Emit.X64.Item}
    (hl : getOp fr tr a = .ok l) {pc pc' : Int64} (hc : SubCdTo Cd pc (dirs l) pc') {t : Expr} {s : SEnv}
    {P P' : AS → Prop}
    (hP : ∀ σ (v : BitVec 64), P σ → opdVal (rsOf fr) σ.slot a = some v.toNat →
      P' { σ with regs := σ.regs.set64 tr v }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (brN lbl fr fp ra tp Rn pc t s P))
      (At exe endPc R F (brN lbl fr fp ra tp Rn pc' t s P')) := by
  obtain ⟨zs, hz, hs, hp⟩ := hc
  obtain ⟨dl, hdl⟩ := dirs_getOp hl
  refine seg_blk1 hF hR hlo hhi (hs.cdOf hCd)
    (hWB _ _ hs rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (zip_ne_nil hz (by rw [hdl]; simp))
    (by
      have := okBlk_getOp hf h1 ht ht' hl hz []
      rw [List.append_nil] at this
      show okBlk _ _ (oB fr) _ = true
      rw [this]; rfl)
    fun σ c hJ => ⟨c, .refl c, ?_⟩
  obtain ⟨v, hv, hr⟩ := arun_getOp hf h1 ht' hl (_root_.Executable.labels exe).label pc σ hz
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c
  rw [hr]
  exact brN_hit hJ hp.symm rfl (Reg64s.set64_fsBase _ _ _) (fun a b => ⟨a, b⟩) fun h => hP σ v h hv

/-- **The call node** at `pc` (the callee's label): the bracket's node
(`brN`) after `callq g`, `%rsp` 8 lower (the return address pushed). -/
def callN (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (tp : UInt64)
    (Rn : Ctl → Prop) (pc : Int64) (t : Expr) (s : SEnv) (P : AS → Prop) : ND :=
  ⟨pc, { oB fr with sp := (oB fr).sp - 8 }, fun σ c => NodeJ lbl (rsOf fr) t s σ.slot c ∧ EnvNum c.env ∧
    FrJ fp ra σ.slot ∧ Rn c ∧ σ.regs.fsBase = tp ∧ P σ⟩

/-- **`callq g`'s run**: to `g`'s label, `%rsp` 8 lower, the return address
(the pc past the call) in the cell below `%rsp`. -/
theorem arun_callq (lab : String → Int64) (pc : Int64) (o : SO) (σ : AS) (g : String) (z : Nat) :
    arun lab [(i64 (.call (rel g)), z)] ⟨pc, o, σ⟩ = ⟨lab g, { o with sp := o.sp - 8 },
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64),
               slot := upd σ.slot (o.sp - 8) (pc + Int64.ofNat z).toBitVec }⟩ := by
  simp [arun, dstep, i64, Scc.Emit.X64.op, rel, X64.classify, AI.step, AI.tgt, AI.so]

/-- `callq g` is covered when the return address's cell is. -/
theorem okBlk_callq {lo hi : Int} {o : SO} (g : String) (z : Nat) (h : offOk lo hi (o.sp - 8) = true) :
    okBlk lo hi o [(i64 (.call (rel g)), z)] = true := by
  simp [okBlk, i64, Scc.Emit.X64.op, rel, X64.classify, AI.ok, AI.isTerm, h]

/-- A valid frame's size is a multiple of 8 (`frameOf_size`). -/
theorem frame_mod8B {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) : fr.size % 8 = 0 := by
  obtain ⟨areas, f, -, hsz⟩ := hf
  rw [hsz, frameOf_size]
  omega

theorem so_le_oB8 (fr : Scc.Emit.X64.Frame) :
    SO.le { oB fr with sp := (oB fr).sp - 8 } { oB fr with sp := (oB fr).sp - 8 } = true := by
  simp [SO.le, oB, lk]

/-- A cell below the frame is no operand's. -/
theorem opdVal_upd_out {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {k : Int} (hk : k < -(fr.size : Int))
    (sl : Int → BitVec 64) (v : BitVec 64) (o : Scc.IR.Operand) :
    opdVal (rsOf fr) (upd sl k v) o = opdVal (rsOf fr) sl o :=
  opdVal_upd fun r k' _ hk' => by
    obtain ⟨-, -, hle⟩ := rsOf_bounds hf hk'
    rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))]

/-- **A write below the frame keeps the source's cells.** -/
theorem nodeJ_upd_out {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {k : Int} (hk : k < -(fr.size : Int))
    {t : Expr} {s : SEnv} {sl : Int → BitVec 64} {c : Ctl} (h : NodeJ lbl (rsOf fr) t s sl c) (v : BitVec 64) :
    NodeJ lbl (rsOf fr) t s (upd sl k v) c :=
  ⟨h.1, h.2.1, h.2.2.congr fun _ _ _ _ o _ => opdVal_upd_out hf hk sl v o⟩

/-- **A write below the frame keeps the saved pair.** -/
theorem frJ_upd_out {fp ra : BitVec 64} {sl : Int → BitVec 64} (h : FrJ fp ra sl) {k : Int} (hk : k < 0)
    (v : BitVec 64) : FrJ fp ra (upd sl k v) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨?_, ?_⟩ <;> rw [upd_apply, ite_eq_right_of_eq_false _ _ (eq_false (by omega))] <;> assumption

/-- **`callq g` is one segment**: from the bracket's node at the call (`Bl`)
to the call node at `g`'s label, the return address `pc + zc` pushed into
the cell `-(size) - 8`; the bracket's facts from `P` to `P'` (`hP`). -/
theorem callq_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int) - 8) (hhi : 16 ≤ R.hi)
    {ms0 : MemSide isa} {W₀ : Frag isa} {fp ra : BitVec 64} {tp : UInt64}
    {Bl : Int64 → Nat → Label → Nat → Prop}
    (hBl : ∀ pc zc g k, Bl pc zc g k → CdOf exe endPc pc [(i64 (.call (rel g)), zc)])
    {G0 Rn : Ctl → Prop} (hG : ∀ c, Rn c → G0 c)
    (hWBl : ∀ (n : ND) zc g k, Bl n.pc zc g k → n.o = oB fr → (∀ σ c, n.J σ c → G0 c ∧ FrJ fp ra σ.slot) →
      BlkW W₀ K exe endPc R F n [(i64 (.call (rel g)), zc)])
    {pc : Int64} {zc : Nat} {g : Label} {k : Nat} (hb : Bl pc zc g k) {t : Expr} {s : SEnv} {P P' : AS → Prop}
    (hP : ∀ σ, P σ → P'
      { σ with regs := σ.regs.set64 .rsp (σ.regs.get64 .rsp - 8#64),
               slot := upd σ.slot (-(fr.size : Int) - 8) (pc + Int64.ofNat zc).toBitVec }) :
    SegW W₀ K p lbl ms0 (At exe endPc R F (brN lbl fr fp ra tp Rn pc t s P))
      (At exe endPc R F (callN lbl fr fp ra tp Rn ((_root_.Executable.labels exe).label g) t s P')) := by
  have h8 := frame_mod8B hf
  refine seg_blk1 (lo := -(fr.size : Int) - 8) (hi := 16) hF hR hlo hhi (hBl _ _ _ _ hb)
    (hWBl _ _ _ _ hb rfl fun σ c h => ⟨hG c h.2.2.2.1, h.2.2.1⟩) (by simp)
    (okBlk_callq _ _ (by simp [offOk, brN, oB]; omega)) fun σ c hJ => ⟨c, .refl c, ?_⟩
  show Hit _ (arun _ _ ⟨pc, oB fr, σ⟩) c
  rw [arun_callq]
  obtain ⟨hj, hn, hfj, hr, htp, hp⟩ := hJ
  have hk : (oB fr).sp - 8 = -(fr.size : Int) - 8 := rfl
  refine ⟨rfl, so_le_oB8 fr, ?_, hn, ?_, hr, ?_, ?_⟩
  · show NodeJ _ _ _ _ (upd _ ((oB fr).sp - 8) _) c
    rw [hk]; exact nodeJ_upd_out hf (by omega) hj _
  · show FrJ _ _ (upd _ ((oB fr).sp - 8) _)
    rw [hk]; exact frJ_upd_out hfj (by omega) _
  · show (σ.regs.set64 .rsp _).fsBase = tp
    rw [Reg64s.set64_fsBase]; exact htp
  · show P' { σ with regs := _, slot := upd _ ((oB fr).sp - 8) _ }
    rw [hk]; exact hP σ hp

/-- **A bracket node's `%rbp`** at its offset `0` (the region's base),
claimed in its invariant. -/
theorem at_brN_rbp {fr : Scc.Emit.X64.Frame} {fp ra : BitVec 64} {tp : UInt64} {Rn : Ctl → Prop} {pc : Int64}
    {t : Expr} {s : SEnv} {P : AS → Prop} {st : State} {c : Ctl}
    (h : At exe endPc R F (brN lbl fr fp ra tp Rn pc t s P) st c) :
    At exe endPc R F (brN lbl fr fp ra tp Rn pc t s fun σ => P σ ∧ σ.regs.get64 .rbp = R.addr 0) st c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hj, hen, hfj, hr, htp, hp⟩ := h
  exact ⟨he, hn, hdc, hpc, σ, hA, hD, hj, hen, hfj, hr, htp, hp, hA.so .rbp 0 (by simp [brN, oB, SO.get, lk])⟩

/-- **A frame cell is outside the callee's region**: a cell of the frame
or of its record (`[-(size), 16)`) is a cell of the caller's region, not of
the callee's below the return address. -/
theorem frame_out {R : Region} {size : Nat} {D : Int} (hlo : R.lo ≤ -(size : Int) - 8 - D) (hhi : 16 ≤ R.hi)
    (hD0 : 0 ≤ D) {k : Int} (hk8 : k % 8 = 0) (hk1 : -(size : Int) ≤ k) (hk2 : k + 8 ≤ 16) :
    R.Off k ∧ ¬ (R.callee (-(size : Int) - 8) (-D) 8).Off (k - (-(size : Int) - 8)) := by
  simp only [Region.Off, Region.callee]
  omega

/-- **The callee's exit seen from its region** (`ExitC`'s return at `⟨16,
[]⟩` in the rebased region is `⟨8, []⟩` here, `at_of_rbR`): the callee's
entry control `q.cE` runs at the pushed frames to `c0'`, from which the
return's exit holds. -/
def exN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (tp : UInt64) (fs : List TermRun.Frame) (q : CallG)
    (frm : TermRun.Frame) (c0' : Ctl) : ND :=
  ⟨Int64.ofBitVec q.ra, ⟨8, []⟩, fun σ c => FrameRun p (q.cE, frm :: fs) (c0', frm :: fs) ∧
    ((retN p lbl q.fp q.ra c0').withTp tp).J { σ with slot := shSl σ.slot } c⟩

/-- **`%rbp` at the region's offset `k`** in a node's invariant makes it a
static offset. -/
theorem at_rbp_addr {pc : Int64} {sp k : Int} {rs : List (Reg64 × Int)} {J : AS → Ctl → Prop} {s : State}
    {c : Ctl} (h : At exe endPc R F ⟨pc, ⟨sp, rs⟩, J⟩ s c) (hJ : ∀ σ c, J σ c → σ.regs.get64 .rbp = R.addr k) :
    At exe endPc R F ⟨pc, ⟨sp, (.rbp, k) :: rs⟩, J⟩ s c := by
  obtain ⟨he, hn, hdc, hpc, σ, hA, hD, hJ'⟩ := h
  refine ⟨he, hn, hdc, hpc, σ, ⟨hA.regs, hA.zmms, hA.status, fun r k' hk => ?_, hA.slot⟩, hD, hJ'⟩
  unfold SO.get at hk
  split at hk
  · rename_i hr; subst hr; cases hk; exact hA.so .rsp sp (SO.get_rsp _)
  · rename_i hr
    simp only [lk] at hk
    split at hk
    · rename_i hb; subst hb; cases hk; exact hJ σ c hJ'
    · exact hA.so r k' (by simp only [SO.get, hr, ↓reduceIte]; exact hk)

end Edges

/-! ## The interface's facts -/

/-- **The callee's region is a region**, within the caller's room
(`CallC`'s `hlo`, `hhi`). -/
theorem calleeR_ok {R : Region} {size : Nat} {D : Int} (hR : R.OK) (hD0 : 0 ≤ D)
    (hlo : R.lo ≤ -(size : Int) - 8 - D) (hhi : 0 ≤ R.hi) : (calleeR R size D).OK :=
  Region.callee_ok hR (by omega) (by omega) (by omega) (by omega)

/-- **The callee's room** (`FnSpecC`'s `R.lo ≤ -8 - size`, `8 ≤ R.hi`): a
callee frame of `size'` bytes fits when `8 + size' ≤ D`. -/
theorem calleeR_room {R : Region} {size size' : Nat} {D : Int} (hD : 8 + (size' : Int) ≤ D) :
    (calleeR R size D).lo ≤ -8 - (size' : Int) ∧ 8 ≤ (calleeR R size D).hi := by
  simp only [calleeR, Region.callee]
  omega

/-- **The callee's entry has the `%fs` base `tp`** (`FnSpecC`'s `htp`). -/
theorem calleeN_tp {lab : Label → Int64} {g : String} {tp : UInt64} {q : CallG} :
    ∀ σ c, (calleeN lab g tp q).J σ c → σ.regs.fsBase = tp :=
  fun _ _ h => h.2.2.2.2

/-- **The callee's entry environment is numeric.** -/
theorem ArgV.envNum {lbl : WeakMem.AllocLabel → Option Nat} {q : CallG} (h : ArgV lbl q) : EnvNum q.cE.env := by
  obtain ⟨x, t, w, he, -, k, hk, hlt⟩ := h
  rw [he]
  exact envNum_entry hk hlt

/-- **The callee's entry environment is small.** -/
theorem ArgV.envSmall {lbl : WeakMem.AllocLabel → Option Nat} {q : CallG} (h : ArgV lbl q) :
    EnvSmall q.cE.env :=
  AbortSrc.envSmall_of_envNum h.envNum

section CalleeF

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {fr : Scc.Emit.X64.Frame} {R : Region}
  {F : MachineData → Prop} {D : Int} {fp ra : BitVec 64} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop}
  {q : CallG} {frm : TermRun.Frame} {F' : MachineData → Prop}

/-- The callee's frame condition is inside the caller's. -/
theorem CalleeF.inF (h : CalleeF p lbl fr R F D fp ra i T q frm F') : ∀ m, F' m → F m :=
  fun m hm => (h m hm).1

/-- The caller's cells outside the callee's region hold values. -/
theorem CalleeF.callerCells (h : CalleeF p lbl fr R F D fp ra i T q frm F') :
    ∀ m, F' m → CallerCells R (-(fr.size : Int) - 8) (-D) 8 m :=
  fun m hm => (h m hm).2.1

/-- **The caller at the call** under the callee's frame condition: its
state, its source control calling the callee's entry with `frm` pushed
(`SrcCallTo`), placed in its frame's cells, numeric, at a term in `T`. -/
theorem CalleeF.caller (h : CalleeF p lbl fr R F D fp ra i T q frm F') {m : MachineData} (hm : F' m) :
    ∃ mC σC c t s, Abs R { oB fr with sp := (oB fr).sp - 8 } mC σC ∧ CKept R (-(fr.size : Int) - 8) (-D) 8 mC m ∧
      SrcCallTo p c q.cE frm ∧ T t ∧ NodeJ lbl (rsOf fr) t s σC.slot c ∧ EnvNum c.env ∧ FrJ fp ra σC.slot := by
  obtain ⟨mC, σC, c, t, s, hA, hk, hc, hT, hj, hn, hf, -, -⟩ := (h m hm).2.2
  exact ⟨mC, σC, c, t, s, hA, hk, hc, hT, hj, hn, hf⟩

/-- **The caller at the call** with the continuation's free variables but
the result bound in its symbolic environment, their immediates the table
`i`'s at the continuation. -/
theorem CalleeF.callerI (h : CalleeF p lbl fr R F D fp ra i T q frm F') {m : MachineData} (hm : F' m) :
    ∃ mC σC c t s, Abs R { oB fr with sp := (oB fr).sp - 8 } mC σC ∧ CKept R (-(fr.size : Int) - 8) (-D) 8 mC m ∧
      CallTo p c q.cE frm ∧ T t ∧ NodeJ lbl (rsOf fr) t s σC.slot c ∧ EnvNum c.env ∧ FrJ fp ra σC.slot ∧
      (∀ y ∈ Scc.Sem.exprFv frm.body, y ≠ frm.x → (Spike.Lib.Form.lookupS s y).isSome) ∧
      ∀ y k v, y ≠ frm.x → (Spike.Lib.Form.lookupS s y).bind (·.2[k]?) = some (.one (.imm v)) →
        i frm.body y k = some v.toNat :=
  (h m hm).2.2

/-- **The caller's frames kept placed in the callee**: frames placed in the
slots of `A` (caller cells outside the callee's region) at a state `sC` of
the caller's memory `mC` stay placed at a state `s` of every memory the
callee's frame condition admits (`FramesPlacedInI.of_cKept`). -/
theorem CalleeF.framesKept {Λ : Scc.Sem.Layout} {lbl' : Spike.Lib.X64Consumer.Lbl} {A : Nat → Prop}
    {fs : List TermRun.Frame} {mC : MachineData} {sC s : State} (hsC : sC.st.1 = mC)
    (hk : CKept R (-(fr.size : Int) - 8) (-D) 8 mC s.st.1)
    (hf : Spike.Lib.X64ConsumerS.FramesPlacedInI Λ lbl' sC fs A)
    (hA : ∀ a, A a → ∃ k, R.Off k ∧ ¬ (R.callee (-(fr.size : Int) - 8) (-D) 8).Off (k - (-(fr.size : Int) - 8)) ∧
      a = (R.addr k).toNat) :
    Spike.Lib.X64ConsumerS.FramesPlacedInI Λ lbl' s fs A :=
  hf.of_cKept (hsC ▸ hk) hA

end CalleeF

end Spike.Lib.LowerX64
