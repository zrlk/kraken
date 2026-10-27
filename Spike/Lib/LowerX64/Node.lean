/-
**Per-construct segments** (x86-64), symbolic in the frame, the IR
registers' slots, the pc, the cell sizes and the source; the twin of
`Spike/Lib/LowerA64/Node.lean`.

The node invariant at a point of a lowered `Accepted0` body is `NJ`: the
source runs locally to a control at the point's term whose environment the
lowering's environment (`ofEnv`) represents, operands valued in the frame's
slots (`rsOf`), and the frame record's saved `%rbp` and return address are
the ghosts `fp`/`ra` (`FrJ`).

- `NJ.atom`: `let x = a` emits nothing; the node invariant moves past it.
- `add_seg`: the checked `+`'s block (operand loads, `addq`, `jc`) lands at
  the pending-store node (`pendN`: the source has added, `x`'s slot valued
  by `%rax`) or, on carry, at the overflow abort label with the source at
  the `+` about to overflow (`AbJ`: `OvfReady`, every bound word a number,
  the environment placed in the frame's cells, the free variables placed,
  its immediates the table `i`'s at the source's term, `ImmIn`).
- `store_seg`: the store `movq %rax, off(%rbp)` lands at the next node.
- `ret_seg`: `ret a` (the operand's load into `%rax`, the epilogue, `ret`)
  lands at the saved return address with `%rax` representing `a`'s word
  (`RetJ`).

Where x86-64 differs from AArch64:
- a block is `ds.zip zs` at any cell sizes `zs` of its length (`hz`), and
  the pc after it is `pc + Int64.ofNat zs.sum` (AArch64: `pc + 4 * length`);
- the body runs at `%rbp`-based offsets (`oB`): the region `[-size, 16)` is
  based at the frame record, the saved `%rbp` in cell `0`, the return
  address in cell `8` (AArch64: `x29`/`x30` at `-16`/`-8` from the region's
  top, `sp`-based); an IR register's cell is its slot offset itself, no
  `- frame` shift;
- the overflow abort label is the function's `ovf` label (`labelOf fr.fn
  "ovf"`, AArch64: `cx.local "abort_overflow"`);
- `ret` pops the return address, so the exit's offsets are `⟨16, []⟩` and
  `RetJ` restores `%rbp` only (AArch64: `x29` and `x30`, at `⟨0, []⟩`);
- no region alignment hypothesis (`seg_ndW` on x64 has none).
-/
import Spike.Lib.LowerX64.Construct
import Spike.Lib.LowerX64.Checks
import Spike.Lib.LowerNode
import Spike.Lib.LowerEnvImm
import Spike.Lib.Src
import Spike.Lib.Typed

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item ld st frameOf i64 xr xm om or_ mem labelOf)
open Scc.Lower.InvX64
open Spike.Lib.Form (opdVal NodeJ SEnv sevalAt lookupS WordPl WordsRep WordRep SRep)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode

set_option linter.unusedSimpArgs false

/-! ## The frame's nodes (x86-64) -/

variable {p : Prog}

/-- **The saved frame pointer and return address** in the frame record's
cells (`%rbp`-relative). -/
def FrJ (fp ra : BitVec 64) (sl : Int → BitVec 64) : Prop := sl 0 = fp ∧ sl 8 = ra

/-- **A node of the body** at `pc`, term `t`, symbolic environment `s`;
the source control reached locally from the ghost `c0` (the function's
entry). -/
def bodyN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64)
    (c0 : Ctl) (pc : Int64) (t : Expr) (s : SEnv) : ND :=
  ⟨pc, oB fr, fun σ c => NJ p lbl (rsOf fr) t s σ.slot c ∧ FrJ fp ra σ.slot ∧ LocalRun p c0 c⟩

/-- **The pending store** of a checked `+`: the source has added, `x`'s
cell `k` valued by `%rax`. -/
def pendN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64)
    (c0 : Ctl) (pc : Int64) (t : Expr) (s : SEnv) (k : Int) : ND :=
  ⟨pc, oB fr, fun σ c => NJ p lbl (rsOf fr) t s (upd σ.slot k (σ.regs.get64 .rax)) c ∧ FrJ fp ra σ.slot ∧
    LocalRun p c0 c⟩

/-- **The source at the overflow abort label** (the handover to the abort
path): `AbSrc` in some symbolic environment whose immediates are the table
`i`'s at the source's term (`ImmIn`), the term satisfying `T` (in practice:
a point of the body's walk, `InWalk`), operands in the frame's cells, and
the saved pair. -/
def AbJ (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (lbl : WeakMem.AllocLabel → Option Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  (∃ s, AbSrc lbl (rsOf fr) s σ.slot c ∧ ImmIn i s c.term ∧ T c.term) ∧ FrJ fp ra σ.slot

/-- **The overflow abort label**, the source at the `+` that carries. -/
def abortN (i : Expr → String → Nat → Option Nat) (T : Expr → Prop) (p : Prog)
    (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame) (lab : String → Int64) (fp ra : BitVec 64)
    (c0 : Ctl) : ND :=
  ⟨lab (ovfL fr), oB fr, fun σ c => AbJ i T lbl fr fp ra σ c ∧ LocalRun p c0 c⟩

/-- A slot's bounds: a negative multiple of 8 inside the frame. -/
theorem rsOf_bounds {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {r : Scc.IR.Reg} {k : Int}
    (h : rsOf fr r = some k) : k ≤ -8 ∧ k % 8 = 0 ∧ -k ≤ (fr.size : Int) := by
  obtain ⟨areas, f, hsl, hsz⟩ := hf
  unfold rsOf at h
  cases h1 : fr.slotOff r {} with
  | error _ => simp [h1] at h
  | ok q =>
    obtain ⟨o, s'⟩ := q
    simp only [h1, Option.some.injEq] at h
    subst h
    obtain ⟨h8, hm, hle, hsize⟩ := slotOff_bounds hsl hsz h1
    refine ⟨h8, hm, by omega⟩

/-- Different IR registers have different cells. -/
theorem rsOf_inj {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) {r d : Scc.IR.Reg} {k : Int}
    (hr : rsOf fr r = some k) (hd : rsOf fr d = some k) : r = d := by
  obtain ⟨areas, f, hsl, -⟩ := hf
  unfold rsOf at hr hd
  cases h1 : fr.slotOff r {} with
  | error _ => simp [h1] at hr
  | ok q1 =>
    cases h2 : fr.slotOff d {} with
    | error _ => simp [h2] at hd
    | ok q2 =>
      obtain ⟨o1, s1⟩ := q1
      obtain ⟨o2, s2⟩ := q2
      simp only [h1, h2, Option.some.injEq] at hr hd
      subst hr hd
      exact slotOff_inj hsl h1 h2

theorem so_le_oB (fr : Scc.Emit.X64.Frame) : SO.le (oB fr) (oB fr) = true := by
  simp [SO.le, oB, lk]

/-- **The return's exit**: at the saved return address, the frame popped;
the source at `ret a` with `a`'s one word a number represented by `%rax`,
`%rbp` restored to the ghost `fp`. -/
def RetJ (lbl : WeakMem.AllocLabel → Option Nat) (fp : BitVec 64) (σ : AS) (c : Ctl) : Prop :=
  ∃ a t w, c.term = .ret a ∧ c.hold = none ∧ TermRun.evalAt c.env a = some (t, [w]) ∧ (∃ n, w.val = .num n) ∧
    ValRep lbl w.val (σ.regs.get64 .rax).toNat ∧ σ.regs.get64 .rbp = fp

/-- **The return's exit node**: `%rsp` past the popped return address. -/
def retN (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (fp ra : BitVec 64) (c0 : Ctl) : ND :=
  ⟨Int64.ofBitVec ra, ⟨16, []⟩, fun σ c => RetJ lbl fp σ c ∧ LocalRun p c0 c⟩

theorem dirs_epiItems : dirs epiItems = epi := rfl

/-- **A block's edge** from node `n` (the obligation of `seg_ndW` on its
closed form): the block is not empty and covered from the node's offsets
for cells in `[lo, hi)`, and from every state of the node's invariant its
abstract run (labels `lab`) lands at an internal node of `N` or an exit of
`E`, after a local run of the source. -/
def BlkEdge (p : Prog) (lab : String → Int64) (lo hi : Int) (n : ND) (blk : List (Directive × Nat))
    {ι κ : Sort _} (N : ι → ND) (E : κ → ND) : Prop :=
  blk ≠ [] ∧ okBlk lo hi n.o blk = true ∧
    ∀ σ c, n.J σ c → ∃ c', LocalRun p c c' ∧ Lands N E (arun lab blk ⟨n.pc, n.o, σ⟩) c'

/-- **A block's edge is one segment** (`seg_ndW`). -/
theorem BlkEdge.seg {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : Frag isa} {K : State → State → Prop}
    {lo hi : Int} {n : ND} {blk : List (Directive × Nat)} {ι κ : Sort _} {N : ι → ND} {E : κ → ND}
    (h : BlkEdge p (_root_.Executable.labels exe).label lo hi n blk N E)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hW : BlkW W K exe endPc R F n blk) :
    SegW W K p lbl ms (At exe endPc R F n) (Next exe endPc R F N E) :=
  seg_ndW h.1 h.2.1 hF hR hlo hhi hcode hW h.2.2

section Segs

variable {lbl : WeakMem.AllocLabel → Option Nat} {c0 : Ctl} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
  {W : Frag isa} {K : State → State → Prop}

/-- An `At` exit from a one-exit `Next`. -/
theorem SegW.of_next1 {P : Frag isa} {n : ND}
    (h : SegW W K p lbl ms P (Next exe endPc R F (fun _ : Unit => n) (fun e : Empty => e.elim))) :
    SegW W K p lbl ms P (At exe endPc R F n) :=
  h.mono_post fun _ _ h => h.elim (fun ⟨_, h⟩ => h) fun ⟨e, _⟩ => e.elim

/-- **The checked `+`'s edge** (`add_seg`'s block, at the labels `lab`). -/
theorem add_edge {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ addChecked (ovfL fr))).length) (lab : String → Int64)
    {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i s (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e)) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN p lbl fr fp ra c0 pc (.let_ x (.add a b) e) s)
      ((dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs)
      (fun _ : Unit => pendN p lbl fr fp ra c0 (pc + Int64.ofNat zs.sum)
        e ((x, .int, [.one (.reg d)]) :: s) off)
      (fun _ : Unit => abortN i T p lbl fr lab fp ra c0) := by
  have hne : (dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs ≠ [] := by
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    rw [dirs_append, dirs_append, hda, hdb, dirs_addChecked] at hz ⊢
    match zs, hz with
    | [_, _, _, _], _ => simp
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs) = true := by
    obtain ⟨da, hda⟩ := dirs_getOp ha
    obtain ⟨db, hdb⟩ := dirs_getOp hb
    have hz' := hz
    rw [dirs_append, dirs_append, hda, hdb, dirs_addChecked] at hz'
    match zs, hz' with
    | [z0, z1, z2, z3], _ =>
    have hsplit : (dirs (la ++ lb ++ addChecked (ovfL fr))).zip [z0, z1, z2, z3] =
        (dirs la).zip [z0] ++ ((dirs lb).zip [z1] ++ (dirs (addChecked (ovfL fr))).zip [z2, z3]) := by
      rw [dirs_append, dirs_append, hda, hdb, dirs_addChecked]; rfl
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hda]),
      okBlk_getOp hf h1 (by decide) (by decide) hb (by simp [hdb])]
    exact okBlk_addChecked (by simp [oB, SO.kill, rm]) _
  refine ⟨hne, hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  show ∃ c', LocalRun p c c' ∧ Lands _ _ (arun _ _ ⟨pc, oB fr, σ⟩) c'
  obtain ⟨-, va, vb, hva, hvb, hpc, hso, h9, hsl⟩ :=
    add_block hf h1 ha hb (ovfL fr) lab pc σ hz
  by_cases hlt : va.toNat + vb.toNat < 2 ^ 64
  · refine ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0⟩⟩
    · show pc + _ = _
      rw [hpc]; simp [hlt]
    · show SO.le (oB fr) _ = true
      rw [hso]; exact so_le_oB fr
    · show NJ p lbl (rsOf fr) e _ (upd _ off _) c
      rw [hsl, h9]
      refine hJ.add_ok hsa hsb hva hvb hlt hd ?_ ?_
      · intro q hq pl hpl o ho r k' hor hr' hk
        subst hk
        exact hfr q hq pl hpl o ho r hor (rsOf_inj hf hr' hd)
      · rw [BitVec.toNat_add]; exact Nat.mod_eq_of_lt hlt
    · show FrJ fp ra _
      rw [hsl]; exact hfj
  · obtain ⟨c1, hr, hab, ht⟩ := hJ.add_ovf_term hsa hsb hva hvb (by omega) htot
    refine ⟨c1, hr, .inr ⟨(), ?_, ?_, ?_, hc0.trans hr⟩⟩
    · show _ = _
      rw [hpc]; simp [hlt]; rfl
    · show SO.le (oB fr) _ = true
      rw [hso]; exact so_le_oB fr
    · show AbJ i T lbl fr fp ra _ c1
      rw [AbJ, hsl]; exact ⟨⟨s, hab, ht ▸ himm, ht ▸ hT⟩, hfj⟩

/-- **The checked `+`'s block is one segment**: from the node at
`let x = a + b` (operands placed at `pa`, `pb`, loaded into `%rax`, `%rcx`)
to the pending store after the block, or, on carry, to the overflow abort
label. `x`'s IR register `d` has a cell no other placed operand has. -/
theorem add_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa pb : Scc.IR.Operand} {la lb : List Item} (ha : getOp fr .rax pa = .ok la) (hb : getOp fr .rcx pb = .ok lb)
    {d : Scc.IR.Reg} {off : Int} (hd : rsOf fr d = some off) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (la ++ lb ++ addChecked (ovfL fr))).length)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc →
      CodeAt s pc ((dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs))
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {x : String} {a b : At} {e : Expr} {s : SEnv} {ta tb : Ty}
    (hsa : sevalAt s a = some (ta, [.one pa])) (hsb : sevalAt s b = some (tb, [.one pb]))
    (hfr : ∀ q ∈ s, ∀ pl ∈ q.2.2, ∀ o ∈ pl.opds, ∀ r, o = .reg r → r ≠ d)
    (htot : ∀ y ∈ Scc.Sem.exprFv (.let_ x (.add a b) e), (lookupS s y).isSome)
    {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} (himm : ImmIn i s (.let_ x (.add a b) e))
    (hT : T (.let_ x (.add a b) e))
    (hW : BlkW W K exe endPc R F (bodyN p lbl fr fp ra c0 pc (.let_ x (.add a b) e) s)
      ((dirs (la ++ lb ++ addChecked (ovfL fr))).zip zs)) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl fr fp ra c0 pc (.let_ x (.add a b) e) s))
      (Next exe endPc R F
        (fun _ : Unit => pendN p lbl fr fp ra c0 (pc + Int64.ofNat zs.sum)
          e ((x, .int, [.one (.reg d)]) :: s) off)
        (fun _ : Unit => abortN i T p lbl fr (_root_.Executable.labels exe).label fp ra c0)) :=
  (add_edge hf h1 ha hb hd hz _ hsa hsb hfr htot himm hT).seg hF hR hlo hhi hcode hW

/-- **The store's edge** (`store_seg`'s block, at the labels `lab`). -/
theorem store_edge {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Scc.IR.Reg} {off : Int}
    (hd : rsOf fr d = some off) {pc : Int64} {z : Nat} (lab : String → Int64) {fp ra : BitVec 64} {t : Expr}
    {s : SEnv} :
    BlkEdge p lab (-(fr.size : Int)) 16 (pendN p lbl fr fp ra c0 pc t s off) [(stDir off, z)]
      (fun _ : Unit => bodyN p lbl fr fp ra c0 (pc + Int64.ofNat z) t s) (fun e : Empty => e.elim) := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hd
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) [(stDir off, z)] = true := by
    simp only [okBlk, hc, AI.ok, AI.isTerm, AI.so, oB, SO.get, lk, ho, offOk]
    simp
    omega
  have hrun : ∀ σ : AS, arun lab [(stDir off, z)] ⟨pc, oB fr, σ⟩ =
      ⟨pc + Int64.ofNat z, oB fr, { σ with slot := upd σ.slot off (σ.regs.get64 .rax) }⟩ := by
    intro σ
    simp [arun, dstep, hc, AI.tgt, AI.so, AI.step, oB, SO.get, lk, ho]
  refine ⟨by simp, hok, fun σ c ⟨hJ, hfj, hc0⟩ =>
    ⟨c, .refl c, .inl ⟨(), ?_, ?_, ?_, ?_, hc0⟩⟩⟩
  all_goals simp only [pendN, hrun]
  · rfl
  · exact so_le_oB fr
  · exact hJ
  · obtain ⟨h0', h8'⟩ := hfj
    have hk1 : (0 : Int) ≠ off := by omega
    have hk2 : (8 : Int) ≠ off := by omega
    show upd σ.slot _ _ 0 = fp ∧ upd σ.slot _ _ 8 = ra
    simp only [upd_apply, Ne.symm hk1, Ne.symm hk2, hk1, hk2, ↓reduceIte, h0', h8', and_self]

/-- **The store `movq %rax, off(%rbp)` of a checked `+`'s result is one
segment**: from the pending store to the next node. -/
theorem store_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d : Scc.IR.Reg} {off : Int}
    (hd : rsOf fr d = some off) {pc : Int64} {z : Nat}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc [(stDir off, z)])
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {t : Expr} {s : SEnv}
    (hW : BlkW W K exe endPc R F (pendN p lbl fr fp ra c0 pc t s off) [(stDir off, z)]) :
    SegW W K p lbl ms (At exe endPc R F (pendN p lbl fr fp ra c0 pc t s off))
      (At exe endPc R F (bodyN p lbl fr fp ra c0 (pc + Int64.ofNat z) t s)) :=
  SegW.of_next1 ((store_edge hf h1 hd _).seg hF hR hlo hhi hcode hW)

/-- **`ret a`'s edge** (`ret_seg`'s block, at the labels `lab`). -/
theorem ret_edge {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa : Scc.IR.Operand} {l : List Item} (ha : getOp fr .rax pa = .ok l) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (l ++ epiItems)).length) (lab : String → Int64)
    {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty}
    (hsa : sevalAt s a = some (t, [.one pa])) :
    BlkEdge p lab (-(fr.size : Int)) 16 (bodyN p lbl fr fp ra c0 pc (.ret a) s) ((dirs (l ++ epiItems)).zip zs)
      (fun _ : Unit => retN p lbl fp ra c0) (fun e : Empty => e.elim) := by
  obtain ⟨dl, hdl⟩ := dirs_getOp ha
  have hds : dirs (l ++ epiItems) = dirs l ++ epi := by rw [dirs_append, dirs_epiItems]
  rw [hds, hdl] at hz
  match zs, hz with
  | [z0, z1, z2, z3], _ =>
  have hsplit : (dirs (l ++ epiItems)).zip [z0, z1, z2, z3] = (dirs l).zip [z0] ++ epi.zip [z1, z2, z3] := by
    rw [hds, hdl]; rfl
  have hok : okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs (l ++ epiItems)).zip [z0, z1, z2, z3]) = true := by
    rw [hsplit, okBlk_getOp hf h1 (by decide) (by decide) ha (by simp [hdl])]
    exact okBlk_epi (by omega) z1 z2 z3
  refine ⟨by rw [hsplit]; simp [epi], hok, fun σ c ⟨hJ, hfj, hc0⟩ => ?_⟩
  obtain ⟨c1, hr, hj, hnum⟩ := hJ
  obtain ⟨ws, he, hw⟩ := hj.2.2.evalAt (Spike.Lib.Form.opdVal_imm _ _) hsa
  have hwn := hnum.evalAt hsa he
  obtain ⟨v, hv, hrun⟩ := arun_getOp hf h1 (by decide) ha lab pc σ
    (zs := [z0]) (by simp [hdl])
  match ws, hw with
  | [w], ⟨⟨v', hv', hrep⟩, _⟩ =>
  rw [hv] at hv'
  cases hv'
  refine ⟨c1, hr, .inl ⟨(), ?_⟩⟩
  show Hit (retN p lbl fp ra c0)
    (arun _ ((dirs (l ++ epiItems)).zip [z0, z1, z2, z3]) ⟨pc, oB fr, σ⟩) c1
  rw [hsplit, arun_append, hrun]
  obtain ⟨hpc, hso, hsl, -, hbp, -, hr0⟩ := arun_epi lab
    (pc + Int64.ofNat [z0].sum) (-(fr.size : Int)) { σ with regs := σ.regs.set64 .rax v } z1 z2 z3
  obtain ⟨hfp, hra⟩ := hfj
  obtain ⟨n, hn, -⟩ := hwn w (List.mem_singleton_self w)
  refine ⟨?_, ?_, ⟨a, t, w, hj.1, hj.2.1, he, ⟨n, hn⟩, ?_, ?_⟩, hc0.trans hr⟩
  · show _ = (arun _ _ ⟨_, oR _, _⟩).pc
    rw [hpc]; simp [retN, hra]
  · show SO.le ⟨16, []⟩ (arun _ _ ⟨_, oR _, _⟩).so = true
    rw [hso]; rfl
  · show ValRep lbl w.val ((arun _ _ ⟨_, oR _, _⟩).σ.regs.get64 .rax).toNat
    rw [hr0 .rax (by decide) (by decide), Reg64s.get64_set64_self]
    simpa using hrep
  · show (arun _ _ ⟨_, oR _, _⟩).σ.regs.get64 .rbp = fp
    rw [hbp]; exact hfp

/-- **`ret a` is one segment**: from the node at `ret a` (`a` placed at
`pa`) through the load of `pa` into `%rax`, the epilogue and `ret` to the
saved return address. -/
theorem ret_seg {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    {pa : Scc.IR.Operand} {l : List Item} (ha : getOp fr .rax pa = .ok l) {pc : Int64} {zs : List Nat}
    (hz : zs.length = (dirs (l ++ epiItems)).length)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s pc ((dirs (l ++ epiItems)).zip zs))
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int))
    (hhi : 16 ≤ R.hi) {fp ra : BitVec 64} {a : At} {s : SEnv} {t : Ty}
    (hsa : sevalAt s a = some (t, [.one pa]))
    (hW : BlkW W K exe endPc R F (bodyN p lbl fr fp ra c0 pc (.ret a) s) ((dirs (l ++ epiItems)).zip zs)) :
    SegW W K p lbl ms (At exe endPc R F (bodyN p lbl fr fp ra c0 pc (.ret a) s))
      (At exe endPc R F (retN p lbl fp ra c0)) :=
  SegW.of_next1 ((ret_edge hf h1 ha hz _ hsa).seg hF hR hlo hhi hcode hW)

end Segs

end Spike.Lib.LowerX64
