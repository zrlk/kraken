/-
**A lane store's segment** (x86-64): `LaneC` (`Body2.lean`) from
`xchg_segW` (`Spike/Lib/X64XchgSeg.lean`) and `NJB.xchg2`.

`let x = xchgAt b k v` lowers to `xchgLoad d a; xchgStore a w` with `a`
the element's slot address (`slotAddr`, base `b`'s register `rb`,
displacement `8 * k`), which emit
`ld rb → %rcx; movq disp(%rcx), %rax; st %rax → d` and
`ld rb → %rcx; ld w → %rax; movq %rax, disp(%rcx)`. So `xchg_segW`'s
blocks are `B1 = [ld rb → %rcx]`, the load, `B2 = [st %rax → d; ld rb →
%rcx; ld w → %rax]` (across the two instructions' code), the store.

- `emits_xchgLoad`, `emits_xchgStore`: the instructions' directives;
- `insts_xchg`, `xchg_code`, `cdOf_append`: the two instructions' code as
  the four blocks;
- `xchg_b1`, `xchg_b2`: `B1`'s and `B2`'s coverage and runs;
- `LaneW`: the memory side's facts at an exchange (states in `W₀` at one
  lane's nodes, the access's address unmapped in their private memory);
- `laneJ`, `laneP`: the lane's node and source relation at the exchange;
- `LaneH`: the site's facts `laneC_of` gives `LaneW`'s discharge;
- `lane_segW`: the segment, the source side's facts at the exchange site
  premises;
- `laneC_of`: `LaneC` from them, the source side by `xchg_site`,
  `xchg_val` (`Spike/Lib/Src/XchgSiteB.lean`) and `NJB.xchg2`.
-/
import Spike.Lib.LowerX64.Body2Seg
import Spike.Lib.X64XchgSeg
import Spike.Lib.Src.NJBXchg2
import Spike.Lib.Src.XchgB
import Spike.Lib.Src.GroupPl
import Spike.Lib.Src.XchgSiteB
import Spike.Lib.Src.LblRange

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64
open Scc.Emit.X64 (S E Item emitInst ins ld st i64 xr xm om or_ mem labelOf)
open Spike.Lib.Form (opdVal NodeJ NodeJE SEnv sevalAt lookupS WordPl WordsRep WordRep SRep grp group)
open Scc.Sem (ValRep)
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (slotAddr xchgLoad xchgStore refO)
open Scc.Lower.Inv (atomV regName)

/-! ## The instructions' directives -/

theorem emitInst_xchgLoad (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (d : Scc.IR.Reg)
    (a : Scc.IR.Addr) :
    emitInst fr sm (xchgLoad d a) = (do
      ld fr (.reg a.base) .rcx
      ins (i64 (.mov (xr .rax) (om (mem .rcx a.disp))))
      st fr .rax d) := rfl

theorem emitInst_xchgStore (fr : Scc.Emit.X64.Frame) (sm : Option Scc.IR.StackMap.Entry) (a : Scc.IR.Addr)
    (w : Scc.IR.Operand) :
    emitInst fr sm (xchgStore a w) = (do
      ld fr (.reg a.base) .rcx
      ld fr w .rax
      ins (i64 (.mov (xm (mem .rcx a.disp)) (or_ .rax)))) := rfl

/-- **The directives of a lane store's load**: the base's load into `%rcx`,
the element's load into `%rax`, `%rax`'s store into `d`'s slot. -/
theorem emits_xchgLoad {fr : Scc.Emit.X64.Frame} {sm} {d : Scc.IR.Reg} {a : Scc.IR.Addr} {l : List Item}
    (h : Emits (emitInst fr sm (xchgLoad d a)) l) :
    ∃ lb off, getOp fr .rcx (.reg a.base) = .ok lb ∧ rsOf fr d = some off ∧
      dirs l = dirs lb ++ [X64.ldDir .rcx (Int64.ofInt a.disp) .rax, stDir off] := by
  have h0 := h {}
  rw [emitInst_xchgLoad] at h0
  rcases ld_cases fr (.reg a.base) .rcx {} with ⟨lb, hb, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1, bind_ok (ins_eq _ _)] at h0
    rcases st_cases fr d _ with ⟨off, hd, e3⟩ | ⟨e, e3⟩
    · refine ⟨lb, off, hb, hd, ?_⟩
      have hl := emits_out (l' := lb ++ [.d (X64.ldDir .rcx (Int64.ofInt a.disp) .rax), .d (stDir off)]) h
        (by rw [emitInst_xchgLoad, bind_ok e1, bind_ok (ins_eq _ _), e3]; simp [List.reverse_append]; rfl)
      rw [hl, dirs_append]; rfl
    · rw [e3] at h0; cases h0
  · rw [bind_err e1] at h0; cases h0

/-- **The directives of a lane store's store**: the base's load into
`%rcx`, the stored word's into `%rax`, `%rax`'s store into the element. -/
theorem emits_xchgStore {fr : Scc.Emit.X64.Frame} {sm} {a : Scc.IR.Addr} {w : Scc.IR.Operand} {l : List Item}
    (h : Emits (emitInst fr sm (xchgStore a w)) l) :
    ∃ lb lw, getOp fr .rcx (.reg a.base) = .ok lb ∧ getOp fr .rax w = .ok lw ∧
      dirs l = dirs lb ++ dirs lw ++ [X64.stDir .rcx (Int64.ofInt a.disp) .rax] := by
  have h0 := h {}
  rw [emitInst_xchgStore] at h0
  rcases ld_cases fr (.reg a.base) .rcx {} with ⟨lb, hb, e1⟩ | ⟨e, e1⟩
  · rw [bind_ok e1] at h0
    rcases ld_cases fr w .rax _ with ⟨lw, hw, e2⟩ | ⟨e, e2⟩
    · refine ⟨lb, lw, hb, hw, ?_⟩
      have hl := emits_out (l' := lb ++ lw ++ [.d (X64.stDir .rcx (Int64.ofInt a.disp) .rax)]) h
        (by rw [emitInst_xchgStore, bind_ok e1, bind_ok e2, ins_eq]; simp [List.reverse_append]; rfl)
      rw [hl, dirs_append, dirs_append]; rfl
    · rw [bind_err e2] at h0; cases h0
  · rw [bind_err e1] at h0; cases h0

/-! ## The code -/

theorem slotAddr_base (o : Scc.ObjLayout) (b : Scc.IR.Reg) (w : UInt64) (s : Bool × Nat) :
    (slotAddr o b w s).base = b := by
  obtain ⟨tr, i⟩ := s
  cases tr <;> rfl

/-- **Two code segments in a row are one.** -/
theorem cdOf_append {exe : _root_.Executable} {endPc pc : Int64} {A B : List (Directive × Nat)}
    (hA : CdOf exe endPc pc A) (hB : CdOf exe endPc (pc + Int64.ofNat (A.map (·.2)).sum) B) :
    CdOf exe endPc pc (A ++ B) := by
  intro s he hn j d z hj
  rcases Nat.lt_or_ge j A.length with h' | h'
  · rw [List.getElem?_append_left h'] at hj
    have hoff : cellOff (A ++ B) j = cellOff A j := by
      unfold cellOff; rw [List.take_append_of_le_length (by omega)]
    rw [hoff]; exact hA s he hn j d z hj
  · obtain ⟨j', rfl⟩ := Nat.exists_eq_add_of_le h'
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hj
    have hoff : cellOff (A ++ B) (A.length + j') = (A.map (·.2)).sum + cellOff B j' := by
      unfold cellOff
      rw [List.take_append, List.take_of_length_le (by omega), Nat.add_sub_cancel_left, List.map_append,
        List.sum_append]
    have hc := hB s he hn j' d z hj
    rwa [hoff, Int64.ofNat_add, ← Int64.add_assoc]

/-- **A lane store's two instructions' code**: no calls, each its emitted
directives at its pc. -/
theorem insts_xchg {fr : Scc.Emit.X64.Frame} {Cd : Int64 → List (Directive × Nat) → Prop}
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk kk' : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr}
    {w : Scc.IR.Operand} (h : InstsC2 fr Cd Bl kk pc [xchgLoad d a, xchgStore a w] kk' pc') :
    ∃ l1 zs1 l2 zs2, Emits (emitInst fr none (xchgLoad d a)) l1 ∧ zs1.length = (dirs l1).length ∧
      Cd pc ((dirs l1).zip zs1) ∧ Emits (emitInst fr none (xchgStore a w)) l2 ∧
      zs2.length = (dirs l2).length ∧ Cd (pc + Int64.ofNat zs1.sum) ((dirs l2).zip zs2) ∧
      kk' = kk ∧ pc' = pc + Int64.ofNat zs1.sum + Int64.ofNat zs2.sum := by
  rcases h with ⟨-, l1, zs1, hE1, hz1, hc1, h⟩ | ⟨_, _, _, _, _, _, _, _, hi, _⟩ |
    ⟨_, _, _, _, _, _, _, hi, _⟩ | ⟨_, _, _, _, hi, _⟩
  · rcases h with ⟨-, l2, zs2, hE2, hz2, hc2, ⟨rfl, rfl⟩⟩ | ⟨_, _, _, _, _, _, _, _, hi, _⟩ |
      ⟨_, _, _, _, _, _, _, hi, _⟩ | ⟨_, _, _, _, hi, _⟩
    · exact ⟨l1, zs1, l2, zs2, hE1, hz1, hc1, hE2, hz2, hc2, rfl, rfl⟩
    all_goals cases hi
  all_goals cases hi

/-- **A lane store's code as `xchg_segW`'s blocks**: `B1` (the base's load
into `%rcx`) at `pc`, the load, `B2` (the result's store into `d`'s slot,
the base's and the stored word's loads) and the store, back to back, to
`pc'`. -/
theorem xchg_code {exe : _root_.Executable} {endPc : Int64} {fr : Scc.Emit.X64.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk kk' : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr}
    {w : Scc.IR.Operand} (h : InstsC2 fr Cd Bl kk pc [xchgLoad d a, xchgStore a w] kk' pc') :
    ∃ lb lw off z0 zL zt z1 z2 zS, getOp fr .rcx (.reg a.base) = .ok lb ∧ getOp fr .rax w = .ok lw ∧
      rsOf fr d = some off ∧
      CdOf exe endPc pc ((dirs lb).zip [z0]) ∧
      CdOf exe endPc (pc + Int64.ofNat z0) [(X64.ldDir .rcx (Int64.ofInt a.disp) .rax, zL)] ∧
      CdOf exe endPc (pc + Int64.ofNat z0 + Int64.ofNat zL)
        ((stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2])) ∧
      CdOf exe endPc (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2))
        [(X64.stDir .rcx (Int64.ofInt a.disp) .rax, zS)] ∧
      kk' = kk ∧ pc' = pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2) + Int64.ofNat zS ∧
      Cd pc ((dirs lb ++ [X64.ldDir .rcx (Int64.ofInt a.disp) .rax, stDir off]).zip [z0, zL, zt]) ∧
      Cd (pc + Int64.ofNat (z0 + zL + zt))
        ((dirs lb ++ dirs lw ++ [X64.stDir .rcx (Int64.ofInt a.disp) .rax]).zip [z1, z2, zS]) := by
  obtain ⟨l1, zs1, l2, zs2, hE1, hz1, hc1, hE2, hz2, hc2, rfl, rfl⟩ := insts_xchg h
  obtain ⟨lb, off, hb, hoff, hd1⟩ := emits_xchgLoad hE1
  obtain ⟨lb', lw, hb', hw, hd2⟩ := emits_xchgStore hE2
  rw [hb] at hb'; cases hb'
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  obtain ⟨dw, hdw⟩ := dirs_getOp hw
  rw [hd1, hdb] at hz1 hc1
  rw [hd2, hdb, hdw] at hz2 hc2
  match zs1, zs2, hz1, hz2 with
  | [z0, zL, zt], [z1, z2, zS], _, _ =>
    have c1 := hCd _ _ hc1
    have c2 := hCd _ _ hc2
    simp only [List.cons_append, List.nil_append, List.zip_cons_cons, List.zip_nil_right] at c1 c2
    refine ⟨lb, lw, off, z0, zL, zt, z1, z2, zS, hb, hw, hoff, ?_, ?_, ?_, ?_, rfl, ?_, by rw [hdb]; exact hc1,
      by rw [hdb, hdw]; simpa only [List.sum_cons, List.sum_nil, Nat.add_zero, Nat.add_assoc] using hc2⟩
    · have e := cdOf_sub (pre := []) (blk := [(db, z0)]) (post := [_, _]) c1
      simp only [List.map_nil, List.sum_nil] at e
      rw [hdb]; simpa [Int64.add_zero] using e
    · have e := cdOf_sub (pre := [(db, z0)]) (blk := [_]) (post := [_]) c1
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at e
      exact e
    · rw [hdb, hdw]
      have e1 := cdOf_sub (pre := [(db, z0), (_, zL)]) (blk := [_]) (post := []) c1
      have e2 := cdOf_sub (pre := []) (blk := [(db, z1), (dw, z2)]) (post := [_]) c2
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero] at e1 e2
      have e := cdOf_append e1 (B := [(db, z1), (dw, z2)]) (by
        simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
          Int64.add_assoc] at e2 ⊢
        simpa [Int64.add_zero, Int64.add_assoc] using e2)
      simp only [Int64.ofNat_add, Int64.add_assoc, List.zip_cons_cons, List.zip_nil_right] at e ⊢
      exact e
    · have e := cdOf_sub (pre := [(db, z1), (dw, z2)]) (blk := [_]) (post := []) c2
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add,
        Int64.add_assoc] at e ⊢
      exact e
    · simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]

/-! ## The blocks' runs -/

/-- **`B1`**: covered, it loads the base's value `vb` into `%rcx`. -/
theorem xchg_b1 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {rb : Scc.IR.Reg}
    {lb : List Item} (hb : getOp fr .rcx (.reg rb) = .ok lb) (lab : String → Int64) (pc : Int64)
    {z0 : Nat} (hz : [z0].length = (dirs lb).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((dirs lb).zip [z0]) = true ∧
      ∀ σ : AS, ∃ vb : BitVec 64, opdVal (rsOf fr) σ.slot (.reg rb) = some vb.toNat ∧
        arun lab ((dirs lb).zip [z0]) ⟨pc, oB fr, σ⟩ =
          ⟨pc + Int64.ofNat z0, oB fr, { σ with regs := σ.regs.set64 .rcx vb }⟩ := by
  refine ⟨?_, ?_⟩
  · have := okBlk_getOp hf h1 (by decide) (by decide) hb hz []
    rw [List.append_nil] at this
    rw [this]; rfl
  · intro σ
    obtain ⟨vb, hv, e⟩ := arun_getOp hf h1 (by decide) hb lab pc σ hz
    exact ⟨vb, hv, by rw [e]; simp⟩

/-- **`B2`**: covered, it stores `%rax` into `d`'s slot `off`, then loads
the base's value `vb` into `%rcx` and the stored word's `vw` into `%rax`
(read in the updated slots). -/
theorem xchg_b2 {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) {d rb : Scc.IR.Reg}
    {off : Int} (hoff : rsOf fr d = some off) {w : Scc.IR.Operand} {lb lw : List Item}
    (hb : getOp fr .rcx (.reg rb) = .ok lb) (hw : getOp fr .rax w = .ok lw) (lab : String → Int64) (pc : Int64)
    {zt z1 z2 : Nat} (hz1 : [z1].length = (dirs lb).length) (hz2 : [z2].length = (dirs lw).length) :
    okBlk (-(fr.size : Int)) 16 (oB fr) ((stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2])) = true ∧
      ∀ σ : AS, ∃ vb vw : BitVec 64, opdVal (rsOf fr) (upd σ.slot off (σ.regs.get64 .rax)) (.reg rb) = some vb.toNat ∧
        opdVal (rsOf fr) (upd σ.slot off (σ.regs.get64 .rax)) w = some vw.toNat ∧
        arun lab ((stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2])) ⟨pc, oB fr, σ⟩ =
          ⟨pc + Int64.ofNat (zt + z1 + z2), oB fr,
            { σ with slot := upd σ.slot off (σ.regs.get64 .rax), regs := (σ.regs.set64 .rcx vb).set64 .rax vw }⟩ := by
  obtain ⟨h8, hm, hle⟩ := rsOf_bounds hf hoff
  have ho : (Int64.ofInt off).toInt = off := toInt_ofInt_small (by omega) (by omega)
  have hc : classify (stDir off) = some (AI.st .rbp (Int64.ofInt off) .rax) := rfl
  refine ⟨?_, ?_⟩
  · have e1 := okBlk_getOp hf h1 (by decide) (by decide) hw hz2 []
    have e2 := okBlk_getOp hf h1 (by decide) (by decide) hb hz1 ((dirs lw).zip [z2])
    rw [List.append_nil] at e1
    have hst : ∀ ds, okBlk (-(fr.size : Int)) 16 (oB fr) ((stDir off, zt) :: ds) =
        okBlk (-(fr.size : Int)) 16 (oB fr) ds := by
      intro ds
      cases ds with
      | nil => simp only [okBlk, hc, AI.ok, AI.isTerm, oB, SO.get, lk, ho, offOk]; simp; omega
      | cons _ _ => simp only [okBlk, hc, AI.ok, AI.isTerm, AI.so, oB, SO.get, lk, ho, offOk]; simp; omega
    rw [hst, e2, e1]; rfl
  · intro σ
    have hrun : arun lab [(stDir off, zt)] ⟨pc, oB fr, σ⟩ =
        ⟨pc + Int64.ofNat zt, oB fr, { σ with slot := upd σ.slot off (σ.regs.get64 .rax) }⟩ := by
      simp [arun, dstep, hc, AI.tgt, AI.so, AI.step, oB, SO.get, lk, ho]
    obtain ⟨vb, hvb, eb⟩ := arun_getOp hf h1 (by decide) hb lab (pc + Int64.ofNat zt)
      { σ with slot := upd σ.slot off (σ.regs.get64 .rax) } hz1
    obtain ⟨vw, hvw, ew⟩ := arun_getOp hf h1 (by decide) hw lab (pc + Int64.ofNat zt + Int64.ofNat [z1].sum)
      { σ with slot := upd σ.slot off (σ.regs.get64 .rax), regs := σ.regs.set64 .rcx vb } hz2
    refine ⟨vb, vw, hvb, hvw, ?_⟩
    rw [show (stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2]) =
      [(stDir off, zt)] ++ (dirs lb).zip [z1] ++ (dirs lw).zip [z2] from rfl, arun_append, arun_append, hrun, eb]
    simp only at ew
    rw [ew]
    simp only [List.sum_cons, List.sum_nil, Nat.add_zero, Int64.ofNat_add, Int64.add_assoc]

/-! ## The memory side at an exchange -/

/-- **The memory side's states at a lane store's nodes in `W₀`**: for the
lane's code at `pc` (`xchg_code`'s data: the base's and the stored word's
loads `lb`, `lw`, `d`'s slot `off`, the two instructions' chunks of the code
predicate `Cd` with their cells' sizes), the states
along `B1` from `⟨pc, oB fr, J⟩`, at the load's node, along `B2` and at the
store's node (`xchg_segW`'s nodes from the lane's `J` and `P`) lie in `W₀`,
not moved by `K`. (The access's address unmapped in private memory is
`lane_segW`'s `hsite`.) -/
def LaneW (Cd : Int64 → List (Directive × Nat) → Prop) (W₀ : Frag isa) (K : State → State → Prop)
    (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (ms : MemSide isa) (lbl : WeakMem.AllocLabel → Option Nat) (fr : Scc.Emit.X64.Frame)
    (pc : Int64) (d : Scc.IR.Reg) (a : Scc.IR.Addr) (w : Scc.IR.Operand) (J : AS → Ctl → Prop)
    (P : AS → Ctl → Ctl → Prop) : Prop :=
  ∀ (lb lw : List Item) (off : Int) (z0 zL zt z1 z2 zS : Nat), getOp fr .rcx (.reg a.base) = .ok lb →
    getOp fr .rax w = .ok lw → rsOf fr d = some off →
    Cd pc ((dirs lb ++ [X64.ldDir .rcx (Int64.ofInt a.disp) .rax, stDir off]).zip [z0, zL, zt]) →
    Cd (pc + Int64.ofNat (z0 + zL + zt))
      ((dirs lb ++ dirs lw ++ [X64.stDir .rcx (Int64.ofInt a.disp) .rax]).zip [z1, z2, zS]) →
    BlkW W₀ K exe endPc R F ⟨pc, oB fr, J⟩ ((dirs lb).zip [z0]) ∧
    NodeW W₀ K exe endPc R F (Flow.XchgSeg.xsNL (_root_.Executable.labels exe).label ((dirs lb).zip [z0]) pc
      (pc + Int64.ofNat z0) (oB fr) (oB fr) J P) ∧
    BlkW W₀ K exe endPc R F (Flow.XchgSeg.xsNH ms lbl (_root_.Executable.labels exe).label ((dirs lb).zip [z0]) pc
      (pc + Int64.ofNat z0) zL (oB fr) (oB fr) .rax .rcx (Int64.ofInt a.disp) J P)
      ((stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2])) ∧
    NodeW W₀ K exe endPc R F (Flow.XchgSeg.xsNS ms lbl (_root_.Executable.labels exe).label ((dirs lb).zip [z0])
      ((stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2])) pc (pc + Int64.ofNat z0)
      (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr) (oB fr) (oB fr) .rax .rcx
      (Int64.ofInt a.disp) J P)

/-! ## The segment -/

section Lane

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat} {ms : MemSide isa}
  {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}

/-- **A lane store's segment**: from the node at `pc` (the frame's offsets
`oB fr`, `J`) to the node after both instructions with `J'`. At each state
`σ`, control `c` of `J`: the source takes a local run to `c1` with
`P σ c c1` (`hsrc`), an exchange site of `x`'s word at `sa` (`XchgSite`),
no hold pending; with the base register `a.base` valued `vb` (`opdVal` at
`rsOf`): `vb + disp` represents `sa` and is unmapped in the private memory of
the frame condition's states; for every loaded `r` and held word
`w'` the memory side relates, `d`'s
slot `off` updated by `r` keeps the base's value, the stored operand `w`'s
value `vw` represents `v`'s word, and `J'` holds of every state with those
slots and `%fs` base, the source past the exchange (`x` bound to `w'`). -/
theorem lane_segW {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31) (hF : FStable R F)
    (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {Cd : Int64 → List (Directive × Nat) → Prop} (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {Bl : Int64 → Nat → Label → Nat → Prop} {kk kk' : Nat} {pc pc' : Int64} {d : Scc.IR.Reg} {a : Scc.IR.Addr}
    {w : Scc.IR.Operand} (hI : InstsC2 fr Cd Bl kk pc [xchgLoad d a, xchgStore a w] kk' pc')
    {W₀ : Frag isa} {Kw : State → State → Prop}
    {J J' : AS → Ctl → Prop} {P : AS → Ctl → Ctl → Prop}
    (hsrc : ∀ σ c, J σ c → ∃ c1, LocalRun p c c1 ∧ P σ c c1)
    (hsite : ∀ σ c c1, J σ c → P σ c c1 → ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
      XchgSite c1 x sa u v e ∧ c1.hold = none ∧ (-(2 ^ 62) ≤ a.disp ∧ a.disp ≤ 2 ^ 62) ∧
      ∀ vb : BitVec 64, opdVal (rsOf fr) σ.slot (.reg a.base) = some vb.toNat →
        ValRep lbl (.loc sa 0) (vb + BitVec.ofInt 64 a.disp).toNat ∧
        (∀ m, F m → Mem.loadInt m.dmem (vb + BitVec.ofInt 64 a.disp) 8 = none) ∧
        ∀ (r : BitVec 64) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val r.toNat →
          ∀ off, rsOf fr d = some off →
          opdVal (rsOf fr) (upd σ.slot off r) (.reg a.base) = some vb.toNat ∧
          ∀ vw : BitVec 64, opdVal (rsOf fr) (upd σ.slot off r) w = some vw.toNat →
            (∃ tv wv, TermRun.evalAt c1.env v = some (tv, [wv]) ∧ ValRep lbl wv.val vw.toNat) ∧
            ∀ σ2 : AS, σ2.slot = upd σ.slot off r → σ2.regs.fsBase = σ.regs.fsBase →
              J' σ2 ⟨e, (x, u, [w']) :: c1.env, none⟩)
    (hLW : LaneW Cd W₀ Kw exe endPc R F ms lbl fr pc d a w J P) :
    SegW W₀ Kw p lbl ms (At exe endPc R F ⟨pc, oB fr, J⟩) (At exe endPc R F ⟨pc', oB fr, J'⟩) := by
  obtain ⟨lb, lw, off, z0, zL, zt, z1, z2, zS, hb, hw, hoff, hcB1, hcL, hcB2, hcS, -, rfl, hC1, hC2⟩ :=
    xchg_code hCd hI
  obtain ⟨db, hdb⟩ := dirs_getOp hb
  obtain ⟨dw, hdw⟩ := dirs_getOp hw
  have hz0 : [z0].length = (dirs lb).length := by rw [hdb]; rfl
  have hz1 : [z1].length = (dirs lb).length := by rw [hdb]; rfl
  have hz2 : [z2].length = (dirs lw).length := by rw [hdw]; rfl
  have hoK : (oB fr).kill .rax = oB fr := by simp [oB, SO.kill, rm]
  let L := (_root_.Executable.labels exe).label
  let B1 := (dirs lb).zip [z0]
  let B2 := (stDir off, zt) :: ((dirs lb).zip [z1] ++ (dirs lw).zip [z2])
  let i := Int64.ofInt a.disp
  obtain ⟨hok1, hB1⟩ := xchg_b1 hf h1 hb L pc hz0
  obtain ⟨hok2, hB2⟩ := xchg_b2 hf h1 hoff hb hw L (pc + Int64.ofNat z0 + Int64.ofNat zL) (zt := zt) hz1 hz2
  have hne1 : B1 ≠ [] := by simp [B1, hdb]
  have hne2 : B2 ≠ [] := by simp [B2]
  -- the source's exchange site, at the blocks' runs
  have hsite' : ∀ σ c c1, J σ c → P σ c c1 →
      ∃ (x : String) (sa : WeakMem.Address) (u : Ty) (v : At) (e : Expr),
      XchgSite c1 x sa u v e ∧ c1.hold = none ∧
      ValRep lbl (.loc sa 0) (bAddr (arun L B1 ⟨pc, oB fr, σ⟩).σ.regs .rcx i).toNat ∧
      ∀ (r : BitVec 64) (w' : TermRun.Word), ms.rd w' → ValRep lbl w'.val r.toNat →
        let σ1 := (arun L B1 ⟨pc, oB fr, σ⟩).σ
        let σ2 := (arun L B2 ⟨pc + Int64.ofNat z0 + Int64.ofNat zL, (oB fr).kill .rax, ownStep .rax r σ1⟩).σ
        bAddr σ2.regs .rcx i = bAddr σ1.regs .rcx i ∧
        (∃ tv wv, TermRun.evalAt c1.env v = some (tv, [wv]) ∧
          ValRep lbl wv.val ((σ2.regs.get64 .rax).setWidth 128).toNat) ∧
        J' σ2 ⟨e, (x, u, [w']) :: c1.env, none⟩ := by
    intro σ c c1 hJ hP
    obtain ⟨x, sa, u, v, e, hX, hh, hdisp, hk⟩ := hsite σ c c1 hJ hP
    have hdi : (Int64.ofInt a.disp).toInt = a.disp := toInt_ofInt_small hdisp.1 hdisp.2
    have hbA : ∀ regs : Reg64s, bAddr regs .rcx i = regs.get64 .rcx + BitVec.ofInt 64 a.disp := by
      intro regs; simp only [bAddr, i, hdi]
    obtain ⟨vb, hvb, he1⟩ := hB1 σ
    obtain ⟨hrep, -, hk⟩ := hk vb hvb
    have hr1 : (arun L B1 ⟨pc, oB fr, σ⟩).σ.regs.get64 .rcx = vb := by
      rw [he1]; simp
    refine ⟨x, sa, u, v, e, hX, hh, by rw [hbA, hr1]; exact hrep, ?_⟩
    intro r w' hrd hr
    obtain ⟨hb2, hk2⟩ := hk r w' hrd hr off hoff
    rw [hoK]
    obtain ⟨vb', vw, hvb', hvw, he2⟩ := hB2 (ownStep .rax r (arun L B1 ⟨pc, oB fr, σ⟩).σ)
    have hsl1 : (ownStep .rax r (arun L B1 ⟨pc, oB fr, σ⟩).σ).slot = σ.slot := by rw [he1]; rfl
    have hra : (ownStep .rax r (arun L B1 ⟨pc, oB fr, σ⟩).σ).regs.get64 .rax = r := by simp [ownStep]
    rw [hsl1, hra] at hvb' hvw
    rw [hsl1, hra] at he2
    have hvv : vb' = vb := BitVec.eq_of_toNat_eq (Option.some.inj (hvb'.symm.trans hb2))
    rw [hvv] at he2
    obtain ⟨⟨tv, wv, hev, hV⟩, hJ'⟩ := hk2 vw hvw
    simp only
    rw [he2]
    refine ⟨?_, ⟨tv, wv, hev, ?_⟩, hJ' _ rfl ?_⟩
    · rw [hbA, hbA, hr1]; simp
    · simp only [Reg64s.get64_set64, ↓reduceIte, toNat_setWidth128]; exact hV
    · simp only [Reg64s.set64_fsBase, ownStep]
      rw [he1]; simp only [Reg64s.set64_fsBase]
  -- the access's address unmapped in private memory
  have hdm1 : ∀ σ c c1, J σ c → P σ c c1 → ∀ m, F m →
      Mem.loadInt m.dmem (bAddr (arun L B1 ⟨pc, oB fr, σ⟩).σ.regs .rcx i) 8 = none := by
    intro σ c c1 hJ hP m hm
    obtain ⟨_, _, _, _, _, _, _, hdisp, hk⟩ := hsite σ c c1 hJ hP
    have hdi : (Int64.ofInt a.disp).toInt = a.disp := toInt_ofInt_small hdisp.1 hdisp.2
    obtain ⟨vb, hvb, he1⟩ := hB1 σ
    have hr1 : (arun L B1 ⟨pc, oB fr, σ⟩).σ.regs.get64 .rcx = vb := by
      rw [he1]; simp
    have hbA : bAddr (arun L B1 ⟨pc, oB fr, σ⟩).σ.regs .rcx i = vb + BitVec.ofInt 64 a.disp := by
      simp only [bAddr, i, hdi, hr1]
    rw [hbA]
    exact (hk vb hvb).2.1 m hm
  have hDL : ∀ s c σ, W₀ s c → Abs R (oB fr) s.st.1 σ → F s.st.1 →
      (Flow.XchgSeg.xsNL L B1 pc (pc + Int64.ofNat z0) (oB fr) (oB fr) J P).J σ c →
      Mem.loadInt s.st.1.dmem (bAddr σ.regs .rcx i) 8 = none := by
    rintro s c σ - - hFs ⟨σ0, c0, hJ, hP, rfl⟩
    exact hdm1 σ0 c0 c hJ hP _ hFs
  have hDS : ∀ s c σ, W₀ s c → Abs R (oB fr) s.st.1 σ → F s.st.1 →
      (Flow.XchgSeg.xsNS ms lbl L B1 B2 pc (pc + Int64.ofNat z0)
        (pc + Int64.ofNat z0 + Int64.ofNat zL + Int64.ofNat (zt + z1 + z2)) zL (oB fr) (oB fr) (oB fr) .rax .rcx i
        J P).J σ c →
      Mem.loadInt s.st.1.dmem (bAddr σ.regs .rcx i) 8 = none := by
    rintro s c σ - - hFs ⟨σ0, c0, c1, r, w', hJ, hP, hrd, hr, rfl, -⟩
    obtain ⟨_, _, _, _, _, _, _, _, hk⟩ := hsite' σ0 c0 c1 hJ hP
    rw [(hk r w' hrd hr).1]
    exact hdm1 σ0 c0 c1 hJ hP _ hFs
  -- the memory side's states
  obtain ⟨hW1, hWL, hW2, hWS⟩ := hLW lb lw off z0 zL zt z1 z2 zS hb hw hoff hC1 hC2
  exact Flow.XchgSeg.xchg_segW (B1 := B1) (B2 := B2) (oL := oB fr) (oS := oB fr) hne1 hne2 hok1
    (by rw [hoK]; exact hok2) hF hR hlo hhi (by decide) hcB1 hcL hcB2 hcS
    (fun σ => by obtain ⟨_, _, he⟩ := hB1 σ; rw [he]; exact ⟨rfl, rfl⟩)
    (fun σ => by rw [hoK]; obtain ⟨_, _, _, _, he⟩ := hB2 σ; rw [he]; exact ⟨rfl, rfl⟩)
    ⟨so_le_oB fr, by rw [hoK]; exact so_le_oB fr, so_le_oB fr⟩ hsrc hsite' hW1 hWL hW2 hWS hDL hDS

end Lane

/-! ## The construct's premise -/

/-- The lane's node at the exchange: `bodyN2` at the term `t`, the thread
pointer `tp` (`laneC_of`'s `J`). -/
def laneJ (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat)
    (fr : Scc.Emit.X64.Frame) (fp ra : BitVec 64) (tp : UInt64) (c0 : Ctl) (pc : Int64) (t : Expr)
    (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) :
    AS → Ctl → Prop :=
  ((bodyN2 p lbl lsize i fr fp ra c0 pc t (ofEnv2 env) lits cs bufs).withTp tp).J

/-- The lane's source relation at the exchange: `J` holds, and the local run
to `c1` reaches `NodeJ` at `t` with the environment's literal, buffer and
size facts (`laneC_of`'s `P`). -/
def laneP (p : Prog) (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (fr : Scc.Emit.X64.Frame) (J : AS → Ctl → Prop)
    (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV)) (cs bufs : List (String × Nat)) :
    AS → Ctl → Ctl → Prop :=
  fun σ c c1 => J σ c ∧ ∃ L sm B, LocalRun p c c1 ∧ NodeJE lbl (rsOf fr) t (ofEnv2 env) σ.slot c1 ∧
    EnvLit lits c1.env ∧ EnvB lits cs bufs L sm lsize c1.env ∧ MemB L sm B ∧ EnvSmall c1.env

/-- **The lane's facts at the exchange site** for `LaneW`'s discharge
(`laneC_of` proves them): at each state `σ`, control `c` of `J` and site
control `c1` of `P`, `c1` at the `let` `t` (not a `ret`); given the walk's facts at `t`
(free variables placed, register bases, immediates), `c1` placed in the slot
file, also with `d`'s slot updated; the displacement small; the base's value
not moved by `d`'s slot; and the element's word `vb + disp` the `k`-th word
of a placed label `l` at `b`, `k < lsize l`. -/
def LaneH (lbl : WeakMem.AllocLabel → Option Nat) (lsize : WeakMem.AllocLabel → Nat)
    (i : Expr → String → Nat → Option Nat) (fr : Scc.Emit.X64.Frame) (t : Expr) (env : Scc.Lower.Env)
    (d : Scc.IR.Reg) (a : Scc.IR.Addr) (J : AS → Ctl → Prop) (P : AS → Ctl → Ctl → Prop) : Prop :=
  ∀ σ c c1, J σ c → P σ c c1 →
    c1.term = t ∧ (∀ a, c1.term ≠ .ret a) ∧
    ((∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome) → LocBaseRegAt (ofEnv2 env) t →
      ImmIn i (ofEnv2 env) t →
      SlotRepAt i lbl (rsOf fr) σ.slot c1 ∧
        ∀ k, rsOf fr d = some k → ∀ v, SlotRepAt i lbl (rsOf fr) (upd σ.slot k v) c1) ∧
    (-(2 ^ 62) ≤ a.disp ∧ a.disp ≤ 2 ^ 62) ∧
    (∀ k, rsOf fr d = some k → ∀ r, opdVal (rsOf fr) (upd σ.slot k r) (.reg a.base) =
      opdVal (rsOf fr) σ.slot (.reg a.base)) ∧
    ∀ vb : BitVec 64, opdVal (rsOf fr) σ.slot (.reg a.base) = some vb.toNat →
      ∃ l b k, lbl l = some b ∧ k < lsize l ∧ (vb + BitVec.ofInt 64 a.disp).toNat = b + 8 * k

/-- An `elem2` type's one operand is one word. -/
theorem group_elem2 {u : Ty} (hu : Scc.Lower.elem2 u = true) (o : Scc.IR.Operand) : group u [o] = some [.one o] := by
  cases u <;> first | rfl | simp [Scc.Lower.elem2] at hu

/-- **A lane store** (`LaneC`) at the frames `fs`, in the frame's region
(`hlo`, `hhi`): the code predicate gives code (`hCd`); the memory side's
states at the exchange's nodes in `W₀` (inside `W` at `fs`, `hW₀`;
`LaneW` at the lane's `laneJ`, `laneP`, `hLW`); the words the memory side
reads numbers (`hrd`); room after each placed label for an element's
displacement (`LblRoom`); every placed label's words in the heap or `.data`
(`hrg`), none of which the frame condition's private memory loads (`hwn`). -/
theorem laneC_of {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    {ms : List TermRun.Frame → MemSide isa}
    {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop} {W : FragS isa}
    {K : State → State → Prop} {fr : Scc.Emit.X64.Frame} (hf : FrameOk fr) (h1 : fr.size ≤ 2 ^ 31)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -(fr.size : Int)) (hhi : 16 ≤ R.hi)
    {lcx : Scc.Lower.Ctx} {fp ra : BitVec 64} {tp : UInt64} {fs : List TermRun.Frame}
    {Cd : Int64 → List (Directive × Nat) → Prop} {Bl : Int64 → Nat → Label → Nat → Prop}
    (hCd : ∀ pc blk, Cd pc blk → CdOf exe endPc pc blk)
    {W₀ : Frag isa} (hW₀ : ∀ s c, W₀ s c → W s c fs)
    (hrd : ∀ w', (ms fs).rd w' → IsNum w') (hroom : LblRoom lbl)
    {Λ : Scc.Sem.Layout} (hrg : LblRange Λ lbl lsize) (hwn : ∀ m, F m → Spike.Lib.DmemPriv.WordsNone Λ m.dmem)
    {G0 : Ctl → Prop} {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {Ab : FragS isa}
    (hLW : ∀ (c0 : Ctl) (pc : Int64) (t : Expr) (env : Scc.Lower.Env) (lits : List (String × Scc.Lower.LitV))
      (cs bufs : List (String × Nat)) (d : Scc.IR.Reg) (a : Scc.IR.Addr) (w : Scc.IR.Operand), G0 c0 → T t →
      (∀ y ∈ Scc.Sem.exprFv t, (lookupS (ofEnv2 env) y).isSome) → LocBaseRegAt (ofEnv2 env) t →
      ImmIn i (ofEnv2 env) t →
      LaneH lbl lsize i fr t env d a (laneJ p lbl lsize i fr fp ra tp c0 pc t env lits cs bufs)
        (laneP p lbl lsize fr (laneJ p lbl lsize i fr fp ra tp c0 pc t env lits cs bufs) t env lits cs bufs) →
      LaneW Cd W₀ K exe endPc R F (ms fs) lbl fr pc d a w (laneJ p lbl lsize i fr fp ra tp c0 pc t env lits cs bufs)
        (laneP p lbl lsize fr (laneJ p lbl lsize i fr fp ra tp c0 pc t env lits cs bufs) t env lits cs bufs)) :
    LaneC p lbl lsize lcx fr Cd Bl exe endPc R F W K ms fp ra tp fs G0 i T Ab := by
  intro c0 pc pc' kk kk' env n x b j v e t bw rb o tj iv μ u nu mu tv w s1 lits cs bufs hG0 hT hfresh _ _ hgrp _ hXB
    hab hrf haj hbe hro hav hsl hI htot' himm' hlb' htot himm hlb
  let d := regName x n
  let a := slotAddr lcx.obj rb (o + iv * UInt64.ofNat (Scc.Obj.stride nu mu)) s1
  have hab' : a.base = rb := slotAddr_base _ _ _ _
  -- the registers of `b` and `v` are not `d`
  have hrbd : rb ≠ d := by
    have hm : Scc.IR.Operand.reg rb ∈ bw := by
      match bw, hrf with
      | [_], hrf => simp only [refO, Option.some.injEq, Prod.mk.injEq] at hrf; simp [hrf.1]
      | [_, _], hrf => simp only [refO, Option.some.injEq, Prod.mk.injEq] at hrf; simp [hrf.1]
    exact atomV_fresh hfresh hab x _ hm rb rfl
  have hwd : ∀ r, w = .reg r → r ≠ d := fun r hr => atomV_fresh hfresh hav x w (by simp) r hr
  have hupd : ∀ (sl : Int → BitVec 64) (off : Int) (r : BitVec 64) (o' : Scc.IR.Operand), rsOf fr d = some off →
      (∀ r', o' = .reg r' → r' ≠ d) → opdVal (rsOf fr) (upd sl off r) o' = opdVal (rsOf fr) sl o' := by
    intro sl off r o' hoff hne
    refine Spike.Lib.Form.opdVal_upd fun r' k' hor hr' => ?_
    have hk : k' ≠ off := fun hk => hne r' hor (rsOf_inj hf hr' (hk ▸ hoff))
    simp [upd_apply, hk]
  -- the nodes
  let J : AS → Ctl → Prop := laneJ p lbl lsize i fr fp ra tp c0 pc (.let_ x (.xchgAt b j v) e) env lits cs bufs
  let env' : Scc.Lower.Env := (x, u, [.reg d]) :: env
  let lits' := (x, Scc.Lower.opLit lcx.prog lits (.xchgAt b j v)) :: lits
  let cs' := Scc.Lower.csAfter x cs (.xchgAt b j v)
  let bufs' := Scc.Lower.bufsAfter x cs bufs (.xchgAt b j v)
  let J' : AS → Ctl → Prop := fun σ c => ∃ c0', FrameRunM p (c0, fs) (c0', fs) ∧
    ((bodyN2 p lbl lsize i fr fp ra c0' pc' e (ofEnv2 env') lits' cs' bufs').withTp tp).J σ c
  let P : AS → Ctl → Ctl → Prop := laneP p lbl lsize fr J (.let_ x (.xchgAt b j v) e) env lits cs bufs
  have hsrc : ∀ σ c, J σ c → ∃ c1, LocalRun p c c1 ∧ P σ c c1 := by
    intro σ c hJ
    obtain ⟨L, sm, B, c1, hr, hj, hn, hb, hm, hS⟩ := hJ.1.1
    exact ⟨c1, hr, hJ, L, sm, B, hr, hj, hn, hb, hm, hS⟩
  have hsite : ∀ σ c c1, J σ c → P σ c c1 → ∃ (x' : String) (sa : WeakMem.Address) (u' : Ty) (v' : At) (e' : Expr),
      XchgSite c1 x' sa u' v' e' ∧ c1.hold = none ∧ (-(2 ^ 62) ≤ a.disp ∧ a.disp ≤ 2 ^ 62) ∧
      ∀ vb : BitVec 64, opdVal (rsOf fr) σ.slot (.reg a.base) = some vb.toNat →
        ValRep lbl (.loc sa 0) (vb + BitVec.ofInt 64 a.disp).toNat ∧
        (∀ m, F m → Mem.loadInt m.dmem (vb + BitVec.ofInt 64 a.disp) 8 = none) ∧
        ∀ (r : BitVec 64) (w' : TermRun.Word), (ms fs).rd w' → ValRep lbl w'.val r.toNat →
          ∀ off, rsOf fr d = some off →
          opdVal (rsOf fr) (upd σ.slot off r) (.reg a.base) = some vb.toNat ∧
          ∀ vw : BitVec 64, opdVal (rsOf fr) (upd σ.slot off r) w = some vw.toNat →
            (∃ tv wv, TermRun.evalAt c1.env v' = some (tv, [wv]) ∧ ValRep lbl wv.val vw.toNat) ∧
            ∀ σ2 : AS, σ2.slot = upd σ.slot off r → σ2.regs.fsBase = σ.regs.fsBase →
              J' σ2 ⟨e', (x', u', [w']) :: c1.env, none⟩ := by
    intro σ c c1 hJ ⟨_, L, sm, B, hrun1, hj, hn, hb, hm, hS⟩
    obtain ⟨⟨-, hfj, hc0, -⟩, htp⟩ := hJ
    obtain ⟨hel, sa, vbN, k, hX, hh, hvbN, hdk, hk28, -, hlv, hks, hlt, hrep⟩ :=
      xchg_site hj hb hXB hgrp hroom hab hrf haj hbe hro hsl lcx.obj
    have hdk' : a.disp = 8 * (k : Int) := hdk
    refine ⟨x, sa, u, v, e, hX, hh, by omega, fun vb hvb => ?_⟩
    rw [hab'] at hvb ⊢
    have hvN : vb.toNat = vbN := Option.some.inj (hvb.symm.trans hvbN)
    have hadd : (vb + BitVec.ofInt 64 a.disp).toNat = vbN + 8 * k := by
      rw [hdk', toNat_add_ofInt8 (by omega), hvN]
    refine ⟨by rw [hadd]; exact hrep, fun m hm => heapWord_none hrg (hwn m hm) hlv hks hadd,
      fun r w' hrd' hr off hoff => ?_⟩
    refine ⟨by rw [hupd _ _ _ _ hoff (fun r' h => by cases h; exact hrbd)]; exact hvb, fun vw hvw => ?_⟩
    rw [hupd _ _ _ _ hoff hwd] at hvw
    obtain ⟨tv', wv, nv, hev, hnv, hV⟩ := xchg_val hj hgrp hav
    have hnv' : nv = vw.toNat := Option.some.inj (hnv.symm.trans hvw)
    refine ⟨⟨tv', wv, hev, hnv' ▸ hV⟩, fun σ2 hσ2 hfs => ?_⟩
    -- the node after the store: the ghost run to the post-exchange control
    obtain ⟨hd8, -, -⟩ := rsOf_bounds hf hoff
    have hfr : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds, ∀ r' k', o' = .reg r' → rsOf fr r' = some k' →
        k' ≠ off := fun q hq pl hpl o' ho' r' k' hor hr' hk =>
      fresh_ofEnv2 hfresh x q hq pl hpl o' ho' r' hor (rsOf_inj hf hr' (hk ▸ hoff))
    have hN := NJB.xchg2 (p := p) hj hn hb hm hS hel (hrd w' hrd') hoff hfr hr
    have hlit : Scc.Lower.opLit lcx.prog lits (.xchgAt b j v) = .leaf none := rfl
    have henv : ofEnv2 env' = (x, u, [.one (.reg d)]) :: ofEnv2 env := by
      simp only [env', ofEnv2, List.map_cons, group_elem2 hel, Option.getD_some]
    refine ⟨⟨e, (x, u, [w']) :: c1.env, none⟩, ?_, ⟨⟨L, sm, B, ?_⟩, ?_, .refl _, ?_⟩, ?_⟩
    · exact (FrameRunM.ofLocal hc0 fs).trans ((FrameRunM.ofLocal hrun1 fs).trans
        (FrameRunM.mem1 hh hj.1 trivial))
    · rw [hσ2, henv]; simp only [lits', hlit]; exact hN
    · obtain ⟨h0', h8'⟩ := hfj
      have hk1 : (0 : Int) ≠ off := by omega
      have hk2 : (8 : Int) ≠ off := by omega
      show σ2.slot 0 = fp ∧ σ2.slot 8 = ra
      rw [hσ2]
      simp only [upd_apply, hk1, hk2, ↓reduceIte, h0', h8', and_self]
    · rw [hσ2]
      refine SlotRepAt.of_nodeJE (NodeJE.xchg2 (u := u) hj hoff hfr hr) ?_ ?_ ?_
      · rw [← henv]; exact htot'
      · rw [← henv]; exact hlb'
      · rw [← henv]; exact himm'
    · show σ2.regs.fsBase = tp
      rw [hfs]; exact htp
  -- the site's facts for `LaneW`
  have hH : LaneH lbl lsize i fr (.let_ x (.xchgAt b j v) e) env d a J P := by
    intro σ c c1 _ ⟨_, L, sm, B, _, hj, _, hb, _, _⟩
    obtain ⟨-, sa, vbN, k, -, -, hvbN, hdk, hk28, -, hlv, hks, hlt, -⟩ :=
      xchg_site hj hb hXB hgrp hroom hab hrf haj hbe hro hsl lcx.obj
    have hdk' : a.disp = 8 * (k : Int) := hdk
    refine ⟨hj.1, (fun _ h => by rw [hj.1] at h; cases h),
      fun htot hlb himm => ⟨SlotRepAt.of_nodeJE hj htot hlb himm, fun off hoff v => ?_⟩, by omega,
      fun off hoff r => hupd _ _ _ _ hoff (fun r' h => by rw [hab'] at h; cases h; exact hrbd), fun vb hvb => ?_⟩
    · have hsl' : ∀ q ∈ ofEnv2 env, ∀ pl ∈ q.2.2, ∀ o' ∈ pl.opds,
          opdVal (rsOf fr) (upd σ.slot off v) o' = opdVal (rsOf fr) σ.slot o' :=
        fun q hq pl hpl o' ho' => Spike.Lib.Form.opdVal_upd fun r' k' hor hr' => by
          have hk : k' ≠ off := fun hk =>
            fresh_ofEnv2 hfresh x q hq pl hpl o' ho' r' hor (rsOf_inj hf hr' (hk ▸ hoff))
          simp [upd_apply, hk]
      exact SlotRepAt.of_nodeJE ⟨hj.1, hj.2.1, hj.2.2.congr hsl'⟩ htot hlb himm
    · rw [hab'] at hvb
      have hvN : vb.toNat = vbN := Option.some.inj (hvb.symm.trans hvbN)
      exact ⟨_, _, _, hlv, hks, by rw [hdk', toNat_add_ofInt8 (by omega), hvN]⟩
  have hseg := lane_segW (ms := ms fs) (J := J) (J' := J') (P := P) hf h1 hF hR hlo hhi hCd hI hsrc hsite
    (hLW c0 pc _ env lits cs bufs _ _ _ hG0 hT htot hlb himm hH)
  refine (SegWS.liftS fs hseg hW₀).mono_post ?_
  rintro s c fs' ⟨⟨he, hn, hdc, hpc, σ, hA, hD, c0', hrun, hJ⟩, rfl⟩
  exact .inl ⟨rfl, c0', hrun, he, hn, hdc, hpc, σ, hA, hD, hJ⟩

end Spike.Lib.LowerX64
