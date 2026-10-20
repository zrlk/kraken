/-
The KNOWN_GAPS fence-release writer at the cell level.

```
 fwriter:
 0   mov  w2, #42
 1   mov  w3, #1
 2   str  w2, [x1]      // data := 42 (plain)
 3   dmb  ish           // fence .sy
 4   str  w3, [x0]      // flag := 1 (plain, fence-released)
 5 done_w:
```
`X0` holds the flag address, `X1` the data address. With a release predicate
`rel` under which `flag := 1` is impure (it owns `data`) and every `data`
value is pure, the cells:

- `str w3, [x0]` (`exec_fw_str_flag`) is **not** `RelWrites` for `rel`
  (`fw_str_flag_not_relWrites`): a plain store of an impure value. This is
  the counterexample of `KNOWN_GAPS.md`: `PromisePure` (at `G₀`) is false for
  this program.
- It **is** `RelWritesF` at the flag `True` (`fw_str_flag_relWritesF`): the
  store is fence-released. The flag is the thread's `views.FenceRel` at
  position 4, which `dmb ish` establishes (`fw_dmb_fenceRel`, through
  `stepOne_fenceRel_of_fence_sy`).
- `str w2, [x1]` is `RelWritesF` at every flag (`fw_str_data_relWritesF`),
  `dmb ish` and the `mov`s write nothing.

So the cell condition of `theorem1IIPure_of_relWritesF` holds for the writer
with the thread invariant "at position 4, `views.FenceRel`" (the invariant
itself, a reachability fact, is not proved here). **No full program theorem:**
that also needs `NPSafeP (GHyb g.rel) (K2Scope AllocIds)` for the writer, a
rule that prepays the promise of `flag := 1` when the next instruction is the
fence-released `str` (`Thread.RelFulfilsLiveF` of an impure message), i.e. a
`ThreadRuleRXG (GHyb rel)` whose `prepay` covers the second `GHyb` disjunct
(the existing writer rule only prepays at `stlr`).
-/
import Kraken.Promising.SLR.A64Trees
import Kraken.Promising.SLR.PromisePureF
import Kraken.AArch64.Parser

namespace Kraken.Promising.SLR.PromisePureFTests

open Kraken Kraken.Promising Kraken.Promising.AArch64

/-- The fence-release writer of `KNOWN_GAPS.md`: data `:= 42` (plain),
`dmb ish`, flag `:= 1` (plain). -/
def fwriter : Program := parseAArch64("
    mov w2, #42
    mov w3, #1
    str w2, [x1]
    dmb ish
    str w3, [x0]
done_w:
")

/-- info: 6 -/
#guard_msgs in
#eval fwriter.length

/-! ## A concrete release predicate

`relEx f`: the flag word owns everything (`Pred.bot` is impure at every
value: it holds of no resource), every other word is `Pred.top` (pure). -/

/-- The flag word at `f` is impure, every other word pure. -/
def relEx (f : BitVec 64) : Loc → Pred := fun l => if l = ⟨f, 4⟩ then Pred.bot else Pred.top

theorem relEx_flag_impure (f : BitVec 64) (v : Val) : ¬ Pred.Pure (relEx f ⟨f, 4⟩) v := by
  intro h
  simpa [relEx, Pred.bot] using h default default

theorem relEx_pure {f : BitVec 64} {l : Loc} (hl : l ≠ ⟨f, 4⟩) (v : Val) : Pred.Pure (relEx f l) v := by
  simp [relEx, hl, Pred.Pure, Pred.top]

variable [layout : _root_.Layout]

open Kraken.Promising.SLR.A64Trees (At goto next_pc)

variable [hw : Executable.ValidLayout (layout fwriter)]

/-- Read the writer's cell at position `i` (as `MpTrees.wcell`). -/
local macro "fcell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  have hc := Kraken.Executable.codeAt_addrOf (p := fwriter) (i := $i)
    (d := fwriter[$i]) (by decide) (by decide)
  rw [← ($h).pc] at hc
  generalize hd : fwriter[$i] = d at hc
  simp only [fwriter, List.getElem_cons_succ, List.getElem_cons_zero] at hd
  subst hd
  rw [exec_eq_of_codeAt ($h).exe ($h).decls ($h).ne hc]
  simp only [Directive.interp, Instr.interp, Operation.interp, ConstExpr.evalBranchTarget,
    ConstExpr.interp]
  simp [goto, toEv, RegOrSp.interpBase, MachineData.rmwK, MachineData.loadK,
    MachineData.storeK, MachineData.load, MachineData.store, EvTree.access_empty, EvTree.map,
    AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore, AddrExpr.checkSPAlignment,
    AddrExpr.eval, MachineData.setRegOrZr, MachineData.setRegOrSp, Reg64s.getRegOrSp,
    Reg64s.getRegOrSp64, RegOrSp.base, RegOrZr.base, RegOrZr.isZr, Reg64s.getXReg, $ts,*]))

/-- `str w2, [x1]` (position 2): a plain store of `X2`'s low word to the data
word. -/
theorem exec_fw_str_data (st : State) (h : At fwriter st 2) {d : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = d) (hdd : Mem.loadInt st.st.1.dmem d 4 = none) :
    isa.exec st = some (.store .plain false ⟨d, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X2.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout fwriter).addrOf 3))) := by
  rw [next_pc h (by decide)]
  fcell h 2 [hx1, hdd]

/-- `dmb ish` (position 3): a full fence. -/
theorem exec_fw_dmb (st : State) (h : At fwriter st 3) :
    isa.exec st = some (.fence .sy fun _ => .done (goto st st.st.1 ((layout fwriter).addrOf 4))) := by
  rw [next_pc h (by decide)]
  fcell h 3 []

/-- `str w3, [x0]` (position 4): a plain store of `X3`'s low word to the
flag. -/
theorem exec_fw_str_flag (st : State) (h : At fwriter st 4) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none) :
    isa.exec st = some (.store .plain false ⟨f, 4⟩
      (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec))
      fun _ => .done (goto st st.st.1 ((layout fwriter).addrOf 5))) := by
  rw [next_pc h (by decide)]
  fcell h 4 [hx0, hdf]

/-! ## The cell conditions -/

variable {rel : Loc → Pred}

/-- **`RelWrites` fails at the flag store** when `flag := X3` is impure. -/
theorem fw_str_flag_not_relWrites (st : State) (h : At fwriter st 4) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none)
    (himp : ¬ Pred.Pure (rel ⟨f, 4⟩) (BitVec.setWidth 128 (BitVec.setWidth 32 st.st.1.regs.X3.toBitVec)))
    {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    ¬ tree.RelWrites Arch.armv8 fun l v => Pred.Pure (rel l) v := by
  rw [exec_fw_str_flag st h hx0 hdf] at hex
  obtain rfl := Option.some.inj hex
  exact fun hR => himp (hR.1 (by decide))

/-- **The flag store is `RelWritesF` once fence-released**, for every `rel`. -/
theorem fw_str_flag_relWritesF (st : State) (h : At fwriter st 4) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none)
    {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    tree.RelWritesF Arch.armv8 (fun l v => Pred.Pure (rel l) v) True := by
  rw [exec_fw_str_flag st h hx0 hdf] at hex
  obtain rfl := Option.some.inj hex
  exact ⟨fun _ hn => absurd trivial hn, fun _ => trivial⟩

/-- The data store is `RelWritesF` at every flag when every data value is
pure. -/
theorem fw_str_data_relWritesF (st : State) (h : At fwriter st 2) {d : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = d) (hdd : Mem.loadInt st.st.1.dmem d 4 = none)
    (hpure : ∀ v, Pred.Pure (rel ⟨d, 4⟩) v) {F : Prop} {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    tree.RelWritesF Arch.armv8 (fun l v => Pred.Pure (rel l) v) F := by
  rw [exec_fw_str_data st h hx1 hdd] at hex
  obtain rfl := Option.some.inj hex
  exact ⟨fun _ _ => hpure _, fun _ => trivial⟩

/-- `dmb ish` writes nothing. -/
theorem fw_dmb_relWritesF (st : State) (h : At fwriter st 3) {Q : Loc → Val → Prop} {F : Prop}
    {tree : EvTree isa.State} (hex : isa.exec st = some tree) : tree.RelWritesF Arch.armv8 Q F := by
  rw [exec_fw_dmb st h] at hex
  obtain rfl := Option.some.inj hex
  exact fun _ => trivial

/-- **After `dmb ish` the writer's views are `FenceRel`**: every outcome of
the step at position 3 has fence-released views, so the flag store at
position 4 runs with the flag `True`. -/
theorem fw_dmb_fenceRel {A : Arch} {t : Thread isa} {tid : Nat} {mem : Memory}
    {outs : List (Except String (Outcome isa))} (hstep : stepOne A t tid mem = some outs)
    {o : Outcome isa} (ho : .ok o ∈ outs) (h : At fwriter t.st 3) : o.thread.views.FenceRel :=
  stepOne_fenceRel_of_fence_sy hstep ho (exec_fw_dmb t.st h)

/-- **The cell condition at position 4, thread form**: a thread at the flag
store whose views are `FenceRel` satisfies the cell condition of
`theorem1IIPure_of_relWritesF` (flag `t.views.FenceRel`). -/
theorem fw_str_flag_cell {t : Thread isa} (h : At fwriter t.st 4) (hF : t.views.FenceRel) {f : BitVec 64}
    (hx0 : t.st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt t.st.st.1.dmem f 4 = none)
    {tree : EvTree isa.State} (hex : isa.exec t.st = some tree) :
    tree.RelWritesF Arch.armv8 (fun l v => Pred.Pure (rel l) v) t.views.FenceRel :=
  (fw_str_flag_relWritesF t.st h hx0 hdf hex).mono (fun _ _ h => h) fun _ => hF

/-- **The gap, concretely**: at the flag store, for `relEx`, the cell fails
`RelWrites` and satisfies `RelWritesF` once fence-released. -/
theorem fw_str_flag_relEx (st : State) (h : At fwriter st 4) {f : BitVec 64}
    (hx0 : st.st.1.regs.X0.toBitVec = f) (hdf : Mem.loadInt st.st.1.dmem f 4 = none)
    {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    ¬ tree.RelWrites Arch.armv8 (fun l v => Pred.Pure (relEx f l) v) ∧
      tree.RelWritesF Arch.armv8 (fun l v => Pred.Pure (relEx f l) v) True :=
  ⟨fw_str_flag_not_relWrites st h hx0 hdf (relEx_flag_impure f _) hex, fw_str_flag_relWritesF st h hx0 hdf hex⟩

/-- The data store is `RelWritesF` (indeed `RelWrites`) for `relEx` when the
data word is not the flag word. -/
theorem fw_str_data_relEx (st : State) (h : At fwriter st 2) {d f : BitVec 64}
    (hx1 : st.st.1.regs.X1.toBitVec = d) (hdd : Mem.loadInt st.st.1.dmem d 4 = none) (hdf : d ≠ f) {F : Prop}
    {tree : EvTree isa.State} (hex : isa.exec st = some tree) :
    tree.RelWritesF Arch.armv8 (fun l v => Pred.Pure (relEx f l) v) F :=
  fw_str_data_relWritesF st h hx1 hdd (relEx_pure (by simp [hdf])) hex

end Kraken.Promising.SLR.PromisePureFTests

#print axioms Kraken.Promising.SLR.PromisePureFTests.fw_str_flag_not_relWrites
#print axioms Kraken.Promising.SLR.PromisePureFTests.fw_str_flag_relWritesF
#print axioms Kraken.Promising.SLR.PromisePureFTests.fw_dmb_fenceRel
#print axioms Kraken.Promising.SLR.PromisePureFTests.fw_str_flag_cell
#print axioms Kraken.Promising.SLR.PromisePureFTests.fw_str_flag_relEx
#print axioms Kraken.Promising.SLR.PromisePureFTests.fw_str_data_relEx
