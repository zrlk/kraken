/-
**The AArch64 instance of `Kernel.DomHyps`** (`Scc/Sem/OwnDom.lean`) on the
fragment `WideA64.WideSt`: on it, every leaf of the FEAT_LSE2 semantics
maps exactly the private-memory addresses its state maps (`execLSE2_dom`:
a store to private memory only follows a successful load of the same bytes,
so it writes only mapped bytes, `Mem.mem_storeInt_of_loadInt` in
`Scc/Sem/OwnDom.lean`); the ABI's
return, thread-pointer change, `skip` and `setDmem` keep the fragment, and
the child of a `clone` has no private memory.

- `SameDom D s`: `s` maps the addresses `D` maps. `ED D e`: every leaf of
  the effects `e` maps them (`ed_*` combinators, one per effect shape of the
  fragment).
- `lse2Effects_ed`, `step_ed`: the effects of an instruction of the
  fragment keep the domain; `execLSE2_dom` lifts that to the event tree.
- `domHyps`: the instance, with `P := WideSt`.
-/
import Scc.Cert.Rt.WideA64
import Scc.Sem.OwnDom
open Std

namespace Scc.Cert.DomA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Cert.WideA64

/-- The private memory of `s` maps exactly the addresses `D` maps. -/
def SameDom (D : DataMem) (s : MachineData) : Prop := ∀ k, k ∈ s.dmem ↔ k ∈ D

/-- **Every leaf keeps the private memory's domain**: the `Effects` of an
instruction whose finished machine states map exactly the addresses `D`
maps, every effect handing back its private memory unchanged. -/
inductive ED (D : DataMem) : Effects → Prop
  | done {a} : SameDom D a.1 → ED D (.done a)
  | unimplemented (m) : ED D (.unimplemented m)
  | nonmem_load {dmem addr w ret} : (∀ v, ED D (ret v dmem)) → ED D (.nonmem_load dmem addr w ret)
  | nonmem_store {dmem addr w v ret} : ED D (ret dmem) → ED D (@Effects.nonmem_store dmem addr w v ret)
  | undefined {α inst ret} : (∀ a, ED D (ret a)) → ED D (@Effects.undefined α inst ret)
  | require_read_access {addr w ok} : (∀ u, ED D (ok u)) → ED D (.require_read_access addr w ok)
  | require_write_access {addr w ok} : (∀ u, ED D (ok u)) → ED D (.require_write_access addr w ok)
  | require_exec_access {p ok} : (∀ u, ED D (ok u)) → ED D (.require_exec_access p ok)
  | unaligned_sp {w} (sp) : ED D (@Effects.unaligned_sp w sp)
  | sync_load {k xcl dmem addr w ret} : (∀ v, ED D (ret v dmem)) → ED D (.sync_load k xcl dmem addr w ret)
  | sync_store {k xcl dmem addr w v ret} : (∀ b, ED D (ret b dmem)) →
      ED D (@Effects.sync_store k xcl dmem addr w v ret)
  | rmw {k nr dmem addr w op ret} : (∀ v, ED D (ret v dmem)) → ED D (.rmw k nr dmem addr w op ret)
  | fence {k ok} : (∀ u, ED D (ok u)) → ED D (.fence k ok)
  | sync_load_pair {k xcl dmem addr w ret} : (∀ v1 v2, ED D (ret v1 v2 dmem)) →
      ED D (.sync_load_pair k xcl dmem addr w ret)
  | syscall {info ret} : (∀ r, ED D (ret r)) → ED D (.syscall info ret)

section Combinators
variable {D : DataMem} {s : MachineData} (hs : SameDom D s)
include hs

/-- Close an `ED` goal over the `Effects` combinators. -/
local macro "ed" : tactic => `(tactic| repeat (first
  | assumption
  | (apply ED.nonmem_load; intros) | (apply ED.nonmem_store) | (apply ED.undefined; intros)
  | (apply ED.require_read_access; intros) | (apply ED.require_write_access; intros)
  | (apply ED.sync_load; intros) | (apply ED.sync_store; intros) | (apply ED.rmw; intros)
  | (apply ED.sync_load_pair; intros)
  | split
  | apply_assumption))

theorem ed_load {a : BitVec 64} {w : MemWidth} {k : w.type → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (s.load a w k) := by
  unfold MachineData.load; ed

theorem ed_loadK {lk : LoadKind} {xcl : Bool} {a : BitVec 64} {w : MemWidth}
    {k : w.type → MachineData → Effects} (h : ∀ v s', SameDom D s' → ED D (k v s')) :
    ED D (s.loadK lk xcl a w k) := by
  unfold MachineData.loadK; ed

theorem ed_loadPairK {lk : LoadKind} {xcl : Bool} {a : BitVec 64} {w : MemWidth}
    {k : w.type → w.type → MachineData → Effects} (h : ∀ v1 v2 s', SameDom D s' → ED D (k v1 v2 s')) :
    ED D (s.loadPairK lk xcl a w k) := by
  unfold MachineData.loadPairK; ed

theorem ed_store {a : BitVec 64} {w : MemWidth} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s', SameDom D s' → ED D (k s')) : ED D (s.store a v k) := by
  unfold MachineData.store
  apply ED.require_write_access; intro
  split
  · rename_i hl; exact h _ fun x => (Mem.mem_storeInt_of_loadInt hl x).trans (hs x)
  · exact ED.nonmem_store (h _ hs)

theorem ed_storeK {sk : StoreKind} {xcl : Bool} {a : BitVec 64} {w : MemWidth} {v : w.type}
    {k : Bool → MachineData → Effects} (h : ∀ b s', SameDom D s' → ED D (k b s')) :
    ED D (s.storeK sk xcl a v k) := by
  unfold MachineData.storeK
  apply ED.require_write_access; intro
  split
  · rename_i hl
    have hs' : SameDom D { s with dmem := Mem.storeInt s.dmem a w.bytes v.toInt } :=
      fun x => (Mem.mem_storeInt_of_loadInt hl x).trans (hs x)
    dsimp only
    split
    · exact ED.undefined fun ok => by split <;> exact h _ _ (by assumption)
    · exact h _ _ hs'
  · exact ED.sync_store fun _ => h _ _ hs

theorem ed_rmwK {rk : RmwKind} {nr : Bool} {a : BitVec 64} {w : MemWidth} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects} (h : ∀ v s', SameDom D s' → ED D (k v s')) :
    ED D (s.rmwK rk nr a w op k) := by
  unfold MachineData.rmwK
  apply ED.require_read_access; intro; apply ED.require_write_access; intro
  split
  · rename_i hl
    dsimp only; split
    · exact h _ _ fun x => (Mem.mem_storeInt_of_loadInt hl x).trans (hs x)
    · exact h _ _ hs
  · exact ED.rmw fun _ => h _ _ hs

omit hs in
theorem ed_interpBase {b : RegOrSp .W64} {k : BitVec 64 → Effects} (h : ∀ a, ED D (k a)) :
    ED D (b.interpBase s k) := by
  unfold RegOrSp.interpBase; repeat' split
  all_goals first | exact ED.unaligned_sp _ | exact h _

omit hs in
theorem ed_checkSP {m : AddrExpr} {k : Unit → Effects} (h : ∀ u, ED D (k u)) : ED D (m.checkSPAlignment s k) := by
  unfold AddrExpr.checkSPAlignment; repeat' split
  all_goals first | exact ED.unaligned_sp _ | exact h _

omit hs in
theorem ed_checkSPU {m : UnscaledAddrExpr} {k : Unit → Effects} (h : ∀ u, ED D (k u)) :
    ED D (m.checkSPAlignment s k) := by
  unfold UnscaledAddrExpr.checkSPAlignment; repeat' split
  all_goals first | exact ED.unaligned_sp _ | exact h _

end Combinators

/-- An address computation's write-back changes registers only. -/
theorem eval_dmem [Labels] (m : AddrExpr) (s : MachineData) (p : Std.Rco Int64) : (m.eval s p).2.dmem = s.dmem := by
  unfold AddrExpr.eval
  split
  · rfl
  · dsimp only; split <;> rfl

theorem SameDom.eval [Labels] {D : DataMem} {s : MachineData} (hs : SameDom D s) (m : AddrExpr)
    (p : Std.Rco Int64) : SameDom D (m.eval s p).2 := by
  intro k; rw [eval_dmem]; exact hs k

/-- Close a `SameDom` goal: the state, or one with registers changed. -/
local macro "sd" : tactic => `(tactic| first
  | assumption
  | exact SameDom.eval (by assumption) _ _
  | exact fun k => (by assumption : SameDom _ _) k)

/-- `ed` with the memory combinators. -/
local macro "edm" : tactic => `(tactic| repeat (first
  | assumption
  | (apply ed_load (by sd); intros) | (apply ed_loadK (by sd); intros)
  | (apply ed_loadPairK (by sd); intros)
  | (apply ed_store (by sd); intros) | (apply ed_storeK (by sd); intros)
  | (apply ed_rmwK (by sd); intros)
  | (apply ed_interpBase; intros) | (apply ed_checkSP; intros)
  | (apply ed_checkSPU; intros)
  | apply ED.unimplemented | apply ED.unaligned_sp
  | (apply ED.undefined; intros) | (apply ED.require_exec_access; intros) | (apply ED.fence; intros)
  | (apply ED.syscall; intros)
  | split
  | (apply_assumption <;> sd)
  | apply_assumption))

/-- **An operation of the fragment keeps the private memory's domain**,
given continuations that do from a state of the domain. -/
theorem interp_ed [Labels] {w : RegWidth} (op : Operation w) (hw : op.wideOk = true) (p : Std.Rco Int64)
    {D : DataMem} (s : MachineData) (hs : SameDom D s) {next : MachineData → Effects}
    {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, SameDom D s → ED D (next s)) (hj : ∀ pc s, SameDom D s → ED D (jmp pc s)) :
    ED D (op.interp p s next jmp) := by
  cases w <;> cases op
  all_goals first | (simp [Operation.wideOk] at hw; done) | skip
  all_goals try (revert hw; cases ‹MemWidth› <;> intro hw <;> try cases hw)
  all_goals (simp only [Operation.interp, AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore,
    UnscaledAddrExpr.interpLoad, UnscaledAddrExpr.interpStore, Literal.interpLoad, MachineData.setRegOrZr]
    <;> edm)


theorem directive_ed [Labels] {d : Directive} (hd : d.wideOk = true) {D : DataMem} (s : MachineData)
    (hs : SameDom D s) (p : Std.Rco Int64) {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, SameDom D s → ED D (next s)) (hj : ∀ pc s, SameDom D s → ED D (jmp pc s)) :
    ED D (d.interp s p next jmp) := by
  cases d with
  | label => exact hn s hs
  | instr i => exact ED.require_exec_access fun _ => interp_ed i.operation hd p s hs hn hj
  | byteArray => exact ED.unimplemented _

theorem directives_ed [Labels] {D : DataMem} {ret : Int64 → MachineData → Effects}
    (hr : ∀ pc s, SameDom D s → ED D (ret pc s)) :
    ∀ (ds : List (Directive × Nat)), (∀ c ∈ ds, c.1.wideOk = true) →
      ∀ s pc, SameDom D s → ED D (Directives.interp ds s pc ret)
  | [], _, s, pc, hs => hr pc s hs
  | (_, _) :: ds, h, s, _, hs =>
    directive_ed (h _ (List.mem_cons_self ..)) s hs _
      (fun s hs => directives_ed hr ds (fun c hc => h c (List.mem_cons_of_mem _ hc)) s _ hs) hr

theorem step_ed {e : _root_.Executable} (he : ExeWide e) (st : MachineState) :
    ED st.1.dmem (_root_.Executable.step e st fun s' => .done s') := by
  unfold _root_.Executable.step
  letI := _root_.Executable.labels e
  exact directives_ed (fun _ _ hs => ED.done hs) _ (fun c hc => he c (mem_of_mem_directivesAtAddress hc)) _ _
    fun _ => Iff.rfl

theorem lse2Effects_ed {s : State} (he : ExeWide s.exe) {e : Effects} (h : lse2Effects s = some e) :
    ED s.st.1.dmem e := by
  unfold lse2Effects at h
  split at h
  rename_i st pc hst
  rw [hst]
  split at h
  · rename_i d z hc
    have hd := he _ (mem_of_cell hc)
    unfold Directive.interpLSE2? at h
    split at h
    · rename_i _ _ src
      have hs : SameDom st.dmem st := fun _ => Iff.rfl
      have hev := @SameDom.eval (_root_.Executable.labels s.exe) _ _ hs src (.mk pc (pc + .ofNat z))
      revert hev
      generalize @AddrExpr.eval (_root_.Executable.labels s.exe) src _ _ = r at h
      obtain ⟨addr, s'⟩ := r
      intro hev
      by_cases ha : (addr % 16 != 0) = true <;>
        simp only [ha, ↓reduceIte, Option.some.injEq, reduceCtorEq, Bool.false_eq_true] at h
      subst h
      refine ed_checkSP fun _ => ed_loadPairK hev fun _ _ _ h3 => ?_
      simp only [MachineData.setRegOrZr]
      repeat' split
      all_goals exact ED.done (by sd)
    · simp [Directive.wideOk, Operation.wideOk] at hd
    · cases h
  · cases h

/-- **`toEv` of domain-keeping effects**: every leaf maps exactly `D`. -/
theorem toEv_leaf {ds : Decls} {D : DataMem} {e : Effects} (h : ED D e) {x : MachineState}
    (hl : TreeLeaf (toEv ds e) x) : SameDom D x.1 := by
  induction h with
  | done h0 => simp only [toEv, TreeLeaf] at hl; subst hl; exact h0
  | unimplemented | unaligned_sp | syscall => simp only [toEv, TreeLeaf] at hl
  | nonmem_load _ ih | sync_load _ ih =>
    simp only [toEv, EvTree.access] at hl; split at hl
    · obtain ⟨_, hl⟩ := hl; exact ih _ hl
    · exact hl.elim
  | nonmem_store _ ih =>
    simp only [toEv, EvTree.access] at hl; split at hl
    · obtain ⟨_, hl⟩ := hl; exact ih hl
    · exact hl.elim
  | sync_store _ ih | rmw _ ih =>
    simp only [toEv, EvTree.access] at hl; split at hl
    · obtain ⟨_, hl⟩ := hl; exact ih _ hl
    · exact hl.elim
  | fence _ ih => simp only [toEv, TreeLeaf] at hl; obtain ⟨_, hl⟩ := hl; exact ih _ hl
  | require_read_access _ ih | require_write_access _ ih | require_exec_access _ ih =>
    simp only [toEv] at hl; exact ih _ hl
  | @undefined α inst ret _ ih =>
    cases inst <;> simp only [toEv, TreeLeaf] at hl
    obtain ⟨_, hl⟩ := hl; exact ih _ hl
  | sync_load_pair _ ih =>
    simp only [toEv] at hl
    split at hl
    · simp only [EvTree.access] at hl; split at hl
      · obtain ⟨_, hl⟩ := hl; exact ih _ _ hl
      · exact hl.elim
    · simp only [EvTree.access] at hl; split at hl
      · obtain ⟨_, hl⟩ := hl; split at hl
        · obtain ⟨_, hl⟩ := hl; exact ih _ _ hl
        · exact hl.elim
      · exact hl.elim


/-- **The FEAT_LSE2 semantics on the fragment keeps the private memory's
domain**: every leaf maps exactly the addresses the state maps. -/
theorem execLSE2_dom {s : State} (hs : WideSt s) {t : EvTree State} (h : execLSE2 s = some t) {s' : State}
    (hl : TreeLeaf t s') (k : BitVec 64) : k ∈ s'.st.1.dmem ↔ k ∈ s.st.1.dmem := by
  unfold execLSE2 at h
  split at h
  · cases h
  · split at h
    · rename_i e he
      cases h
      obtain ⟨x, hx, rfl⟩ := leaf_of_map _ hl
      exact toEv_leaf (lse2Effects_ed hs.2 he) hx k
    · split at h
      · rename_i hx
        exfalso
        unfold State.isCaspX at hx
        split at hx
        · rename_i d hd
          obtain ⟨z, hm⟩ := mem_of_directive hd
          have hw := hs.2 _ hm
          unfold Directive.isCaspX at hx
          split at hx
          · simp [Directive.wideOk, Operation.wideOk] at hw
          · cases hx
        · cases hx
      · unfold exec at h
        split at h
        · cases h
        · cases h
          obtain ⟨x, hx, rfl⟩ := leaf_of_map _ hl
          exact toEv_leaf (step_ed hs.2 _) hx k

/-- **The AArch64 instance of `Kernel.DomHyps`** on the fragment: every leaf
keeps `WideSt` and the private memory's domain; the ABI's return,
thread-pointer change, `setDmem` and `skip` change the machine state only,
keeping `WideSt`; `ret` and `setTp` keep the private memory and the child
of a `clone` has none. -/
theorem domHyps : Kernel.DomHyps A64.abi WideSt where
  exec _ _ _ hs h hl := ⟨exec_wideInv _ _ _ hs h hl, execLSE2_dom hs h hl⟩
  ret _ _ hs := ⟨hs, rfl⟩
  setTp _ _ hs := ⟨hs, rfl⟩
  child _ _ _ hs := ⟨hs, rfl⟩
  setDmem _ _ hs := hs
  skip _ hs := hs

end Scc.Cert.DomA64
