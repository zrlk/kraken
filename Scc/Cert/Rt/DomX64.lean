/-
**The x86-64 instance of `Kernel.DomHyps`** (`Scc/Sem/OwnDom.lean`) on the
fragment `WideX64.WideSt`: on it, every leaf of the x86-64 semantics maps
exactly the private-memory addresses its state maps (`exec_dom`: a store to
private memory only follows a successful load of the same bytes, so it
writes only mapped bytes, `Mem.mem_storeInt_of_loadInt`); the ABI's return,
thread-pointer change, `skip` and `setDmem` keep the fragment, and the child
of a `clone` has no private memory.

- `SameDom D s`: `s` maps the addresses `D` maps. `ED D e`: every leaf of
  the effects `e` maps them (`ed_*` combinators, one per effect shape of the
  fragment; the vector stores and `cmpxchg16b` are outside it).
- `interp_ed`, `avxInterp_ed`, `step_ed`: the effects of an instruction of
  the fragment keep the domain; `exec_dom` lifts that to the event tree.
- `domHyps`: the instance, with `P := WideSt`.
-/
import Scc.Cert.Rt.WideX64
import Scc.Sem.OwnDom

namespace Scc.Cert.DomX64

open Kraken Kraken.Promising Scc.Sem Scc.Cert.WideX64

/-- The private memory of `s` maps exactly the addresses `D` maps. -/
def SameDom (D : DataMem) (s : MachineData) : Prop := ∀ k, k ∈ s.dmem ↔ k ∈ D

/-- **Every leaf keeps the private memory's domain**: the `Effects` of an
instruction whose finished machine states map exactly the addresses `D`
maps, every effect handing back its private memory unchanged. No vector
store and no 16-byte RMW (`nonmem_store_avx`, `rmw16`). -/
inductive ED (D : DataMem) : Effects → Prop
  | done {a} : SameDom D a.1 → ED D (.done a)
  | unimplemented (m) : ED D (.unimplemented m)
  | gp_unaligned (a w) : ED D (.gp_unaligned a w)
  | nonmem_load {dmem addr w ret} : (∀ v, ED D (ret v dmem)) → ED D (.nonmem_load dmem addr w ret)
  | nonmem_store {dmem addr w v ret} : ED D (ret dmem) → ED D (@Effects.nonmem_store dmem addr w v ret)
  | undefined {α inst ret} : (∀ a, ED D (ret a)) → ED D (@Effects.undefined α inst ret)
  | require_read_access {addr w ok} : (∀ u, ED D (ok u)) → ED D (.require_read_access addr w ok)
  | require_write_access {addr w ok} : (∀ u, ED D (ok u)) → ED D (.require_write_access addr w ok)
  | require_exec_access {p ok} : (∀ u, ED D (ok u)) → ED D (.require_exec_access p ok)
  | sync_load {k xcl dmem addr w ret} : (∀ v, ED D (ret v dmem)) → ED D (.sync_load k xcl dmem addr w ret)
  | sync_store {k xcl dmem addr w v ret} : (∀ b, ED D (ret b dmem)) →
      ED D (@Effects.sync_store k xcl dmem addr w v ret)
  | rmw {k dmem addr w op ret} : (∀ v, ED D (ret v dmem)) → ED D (.rmw k dmem addr w op ret)
  | fence {k ok} : (∀ u, ED D (ok u)) → ED D (.fence k ok)
  | require_read_access_avx {addr w atm ok} : (∀ u, ED D (ok u)) →
      ED D (.require_read_access_avx addr w atm ok)
  | require_write_access_avx {addr w atm ok} : (∀ u, ED D (ok u)) →
      ED D (.require_write_access_avx addr w atm ok)
  | nonmem_load_avx {atm dmem addr w ret} : (∀ v, ED D (ret v dmem)) →
      ED D (.nonmem_load_avx atm dmem addr w ret)
  | syscall {info ret} : (∀ r, ED D (ret r)) → ED D (.syscall info ret)

/-- Close a `SameDom` goal: the state, or one with registers changed. -/
local macro "sd" : tactic => `(tactic| first
  | assumption
  | exact fun k => (by assumption : SameDom _ _) k)

section Combinators
variable {D : DataMem} {s : MachineData} (hs : SameDom D s)
include hs

theorem ed_load {a : BitVec 64} {w : Width} {k : w.type → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (s.load a w k) := by
  unfold MachineData.load
  refine ED.require_read_access fun _ => ?_
  split
  · exact h _ _ hs
  · exact ED.nonmem_load fun _ => h _ _ hs

theorem ed_store {a : BitVec 64} {w : Width} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s', SameDom D s' → ED D (k s')) : ED D (s.store a v k) := by
  unfold MachineData.store
  refine ED.require_write_access fun _ => ?_
  split
  · rename_i hl; exact h _ fun x => (Mem.mem_storeInt_of_loadInt hl x).trans (hs x)
  · exact ED.nonmem_store (h _ hs)

theorem ed_storeNT {a : BitVec 64} {w : Width} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s', SameDom D s' → ED D (k s')) : ED D (s.storeNT a v k) := by
  unfold MachineData.storeNT
  refine ED.require_write_access fun _ => ?_
  split
  · rename_i hl; exact h _ fun x => (Mem.mem_storeInt_of_loadInt hl x).trans (hs x)
  · exact ED.sync_store fun _ => h _ hs

theorem ed_rmwK {rk : RmwKind} {a : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects} (h : ∀ v s', SameDom D s' → ED D (k v s')) :
    ED D (s.rmwK rk a w op k) := by
  unfold MachineData.rmwK
  refine ED.require_read_access fun _ => ED.require_write_access fun _ => ?_
  split
  · rename_i hl
    dsimp only; split
    · exact h _ _ fun x => (Mem.mem_storeInt_of_loadInt hl x).trans (hs x)
    · exact h _ _ hs
  · exact ED.rmw fun _ => h _ _ hs

theorem ed_rmwPlain {a : BitVec 64} {w : Width} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects} (h : ∀ v s', SameDom D s' → ED D (k v s')) :
    ED D (s.rmwPlain a w op k) := by
  unfold MachineData.rmwPlain
  refine ed_load hs fun _ s' hs' => ?_
  split
  · exact ed_store hs' (h _)
  · exact h _ _ hs'

theorem ed_loadAvx {a : BitVec 64} {w : AvxWidth} {k : w.type → MachineData → Effects} {ca atm : Bool}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (s.loadAvx a w k ca atm) := by
  unfold MachineData.loadAvx
  split
  · exact ED.gp_unaligned _ _
  · refine ED.require_read_access_avx fun _ => ?_
    split
    · exact h _ _ hs
    · exact ED.nonmem_load_avx fun _ => h _ _ hs

variable [Labels] [AddressSize] {p : Std.Rco Int64}

theorem ed_rmInterp {w : Width} {o : RegOrMem w} {k : w.type → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (o.interp s p k) := by
  cases o with
  | reg _ => exact h _ _ hs
  | mem _ => exact ed_load hs h

theorem ed_opInterp {w : Width} {o : Operand w} {k : w.type → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (o.interp s p k) := by
  cases o with
  | regOrMem _ => exact ed_rmInterp hs h
  | imm _ => exact h _ _ hs

theorem ed_rmInterpSeg {w : Width} {o : RegOrMem w} {seg : BitVec 64} {k : w.type → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (o.interpSeg seg s p k) := by
  cases o with
  | reg _ => exact h _ _ hs
  | mem _ => exact ed_load hs h

theorem ed_opInterpSeg {w : Width} {o : Operand w} {seg : BitVec 64} {k : w.type → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (o.interpSeg seg s p k) := by
  cases o with
  | regOrMem _ => exact ed_rmInterpSeg hs h
  | imm _ => exact h _ _ hs

theorem ed_relInterp {o : RelRegOrMem} {k : BitVec 64 → MachineData → Effects}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (o.interp s p k) := by
  cases o with
  | rel _ => exact h _ _ hs
  | reg _ => exact h _ _ hs
  | mem _ => exact ed_load hs h

theorem ed_avxInterp {w : AvxWidth} {o : AvxRegOrMem w} {k : w.type → MachineData → Effects} {ca atm : Bool}
    (h : ∀ v s', SameDom D s' → ED D (k v s')) : ED D (o.interp s p k ca atm) := by
  cases o with
  | avx _ => exact h _ _ hs
  | mem _ => exact ed_loadAvx hs h

/-- A write of a destination: a register, or memory. -/
theorem ed_set {w : Width} {d : Dst w} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s', SameDom D s' → ED D (k s')) : ED D (s.set d v p k) := by
  cases d with
  | reg _ => exact h _ hs
  | mem _ => exact ed_store hs h

theorem ed_setSeg {w : Width} {d : Dst w} {seg : BitVec 64} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s', SameDom D s' → ED D (k s')) : ED D (s.setSeg seg d v p k) := by
  cases d with
  | reg _ => exact h _ hs
  | mem _ => exact ed_store hs h

/-- A read-modify-write of a register or of memory. -/
theorem ed_rmw {w : Width} {o : RegOrMem w} {lock : Bool} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects} (h : ∀ v s', SameDom D s' → ED D (k v s')) :
    ED D (o.rmw lock s p op k) := by
  cases o with
  | reg _ => dsimp only [RegOrMem.rmw]; split <;> exact h _ _ hs
  | mem _ =>
    dsimp only [RegOrMem.rmw]
    split
    · exact ed_rmwK hs h
    · exact ed_rmwPlain hs h

end Combinators

/-- `ed` with the memory and operand combinators. -/
local macro "edm" : tactic => `(tactic| repeat (first
  | assumption
  | (apply ed_load (by sd); intros) | (apply ed_store (by sd); intros) | (apply ed_storeNT (by sd); intros)
  | (apply ed_rmwK (by sd); intros) | (apply ed_rmw (by sd); intros) | (apply ed_set (by sd); intros)
  | (apply ed_setSeg (by sd); intros)
  | (apply ed_rmInterp (by sd); intros) | (apply ed_opInterp (by sd); intros)
  | (apply ed_rmInterpSeg (by sd); intros) | (apply ed_opInterpSeg (by sd); intros)
  | (apply ed_relInterp (by sd); intros) | (apply ed_avxInterp (by sd); intros)
  | apply ED.unimplemented | apply ED.gp_unaligned
  | (apply ED.undefined; intros) | (apply ED.require_exec_access; intros) | (apply ED.fence; intros)
  | (apply ED.syscall; intros)
  | (apply ED.done; sd)
  | split
  | (apply_assumption <;> sd)
  | apply_assumption))

/-- `imul` of the fragment (`interp_ed`). -/
theorem imul_ed [Labels] [AddressSize] {w : Width} (d : Option (Dst w)) (a : RegOrMem w) (b : Operand w)
    (hw : (Operation.imul d a b).wideOk = true) (p : Std.Rco Int64) {D : DataMem} (s : MachineData)
    (hs : SameDom D s) {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, SameDom D s → ED D (next s)) : ED D ((Operation.imul d a b).interp p s next jmp) := by
  cases d <;> cases w
  all_goals try simp only [Operation.wideOk, Operation.narrowOk] at hw
  all_goals try (obtain ⟨_, rfl⟩ := noMem_eq hw)
  all_goals (simp only [Operation.interp] <;> edm)

/-- **A regular operation of the fragment keeps the private memory's
domain**, given continuations that do from a state of the domain. -/
theorem interp_ed [Labels] [AddressSize] {w : Width} (op : Operation w) (hw : op.wideOk = true)
    (p : Std.Rco Int64) {D : DataMem} (s : MachineData) (hs : SameDom D s) {next : MachineData → Effects}
    {jmp : Int64 → MachineData → Effects} (hn : ∀ s, SameDom D s → ED D (next s))
    (hj : ∀ pc s, SameDom D s → ED D (jmp pc s)) : ED D (op.interp p s next jmp) := by
  cases w <;> cases op
  all_goals first | exact imul_ed _ _ _ hw p s hs hn | skip
  all_goals try simp only [Operation.wideOk, Operation.narrowOk, Bool.false_eq_true] at hw
  all_goals try (obtain ⟨_, rfl⟩ := noMem_eq hw)
  all_goals (simp only [Operation.interp, MachineData.pendingSyscall, Reg.interp] <;> edm)

set_option maxRecDepth 4096 in
/-- **A vector operation of the fragment keeps the private memory's
domain**, given a continuation that does from a state of the domain. -/
theorem avxInterp_ed [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w) (hw : op.wideOk = true)
    (p : Std.Rco Int64) {D : DataMem} (s : MachineData) (hs : SameDom D s) {next : MachineData → Effects}
    (hn : ∀ s, SameDom D s → ED D (next s)) : ED D (op.interp p s next) := by
  cases op
  all_goals try simp only [AvxOperation.wideOk, Bool.false_eq_true] at hw
  all_goals try (obtain ⟨_, rfl⟩ := avxNoMem_eq hw)
  all_goals (simp only [AvxOperation.interp, MachineData.setAvx, MachineData.setAvxLegacy] <;> edm)

theorem directive_ed [Labels] {d : Directive} (hd : d.wideOk = true) {D : DataMem} (s : MachineData)
    (hs : SameDom D s) (p : Std.Rco Int64) {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, SameDom D s → ED D (next s)) (hj : ∀ pc s, SameDom D s → ED D (jmp pc s)) :
    ED D (d.interp s p next jmp) := by
  cases d with
  | label => exact hn s hs
  | instr i =>
    refine ED.require_exec_access fun _ => ?_
    cases i with
    | regular a _ op => letI : AddressSize := .mk a; exact interp_ed op hd p s hs hn hj
    | avx a _ op => letI : AddressSize := .mk a; exact avxInterp_ed op hd p s hs hn
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

/-- A leaf of an access is a leaf of its continuation. -/
theorem access_leaf {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ} {x : σ}
    (hl : TreeLeaf (EvTree.access ds a n k) x) : ∃ l, TreeLeaf (k l) x := by
  unfold EvTree.access at hl
  split at hl
  · exact ⟨_, hl⟩
  · exact hl.elim

/-- A leaf of a non-atomic vector load is a leaf of its continuation. -/
theorem loadPieces_leaf {σ : Type} {ds : Decls} {dmem : DataMem} :
    ∀ {addr : BitVec 64} {n : Nat} {k : List UInt8 → EvTree σ} {x : σ},
      TreeLeaf (X64.loadPieces ds dmem addr n k) x → ∃ bs, TreeLeaf (k bs) x
  | _, 0, _, _, hl => ⟨_, hl⟩
  | _, _ + 1, _, _, hl => by
    simp only [X64.loadPieces] at hl
    split at hl
    · obtain ⟨_, h⟩ := loadPieces_leaf hl; exact ⟨_, h⟩
    · split at hl
      · exact hl.elim
      · obtain ⟨_, _, hl⟩ := access_leaf hl
        obtain ⟨_, h⟩ := loadPieces_leaf hl; exact ⟨_, h⟩

/-- **`toEv` of domain-keeping effects**: every leaf maps exactly `D`. -/
theorem toEv_leaf {ds : Decls} {D : DataMem} {e : Effects} (h : ED D e) {x : MachineState}
    (hl : TreeLeaf (X64.toEv ds e) x) : SameDom D x.1 := by
  induction h with
  | done h0 => simp only [X64.toEv, TreeLeaf] at hl; subst hl; exact h0
  | unimplemented | gp_unaligned | syscall => simp only [X64.toEv, TreeLeaf] at hl
  | nonmem_load _ ih | sync_load _ ih =>
    simp only [X64.toEv] at hl; obtain ⟨_, _, hl⟩ := access_leaf hl; exact ih _ hl
  | nonmem_store _ ih =>
    simp only [X64.toEv] at hl; obtain ⟨_, _, hl⟩ := access_leaf hl; exact ih hl
  | sync_store _ ih | rmw _ ih =>
    simp only [X64.toEv] at hl; obtain ⟨_, _, hl⟩ := access_leaf hl; exact ih _ hl
  | fence _ ih => simp only [X64.toEv, TreeLeaf] at hl; obtain ⟨_, hl⟩ := hl; exact ih _ hl
  | require_read_access _ ih | require_write_access _ ih | require_exec_access _ ih
  | require_read_access_avx _ ih | require_write_access_avx _ ih =>
    simp only [X64.toEv] at hl; exact ih _ hl
  | @undefined α inst ret _ ih =>
    cases inst <;> simp only [X64.toEv, TreeLeaf] at hl
    obtain ⟨_, hl⟩ := hl; exact ih _ hl
  | nonmem_load_avx _ ih =>
    simp only [X64.toEv] at hl
    split at hl
    · obtain ⟨_, _, hl⟩ := access_leaf hl; exact ih _ hl
    · obtain ⟨_, hl⟩ := loadPieces_leaf hl; exact ih _ hl

/-- **The x86-64 semantics on the fragment keeps the private memory's
domain**: every leaf maps exactly the addresses the state maps. -/
theorem exec_dom {s : X64.State} (hs : WideSt s) {t : EvTree X64.State} (h : X64.exec s = some t)
    {s' : X64.State} (hl : TreeLeaf t s') (k : BitVec 64) : k ∈ s'.st.1.dmem ↔ k ∈ s.st.1.dmem := by
  unfold X64.exec at h
  split at h
  · cases h
  · cases h
    obtain ⟨x, hx, rfl⟩ := leaf_of_map _ hl
    exact toEv_leaf (step_ed hs.2 _) hx k

/-- **The x86-64 instance of `Kernel.DomHyps`** on the fragment: every leaf
keeps `WideSt` and the private memory's domain; the ABI's return,
thread-pointer change, `setDmem` and `skip` change the machine state only,
keeping `WideSt`; `ret` and `setTp` keep the private memory and the child
of a `clone` has none. -/
theorem domHyps : Kernel.DomHyps Scc.Sem.X64.abi WideSt where
  exec _ _ _ hs h hl := ⟨exec_wideInv _ _ _ hs h hl, exec_dom hs h hl⟩
  ret _ _ hs := ⟨hs, rfl⟩
  setTp _ _ hs := ⟨hs, rfl⟩
  child _ _ _ hs := ⟨hs, rfl⟩
  setDmem _ _ hs := hs
  skip _ hs := hs

end Scc.Cert.DomX64
