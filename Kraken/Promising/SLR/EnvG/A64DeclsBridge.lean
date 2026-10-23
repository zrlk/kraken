/-
**Declarations as a fault restriction, AArch64: the bridge**. The AArch64
analogue of the x64 vector proofs'
`EnvG/X64VecDeclsFault.lean` (its ISA-neutral half is
`EnvG/A64DeclsCommon.lean`).

`Kraken.Promising.AArch64.toEv ds` builds every access through
`EvTree.access ds`, so with **strict sized** declarations (`Decls.StrictSized`:
the `.kl` runner's declarations of a typed header) a thread's tree is its
`decls = {}` tree re-resolved against `ds` (`EvTree.reresolve`): an access at
a declared footprint, or at an undeclared address, is unchanged; a mixed-size
access is a fault. One exception: a **pair** effect (`sync_load_pair` /
`sync_store_pair`, from `LDXP`/`STXP` with both halves shared) is *one*
`2w`-byte access when the pair is a declared `2w`-byte location
(`pairIsOneLoc ds addr w`) and two `w`-byte accesses otherwise; with `ds = {}`
it is always two. So the node-by-node agreement needs the side condition
that no pair node of the effect tree merges under `ds`:

- `Effects.NoPairMerge ds eff`: every `sync_load_pair`/`sync_store_pair`
  node of `eff` has `pairIsOneLoc ds addr w = false`; `Effects.NoPairs eff`:
  `eff` has no pair node at all (`NoPairMerge` for every `ds`);
- the **static form** `Executable.noPairs e` (`Program.noPairs`,
  `Operation.noPairs`: no `LDXP`/`STXP`; `LDP`/`STP` are two plain accesses
  under `isa`, and `CASP`'s `caspTree` resolves each half through
  `EvTree.access ds`), decided by `decide` after `Layout.apply_noPairs`;
  `directive_noPairs`: the tree of a directive that passes the check has no
  pair node. No example in `Kraken/Examples/LockFree/AArch64` uses
  `LDXP`/`STXP`;
- `toEv_reresolve`: `(toEv {} eff).reresolve ds = toEv ds eff` under
  `NoPairMerge ds eff`;
- `exec_reresolve`: for a thread state whose executable passes the check,
  `isa.exec st = (isa.exec st.noDecls).map (·.reresolve st.decls |>.map (withDecls st.decls))`
  (`exec`'s one `toEv s.decls` site);
- the run bridges `exec_treeJLive_of_reresolve`, `exec_treeJ_of_reresolve`:
  any `decls = {}` run lemma, applied at `st.noDecls` to
  `(J.comap (withDecls st.decls)).reresolve st.decls`, gives the run at
  `decls = st.decls`.

As on x64, the restriction says nothing about faults (a fault is a `W` law):
the no-fault side of a program with mixed-size accesses is not covered.
-/
import Kraken.Promising.SLR.EnvG.A64DeclsCommon
import Kraken.Promising.SLR.EnvG.A64MaskCore
import Kraken.AArch64.Parser

open Kraken

/-! ## The static check: no `LDXP`/`STXP` -/

/-- No exclusive pair: `LDXP`/`LDAXP` and `STXP`/`STLXP` fail the check,
every other operation passes. -/
def Operation.noPairs {w : RegWidth} : Operation w → Bool
  | .LDXP .. => false
  | .STXP .. => false
  | _ => true

/-- `Operation.noPairs` of an instruction; labels and data pass. -/
def Directive.noPairs : Directive → Bool
  | .instr i => i.operation.noPairs
  | .label _ => true
  | .byteArray _ => true

/-- **The static no-pair check** of a program: every directive passes. -/
def Program.noPairs (p : Program) : Bool := p.all Directive.noPairs

/-- The check on a laid-out program. -/
def Kraken.Executable.noPairs (e : Kraken.Executable Directive) : Bool := e.2.all (·.1.noPairs)

private theorem mapIdx_noPairs :
    ∀ (p : Program) (sz : Nat → Nat), (p.mapIdx fun i d => (d, sz i)).all (·.1.noPairs) = p.all Directive.noPairs
  | [], _ => rfl
  | d :: p, sz => by
    rw [List.mapIdx_cons, List.all_cons, List.all_cons, mapIdx_noPairs p (fun i => sz (i + 1))]

/-- Laying out does not change the check. -/
theorem Layout.apply_noPairs (l : Kraken.Layout Directive) (p : Program) :
    (l p).noPairs = p.noPairs :=
  mapIdx_noPairs p l.size

/-! ## Pair nodes of an effect tree -/

/-- **No pair node merges under `ds`**: every `sync_load_pair` /
`sync_store_pair` node has `pairIsOneLoc ds addr w = false`, so `toEv ds`
performs it as two accesses, as `toEv {}` does. -/
def Effects.NoPairMerge (ds : Kraken.Promising.Decls) : Effects → Prop
  | .done _ => True
  | .unimplemented _ => True
  | .syscall .. => True
  | .unaligned_sp _ => True
  | .nonmem_load _ _ _ ret => ∀ v d, (ret v d).NoPairMerge ds
  | .nonmem_store _ _ _ ret => ∀ d, (ret d).NoPairMerge ds
  | @Effects.undefined _ _ ret => ∀ a, (ret a).NoPairMerge ds
  | .require_read_access _ _ ok => (ok ()).NoPairMerge ds
  | .require_write_access _ _ ok => (ok ()).NoPairMerge ds
  | .require_exec_access _ ok => (ok ()).NoPairMerge ds
  | .sync_load _ _ _ _ _ ret => ∀ v d, (ret v d).NoPairMerge ds
  | .sync_store _ _ _ _ _ ret => ∀ b d, (ret b d).NoPairMerge ds
  | .rmw _ _ _ _ _ _ ret => ∀ v d, (ret v d).NoPairMerge ds
  | .fence _ ok => (ok ()).NoPairMerge ds
  | .sync_load_pair _ _ _ addr w ret =>
    Kraken.Promising.AArch64.pairIsOneLoc ds addr w = false ∧ ∀ v₁ v₂ d, (ret v₁ v₂ d).NoPairMerge ds
  | @Effects.sync_store_pair _ _ _ addr w _ _ ret =>
    Kraken.Promising.AArch64.pairIsOneLoc ds addr w = false ∧ ∀ b d, (ret b d).NoPairMerge ds
  | .rmw_pair _ _ _ _ _ _ _ ret => ∀ o₁ o₂ d, (ret o₁ o₂ d).NoPairMerge ds

/-- **No pair node at all** (`sync_load_pair`/`sync_store_pair`): the
static form, independent of the declarations. -/
def Effects.NoPairs : Effects → Prop
  | .done _ => True
  | .unimplemented _ => True
  | .syscall .. => True
  | .unaligned_sp _ => True
  | .nonmem_load _ _ _ ret => ∀ v d, (ret v d).NoPairs
  | .nonmem_store _ _ _ ret => ∀ d, (ret d).NoPairs
  | @Effects.undefined _ _ ret => ∀ a, (ret a).NoPairs
  | .require_read_access _ _ ok => (ok ()).NoPairs
  | .require_write_access _ _ ok => (ok ()).NoPairs
  | .require_exec_access _ ok => (ok ()).NoPairs
  | .sync_load _ _ _ _ _ ret => ∀ v d, (ret v d).NoPairs
  | .sync_store _ _ _ _ _ ret => ∀ b d, (ret b d).NoPairs
  | .rmw _ _ _ _ _ _ ret => ∀ v d, (ret v d).NoPairs
  | .fence _ ok => (ok ()).NoPairs
  | .sync_load_pair .. => False
  | .sync_store_pair .. => False
  | .rmw_pair _ _ _ _ _ _ _ ret => ∀ o₁ o₂ d, (ret o₁ o₂ d).NoPairs

/-- A tree with no pair node merges none, under any declarations. -/
theorem Effects.NoPairMerge.of_noPairs (ds : Kraken.Promising.Decls) :
    ∀ eff : Effects, eff.NoPairs → eff.NoPairMerge ds := by
  intro eff
  induction eff with
  | done _ => exact id
  | unimplemented _ => exact id
  | syscall => exact id
  | unaligned_sp _ => exact id
  | nonmem_load _ _ _ _ ih => exact fun h v d => ih v d (h v d)
  | nonmem_store _ _ _ _ ih => exact fun h d => ih d (h d)
  | undefined _ ih => exact fun h a => ih a (h a)
  | require_read_access _ _ _ ih => exact fun h => ih () h
  | require_write_access _ _ _ ih => exact fun h => ih () h
  | require_exec_access _ _ ih => exact fun h => ih () h
  | sync_load _ _ _ _ _ _ ih => exact fun h v d => ih v d (h v d)
  | sync_store _ _ _ _ _ _ ih => exact fun h b d => ih b d (h b d)
  | rmw _ _ _ _ _ _ _ ih => exact fun h v d => ih v d (h v d)
  | fence _ _ ih => exact fun h => ih () h
  | sync_load_pair => exact fun h => h.elim
  | sync_store_pair => exact fun h => h.elim
  | rmw_pair _ _ _ _ _ _ _ _ ih => exact fun h o₁ o₂ d => ih o₁ o₂ d (h o₁ o₂ d)

namespace Kraken.Promising.AArch64.EnvG

open Kraken.Promising Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
  Kraken.Promising.AArch64.EnvSpike

/-! ## No pair node, per primitive (the pattern of `A64Live.lean`) -/

section NoPairs

theorem load_noPairs {s : MachineData} {addr : BitVec 64} {w : MemWidth} {k : w.type → MachineData → Effects}
    (hk : ∀ v s, (k v s).NoPairs) : (MachineData.load s addr w k).NoPairs := by
  unfold MachineData.load
  simp only [Effects.NoPairs]
  cases Mem.loadInt s.dmem addr w.bytes
  · exact fun _ _ => hk _ _
  · exact hk _ _

theorem loadK_noPairs {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {k : w.type → MachineData → Effects} (hk : ∀ v s, (k v s).NoPairs) :
    (MachineData.loadK s lk xcl addr w k).NoPairs := by
  unfold MachineData.loadK
  simp only [Effects.NoPairs]
  cases Mem.loadInt s.dmem addr w.bytes
  · exact fun _ _ => hk _ _
  · exact hk _ _

theorem store_noPairs {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {k : MachineData → Effects} (hk : ∀ s, (k s).NoPairs) : (MachineData.store s addr v k).NoPairs := by
  unfold MachineData.store
  simp only [Effects.NoPairs]
  cases Mem.loadInt s.dmem addr w.bytes
  · exact fun _ => hk _
  · exact hk _

theorem storeK_noPairs {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {k : Bool → MachineData → Effects} (hk : ∀ b s, (k b s).NoPairs) :
    (MachineData.storeK s sk xcl addr v k).NoPairs := by
  unfold MachineData.storeK
  simp only [Effects.NoPairs]
  cases Mem.loadInt s.dmem addr w.bytes
  · exact fun _ _ => hk _ _
  · simp only
    cases xcl
    · exact hk _ _
    · simp only [ite_true, Effects.NoPairs]
      intro b
      split <;> exact hk _ _

theorem rmwK_noPairs {s : MachineData} {rk : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {k : w.type → MachineData → Effects} (hk : ∀ v s, (k v s).NoPairs) :
    (MachineData.rmwK s rk nr addr w op k).NoPairs := by
  unfold MachineData.rmwK
  simp only [Effects.NoPairs]
  cases Mem.loadInt s.dmem addr w.bytes
  · exact fun _ _ => hk _ _
  · simp only
    split <;> exact hk _ _

/-- `CASP` is no pair node: `rmw_pair` (both halves shared) or a single
`rmw`. -/
theorem rmwPairK_noPairs {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {k : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s, (k v₁ v₂ s).NoPairs) : (MachineData.rmwPairK s rk addr c₁ c₂ n₁ n₂ k).NoPairs := by
  unfold MachineData.rmwPairK
  simp only [Effects.NoPairs]
  cases Mem.loadInt s.dmem addr w.bytes <;> cases Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [Effects.NoPairs]
  · exact fun _ _ _ => hk _ _ _
  · intro _ _; split <;> exact hk _ _ _
  · intro _ _; split <;> exact hk _ _ _
  · split <;> exact hk _ _ _

/-! ### Per addressing form -/

theorem AddrExpr.checkSPAlignment_noPairs {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    (hk : (ok ()).NoPairs) : (a.checkSPAlignment s ok).NoPairs := by
  unfold AddrExpr.checkSPAlignment
  generalize a.base = b
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk
    | SP =>
      simp only
      split
      · simp only [Effects.NoPairs]
      · exact hk

theorem UnscaledAddrExpr.checkSPAlignment_noPairs {a : UnscaledAddrExpr} {s : MachineData}
    {ok : Unit → Effects} (hk : (ok ()).NoPairs) : (a.checkSPAlignment s ok).NoPairs := by
  unfold UnscaledAddrExpr.checkSPAlignment
  generalize a.base = b
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk
    | SP =>
      simp only
      split
      · simp only [Effects.NoPairs]
      · exact hk

theorem interpBase_noPairs {base : RegOrSp .W64} {s : MachineData} {ok : BitVec 64 → Effects}
    (hk : ∀ a, (ok a).NoPairs) : (base.interpBase s ok).NoPairs := by
  unfold RegOrSp.interpBase
  cases base with
  | low x w' =>
    cases x with
    | reg x => exact hk _
    | SP =>
      simp only
      split
      · simp only [Effects.NoPairs]
      · exact hk _

theorem AddrExpr.interpLoad_noPairs [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64} {s : MachineData}
    {k : w.type → MachineData → Effects} (hk : ∀ v s, (k v s).NoPairs) : (a.interpLoad s p k).NoPairs := by
  unfold AddrExpr.interpLoad
  exact AddrExpr.checkSPAlignment_noPairs (load_noPairs hk)

theorem AddrExpr.interpStore_noPairs [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64}
    {s : MachineData} {v : w.type} {k : MachineData → Effects} (hk : ∀ s, (k s).NoPairs) :
    (a.interpStore s p v k).NoPairs := by
  unfold AddrExpr.interpStore
  exact AddrExpr.checkSPAlignment_noPairs (store_noPairs hk)

theorem UnscaledAddrExpr.interpLoad_noPairs [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {k : w.type → MachineData → Effects}
    (hk : ∀ v s, (k v s).NoPairs) : (a.interpLoad s p k).NoPairs := by
  unfold UnscaledAddrExpr.interpLoad
  exact UnscaledAddrExpr.checkSPAlignment_noPairs (load_noPairs hk)

theorem UnscaledAddrExpr.interpStore_noPairs [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {v : w.type} {k : MachineData → Effects}
    (hk : ∀ s, (k s).NoPairs) : (a.interpStore s p v k).NoPairs := by
  unfold UnscaledAddrExpr.interpStore
  exact UnscaledAddrExpr.checkSPAlignment_noPairs (store_noPairs hk)

theorem AddrOrLit.interpLoad_noPairs [Labels] {w : MemWidth} {a : AddrOrLit} {p : Std.Rco Int64}
    {s : MachineData} {k : w.type → MachineData → Effects} (hk : ∀ v s, (k v s).NoPairs) :
    (a.interpLoad s p k).NoPairs := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_noPairs hk
  | lit l =>
    cases l with
    | addr a => exact load_noPairs hk
    | pool q => exact hk _ _

/-! ### Per instruction -/

set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK MachineData.storeK
  MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK AddrExpr.interpLoad
  AddrExpr.interpStore UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore AddrOrLit.interpLoad AddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- `live_search` (`A64Live.lean`) for the no-pair property: the primitive
lemmas above; the check `hop` closes `LDXP`/`STXP`. -/
local macro "nopairs_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Operation.noPairs, MachineData.setRegOrZr, MachineData.setRegOrSp,
      AddrExpr.eval_mk, Bool.false_eq_true] at hop ⊢ <;>
    repeat' first
      | exact hk _
      | exact hj _ _
      | exact trivial
      | (simp only [Effects.NoPairs]; done)
      | refine AddrOrLit.interpLoad_noPairs (fun v s => ?_)
      | refine AddrExpr.interpLoad_noPairs (fun v s => ?_)
      | refine UnscaledAddrExpr.interpLoad_noPairs (fun v s => ?_)
      | refine AddrExpr.interpStore_noPairs (fun s => ?_)
      | refine UnscaledAddrExpr.interpStore_noPairs (fun s => ?_)
      | refine AddrExpr.checkSPAlignment_noPairs ?_
      | refine load_noPairs (fun v s => ?_)
      | refine store_noPairs (fun s => ?_)
      | refine loadK_noPairs (fun v s => ?_)
      | refine storeK_noPairs (fun b s => ?_)
      | refine rmwK_noPairs (fun v s => ?_)
      | refine rmwPairK_noPairs (fun v₁ v₂ s => ?_)
      | refine interpBase_noPairs (fun a => ?_)
      | (simp only [Effects.NoPairs]; intro _)
      | (split <;> rename_i hcond <;> try simp only [hcond, ite_true, ite_false, Bool.false_eq_true])
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, AddrExpr.eval_mk]))

/-- **One operation's tree has no pair node** if the operation passes the
check and its continuations' trees have none. -/
theorem operation_noPairs [Labels] {w : RegWidth} (op : Operation w) (p : Std.Rco Int64) {s : MachineData}
    {k : MachineData → Effects} {j : Int64 → MachineData → Effects} (hop : op.noPairs = true)
    (hk : ∀ s, (k s).NoPairs) (hj : ∀ pc s, (j pc s).NoPairs) : (Operation.interp op p s k j).NoPairs := by
  cases op <;> nopairs_search

theorem directive_noPairs [Labels] (dir : Directive) (p : Std.Rco Int64) {s : MachineData}
    {k : MachineData → Effects} {j : Int64 → MachineData → Effects} (hd : dir.noPairs = true)
    (hk : ∀ s, (k s).NoPairs) (hj : ∀ pc s, (j pc s).NoPairs) : (dir.interp s p k j).NoPairs := by
  cases dir with
  | instr i =>
    show (i.interp s p k j).NoPairs
    unfold Instr.interp
    exact operation_noPairs _ _ hd hk hj
  | label l => exact hk _
  | byteArray b => simp only [Directive.interp, Effects.NoPairs]

end NoPairs

/-- On an executable that passes the check, the instruction `codeAt` finds
passes it. -/
theorem noPairs_of_mem_codeAt {e : Kraken.Executable Directive} (hp : e.noPairs = true) {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) :
    d.noPairs = true :=
  List.all_eq_true.mp hp _ (mem_of_codeAt h)

/-- **The step at a pc whose instruction passes the check has no pair
node.** -/
theorem step_noPairs_of_codeAt {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)} (hcode : e.codeAt pc = (d, z) :: rest)
    (hd : d.noPairs = true) (s : MachineData) :
    (Executable.step e (s, pc) fun s' => .done s').NoPairs := by
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  unfold Executable.step
  letI := Executable.labels e
  simp only
  rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
  simp only [Directives.interp]
  exact directive_noPairs d _ hd (fun _ => trivial) (fun _ _ => trivial)

/-! ## The bridge -/

/-- `caspTree` resolves each half through `EvTree.access ds`: re-resolving
the `decls = {}` tree gives the tree at `ds`. -/
theorem caspTree_reresolve {σ : Type} (ds : Decls) (k : RmwKind) (addr : BitVec 64) {w : MemWidth}
    (c₁ c₂ n₁ n₂ : w.type) (ret : w.type → w.type → EvTree σ) :
    (caspTree {} k addr c₁ c₂ n₁ n₂ ret).reresolve ds =
      caspTree ds k addr c₁ c₂ n₁ n₂ fun o₁ o₂ => (ret o₁ o₂).reresolve ds := by
  unfold caspTree
  simp only [EvTree.access_empty, EvTree.reresolve]
  congr 1; funext succ; congr 1; funext rev
  have hguard : ∀ (b : Bool) (t : EvTree σ),
      (if b = true then t else EvTree.choose 0 nofun).reresolve ds =
        if b = true then t.reresolve ds else EvTree.choose 0 nofun := by
    intro b t
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, EvTree.reresolve]
      congr 1; funext i; exact i.elim0
    · rfl
  split <;> simp only [EvTree.reresolve] <;>
    (congr 1; funext l₁; congr 1; funext v₁; congr 1; funext l₂; congr 1; funext v₂; exact hguard _ _)

/-- With no declarations no pair is one location. -/
theorem pairIsOneLoc_empty (addr : BitVec 64) (w : MemWidth) : pairIsOneLoc {} addr w = false := rfl

/-- **Every effect tree with no merging pair translates under `ds` as its
translation under no declarations, re-resolved against `ds`.** -/
theorem toEv_reresolve (ds : Decls) : ∀ eff : Effects, eff.NoPairMerge ds →
    (toEv {} eff).reresolve ds = toEv ds eff := by
  intro eff
  induction eff with
  | done _ => exact fun _ => rfl
  | unimplemented _ => exact fun _ => rfl
  | syscall => exact fun _ => rfl
  | unaligned_sp _ => exact fun _ => rfl
  | nonmem_load dmem addr w ret ih =>
    intro h
    simp only [toEv, EvTree.access_empty, EvTree.reresolve]
    congr 1; funext l; congr 1; funext v; exact ih _ _ (h _ _)
  | nonmem_store dmem addr v ret ih =>
    intro h
    simp only [toEv, EvTree.access_empty, EvTree.reresolve]
    congr 1; funext l; congr 1; funext b; exact ih _ (h _)
  | undefined ret ih =>
    intro h
    rename_i inst
    cases inst <;> simp only [toEv, EvTree.reresolve]
    congr 1; funext i; exact ih _ (h _)
  | require_read_access _ _ ok ih => exact fun h => ih () h
  | require_write_access _ _ ok ih => exact fun h => ih () h
  | require_exec_access _ ok ih => exact fun h => ih () h
  | sync_load k xcl dmem addr w ret ih =>
    intro h
    simp only [toEv, EvTree.access_empty, EvTree.reresolve]
    congr 1; funext l; congr 1; funext v; exact ih _ _ (h _ _)
  | sync_store k xcl dmem addr v ret ih =>
    intro h
    simp only [toEv, EvTree.access_empty, EvTree.reresolve]
    congr 1; funext l; congr 1; funext b; exact ih _ _ (h _ _)
  | rmw k nr dmem addr w op ret ih =>
    intro h
    simp only [toEv, EvTree.access_empty, EvTree.reresolve]
    congr 1; funext l; congr 1; funext v; exact ih _ _ (h _ _)
  | fence k ok ih =>
    intro h
    simp only [toEv, EvTree.reresolve]
    congr 1; funext u; exact ih () h
  | sync_load_pair k xcl dmem addr w ret ih =>
    intro ⟨hp, h⟩
    simp only [toEv, hp, pairIsOneLoc_empty, Bool.false_eq_true, ↓reduceIte, EvTree.access_empty,
      EvTree.reresolve]
    congr 1; funext l₁; congr 1; funext v₁; congr 1; funext l₂; congr 1; funext v₂
    exact ih _ _ _ (h _ _ _)
  | sync_store_pair k xcl dmem addr v₁ v₂ ret ih =>
    intro ⟨hp, h⟩
    simp only [toEv, hp, pairIsOneLoc_empty, Bool.false_eq_true, ↓reduceIte, EvTree.access_empty,
      EvTree.reresolve]
    congr 1; funext l₁; congr 1; funext ok
    cases ok
    · exact ih _ _ (h _ _)
    · simp only [↓reduceIte, EvTree.reresolve]
      congr 1; funext l₂; congr 1; funext b; exact ih _ _ (h _ _)
  | rmw_pair k dmem addr c₁ c₂ n₁ n₂ ret ih =>
    intro h
    simp only [toEv, caspTree_reresolve]
    congr 1; funext o₁ o₂; exact ih _ _ _ (h _ _ _)

/-- The thread state with its declarations dropped. -/
abbrev _root_.Kraken.Promising.AArch64.State.noDecls (st : State) : State := { st with decls := {} }

/-- Put the declarations `ds` back. -/
abbrev _root_.Kraken.Promising.AArch64.State.withDecls (ds : Decls) (st : State) : State := { st with decls := ds }

theorem _root_.Kraken.Promising.AArch64.State.withDecls_noDecls_st (st : State) (m : MachineState) :
    State.withDecls st.decls { st.noDecls with st := m } = { st with st := m } := by
  cases st; rfl

/-- A thread state's directive is the first cell of its code. -/
theorem codeAt_of_directive {st : State} {d : Directive} (hd : st.directive = some d) :
    ∃ z rest, Kraken.Executable.codeAt st.exe st.st.2 = (d, z) :: rest := by
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  unfold State.directive at hd
  simp only at hd ⊢
  rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
    unfold Kraken.Executable.codeAt
    congr 1] at hd
  cases hc : Kraken.Executable.codeAt exe pc with
  | nil => rw [hc] at hd; cases hd
  | cons c rest =>
    rw [hc] at hd
    simp only [List.head?_cons, Option.map_some, Option.some.injEq] at hd
    exact ⟨c.2, rest, by rw [← hd]⟩

/-- **The bridge, for every thread state whose executable passes the
no-pair check**: the tree is the tree of the state with no declarations,
re-resolved against the declarations, with the declarations put back in the
leaves. -/
theorem exec_reresolve (st : State) [Kraken.Executable.ValidLayout st.exe] (hnp : Kraken.Executable.noPairs st.exe = true) :
    isa.exec st = (isa.exec st.noDecls).map
      (fun t => (t.reresolve st.decls).map (State.withDecls st.decls)) := by
  show exec st = (exec st.noDecls).map _
  have hdir : st.noDecls.directive = st.directive := rfl
  unfold exec
  rw [hdir]
  split
  · rfl
  · next hc =>
    simp only [Bool.or_eq_true, beq_iff_eq, not_or, Option.isNone_iff_eq_none] at hc
    obtain ⟨d, hd⟩ := Option.ne_none_iff_exists'.mp hc.2
    obtain ⟨z, rest, hcode⟩ := codeAt_of_directive hd
    have hnp' := step_noPairs_of_codeAt hcode (noPairs_of_mem_codeAt hnp hcode) st.st.1
    rw [← toEv_reresolve st.decls _ (Effects.NoPairMerge.of_noPairs st.decls _ hnp')]
    show some _ = some _
    congr 1
    show _ = EvTree.map (State.withDecls st.decls) (EvTree.reresolve st.decls
      (EvTree.map (fun m => ({ st with st := m, decls := {} } : State))
        (toEv {} (_root_.Executable.step st.exe st.st fun s' => .done s'))))
    rw [EvTree.map_reresolve (σ := State) (State.withDecls st.decls), evTree_map_map, EvTree.map_reresolve]
    rfl

/-- **A `decls = {}` live run gives the run with strict sized
declarations**: apply the run lemma at `st.noDecls` to
`(J.comap (withDecls st.decls)).reresolve st.decls`. -/
theorem exec_treeJLive_of_reresolve {E : SharedEnv} (J : TreeJLive E State) {st : State} {g : E.State}
    [Kraken.Executable.ValidLayout st.exe] (hnp : Kraken.Executable.noPairs st.exe = true) (hs : st.decls.StrictSized)
    (h₀ : ∀ tree₀, isa.exec st.noDecls = some tree₀ →
      ((J.comap (State.withDecls st.decls)).reresolve st.decls hs).W tree₀ g) :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  rw [exec_reresolve st hnp] at htree
  obtain ⟨tree₀, h, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact h₀ tree₀ h

/-- **A `decls = {}` run gives the run with strict sized declarations**
(`exec_treeJLive_of_reresolve` for `TreeJ`). -/
theorem exec_treeJ_of_reresolve {E : SharedEnv} (J : TreeJ E State) {st : State} {g : E.State}
    [Kraken.Executable.ValidLayout st.exe] (hnp : Kraken.Executable.noPairs st.exe = true) (hs : st.decls.StrictSized)
    (h₀ : ∀ tree₀, isa.exec st.noDecls = some tree₀ →
      ((J.comap (State.withDecls st.decls)).reresolve st.decls hs).W tree₀ g) :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  intro tree htree
  rw [exec_reresolve st hnp] at htree
  obtain ⟨tree₀, h, rfl⟩ := Option.map_eq_some_iff.mp htree
  exact h₀ tree₀ h

/-- **One instruction from a `Safely` judgment, with strict sized
declarations, any tree judgment**: every tree of a thread running
`e` (no pair accesses) to `endPc` with declarations `ds`, at a `Safely`
judgment in `E`, satisfies a tree judgment `J` of `E` whose leaf condition
holds at the same judgment (`exec_treeJ_of_reresolve` at the thread with
its declarations dropped). `relPureSpec_stepD` and
`TicketLock.dispSpec_stepD` are its instances. -/
theorem exec_treeJ_of_safelyD {E : SharedEnv} (J : TreeJ E State) {ds : Decls} (hsz : ds.StrictSized)
    {e : Kraken.Executable Directive} [hv : Kraken.Executable.ValidLayout e]
    (hnp : Kraken.Executable.noPairs e = true) {endPc : Int64} {post : MachineState × E.State → Prop}
    (hpost : ∀ y, post y → y.1.2 = endPc)
    (hJ : ∀ s g', s.exe = e → s.endPc = endPc → s.decls = ds → Safely (e.instrStepEnv E) post (s.st, g') →
      J.Post s g')
    {st : State} {g : E.State} (he : st.exe = e) (hend : st.endPc = endPc) (hds : st.decls = ds)
    (hs : Safely (e.instrStepEnv E) post (st.st, g)) (tree : EvTree State) (hex : isa.exec st = some tree) :
    J.W tree g := by
  rcases hs.unfold with hP | ⟨R, hT, hR⟩
  · have hpc : st.st.2 = endPc := hpost _ hP
    have hnone : isa.exec st = none := by
      show exec st = none
      simp [exec, hpc, hend]
    rw [hnone] at hex
    cases hex
  · subst hds
    haveI : Kraken.Executable.ValidLayout st.exe := he ▸ hv
    refine exec_treeJ_of_reresolve J (g := g) (he ▸ hnp) hsz (fun tree₀ h₀ => ?_) tree hex
    exact EnvSpike.exec_treeJ_of_instrStepEnv ((J.comap (State.withDecls st.decls)).reresolve st.decls hsz)
      (st := st.noDecls) he rfl hT
      (fun m g' hm => by
        show J.Post (State.withDecls st.decls { st.noDecls with st := m }) g'
        rw [State.withDecls_noDecls_st]
        exact hJ _ _ he hend rfl (hR _ hm)) tree₀ h₀

/-- The `Post` of the re-resolved comapped judgment is `J.Post` at the
leaf with the declarations put back. -/
theorem reresolve_comap_post {E : SharedEnv} (J : TreeJLive E State) (ds : Decls) (hs : ds.StrictSized)
    (s : State) (g : E.State) :
    ((J.comap (State.withDecls ds)).reresolve ds hs).Post s g = J.Post (State.withDecls ds s) g := rfl

end Kraken.Promising.AArch64.EnvG

/-! ## Tests -/

-- No example of the AArch64 lock-free corpus uses `LDXP`/`STXP`.
/-- info: true -/
#guard_msgs in
#eval Program.noPairs (parseAArch64("
  LDR X0,[X1]
  STLR X2,[X3]
  CASAL X4,X5,[X6]
  LDP X7,X8,[X9]
  CASP X10,X11,X12,X13,[X14]
"))

/-- info: false -/
#guard_msgs in
#eval Program.noPairs (parseAArch64("
  LDXP X7,X8,[X9]
"))

#print axioms Kraken.Promising.AArch64.EnvG.exec_reresolve
