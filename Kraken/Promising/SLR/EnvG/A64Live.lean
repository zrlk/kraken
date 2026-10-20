/-
EnvG, live trees (AArch64 part): the static `RmwLive` check and the live link step.

- `Operation.rmwLive`, `Directive.rmwLive`, `Program.rmwLive`,
  `Executable.rmwLive`: decidable (`Bool`) checks that no `SWP*`/`LD<op>*`
  has the zero register as destination `Rt` and no `CAS*` has the zero
  register as comparand `Rs` — exactly the three `rmwK` call sites of the
  interpreter that pass `rs.isZr`/`rt.isZr` as `noRet`
  (`Kraken/AArch64/Semantics.lean`, `Operation.interp`); `CASP`
  (`rmwPairK`, `caspTree`) always emits `noRet = false`.
- `rmwLive_of_codeAt`: at a pc of an executable that passes the check, with
  no declarations, every instruction tree of the thread is `RmwLive`.
- `exec_treeJLive_of_instrStepEnv`: `EnvSpikeA64.exec_treeJ_of_instrStepEnv`
  for a `TreeJLive`, given that the trees are live;
  `exec_treeJLive_of_instrStepEnv'` derives liveness from the static check.

Phase 1: single-access trees; the lemmas here hold
for every tree, the restriction is in how they are used.
-/
import Kraken.Promising.SLR.EnvSpikeA64
import Kraken.Promising.SLR.EnvG.Live

open Kraken

/-! ## The static check -/

/-- No `noRet` RMW: the destination of `SWP`/`LD<op>` and the comparand of
`CAS` are not the zero register. Every other operation passes. -/
def Operation.rmwLive {w : RegWidth} : Operation w → Bool
  | .CAS _ _ rs _ _ => !rs.isZr
  | .SWP _ _ _ rt _ => !rt.isZr
  | .LDOP _ _ _ _ rt _ => !rt.isZr
  | _ => true

/-- `Operation.rmwLive` of an instruction; labels and data pass. -/
def Directive.rmwLive : Directive → Bool
  | .instr i => i.operation.rmwLive
  | .label _ => true
  | .byteArray _ => true

/-- **The static `RmwLive` check** of a program: every directive passes. -/
def Program.rmwLive (p : Program) : Bool := p.all Directive.rmwLive

/-- The check on a laid-out program. -/
def Kraken.Executable.rmwLive (e : Kraken.Executable Directive) : Bool := e.2.all (·.1.rmwLive)

private theorem mapIdx_rmwLive :
    ∀ (p : Program) (sz : Nat → Nat), (p.mapIdx fun i d => (d, sz i)).all (·.1.rmwLive) = p.all Directive.rmwLive
  | [], _ => rfl
  | d :: p, sz => by
    rw [List.mapIdx_cons, List.all_cons, List.all_cons, mapIdx_rmwLive p (fun i => sz (i + 1))]

/-- Laying out does not change the check. -/
theorem Layout.apply_rmwLive (l : Kraken.Layout Directive) (p : Program) :
    (l p).rmwLive = p.rmwLive :=
  mapIdx_rmwLive p l.size

namespace Kraken.Promising.AArch64.EnvG

open Kraken.Promising Kraken.Promising.SLR.EnvG Kraken.Promising.SLR.EnvSpike
  Kraken.Promising.AArch64.EnvSpike

/-! ## Live trees, per primitive -/

section Live

/-- Shorthand: the tree of an effect, with no declarations, is live. -/
local notation "Lv " e => EvTree.RmwLive (toEv {} e)

theorem load_live {s : MachineData} {addr : BitVec 64} {w : MemWidth} {k : w.type → MachineData → Effects}
    (hk : ∀ v s, Lv (k v s)) : Lv (MachineData.load s addr w k) := by
  unfold MachineData.load
  simp only [toEv]
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => exact hk _ _
  | none => simp only [toEv, EvTree.access_empty, EvTree.RmwLive]; exact fun _ => hk _ _

theorem loadK_live {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {k : w.type → MachineData → Effects} (hk : ∀ v s, Lv (k v s)) :
    Lv (MachineData.loadK s lk xcl addr w k) := by
  unfold MachineData.loadK
  simp only [toEv]
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => exact hk _ _
  | none => simp only [toEv, EvTree.access_empty, EvTree.RmwLive]; exact fun _ => hk _ _

theorem store_live {s : MachineData} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {k : MachineData → Effects} (hk : ∀ s, Lv (k s)) : Lv (MachineData.store s addr v k) := by
  unfold MachineData.store
  simp only [toEv]
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x => exact hk _
  | none => simp only [toEv, EvTree.access_empty, EvTree.RmwLive]; exact fun _ => hk _

theorem storeK_live {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64} {w : MemWidth}
    {v : w.type} {k : Bool → MachineData → Effects} (hk : ∀ b s, Lv (k b s)) :
    Lv (MachineData.storeK s sk xcl addr v k) := by
  unfold MachineData.storeK
  simp only [toEv]
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    simp only
    cases xcl with
    | false => exact hk _ _
    | true =>
      simp only [ite_true, toEv, EvTree.RmwLive]
      intro i
      split <;> exact hk _ _
  | none => simp only [toEv, EvTree.access_empty, EvTree.RmwLive]; exact fun _ => hk _ _

/-- The one primitive that needs the check: `rmwK` with `noRet = false`. -/
theorem rmwK_live {s : MachineData} {rk : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {k : w.type → MachineData → Effects} (hnr : nr = false)
    (hk : ∀ v s, Lv (k v s)) : Lv (MachineData.rmwK s rk nr addr w op k) := by
  unfold MachineData.rmwK
  simp only [toEv]
  cases hd : Mem.loadInt s.dmem addr w.bytes with
  | some x =>
    simp only
    cases op (BitVec.ofInt w.bits x) <;> exact hk _ _
  | none => simp only [toEv, EvTree.access_empty, EvTree.RmwLive]; exact ⟨hnr, fun _ => hk _ _⟩

theorem loadPairK_live {s : MachineData} {lk : Kraken.LoadKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {k : w.type → w.type → MachineData → Effects} (hk : ∀ v₁ v₂ s, Lv (k v₁ v₂ s)) :
    Lv (MachineData.loadPairK s lk xcl addr w k) := by
  unfold MachineData.loadPairK
  simp only [toEv]
  cases Mem.loadInt s.dmem addr w.bytes <;> cases Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [toEv, EvTree.access_empty, EvTree.RmwLive]
  all_goals repeat' first
    | exact hk _ _ _
    | intro _
    | split
    | simp only [toEv, EvTree.access_empty, EvTree.RmwLive]

set_option linter.unusedSimpArgs false in
theorem storePairK_live {s : MachineData} {sk : Kraken.StoreKind} {xcl : Bool} {addr : BitVec 64}
    {w : MemWidth} {v₁ v₂ : w.type} {k : Bool → MachineData → Effects} (hk : ∀ b s, Lv (k b s)) :
    Lv (MachineData.storePairK s sk xcl addr v₁ v₂ k) := by
  unfold MachineData.storePairK
  simp only [toEv]
  cases Mem.loadInt s.dmem addr w.bytes <;> cases Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [toEv, EvTree.access_empty, EvTree.RmwLive]
  all_goals repeat' first
    | exact hk _ _
    | intro _
    | split
    | simp only [toEv, EvTree.access_empty, EvTree.RmwLive]

/-- `caspTree` emits `noRet = false` in both halves. -/
theorem caspTree_live {σ : Type} {k : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {ret : w.type → w.type → EvTree σ} (hk : ∀ o₁ o₂, (ret o₁ o₂).RmwLive) :
    (caspTree {} k addr c₁ c₂ n₁ n₂ ret).RmwLive := by
  unfold caspTree
  simp only [EvTree.access_empty, EvTree.RmwLive]
  have hguard : ∀ (b : Bool) (t : EvTree σ), t.RmwLive →
      (if b = true then t else EvTree.choose 0 nofun).RmwLive := by
    intro b t ht
    cases b
    · exact fun i => i.elim0
    · exact ht
  intro i j
  split
  · exact ⟨rfl, fun _ => ⟨rfl, fun _ => hguard _ _ (hk _ _)⟩⟩
  · exact ⟨rfl, fun _ => ⟨rfl, fun _ => hguard _ _ (hk _ _)⟩⟩

theorem rmwPairK_live {s : MachineData} {rk : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c₁ c₂ n₁ n₂ : w.type} {k : w.type → w.type → MachineData → Effects}
    (hk : ∀ v₁ v₂ s, Lv (k v₁ v₂ s)) : Lv (MachineData.rmwPairK s rk addr c₁ c₂ n₁ n₂ k) := by
  unfold MachineData.rmwPairK
  simp only [toEv]
  cases Mem.loadInt s.dmem addr w.bytes <;> cases Mem.loadInt s.dmem (addr + w.bytesv) w.bytes <;>
    simp only [toEv, EvTree.access_empty, EvTree.RmwLive]
  · exact caspTree_live fun _ _ => hk _ _ _
  · refine ⟨trivial, fun old => ?_⟩
    split <;> exact hk _ _ _
  · refine ⟨trivial, fun old => ?_⟩
    split <;> exact hk _ _ _
  · split <;> exact hk _ _ _

/-! ### Per addressing form -/

theorem AddrExpr.checkSPAlignment_live {a : AddrExpr} {s : MachineData} {ok : Unit → Effects}
    (hk : Lv (ok ())) : Lv (a.checkSPAlignment s ok) := by
  unfold AddrExpr.checkSPAlignment
  generalize a.base = b
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk
    | SP =>
      simp only
      split
      · simp only [toEv, EvTree.RmwLive]
      · exact hk

theorem UnscaledAddrExpr.checkSPAlignment_live {a : UnscaledAddrExpr} {s : MachineData}
    {ok : Unit → Effects} (hk : Lv (ok ())) : Lv (a.checkSPAlignment s ok) := by
  unfold UnscaledAddrExpr.checkSPAlignment
  generalize a.base = b
  cases b with
  | low x w' =>
    cases x with
    | reg x => exact hk
    | SP =>
      simp only
      split
      · simp only [toEv, EvTree.RmwLive]
      · exact hk

theorem interpBase_live {base : RegOrSp .W64} {s : MachineData} {ok : BitVec 64 → Effects}
    (hk : ∀ a, Lv (ok a)) : Lv (base.interpBase s ok) := by
  unfold RegOrSp.interpBase
  cases base with
  | low x w' =>
    cases x with
    | reg x => exact hk _
    | SP =>
      simp only
      split
      · simp only [toEv, EvTree.RmwLive]
      · exact hk _

theorem AddrExpr.interpLoad_live [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64} {s : MachineData}
    {k : w.type → MachineData → Effects} (hk : ∀ v s, Lv (k v s)) : Lv (a.interpLoad s p k) := by
  unfold AddrExpr.interpLoad
  exact AddrExpr.checkSPAlignment_live (load_live hk)

theorem AddrExpr.interpStore_live [Labels] {w : MemWidth} {a : AddrExpr} {p : Std.Rco Int64}
    {s : MachineData} {v : w.type} {k : MachineData → Effects} (hk : ∀ s, Lv (k s)) :
    Lv (a.interpStore s p v k) := by
  unfold AddrExpr.interpStore
  exact AddrExpr.checkSPAlignment_live (store_live hk)

theorem UnscaledAddrExpr.interpLoad_live [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {k : w.type → MachineData → Effects}
    (hk : ∀ v s, Lv (k v s)) : Lv (a.interpLoad s p k) := by
  unfold UnscaledAddrExpr.interpLoad
  exact UnscaledAddrExpr.checkSPAlignment_live (load_live hk)

theorem UnscaledAddrExpr.interpStore_live [Labels] {w : MemWidth} {a : UnscaledAddrExpr}
    {p : Std.Rco Int64} {s : MachineData} {v : w.type} {k : MachineData → Effects}
    (hk : ∀ s, Lv (k s)) : Lv (a.interpStore s p v k) := by
  unfold UnscaledAddrExpr.interpStore
  exact UnscaledAddrExpr.checkSPAlignment_live (store_live hk)

theorem AddrOrLit.interpLoad_live [Labels] {w : MemWidth} {a : AddrOrLit} {p : Std.Rco Int64}
    {s : MachineData} {k : w.type → MachineData → Effects} (hk : ∀ v s, Lv (k v s)) :
    Lv (a.interpLoad s p k) := by
  cases a with
  | addr a => exact AddrExpr.interpLoad_live hk
  | lit l =>
    cases l with
    | addr a => exact load_live hk
    | pool q => exact hk _ _

/-! ### Per instruction -/

set_option allowUnsafeReducibility true in
attribute [local irreducible] MachineData.load MachineData.store MachineData.loadK MachineData.storeK
  MachineData.rmwK MachineData.loadPairK MachineData.storePairK MachineData.rmwPairK AddrExpr.interpLoad
  AddrExpr.interpStore UnscaledAddrExpr.interpLoad
  UnscaledAddrExpr.interpStore AddrOrLit.interpLoad AddrExpr.checkSPAlignment RegOrSp.interpBase

set_option hygiene false in
/-- `jsim_search` (`EnvSpikeA64`) for liveness: the primitive lemmas above,
with the check `hop` closing `rmwK`'s `noRet = false`. -/
local macro "live_search" : tactic =>
  `(tactic| (
    simp only [Operation.interp, Operation.rmwLive, MachineData.setRegOrZr, MachineData.setRegOrSp,
      AddrExpr.eval_mk, toEv] at hop ⊢ <;>
    repeat' first
      | exact hk _
      | exact hj _ _
      | exact trivial
      | (simp only [EvTree.RmwLive]; done)
      | refine AddrOrLit.interpLoad_live (fun v s => ?_)
      | refine AddrExpr.interpLoad_live (fun v s => ?_)
      | refine UnscaledAddrExpr.interpLoad_live (fun v s => ?_)
      | refine AddrExpr.interpStore_live (fun s => ?_)
      | refine UnscaledAddrExpr.interpStore_live (fun s => ?_)
      | refine AddrExpr.checkSPAlignment_live ?_
      | refine load_live (fun v s => ?_)
      | refine store_live (fun s => ?_)
      | refine loadK_live (fun v s => ?_)
      | refine storeK_live (fun b s => ?_)
      | refine rmwK_live (by simpa using hop) (fun v s => ?_)
      | refine loadPairK_live (fun v₁ v₂ s => ?_)
      | refine storePairK_live (fun b s => ?_)
      | refine rmwPairK_live (fun v₁ v₂ s => ?_)
      | refine interpBase_live (fun a => ?_)
      | (simp only [EvTree.RmwLive]; intro _)
      | (split <;> rename_i hcond <;> try simp only [hcond, ite_true, ite_false, Bool.false_eq_true])
      | simp only [MachineData.setRegOrZr, MachineData.setRegOrSp, AddrExpr.eval_mk, toEv]))

/-- **One operation's tree is live** if the operation passes the check and its
continuations' trees are. -/
theorem operation_live [Labels] {w : RegWidth} (op : Operation w) (p : Std.Rco Int64) {s : MachineData}
    {k : MachineData → Effects} {j : Int64 → MachineData → Effects} (hop : op.rmwLive = true)
    (hk : ∀ s, Lv (k s)) (hj : ∀ pc s, Lv (j pc s)) : Lv (Operation.interp op p s k j) := by
  cases op <;> live_search

theorem directive_live [Labels] (dir : Directive) (p : Std.Rco Int64) {s : MachineData}
    {k : MachineData → Effects} {j : Int64 → MachineData → Effects} (hd : dir.rmwLive = true)
    (hk : ∀ s, Lv (k s)) (hj : ∀ pc s, Lv (j pc s)) : Lv (dir.interp s p k j) := by
  cases dir with
  | instr i =>
    show Lv (i.interp s p k j)
    unfold Instr.interp
    exact operation_live _ _ hd hk hj
  | label l => exact hk _
  | byteArray b => simp only [Directive.interp, toEv, EvTree.RmwLive]

end Live

/-! ## One instruction -/

/-- The cell `codeAt` finds is a cell of the executable. -/
theorem mem_of_codeAt {e : Kraken.Executable Directive} {pc : Int64} {d : Directive} {z : Nat}
    {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) : (d, z) ∈ e.2 := by
  obtain ⟨start, ds⟩ := e
  obtain ⟨a', ds', hW, hsuf⟩ := dropWhile_withAddresses (fun x => decide (x.1 ≠ pc)) ds start
  have hfrom : Kraken.Executable.directivesFromAddress (start, ds) pc = ds' := by
    unfold Kraken.Executable.directivesFromAddress
    rw [hW, Kraken.Executable.withAddresses_map_snd]
  unfold Kraken.Executable.codeAt at h
  rw [hfrom] at h
  have hm : (d, z) ∈ ds'.dropWhile (fun c => c.1.isLabel) := by rw [h]; exact List.mem_cons_self
  exact hsuf.subset ((List.dropWhile_suffix _).subset hm)

/-- On an executable that passes the check, the instruction `codeAt` finds
passes it. -/
theorem rmwLive_of_mem_codeAt {e : Kraken.Executable Directive} (hp : e.rmwLive = true) {pc : Int64}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)} (h : e.codeAt pc = (d, z) :: rest) :
    d.rmwLive = true :=
  List.all_eq_true.mp hp _ (mem_of_codeAt h)

/-- **`rmwLive_of_codeAt`**: at a pc whose instruction passes the check, with
no declarations, the thread's instruction tree is live. -/
theorem rmwLive_of_codeAt {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)} (he : st.exe = e) (hds : st.decls = {})
    (hcode : e.codeAt st.st.2 = (d, z) :: rest) (hd : d.rmwLive = true) :
    ∀ tree, isa.exec st = some tree → tree.RmwLive := by
  intro tree htree
  obtain ⟨ls, hat, hls⟩ := directivesAtAddress_of_codeAt hcode
  obtain ⟨exe, endPc, ⟨s, pc⟩, showPc, decls⟩ := st
  simp only at he hds hcode hat ⊢
  subst he hds
  have hdir : ({ exe, endPc, st := (s, pc), showPc, decls := {} } : State).directive = some d := by
    unfold State.directive
    simp only
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress exe pc) = Kraken.Executable.codeAt exe pc from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  simp only [isa, exec, hdir, Option.isNone_some, Bool.or_false] at htree
  split at htree
  · cases htree
  · cases htree
    refine (EvTree.rmwLive_map (σ := MachineState) (τ := State) _ _).mpr ?_
    unfold Executable.step
    letI := Executable.labels exe
    simp only
    rw [hat, Directives.interp_label_prefix ls _ _ _ _ hls]
    simp only [Directives.interp]
    exact directive_live d _ hd (fun _ => trivial) (fun _ _ => trivial)

/-- The same from the static check of the whole executable. -/
theorem rmwLive_of_codeAt' {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State}
    {d : Directive} {z : Nat} {rest : List (Directive × Nat)} (he : st.exe = e) (hds : st.decls = {})
    (hcode : e.codeAt st.st.2 = (d, z) :: rest) (hp : e.rmwLive = true) :
    ∀ tree, isa.exec st = some tree → tree.RmwLive :=
  rmwLive_of_codeAt he hds hcode (rmwLive_of_mem_codeAt hp hcode)

/-- **One instruction, any live tree judgment**
(`EnvSpikeA64.exec_treeJ_of_instrStepEnv` for a `TreeJLive`): as the prototype's
link step, plus the hypothesis that the thread's trees are live. The proof
is the prototype's at `J.toTreeJ`. -/
theorem exec_treeJLive_of_instrStepEnv {E : SharedEnv} (J : TreeJLive E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {})
    (h : e.instrStepEnv E (st.st, g) R) (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g')
    (hlive : ∀ tree, isa.exec st = some tree → tree.RmwLive) :
    ∀ tree, isa.exec st = some tree → J.W tree g := fun tree ht =>
  exec_treeJ_of_instrStepEnv J.toTreeJ he hds h hR tree ht (hlive tree ht)

/-- **One instruction of a checked program**: `exec_treeJLive_of_instrStepEnv`
with liveness from the static check `e.rmwLive` (for a laid-out program,
`Layout.apply_rmwLive` turns it into `Program.rmwLive`, decided by
`decide`). -/
theorem exec_treeJLive_of_instrStepEnv' {E : SharedEnv} (J : TreeJLive E State)
    {e : Kraken.Executable Directive} [Kraken.Executable.ValidLayout e] {st : State} {g : E.State}
    {R : MachineState × E.State → Prop} (he : st.exe = e) (hds : st.decls = {})
    (h : e.instrStepEnv E (st.st, g) R) (hR : ∀ m g', R (m, g') → J.Post { st with st := m } g')
    (hp : e.rmwLive = true) :
    ∀ tree, isa.exec st = some tree → J.W tree g := by
  obtain ⟨d, z, rest, hcode, -⟩ := id h
  exact exec_treeJLive_of_instrStepEnv J he hds h hR (rmwLive_of_codeAt' he hds hcode hp)

end Kraken.Promising.AArch64.EnvG
