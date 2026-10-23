/-
**The certified x86-64 fragment writes words only**: every write event of
the canonical x86-64 certification semantics (`Kernel.certExec X64.abi`,
`Scc/Sem/TargetX64.lean`) on a program of the fragment is to an 8-byte
location.

The fragment is syntactic and decidable (`Directive.wideOk`, `wideIn`,
`Scc/Cert/Rt/WideOkX64.lean`, light enough for `scc-x64` to import): every
memory write is 8 bytes,

- every regular instruction at operand width `W64` (`mov`, `push`, `pop`,
  ALU operations to memory, `xchg`, `[lock] xadd`, `[lock] cmpxchg`,
  `lock <op>`, `movnti`, `movfs`), and `call` at every width;
- a narrower regular instruction with no memory destination;
- a vector instruction with no memory destination.

**Fragment limit**: `movb`/`movw`/`movl` and every other 1, 2 or 4-byte
memory destination (`setcc` to memory, a narrow `push`, narrow
`xchg`/`xadd`/`cmpxchg`/`lock <op>`/`movnti`), the vector stores and
`cmpxchg16b` are outside it; `scc --code` refuses a program outside the
fragment (keyed off `wideIn`).

The width of a write is that of its location, which `Decls.resolve` picks:
an 8-byte access gets an 8-byte location (or a fault) when no declaration is
unsized (`DeclsWide`; the canonical thread's declarations are empty,
`declsWide_empty`).

- `wide8Tree_map`: `Scc.Sem.Wide8Tree` (the write events of a tree are to
  8-byte locations) survives `EvTree.map`.
- `EW`: the same for the `Effects` of the instruction semantics before
  resolution (no vector store, no `rmw16`); `toEv_w8`: `toEv` maps the one
  to the other (`loadPieces_w8`: a non-atomic vector load is loads only).
- `interp_ew`, `avxInterp_ew`: an instruction of the fragment has `EW`
  effects.
- `exec_w8`, `certExec_w8`: the certification semantics at a state of the
  fragment (`WideSt`) writes words only.
- `leaf_map`, `certExec_leaf`, `wideSt_leaf` (on `Scc.Sem.TreeLeaf`):
  every leaf state keeps the executable and the declarations (system-call
  returns included), so `WideSt` is kept along solo runs. `wide8CodeOn` and
  `wideInv`: `Scc.Sem.Wide8CodeOn WideSt` and `Scc.Sem.WideInv WideSt` of
  `Kernel.certExec X64.abi`, what `Inv1.promise_cert_on` takes.
- `fit64Tree_map`, `access_fit`, `toEv_fit`, `exec_fit`, `certExec_fit`,
  `fit64CodeOn`: on the fragment every write is of a 64-bit value
  (`Scc.Sem.Fit64CodeOn WideSt`, what `Scc.Sem.fits_promise_cert_on`
  takes).
- `wideSt_soloLeaf`, `exec_wide8CodeOn`, `exec_wideInv`, `exec_fit64CodeOn`,
  `soloWide8CodeOn`, `soloWideInv`, `soloFit64CodeOn`: the same for the
  ISA's `exec` and for the solo projection `Kernel.soloExec` (the
  certification semantics of the canonical target, `Kernel.certSem`).
- `wideSt_threadAt`: the canonical thread of code cells whose directives are
  `wideIn` is `WideSt`; `wideSt_threadAt_sized` for the cells `sizedCells`
  lays a `wideIn` program out to.
-/
import Scc.Sem.TargetX64
import Scc.Sem.CertStep
import Scc.Sem.Wide
import Scc.Cert.Rt.WideOkX64
import Scc.Cert.PlaceSyms

namespace Scc.Cert.WideX64

open Kraken Kraken.Promising Scc.Sem

/-! ## Trees and effects that write words only -/

theorem wide8Tree_map {σ τ : Type} (f : σ → τ) : ∀ {t : EvTree σ}, Wide8Tree t → Wide8Tree (t.map f)
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => wide8Tree_map f (h i)
  | .load _ _ _ _, h => fun v => wide8Tree_map f (h v)
  | .store _ _ _ _ _, h => ⟨h.1, fun b => wide8Tree_map f (h.2 b)⟩
  | .rmw _ _ _ _ _, h => ⟨h.1, fun v => wide8Tree_map f (h.2 v)⟩
  | .fence _ _, h => fun u => wide8Tree_map f (h u)

/-- **No declaration is unsized** and an undeclared address is its own
footprint: an 8-byte access resolves to an 8-byte location or faults. -/
def DeclsWide (ds : Decls) : Prop := (∀ l ∈ ds.locs, l.bytes ≠ 0) ∧ ds.unsizedDefault = false

theorem declsWide_empty : DeclsWide {} := by
  refine ⟨?_, rfl⟩
  intro l h
  cases h

theorem resolve_bytes {ds : Decls} (hds : DeclsWide ds) {a : BitVec 64} {l : Loc}
    (h : ds.resolve a 8 = .ok l) : l.bytes = 8 := by
  unfold Decls.resolve at h
  split at h
  · rename_i l' hf
    have h0 : l'.bytes ≠ 0 := hds.1 l' (List.mem_of_find?_eq_some hf)
    by_cases h8 : l'.bytes = 8
    · simp only [h8, BEq.rfl, ↓reduceIte, Except.ok.injEq] at h; rw [← h, h8]
    · simp [h8, h0] at h
  · split at h
    · cases h
    · simp only [hds.2, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h; rw [← h]

theorem access_w8 {σ : Type} {ds : Decls} (hds : DeclsWide ds) {a : BitVec 64} {k : Loc → EvTree σ}
    (h : ∀ l, l.bytes = 8 → Wide8Tree (k l)) : Wide8Tree (EvTree.access ds a 8 k) := by
  unfold EvTree.access
  split
  · exact h _ (resolve_bytes hds ‹_›)
  · trivial

theorem access_any {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, Wide8Tree (k l)) : Wide8Tree (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · trivial

/-- **A non-atomic vector load writes nothing**: its pieces are loads (or a
fault), given continuations that write words only. -/
theorem loadPieces_w8 {σ : Type} {ds : Decls} {dmem : DataMem} :
    ∀ {addr : BitVec 64} {n : Nat} {k : List UInt8 → EvTree σ}, (∀ bs, Wide8Tree (k bs)) →
      Wide8Tree (X64.loadPieces ds dmem addr n k)
  | _, 0, _, h => h _
  | _, _ + 1, _, h => by
    simp only [X64.loadPieces]
    split
    · exact loadPieces_w8 fun _ => h _
    · split
      · trivial
      · exact access_any fun _ _ => loadPieces_w8 fun _ => h _

/-- **Every store-like effect is one word wide**: plain, kinded and
non-temporal stores and RMWs only at `Width.W64`; no vector store and no
16-byte RMW (`nonmem_store_avx`, `rmw16`). -/
inductive EW : Effects → Prop
  | done (a) : EW (.done a)
  | unimplemented (m) : EW (.unimplemented m)
  | gp_unaligned (a w) : EW (.gp_unaligned a w)
  | nonmem_load {dmem addr w ret} : (∀ v d, EW (ret v d)) → EW (.nonmem_load dmem addr w ret)
  | nonmem_store {dmem addr v ret} : (∀ d, EW (ret d)) → EW (@Effects.nonmem_store dmem addr .W64 v ret)
  | undefined {α inst ret} : (∀ a, EW (ret a)) → EW (@Effects.undefined α inst ret)
  | require_read_access {addr w ok} : (∀ u, EW (ok u)) → EW (.require_read_access addr w ok)
  | require_write_access {addr w ok} : (∀ u, EW (ok u)) → EW (.require_write_access addr w ok)
  | require_exec_access {p ok} : (∀ u, EW (ok u)) → EW (.require_exec_access p ok)
  | sync_load {k xcl dmem addr w ret} : (∀ v d, EW (ret v d)) → EW (.sync_load k xcl dmem addr w ret)
  | sync_store {k xcl dmem addr v ret} : (∀ b d, EW (ret b d)) →
      EW (@Effects.sync_store k xcl dmem addr .W64 v ret)
  | rmw {k dmem addr op ret} : (∀ v d, EW (ret v d)) → EW (.rmw k dmem addr .W64 op ret)
  | fence {k ok} : (∀ u, EW (ok u)) → EW (.fence k ok)
  | require_read_access_avx {addr w atm ok} : (∀ u, EW (ok u)) → EW (.require_read_access_avx addr w atm ok)
  | require_write_access_avx {addr w atm ok} : (∀ u, EW (ok u)) → EW (.require_write_access_avx addr w atm ok)
  | nonmem_load_avx {atm dmem addr w ret} : (∀ v d, EW (ret v d)) → EW (.nonmem_load_avx atm dmem addr w ret)
  | syscall {info ret} : (∀ r, EW (ret r)) → EW (.syscall info ret)

/-- **`toEv` of one-word effects writes words only.** -/
theorem toEv_w8 {ds : Decls} (hds : DeclsWide ds) {e : Effects} (h : EW e) : Wide8Tree (X64.toEv ds e) := by
  induction h with
  | done | unimplemented | gp_unaligned | syscall => simp only [X64.toEv]; trivial
  | nonmem_load _ ih | sync_load _ ih =>
    simp only [X64.toEv]; exact access_any fun _ v => ih _ _
  | nonmem_store _ ih =>
    simp only [X64.toEv]; exact access_w8 hds fun _ hl => ⟨hl, fun _ => ih _⟩
  | sync_store _ ih =>
    simp only [X64.toEv]; exact access_w8 hds fun _ hl => ⟨hl, fun _ => ih _ _⟩
  | rmw _ ih =>
    simp only [X64.toEv]; exact access_w8 hds fun _ hl => ⟨hl, fun _ => ih _ _⟩
  | fence _ ih => simp only [X64.toEv]; exact fun _ => ih _
  | require_read_access _ ih | require_write_access _ ih | require_exec_access _ ih
  | require_read_access_avx _ ih | require_write_access_avx _ ih =>
    simp only [X64.toEv]; exact ih _
  | @undefined α inst ret _ ih =>
    cases inst <;> simp only [X64.toEv]
    all_goals first | trivial | exact fun i => ih _
  | nonmem_load_avx _ ih =>
    simp only [X64.toEv]
    split
    · exact access_any fun _ v => ih _ _
    · exact loadPieces_w8 fun _ => ih _ _

/-! ## The instruction semantics of the fragment -/

/-- Close an `EW` goal over the `Effects` constructors. -/
local macro "ew" : tactic => `(tactic| repeat (first
  | assumption
  | apply EW.done | apply EW.unimplemented | apply EW.gp_unaligned
  | (apply EW.nonmem_load; intros) | (apply EW.nonmem_store; intros) | (apply EW.undefined; intros)
  | (apply EW.require_read_access; intros) | (apply EW.require_write_access; intros)
  | (apply EW.require_exec_access; intros) | (apply EW.sync_load; intros) | (apply EW.sync_store; intros)
  | (apply EW.rmw; intros) | (apply EW.fence; intros)
  | (apply EW.require_read_access_avx; intros) | (apply EW.require_write_access_avx; intros)
  | (apply EW.nonmem_load_avx; intros) | (apply EW.syscall; intros)
  | split
  | apply_assumption))

theorem noMem_eq {w : Width} {d : RegOrMem w} (h : noMem d = true) : ∃ r, d = .reg r := by
  cases d with
  | reg r => exact ⟨r, rfl⟩
  | mem _ => cases h

theorem avxNoMem_eq {w : AvxWidth} {d : AvxRegOrMem w} (h : avxNoMem d = true) : ∃ r, d = .avx r := by
  cases d with
  | avx r => exact ⟨r, rfl⟩
  | mem _ => cases h

section Combinators
variable {s : MachineData}

theorem ew_load {a : BitVec 64} {w : Width} {k : w.type → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (s.load a w k) := by
  unfold MachineData.load; ew

theorem ew_store {a : BitVec 64} {v : Width.W64.type} {k : MachineData → Effects}
    (h : ∀ s, EW (k s)) : EW (s.store a v k) := by
  unfold MachineData.store; ew

theorem ew_storeNT {a : BitVec 64} {v : Width.W64.type} {k : MachineData → Effects}
    (h : ∀ s, EW (k s)) : EW (s.storeNT a v k) := by
  unfold MachineData.storeNT; ew

theorem ew_rmwK {rk : RmwKind} {a : BitVec 64} {op : Width.W64.type → Option Width.W64.type}
    {k : Width.W64.type → MachineData → Effects} (h : ∀ v s, EW (k v s)) :
    EW (s.rmwK rk a .W64 op k) := by
  unfold MachineData.rmwK
  apply EW.require_read_access; intro; apply EW.require_write_access; intro
  split
  · dsimp only; split <;> exact h _ _
  · exact EW.rmw fun _ _ => h _ _

theorem ew_rmwPlain {a : BitVec 64} {op : Width.W64.type → Option Width.W64.type}
    {k : Width.W64.type → MachineData → Effects} (h : ∀ v s, EW (k v s)) :
    EW (s.rmwPlain a .W64 op k) := by
  unfold MachineData.rmwPlain
  exact ew_load fun _ _ => by split <;> first | exact ew_store (h _) | exact h _ _

theorem ew_loadAvx {a : BitVec 64} {w : AvxWidth} {k : w.type → MachineData → Effects} {ca atm : Bool}
    (h : ∀ v s, EW (k v s)) : EW (s.loadAvx a w k ca atm) := by
  unfold MachineData.loadAvx; ew

variable [Labels] [AddressSize] {p : Std.Rco Int64}

theorem ew_rmInterp {w : Width} {o : RegOrMem w} {k : w.type → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (o.interp s p k) := by
  cases o with
  | reg _ => exact h _ _
  | mem _ => exact ew_load h

theorem ew_opInterp {w : Width} {o : Operand w} {k : w.type → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (o.interp s p k) := by
  cases o with
  | regOrMem _ => exact ew_rmInterp h
  | imm _ => exact h _ _

theorem ew_rmInterpSeg {w : Width} {o : RegOrMem w} {seg : BitVec 64} {k : w.type → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (o.interpSeg seg s p k) := by
  cases o with
  | reg _ => exact h _ _
  | mem _ => exact ew_load h

theorem ew_opInterpSeg {w : Width} {o : Operand w} {seg : BitVec 64} {k : w.type → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (o.interpSeg seg s p k) := by
  cases o with
  | regOrMem _ => exact ew_rmInterpSeg h
  | imm _ => exact h _ _

theorem ew_relInterp {o : RelRegOrMem} {k : BitVec 64 → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (o.interp s p k) := by
  cases o with
  | rel _ => exact h _ _
  | reg _ => exact h _ _
  | mem _ => exact ew_load h

theorem ew_avxInterp {w : AvxWidth} {o : AvxRegOrMem w} {k : w.type → MachineData → Effects} {ca atm : Bool}
    (h : ∀ v s, EW (k v s)) : EW (o.interp s p k ca atm) := by
  cases o with
  | avx _ => exact h _ _
  | mem _ => exact ew_loadAvx h

/-- A write of a destination: a register, or memory at `W64`. -/
theorem ew_set {w : Width} {d : Dst w} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s, EW (k s)) (hd : w = .W64 ∨ noMem d = true) : EW (s.set d v p k) := by
  cases d with
  | reg _ => exact h _
  | mem _ =>
    rcases hd with rfl | hd
    · exact ew_store h
    · cases hd

theorem ew_setSeg {w : Width} {d : Dst w} {seg : BitVec 64} {v : w.type} {k : MachineData → Effects}
    (h : ∀ s, EW (k s)) (hd : w = .W64 ∨ noMem d = true) : EW (s.setSeg seg d v p k) := by
  cases d with
  | reg _ => exact h _
  | mem _ =>
    rcases hd with rfl | hd
    · exact ew_store h
    · cases hd

/-- A read-modify-write of a register, or of memory at `W64`. -/
theorem ew_rmw {w : Width} {o : RegOrMem w} {lock : Bool} {op : w.type → Option w.type}
    {k : w.type → MachineData → Effects} (h : ∀ v s, EW (k v s)) (hd : w = .W64 ∨ noMem o = true) :
    EW (o.rmw lock s p op k) := by
  cases o with
  | reg _ => dsimp only [RegOrMem.rmw]; split <;> exact h _ _
  | mem _ =>
    rcases hd with rfl | hd
    · dsimp only [RegOrMem.rmw]
      split
      · exact ew_rmwK h
      · exact ew_rmwPlain h
    · cases hd

end Combinators

/-- `ew` with the memory and operand combinators. -/
local macro "ewm" : tactic => `(tactic| repeat (first
  | assumption
  | exact Or.inl rfl | exact Or.inr rfl
  | (apply ew_load; intros) | (apply ew_store; intros) | (apply ew_storeNT; intros)
  | (apply ew_rmwK; intros) | (apply ew_rmw; intros) | (apply ew_set; intros) | (apply ew_setSeg; intros)
  | (apply ew_rmInterp; intros) | (apply ew_opInterp; intros) | (apply ew_rmInterpSeg; intros)
  | (apply ew_opInterpSeg; intros) | (apply ew_relInterp; intros) | (apply ew_avxInterp; intros)
  | apply EW.done | apply EW.unimplemented | apply EW.gp_unaligned
  | (apply EW.undefined; intros) | (apply EW.require_exec_access; intros) | (apply EW.fence; intros)
  | (apply EW.syscall; intros)
  | split
  | apply_assumption))

/-- `imul` of the fragment (`interp_ew`): the destination is the explicit one
or the first source. -/
theorem imul_ew [Labels] [AddressSize] {w : Width} (d : Option (Dst w)) (a : RegOrMem w) (b : Operand w)
    (hw : (Operation.imul d a b).wideOk = true) (p : Std.Rco Int64) (s : MachineData)
    {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, EW (next s)) : EW ((Operation.imul d a b).interp p s next jmp) := by
  cases d <;> cases w
  all_goals try simp only [Operation.wideOk, Operation.narrowOk] at hw
  all_goals try (obtain ⟨_, rfl⟩ := noMem_eq hw)
  all_goals (simp only [Operation.interp] <;> ewm)

/-- **A regular operation of the fragment has one-word effects**, given
one-word continuations. -/
theorem interp_ew [Labels] [AddressSize] {w : Width} (op : Operation w) (hw : op.wideOk = true)
    (p : Std.Rco Int64) (s : MachineData) {next : MachineData → Effects}
    {jmp : Int64 → MachineData → Effects} (hn : ∀ s, EW (next s)) (hj : ∀ pc s, EW (jmp pc s)) :
    EW (op.interp p s next jmp) := by
  cases w <;> cases op
  all_goals first | exact imul_ew _ _ _ hw p s hn | skip
  all_goals try simp only [Operation.wideOk, Operation.narrowOk, Bool.false_eq_true] at hw
  all_goals try (obtain ⟨_, rfl⟩ := noMem_eq hw)
  all_goals (simp only [Operation.interp, MachineData.pendingSyscall, Reg.interp] <;> ewm)

/-- **A vector operation of the fragment has one-word effects**, given
one-word continuations. -/
theorem avxInterp_ew [Labels] [AddressSize] {w : AvxWidth} (op : AvxOperation w) (hw : op.wideOk = true)
    (p : Std.Rco Int64) (s : MachineData) {next : MachineData → Effects} (hn : ∀ s, EW (next s)) :
    EW (op.interp p s next) := by
  cases op
  all_goals try simp only [AvxOperation.wideOk, Bool.false_eq_true] at hw
  all_goals try (obtain ⟨_, rfl⟩ := avxNoMem_eq hw)
  all_goals (simp only [AvxOperation.interp, MachineData.setAvx, MachineData.setAvxLegacy] <;> ewm)

theorem directive_ew [Labels] {d : Directive} (hd : d.wideOk = true) (s : MachineData) (p : Std.Rco Int64)
    {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, EW (next s)) (hj : ∀ pc s, EW (jmp pc s)) : EW (d.interp s p next jmp) := by
  cases d with
  | label => exact hn s
  | instr i =>
    refine EW.require_exec_access fun _ => ?_
    cases i with
    | regular a _ op => letI : AddressSize := .mk a; exact interp_ew op hd p s hn hj
    | avx a _ op => letI : AddressSize := .mk a; exact avxInterp_ew op hd p s hn
  | byteArray => exact EW.unimplemented _

theorem directives_ew [Labels] {ret : Int64 → MachineData → Effects} (hr : ∀ pc s, EW (ret pc s)) :
    ∀ (ds : List (Directive × Nat)), (∀ c ∈ ds, c.1.wideOk = true) → ∀ s pc, EW (Directives.interp ds s pc ret)
  | [], _, s, pc => hr pc s
  | (_, _) :: ds, h, s, _ =>
    directive_ew (h _ (List.mem_cons_self ..)) s _
      (fun s => directives_ew hr ds (fun c hc => h c (List.mem_cons_of_mem _ hc)) s _) hr

/-! ## The certification semantics on the fragment -/

/-- **Every directive of the executable is in the fragment.** -/
def ExeWide (e : _root_.Executable) : Prop := ∀ c ∈ e.2, c.1.wideOk = true

/-- **A thread state of the fragment**: its declarations are wide and its
executable is in the fragment. Both are fixed along the thread's run
(`certExec_leaf`). -/
def WideSt (s : X64.State) : Prop := DeclsWide s.decls ∧ ExeWide s.exe

theorem mem_of_mem_directivesAtAddress {e : _root_.Executable} {a : Int64} {c : Directive × Nat}
    (h : c ∈ Kraken.Executable.directivesAtAddress e a) : c ∈ e.2 := by
  obtain ⟨start, ds⟩ := e
  unfold Kraken.Executable.directivesAtAddress at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have hx' : x ∈ Kraken.Executable.withAddresses (start, ds) :=
    (List.dropWhile_suffix _).subset ((List.takeWhile_prefix _).subset hx)
  rw [← Kraken.Executable.withAddresses_map_snd ds start]
  exact List.mem_map_of_mem hx'

theorem step_ew {e : _root_.Executable} (he : ExeWide e) (st : MachineState) :
    EW (_root_.Executable.step e st fun s' => .done s') := by
  unfold _root_.Executable.step
  letI := _root_.Executable.labels e
  exact directives_ew (fun _ _ => EW.done _) _ (fun c hc => he c (mem_of_mem_directivesAtAddress hc)) _ _

/-- **The x86-64 semantics on the fragment writes words only.** -/
theorem exec_w8 {s : X64.State} (hs : WideSt s) {t : EvTree X64.State} (h : X64.exec s = some t) :
    Wide8Tree t := by
  unfold X64.exec at h
  split at h
  · cases h
  · cases h
    exact wide8Tree_map _ (toEv_w8 hs.1 (step_ew hs.2 _))

/-- **The canonical x86-64 certification semantics on the fragment writes
words only.** At a supported system call it is a choice among `done`s;
otherwise it is `X64.exec`. -/
theorem certExec_w8 {s : X64.State} (hs : WideSt s) {t : EvTree X64.State}
    (h : Kernel.certExec Scc.Sem.X64.abi s = some t) : Wide8Tree t := by
  unfold Kernel.certExec at h
  split at h
  · split at h
    · cases h; exact fun _ => trivial
    · exact exec_w8 hs h
  · exact exec_w8 hs h

/-! ## Writes of 64-bit values

The values the fragment writes are 64-bit registers widened to `Val`
(`Scc.Sem.Fit64Tree`), whatever the declarations: the same `EW` effects,
any resolution. -/

theorem fit64Tree_map {σ τ : Type} (f : σ → τ) : ∀ {t : EvTree σ}, Fit64Tree t → Fit64Tree (t.map f)
  | .done _, _ => trivial
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => fit64Tree_map f (h i)
  | .load _ _ _ _, h => fun v => fit64Tree_map f (h v)
  | .store _ _ _ _ _, h => ⟨h.1, fun b => fit64Tree_map f (h.2 b)⟩
  | .rmw _ _ _ _ _, h => ⟨h.1, fun v => fit64Tree_map f (h.2 v)⟩
  | .fence _ _, h => fun u => fit64Tree_map f (h u)

theorem access_fit {σ : Type} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, Fit64Tree (k l)) : Fit64Tree (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · trivial

/-- **A non-atomic vector load writes nothing** (`loadPieces_w8` for
`Fit64Tree`). -/
theorem loadPieces_fit {σ : Type} {ds : Decls} {dmem : DataMem} :
    ∀ {addr : BitVec 64} {n : Nat} {k : List UInt8 → EvTree σ}, (∀ bs, Fit64Tree (k bs)) →
      Fit64Tree (X64.loadPieces ds dmem addr n k)
  | _, 0, _, h => h _
  | _, _ + 1, _, h => by
    simp only [X64.loadPieces]
    split
    · exact loadPieces_fit fun _ => h _
    · split
      · trivial
      · exact access_fit fun _ _ => loadPieces_fit fun _ => h _

/-- **`toEv` of one-word effects writes 64-bit values only.** -/
theorem toEv_fit {ds : Decls} {e : Effects} (h : EW e) : Fit64Tree (X64.toEv ds e) := by
  induction h with
  | done | unimplemented | gp_unaligned | syscall => simp only [X64.toEv]; trivial
  | nonmem_load _ ih | sync_load _ ih =>
    simp only [X64.toEv]; exact access_fit fun _ v => ih _ _
  | nonmem_store _ ih =>
    simp only [X64.toEv]; exact access_fit fun _ => ⟨fit64_setWidth _ _, fun _ => ih _⟩
  | sync_store _ ih =>
    simp only [X64.toEv]; exact access_fit fun _ => ⟨fit64_setWidth _ _, fun _ => ih _ _⟩
  | rmw _ ih =>
    simp only [X64.toEv]
    refine access_fit fun l => ⟨fun old v he => ?_, fun _ => ih _ _⟩
    obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp he
    exact fit64_setWidth _ x
  | fence _ ih => simp only [X64.toEv]; exact fun _ => ih _
  | require_read_access _ ih | require_write_access _ ih | require_exec_access _ ih
  | require_read_access_avx _ ih | require_write_access_avx _ ih =>
    simp only [X64.toEv]; exact ih _
  | @undefined α inst ret _ ih =>
    cases inst <;> simp only [X64.toEv]
    all_goals first | trivial | exact fun i => ih _
  | nonmem_load_avx _ ih =>
    simp only [X64.toEv]
    split
    · exact access_fit fun _ v => ih _ _
    · exact loadPieces_fit fun _ => ih _ _

/-- **The x86-64 semantics on the fragment writes 64-bit values only.** -/
theorem exec_fit {s : X64.State} (hs : WideSt s) {t : EvTree X64.State} (h : X64.exec s = some t) :
    Fit64Tree t := by
  unfold X64.exec at h
  split at h
  · cases h
  · cases h
    exact fit64Tree_map _ (toEv_fit (step_ew hs.2 _))

/-- **The canonical x86-64 certification semantics on the fragment writes
64-bit values only.** -/
theorem certExec_fit {s : X64.State} (hs : WideSt s) {t : EvTree X64.State}
    (h : Kernel.certExec Scc.Sem.X64.abi s = some t) : Fit64Tree t := by
  unfold Kernel.certExec at h
  split at h
  · split at h
    · cases h; exact fun _ => trivial
    · exact exec_fit hs h
  · exact exec_fit hs h

/-- **`Fit64CodeOn` for the canonical x86-64 certification semantics** on
the fragment. -/
theorem fit64CodeOn : Fit64CodeOn WideSt (Kernel.certExec Scc.Sem.X64.abi) :=
  fun _ _ hs h => certExec_fit hs h

/-! ## The fragment along a run -/

theorem leaf_map {σ τ : Type} (f : σ → τ) : ∀ {t : EvTree σ} {y : τ}, TreeLeaf (t.map f) y → ∃ x, y = f x
  | .done x, _, h => ⟨x, h⟩
  | .fault _, _, h => h.elim
  | .choose _ _, _, ⟨_, h⟩ => leaf_map f h
  | .load _ _ _ _, _, ⟨_, h⟩ => leaf_map f h
  | .store _ _ _ _ _, _, ⟨_, h⟩ => leaf_map f h
  | .rmw _ _ _ _ _, _, ⟨_, h⟩ => leaf_map f h
  | .fence _ _, _, ⟨_, h⟩ => leaf_map f h

/-- Every leaf of `X64.exec` keeps the executable and the declarations: an
instruction changes the machine state only. -/
theorem exec_leaf {s : X64.State} {t : EvTree X64.State} (h : X64.exec s = some t) {s' : X64.State}
    (hl : TreeLeaf t s') : s'.exe = s.exe ∧ s'.decls = s.decls := by
  unfold X64.exec at h
  split at h
  · cases h
  · cases h; obtain ⟨_, rfl⟩ := leaf_map _ hl; exact ⟨rfl, rfl⟩

/-- **Every leaf of the certification semantics keeps the executable and the
declarations**, the system-call returns (`certSuccs`) included. -/
theorem certExec_leaf {s : X64.State} {t : EvTree X64.State} (h : Kernel.certExec Scc.Sem.X64.abi s = some t)
    {s' : X64.State} (hl : TreeLeaf t s') : s'.exe = s.exe ∧ s'.decls = s.decls := by
  unfold Kernel.certExec at h
  split at h
  · split at h
    · rename_i call _
      have hm : ∀ x ∈ Kernel.certSuccs Scc.Sem.X64.abi s call, x.exe = s.exe ∧ x.decls = s.decls := by
        intro x hx
        unfold Kernel.certSuccs at hx
        split at hx
        · simp only [List.mem_singleton] at hx; subst hx; exact ⟨rfl, rfl⟩
        · obtain ⟨_, -, he⟩ := List.mem_map.mp hx; subst he; exact ⟨rfl, rfl⟩
      cases h
      obtain ⟨i, rfl⟩ := hl
      exact hm _ (List.getElem_mem _)
    · exact exec_leaf h hl
  · exact exec_leaf h hl

/-- **The fragment is kept along a run**: every leaf of the certification
semantics from a `WideSt` state is `WideSt`. -/
theorem wideSt_leaf {s : X64.State} (hs : WideSt s) {t : EvTree X64.State}
    (h : Kernel.certExec Scc.Sem.X64.abi s = some t) {s' : X64.State} (hl : TreeLeaf t s') : WideSt s' := by
  obtain ⟨he, hd⟩ := certExec_leaf h hl
  exact ⟨hd ▸ hs.1, he ▸ hs.2⟩

/-- **`Wide8CodeOn` for the canonical x86-64 certification semantics** on
the fragment. -/
theorem wide8CodeOn : Wide8CodeOn WideSt (Kernel.certExec Scc.Sem.X64.abi) :=
  fun _ _ hs h => certExec_w8 hs h

/-- **`WideInv` for the canonical x86-64 certification semantics**: the
fragment is kept by every leaf. -/
theorem wideInv : WideInv WideSt (Kernel.certExec Scc.Sem.X64.abi) :=
  fun _ _ _ hs h hl => wideSt_leaf hs h hl

/-! ## The solo projection on the fragment

The certification semantics of the canonical target is `Kernel.soloExec`
(`Kernel.certSem`): the ISA's `exec`, or a quiet tree whose leaves are solo
leaves (`Kernel.SoloLeaf`), which change the machine state only. -/

/-- **A solo leaf keeps the fragment**: `ret`, `setTp`, `setDmem` and `skip`
change the machine state only. -/
theorem wideSt_soloLeaf {s s' : X64.State} (hs : WideSt s) (h : Kernel.SoloLeaf Scc.Sem.X64.abi s s') : WideSt s' := by
  rcases h with rfl | ⟨m, rfl⟩ | ⟨r, rfl⟩ | ⟨a, r, rfl⟩ | ⟨m, r, rfl⟩ <;> exact hs

/-- `Wide8CodeOn WideSt` of the x86-64 semantics. -/
theorem exec_wide8CodeOn : Wide8CodeOn WideSt X64.isa.exec :=
  fun _ _ hs h => exec_w8 hs h

/-- `WideInv WideSt` of the x86-64 semantics. -/
theorem exec_wideInv : WideInv WideSt X64.isa.exec :=
  fun _ _ _ hs h hl => by
    obtain ⟨he, hd⟩ := exec_leaf h hl
    exact ⟨hd ▸ hs.1, he ▸ hs.2⟩

/-- `Fit64CodeOn WideSt` of the x86-64 semantics. -/
theorem exec_fit64CodeOn : Fit64CodeOn WideSt X64.isa.exec :=
  fun _ _ hs h => exec_fit hs h

/-- **`Wide8CodeOn` for the canonical x86-64 certification semantics**
(`Kernel.soloExec`) on the fragment. -/
theorem soloWide8CodeOn (μ : Marks) (x : Kernel.KState) (tid : Nat) :
    Wide8CodeOn WideSt (Kernel.soloExec Scc.Sem.X64.abi Arch.tso μ x tid) :=
  Kernel.soloExec_wide8CodeOn exec_wide8CodeOn

/-- **`WideInv` for the canonical x86-64 certification semantics**
(`Kernel.soloExec`): the fragment is kept by every leaf. -/
theorem soloWideInv (μ : Marks) (x : Kernel.KState) (tid : Nat) :
    WideInv WideSt (Kernel.soloExec Scc.Sem.X64.abi Arch.tso μ x tid) :=
  Kernel.soloExec_wideInv exec_wideInv fun _ _ hs h => wideSt_soloLeaf hs h

/-- **`Fit64CodeOn` for the canonical x86-64 certification semantics**
(`Kernel.soloExec`) on the fragment. -/
theorem soloFit64CodeOn (μ : Marks) (x : Kernel.KState) (tid : Nat) :
    Fit64CodeOn WideSt (Kernel.soloExec Scc.Sem.X64.abi Arch.tso μ x tid) :=
  Kernel.soloExec_writeCodeOn exec_fit64CodeOn

/-! ## The canonical thread of a program of the fragment -/

theorem placeSyms_wideOk {cur : Nat} {syms : List (String × Nat)} :
    ∀ c ∈ Scc.Sem.placeSyms (Directive.byteArray (.mk #[])) Directive.label cur syms, c.1.wideOk = true := by
  intro c h
  rcases (Scc.Cert.PlaceSyms.placeSyms_spec _ _ cur syms).1 c h with ⟨he, -⟩ | ⟨p, -, rfl⟩
  · rw [he]; rfl
  · rfl

theorem placeBelow_wideOk {lo : Nat} {syms : List (String × Nat)} :
    ∀ c ∈ Scc.Sem.placeBelow (Directive.byteArray (.mk #[])) Directive.label lo syms, c.1.wideOk = true := by
  intro c h
  rcases (Scc.Cert.PlaceSyms.placeBelow_spec _ _ lo syms).1 c h with ⟨he, -⟩ | ⟨p, -, rfl⟩
  · rw [he]; rfl
  · rfl

/-- **The canonical thread of code of the fragment is `WideSt`**
(`X64.threadAt`: no declarations; the code cells, then data and label
cells). -/
theorem wideSt_threadAt {cells : List (Directive × Nat)} (hw : wideIn (cells.map (·.1)) = true)
    (E : Scc.Sem.Entry) (base : Nat) (syms : List (String × Nat)) :
    WideSt (Scc.Sem.X64.threadAt E base cells syms) := by
  refine ⟨declsWide_empty, ?_⟩
  intro c hc
  simp only [Scc.Sem.X64.threadAt, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact placeBelow_wideOk c hc
  · exact List.all_eq_true.mp hw c.1 (List.mem_map_of_mem hc)
  · exact placeSyms_wideOk c hc

/-- `wideSt_threadAt` for the cells a `wideIn` program is laid out to at its
sizes (`sizedCells`, as `X64.cellsOf` does). -/
theorem wideSt_threadAt_sized {prog : Program} {sizes : List Nat} {cells : List (Directive × Nat)}
    (hw : wideIn prog = true) (hc : X64.sizedCells prog sizes = some cells)
    (E : Scc.Sem.Entry) (base : Nat) (syms : List (String × Nat)) :
    WideSt (Scc.Sem.X64.threadAt E base cells syms) :=
  wideSt_threadAt (by rw [X64.sizedCells_fst hc]; exact hw) E base syms

end Scc.Cert.WideX64
