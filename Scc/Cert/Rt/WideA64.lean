/-
**The certified AArch64 fragment writes words only**: every write event of
the canonical AArch64 certification semantics (`Kernel.certExec abi`,
`Scc/Sem/TargetA64.lean`) on a program of the fragment is to an 8-byte
location.

The fragment is syntactic and decidable (`Directive.wideOk`, `wideIn`):
every store-like instruction is one of the one-word forms the emitter
(`Scc/Emit/A64.lean`) produces,

- `str x`/`stur x` (every addressing form),
- `stlr x`,
- `swp x`, `ld<op> x`, `cas x` (every ordering),

and every other instruction is allowed. **Fragment limit**: the narrower
and wider stores are outside it: `str w`/`stur w`/`stlr w`/`swp w`/`cas w`/
`ld<op> w` (and their byte and half-word forms `strb`/`strh`/`sturb`/
`sturh`), `stp` (one 16-byte or two stores), the exclusives `stxr`/`stxp`
and `casp`. `scc --code` refuses a program outside the fragment (keyed off
`wideIn`), so the emitter's `.w32` store path and its sub-word stores by `str
w` are not certified yet.

The width of a write is that of its location, which `Decls.resolve` picks:
an 8-byte access gets an 8-byte location (or a fault) when no declaration is
unsized (`DeclsWide`; the canonical thread's declarations are empty,
`declsWide_empty`).

- `wide8Tree_map`: `Scc.Sem.Wide8Tree` (the write events of a tree are to
  8-byte locations) survives `EvTree.map`.
- `EW`: the same for the `Effects` of the instruction semantics before
  resolution; `toEv_w8`: `toEv` maps the one to the other.
- `Operation.wideOk`, `Directive.wideOk`, `wideIn`: the fragment
  (`Scc/Cert/Rt/WideOkA64.lean`, light enough for `scc-arm` to import).
- `interp_ew`: an instruction of the fragment has `EW` effects.
- `execLSE2_w8`, `certExec_w8`: the certification semantics at a state of
  the fragment (`WideSt`) writes words only.
- `leaf_map`, `certExec_leaf`, `wideSt_leaf` (on `Scc.Sem.TreeLeaf`):
  every leaf state keeps the executable and the declarations (system-call
  returns included), so `WideSt` is kept along solo runs. `wide8CodeOn` and
  `wideInv`: `Scc.Sem.Wide8CodeOn WideSt` and `Scc.Sem.WideInv WideSt` of
  `Kernel.certExec abi`, what `Inv1.promise_cert_on` takes.
- `fit64Tree_map`, `access_fit`, `toEv_fit`, `execLSE2_fit`, `certExec_fit`,
  `fit64CodeOn`: on the fragment every write is of a 64-bit value
  (`Scc.Sem.Fit64CodeOn WideSt`, what `Scc.Sem.fits_promise_cert_on`
  takes).
- `wideSt_soloLeaf`, `exec_wide8CodeOn`, `exec_wideInv`, `exec_fit64CodeOn`,
  `soloWide8CodeOn`, `soloWideInv`, `soloFit64CodeOn`: the same for the
  ISA's `exec` and for the solo projection `Kernel.soloExec` (the
  certification semantics of the canonical target, `Kernel.certSem`).
- `wideSt_threadAt`: the canonical thread of a `wideIn` program is
  `WideSt`.
-/
import Scc.Sem.TargetA64
import Scc.Sem.CertStep
import Scc.Sem.Wide
import Scc.Cert.Rt.WideOkA64
import Scc.Cert.PlaceSyms

namespace Scc.Cert.WideA64

open Kraken Kraken.Promising Kraken.Promising.AArch64 Scc.Sem

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

/-- **Every store-like effect is one word wide**: plain and kinded stores and
RMWs only at `MemWidth.W64`; no pair store or pair RMW. -/
inductive EW : Effects → Prop
  | done (a) : EW (.done a)
  | unimplemented (m) : EW (.unimplemented m)
  | nonmem_load {dmem addr w ret} : (∀ v d, EW (ret v d)) → EW (.nonmem_load dmem addr w ret)
  | nonmem_store {dmem addr v ret} : (∀ d, EW (ret d)) → EW (@Effects.nonmem_store dmem addr .W64 v ret)
  | undefined {α inst ret} : (∀ a, EW (ret a)) → EW (@Effects.undefined α inst ret)
  | require_read_access {addr w ok} : (∀ u, EW (ok u)) → EW (.require_read_access addr w ok)
  | require_write_access {addr w ok} : (∀ u, EW (ok u)) → EW (.require_write_access addr w ok)
  | require_exec_access {p ok} : (∀ u, EW (ok u)) → EW (.require_exec_access p ok)
  | unaligned_sp {w} (sp) : EW (@Effects.unaligned_sp w sp)
  | sync_load {k xcl dmem addr w ret} : (∀ v d, EW (ret v d)) → EW (.sync_load k xcl dmem addr w ret)
  | sync_store {k xcl dmem addr v ret} : (∀ b d, EW (ret b d)) →
      EW (@Effects.sync_store k xcl dmem addr .W64 v ret)
  | rmw {k nr dmem addr op ret} : (∀ v d, EW (ret v d)) → EW (.rmw k nr dmem addr .W64 op ret)
  | fence {k ok} : (∀ u, EW (ok u)) → EW (.fence k ok)
  | sync_load_pair {k xcl dmem addr w ret} : (∀ v1 v2 d, EW (ret v1 v2 d)) →
      EW (.sync_load_pair k xcl dmem addr w ret)
  | syscall {info ret} : (∀ r, EW (ret r)) → EW (.syscall info ret)

/-- **`toEv` of one-word effects writes words only.** -/
theorem toEv_w8 {ds : Decls} (hds : DeclsWide ds) {e : Effects} (h : EW e) : Wide8Tree (toEv ds e) := by
  induction h with
  | done | unimplemented | unaligned_sp | syscall => simp only [toEv]; trivial
  | nonmem_load _ ih | sync_load _ ih =>
    simp only [toEv]; exact access_any fun _ v => ih _ _
  | nonmem_store _ ih =>
    simp only [toEv]; exact access_w8 hds fun _ hl => ⟨hl, fun _ => ih _⟩
  | sync_store _ ih =>
    simp only [toEv]; exact access_w8 hds fun _ hl => ⟨hl, fun _ => ih _ _⟩
  | rmw _ ih =>
    simp only [toEv]; exact access_w8 hds fun _ hl => ⟨hl, fun _ => ih _ _⟩
  | fence _ ih => simp only [toEv]; exact fun _ => ih _
  | require_read_access _ ih | require_write_access _ ih | require_exec_access _ ih =>
    simp only [toEv]; exact ih _
  | @undefined α inst ret _ ih =>
    cases inst <;> simp only [toEv]
    all_goals first | trivial | exact fun i => ih _
  | sync_load_pair _ ih =>
    simp only [toEv]
    split
    · exact access_any fun _ v => ih _ _ _
    · exact access_any fun _ v1 => access_any fun _ v2 => ih _ _ _

/-! ## The instruction semantics of the fragment -/

/-- Close an `EW` goal over the `Effects` combinators. -/
local macro "ew" : tactic => `(tactic| repeat (first
  | assumption
  | apply EW.done | apply EW.unimplemented | apply EW.unaligned_sp
  | (apply EW.nonmem_load; intros) | (apply EW.nonmem_store; intros) | (apply EW.undefined; intros)
  | (apply EW.require_read_access; intros) | (apply EW.require_write_access; intros)
  | (apply EW.require_exec_access; intros) | (apply EW.sync_load; intros) | (apply EW.sync_store; intros)
  | (apply EW.rmw; intros) | (apply EW.fence; intros) | (apply EW.sync_load_pair; intros)
  | (apply EW.syscall; intros)
  | split
  | apply_assumption))

section Combinators
variable {s : MachineData}

theorem ew_load {a : BitVec 64} {w : MemWidth} {k : w.type → MachineData → Effects}
    (h : ∀ v s, EW (k v s)) : EW (s.load a w k) := by
  unfold MachineData.load; ew

theorem ew_loadK {lk : LoadKind} {xcl : Bool} {a : BitVec 64} {w : MemWidth}
    {k : w.type → MachineData → Effects} (h : ∀ v s, EW (k v s)) : EW (s.loadK lk xcl a w k) := by
  unfold MachineData.loadK; ew

theorem ew_loadPairK {lk : LoadKind} {xcl : Bool} {a : BitVec 64} {w : MemWidth}
    {k : w.type → w.type → MachineData → Effects} (h : ∀ v1 v2 s, EW (k v1 v2 s)) :
    EW (s.loadPairK lk xcl a w k) := by
  unfold MachineData.loadPairK; ew

theorem ew_store {a : BitVec 64} {v : MemWidth.W64.type} {k : MachineData → Effects}
    (h : ∀ s, EW (k s)) : EW (s.store a v k) := by
  unfold MachineData.store; ew

theorem ew_storeK {sk : StoreKind} {xcl : Bool} {a : BitVec 64} {v : MemWidth.W64.type}
    {k : Bool → MachineData → Effects} (h : ∀ b s, EW (k b s)) : EW (s.storeK sk xcl a v k) := by
  unfold MachineData.storeK; ew

theorem ew_rmwK {rk : RmwKind} {nr : Bool} {a : BitVec 64} {op : MemWidth.W64.type → Option MemWidth.W64.type}
    {k : MemWidth.W64.type → MachineData → Effects} (h : ∀ v s, EW (k v s)) :
    EW (s.rmwK rk nr a .W64 op k) := by
  unfold MachineData.rmwK
  apply EW.require_read_access; intro; apply EW.require_write_access; intro
  split
  · dsimp only; split <;> exact h _ _
  · exact EW.rmw fun _ _ => h _ _

theorem ew_interpBase {b : RegOrSp .W64} {k : BitVec 64 → Effects} (h : ∀ a, EW (k a)) :
    EW (b.interpBase s k) := by
  unfold RegOrSp.interpBase; ew

theorem ew_checkSP {m : AddrExpr} {k : Unit → Effects} (h : ∀ u, EW (k u)) : EW (m.checkSPAlignment s k) := by
  unfold AddrExpr.checkSPAlignment; ew

theorem ew_checkSPU {m : UnscaledAddrExpr} {k : Unit → Effects} (h : ∀ u, EW (k u)) :
    EW (m.checkSPAlignment s k) := by
  unfold UnscaledAddrExpr.checkSPAlignment; ew

end Combinators

/-- `ew` with the memory combinators. -/
local macro "ewm" : tactic => `(tactic| repeat (first
  | assumption
  | (apply ew_load; intros) | (apply ew_loadK; intros) | (apply ew_loadPairK; intros)
  | (apply ew_store; intros) | (apply ew_storeK; intros) | (apply ew_rmwK; intros)
  | (apply ew_interpBase; intros) | (apply ew_checkSP; intros) | (apply ew_checkSPU; intros)
  | apply EW.done | apply EW.unimplemented | apply EW.unaligned_sp
  | (apply EW.undefined; intros) | (apply EW.require_exec_access; intros) | (apply EW.fence; intros)
  | (apply EW.syscall; intros)
  | split
  | apply_assumption))

/-- **An operation of the fragment has one-word effects**, given one-word
continuations. -/
theorem interp_ew [Labels] {w : RegWidth} (op : Operation w) (hw : op.wideOk = true) (p : Std.Rco Int64)
    (s : MachineData) {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, EW (next s)) (hj : ∀ pc s, EW (jmp pc s)) : EW (op.interp p s next jmp) := by
  cases w <;> cases op
  all_goals first | (simp [Operation.wideOk] at hw; done) | skip
  all_goals try (revert hw; cases ‹MemWidth› <;> intro hw <;> try cases hw)
  all_goals (simp only [Operation.interp, AddrOrLit.interpLoad, AddrExpr.interpLoad, AddrExpr.interpStore,
    UnscaledAddrExpr.interpLoad, UnscaledAddrExpr.interpStore, Literal.interpLoad, MachineData.setRegOrZr]
    <;> ewm)

theorem directive_ew [Labels] {d : Directive} (hd : d.wideOk = true) (s : MachineData) (p : Std.Rco Int64)
    {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    (hn : ∀ s, EW (next s)) (hj : ∀ pc s, EW (jmp pc s)) : EW (d.interp s p next jmp) := by
  cases d with
  | label => exact hn s
  | instr i => exact EW.require_exec_access fun _ => interp_ew i.operation hd p s hn hj
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
def WideSt (s : State) : Prop := DeclsWide s.decls ∧ ExeWide s.exe

theorem mem_of_mem_directivesAtAddress {e : _root_.Executable} {a : Int64} {c : Directive × Nat}
    (h : c ∈ Kraken.Executable.directivesAtAddress e a) : c ∈ e.2 := by
  obtain ⟨start, ds⟩ := e
  unfold Kraken.Executable.directivesAtAddress at h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  have hx' : x ∈ Kraken.Executable.withAddresses (start, ds) :=
    (List.dropWhile_suffix _).subset ((List.takeWhile_prefix _).subset hx)
  rw [← Kraken.Executable.withAddresses_map_snd ds start]
  exact List.mem_map_of_mem hx'

theorem mem_of_cell {s : State} {c : Directive × Nat} (h : s.cell = some c) : c ∈ s.exe.2 := by
  unfold State.cell at h
  have hc := (List.dropWhile_suffix _).subset (List.mem_of_mem_head? h)
  unfold Kraken.Executable.directivesFromAddress at hc
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
  have hx' := (List.dropWhile_suffix _).subset hx
  revert hx'
  generalize s.exe = e
  obtain ⟨start, ds⟩ := e
  intro hx'
  rw [← Kraken.Executable.withAddresses_map_snd ds start]
  exact List.mem_map_of_mem hx'

theorem mem_of_directive {s : State} {d : Directive} (h : s.directive = some d) : ∃ z, (d, z) ∈ s.exe.2 := by
  unfold State.directive at h
  obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
  exact ⟨c.2, mem_of_cell (s := s) hc⟩

theorem step_ew {e : _root_.Executable} (he : ExeWide e) (st : MachineState) :
    EW (_root_.Executable.step e st fun s' => .done s') := by
  unfold _root_.Executable.step
  letI := _root_.Executable.labels e
  exact directives_ew (fun _ _ => EW.done _) _ (fun c hc => he c (mem_of_mem_directivesAtAddress hc)) _ _

theorem lse2Effects_ew {s : State} (he : ExeWide s.exe) {e : Effects} (h : lse2Effects s = some e) : EW e := by
  unfold lse2Effects at h
  split at h
  split at h
  · rename_i d z hc
    have hd := he _ (mem_of_cell hc)
    unfold Directive.interpLSE2? at h
    split at h
    · rename_i _ _ src
      generalize @AddrExpr.eval (_root_.Executable.labels s.exe) src _ _ = r at h
      obtain ⟨addr, s'⟩ := r
      by_cases ha : (addr % 16 != 0) = true <;>
        simp only [ha, ↓reduceIte, Option.some.injEq, reduceCtorEq, Bool.false_eq_true] at h
      subst h
      exact ew_checkSP fun _ => ew_loadPairK fun _ _ _ => by ewm
    · simp [Directive.wideOk, Operation.wideOk] at hd
    · cases h
  · cases h

/-- **The FEAT_LSE2 semantics on the fragment writes words only.** -/
theorem execLSE2_w8 {s : State} (hs : WideSt s) {t : EvTree State} (h : execLSE2 s = some t) : Wide8Tree t := by
  unfold execLSE2 at h
  split at h
  · cases h
  · split at h
    · rename_i e he
      cases h
      exact wide8Tree_map _ (toEv_w8 hs.1 (lse2Effects_ew hs.2 he))
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
          exact wide8Tree_map _ (toEv_w8 hs.1 (step_ew hs.2 _))

open Scc.Sem in
/-- **The canonical AArch64 certification semantics on the fragment writes
words only.** At a supported system call it is a choice among `done`s;
otherwise it is `execLSE2`. -/
theorem certExec_w8 {s : State} (hs : WideSt s) {t : EvTree State} (h : Kernel.certExec A64.abi s = some t) :
    Wide8Tree t := by
  unfold Kernel.certExec at h
  split at h
  · split at h
    · cases h; exact fun _ => trivial
    · exact execLSE2_w8 hs h
  · exact execLSE2_w8 hs h

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

/-- **`toEv` of one-word effects writes 64-bit values only.** -/
theorem toEv_fit {ds : Decls} {e : Effects} (h : EW e) : Fit64Tree (toEv ds e) := by
  induction h with
  | done | unimplemented | unaligned_sp | syscall => simp only [toEv]; trivial
  | nonmem_load _ ih | sync_load _ ih =>
    simp only [toEv]; exact access_fit fun _ v => ih _ _
  | nonmem_store _ ih =>
    simp only [toEv]; exact access_fit fun _ => ⟨fit64_setWidth _ _, fun _ => ih _⟩
  | sync_store _ ih =>
    simp only [toEv]; exact access_fit fun _ => ⟨fit64_setWidth _ _, fun _ => ih _ _⟩
  | rmw _ ih =>
    simp only [toEv]
    refine access_fit fun l => ⟨fun old v he => ?_, fun _ => ih _ _⟩
    obtain ⟨x, -, rfl⟩ := Option.map_eq_some_iff.mp he
    exact fit64_setWidth _ x
  | fence _ ih => simp only [toEv]; exact fun _ => ih _
  | require_read_access _ ih | require_write_access _ ih | require_exec_access _ ih =>
    simp only [toEv]; exact ih _
  | @undefined α inst ret _ ih =>
    cases inst <;> simp only [toEv]
    all_goals first | trivial | exact fun i => ih _
  | sync_load_pair _ ih =>
    simp only [toEv]
    split
    · exact access_fit fun _ v => ih _ _ _
    · exact access_fit fun _ v1 => access_fit fun _ v2 => ih _ _ _

/-- **The FEAT_LSE2 semantics on the fragment writes 64-bit values only.** -/
theorem execLSE2_fit {s : State} (hs : WideSt s) {t : EvTree State} (h : execLSE2 s = some t) : Fit64Tree t := by
  unfold execLSE2 at h
  split at h
  · cases h
  · split at h
    · rename_i e he
      cases h
      exact fit64Tree_map _ (toEv_fit (lse2Effects_ew hs.2 he))
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
          exact fit64Tree_map _ (toEv_fit (step_ew hs.2 _))

open Scc.Sem in
/-- **The canonical AArch64 certification semantics on the fragment writes
64-bit values only.** -/
theorem certExec_fit {s : State} (hs : WideSt s) {t : EvTree State} (h : Kernel.certExec A64.abi s = some t) :
    Fit64Tree t := by
  unfold Kernel.certExec at h
  split at h
  · split at h
    · cases h; exact fun _ => trivial
    · exact execLSE2_fit hs h
  · exact execLSE2_fit hs h

/-- **`Fit64CodeOn` for the canonical AArch64 certification semantics** on
the fragment. -/
theorem fit64CodeOn : Fit64CodeOn WideSt (Kernel.certExec A64.abi) :=
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

/-- Every leaf of `execLSE2` keeps the executable and the declarations: an
instruction changes the machine state only. -/
theorem execLSE2_leaf {s : State} {t : EvTree State} (h : execLSE2 s = some t) {s' : State} (hl : TreeLeaf t s') :
    s'.exe = s.exe ∧ s'.decls = s.decls := by
  unfold execLSE2 exec at h
  split at h
  · cases h
  · split at h
    · cases h; obtain ⟨_, rfl⟩ := leaf_map _ hl; exact ⟨rfl, rfl⟩
    · split at h
      · cases h; obtain ⟨_, rfl⟩ := leaf_map _ hl; exact ⟨rfl, rfl⟩
      · cases h; obtain ⟨_, rfl⟩ := leaf_map _ hl; exact ⟨rfl, rfl⟩

open Scc.Sem in
/-- **Every leaf of the certification semantics keeps the executable and the
declarations**, the system-call returns (`certSuccs`) included. -/
theorem certExec_leaf {s : State} {t : EvTree State} (h : Kernel.certExec A64.abi s = some t) {s' : State}
    (hl : TreeLeaf t s') : s'.exe = s.exe ∧ s'.decls = s.decls := by
  unfold Kernel.certExec at h
  split at h
  · split at h
    · rename_i call _
      have hm : ∀ x ∈ Kernel.certSuccs A64.abi s call, x.exe = s.exe ∧ x.decls = s.decls := by
        intro x hx
        unfold Kernel.certSuccs at hx
        split at hx
        · simp only [List.mem_singleton] at hx; subst hx; exact ⟨rfl, rfl⟩
        · obtain ⟨_, -, he⟩ := List.mem_map.mp hx; subst he; exact ⟨rfl, rfl⟩
      cases h
      obtain ⟨i, rfl⟩ := hl
      exact hm _ (List.getElem_mem _)
    · exact execLSE2_leaf h hl
  · exact execLSE2_leaf h hl

open Scc.Sem in
/-- **The fragment is kept along a run**: every leaf of the certification
semantics from a `WideSt` state is `WideSt`. -/
theorem wideSt_leaf {s : State} (hs : WideSt s) {t : EvTree State} (h : Kernel.certExec A64.abi s = some t)
    {s' : State} (hl : TreeLeaf t s') : WideSt s' := by
  obtain ⟨he, hd⟩ := certExec_leaf h hl
  exact ⟨hd ▸ hs.1, he ▸ hs.2⟩

/-- **`Wide8CodeOn` for the canonical AArch64 certification semantics** on
the fragment. -/
theorem wide8CodeOn : Wide8CodeOn WideSt (Kernel.certExec A64.abi) :=
  fun _ _ hs h => certExec_w8 hs h

/-- **`WideInv` for the canonical AArch64 certification semantics**: the
fragment is kept by every leaf. -/
theorem wideInv : WideInv WideSt (Kernel.certExec A64.abi) :=
  fun _ _ _ hs h hl => wideSt_leaf hs h hl

/-! ## The solo projection on the fragment

The certification semantics of the canonical target is `Kernel.soloExec`
(`Kernel.certSem`): the ISA's `exec`, or a quiet tree whose leaves are solo
leaves (`Kernel.SoloLeaf`), which change the machine state only. -/

open Scc.Sem in
/-- **A solo leaf keeps the fragment**: `ret`, `setTp`, `setDmem` and `skip`
change the machine state only. -/
theorem wideSt_soloLeaf {s s' : State} (hs : WideSt s) (h : Kernel.SoloLeaf A64.abi s s') : WideSt s' := by
  rcases h with rfl | ⟨m, rfl⟩ | ⟨r, rfl⟩ | ⟨a, r, rfl⟩ | ⟨m, r, rfl⟩ <;> exact hs

open Scc.Sem in
/-- `Wide8CodeOn WideSt` of the AArch64 semantics. -/
theorem exec_wide8CodeOn : Wide8CodeOn WideSt isaLSE2.exec :=
  fun _ _ hs h => execLSE2_w8 hs h

open Scc.Sem in
/-- `WideInv WideSt` of the AArch64 semantics. -/
theorem exec_wideInv : WideInv WideSt isaLSE2.exec :=
  fun _ _ _ hs h hl => by
    obtain ⟨he, hd⟩ := execLSE2_leaf h hl
    exact ⟨hd ▸ hs.1, he ▸ hs.2⟩

open Scc.Sem in
/-- `Fit64CodeOn WideSt` of the AArch64 semantics. -/
theorem exec_fit64CodeOn : Fit64CodeOn WideSt isaLSE2.exec :=
  fun _ _ hs h => execLSE2_fit hs h

open Scc.Sem in
/-- **`Wide8CodeOn` for the canonical AArch64 certification semantics**
(`Kernel.soloExec`) on the fragment. -/
theorem soloWide8CodeOn (μ : Marks) (x : Kernel.KState) (tid : Nat) :
    Wide8CodeOn WideSt (Kernel.soloExec A64.abi Arch.armv8 μ x tid) :=
  Kernel.soloExec_wide8CodeOn exec_wide8CodeOn

open Scc.Sem in
/-- **`WideInv` for the canonical AArch64 certification semantics**
(`Kernel.soloExec`): the fragment is kept by every leaf. -/
theorem soloWideInv (μ : Marks) (x : Kernel.KState) (tid : Nat) :
    WideInv WideSt (Kernel.soloExec A64.abi Arch.armv8 μ x tid) :=
  Kernel.soloExec_wideInv exec_wideInv fun _ _ hs h => wideSt_soloLeaf hs h

open Scc.Sem in
/-- **`Fit64CodeOn` for the canonical AArch64 certification semantics**
(`Kernel.soloExec`) on the fragment. -/
theorem soloFit64CodeOn (μ : Marks) (x : Kernel.KState) (tid : Nat) :
    Fit64CodeOn WideSt (Kernel.soloExec A64.abi Arch.armv8 μ x tid) :=
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

/-- **The canonical thread of a program of the fragment is `WideSt`**
(`A64.threadAt`: no declarations; the program, then data and label cells). -/
theorem wideSt_threadAt {prog : Program} (hw : wideIn prog = true) (E : Scc.Sem.Entry) (base : Nat)
    (syms : List (String × Nat)) : WideSt (Scc.Sem.A64.threadAt E base prog syms) := by
  refine ⟨declsWide_empty, ?_⟩
  intro c hc
  simp only [Scc.Sem.A64.threadAt, List.mem_append, List.mem_map] at hc
  rcases hc with (hc | ⟨d, hd, rfl⟩) | hc
  · exact placeBelow_wideOk c hc
  · exact List.all_eq_true.mp hw d hd
  · exact placeSyms_wideOk c hc

end Scc.Cert.WideA64
