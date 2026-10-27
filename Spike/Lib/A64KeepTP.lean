/-
**`TPIDR_EL0` kept across a segment on AArch64**: a segment whose states
execute no `MSR` and whose environment moves keep `TPIDR_EL0` carries
`TPIDR_EL0 = t` from its start to its exits.

- `setXReg_tp`, `setRegOrSp64_tp`, `setRegOrZr64_tp`, `setRegOrSp_tp`,
  `setRegOrZr_tp`: register writes leave `TPIDR_EL0` alone;
- `EAll`, `TAll`: a predicate on every register file in an effect, resp. an
  event tree;
- `isMsr`, `dNoMsr`, `all_interp`, `all_dinterp`: every non-`MSR` operation
  and decoded instruction keeps `TPIDR_EL0`;
- `TP`, `NoMsrAt`: `TPIDR_EL0 = t`; the state's cell decodes to no `MSR`;
- `exec_tp`, `certSuccs_tp`, `out_tp`: one step keeps `TPIDR_EL0`;
- `tpXa`: the `xa` exit additionally assuming `TPIDR_EL0 = t`;
- `SegW.keepTP`: the segment with `TPIDR_EL0 = t` conjoined at the start and
  at every exit; `SegW.keepTP'`: into a `W` asked only at `TPIDR_EL0 = t`.
-/
import Spike.Lib.A64Cfg

namespace Spike.Lib.A64.KeepTP

open Kraken Kraken.Promising Kraken.Promising.AArch64

set_option linter.unusedSimpArgs false

/-! ## Registers -/

theorem setXReg_tp (r : Reg64s) (x : XReg) (v : BitVec 64) : (r.setXReg x v).TPIDR_EL0 = r.TPIDR_EL0 := by
  cases x <;> rfl

theorem setRegOrSp64_tp (r : Reg64s) (x : XRegOrSp) (v : BitVec 64) :
    (r.setRegOrSp64 x v).TPIDR_EL0 = r.TPIDR_EL0 := by
  cases x <;> simp [Reg64s.setRegOrSp64, setXReg_tp]

theorem setRegOrZr64_tp (r : Reg64s) (x : XRegOrXzr) (v : BitVec 64) :
    (r.setRegOrZr64 x v).TPIDR_EL0 = r.TPIDR_EL0 := by
  cases x <;> simp [Reg64s.setRegOrZr64, setXReg_tp]

theorem setRegOrSp_tp {w} (r : Reg64s) (x : RegOrSp w) (v : w.type) :
    (r.setRegOrSp x v).TPIDR_EL0 = r.TPIDR_EL0 := by
  rcases x with ⟨x, _ | _⟩ <;> simp [Reg64s.setRegOrSp, setRegOrSp64_tp]

theorem setRegOrZr_tp {w} (r : Reg64s) (x : RegOrZr w) (v : w.type) :
    (r.setRegOrZr x v).TPIDR_EL0 = r.TPIDR_EL0 := by
  rcases x with ⟨x, _ | _⟩ <;> simp [Reg64s.setRegOrZr, setRegOrZr64_tp]

/-! ## Effects -/

/-- **Every outcome of an effect tree satisfies `P`**: every `done` leaf
reached for any answer of its events. -/
def EAll (P : MachineData × Int64 → Prop) : Effects → Prop
  | .done a => P a
  | .unimplemented _ => True
  | .nonmem_load _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .nonmem_store _ _ _ ret => ∀ d, EAll P (ret d)
  | @Effects.undefined α _ ret => ∀ a : α, EAll P (ret a)
  | .require_read_access _ _ ok => EAll P (ok ())
  | .require_write_access _ _ ok => EAll P (ok ())
  | .require_exec_access _ ok => EAll P (ok ())
  | .unaligned_sp _ => True
  | .sync_load _ _ _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .sync_store _ _ _ _ _ ret => ∀ b d, EAll P (ret b d)
  | .rmw _ _ _ _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .fence _ ok => EAll P (ok ())
  | .sync_load_pair _ _ _ _ _ ret => ∀ v1 v2 d, EAll P (ret v1 v2 d)
  | .sync_store_pair _ _ _ _ _ _ ret => ∀ b d, EAll P (ret b d)
  | .rmw_pair _ _ _ _ _ _ _ ret => ∀ v1 v2 d, EAll P (ret v1 v2 d)
  | .syscall _ ret => ∀ r, EAll P (ret r)

/-- A continuation from machine data with thread pointer `t` ends in `P`. -/
abbrev KOk (P : MachineData × Int64 → Prop) (t : UInt64) (k : MachineData → Effects) : Prop :=
  ∀ m : MachineData, m.regs.TPIDR_EL0 = t → EAll P (k m)

section Helpers

variable {P : MachineData × Int64 → Prop} {t : UInt64} {s : MachineData}

theorem all_setRegOrZr {w} {r : RegOrZr w} {v : w.type} {k : MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : KOk P t k) : EAll P (s.setRegOrZr r v k) :=
  hk _ (by simp only [setRegOrZr_tp, hs])

theorem all_setRegOrSp {w} {r : RegOrSp w} {v : w.type} {k : MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : KOk P t k) : EAll P (s.setRegOrSp r v k) :=
  hk _ (by simp only [setRegOrSp_tp, hs])

theorem all_load {addr : BitVec 64} {w : MemWidth} {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.load addr w ret) := by
  unfold MachineData.load
  simp only [EAll]
  split
  · exact hk _ _ hs
  · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_store {addr : BitVec 64} {w : MemWidth} {v : w.type} {k : MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : KOk P t k) : EAll P (s.store addr v k) := by
  unfold MachineData.store
  simp only [EAll]
  split
  · exact hk _ hs
  · simp only [EAll]; exact fun d => hk _ hs

theorem all_loadK {k' : Kraken.LoadKind} {x : Bool} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.loadK k' x addr w ret) := by
  unfold MachineData.loadK
  simp only [EAll]
  split
  · exact hk _ _ hs
  · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_storeK {k' : Kraken.StoreKind} {x : Bool} {addr : BitVec 64} {w : MemWidth} {v : w.type}
    {ret : Bool → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ b, KOk P t (ret b)) : EAll P (s.storeK k' x addr v ret) := by
  unfold MachineData.storeK
  simp only [EAll]
  split
  · split
    · simp only [EAll]; intro b; split <;> exact hk _ _ hs
    · exact hk _ _ hs
  · simp only [EAll]; exact fun b d => hk _ _ hs

theorem all_rmwK {k' : Kraken.RmwKind} {nr : Bool} {addr : BitVec 64} {w : MemWidth}
    {op : w.type → Option w.type} {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.rmwK k' nr addr w op ret) := by
  unfold MachineData.rmwK
  simp only [EAll]
  split
  · split
    · exact hk _ _ hs
    · exact hk _ _ hs
  · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_loadPairK {k' : Kraken.LoadKind} {x : Bool} {addr : BitVec 64} {w : MemWidth}
    {ret : w.type → w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v1 v2, KOk P t (ret v1 v2)) :
    EAll P (s.loadPairK k' x addr w ret) := by
  unfold MachineData.loadPairK
  simp only [EAll]
  split <;> (try simp only [EAll])
  · exact hk _ _ _ hs
  · exact fun v1 v2 d => hk _ _ _ hs
  · exact fun v d => hk _ _ _ hs
  · exact fun v d => hk _ _ _ hs

theorem all_storePairK {k' : Kraken.StoreKind} {x : Bool} {addr : BitVec 64} {w : MemWidth} {v1 v2 : w.type}
    {ret : Bool → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ b, KOk P t (ret b)) : EAll P (s.storePairK k' x addr v1 v2 ret) := by
  unfold MachineData.storePairK
  simp only [EAll]
  split <;> (try simp only [EAll])
  · split
    · simp only [EAll]; intro b; split <;> exact hk _ _ hs
    · exact hk _ _ hs
  · exact fun b d => hk _ _ hs
  · intro b d; split <;> exact hk _ _ hs
  · intro b d; split <;> exact hk _ _ hs

theorem all_rmwPairK {k' : Kraken.RmwKind} {addr : BitVec 64} {w : MemWidth} {c1 c2 n1 n2 : w.type}
    {ret : w.type → w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v1 v2, KOk P t (ret v1 v2)) :
    EAll P (s.rmwPairK k' addr c1 c2 n1 n2 ret) := by
  unfold MachineData.rmwPairK
  simp only [EAll]
  split <;> (try simp only [EAll])
  · split <;> exact hk _ _ _ hs
  · exact fun v1 v2 d => hk _ _ _ hs
  · intro v d; split <;> exact hk _ _ _ hs
  · intro v d; split <;> exact hk _ _ _ hs

theorem all_interpBase {b : RegOrSp .W64} {ok : BitVec 64 → Effects} (hk : ∀ a, EAll P (ok a)) :
    EAll P (b.interpBase s ok) := by
  unfold RegOrSp.interpBase
  split
  · split
    · simp only [EAll]
    · exact hk _
  · exact hk _

theorem all_checkSP {mem : AddrExpr} {ok : Unit → Effects} (hk : EAll P (ok ())) :
    EAll P (mem.checkSPAlignment s ok) := by
  unfold AddrExpr.checkSPAlignment
  split
  · split
    · simp only [EAll]
    · exact hk
  · exact hk

theorem all_checkSPU {mem : UnscaledAddrExpr} {ok : Unit → Effects} (hk : EAll P (ok ())) :
    EAll P (mem.checkSPAlignment s ok) := by
  unfold UnscaledAddrExpr.checkSPAlignment
  split
  · split
    · simp only [EAll]
    · exact hk
  · exact hk

theorem eval_tp [Labels] (mem : AddrExpr) (p : Std.Rco Int64) :
    (mem.eval s p).2.regs.TPIDR_EL0 = s.regs.TPIDR_EL0 := by
  unfold AddrExpr.eval
  split
  · rfl
  · rename_i i _
    cases i.index <;> simp [setRegOrSp_tp]

theorem all_interpLoad [Labels] {mem : AddrExpr} {p : Std.Rco Int64} {w : MemWidth}
    {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (mem.interpLoad s p ret) := by
  unfold AddrExpr.interpLoad
  refine all_checkSP ?_
  exact all_load ((eval_tp mem p).trans hs) hk

theorem all_interpStore [Labels] {mem : AddrExpr} {p : Std.Rco Int64} {w : MemWidth} {v : w.type}
    {k : MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : KOk P t k) : EAll P (mem.interpStore s p v k) := by
  unfold AddrExpr.interpStore
  refine all_checkSP ?_
  exact all_store ((eval_tp mem p).trans hs) hk

theorem all_interpLoadU [Labels] {mem : UnscaledAddrExpr} {p : Std.Rco Int64} {w : MemWidth}
    {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (mem.interpLoad s p ret) := by
  unfold UnscaledAddrExpr.interpLoad
  exact all_checkSPU (all_load hs hk)

theorem all_interpStoreU [Labels] {mem : UnscaledAddrExpr} {p : Std.Rco Int64} {w : MemWidth} {v : w.type}
    {k : MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : KOk P t k) : EAll P (mem.interpStore s p v k) := by
  unfold UnscaledAddrExpr.interpStore
  exact all_checkSPU (all_store hs hk)

theorem all_litLoad [Labels] {e : Literal} {p : Std.Rco Int64} {w : MemWidth}
    {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (e.interpLoad s p ret) := by
  unfold Literal.interpLoad
  split
  · exact all_load hs hk
  · exact hk _ _ hs

theorem all_addrOrLitLoad [Labels] {e : AddrOrLit} {p : Std.Rco Int64} {w : MemWidth}
    {ret : w.type → MachineData → Effects}
    (hs : s.regs.TPIDR_EL0 = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (e.interpLoad s p ret) := by
  unfold AddrOrLit.interpLoad
  split
  · exact all_interpLoad hs hk
  · exact all_litLoad hs hk

theorem all_pending {imm : Nat} {k : MachineData → Effects} (hs : s.regs.TPIDR_EL0 = t) (hk : KOk P t k) :
    EAll P (s.pendingSyscall imm k) := by
  unfold MachineData.pendingSyscall
  simp only [EAll]
  exact fun r => hk _ (by simp only [setXReg_tp, hs])

end Helpers

/-! ## One operation -/

/-- An `MSR` (the only write of the thread pointer). -/
def isMsr {w} : Operation w → Bool
  | .MSR _ _ => true
  | _ => false

/-- The steps of `all_interp`: a continuation's facts, one helper. -/
macro "tp_step" : tactic => `(tactic| first
  | (intro)
  | (apply all_setRegOrZr (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_setRegOrSp (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_interpLoad (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_interpStore (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_interpLoadU (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_interpStoreU (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_addrOrLitLoad (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_litLoad (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_load (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_store (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_loadK (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_storeK (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_rmwK (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_loadPairK (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_storePairK (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_rmwPairK (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_pending (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp]))
  | (apply all_interpBase)
  | (apply all_checkSP)
  | (apply all_checkSPU)
  | (simp only [EAll])
  | split)

/-- **One operation other than `MSR` keeps the thread pointer**: every
outcome of its effects, from machine data with thread pointer `t` and
continuations that end in `P` from any such data, ends in `P`. -/
theorem all_interp [Labels] {w} (op : Operation w) (hop : isMsr op = false) (p : Std.Rco Int64)
    {s : MachineData} {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    {P : MachineData × Int64 → Prop} {t : UInt64}
    (hs : s.regs.TPIDR_EL0 = t) (hn : KOk P t next) (hj : ∀ pc, KOk P t (jmp pc)) :
    EAll P (Operation.interp op p s next jmp) := by
  cases op <;> (try simp only [isMsr, Bool.true_eq_false] at hop) <;> simp only [Operation.interp] <;>
    repeat' (first
      | exact hn _ (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp])
      | exact hj _ _ (by first | assumption | simp_all [setRegOrZr_tp, setRegOrSp_tp, setXReg_tp])
      | tp_step)

/-! ## A directive -/

/-- A directive other than an `MSR`. -/
def dNoMsr : Directive → Bool
  | .instr i => !isMsr i.operation
  | _ => true

theorem all_dinterp [Labels] {d : Directive} (hd : dNoMsr d = true) (p : Std.Rco Int64)
    {s : MachineData} {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    {P : MachineData × Int64 → Prop} {t : UInt64}
    (hs : s.regs.TPIDR_EL0 = t) (hn : KOk P t next) (hj : ∀ pc, KOk P t (jmp pc)) :
    EAll P (d.interp s p next jmp) := by
  unfold Directive.interp
  split
  · exact hn _ hs
  · rename_i i
    simp only [dNoMsr, Bool.not_eq_eq_eq_not, Bool.not_true] at hd
    simp only [Instr.interp, require_exec_access, EAll]
    exact all_interp _ hd p hs hn hj
  · simp only [EAll]

theorem all_dinterpLSE2? [Labels] {d : Directive} (p : Std.Rco Int64)
    {s : MachineData} {next : MachineData → Effects} {e : Effects}
    {P : MachineData × Int64 → Prop} {t : UInt64}
    (hs : s.regs.TPIDR_EL0 = t) (hn : KOk P t next) (he : d.interpLSE2? s p next = some e) : EAll P e := by
  unfold Directive.interpLSE2? at he
  split at he
  · rename_i src
    split at he
    rename_i addr s' heq
    split at he
    · cases he
    · cases he
      have hs' : s'.regs.TPIDR_EL0 = t := by
        have := eval_tp (s := s) src p
        rw [heq] at this; exact this.trans hs
      exact all_checkSP (all_loadPairK hs' fun v1 v2 m hm =>
        all_setRegOrZr hm fun m' hm' => all_setRegOrZr hm' hn)
  · rename_i dst
    split at he
    rename_i addr s' heq
    split at he
    · cases he
    · cases he
      have hs' : s'.regs.TPIDR_EL0 = t := by
        have := eval_tp (s := s) dst p
        rw [heq] at this; exact this.trans hs
      exact all_checkSP (all_storePairK hs' fun b m hm => hn m hm)
  · cases he

/-! ## Event trees -/

/-- **Every leaf of an event tree satisfies `P`**, for any answer of its
events. -/
def TAll {σ : Type} (P : σ → Prop) : EvTree σ → Prop
  | .done s => P s
  | .fault _ => True
  | .choose _ k => ∀ i, TAll P (k i)
  | .load _ _ _ ret => ∀ v, TAll P (ret v)
  | .store _ _ _ _ ret => ∀ b, TAll P (ret b)
  | .rmw _ _ _ _ ret => ∀ v, TAll P (ret v)
  | .fence _ ret => ∀ u, TAll P (ret u)

theorem tall_access {σ : Type} {P : σ → Prop} {ds : Decls} {a : BitVec 64} {n : Nat} {k : Loc → EvTree σ}
    (h : ∀ l, TAll P (k l)) : TAll P (EvTree.access ds a n k) := by
  unfold EvTree.access
  split
  · exact h _
  · simp only [TAll]

theorem tall_map {σ τ : Type} {P : τ → Prop} (f : σ → τ) :
    ∀ {tr : EvTree σ}, TAll (fun s => P (f s)) tr → TAll P (tr.map f)
  | .done _, h => h
  | .fault _, _ => trivial
  | .choose _ _, h => fun i => tall_map f (h i)
  | .load .., h => fun v => tall_map f (h v)
  | .store .., h => fun b => tall_map f (h b)
  | .rmw .., h => fun v => tall_map f (h v)
  | .fence .., h => fun u => tall_map f (h u)

theorem tall_caspTree {σ : Type} {P : σ → Prop} {ds : Decls} {k : RmwKind} {addr : BitVec 64} {w : MemWidth}
    {c1 c2 n1 n2 : w.type} {ret : w.type → w.type → EvTree σ} (h : ∀ o1 o2, TAll P (ret o1 o2)) :
    TAll P (caspTree ds k addr c1 c2 n1 n2 ret) := by
  unfold caspTree
  simp only [TAll]
  intro succ rev
  split
  · refine tall_access fun l v => tall_access fun l' v' => ?_
    dsimp only
    split
    · exact h _ _
    · intro i; exact i.elim0
  · refine tall_access fun l v => tall_access fun l' v' => ?_
    dsimp only
    split
    · exact h _ _
    · intro i; exact i.elim0

theorem tall_toEv (ds : Decls) {P : MachineData × Int64 → Prop} (e : Effects) :
    EAll P e → TAll P (toEv ds e) := by
  induction e with
  | done a => exact id
  | unimplemented _ => intro _; trivial
  | nonmem_load dmem addr w ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | @nonmem_store dmem addr w v ret ih => intro h; exact tall_access fun _ _ => ih _ (h _)
  | @undefined α inst ret ih =>
    intro h
    cases inst with
    | bool => exact fun i => ih _ (h _)
    | bitvec _ => trivial
    | statusFlags => trivial
  | require_read_access _ _ ok ih => intro h; exact ih () h
  | require_write_access _ _ ok ih => intro h; exact ih () h
  | require_exec_access _ ok ih => intro h; exact ih () h
  | @unaligned_sp _ _ => intro _; trivial
  | sync_load k x dmem addr w ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | @sync_store k x dmem addr w v ret ih => intro h; exact tall_access fun _ b => ih _ _ (h _ _)
  | rmw k nr dmem addr w op ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | fence k ok ih => intro h; exact fun _ => ih () h
  | sync_load_pair k x dmem addr w ret ih =>
    intro h
    simp only [toEv]
    split
    · exact tall_access fun _ v => ih _ _ _ (h _ _ _)
    · exact tall_access fun _ v1 => tall_access fun _ v2 => ih _ _ _ (h _ _ _)
  | @sync_store_pair k x dmem addr w v1 v2 ret ih =>
    intro h
    simp only [toEv]
    split
    · exact tall_access fun _ b => ih _ _ (h _ _)
    · refine tall_access fun _ b => ?_
      dsimp only
      split
      · exact tall_access fun _ _ => ih _ _ (h _ _)
      · exact ih _ _ (h _ _)
  | @rmw_pair k dmem addr w c1 c2 n1 n2 ret ih =>
    intro h; exact tall_caspTree fun _ _ => ih _ _ _ (h _ _ _)
  | syscall _ _ _ => intro _; trivial

theorem tall_toEvCASP (ds : Decls) {P : MachineData × Int64 → Prop} (e : Effects) :
    EAll P e → TAll P (toEvCASP ds e) := by
  induction e with
  | require_read_access _ _ ok ih => intro h; simp only [toEvCASP]; exact ih () h
  | require_write_access _ _ ok ih => intro h; simp only [toEvCASP]; exact ih () h
  | require_exec_access _ ok ih => intro h; simp only [toEvCASP]; exact ih () h
  | @rmw_pair k dmem addr w c1 c2 n1 n2 ret ih =>
    intro h
    cases w <;> simp only [toEvCASP] <;> (try split) <;> first
      | exact tall_access fun _ _ => tall_toEv ds _ (h _ _ _)
      | exact tall_toEv ds _ h
  | _ => intro h; simp only [toEvCASP]; exact tall_toEv ds _ h

/-- A silent tree whose leaves all satisfy `Q` is silent with `Q` added. -/
theorem silent_and {σ : Type} {P Q : σ → Prop} :
    ∀ {tr : EvTree σ}, Lower.SilentTree P tr → TAll Q tr → Lower.SilentTree (fun s => P s ∧ Q s) tr
  | .done _, h, q => ⟨h, q⟩
  | .choose _ _, h, q => ⟨h.1, fun i => silent_and (h.2 i) (q i)⟩
  | .fault _, h, _ => h.elim
  | .load .., h, _ => h.elim
  | .store .., h, _ => h.elim
  | .rmw .., h, _ => h.elim
  | .fence .., h, _ => h.elim

/-! ## A step of `isaLSE2` -/

/-- The thread pointer of a state is `t`. -/
abbrev TP (t : UInt64) (s : State) : Prop := s.st.1.regs.TPIDR_EL0 = t

/-- **A state at a cell other than an `MSR`.** -/
def NoMsrAt (s : State) : Prop := ∃ d sz, Lower.A64.CellAt s d sz ∧ dNoMsr d = true

/-- **A step at a cell other than an `MSR` keeps the thread pointer**: every
leaf of its event tree. -/
theorem exec_tp {s : State} {t : UInt64} (hc : NoMsrAt s) (hs : TP t s) {tr : EvTree State}
    (he : isaLSE2.exec s = some tr) : TAll (TP t) tr := by
  obtain ⟨d, sz, hc, hd⟩ := hc
  letI := _root_.Executable.labels s.exe
  cases hx : d.isCaspX
  · rw [show isaLSE2.exec s = execLSE2 s from rfl, Lower.A64.execLSE2_of_cellAt hc hx] at he
    cases he
    refine tall_map _ (tall_toEv _ _ ?_)
    unfold Directive.interpLSE2
    cases h2 : d.interpLSE2? s.st.1 (.mk s.st.2 (s.st.2 + .ofNat sz)) (Lower.A64.nextS s sz) with
    | some e => exact all_dinterpLSE2? (next := Lower.A64.nextS s sz) _ hs (fun m hm => hm) h2
    | none =>
      exact all_dinterp (next := Lower.A64.nextS s sz) (jmp := Lower.A64.jmpS)
        hd _ hs (fun m hm => hm) (fun pc m hm => hm)
  · rw [show isaLSE2.exec s = execLSE2 s from rfl, Lower.A64.execLSE2_of_cellAt_casp hc hx] at he
    cases he
    exact tall_map _ (tall_toEvCASP _ _ (all_dinterp (next := Lower.A64.nextS s sz) (jmp := Lower.A64.jmpS)
      hd _ hs (fun m hm => hm) (fun pc m hm => hm)))

/-- `decode` on AArch64 never asks for `arch_prctl`. -/
theorem decode_a64_ne (nr : Nat) (a : Fin 6 → Nat) (x : Nat) :
    Scc.Sem.Kernel.decode Scc.Sem.Kernel.Nrs.a64 nr a ≠ some (.archSetFs x) := by
  unfold Scc.Sem.Kernel.decode
  simp only [Scc.Sem.Kernel.Nrs.a64, reduceCtorEq, false_and, ite_false]
  repeat' split
  all_goals first
    | (simp; done)
    | (by_cases hc : a 0 = Scc.Sem.Kernel.cloneFlags ∧ a 2 = 0 ∧ a 4 = 0 <;> simp [hc])

/-- **The kernel's returns keep the thread pointer** on AArch64. -/
theorem certSuccs_tp {s : State} {t : UInt64} (hs : TP t s) {call : Scc.Sem.Kernel.Call}
    (hd : Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) = some call) :
    ∀ s' ∈ Scc.Sem.Kernel.certSuccs Scc.Sem.A64.abi s call, TP t s' := by
  cases call with
  | archSetFs x => exact absurd hd (decode_a64_ne _ _ x)
  | _ =>
    intro s' hm
    simp only [Scc.Sem.Kernel.certSuccs, List.mem_map] at hm
    obtain ⟨r, -, rfl⟩ := hm
    exact hs

/-! ## Segments -/

/-- **`ms` with every allocation landing asked only at thread pointer `t`.** -/
def tpXa (ms : MemSide isaLSE2) (t : UInt64) : MemSide isaLSE2 :=
  { ms with xa := fun l b n s c => TP t s → ms.xa l b n s c }

/-- **One instruction at a cell other than an `MSR`, the thread pointer
kept**: what it does under `tpXa ms t` from a state with thread pointer `t`
it does under `ms` with `t` kept in the fragment it lands in. -/
theorem out_tp {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
    {X : Frag isaLSE2} {s : State} {c : Ctl} {t : UInt64}
    (hK : ms.K = some Scc.Sem.A64.abi) (hc : NoMsrAt s) (hs : TP t s)
    (h : Out p lbl (tpXa ms t) X s c) : Out p lbl ms (fun s c => X s c ∧ TP t s) s c := by
  have hT : ∀ tr, isaLSE2.exec s = some tr → TAll (TP t) tr := fun tr he => exec_tp hc hs he
  cases h with
  | silent s' c' he hr hx => exact .silent s' c' he hr ⟨hx, hT _ he⟩
  | choice P tr he hst hl =>
    refine .choice (fun s' => P s' ∧ TP t s') tr he (silent_and hst (hT _ he)) fun s' hp => ?_
    obtain ⟨c', hr, hx⟩ := hl s' hp.1
    exact ⟨c', hr, hx, hp.2⟩
  | load kl A g x a e ty w he h1 h2 h3 h4 h5 =>
    exact .load kl A g x a e ty w he h1 h2 h3 (fun v w' hr hv => ⟨h4 v w' hr hv, hT _ he v⟩) h5
  | store kr A V s' x a b e ty tb w wb he h1 h2 h3 h4 h5 h6 h7 =>
    exact .store kr A V s' x a b e ty tb w wb he h1 h2 h3 h4 h5 ⟨h6, hT _ he true⟩ h7
  | rtStore kr L V s' c' he h1 h2 h3 hr hx => exact .rtStore kr L V s' c' he h1 h2 h3 hr ⟨hx, hT _ he true⟩
  | rtLoad kl L g c' he h1 h2 hr hx =>
    exact .rtLoad kl L g c' he h1 h2 hr fun v hG ho => ⟨hx v hG ho, hT _ he v⟩
  | rtRmw k L op g c' he h1 h2 hr hx =>
    exact .rtRmw k L op g c' he h1 h2 hr fun old hG ho => ⟨(hx old hG ho).1, (hx old hG ho).2, hT _ he old⟩
  | sys K' call hK' hat hd hok hsc =>
    have hK2 : ms.K = some K' := hK'
    rw [hK] at hK2
    cases hK2
    refine .sys _ call hK hat hd hok fun s' hm => ?_
    obtain ⟨c', hr, hx⟩ := hsc s' hm
    exact ⟨c', hr, hx, certSuccs_tp hs hd s' hm⟩
  | holdLoad kl A g x sa u v e he h1 h2 h3 h4 =>
    exact .holdLoad kl A g x sa u v e he h1 h2 h3 fun r w' hr hv => ⟨h4 r w' hr hv, hT _ he r⟩
  | xchgStore kr A V s' x sa u v e tv wv wold he h1 h2 h3 h4 h5 h6 =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he h1 h2 h3 h4 h5 ⟨h6, hT _ he true⟩
  | ctrRmw k op g x a τ e ta ws n he h1 h2 h3 h4 h5 h6 h7 h8 =>
    exact .ctrRmw k op g x a τ e ta ws n he h1 h2 h3 h4 h5 h6 h7 fun old hG ho hle =>
      ⟨(h8 old hG ho hle).1, (h8 old hG ho hle).2, hT _ he old⟩
  | alloc s' A x a τ e ta ws k wold old us he h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .alloc s' A x a τ e ta ws k wold old us he h1 h2 h3 h4 h5 h6 h7 h8 fun l ini hl => h9 l ini hl (hT _ he)
  | emit K' buf n Pw Qw hK' hat hd h0 hb hr hq =>
    have hK2 : ms.K = some K' := hK'
    rw [hK] at hK2
    cases hK2
    exact .emit _ buf n Pw Qw hK hat hd h0 hb (fun j hj c1 hp r hm hok =>
      ⟨⟨(hr j hj c1 hp r hm hok).1, hs⟩, (hr j hj c1 hp r hm hok).2⟩) hq

/-- **A segment keeps the thread pointer**: a segment under `tpXa ms t`
(its allocation landings asked only at thread pointer `t`) whose states are
at cells other than an `MSR` (`hW`) and whose outside moves keep the thread
pointer (`hKt`) is one under `ms` with thread pointer `t` at its entry and
its exit. -/
theorem SegW.keepTP {W : Frag isaLSE2} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P Q : Frag isaLSE2} {t : UInt64}
    (hK : ms.K = some Scc.Sem.A64.abi) (h : SegW W K p lbl (tpXa ms t) P Q)
    (hW : ∀ s c, W s c → NoMsrAt s) (hKt : ∀ s c, W s c → ∀ s', K s s' → TP t s → TP t s') :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨fun s c => inv s c ∧ TP t s, fun s c hp => ⟨hP s c hp.1, hp.2⟩, fun s c h => hiW s c h.1,
    fun s c hi => ?_⟩
  obtain ⟨hout, hk⟩ := hcl s c hi.1
  refine ⟨fun hK' => (out_tp hK (hW s c (hiW s c hi.1)) hi.2 (hout hK')).mono ?_, fun s' hks => ?_⟩
  · exact fun s c hx => hx.1.elim (fun h => .inl ⟨h, hx.2⟩) fun h => .inr ⟨h, hx.2⟩
  · obtain ⟨c', hr, hx⟩ := hk s' hks
    have ht := hKt s c (hiW s c hi.1) s' hks hi.2
    exact ⟨c', hr, hx.elim (fun h => .inl ⟨h, ht⟩) fun h => .inr ⟨h, ht⟩⟩

/-- **A segment keeps the thread pointer, into a `W` relative to it**
(`SegW.keepTP` with the segment's states inside `W'`, and `W` asked only
at thread pointer `t`, `hW`): the invariant carries `t`, so its states are
in `W`. -/
theorem SegW.keepTP' {W W' : Frag isaLSE2} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P Q : Frag isaLSE2} {t : UInt64}
    (hK : ms.K = some Scc.Sem.A64.abi) (h : SegW W' K p lbl (tpXa ms t) P Q)
    (hN : ∀ s c, W' s c → NoMsrAt s) (hKt : ∀ s c, W' s c → ∀ s', K s s' → TP t s → TP t s')
    (hW : ∀ s c, W' s c → TP t s → W s c) :
    SegW W K p lbl ms (fun s c => P s c ∧ TP t s) (fun s c => Q s c ∧ TP t s) := by
  obtain ⟨inv, hP, hiW, hcl⟩ := h
  refine ⟨fun s c => inv s c ∧ TP t s, fun s c hp => ⟨hP s c hp.1, hp.2⟩,
    fun s c h => hW s c (hiW s c h.1) h.2, fun s c hi => ?_⟩
  obtain ⟨hout, hk⟩ := hcl s c hi.1
  refine ⟨fun hK' => (out_tp hK (hN s c (hiW s c hi.1)) hi.2 (hout hK')).mono ?_, fun s' hks => ?_⟩
  · exact fun s c hx => hx.1.elim (fun h => .inl ⟨h, hx.2⟩) fun h => .inr ⟨h, hx.2⟩
  · obtain ⟨c', hr, hx⟩ := hk s' hks
    have ht := hKt s c (hiW s c hi.1) s' hks hi.2
    exact ⟨c', hr, hx.elim (fun h => .inl ⟨h, ht⟩) fun h => .inr ⟨h, ht⟩⟩

end Spike.Lib.A64.KeepTP
