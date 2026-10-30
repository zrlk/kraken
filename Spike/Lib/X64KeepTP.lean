/-
**`fsBase` kept across a segment on x64**: the x64 twin of
`Spike/Lib/A64KeepTP.lean`. No x64 instruction writes the `%fs` base (only
the loader and `arch_prctl(ARCH_SET_FS)`, `Scc.Sem.X64`'s `setTp`, do), so
every instruction step keeps it; the one move that can change it is the
system call `arch_prctl`. A segment whose states are at no system call that
asks for `arch_prctl` and whose environment moves keep `fsBase` carries
`fsBase = t` from its start to its exits.

- `set64_tp`, `set_tp`: register writes leave `fsBase` alone;
- `EAll`, `TAll`: a predicate on every machine data in an effect, resp. an
  event tree;
- `all_interp`, `all_avx`, `all_dinterp`, `all_dirs`: every operation,
  directive and directive run keeps `fsBase`;
- `TP`, `NoSetFsAt`: `fsBase = t`; the state is at no system call asking
  for `arch_prctl`; `noSetFsAt_of_cell`: a state at a cell other than
  `syscall` (`dNoSys`);
- `exec_tp`, `certSuccs_tp`, `out_tp`: one step keeps `fsBase`;
- `tpXa`: the `xa` exit additionally assuming `fsBase = t`;
- `SegW.keepTP`: the segment with `fsBase = t` conjoined at the start and at
  every exit.
-/
import Spike.Lib.X64Cfg

namespace Spike.Lib.X64.KeepTP

open Kraken Kraken.Promising Kraken.Promising.X64

set_option linter.unusedSimpArgs false

/-! ## Registers -/

theorem set64_tp (r : Reg64s) (x : Reg64) (v : BitVec 64) : (r.set64 x v).fsBase = r.fsBase := by
  cases x <;> rfl

theorem set_tp {w} (r : Reg64s) (x : Reg w) (v : w.type) : (r.set x v).fsBase = r.fsBase := by
  unfold Reg64s.set
  split <;> simp only [set64_tp]

theorem setReg_tp {w} (s : MachineData) (x : Reg w) (v : w.type) : (s.setReg x v).regs.fsBase = s.regs.fsBase :=
  set_tp _ _ _

/-! ## Effects -/

/-- **Every outcome of an effect tree satisfies `P`**: every `done` leaf
reached for any answer of its events. -/
def EAll (P : MachineData × Int64 → Prop) : Effects → Prop
  | .done a => P a
  | .unimplemented _ => True
  | .gp_unaligned _ _ => True
  | .nonmem_load _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .nonmem_store _ _ _ ret => ∀ d, EAll P (ret d)
  | @Effects.undefined α _ ret => ∀ a : α, EAll P (ret a)
  | .require_read_access _ _ ok => EAll P (ok ())
  | .require_write_access _ _ ok => EAll P (ok ())
  | .require_exec_access _ ok => EAll P (ok ())
  | .sync_load _ _ _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .sync_store _ _ _ _ _ ret => ∀ b d, EAll P (ret b d)
  | .rmw _ _ _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .fence _ ok => EAll P (ok ())
  | .require_read_access_avx _ _ _ ok => EAll P (ok ())
  | .require_write_access_avx _ _ _ ok => EAll P (ok ())
  | .nonmem_load_avx _ _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .nonmem_store_avx _ _ _ _ ret => ∀ d, EAll P (ret d)
  | .rmw16 _ _ _ _ ret => ∀ v d, EAll P (ret v d)
  | .syscall _ ret => ∀ r, EAll P (ret r)

/-- A continuation from machine data with `fsBase = t` ends in `P`. -/
abbrev KOk (P : MachineData × Int64 → Prop) (t : UInt64) (k : MachineData → Effects) : Prop :=
  ∀ m : MachineData, m.regs.fsBase = t → EAll P (k m)

section Helpers

variable {P : MachineData × Int64 → Prop} {t : UInt64} {s : MachineData}

theorem all_load {addr : BitVec 64} {w : Width} {ret : w.type → MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.load addr w ret) := by
  unfold MachineData.load
  simp only [EAll]
  split
  · exact hk _ _ hs
  · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_store {addr : BitVec 64} {w : Width} {v : w.type} {k : MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : KOk P t k) : EAll P (s.store addr v k) := by
  unfold MachineData.store
  simp only [EAll]
  split
  · exact hk _ hs
  · simp only [EAll]; exact fun d => hk _ hs

theorem all_storeNT {addr : BitVec 64} {w : Width} {v : w.type} {k : MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : KOk P t k) : EAll P (s.storeNT addr v k) := by
  unfold MachineData.storeNT
  simp only [EAll]
  split
  · exact hk _ hs
  · simp only [EAll]; exact fun b d => hk _ hs

theorem all_rmwK {k' : Kraken.RmwKind} {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {ret : w.type → MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.rmwK k' addr w op ret) := by
  unfold MachineData.rmwK
  simp only [EAll]
  split
  · split
    · exact hk _ _ hs
    · exact hk _ _ hs
  · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_rmwPlain {addr : BitVec 64} {w : Width}
    {op : w.type → Option w.type} {ret : w.type → MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.rmwPlain addr w op ret) := by
  unfold MachineData.rmwPlain
  refine all_load hs fun old m hm => ?_
  split
  · exact all_store hm (hk old)
  · exact hk _ _ hm

theorem all_loadAvx {addr : BitVec 64} {w : AvxWidth} {ret : w.type → MachineData → Effects}
    {ca at' : Bool} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (s.loadAvx addr w ret ca at') := by
  unfold MachineData.loadAvx
  split
  · simp only [EAll]
  · simp only [EAll]
    split
    · exact hk _ _ hs
    · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_storeAvx {addr : BitVec 64} {w : AvxWidth} {v : w.type} {k : MachineData → Effects}
    {ca at' : Bool} (hs : s.regs.fsBase = t) (hk : KOk P t k) : EAll P (s.storeAvx addr v k ca at') := by
  unfold MachineData.storeAvx
  split
  · simp only [EAll]
  · simp only [EAll]
    split
    · exact hk _ hs
    · simp only [EAll]; exact fun d => hk _ hs

theorem all_rmw16K {k' : Kraken.RmwKind} {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {ret : BitVec 128 → MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.rmw16K k' addr op ret) := by
  unfold MachineData.rmw16K
  simp only [EAll]
  split
  · split
    · exact hk _ _ hs
    · exact hk _ _ hs
  · simp only [EAll]; exact fun v d => hk _ _ hs

theorem all_rmw16Plain {addr : BitVec 64}
    {op : BitVec 128 → Option (BitVec 128)} {ret : BitVec 128 → MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (s.rmw16Plain addr op ret) := by
  unfold MachineData.rmw16Plain
  refine all_loadAvx hs fun old m hm => ?_
  split
  · exact all_storeAvx hm (hk old)
  · exact hk _ _ hm

theorem all_rm [Labels] [AddressSize] {w} {o : RegOrMem w} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interp s p ret) := by
  unfold RegOrMem.interp
  split
  · exact hk _ _ hs
  · exact all_load hs hk

theorem all_reg {w} {r : Reg w} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (r.interp s p ret) :=
  hk _ _ hs

theorem all_op [Labels] [AddressSize] {w} {o : Operand w} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interp s p ret) := by
  unfold Operand.interp
  split
  · exact all_rm hs hk
  · exact hk _ _ hs

theorem all_rmSeg [Labels] [AddressSize] {w} {o : RegOrMem w} {seg : BitVec 64} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interpSeg seg s p ret) := by
  unfold RegOrMem.interpSeg
  split
  · exact hk _ _ hs
  · exact all_load hs hk

theorem all_opSeg [Labels] [AddressSize] {w} {o : Operand w} {seg : BitVec 64} {p : Std.Rco Int64}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interpSeg seg s p ret) := by
  unfold Operand.interpSeg
  split
  · exact all_rmSeg hs hk
  · exact hk _ _ hs

theorem all_rel [Labels] [AddressSize] {o : RelRegOrMem} {p : Std.Rco Int64}
    {ret : BitVec 64 → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interp s p ret) := by
  unfold RelRegOrMem.interp
  split
  · exact hk _ _ hs
  · exact hk _ _ hs
  · exact all_load hs hk

theorem all_avxRm [Labels] [AddressSize] {w} {o : AvxRegOrMem w} {p : Std.Rco Int64} {ca at' : Bool}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interp s p ret ca at') := by
  unfold AvxRegOrMem.interp
  split
  · exact hk _ _ hs
  · exact all_loadAvx hs hk

theorem all_avxOp [Labels] [AddressSize] {w} {o : AvxOperand w} {p : Std.Rco Int64} {ca : Bool}
    {ret : w.type → MachineData → Effects} (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) :
    EAll P (o.interp s p ret ca) := by
  unfold AvxOperand.interp
  split
  exact all_avxRm hs hk

theorem all_set [Labels] [AddressSize] {w} {d : Dst w} {v : w.type} {p : Std.Rco Int64}
    {k : MachineData → Effects} (hs : s.regs.fsBase = t) (hk : KOk P t k) : EAll P (s.set d v p k) := by
  unfold MachineData.set
  split
  · exact hk _ (by rw [setReg_tp, hs])
  · exact all_store hs hk

theorem all_setSeg [Labels] [AddressSize] {w} {seg : BitVec 64} {d : Dst w} {v : w.type} {p : Std.Rco Int64}
    {k : MachineData → Effects} (hs : s.regs.fsBase = t) (hk : KOk P t k) :
    EAll P (s.setSeg seg d v p k) := by
  unfold MachineData.setSeg
  split
  · exact hk _ (by rw [setReg_tp, hs])
  · exact all_store hs hk

theorem all_setAvx [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type} {p : Std.Rco Int64}
    {ca at' : Bool} {k : MachineData → Effects} (hs : s.regs.fsBase = t) (hk : KOk P t k) :
    EAll P (s.setAvx d v p k ca at') := by
  unfold MachineData.setAvx
  split
  · exact hk _ hs
  · exact all_storeAvx hs hk

theorem all_setAvxLegacy [Labels] [AddressSize] {w} {d : AvxDst w} {v : w.type} {p : Std.Rco Int64}
    {ca at' : Bool} {k : MachineData → Effects} (hs : s.regs.fsBase = t) (hk : KOk P t k) :
    EAll P (s.setAvxLegacy d v p k ca at') := by
  unfold MachineData.setAvxLegacy
  split
  · exact hk _ hs
  · exact all_storeAvx hs hk

theorem all_rmw [Labels] [AddressSize] {w} {o : RegOrMem w} {lock : Bool} {p : Std.Rco Int64}
    {op : w.type → Option w.type} {ret : w.type → MachineData → Effects}
    (hs : s.regs.fsBase = t) (hk : ∀ v, KOk P t (ret v)) : EAll P (o.rmw lock s p op ret) := by
  unfold RegOrMem.rmw
  split
  · dsimp only
    split
    · exact hk _ _ (by rw [setReg_tp, hs])
    · exact hk _ _ hs
  · split
    · exact all_rmwK hs hk
    · exact all_rmwPlain hs hk

theorem all_pending {p : Std.Rco Int64} {k : MachineData → Effects} (hs : s.regs.fsBase = t) (hk : KOk P t k) :
    EAll P (s.pendingSyscall p k) := by
  unfold MachineData.pendingSyscall
  simp only [EAll]
  exact fun r => hk _ (by simp only [set64_tp, hs])

end Helpers

/-! ## One operation -/

/-- The side condition of a helper: the machine data handed on has `fsBase = t`. -/
macro "tp_dis" : tactic => `(tactic| first
  | assumption
  | (simp_all [setReg_tp, set_tp, set64_tp, MachineData.setReg, MachineData.setAvxReg,
      MachineData.setAvxLegacyReg]; done)
  | (split <;> simp_all [setReg_tp, set_tp, set64_tp, MachineData.setReg]; done))

/-- The steps of `all_interp`: a continuation's facts, one helper. -/
macro "tp_step" : tactic => `(tactic| first
  | (intro)
  | (apply all_set (by tp_dis))
  | (apply all_setSeg (by tp_dis))
  | (apply all_setAvx (by tp_dis))
  | (apply all_setAvxLegacy (by tp_dis))
  | (apply all_rm (by tp_dis))
  | (apply all_reg (by tp_dis))
  | (apply all_op (by tp_dis))
  | (apply all_rmSeg (by tp_dis))
  | (apply all_opSeg (by tp_dis))
  | (apply all_rel (by tp_dis))
  | (apply all_avxRm (by tp_dis))
  | (apply all_avxOp (by tp_dis))
  | (apply all_rmw (by tp_dis))
  | (apply all_load (by tp_dis))
  | (apply all_store (by tp_dis))
  | (apply all_storeNT (by tp_dis))
  | (apply all_rmwK (by tp_dis))
  | (apply all_rmwPlain (by tp_dis))
  | (apply all_rmw16K (by tp_dis))
  | (apply all_rmw16Plain (by tp_dis))
  | (apply all_pending (by tp_dis))
  | (simp only [EAll])
  | split)

/-- **Every operation keeps `fsBase`**: every outcome of its effects, from
machine data with `fsBase = t` and continuations that end in `P` from any
such data, ends in `P`. -/
theorem all_interp [Labels] [AddressSize] {w} (op : Operation w) (p : Std.Rco Int64)
    {s : MachineData} {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    {P : MachineData × Int64 → Prop} {t : UInt64}
    (hs : s.regs.fsBase = t) (hn : KOk P t next) (hj : ∀ pc, KOk P t (jmp pc)) :
    EAll P (Operation.interp op p s next jmp) := by
  cases op <;> simp only [Operation.interp] <;>
    repeat' (first
      | exact hn _ (by tp_dis)
      | exact hj _ _ (by tp_dis)
      | tp_step)

/-- **Every vector operation keeps `fsBase`.** -/
theorem all_avx [Labels] [AddressSize] {w} (op : AvxOperation w) (p : Std.Rco Int64)
    {s : MachineData} {next : MachineData → Effects}
    {P : MachineData × Int64 → Prop} {t : UInt64}
    (hs : s.regs.fsBase = t) (hn : KOk P t next) :
    EAll P (AvxOperation.interp op p s next) := by
  -- Reducible unification only: unfolding the vector writes evaluates `2 ^ 512`.
  cases op <;> unfold AvxOperation.interp <;>
    repeat' (first
      | assumption
      | (with_reducible refine hn _ ?_)
      | (intro)
      | (with_reducible apply all_setAvx)
      | (with_reducible apply all_setAvxLegacy)
      | (with_reducible apply all_avxRm)
      | (with_reducible apply all_avxOp)
      | (with_reducible apply all_rmw16K)
      | (with_reducible apply all_rmw16Plain)
      | (simp only [EAll])
      | (split <;> simp only [set64_tp] <;> assumption)
      | split)

/-! ## A directive -/

theorem all_dinterp [Labels] (d : Directive) (p : Std.Rco Int64)
    {s : MachineData} {next : MachineData → Effects} {jmp : Int64 → MachineData → Effects}
    {P : MachineData × Int64 → Prop} {t : UInt64}
    (hs : s.regs.fsBase = t) (hn : KOk P t next) (hj : ∀ pc, KOk P t (jmp pc)) :
    EAll P (d.interp s p next jmp) := by
  unfold Directive.interp
  split
  · exact hn _ hs
  · rename_i i
    simp only [Instr.interp, require_exec_access, EAll]
    split
    · exact @all_interp _ (.mk _) _ _ p _ _ _ _ _ hs hn hj
    · exact @all_avx _ (.mk _) _ _ p _ _ _ _ hs hn
  · simp only [EAll]

theorem all_dirs [Labels] {P : MachineData × Int64 → Prop} {t : UInt64} {ret : Int64 → MachineData → Effects}
    (hr : ∀ pc, KOk P t (ret pc)) :
    ∀ (ds : List (Directive × Nat)) (s : MachineData) (pc : Int64), s.regs.fsBase = t →
      EAll P (Directives.interp ds s pc ret)
  | [], s, pc, hs => by unfold Directives.interp; exact hr pc s hs
  | (d, sz) :: ds, s, pc, hs => by
    unfold Directives.interp
    exact all_dinterp d _ hs (fun m hm => all_dirs hr ds m _ hm) hr

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

theorem tall_loadPieces {σ : Type} {P : σ → Prop} {ds : Decls} {dmem : DataMem} :
    ∀ (n : Nat) (addr : BitVec 64) {k : List UInt8 → EvTree σ}, (∀ bs, TAll P (k bs)) →
      TAll P (loadPieces ds dmem addr n k)
  | 0, _, _, h => h _
  | n + 1, addr, k, h => by
    unfold loadPieces
    split
    · exact tall_loadPieces n _ fun _ => h _
    · split
      · simp only [TAll]
      · exact tall_access fun _ _ => tall_loadPieces n _ fun _ => h _

theorem tall_storePieces {σ : Type} {P : σ → Prop} {ds : Decls} :
    ∀ (n : Nat) (addr : BitVec 64) (bs : List UInt8) (dmem : DataMem) {k : DataMem → EvTree σ},
      (∀ d, TAll P (k d)) → TAll P (storePieces ds addr n bs dmem k)
  | 0, _, _, _, _, h => h _
  | n + 1, addr, bs, dmem, k, h => by
    unfold storePieces
    split
    · exact tall_storePieces n _ _ _ h
    · split
      · simp only [TAll]
      · exact tall_access fun _ _ => tall_storePieces n _ _ _ h

theorem tall_toEv (ds : Decls) {P : MachineData × Int64 → Prop} (e : Effects) :
    EAll P e → TAll P (toEv ds e) := by
  induction e with
  | done a => exact id
  | unimplemented _ => intro _; trivial
  | gp_unaligned _ _ => intro _; trivial
  | nonmem_load dmem addr w ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | @nonmem_store dmem addr w v ret ih => intro h; exact tall_access fun _ _ => ih _ (h _)
  | @undefined α inst ret ih =>
    intro h
    cases inst with
    | bool => exact fun i => ih _ (h _)
    | bitvec _ => trivial
    | avx_bitvec _ => trivial
    | statusFlags => trivial
  | require_read_access _ _ ok ih => intro h; exact ih () h
  | require_write_access _ _ ok ih => intro h; exact ih () h
  | require_exec_access _ ok ih => intro h; exact ih () h
  | sync_load k x dmem addr w ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | @sync_store k x dmem addr w v ret ih => intro h; exact tall_access fun _ b => ih _ _ (h _ _)
  | rmw k dmem addr w op ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | fence k ok ih => intro h; exact fun _ => ih () h
  | require_read_access_avx _ _ _ ok ih => intro h; exact ih () h
  | require_write_access_avx _ _ _ ok ih => intro h; exact ih () h
  | nonmem_load_avx at' dmem addr w ret ih =>
    intro h
    simp only [toEv]
    split
    · exact tall_access fun _ v => ih _ _ (h _ _)
    · exact tall_loadPieces _ _ fun _ => ih _ _ (h _ _)
  | @nonmem_store_avx at' dmem addr w v ret ih =>
    intro h
    simp only [toEv]
    split
    · exact tall_access fun _ _ => ih _ (h _)
    · exact tall_storePieces _ _ _ _ fun _ => ih _ (h _)
  | rmw16 k dmem addr op ret ih => intro h; exact tall_access fun _ v => ih _ _ (h _ _)
  | syscall _ _ _ => intro _; trivial

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

/-! ## A step of `isa` -/

/-- **`fsBase = t`.** -/
abbrev TP (t : UInt64) (s : State) : Prop := s.st.1.regs.fsBase = t

/-- **Every step keeps `fsBase`**: every leaf of its event tree. -/
theorem exec_tp {s : State} {t : UInt64} (hs : TP t s) {tr : EvTree State}
    (he : isa.exec s = some tr) : TAll (TP t) tr := by
  change exec s = some tr at he
  unfold exec at he
  split at he
  · cases he
  · cases he
    refine tall_map _ (tall_toEv _ _ ?_)
    unfold _root_.Executable.step
    dsimp only
    exact @all_dirs (_root_.Executable.labels s.exe) (fun a => a.1.regs.fsBase = t) t
      (fun pc m => .done (m, pc)) (fun pc m hm => hm) _ _ _ hs

/-- **A state at no system call asking for `arch_prctl`** (the one move
that sets `fsBase`). -/
def NoSetFsAt (s : State) : Prop :=
  Scc.Sem.X64.abi.atSys s = true → ∀ a,
    Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) ≠
      some (.archSetFs a)

/-- A directive other than `syscall`. -/
def dNoSys : Directive → Bool
  | .instr (.regular _ _ .syscall) => false
  | _ => true

/-- **A state at a cell other than `syscall`** is at no `arch_prctl`. -/
theorem noSetFsAt_of_cell {s : State} {d : Directive} {sz : Nat} (h : Lower.X64.CellAt s d sz)
    (hd : dNoSys d = true) : NoSetFsAt s := by
  obtain ⟨-, -, rest, hcode⟩ := h
  have hdir : s.directive = some d := by
    unfold State.directive
    rw [show List.dropWhile _ (Kraken.Executable.directivesFromAddress s.exe s.st.2) =
        Kraken.Executable.codeAt s.exe s.st.2 from by
      unfold Kraken.Executable.codeAt
      congr 1, hcode]
    rfl
  intro hat
  exfalso
  change Scc.Sem.X64.atSyscall s = true at hat
  unfold Scc.Sem.X64.atSyscall at hat
  rw [hdir] at hat
  split at hat
  · rename_i heq
    cases heq
    simp [dNoSys] at hd
  · cases hat

/-- **The kernel's returns keep `fsBase`** at a system call other than
`arch_prctl`. -/
theorem certSuccs_tp {s : State} {t : UInt64} (hs : TP t s) (hn : NoSetFsAt s)
    (hat : Scc.Sem.X64.abi.atSys s = true) {call : Scc.Sem.Kernel.Call}
    (hd : Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) = some call) :
    ∀ s' ∈ Scc.Sem.Kernel.certSuccs Scc.Sem.X64.abi s call, TP t s' := by
  cases call with
  | archSetFs x => exact absurd hd (hn hat x)
  | _ =>
    intro s' hm
    simp only [Scc.Sem.Kernel.certSuccs, List.mem_map] at hm
    obtain ⟨r, -, rfl⟩ := hm
    exact hs

/-! ## Segments -/

/-- **`ms` with every allocation landing asked only at `fsBase = t`.** -/
def tpXa (ms : MemSide isa) (t : UInt64) : MemSide isa :=
  { ms with xa := fun l b n s c => TP t s → ms.xa l b n s c }

/-- **One instruction at no `arch_prctl`, `fsBase` kept**: what it does
under `tpXa ms t` from a state with `fsBase = t` it does under `ms` with `t`
kept in the fragment it lands in. -/
theorem out_tp {p : CoreTerm.Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
    {X : Frag isa} {s : State} {c : Ctl} {t : UInt64}
    (hK : ms.K = some Scc.Sem.X64.abi) (hn : NoSetFsAt s) (hs : TP t s)
    (h : Out p lbl (tpXa ms t) X s c) : Out p lbl ms (fun s c => X s c ∧ TP t s) s c := by
  have hT : ∀ tr, isa.exec s = some tr → TAll (TP t) tr := fun tr he => exec_tp hs he
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
    exact ⟨c', hr, hx, certSuccs_tp hs hn hat hd s' hm⟩
  | holdLoad kl A g x sa u v e he h1 h2 h3 h4 =>
    exact .holdLoad kl A g x sa u v e he h1 h2 h3 fun r w' hr hv => ⟨h4 r w' hr hv, hT _ he r⟩
  | xchgStore kr A V s' x sa u v e tv wv wold he h1 h2 h3 h4 h5 h6 =>
    exact .xchgStore kr A V s' x sa u v e tv wv wold he h1 h2 h3 h4 h5 ⟨h6, hT _ he true⟩
  | ctrRmw k op g x τ e n he h1 h2 h3 h4 h5 h6 =>
    exact .ctrRmw k op g x τ e n he h1 h2 h3 h4 h5 fun old hG ho hle hl =>
      ⟨(h6 old hG ho hle hl).1, (h6 old hG ho hle hl).2, hT _ he old⟩
  | alloc s' A x a τ e ta ws k wold old us he h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    exact .alloc s' A x a τ e ta ws k wold old us he h1 h2 h3 h4 h5 h6 h7 h8 fun l ini hl => h9 l ini hl (hT _ he)
  | newStore kr A V s' x a ty e w wold old h0 he h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 =>
    exact .newStore kr A V s' x a ty e w wold old h0 he h1 h2 h3 h4 h5 h6 h7 h8 h9 fun l hl =>
      h10 l hl (hT _ he true)
  | emit K' buf n Pw Qw hK' hat hd h0 hb hr hq =>
    have hK2 : ms.K = some K' := hK'
    rw [hK] at hK2
    cases hK2
    exact .emit _ buf n Pw Qw hK hat hd h0 hb (fun j hj c1 hp r hm hok =>
      ⟨⟨(hr j hj c1 hp r hm hok).1, hs⟩, (hr j hj c1 hp r hm hok).2⟩) hq
  | fence k s' c' he hr hx => exact .fence k s' c' he hr ⟨hx, hT _ he ()⟩

/-- **A segment keeps `fsBase`**: a segment under `tpXa ms t` (its
allocation landings asked only at `fsBase = t`) whose states are at no
`arch_prctl` (`hW`) and whose outside moves keep `fsBase` (`hKt`) is one
under `ms` with `fsBase = t` at its entry and its exit. -/
theorem SegW.keepTP {W : Frag isa} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {P Q : Frag isa} {t : UInt64}
    (hK : ms.K = some Scc.Sem.X64.abi) (h : SegW W K p lbl (tpXa ms t) P Q)
    (hW : ∀ s c, W s c → NoSetFsAt s) (hKt : ∀ s c, W s c → ∀ s', K s s' → TP t s → TP t s') :
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

/-- **A segment keeps `fsBase`, its predicate asked only there**:
`SegW.keepTP` for a segment inside `W'`, which gives `W` at each state with
`fsBase = t` (`hW`); the conclusion is inside `W`. -/
theorem SegW.keepTP' {W W' : Frag isa} {K : State → State → Prop} {p : CoreTerm.Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {P Q : Frag isa} {t : UInt64}
    (hK : ms.K = some Scc.Sem.X64.abi) (h : SegW W' K p lbl (tpXa ms t) P Q)
    (hN : ∀ s c, W' s c → NoSetFsAt s) (hKt : ∀ s c, W' s c → ∀ s', K s s' → TP t s → TP t s')
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

end Spike.Lib.X64.KeepTP

/-- info: 'Spike.Lib.X64.KeepTP.SegW.keepTP'' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.KeepTP.SegW.keepTP'
