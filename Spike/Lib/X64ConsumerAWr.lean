/-
**The arena's write obligations at one pair, for producers** (`NodesA`'s
`ctrRow` and `arena` from facts about the instruction's address).

`NodesA.ctrRow` and `NodesA.arena` speak of every outcome of the
instruction (`stepOne`, `Writes`). A producer knows less and more: the
instruction's event tree at the pair (the `Out` row it proves) and the
concrete address `L` it writes (a stack slot, a TCB word, a runtime counter,
the header of an allocation in progress). `WrOkA` is the obligation in that
form: for every location the instruction stores to or read-modify-writes
(`WrAt`, the tree shapes of the `Out` rows), the arena allows the write
(`ArenaW`), and a write of the counter word is the counter's add
(`CtrRow`). `WrOkA.ctrRow` and `WrOkA.arena` give `NodesA`'s fields at the
pair from it and the pair's `Out` row.

- `MemEff`, `append_ne`, `append_inj`, `erase_inj`, `erase_ne`: one message
  at `L`, appended or fulfilled; `not_writes_of_same`, `loc_of_writes`: an
  outcome that keeps memory and promises writes nothing; one with `MemEff L`
  writes only `L`.
- `load_same`, `rmw_eff`: a load keeps memory and promises; a
  read-modify-write at `L` keeps them or writes `L`.
- `WrAt`, `out_eff`: an `Out` row's outcome keeps memory and promises or
  writes a location the instruction writes.
- `WrOkA`, `WrOkA.ctrRow`, `WrOkA.arena`: the obligation and the reduction.
- Producer lemmas, one per row kind: `wrOkA_of_noWr` with `noWr_done`,
  `noWr_load` (no write); `wrOkA_off` (a store off the arena, not the
  counter: a stack slot, a TCB word, another runtime counter);
  `wrOkA_label` (a store into a placed label); `wrOkA_ctr` (the counter's
  add); `wrOkA_header` with `loc_ne_ctrLoc` (**the worked example**: the
  header store of an allocation in progress, below the object's base).
-/
import Spike.Lib.X64ConsumerA
import Scc.Sem.Rows1Rmw
import Spike.Lib.FenceStep

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower
open Scc.Sem Scc.Sem.X64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {p : Prog}

/-! ## One message -/

/-- **The outcome `o` writes one message at `L`**: appended, or fulfilling an
outstanding promise of it (memory unchanged, the promise erased). -/
def MemEff (t : Thread isa) (mem : Memory) (o : Outcome isa) (L : Loc) : Prop :=
  ∃ V : Val, o.mem = (mem.append ⟨L, V, 0⟩).1 ∨
    ∃ q ∈ t.prom, mem.get? q = some ⟨L, V, 0⟩ ∧ o.mem = mem ∧ o.thread.prom = t.prom.erase q

theorem append_ne (mem : Memory) (m : Msg) : (mem.append m).1 ≠ mem := by
  intro h
  have := congrArg (fun x : Memory => x.msgs.size) h
  simp [Memory.append] at this

theorem append_inj {mem : Memory} {m m' : Msg} (h : (mem.append m).1 = (mem.append m').1) : m = m' := by
  have := congrArg (fun x : Memory => x.msgs.back?) h
  simpa [Memory.append] using this

theorem erase_inj {l : List Nat} {q q' : Nat} (hq : q ∈ l) (h : l.erase q = l.erase q') : q = q' := by
  refine Classical.byContradiction fun hne => ?_
  have h1 := congrArg (List.count q) h
  rw [List.count_erase_self, List.count_erase_of_ne hne] at h1
  have := List.count_pos_iff.mpr hq
  omega

theorem erase_ne {l : List Nat} {q : Nat} (hq : q ∈ l) : l.erase q ≠ l := by
  intro h
  have h1 := congrArg List.length h
  rw [List.length_erase_of_mem hq] at h1
  have := List.length_pos_of_mem hq
  omega

/-- **An outcome keeping memory and promises writes nothing.** -/
theorem not_writes_of_same {t : Thread isa} {mem : Memory} {o : Outcome isa} {L : Loc}
    (hm : o.mem = mem) (hp : o.thread.prom = t.prom) : ¬ Writes t mem o L := by
  rintro ⟨V, ⟨h1, -⟩ | ⟨q, hq, -, -, h2⟩⟩
  · exact append_ne _ _ (h1.symm.trans hm)
  · exact erase_ne hq (h2.symm.trans hp)

/-- **An outcome writing one message at `L` writes only `L`.** -/
theorem loc_of_writes {t : Thread isa} {mem : Memory} {o : Outcome isa} {L L' : Loc}
    (he : MemEff t mem o L) (hw : Writes t mem o L') : L' = L := by
  obtain ⟨V, ha | ⟨q, hq, hg, hm, hp⟩⟩ := he <;> obtain ⟨V', ⟨ha', -⟩ | ⟨q', hq', hg', hm', hp'⟩⟩ := hw
  · exact congrArg Msg.loc (append_inj (ha'.symm.trans ha))
  · exact absurd (ha.symm.trans hm') (append_ne _ _)
  · exact absurd (ha'.symm.trans hm) (append_ne _ _)
  · have hqq := erase_inj hq (hp.symm.trans hp')
    subst hqq
    rw [hg] at hg'
    exact (congrArg Msg.loc (Option.some.inj hg')).symm

/-! ## The rows' trees -/

/-- **A load keeps memory and promises.** -/
theorem load_same {A : Arch} {t : Thread isa} {mem : Memory} {kl : Kraken.LoadKind} {xcl : Bool} {L : Loc}
    {g : Val → State} (hex : isa.exec t.st = some (.load kl xcl L fun v => .done (g v)))
    {outs : List (Except String (Outcome isa))} (hstep : stepOne A t 0 mem = some outs) {o : Outcome isa}
    (ho : .ok o ∈ outs) : o.mem = mem ∧ o.thread.prom = t.prom := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A 0 hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  obtain ⟨ts1, v, hx, rfl⟩ := (Lower.run_load_iff A 0 _ (f := g)).mp hr
  have hmem : c'.mem = mem := by
    obtain ⟨-, -, -, he⟩ := readSuccs_shape A _ hx
    have := congrArg Ctx.mem he; exact this
  exact ⟨hm.trans hmem, (finishInstr_relKey hth).1.trans (readSuccs_prom A _ hx)⟩

/-- **A read-modify-write at `L` keeps memory and promises or writes `L`**
(`Scc.Sem.stepOne_rmw_cases` without the read's facts, at any location). -/
theorem rmw_eff {A : Arch} {t : Thread isa} {mem : Memory} {k : Kraken.RmwKind} {L : Loc}
    {op : Val → Option Val} {g : Val → State}
    (hex : isa.exec t.st = some (.rmw k false L op fun v => .done (g v)))
    {outs : List (Except String (Outcome isa))} (hstep : stepOne A t 0 mem = some outs) {o : Outcome isa}
    (ho : .ok o ∈ outs) : (o.mem = mem ∧ o.thread.prom = t.prom) ∨ MemEff t mem o L := by
  obtain ⟨st, c', hr, hth, hm⟩ := (Lower.stepOne_ok_iff A 0 hex).mp ⟨outs, o, hstep, ho, rfl, rfl⟩
  obtain ⟨tr, old, c1, hx, -, hcase⟩ := (Lower.run_rmw_iff A 0 _ (f := g)).mp hr
  obtain ⟨hm0, hp0⟩ := rmwFenceOpt_mem_prom A (Live.TicketStep.ctx0 0 t mem)
  have hm1 : c1.mem = mem := by
    obtain ⟨-, -, -, h⟩ := readSuccs_shape A _ hx
    exact (congrArg Ctx.mem h).trans hm0
  have hp1 : c1.prom = t.prom := (readSuccs_prom A _ hx).trans hp0
  unfold MemEff
  rw [(finishInstr_relKey hth).1, hm]
  rcases hcase with ⟨-, rfl⟩ | ⟨new, c2, -, hw, rfl⟩
  · obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A c1
    exact .inl ⟨h1.trans hm1, h2.trans hp1⟩
  · refine .inr ⟨new, ?_⟩
    obtain ⟨h1, h2⟩ := rmwFenceOpt_mem_prom A
      (Lower.rmwBump (A.rmwKind k) false L { c2 with rmwWrote := true })
    obtain ⟨h3, h4⟩ := rmwBump_mem_prom (A.rmwKind k) false L { c2 with rmwWrote := true }
    rw [h1, h3, h2, h4]
    simp only
    rcases (Lower.mem_writeSuccs_iff A 0 _).mp hw with ⟨q, hq, hg, -, rfl⟩ | ⟨-, rfl⟩
    · rw [hp1] at hq
      rw [hm1] at hg
      exact .inr ⟨q, hq, hg, hm1, by show c1.prom.erase q = _; rw [hp1]⟩
    · exact .inl (by show (c1.mem.append _).1 = _; rw [hm1])

/-- **The instruction at `s` writes `L`**: a store or a read-modify-write of
`L` in the tree shapes of the `Out` rows. -/
def WrAt (s : State) (L : Loc) : Prop :=
  (∃ kr V s', isa.exec s = some (.store kr false L V fun _ => .done s')) ∨
    ∃ (k : Kraken.RmwKind) (op : Val → Option Val) (g : Val → State),
      isa.exec s = some (.rmw k false L op fun v => .done (g v))

/-- **An `Out` row's outcome** off a system call (the kernel `abi`) keeps
memory and promises, or writes one message at a location the instruction
writes. -/
theorem out_eff {A : Arch} {lbl : Lbl} {ms : MemSide isa} {X : Frag isa} {s : State} {c : Ctl}
    (hout : Out p lbl ms X s c) (hK : ms.K = some abi) (hns : abi.atSys s = false)
    {t : Thread isa} {mem : Memory} (hst : t.st = s) {outs : List (Except String (Outcome isa))}
    (hstep : stepOne A t 0 mem = some outs) {o : Outcome isa} (ho : .ok o ∈ outs) :
    (o.mem = mem ∧ o.thread.prom = t.prom) ∨ ∃ L, WrAt s L ∧ MemEff t mem o L := by
  subst hst
  have hsil : ∀ {tree : EvTree State} {P : State → Prop}, isa.exec t.st = some tree → SilentTree P tree →
      o.mem = mem ∧ o.thread.prom = t.prom := fun he hs => by
    obtain ⟨_, -, hth, hm⟩ := stepOne_silent_ok A 0 he hs ⟨outs, o, hstep, ho, rfl, rfl⟩
    exact ⟨hm, (finishInstr_relKey hth).1⟩
  have hsto : ∀ {kr L V s'}, isa.exec t.st = some (.store kr false L V fun _ => .done s') →
      ∃ L, WrAt t.st L ∧ MemEff t mem o L := fun {kr L V s'} he => by
    obtain ⟨-, ⟨hm, -⟩ | ⟨q, hq, hg, hm, hp⟩⟩ := k_store_out A he ⟨outs, o, hstep, ho, rfl⟩
    · exact ⟨L, Or.inl ⟨kr, V, s', he⟩, V, .inl hm⟩
    · exact ⟨L, Or.inl ⟨kr, V, s', he⟩, V, .inr ⟨q, hq, hg, hm, hp⟩⟩
  have hrmw : ∀ {k L op} {g : Val → State}, isa.exec t.st = some (.rmw k false L op fun v => .done (g v)) →
      (o.mem = mem ∧ o.thread.prom = t.prom) ∨ ∃ L, WrAt t.st L ∧ MemEff t mem o L := fun {k L op g} he =>
    (rmw_eff he hstep ho).imp_right fun h => ⟨L, Or.inr ⟨k, op, g, he⟩, h⟩
  have hsys : ∀ {K : Kernel.Abi isa}, ms.K = some K → K.atSys t.st = true → False := fun hK' hat => by
    rw [hK] at hK'
    cases Option.some.inj hK'
    rw [hat] at hns; cases hns
  cases hout with
  | silent s' _ he => exact .inl (hsil he (silentTree_done s'))
  | choice _ _ he hs => exact .inl (hsil he hs)
  | load _ _ _ _ _ _ _ _ he => exact .inl (load_same he hstep ho)
  | store _ _ _ _ _ _ _ _ _ _ _ _ he => exact .inr (hsto he)
  | rtStore _ _ _ _ _ he => exact .inr (hsto he)
  | rtLoad _ _ _ _ he => exact .inl (load_same he hstep ho)
  | rtRmw _ _ _ _ _ he => exact hrmw he
  | sys _ _ hK' hat => exact (hsys hK' hat).elim
  | holdLoad _ _ _ _ _ _ _ _ he => exact .inl (load_same he hstep ho)
  | xchgStore _ _ _ _ _ _ _ _ _ _ _ _ he => exact .inr (hsto he)
  | ctrRmw _ _ _ _ _ _ _ he => exact hrmw he
  | alloc s' _ _ _ _ _ _ _ _ _ _ _ he => exact .inl (hsil he (silentTree_done s'))
  | newStore _ _ _ _ _ _ _ _ _ _ _ _ he => exact .inr (hsto he)
  | emit _ _ _ _ _ hK' hat => exact (hsys hK' hat).elim
  | fence _ _ _ he =>
    obtain ⟨-, hm, hp⟩ := Spike.Lib.FenceStep.stepOne_fence_ok A 0 he ⟨outs, o, hstep, ho, rfl, rfl⟩
    exact .inl ⟨hm, hp⟩

/-! ## The obligation -/

/-- **The arena's write obligation at the pair `(s, c)`** (placement `lbl`,
`lsize`; the counter's add under `ms` landing in `X`): every location the
instruction writes (`WrAt`) is one the arena allows (`ArenaW`), and a write
of the counter word is the counter's add (`CtrRow`). -/
structure WrOkA (ar : Arena) (lbl : Lbl) (lsize : Lsize) (ms : MemSide isa) (X : Frag isa) (s : State)
    (c : Ctl) : Prop where
  arena : ∀ L, WrAt s L → ArenaW ar lbl lsize c L
  ctr : WrAt s ar.ctrLoc → CtrRow ms X s c

/-- **`NodesA.ctrRow` at a pair from `WrOkA`** and an `Out` row at its state
(any control, placement, memory side and landing; the kernel `abi`). -/
theorem WrOkA.ctrRow {ar : Arena} {lbl lbl' : Lbl} {lsize : Lsize} {ms ms' : MemSide isa} {X Y : Frag isa}
    {s : State} {c : Ctl} (hw : WrOkA ar lbl lsize ms X s c) {c₁ : Ctl} (hout : Out p lbl' ms' Y s c₁)
    (hK : ms'.K = some abi) (hns : abi.atSys s = false) {t : Thread isa} {mem : Memory} (hst : t.st = s)
    {outs : List (Except String (Outcome isa))} (hstep : stepOne Arch.tso t 0 mem = some outs)
    {o : Outcome isa} (ho : .ok o ∈ outs) (hW : Writes t mem o ar.ctrLoc) : CtrRow ms X s c := by
  rcases out_eff hout hK hns hst hstep ho with ⟨hm, hp⟩ | ⟨L, hL, he⟩
  · exact absurd hW (not_writes_of_same hm hp)
  · rw [← loc_of_writes he hW] at hL
    exact hw.ctr hL

/-- **`NodesA.arena` at a pair from `WrOkA`** and an `Out` row at its state. -/
theorem WrOkA.arena_of {ar : Arena} {lbl lbl' : Lbl} {lsize : Lsize} {ms ms' : MemSide isa} {X Y : Frag isa}
    {s : State} {c : Ctl} (hw : WrOkA ar lbl lsize ms X s c) {c₁ : Ctl} (hout : Out p lbl' ms' Y s c₁)
    (hK : ms'.K = some abi) (hns : abi.atSys s = false) {t : Thread isa} {mem : Memory} (hst : t.st = s)
    {outs : List (Except String (Outcome isa))} (hstep : stepOne Arch.tso t 0 mem = some outs)
    {o : Outcome isa} (ho : .ok o ∈ outs) {L : Loc} (hW : Writes t mem o L) : ArenaW ar lbl lsize c L := by
  rcases out_eff hout hK hns hst hstep ho with ⟨hm, hp⟩ | ⟨L', hL, he⟩
  · exact absurd hW (not_writes_of_same hm hp)
  · rw [← loc_of_writes he hW] at hL
    exact hw.arena _ hL

/-! ## Producer lemmas -/

variable {ar : Arena} {lbl : Lbl} {lsize : Lsize} {ms : MemSide isa} {X : Frag isa} {s : State} {c : Ctl}

/-- **No write, no obligation.** -/
theorem wrOkA_of_noWr (h : ∀ L, ¬ WrAt s L) : WrOkA ar lbl lsize ms X s c :=
  ⟨fun L hL => (h L hL).elim, fun hL => (h _ hL).elim⟩

/-- A silent instruction writes nothing. -/
theorem noWr_done {s' : State} (he : isa.exec s = some (.done s')) : ∀ L, ¬ WrAt s L := by
  rintro L (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> rw [he] at h <;> cases h

/-- A load writes nothing. -/
theorem noWr_load {kl : Kraken.LoadKind} {xcl : Bool} {L : Loc} {g : Val → EvTree State}
    (he : isa.exec s = some (.load kl xcl L g)) : ∀ L, ¬ WrAt s L := by
  rintro L' (⟨_, _, _, h⟩ | ⟨_, _, _, h⟩) <;> rw [he] at h <;> cases h

/-- The location a store writes. -/
theorem wrAt_store {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : State}
    (he : isa.exec s = some (.store kr false L V fun _ => .done s')) {L' : Loc} (h : WrAt s L') : L' = L := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [he] at h
  · simp only [Option.some.injEq, EvTree.store.injEq] at h; exact h.2.2.1.symm
  · simp at h

/-- The location a read-modify-write writes. -/
theorem wrAt_rmw {k : Kraken.RmwKind} {L : Loc} {op : Val → Option Val} {g : Val → State}
    (he : isa.exec s = some (.rmw k false L op fun v => .done (g v))) {L' : Loc} (h : WrAt s L') : L' = L := by
  rcases h with ⟨_, _, _, h⟩ | ⟨_, _, _, h⟩ <;> rw [he] at h
  · simp at h
  · simp only [Option.some.injEq, EvTree.rmw.injEq] at h; exact h.2.2.1.symm

/-- **A store off the arena, not the counter word** (a stack slot, a TCB
word, another runtime counter). -/
theorem wrOkA_off {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : State}
    (he : isa.exec s = some (.store kr false L V fun _ => .done s'))
    (hoff : ¬ (ar.heap ≤ L.addr.toNat ∧ L.addr.toNat < ar.heap + 16 * ar.cells)) (hne : L ≠ ar.ctrLoc) :
    WrOkA ar lbl lsize ms X s c :=
  ⟨fun _ hL => wrAt_store he hL ▸ .inr (.inl hoff), fun hL => (hne (wrAt_store he hL).symm).elim⟩

/-- **A store into a placed label**, not the counter word. -/
theorem wrOkA_label {kr : Kraken.StoreKind} {L : Loc} {V : Val} {s' : State}
    (he : isa.exec s = some (.store kr false L V fun _ => .done s'))
    (hl : ∃ l b, lbl l = some b ∧ (lrange lsize l b).contains L.addr.toNat) (hne : L ≠ ar.ctrLoc) :
    WrOkA ar lbl lsize ms X s c :=
  ⟨fun _ hL => wrAt_store he hL ▸ .inr (.inr (.inl hl)), fun hL => (hne (wrAt_store he hL).symm).elim⟩

/-- **The counter's add**: a read-modify-write of the counter word that is
the counter's add (`CtrRow`). -/
theorem wrOkA_ctr {k : Kraken.RmwKind} {op : Val → Option Val} {g : Val → State}
    (he : isa.exec s = some (.rmw k false ar.ctrLoc op fun v => .done (g v))) (hc : CtrRow ms X s c) :
    WrOkA ar lbl lsize ms X s c :=
  ⟨fun _ hL => .inl (wrAt_rmw he hL), fun _ => hc⟩

/-- **A word of the arena is not the counter word** (`Arena.OK.ctr_out`). -/
theorem loc_ne_ctrLoc (hok : ar.OK) {A : BitVec 64} (hlo : ar.heap ≤ A.toNat)
    (hhi : A.toNat < ar.heap + 16 * ar.cells) : (⟨A, 8⟩ : Loc) ≠ ar.ctrLoc := by
  intro h
  have hA : A = BitVec.ofNat 64 ar.ctr := congrArg Loc.addr h
  have hc : A.toNat = ar.ctr := by rw [hA, BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hok.ctr_lt
  exact hok.ctr_out ⟨hc ▸ hlo, hc ▸ hhi⟩

/-- **The worked example: the header store** of an allocation in progress.
At `let x = newBuf a τ in e` of `k` elements with the counter held at its
old count `old` (`Out.ctrRmw`'s landing), the allocator stores the header
word at `A = heap + 16 · old + off k τ - 8`, below the object's base; the
arena allows it (`ArenaW`'s header case), and it is not the counter word.
On `hello1`'s x86-64 code this is `scc_rt_alloc`'s `movq %rax, (%rcx)` with
`%rcx = scc_rt_heap + 16 · old + 8 · k · m` (`off k τ = 8 · k · m + 8`); a
producer discharges `hlt` from the register facts its row already has, and
`hne` by `loc_ne_ctrLoc` from `hlo` (`A` in the arena). The other stores of
`hello1` are `wrOkA_off` (stack slots, TCB words, the other counters) or
`wrOkA_label` (lane stores), its `lock xaddq` is `wrOkA_ctr`, and every other
instruction `wrOkA_of_noWr`. -/
theorem wrOkA_header {kr : Kraken.StoreKind} {A : BitVec 64} {V : Val} {s' : State}
    (he : isa.exec s = some (.store kr false ⟨A, 8⟩ V fun _ => .done s')) {old : Nat} {x : String} {a : At}
    {τ : Ty} {e : Expr} {ta : Ty} {ws : List TermRun.Word} {k : Nat}
    (hh : c.hold = some (ar.ctr, TermRun.cst (.num old))) (ht : c.term = .let_ x (.newBuf a τ) e)
    (hev : TermRun.evalAt c.env a = some (ta, ws)) (hk : TermRun.numOf ws = some k)
    (hlt : A.toNat < ar.heap + 16 * old + ar.off k τ) (hne : (⟨A, 8⟩ : Loc) ≠ ar.ctrLoc) :
    WrOkA ar lbl lsize ms X s c :=
  ⟨fun _ hL => wrAt_store he hL ▸ .inr (.inr (.inr ⟨old, x, a, τ, e, ta, ws, k, hh, ht, hev, hk, hlt⟩)),
    fun hL => (hne (wrAt_store he hL).symm).elim⟩

end Spike.Lib.X64ConsumerA
