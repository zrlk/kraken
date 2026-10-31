/-
**`scc_rt_stack_take`'s and `scc_rt_thread_init`'s node obligations at
another source control** (x86-64; twin of `Spike/Lib/A64WakeTi2C0.lean`):
the nodes' invariants `takeNG` / `tiN` pin the source control to the
ghost's `q.c0` and say nothing else about it, so obligations at a
control-blind frag proved at one ghost control `c0'` hold at any other
(`blkW_mapC` / `nodeW_mapC` per node).

This lets the second `scc_rt_thread_init` call (`Ti2*`) run `Rt.takeW_gen` /
`Rt.tiW_gen` at the dummy control `X64Consumer.c0` (whose `CFacts` hold,
`cfacts_c0`) and keep only `SFactsSt` (no source-control field), moved to the
real nodes. **The real control's placement never comes from here**: it enters
at `StartTi.blk2_WS` / `node2_WS` / `site2_WS`, from `hpl0`/`hPl` at the real
node's invariant (`c = c0`).

- `blkW_mapC`, `nodeW_mapC`: a block's / node's obligation at another
  invariant.
- `takeJ_c0`, `tiJ_c0`: a node's invariant at the ghost with another control.
- `takeW_c0`, `tiW_c0`: the node obligations at a control-blind frag moved.

**Unlike AArch64**: `blkW_mapC` / `nodeW_mapC` live here (namespace
`Ti2C0`; A64's are `WcW.blkW_mapC` / `nodeW_mapC` in `A64WakeWcPreW`, the
W-family's file, not ported on this branch); `TakeW` / `TiW` take no `P`;
x86-64's `TakeW` has no `adrp` pairs (A64's `.d0`/`.d7`/… conjunctions), its
single-instruction nodes being plain `NodeW`s, and `TiW` has the extra block
`.c7`.
-/
import Spike.Lib.X64Ret0

namespace Spike.Lib.X64.WakePh.Ti2C0

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib (Ctl)
open Spike.Lib.X64 (ND BlkW NodeW At)
open Spike.Lib.X64.Flow.Ret0 (TK TI TakeG TiG TakeW TiW takeNG tiN)

/-- **A block's obligation at another invariant**: same pc and offsets,
each control of `n`'s invariant with one of `n'`'s at the same state, `W`
there giving `W'` here. -/
theorem blkW_mapC {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n n' : ND} {blk : List (Directive × Nat)}
    (hpc : n'.pc = n.pc) (ho : n'.o = n.o) (h : BlkW W K exe endPc R F n' blk)
    (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) : BlkW W' K exe endPc R F n blk := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  intro s σ c he hn hd hp hA hF hJn k hk m hA' hD
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨h1, h2⟩ := h s σ c' he hn hd hp hA hF hJ' k hk m hA' hD
  exact ⟨hW _ h1, h2⟩

/-- **A node's obligation at another invariant** (as `blkW_mapC`). -/
theorem nodeW_mapC {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Spike.Lib.Region} {F : MachineData → Prop} {n n' : ND} (hpc : n'.pc = n.pc) (ho : n'.o = n.o)
    (h : NodeW W K exe endPc R F n') (hJ : ∀ σ c, n.J σ c → ∃ c', n'.J σ c' ∧ ∀ s, W s c' → W' s c) :
    NodeW W' K exe endPc R F n := by
  obtain ⟨pc, o, J⟩ := n
  obtain ⟨pc', o', J'⟩ := n'
  simp only at hpc ho
  subst hpc ho
  rintro s c ⟨h1, h2, h3, h4, σ, hA, hF, hJn⟩
  obtain ⟨c', hJ', hW⟩ := hJ σ c hJn
  obtain ⟨hw, hk⟩ := h s c' ⟨h1, h2, h3, h4, σ, hA, hF, hJ'⟩
  exact ⟨hW _ hw, hk⟩

/-- **A take node's invariant at another control**: `takeNG`'s at `q` gives
it at `q` with the control `c0'`. -/
theorem takeJ_c0 {lab : Label → Int64} {q : TakeG} {c0' : Ctl} {b : Bool} {i : TK} {σ : Spike.Lib.X64.AS}
    {c : Ctl} (h : (takeNG lab q b i).J σ c) : (takeNG lab { q with c0 := c0' } b i).J σ c0' := by
  cases i
  case ret => exact ⟨h.1, rfl, h.2.2⟩
  all_goals exact ⟨rfl, h.2⟩

/-- **A thread-init node's invariant at another control** (as `takeJ_c0`). -/
theorem tiJ_c0 {lab : Label → Int64} {q : TiG} {c0' : Ctl} {i : TI} {σ : Spike.Lib.X64.AS} {c : Ctl}
    (h : (tiN lab q i).J σ c) : (tiN lab { q with c0 := c0' } i).J σ c0' := by
  cases i
  case call => exact ⟨⟨rfl, h.1.2⟩, h.2⟩
  all_goals exact ⟨rfl, h.2⟩

variable {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Spike.Lib.Region} {F M : MachineData → Prop}

/-- **`scc_rt_stack_take`'s obligations at another control**: proved at the
ghost `q` with control `c0'` inside `W`, they hold at `q` inside `W'` when
`W` at any control gives `W'` at every control (`hW`). -/
theorem takeW_c0 {q : TakeG} {c0' : Ctl} (hW : ∀ s c c', W s c' → W' s c)
    (h : ∀ i, TakeW W K exe endPc R F M { q with c0 := c0' } i) : ∀ i, TakeW W' K exe endPc R F M q i := by
  intro i
  have hi := h i
  have hB : ∀ {F' : MachineData → Prop} {n n' : ND} {blk}, BlkW W K exe endPc R F' n' blk → n'.pc = n.pc →
      n'.o = n.o → (∀ σ c, n.J σ c → n'.J σ c0') → BlkW W' K exe endPc R F' n blk :=
    fun h hp ho hJ => blkW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c c0' h⟩
  have hN : ∀ {F' : MachineData → Prop} {n n' : ND}, NodeW W K exe endPc R F' n' → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → NodeW W' K exe endPc R F' n :=
    fun h hp ho hJ => nodeW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c c0' h⟩
  cases i <;> dsimp only [TakeW] at hi ⊢
  case site =>
    exact fun s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ => hW s c c0' (hi s c0' ⟨he, hn, hd, hp, σ, hA, hF, takeJ_c0 hJ⟩)
  case d0 | d26 | d52 | swp | ldn | b0 | unl | b31 | nxt | ok0 => exact hN hi rfl rfl (fun _ _ => takeJ_c0)
  all_goals exact hB hi rfl rfl (fun _ _ => takeJ_c0)

/-- **`scc_rt_thread_init`'s obligations at another control** (as
`takeW_c0`, its call's by `takeW_c0` at `tiTake`). -/
theorem tiW_c0 {q : TiG} {c0' : Ctl} (hW : ∀ s c c', W s c' → W' s c)
    (h : ∀ i, TiW W K exe endPc R F M { q with c0 := c0' } i) : ∀ i, TiW W' K exe endPc R F M q i := by
  intro i
  have hi := h i
  have hB : ∀ {F' : MachineData → Prop} {n n' : ND} {blk}, BlkW W K exe endPc R F' n' blk → n'.pc = n.pc →
      n'.o = n.o → (∀ σ c, n.J σ c → n'.J σ c0') → BlkW W' K exe endPc R F' n blk :=
    fun h hp ho hJ => blkW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c c0' h⟩
  have hN : ∀ {F' : MachineData → Prop} {n n' : ND}, NodeW W K exe endPc R F' n' → n'.pc = n.pc → n'.o = n.o →
      (∀ σ c, n.J σ c → n'.J σ c0') → NodeW W' K exe endPc R F' n :=
    fun h hp ho hJ => nodeW_mapC hp ho h fun σ c h' => ⟨c0', hJ σ c h', fun s h => hW s c c0' h⟩
  cases i <;> dsimp only [TiW] at hi ⊢
  case call => exact fun g hg j => takeW_c0 hW (hi g hg) j
  case x7 => exact hB hi rfl rfl (fun _ _ h => tiJ_c0 (i := .x7) h)
  case st0 | st1 | st2 | st3 | st4 | st5 => exact hN hi rfl rfl (fun _ _ => tiJ_c0)
  all_goals exact hB hi rfl rfl (fun _ _ => tiJ_c0)

end Spike.Lib.X64.WakePh.Ti2C0

/-- info: 'Spike.Lib.X64.WakePh.Ti2C0.blkW_mapC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2C0.blkW_mapC

/-- info: 'Spike.Lib.X64.WakePh.Ti2C0.nodeW_mapC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2C0.nodeW_mapC

/-- info: 'Spike.Lib.X64.WakePh.Ti2C0.takeJ_c0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2C0.takeJ_c0

/-- info: 'Spike.Lib.X64.WakePh.Ti2C0.tiJ_c0' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2C0.tiJ_c0

/-- info: 'Spike.Lib.X64.WakePh.Ti2C0.takeW_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2C0.takeW_c0

/-- info: 'Spike.Lib.X64.WakePh.Ti2C0.tiW_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.Ti2C0.tiW_c0
