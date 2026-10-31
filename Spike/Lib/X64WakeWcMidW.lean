/-
**`wc_main`'s obligations past the box's store: their conjunction, a
control change, and the clone's pc** (x86-64; the generic half of
`Spike/Lib/A64WakeWcMidW.lean`): the combinators the machine side of
`X64WakeWcHat.wake_wc_mid_hatW`'s `hW` is assembled with.

- `nodeW_and`, `blkW_and`, `reserveW_and`, `tcbWG_and`, `WcResW.and`,
  `WcSp3W.and`, `WcSp4PreW.and`, `WcClonePW.and`, `WcSp4PW.and`,
  `WcMidW.and`: two node obligations combine (the conjunction of the two
  predicates) at the first's outside move `K`.
- `wcNS_cloneAt`, `wcNS_clonePc`: a state at the clone's `syscall` (`wcNS`)
  is at `cloneAt exe`, i.e. `pcOf s = clonePc L`.
- `WcW.blkW_mapC`, `WcW.nodeW_mapC`: an obligation at another invariant
  (A64's are `A64WakeWcPreW`'s, here ahead of that file's twin).
- `WcMidWG.tcbWG_c0`: a control-blind obligation of `scc_rt_alloc_tcb` at
  one source control is one at any other.
- `WcMidWG.stackM_nil`: `StackM` of an empty range holds of every memory.

**Where this differs from AArch64**: x86-64's `WcMidW.sp4` is the published
`WcSp4PW` (`WcSp4PreW` and `WcClonePW`, `X64WakeWcPub`), so its conjunction
goes through `WcSp4PreW.and` and `WcClonePW.and` (A64: one `WcSp4W` of seven
nodes). The clone's pc has no prefix argument (`cloneAt exe`). **Not here**:
`wcSp3W_wcG`, `wcResW_wcG`, `wcMidW_wcG` (the `SFactsSt2`-at-`ownG`
instance) need the x86-64 twins of `A64WakeWcResWI` (`fenceW_wcG`,
`resBlW_wcG`, `reserveW_wcG`), `A64WakeWcSp4W` (`wcSp4W_wcG`, `BandTi`) and
`A64WakeWcPreWI`/`WcPreWN`/`WcPreW`, which do not exist yet.
-/
import Spike.Lib.X64WakeWcMid
import Spike.Lib.X64WakeWcInv

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.WakePh.WcClone (wcNS)
open Spike.Lib.X64.Rt (TcbGG TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.X64WakePreA (cloneAt)

/-! ## Conjunction -/

section And

variable {W₁ W₂ : Frag isa} {K K₂ : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}

/-- Two facts at a node's states combine (the first's outside move). -/
theorem nodeW_and {n : ND} (h₁ : NodeW W₁ K exe endPc R F n) (h₂ : NodeW W₂ K₂ exe endPc R F n) :
    NodeW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n :=
  fun s c hs => ⟨⟨(h₁ s c hs).1, (h₂ s c hs).1⟩, (h₁ s c hs).2⟩

/-- Two facts at a block node's states combine (the first's outside move). -/
theorem blkW_and {n : ND} {blk : List (Directive × Nat)} (h₁ : BlkW W₁ K exe endPc R F n blk)
    (h₂ : BlkW W₂ K₂ exe endPc R F n blk) : BlkW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    ⟨⟨(h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1, (h₂ s σ c he hn hd hp hA hF hJ k hk m hA' hD).1⟩,
      (h₁ s σ c he hn hd hp hA hF hJ k hk m hA' hD).2⟩

/-- The reserve's node obligations combine. -/
theorem reserveW_and {q : ResG} {i : Spike.Lib.X64.Rt.Reserve.RN} (h₁ : ReserveW W₁ K exe endPc R F q i)
    (h₂ : ReserveW W₂ K₂ exe endPc R F q i) : ReserveW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F q i := by
  cases i <;> dsimp only [ReserveW] at h₁ h₂ ⊢ <;> first | exact blkW_and h₁ h₂ | exact nodeW_and h₁ h₂

/-- `scc_rt_alloc_tcb`'s node obligations combine. -/
theorem tcbWG_and {q : TcbGG} {i : Ret0.TN} (h₁ : TcbWG W₁ K exe endPc R F q i)
    (h₂ : TcbWG W₂ K₂ exe endPc R F q i) : TcbWG (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F q i := by
  cases i <;> dsimp only [TcbWG] at h₁ h₂ ⊢ <;> first | exact blkW_and h₁ h₂ | exact nodeW_and h₁ h₂

/-- **From the call block to `.x19`**: two facts combine. -/
theorem WcResW.and {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcResW W₁ K exe endPc R F ms J0 Q) (h₂ : WcResW W₂ K₂ exe endPc R F ms J0 Q) :
    WcResW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F ms J0 Q :=
  ⟨blkW_and h₁.bl h₂.bl, fun g hg i => reserveW_and (h₁.res g hg i) (h₂.res g hg i)⟩

/-- **From `.x19` to `.x20`**: two facts combine. -/
theorem WcSp3W.and {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp3W W₁ K exe endPc R F c0 cA m fr) (h₂ : WcSp3W W₂ K₂ exe endPc R F c0 cA m fr) :
    WcSp3W (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 cA m fr :=
  ⟨blkW_and h₁.blk h₂.blk, fun g hg i => tcbWG_and (h₁.tcb g hg i) (h₂.tcb g hg i)⟩

/-- **From `.x20` to the call**: two facts combine. -/
theorem WcSp4PreW.and {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp4PreW W₁ K exe endPc R F c0 t cA m fr) (h₂ : WcSp4PreW W₂ K₂ exe endPc R F c0 t cA m fr) :
    WcSp4PreW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 t cA m fr :=
  ⟨blkW_and h₁.n20 h₂.n20, nodeW_and h₁.n20s h₂.n20s, blkW_and h₁.n20p h₂.n20p, nodeW_and h₁.nI h₂.nI⟩

/-- **The published clone's nodes**: two facts combine. -/
theorem WcClonePW.and {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t k cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (h₁ : WcClonePW W₁ K exe endPc R F c0 ty l t k cA m fr) (h₂ : WcClonePW W₂ K₂ exe endPc R F c0 ty l t k cA m fr) :
    WcClonePW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F c0 ty l t k cA m fr :=
  ⟨blkW_and h₁.n21 h₂.n21, nodeW_and h₁.nf h₂.nf, blkW_and h₁.na h₂.na, nodeW_and h₁.nd h₂.nd,
    nodeW_and h₁.n10 h₂.n10, blkW_and h₁.nr h₂.nr⟩

/-- **From `.x20` to the `syscall`, published**: two facts combine. -/
theorem WcSp4PW.and {F₂ : MachineData → Prop} {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64}
    (h₁ : WcSp4PW W₁ K exe endPc R F F₂ c0 ty l t cA m fr) (h₂ : WcSp4PW W₂ K₂ exe endPc R F F₂ c0 ty l t cA m fr) :
    WcSp4PW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F F₂ c0 ty l t cA m fr :=
  ⟨WcSp4PreW.and h₁.toWcSp4PreW h₂.toWcSp4PreW, WcClonePW.and h₁.clone h₂.clone⟩

/-- **From the box's store to the `syscall`**: two facts combine at the
first's outside move. -/
theorem WcMidW.and {F₂ : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h₁ : WcMidW W₁ K exe endPc R F F₂ ms J0 Q) (h₂ : WcMidW W₂ K₂ exe endPc R F F₂ ms J0 Q) :
    WcMidW (fun s c => W₁ s c ∧ W₂ s c) K exe endPc R F F₂ ms J0 Q :=
  ⟨WcResW.and h₁.res h₂.res, fun c0 cA m fr hM => WcSp3W.and (h₁.sp3 c0 cA m fr hM) (h₂.sp3 c0 cA m fr hM),
    fun c0 ty l cA m fr hM => WcSp4PW.and (h₁.sp4 c0 ty l cA m fr hM) (h₂.sp4 c0 ty l cA m fr hM)⟩

end And

/-! ## The clone's pc -/

/-- **A state at the clone's `syscall` is at `cloneAt exe`.** -/
theorem wcNS_cloneAt {exe : _root_.Executable} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At exe endPc R F (wcNS (_root_.Executable.labels exe).label c0 t k cA m fr) s c) :
    s.st.2 = cloneAt exe :=
  h.2.2.2.1

/-- **A state at the clone's `syscall` has `pcOf s = clonePc L`**, in `L`'s
executable. -/
theorem wcNS_clonePc {L : Spike.Lib.X64.Rt.RuntimeLayout} {endPc : Int64} {R : Region} {F : MachineData → Prop}
    {c0 : Ctl} {t k cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} {s : State} {c : Ctl}
    (h : At L.exe endPc R F (wcNS (_root_.Executable.labels L.exe).label c0 t k cA m fr) s c) :
    Scc.Sem.X64.pcOf s = clonePc L := by
  unfold Scc.Sem.X64.pcOf clonePc
  rw [wcNS_cloneAt h]

end Spike.Lib.X64.Flow.WakeWc

namespace Spike.Lib.X64.WakePh.WcW

open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64

/-- **A block node's obligation at another invariant**: at the same pc and
offsets, each `n`-state is an `n'`-state at some control `c'` whose `W`
states are `W'` states at `c`. -/
theorem blkW_mapC {W W' : Frag isa} {K : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
    {R : Region} {F : MachineData → Prop} {n n' : ND} {blk : List (Directive × Nat)} (hpc : n'.pc = n.pc)
    (ho : n'.o = n.o) (h : BlkW W K exe endPc R F n' blk)
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
    {R : Region} {F : MachineData → Prop} {n n' : ND} (hpc : n'.pc = n.pc) (ho : n'.o = n.o)
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

end Spike.Lib.X64.WakePh.WcW

namespace Spike.Lib.X64.WakePh.WcMidWG

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Range)
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (TcbGG TcbWG)
open Spike.Lib.X64.Flow.Ret0 (StackM)
open Spike.Lib.X64.WakePh.WcW (blkW_mapC nodeW_mapC)
open Spike.Lib.X64.WakePh.Tcb2Call (tcb2Q)

/-- **A control-blind obligation of `scc_rt_alloc_tcb` at one source control
is one at any other** (`tcb2Q g c0'` to `tcb2Q g c0`). -/
theorem tcbWG_c0 {W : Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {R : Region} {F : MachineData → Prop} (hW : ∀ s c c', W s c → W s c')
    {g : Spike.Lib.X64.Flow.Ret0.AllocTcb.G} {c0 c0' : Ctl} {i : Spike.Lib.X64.Flow.Ret0.TN}
    (h : TcbWG W K exe endPc R F (tcb2Q g c0') i) : TcbWG W K exe endPc R F (tcb2Q g c0) i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;>
    first
    | (refine blkW_mapC (n' := Spike.Lib.X64.Rt.tcbNG _ (tcb2Q g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)
    | (refine nodeW_mapC (n' := Spike.Lib.X64.Rt.tcbNG _ (tcb2Q g c0') _) rfl rfl h ?_
       rintro σ c ⟨-, hJ⟩
       exact ⟨c0', ⟨rfl, hJ⟩, fun s h => hW s _ _ h⟩)

/-- **The empty range is in private memory**: `StackM` at a range of size
`0` holds of every memory. -/
theorem stackM_nil (lo : Nat) (m : MachineData) : StackM ⟨lo, 0⟩ m :=
  fun _ _ h _ => absurd h (by simp [Range.contains])

end Spike.Lib.X64.WakePh.WcMidWG

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcMidW.and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcMidW.and

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wcNS_clonePc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wcNS_clonePc

/-- info: 'Spike.Lib.X64.WakePh.WcMidWG.tcbWG_c0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcMidWG.tcbWG_c0

/-- info: 'Spike.Lib.X64.WakePh.WcMidWG.stackM_nil' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.WcMidWG.stackM_nil
