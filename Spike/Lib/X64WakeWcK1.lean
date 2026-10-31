/-
**`wc_main`'s obligations past the box's store at `h1`'s outside move**
(x86-64, the pre-spawn consumer; the twin of `Spike/Lib/A64WakeWcK1.lean`,
`X64WakeH1Inv.K1W`'s and `X1W`'s pc guards): from `WcMidW` at a stack take
at `a` to `WcMidW` at the take of the site's range or a `clone` refusal
(`TakeCKS a Cl`, `Cl` only at the clone's pc), the states off the clone's
and the take's pcs (what `X64WakeH1Inv.x1W_off` asks).

- `nodeW_mapWK`, `blkW_mapWK`, `reserveW_mapWK`, `tcbWG_mapWK`,
  `WcResW.mapWK`, `WcSp3W.mapWK`, `WcSp4PreW.mapWK`, `WcClonePW.mapWK`,
  `WcSp4PW.mapWK`, `WcMidW.mapWK`: node obligations under a pointwise change
  of the predicate and the outside move.
- `takeK_pc`, `takeCKS_none`, `pcOf_ne`: a state no take at `a` moves is
  off `a`; off `a` and the clone's pc, no take of the site's range and no
  refusal moves it.
- `ckRuns`, `ck_chk`, `ckIn`, `ckInB`, `ck_ne`: the byte runs holding
  `WcMidW`'s nodes (`wc_main` from `.x18 + 18` to the clone's `syscall`,
  `scc_rt_thread_reserve`, `scc_rt_alloc_tcb`, `scc_rt_thread_init`'s
  entry), none holding the clone's pc (`cloneAt exe`, `.x21 + 46`) nor the
  take site's (`scc_rt_take_site`), decided on wake's cells.
- `OffC`, `nodeW_offC`, `nodeW_offC0`, `blkW_offC`, `blkW_offC0`,
  `wcMidW_offC`: `WcMidW`'s states off the clone's pc and the take site's.
- `wcMidW_k1`: `WcMidW` at `TakeCKS a Cl` with both pcs avoided, from
  `WcMidW` at `TakeK a rK`.
- `wcMidW_k1S`: the same at the take site's label, from the listing alone.

**Where this differs from AArch64** (forced by the x86-64 shape):
- `WcMidW` has x86-64's nodes: the reserve's call block `rN .bl` (no fence
  node `f`: TSO, the fence is not a separate node of `WcResW`), and `sp4`
  is the published `WcSp4PW` (`WcSp4PreW`'s four nodes and `WcClonePW`'s
  six, from `.x20` through the `mfence` to the last instruction before the
  `syscall`), so the maps go through `WcSp4PreW.mapWK`/`WcClonePW.mapWK`;
  the source parameter `S` is absent (x86-64 `WcMidW` has `Q` only).
- Instructions have byte sizes: a node's pc is `label l + k` bytes, a
  block's `j`-th instruction at `+ cellOff blk j`; the runs are byte ranges
  (`X64RunsOff.runsNeChk`), each from its label up to the next of the two
  points (or the cells' end), and a block's bytes are its cells' sizes
  (`ckInB`, every size positive).
- The clone's pc has no prefix argument (`cloneAt exe`, `.x21 + 46`).

No absolute address appears in this file.
-/
import Spike.Lib.X64WakeWcMidW
import Spike.Lib.X64RunsOff

namespace Spike.Lib.X64.Flow.WakeWc

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64
open Spike.Lib.X64.Rt (TcbGG TcbWG)
open Spike.Lib.X64.Rt.Reserve (ResG ReserveW)
open Spike.Lib.X64.Flow.Ret0 (TakeK)
open Spike.Lib.X64ConsumerA (TakeKS TakeCKS)
open Spike.Lib.X64WakePreA (cloneAt)
open SccCode (wakeCells)
open Scc.Cert.Rt.X64 (Lays)
open Scc.Sem.X64 (pcOf)

/-! ## A pointwise change of the predicate and the outside move -/

section Map

variable {W W' : Frag isa} {K K' : State → State → Prop} {exe : _root_.Executable} {endPc : Int64}
  {R : Region} {F : MachineData → Prop}
  (hf : ∀ s c, W s c → (∀ s', ¬ K s s') → W' s c ∧ ∀ s', ¬ K' s s')
include hf

/-- A node's obligation under a pointwise change. -/
theorem nodeW_mapWK {n : ND} (h : NodeW W K exe endPc R F n) : NodeW W' K' exe endPc R F n :=
  fun s c hs => hf s c (h s c hs).1 (h s c hs).2

/-- A block node's obligation under a pointwise change. -/
theorem blkW_mapWK {n : ND} {blk : List (Directive × Nat)} (h : BlkW W K exe endPc R F n blk) :
    BlkW W' K' exe endPc R F n blk :=
  fun s σ c he hn hd hp hA hF hJ k hk m hA' hD =>
    hf _ c (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).1 (h s σ c he hn hd hp hA hF hJ k hk m hA' hD).2

/-- The reserve's node obligations under a pointwise change. -/
theorem reserveW_mapWK {q : ResG} {i : Spike.Lib.X64.Rt.Reserve.RN} (h : ReserveW W K exe endPc R F q i) :
    ReserveW W' K' exe endPc R F q i := by
  cases i <;> dsimp only [ReserveW] at h ⊢ <;> first | exact blkW_mapWK hf h | exact nodeW_mapWK hf h

/-- `scc_rt_alloc_tcb`'s node obligations under a pointwise change. -/
theorem tcbWG_mapWK {q : TcbGG} {i : Ret0.TN} (h : TcbWG W K exe endPc R F q i) :
    TcbWG W' K' exe endPc R F q i := by
  cases i <;> dsimp only [TcbWG] at h ⊢ <;> first | exact blkW_mapWK hf h | exact nodeW_mapWK hf h

/-- **From the call block to `.x19`** under a pointwise change. -/
theorem WcResW.mapWK {ms : MemSide isa} {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop}
    (h : WcResW W K exe endPc R F ms J0 Q) : WcResW W' K' exe endPc R F ms J0 Q :=
  ⟨blkW_mapWK hf h.bl, fun g hg i => reserveW_mapWK hf (h.res g hg i)⟩

/-- **From `.x19` to `.x20`** under a pointwise change. -/
theorem WcSp3W.mapWK {c0 : Ctl} {cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp3W W K exe endPc R F c0 cA m fr) : WcSp3W W' K' exe endPc R F c0 cA m fr :=
  ⟨blkW_mapWK hf h.blk, fun g hg i => tcbWG_mapWK hf (h.tcb g hg i)⟩

/-- **From `.x20` to the call** under a pointwise change. -/
theorem WcSp4PreW.mapWK {c0 : Ctl} {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64}
    (h : WcSp4PreW W K exe endPc R F c0 t cA m fr) : WcSp4PreW W' K' exe endPc R F c0 t cA m fr :=
  ⟨blkW_mapWK hf h.n20, nodeW_mapWK hf h.n20s, blkW_mapWK hf h.n20p, nodeW_mapWK hf h.nI⟩

/-- **The published clone's nodes** under a pointwise change. -/
theorem WcClonePW.mapWK {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel} {t k cA m : BitVec 64}
    {fr : BitVec 64 × BitVec 64} (h : WcClonePW W K exe endPc R F c0 ty l t k cA m fr) :
    WcClonePW W' K' exe endPc R F c0 ty l t k cA m fr :=
  ⟨blkW_mapWK hf h.n21, nodeW_mapWK hf h.nf, blkW_mapWK hf h.na, nodeW_mapWK hf h.nd,
    nodeW_mapWK hf h.n10, blkW_mapWK hf h.nr⟩

/-- **From `.x20` to the `syscall`, published**, under a pointwise change. -/
theorem WcSp4PW.mapWK {F₂ : MachineData → Prop} {c0 : Ctl} {ty : Ty} {l : WeakMem.AllocLabel}
    {t cA m : BitVec 64} {fr : BitVec 64 × BitVec 64} (h : WcSp4PW W K exe endPc R F F₂ c0 ty l t cA m fr) :
    WcSp4PW W' K' exe endPc R F F₂ c0 ty l t cA m fr :=
  ⟨WcSp4PreW.mapWK hf h.toWcSp4PreW, WcClonePW.mapWK hf h.clone⟩

/-- **From the box's store to the `syscall`** under a pointwise change of
the predicate and the outside move. -/
theorem WcMidW.mapWK {F₂ : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} (h : WcMidW W K exe endPc R F F₂ ms J0 Q) :
    WcMidW W' K' exe endPc R F F₂ ms J0 Q :=
  ⟨WcResW.mapWK hf h.res, fun c0 cA m fr hM => WcSp3W.mapWK hf (h.sp3 c0 cA m fr hM),
    fun c0 ty l cA m fr hM => WcSp4PW.mapWK hf (h.sp4 c0 ty l cA m fr hM)⟩

end Map

/-! ## The outside moves at a state -/

/-- **A state no take at `a` moves is off `a`**: at `a` the take of any
range from its own memory moves it. -/
theorem takeK_pc {a : Int64} {rS : Scc.Sem.Range} {s : State} (h : ∀ s', ¬ TakeK a rS s s') : s.st.2 ≠ a :=
  fun he => h _ ⟨he, Scc.Sem.X64.abi.dmem s, rfl⟩

/-- **Off the take's pc `a` and the clone's pc `cpc`**, neither the take of
the site's range nor a refusal at `Cl` (only at `cpc`) moves a state. -/
theorem takeCKS_none {a : Int64} {Cl : State → Prop} {cpc : Nat} (hCl : ∀ s, Cl s → pcOf s = cpc) {s : State}
    (ha : s.st.2 ≠ a) (hc : pcOf s ≠ cpc) : ∀ s', ¬ TakeCKS a Cl s s' :=
  fun _ h => h.elim (fun h => ha h.1) fun h => hc (hCl s h.1)

/-- A pc off `a` as an `Int64` is off it as a number. -/
theorem pcOf_ne {a : Int64} {s : State} (h : s.st.2 ≠ a) : pcOf s ≠ a.toBitVec.toNat :=
  fun e => h (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq e))

/-! ## The nodes' pcs off the clone's -/

/-- **The byte runs of `WcMidW`'s nodes**: `wc_main` from `.x18 + 18` (the
reserve's call block) through `.x19`, `.x20` and `.x21` up to the clone's
`syscall` (`.x21 + 46`), and `scc_rt_thread_reserve`'s, `scc_rt_alloc_tcb`'s
and `scc_rt_thread_init`'s labels, each up to the next of the two points
(the take site, the clone's `syscall`) in wake's cells. -/
def ckRuns : List (Label × Nat × Nat) :=
  [(".Lwc_main.x18", 18, 117), (".Lwc_main.x19", 0, 94), (WakePh.WcSp4.x20L, 0, 71),
   (WakePh.WcClone.x21L, 0, 46),
   (Flow.Reserve.fnL, 0, 830), (Flow.Reserve.entryL, 0, 822), (Flow.Reserve.okL, 0, 741),
   (Ret0.AllocTcb.fnL, 0, 1285), (Ret0.AllocTcb.entryL, 0, 1266), (Ret0.AllocTcb.lenL, 0, 1244),
   (Ret0.AllocTcb.okL, 0, 1030), (Ret0.ThreadInit.fnL, 0, 732)]

/-- **The runs' pcs are neither the clone's** (`.x21 + 46`) **nor the take
site's** (`scc_rt_take_site`), on wake's cells. -/
theorem ck_chk : Spike.Lib.X64.RunsOff.runsNeChk wakeCells ckRuns
    [(WakePh.WcClone.x21L, 46), (Ret0.StackTake.siteL, 0)] = true := by
  decide +kernel

/-- **`n` bytes from `l + k` lie in one of the runs.** -/
def ckIn (l : Label) (k n : Nat) : Bool :=
  ckRuns.any fun r => r.1 == l && decide (r.2.1 ≤ k) && decide (k + n ≤ r.2.2)

/-- **A block's bytes from `l + k` lie in one of the runs**, every cell of
the block of positive size. -/
def ckInB (l : Label) (k : Nat) (blk : List (Directive × Nat)) : Bool :=
  ckIn l k (blk.map (·.2)).sum && blk.all fun c => decide (0 < c.2)

/-- A block's `j`-th instruction is before its last byte, every cell of
positive size. -/
theorem cellOff_lt {blk : List (Directive × Nat)} (hpos : blk.all (fun c => decide (0 < c.2)) = true) {j : Nat}
    (hj : j < blk.length) : cellOff blk j < (blk.map (·.2)).sum := by
  have h1 := cellOff_succ hj
  have h2 : cellOff blk (j + 1) ≤ (blk.map (·.2)).sum := by
    have := congrArg (fun l : List (Directive × Nat) => (l.map (·.2)).sum) (List.take_append_drop (j + 1) blk)
    simp only [List.map_append, List.sum_append] at this
    unfold cellOff
    omega
  have h3 : 0 < blk[j].2 := by
    simpa using List.all_eq_true.mp hpos blk[j] (List.getElem_mem hj)
  omega

section Off

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat} (hp : Lays exe wakeCells kp)
  {endPc : Int64} {R : Region} {F : MachineData → Prop}
include hp

/-- **A pc of the runs is neither the clone's nor the take site's.** -/
theorem ck_ne {l : Label} {k n : Nat} (h : ckIn l k n = true) {j : Nat} (hj : j < n) :
    (_root_.Executable.labels exe).label l + Int64.ofNat (k + j) ≠ cloneAt exe ∧
      (_root_.Executable.labels exe).label l + Int64.ofNat (k + j) ≠
        (_root_.Executable.labels exe).label Ret0.StackTake.siteL := by
  obtain ⟨⟨l', lo, hi⟩, hr, hc⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨rfl, h1⟩, h2⟩ := hc
  have hn := Spike.Lib.X64.RunsOff.runsNe_of_chk hp ck_chk _ hr (k + j) (by show lo ≤ k + j; omega)
    (by show k + j < hi; omega)
  exact ⟨hn _ List.mem_cons_self, by
    simpa [Spike.Lib.X64.Flow.ofNat_zero'] using hn _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))⟩

/-- **Off the clone's pc and the take site's.** -/
def OffC (exe : _root_.Executable) : Frag isa := fun s _ =>
  s.st.2 ≠ cloneAt exe ∧ s.st.2 ≠ (_root_.Executable.labels exe).label Ret0.StackTake.siteL

/-- A node at `l + k` in the runs is off the clone's pc. -/
theorem nodeW_offC {n : ND} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat k) (h : ckIn l k 1 = true) :
    NodeW (OffC exe) (fun _ _ => False) exe endPc R F n :=
  fun _ _ ⟨_, _, _, hpc, _⟩ => ⟨by
    show _ ∧ _
    rw [hpc, he]
    simpa using ck_ne hp h (j := 0) (by decide), fun _ h => h⟩

/-- A node at a label in the runs is off the clone's pc. -/
theorem nodeW_offC0 {n : ND} {l : Label} (he : n.pc = (_root_.Executable.labels exe).label l)
    (h : ckIn l 0 1 = true) : NodeW (OffC exe) (fun _ _ => False) exe endPc R F n :=
  nodeW_offC hp (k := 0) (by rw [he, Spike.Lib.X64.Flow.ofNat_zero']) h

/-- A block node at `l + k` whose bytes are in the runs is off the clone's
pc. -/
theorem blkW_offC {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat}
    (he : n.pc = (_root_.Executable.labels exe).label l + Int64.ofNat k) (h : ckInB l k blk = true) :
    BlkW (OffC exe) (fun _ _ => False) exe endPc R F n blk := by
  simp only [ckInB, Bool.and_eq_true] at h
  exact fun _ _ _ _ _ _ _ _ _ _ j hj _ _ _ => ⟨by
    show _ ∧ _
    rw [he, Int64.add_assoc, ← Int64.ofNat_add]
    exact ck_ne hp h.1 (cellOff_lt h.2 hj), fun _ h => h⟩

/-- A block node at a label whose bytes are in the runs is off the clone's
pc. -/
theorem blkW_offC0 {n : ND} {blk : List (Directive × Nat)} {l : Label}
    (he : n.pc = (_root_.Executable.labels exe).label l) (h : ckInB l 0 blk = true) :
    BlkW (OffC exe) (fun _ _ => False) exe endPc R F n blk :=
  blkW_offC hp (k := 0) (by rw [he, Spike.Lib.X64.Flow.ofNat_zero']) h

/-- One node or block of `WcMidW` off the clone's pc. -/
local macro "offc" : tactic =>
  `(tactic| first
    | exact nodeW_offC hp rfl (by decide +kernel)
    | exact nodeW_offC0 hp rfl (by decide +kernel)
    | exact blkW_offC hp rfl (by decide +kernel)
    | exact blkW_offC0 hp rfl (by decide +kernel))

/-- **`WcMidW`'s states are off the clone's pc**, with no outside moves:
every node of `wc_main` from `.x18 + 18` to the clone's `syscall` and of
its callees is at a pc of `ckRuns`. -/
theorem wcMidW_offC {F₂ : MachineData → Prop} {ms : MemSide isa} {J0 : AS → Ctl → Prop}
    {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} :
    WcMidW (OffC exe) (fun _ _ => False) exe endPc R F F₂ ms J0 Q := by
  refine ⟨⟨?_, fun g _ i => ?_⟩, fun c0 cA m fr _ => ⟨?_, fun g _ i => ?_⟩,
    fun c0 ty l cA m fr _ => ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩⟩
  case refine_2 => cases i <;> dsimp only [ReserveW] <;> offc
  case refine_4 => cases i <;> dsimp only [TcbWG] <;> offc
  all_goals offc

end Off

/-! ## `h1`'s outside move -/

/-- **`WcMidW` at the take of the site's range or a refusal**, the states
off the clone's pc and the take's pc `a`, from `WcMidW` at a take at `a`:
no take at `a` moves a state, so it is off `a`; every state is off the
clone's pc (`wcMidW_offC`), where only the refusal `Cl` is (`hCl`). -/
theorem wcMidW_k1 {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeCells kp) {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isa}
    {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {W : Frag isa} {a : Int64}
    {rK : Scc.Sem.Range} {Cl : State → Prop} (hCl : ∀ s, Cl s → pcOf s = (cloneAt exe).toBitVec.toNat)
    (h : WcMidW W (TakeK a rK) exe endPc R F F₂ ms J0 Q) :
    WcMidW (fun s c => W s c ∧ pcOf s ≠ (cloneAt exe).toBitVec.toNat ∧ pcOf s ≠ a.toBitVec.toNat)
      (TakeCKS a Cl) exe endPc R F F₂ ms J0 Q :=
  WcMidW.mapWK (fun _ _ ⟨hW, hc, _⟩ hk =>
      ⟨⟨hW, pcOf_ne hc, pcOf_ne (takeK_pc hk)⟩, takeCKS_none hCl (takeK_pc hk) (pcOf_ne hc)⟩)
    (WcMidW.and h (wcMidW_offC hp))

/-- **`WcMidW` at the take of the site's range or a refusal**, the states
off the clone's pc and the take site's (`wcMidW_offC`): only a refusal at
`Cl` (`hCl`, at the clone's pc) or a take at the site moves a state. -/
theorem wcMidW_k1S {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {kp : Nat}
    (hp : Lays exe wakeCells kp) {endPc : Int64} {R : Region} {F F₂ : MachineData → Prop} {ms : MemSide isa}
    {J0 : AS → Ctl → Prop} {Q : WeakMem.AllocLabel → Nat → Ctl → Prop} {Cl : State → Prop}
    (hCl : ∀ s, Cl s → pcOf s = (cloneAt exe).toBitVec.toNat) :
    WcMidW (fun s _ => pcOf s ≠ (cloneAt exe).toBitVec.toNat ∧
        pcOf s ≠ ((_root_.Executable.labels exe).label Ret0.StackTake.siteL).toBitVec.toNat)
      (TakeCKS ((_root_.Executable.labels exe).label Ret0.StackTake.siteL) Cl) exe endPc R F F₂ ms J0 Q :=
  WcMidW.mapWK (fun _ _ ⟨hc, ha⟩ _ => ⟨⟨pcOf_ne hc, pcOf_ne ha⟩, takeCKS_none hCl ha (pcOf_ne hc)⟩)
    (wcMidW_offC hp)

end Spike.Lib.X64.Flow.WakeWc

/-- info: 'Spike.Lib.X64.Flow.WakeWc.WcMidW.mapWK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.WcMidW.mapWK

/-- info: 'Spike.Lib.X64.Flow.WakeWc.takeCKS_none' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.takeCKS_none

/-- info: 'Spike.Lib.X64.Flow.WakeWc.ck_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.ck_ne

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wcMidW_offC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wcMidW_offC

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wcMidW_k1' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wcMidW_k1

/-- info: 'Spike.Lib.X64.Flow.WakeWc.wcMidW_k1S' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Flow.WakeWc.wcMidW_k1S
