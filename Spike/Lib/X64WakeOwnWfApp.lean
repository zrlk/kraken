/-
**The pre-spawn levels with appended owned words** (x86-64; X64-OwnW lift): `WakeWf.Wf` reads its
owned-words map only in its
`SFactsSt2` conjunct, so a state of `Wf`/`W0`/`W1` at `own` is one at
`own ++ ownS` wherever `ownS` may be appended (`AppOk`), or where the
state's instruction is the lone store taking `ownS`'s word (`takeS`). This
is the generic half of lifting main's pre-spawn producers from `ownG` to
`ownGX` (`ownS`, main's TCB word) and from `ownGX` to `ownGXW` (`ownSW`,
the worker's), the per-producer halves supplying `AppOk` as a `BlkW` /
`NodeW` of their own.

- `Wf.appendS`, `W0.appendS`, `W1.appendS`; `Wf.takeS`, `W0.takeS`.
- `BlkW.appendW`, `NodeW.appendW`: a block's (a node's) states inside a
  fragment at `own` are inside it at `own ++ ownS`, given `AppOk` as a
  `BlkW` (`NodeW`) and the fragment's lift statewise (`BlkW.imp`).
- `blkW_appOk`: `AppOk` on a covered block (its instructions write nothing,
  `exec_ai`) from `ownS` one list `c0` at the block's states and next
  states (`BlkW.leaf`) and `ownS` off `own` (`hd`).
- `nodeW_appOk`: `AppOk` at a node from `ownS` one list at it and its
  successors, the node's write condition, and `hd`.

**Deviations.** None: new lemmas, no producer changed.
-/
import Spike.Lib.X64WakeWf
import Spike.Lib.X64WakeOwnS2
import Spike.Lib.X64WakeOwnTake
import Spike.Lib.X64SpAgree
import Spike.Lib.X64AllocG

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Arena FragS)
open CoreLang CoreTerm
open Spike.Lib.X64Consumer (Own Lbl Lsize)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs)
open Spike.Lib.X64.WakeWf (Wf W0 W1)
open Kraken.Promising.Lower.X64 (CellAt)

variable {Λ : Scc.Sem.Layout} {μ : Marks} {own ownS : Own} {ar : Arena} {p : Prog}
  {Dt Ab Cl Ac : State → Prop} {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize}

/-! ## The levels, statewise -/

/-- **`Wf` with appended words** where they may be appended. -/
theorem _root_.Spike.Lib.X64.WakeWf.Wf.appendS {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs) (ha : AppOk μ own ownS s) :
    Wf Λ μ (fun s => own s ++ ownS s) ar p Dt Ab Cl Ac Ctx lbl lsize s c fs :=
  ⟨h.1.appendS ha, h.2⟩

/-- **`W0` with appended words** where they may be appended. -/
theorem _root_.Spike.Lib.X64.WakeWf.W0.appendS {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {X0 : State → Prop} {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs) (ha : AppOk μ own ownS s) :
    W0 Λ μ (fun s => own s ++ ownS s) ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs :=
  ⟨h.1, h.2.1, h.2.2.appendS ha⟩

/-- **`W1` with appended words** where they may be appended. -/
theorem _root_.Spike.Lib.X64.WakeWf.W1.appendS {L0 : Lbl} {ls0 : Lsize} {l : WeakMem.AllocLabel} {b n : Nat}
    {s : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : W1 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 l b n s c fs) (ha : AppOk μ own ownS s) :
    W1 Λ μ (fun s => own s ++ ownS s) ar p Dt Ab Cl Ac Ctx L0 ls0 l b n s c fs :=
  Spike.Lib.X64.WakeWf.Wf.appendS h ha

/-- **`Wf` with appended words at the store taking them** (`SFactsSt2.takeS`). -/
theorem _root_.Spike.Lib.X64.WakeWf.Wf.takeS {s s' : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    {kr : Kraken.StoreKind} {A : Loc} {V : Val} (h : Wf Λ μ own ar p Dt Ab Cl Ac Ctx lbl lsize s c fs)
    (hex : isa.exec s = some (.store kr false A V fun _ => .done s')) (h8 : A.bytes = 8) (hs0 : ownS s = [])
    (hs' : ownS s' = [(A, V)]) (hd : ∀ w, (A, w) ∉ own s) (hsys : abi.atSys s = false)
    (htk : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    Wf Λ μ (fun s => own s ++ ownS s) ar p Dt Ab Cl Ac Ctx lbl lsize s c fs :=
  ⟨h.1.takeS hex h8 hs0 hs' hd hsys htk, h.2⟩

/-- **`W0` with appended words at the store taking them.** -/
theorem _root_.Spike.Lib.X64.WakeWf.W0.takeS {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {X0 : State → Prop} {s s' : State} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    {kr : Kraken.StoreKind} {A : Loc} {V : Val} (h : W0 Λ μ own ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs)
    (hex : isa.exec s = some (.store kr false A V fun _ => .done s')) (h8 : A.bytes = 8) (hs0 : ownS s = [])
    (hs' : ownS s' = [(A, V)]) (hd : ∀ w, (A, w) ∉ own s) (hsys : abi.atSys s = false)
    (htk : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    W0 Λ μ (fun s => own s ++ ownS s) ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs :=
  ⟨h.1, h.2.1, h.2.2.takeS hex h8 hs0 hs' hd hsys htk⟩

/-! ## Blocks and nodes -/

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}
  {W W' : Spike.Lib.Frag isa} {K : State → State → Prop}

/-- **A block's states inside a lifted fragment**: inside `W`, `AppOk` at
each, and `W` with `AppOk` inside `W'` (`Wf.appendS` & co). -/
theorem _root_.Spike.Lib.X64.BlkW.appendW {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW W K exe endPc R F n blk)
    (ha : BlkW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n blk)
    (hw : ∀ s c, W s c → AppOk μ own ownS s → W' s c) : BlkW W' K exe endPc R F n blk :=
  Spike.Lib.X64.AllocG.BlkW.imp h ha hw

/-- **A node's states inside a lifted fragment** (`BlkW.appendW`'s node
form). -/
theorem _root_.Spike.Lib.X64.NodeW.appendW {n : ND} (h : NodeW W K exe endPc R F n)
    (ha : NodeW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n)
    (hw : ∀ s c, W s c → AppOk μ own ownS s → W' s c) : NodeW W' K exe endPc R F n :=
  Spike.Lib.X64.AllocG.NodeW.imp h ha hw

/-- **`AppOk` on a covered block**: its instructions write nothing
(`exec_ai`), `ownS` is `c0` at its states and next states, and off `own`. -/
theorem blkW_appOk {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {c0 : List (Loc × Val)}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → ownS s = c0)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) → ownS s = c0)
    (hd : ∀ s : State, ∀ l w w', (l, w) ∈ ownS s → (l, w') ∉ own s) :
    BlkW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n blk := by
  have hl := Spike.Lib.X64ConsumerA.BlkW.leaf (μ := μ) (F := F) (P := fun s => ownS s = c0)
    hcode hok hR hlo hhi hns hQ hP
  intro s σ c he hn hdc hpc hA hF hJ k hk m hA' hD
  obtain ⟨⟨h1, h2⟩, -⟩ := hl s σ c he hn hdc hpc hA hF hJ k hk m hA' hD
  refine ⟨⟨fun s' hs' => (h2 s' hs').trans h1.symm, fun _ tree hex => ?_, hd _⟩, fun _ h => h⟩
  obtain ⟨a, hca, haok, -⟩ :=
    Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.X64.classify_sound hca
  have hd' : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } a.toDir blk[k].2 :=
    (hcode s he hn).cell (j := k) (d := a.toDir) (z := blk[k].2) (by rw [hd', ← hdir]) rfl rfl rfl
  obtain ⟨m', hex', -⟩ := Spike.Lib.X64.exec_ai haok hR hlo hhi hc hreg hA'
  rw [hex'] at hex
  cases hex
  trivial

/-- **`AppOk` at a node**: `ownS` one list `c0` at the node's states and
their successors (`hq`), the node's instruction writing none of `c0`'s
words (`hw`), `ownS` off `own` (`hd`). -/
theorem nodeW_appOk {n : ND} {c0 : List (Loc × Val)}
    (hq : NodeW (fun s _ => ownS s = c0 ∧ ∀ s', StSucc μ s s' → ownS s' = c0) (fun _ _ => False) exe endPc R F n)
    (hw : NodeW (fun s _ => abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => ∀ w, (l, w) ∉ c0) tree) (fun _ _ => False) exe endPc R F n)
    (hd : ∀ s : State, ∀ l w w', (l, w) ∈ ownS s → (l, w') ∉ own s) :
    NodeW (fun s _ => AppOk μ own ownS s) (fun _ _ => False) exe endPc R F n := by
  intro s c hAt
  obtain ⟨⟨h1, h2⟩, -⟩ := hq s c hAt
  refine ⟨⟨fun s' hs' => (h2 s' hs').trans h1.symm, fun hns tree hex => ?_, hd _⟩, fun _ h => h⟩
  rw [h1]
  exact (hw s c hAt).1 hns tree hex

end Nodes

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakeWf.W0.appendS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.W0.appendS

/-- info: 'Spike.Lib.X64.WakeWf.W0.takeS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.W0.takeS

/-- info: 'Spike.Lib.X64.WakePh.blkW_appOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkW_appOk

/-- info: 'Spike.Lib.X64.WakePh.nodeW_appOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeW_appOk
