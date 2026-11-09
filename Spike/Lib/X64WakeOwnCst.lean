/-
**The two appended self words at a node, by the pc's class and `%rsp`**
(x86-64; X64-OwnW lift): the per-node half of lifting main's
pre-spawn producers from `ownG` to `ownGXW` (`ownG ++ ownS ++ ownSW`). At
every node of main's pre-spawn path the appended words are one of four
lists, fixed by the pc's class (the ranges `selfOwn` / `selfOwnW` read) and
whether `%rsp` is on the stack pool:

| class | `ownS` (`tcbM`) | `ownSW` (`tcb2`) |
|---|---|---|
| off the pool, no range (`cst_off`) | `[]` | `[]` |
| off the pool, `InA` or `InT` (`cst_offM`) | `tM` | `[]` |
| on the pool, from `.x1`, no `InT`/`InC` (`cst_pool`) | `tM` | `[]` |
| on the pool, `InT` or `InC` (`cst_poolW`) | `tM` | `tW` |
| below `.x1`, any `%rsp` (`cst_lowS`) | `[]` | `[]` |
| `InA`, any `%rsp` (`cst_A`) | `tM` | `[]` |

(none of them in the abort range, `InAb`). The last two read the pc alone:
`_start` and `scc_rt_start`'s head move `%rsp` (`andq $-16`, the switch),
so a `%rsp` band is not available there.

- `InA`, `InT`, `InC`, `InAb`: `scc_rt_start`'s `.x1` to `scc_rt_main`;
  `scc_rt_thread_init`'s `.x7 + 51` to `scc_rt_stack_take`; `wc_main`'s
  `.x21` to `.stk`; `scc_rt_abort` to `scc_rt_thr_worker` (at the canonical
  base, tied to the labels by `hlab`).
- `selfOwn_iffC`, `selfOwnW_iffC`: `selfOwn`/`selfOwnW` by the classes.
- `Cst L c1 c2 s`: `ownS L s = c1 ∧ ownSW L s = c2`; `cst_off`,
  `cst_offM`, `cst_pool`, `cst_poolW`, `cst_lowS`, `cst_A`.
- `CstOk`: the two `AppOk`s (`ownG`→`ownGX`, `ownGX`→`ownGXW`);
  `cstOk_of`: from `Cst` at the state and every successor, the
  instruction writing none of the words, the words off `ownG`'s
  (`PhRec.TcbSep`, `tcbM ≠ a`, `hW`).
- `W0.liftX`: `W0` at `ownG` is `W0` at `ownGXW` where `CstOk`.
- `blkW_cstOk`: `CstOk` on a covered block from `Cst` at its states and next
  states (its instructions write nothing); `nodeW_cstOk`: at a node from
  `Cst` at its states and successors, and its write condition.
- `cst_at`: `Cst` at a state from its pc's class and its `%rsp`'s offset in
  a region band (`BandOff`/`BandOn`).

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnWfApp
import Spike.Lib.X64WakeOwnT2

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (wakeCells)
open CoreLang CoreTerm
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Own Lbl Lsize)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakeWf (W0)
open Spike.Lib.Consumer1 (writeTree_mono)

/-! ## The pc's classes -/

/-- `scc_rt_start`'s `.x1` to `scc_rt_main`. -/
def InA (p : Nat) : Prop := 4198500 ≤ p ∧ p < 4198540
/-- `scc_rt_thread_init`'s `.x7 + 51` to `scc_rt_stack_take`. -/
def InT (p : Nat) : Prop := 4199620 ≤ p ∧ p < 4199695
/-- `wc_main`'s `.x21` to `.stk`. -/
def InC (p : Nat) : Prop := 4203435 ≤ p ∧ p < 4203552
/-- `scc_rt_abort` to `scc_rt_thr_worker`. -/
def InAb (p : Nat) : Prop := 4202487 ≤ p ∧ p < 4202973

instance (p : Nat) : Decidable (InA p) := by unfold InA; infer_instance
instance (p : Nat) : Decidable (InT p) := by unfold InT; infer_instance
instance (p : Nat) : Decidable (InC p) := by unfold InC; infer_instance
instance (p : Nat) : Decidable (InAb p) := by unfold InAb; infer_instance

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

private theorem labC (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo wakeCells l = some y) : L.lab l = Int64.ofNat y :=
  hlab _ _ (by rw [← codeT_eq]; exact h)

private theorem ofNat_toNat {n : Nat} (h : n < 2 ^ 64) : (Int64.ofNat n).toBitVec.toNat = n := by
  simp [Nat.mod_eq_of_lt h]

/-- **`selfOwn` by the classes.** -/
theorem selfOwn_iffC (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    selfOwn L s ↔ (spPool L s ∧ 4198500 ≤ pcOf s) ∨ InA (pcOf s) ∨ InT (pcOf s) := by
  have e1 : L.lab ".Lscc_rt_start.x1" = Int64.ofNat 4198500 := labC hlab (by decide +kernel)
  have eM : L.lab "scc_rt_main" = Int64.ofNat 4198540 := labC hlab (by decide +kernel)
  have e7 : L.lab ".Lscc_rt_thread_init.x0" = Int64.ofNat 4199569 := labC hlab (by decide +kernel)
  have eT : L.lab "scc_rt_stack_take" = Int64.ofNat 4199695 := labC hlab (by decide +kernel)
  unfold selfOwn inPc InA InT
  rw [e1, eM, e7, eT, ofNat_toNat (by decide), ofNat_toNat (by decide), ofNat_toNat (by decide),
    ofNat_toNat (by decide)]

/-- **`selfOwnW` by the classes**, off the abort range. -/
theorem selfOwnW_iffC (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
    (hab : ¬ InAb (pcOf s)) : selfOwnW L s ↔ (spPool L s ∧ InT (pcOf s)) ∨ InC (pcOf s) := by
  have e7 : L.lab ".Lscc_rt_thread_init.x0" = Int64.ofNat 4199569 := labC hlab (by decide +kernel)
  have eT : L.lab "scc_rt_stack_take" = Int64.ofNat 4199695 := labC hlab (by decide +kernel)
  have e21 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203435 := labC hlab (by decide +kernel)
  have eK : L.lab ".Lwc_main.stk" = Int64.ofNat 4203552 := labC hlab (by decide +kernel)
  have eA : L.lab "scc_rt_abort" = Int64.ofNat 4202487 := labC hlab (by decide +kernel)
  have eW : L.lab "scc_rt_thr_worker" = Int64.ofNat 4202973 := labC hlab (by decide +kernel)
  unfold selfOwnW inPc InT InC
  unfold InAb at hab
  rw [e7, eT, e21, eK, eA, eW, ofNat_toNat (by decide), ofNat_toNat (by decide), ofNat_toNat (by decide),
    ofNat_toNat (by decide), ofNat_toNat (by decide), ofNat_toNat (by decide)]
  constructor
  · rintro (h | h | ⟨h, -⟩)
    · exact .inl h
    · exact .inr h
    · exact absurd h hab
  · rintro (h | h)
    · exact .inl h
    · exact .inr (.inl h)

/-! ## The appended words by class -/

/-- Main's TCB word holding its address. -/
abbrev tM (L : RuntimeLayout) : List (Loc × Val) := [(⟨tcbM L, 8⟩, (tcbM L).setWidth 128)]
/-- The worker's TCB word holding its address. -/
abbrev tW (L : RuntimeLayout) : List (Loc × Val) := [(⟨tcb2 L, 8⟩, (tcb2 L).setWidth 128)]

/-- **The appended words at `s` are `c1` (main's) and `c2` (the worker's).** -/
def Cst (L : RuntimeLayout) (c1 c2 : List (Loc × Val)) (s : State) : Prop :=
  ownS L s = c1 ∧ ownSW L s = c2

section Classes

variable (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **Off the pool, in no range**: neither word. -/
theorem cst_off (hsp : ¬ spPool L s) (h : ¬ InA (pcOf s) ∧ ¬ InT (pcOf s) ∧ ¬ InC (pcOf s) ∧ ¬ InAb (pcOf s)) :
    Cst L [] [] s := by
  refine ⟨ownS_of_not ?_, ownSW_of_not ?_⟩
  · rw [selfOwn_iffC hlab]; rintro (h' | h' | h')
    · exact hsp h'.1
    · exact h.1 h'
    · exact h.2.1 h'
  · rw [selfOwnW_iffC hlab h.2.2.2]; rintro (⟨h', -⟩ | h')
    · exact hsp h'
    · exact h.2.2.1 h'
  where ownS_of_not {s : State} (h : ¬ selfOwn L s) : ownS L s = [] := by unfold ownS; simp [h]

/-- **Off the pool, in `InA` or `InT`**: main's word only. -/
theorem cst_offM (hsp : ¬ spPool L s) (h : (InA (pcOf s) ∨ InT (pcOf s)) ∧ ¬ InC (pcOf s) ∧ ¬ InAb (pcOf s)) :
    Cst L (tM L) [] s := by
  refine ⟨ownS_of_self ((selfOwn_iffC hlab).mpr (.inr h.1)), ownSW_of_not ?_⟩
  rw [selfOwnW_iffC hlab h.2.2]; rintro (⟨h', -⟩ | h')
  · exact hsp h'
  · exact h.2.1 h'

/-- **On the pool, in neither `InT` nor `InC`**: main's word only. -/
theorem cst_pool (hsp : spPool L s) (hx : 4198500 ≤ pcOf s)
    (h : ¬ InT (pcOf s) ∧ ¬ InC (pcOf s) ∧ ¬ InAb (pcOf s)) :
    Cst L (tM L) [] s := by
  refine ⟨ownS_of_self ((selfOwn_iffC hlab).mpr (.inl ⟨hsp, hx⟩)), ownSW_of_not ?_⟩
  rw [selfOwnW_iffC hlab h.2.2]; rintro (⟨-, h'⟩ | h')
  · exact h.1 h'
  · exact h.2.1 h'

/-- **On the pool, in `InT` or `InC`**: both words. -/
theorem cst_poolW (hsp : spPool L s) (h : (InT (pcOf s) ∨ InC (pcOf s)) ∧ ¬ InAb (pcOf s)) :
    Cst L (tM L) (tW L) s := by
  have hx : 4198500 ≤ pcOf s := by
    rcases h.1 with h' | h'
    · unfold InT at h'; omega
    · unfold InC at h'; omega
  refine ⟨ownS_of_self ((selfOwn_iffC hlab).mpr (.inl ⟨hsp, hx⟩)), ownSW_of_self ?_⟩
  rw [selfOwnW_iffC hlab h.2]
  rcases h.1 with h' | h'
  · exact .inl ⟨hsp, h'⟩
  · exact .inr h'

/-- **Below `.x1`** (`_start`, `scc_rt_start`'s head): neither word, by the pc alone. -/
theorem cst_lowS (h : pcOf s < 4198500) : Cst L [] [] s := by
  refine ⟨cst_off.ownS_of_not ?_, ownSW_of_not ?_⟩
  · rw [selfOwn_iffC hlab]; unfold InA InT; omega
  · have hab : ¬ InAb (pcOf s) := by unfold InAb; omega
    rw [selfOwnW_iffC hlab hab]; unfold InT InC; omega

/-- **In `InA`** (`scc_rt_start`'s `.x1` to `scc_rt_main`): main's word only, by the pc alone. -/
theorem cst_A (h : InA (pcOf s)) : Cst L (tM L) [] s := by
  refine ⟨ownS_of_self ((selfOwn_iffC hlab).mpr (.inr (.inl h))), ownSW_of_not ?_⟩
  unfold InA at h
  have hab : ¬ InAb (pcOf s) := by unfold InAb; omega
  rw [selfOwnW_iffC hlab hab]; unfold InT InC; omega

end Classes

/-! ## The two `AppOk`s -/

/-- **Both appended maps may be appended at `s`**: `ownS` to `ownG`, then
`ownSW` to `ownGX`. -/
def CstOk (μ : Marks) (L : RuntimeLayout) (a : BitVec 64) (s : State) : Prop :=
  AppOk μ (ownG L a) (ownS L) s ∧ AppOk μ (ownGX L a) (ownSW L) s

/-- **`CstOk` from `Cst`**: the words `c1`, `c2` at `s` and every
successor, the instruction writing none of them, `tcbM` off `ownG`'s words
(`hs`, `ha`) and `tcb2` off `ownGX`'s (`hW`). -/
theorem cstOk_of {μ : Marks} {c1 c2 : List (Loc × Val)} (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (h0 : Cst L c1 c2 s)
    (hsc : ∀ s', StSucc μ s s' → Cst L c1 c2 s')
    (hw : abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    CstOk μ L a s := by
  refine ⟨⟨fun s' h => (hsc s' h).1.trans h0.1.symm, fun hns tree he => ?_, ownS_disj hs ha⟩,
    ⟨fun s' h => (hsc s' h).2.trans h0.2.symm, fun hns tree he => ?_, ?_⟩⟩
  · rw [h0.1]; exact writeTree_mono (fun _ _ h => h.1) (hw hns tree he)
  · rw [h0.2]; exact writeTree_mono (fun _ _ h => h.2) (hw hns tree he)
  · exact ownSW_disj hW

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isa}

/-- **`W0` at `ownG` is `W0` at `ownGXW`** where both maps may be appended. -/
theorem _root_.Spike.Lib.X64.WakeWf.W0.liftX {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {X0 : State → Prop} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : W0 Λ μ (ownG L a) ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs) (hc : CstOk μ L a s) :
    W0 Λ μ (ownGXW L a) ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs :=
  Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownSW L) (own := ownGX L a)
    (Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownS L) (own := ownG L a) h hc.1) hc.2

/-! ## Blocks and nodes -/

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`CstOk` on a covered block**: `Cst` at its states (`hQ`) and next
states (`hP`); its instructions write nothing. -/
theorem blkW_cstOk {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {c1 c2 : List (Loc × Val)}
    (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → Cst L c1 c2 s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      Cst L c1 c2 s) :
    BlkW (fun s _ => CstOk μ L a s) (fun _ _ => False) exe endPc R F n blk := by
  have h1 := blkW_appOk (μ := μ) (F := F) (own := ownG L a) (ownS := ownS L) (c0 := c1) hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs' => (hQ σ c hJ k hk s m hA he hn hs').1)
    (fun σ c hJ k hk s m hA he hn hs' => (hP σ c hJ k hk s m hA he hn hs').1) (fun _ => ownS_disj hs ha)
  have h2 := blkW_appOk (μ := μ) (F := F) (own := ownGX L a) (ownS := ownSW L) (c0 := c2) hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs' => (hQ σ c hJ k hk s m hA he hn hs').2)
    (fun σ c hJ k hk s m hA he hn hs' => (hP σ c hJ k hk s m hA he hn hs').2) (fun _ => ownSW_disj hW)
  exact Spike.Lib.X64.AllocG.BlkW.imp h1 h2 fun _ _ a1 a2 => ⟨a1, a2⟩

/-- **`CstOk` at a node**: `Cst` at its states and their successors (`hq`),
its instruction writing none of the words (`hw`). -/
theorem nodeW_cstOk {n : ND} {c1 c2 : List (Loc × Val)} (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hq : ∀ s c, At exe endPc R F n s c → Cst L c1 c2 s ∧ ∀ s', StSucc μ s s' → Cst L c1 c2 s')
    (hw : ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (fun s _ => CstOk μ L a s) (fun _ _ => False) exe endPc R F n := fun s c hAt =>
  ⟨cstOk_of hs ha hW (hq s c hAt).1 (hq s c hAt).2 (hw s c hAt), fun _ h => h⟩

/-- **A node's instruction writes nothing**, the words empty: no write
condition at `c1 = c2 = []`. -/
theorem hw_nil {n : ND} : ∀ (s : State) (c : Spike.Lib.Ctl), At exe endPc R F n s c → abi.atSys s = false → ∀ tree,
    isa.exec s = some tree → WriteTree (fun l _ => (∀ w, (l, w) ∉ ([] : List (Loc × Val))) ∧
      ∀ w, (l, w) ∉ ([] : List (Loc × Val))) tree :=
  fun _ _ _ _ tree _ => writeTree_mono (fun _ _ _ => ⟨fun _ h => by simp at h, fun _ h => by simp at h⟩)
    (Spike.Lib.Consumer1.writeTree_true tree)

end Nodes

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.selfOwn_iffC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.selfOwn_iffC

/-- info: 'Spike.Lib.X64.WakePh.cst_poolW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cst_poolW

/-- info: 'Spike.Lib.X64.WakePh.cstOk_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cstOk_of

/-- info: 'Spike.Lib.X64.WakeWf.W0.liftX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.W0.liftX

/-- info: 'Spike.Lib.X64.WakePh.blkW_cstOk' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkW_cstOk

/-- info: 'Spike.Lib.X64.WakePh.cst_lowS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cst_lowS

/-- info: 'Spike.Lib.X64.WakePh.cst_A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cst_A
