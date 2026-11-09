/-
**The two appended self words at a node, by the pc's class and `%rsp`** (x86-64 only; the hello counterpart of
`X64WakeOwnCst` and `X64WakeOwnCstN`): the per-node half of lifting main's pre-spawn producers from `ownGH` to
`ownGHXW` (`ownGH ++ ownSH ++ ownSWH`, `X64HelloOwnSX`). At every node of main's pre-spawn path the appended words
are one of four lists, fixed by the pc's class (the ranges `selfOwnH` / `selfOwnWH` read) and whether `%rsp` is
on the stack pool:

| class | `ownSH` (`tcbM`) | `ownSWH` (`tcbWH`) |
|---|---|---|
| off the pool, no range (`cstH_off`) | `[]` | `[]` |
| off the pool, `InAH` or `InTH` (`cstH_offM`) | `tM` | `[]` |
| on the pool, from `.x1`, no `InTH`/`InCH` (`cstH_pool`) | `tM` | `[]` |
| on the pool, `InTH` or `InCH` (`cstH_poolW`) | `tM` | `tWH` |
| below `.x1`, any `%rsp` (`cstH_lowS`) | `[]` | `[]` |
| `InAH`, any `%rsp` (`cstH_A`) | `tM` | `[]` |

(none of them in the abort range `InAbH`).

- `InAH`, `InTH`, `InCH`, `InAbH`: `scc_rt_start`'s `.x1` to `scc_rt_main`; `scc_rt_thread_init`'s `.x8 + 51` to
  `scc_rt_stack_take`; `wc_main`'s `.x25` to `.stk`; `scc_rt_abort` to `scc_rt_thr_worker` (at the canonical
  base, tied to the labels by `hlab`).
- `selfOwnH_iffC`, `selfOwnWH_iffC`: `selfOwnH`/`selfOwnWH` by the classes.
- `CstH L c1 c2 s`: `ownSH L s = c1 ∧ ownSWH L s = c2`; `cstH_off`, `cstH_offM`, `cstH_pool`, `cstH_poolW`,
  `cstH_lowS`, `cstH_A`.
- `CstOkH`: the two `AppOk`s (`ownGH`→`ownGHX`, `ownGHX`→`ownGHXW`); `cstOkH_of`.
- `W0.liftHX`: `W0` at `ownGH` is `W0` at `ownGHXW` where `CstOkH`.
- `blkW_cstOkH`, `nodeW_cstOkH`: `CstOkH` on a covered block / at a node from `CstH` at its states and
  successors; `blkW_cstOkHB`, `nodeW_cstOkHK`: from the pcs and the static `%rsp` offsets (a class `hcls`).
- `NoHH`, `cls_offH`, `cls_poolH`, `cls_poolWH`, `cls_offMH`: the classes as `hcls`, with wake's `BandOffP`,
  `BandOnP` (generic in the layout).

Wake's `AppOk`, `blkW_appOk`, `W0.appendS`, `hw_nil`, `tM`, `soRun`/`arun_so`, `Keep` and the `AllocG.BlkW.imp`
combinator are used as they are.

## Differences from the AArch64 version

AArch64 has no counterpart (main owns no TCB word there). Against wake's x86-64 classes: `InTH` starts at
`scc_rt_thread_init`'s `.x8 + 51` (hello's listing; wake `.x7 + 51`), `InCH` is `wc_main`'s `.x25` to `.stk`
(wake `.x21`), the abort range and `scc_rt_stack_take` are at hello's addresses, and the worker's word is
`tcbWH = pinA + 144` (wake `tcb2 = pinA + 136`). `InAH` is the same range as wake's (the runtime's prefix is
laid out identically).
-/
import Spike.Lib.X64HelloOwnSX
import Spike.Lib.X64WakeOwnCstN

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Cert.Rt.X64 (codeT codeT_eq)
open SccCode (helloCells)
open CoreLang CoreTerm
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Own Lbl Lsize)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakeWf (W0)
open Spike.Lib.Consumer1 (writeTree_mono)
open Spike.Lib.X64.WakePh (inPc spPool raAt tcbM tM AppOk blkW_appOk BandOffP BandOnP Keep)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64HelloOwnLift (tcbWH)

/-! ## The pc's classes -/

/-- `scc_rt_start`'s `.x1` to `scc_rt_main`. -/
def InAH (p : Nat) : Prop := 4198500 ≤ p ∧ p < 4198540
/-- `scc_rt_thread_init`'s `.x8 + 51` to `scc_rt_stack_take`. -/
def InTH (p : Nat) : Prop := 4199657 ≤ p ∧ p < 4199732
/-- `wc_main`'s `.x25` to `.stk`. -/
def InCH (p : Nat) : Prop := 4203812 ≤ p ∧ p < 4203986
/-- `scc_rt_abort` to `scc_rt_thr_worker`. -/
def InAbH (p : Nat) : Prop := 4202524 ≤ p ∧ p < 4203010

instance (p : Nat) : Decidable (InAH p) := by unfold InAH; infer_instance
instance (p : Nat) : Decidable (InTH p) := by unfold InTH; infer_instance
instance (p : Nat) : Decidable (InCH p) := by unfold InCH; infer_instance
instance (p : Nat) : Decidable (InAbH p) := by unfold InAbH; infer_instance

variable {L : RuntimeLayout} {a : BitVec 64} {s : State}

private theorem labCH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {l : Label}
    {y : Nat} (h : codeT lo helloCells l = some y) : L.lab l = Int64.ofNat y :=
  hlab _ _ (by rw [← codeT_eq]; exact h)

private theorem ofNat_toNatH {n : Nat} (h : n < 2 ^ 64) : (Int64.ofNat n).toBitVec.toNat = n := by
  simp [Nat.mod_eq_of_lt h]

/-- **`selfOwnH` by the classes.** -/
theorem selfOwnH_iffC (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    selfOwnH L s ↔ (spPool L s ∧ 4198500 ≤ pcOf s) ∨ InAH (pcOf s) ∨ InTH (pcOf s) := by
  have e1 : L.lab ".Lscc_rt_start.x1" = Int64.ofNat 4198500 := labCH hlab (by decide +kernel)
  have eM : L.lab "scc_rt_main" = Int64.ofNat 4198540 := labCH hlab (by decide +kernel)
  have e8 : L.lab ".Lscc_rt_thread_init.x0" = Int64.ofNat 4199606 := labCH hlab (by decide +kernel)
  have eT : L.lab "scc_rt_stack_take" = Int64.ofNat 4199732 := labCH hlab (by decide +kernel)
  unfold selfOwnH inPc InAH InTH
  rw [e1, eM, e8, eT, ofNat_toNatH (by decide), ofNat_toNatH (by decide), ofNat_toNatH (by decide),
    ofNat_toNatH (by decide)]

/-- **`selfOwnWH` by the classes**, off the abort range. -/
theorem selfOwnWH_iffC (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
    (hab : ¬ InAbH (pcOf s)) : selfOwnWH L s ↔ (spPool L s ∧ InTH (pcOf s)) ∨ InCH (pcOf s) := by
  have e8 : L.lab ".Lscc_rt_thread_init.x0" = Int64.ofNat 4199606 := labCH hlab (by decide +kernel)
  have eT : L.lab "scc_rt_stack_take" = Int64.ofNat 4199732 := labCH hlab (by decide +kernel)
  have e25 : L.lab ".Lwc_main.x3" = Int64.ofNat 4203812 := labCH hlab (by decide +kernel)
  have eK : L.lab ".Lwc_main.stk" = Int64.ofNat 4203986 := labCH hlab (by decide +kernel)
  have eA : L.lab "scc_rt_abort" = Int64.ofNat 4202524 := labCH hlab (by decide +kernel)
  have eW : L.lab "scc_rt_thr_worker" = Int64.ofNat 4203010 := labCH hlab (by decide +kernel)
  unfold selfOwnWH inPc InTH InCH
  unfold InAbH at hab
  rw [e8, eT, e25, eK, eA, eW, ofNat_toNatH (by decide), ofNat_toNatH (by decide), ofNat_toNatH (by decide),
    ofNat_toNatH (by decide), ofNat_toNatH (by decide), ofNat_toNatH (by decide)]
  constructor
  · rintro (h | h | ⟨h, -⟩)
    · exact .inl h
    · exact .inr h
    · exact absurd h hab
  · rintro (h | h)
    · exact .inl h
    · exact .inr (.inl h)

/-! ## The appended words by class -/

/-- **The appended words at `s` are `c1` (main's) and `c2` (the worker's).** -/
def CstH (L : RuntimeLayout) (c1 c2 : List (Loc × Val)) (s : State) : Prop :=
  ownSH L s = c1 ∧ ownSWH L s = c2

section Classes

variable (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **Off the pool, in no range**: neither word. -/
theorem cstH_off (hsp : ¬ spPool L s)
    (h : ¬ InAH (pcOf s) ∧ ¬ InTH (pcOf s) ∧ ¬ InCH (pcOf s) ∧ ¬ InAbH (pcOf s)) : CstH L [] [] s := by
  refine ⟨ownSH_of_not ?_, ownSWH_of_not ?_⟩
  · rw [selfOwnH_iffC hlab]; rintro (h' | h' | h')
    · exact hsp h'.1
    · exact h.1 h'
    · exact h.2.1 h'
  · rw [selfOwnWH_iffC hlab h.2.2.2]; rintro (⟨h', -⟩ | h')
    · exact hsp h'
    · exact h.2.2.1 h'

/-- **Off the pool, in `InAH` or `InTH`**: main's word only. -/
theorem cstH_offM (hsp : ¬ spPool L s)
    (h : (InAH (pcOf s) ∨ InTH (pcOf s)) ∧ ¬ InCH (pcOf s) ∧ ¬ InAbH (pcOf s)) : CstH L (tM L) [] s := by
  refine ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inr h.1)), ownSWH_of_not ?_⟩
  rw [selfOwnWH_iffC hlab h.2.2]; rintro (⟨h', -⟩ | h')
  · exact hsp h'
  · exact h.2.1 h'

/-- **On the pool, in neither `InTH` nor `InCH`**: main's word only. -/
theorem cstH_pool (hsp : spPool L s) (hx : 4198500 ≤ pcOf s)
    (h : ¬ InTH (pcOf s) ∧ ¬ InCH (pcOf s) ∧ ¬ InAbH (pcOf s)) : CstH L (tM L) [] s := by
  refine ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inl ⟨hsp, hx⟩)), ownSWH_of_not ?_⟩
  rw [selfOwnWH_iffC hlab h.2.2]; rintro (⟨-, h'⟩ | h')
  · exact h.1 h'
  · exact h.2.1 h'

/-- **On the pool, in `InTH` or `InCH`**: both words. -/
theorem cstH_poolW (hsp : spPool L s) (h : (InTH (pcOf s) ∨ InCH (pcOf s)) ∧ ¬ InAbH (pcOf s)) :
    CstH L (tM L) (tWH L) s := by
  have hx : 4198500 ≤ pcOf s := by
    rcases h.1 with h' | h'
    · unfold InTH at h'; omega
    · unfold InCH at h'; omega
  refine ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inl ⟨hsp, hx⟩)), ownSWH_of_self ?_⟩
  rw [selfOwnWH_iffC hlab h.2]
  rcases h.1 with h' | h'
  · exact .inl ⟨hsp, h'⟩
  · exact .inr h'

/-- **Below `.x1`** (`_start`, `scc_rt_start`'s head): neither word, by the pc alone. -/
theorem cstH_lowS (h : pcOf s < 4198500) : CstH L [] [] s := by
  refine ⟨ownSH_of_not ?_, ownSWH_of_not ?_⟩
  · rw [selfOwnH_iffC hlab]; unfold InAH InTH; omega
  · have hab : ¬ InAbH (pcOf s) := by unfold InAbH; omega
    rw [selfOwnWH_iffC hlab hab]; unfold InTH InCH; omega

/-- **In `InAH`** (`scc_rt_start`'s `.x1` to `scc_rt_main`): main's word only, by the pc alone. -/
theorem cstH_A (h : InAH (pcOf s)) : CstH L (tM L) [] s := by
  refine ⟨ownSH_of_self ((selfOwnH_iffC hlab).mpr (.inr (.inl h))), ownSWH_of_not ?_⟩
  unfold InAH at h
  have hab : ¬ InAbH (pcOf s) := by unfold InAbH; omega
  rw [selfOwnWH_iffC hlab hab]; unfold InTH InCH; omega

end Classes

/-! ## The two `AppOk`s -/

/-- **Both appended maps may be appended at `s`**: `ownSH` to `ownGH`, then `ownSWH` to `ownGHX`. -/
def CstOkH (μ : Marks) (L : RuntimeLayout) (a : BitVec 64) (s : State) : Prop :=
  AppOk μ (ownGH L a) (ownSH L) s ∧ AppOk μ (ownGHX L a) (ownSWH L) s

/-- **`CstOkH` from `CstH`**: the words `c1`, `c2` at `s` and every successor, the instruction writing none of
them, `tcbM` off `ownGH`'s words (`hs`, `ha`) and `tcbWH` off `ownGHX`'s (`hW`). -/
theorem cstOkH_of {μ : Marks} {c1 c2 : List (Loc × Val)} (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a]) (h0 : CstH L c1 c2 s)
    (hsc : ∀ s', StSucc μ s s' → CstH L c1 c2 s')
    (hw : abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    CstOkH μ L a s := by
  refine ⟨⟨fun s' h => (hsc s' h).1.trans h0.1.symm, fun hns tree he => ?_, ownSH_disj hs ha⟩,
    ⟨fun s' h => (hsc s' h).2.trans h0.2.symm, fun hns tree he => ?_, ?_⟩⟩
  · rw [h0.1]; exact writeTree_mono (fun _ _ h => h.1) (hw hns tree he)
  · rw [h0.2]; exact writeTree_mono (fun _ _ h => h.2) (hw hns tree he)
  · exact ownSWH_disj hW

variable {Λ : Scc.Sem.Layout} {μ : Marks} {ar : Arena} {p : Prog} {Dt Ab Cl Ac : State → Prop}
  {Ctx : FragS isa}

/-- **`W0` at `ownGH` is `W0` at `ownGHXW`** where both maps may be appended. -/
theorem _root_.Spike.Lib.X64.WakeWf.W0.liftHX {L0 : Lbl} {ls0 : Lsize} {frM : TermRun.Frame}
    {X0 : State → Prop} {c : Spike.Lib.Ctl} {fs : List TermRun.Frame}
    (h : W0 Λ μ (ownGH L a) ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs) (hc : CstOkH μ L a s) :
    W0 Λ μ (ownGHXW L a) ar p Dt Ab Cl Ac Ctx L0 ls0 frM X0 s c fs :=
  Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownSWH L) (own := ownGHX L a)
    (Spike.Lib.X64.WakeWf.W0.appendS (ownS := ownSH L) (own := ownGH L a) h hc.1) hc.2

/-! ## Blocks and nodes -/

section Nodes

variable {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`CstOkH` on a covered block**: `CstH` at its states (`hQ`) and next states (`hP`); its instructions write
nothing. -/
theorem blkW_cstOkH {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {c1 c2 : List (Loc × Val)}
    (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → CstH L c1 c2 s)
    (hP : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc →
      s.st = (m, (arun (_root_.Executable.labels exe).label (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).pc) →
      CstH L c1 c2 s) :
    BlkW (fun s _ => CstOkH μ L a s) (fun _ _ => False) exe endPc R F n blk := by
  have h1 := blkW_appOk (μ := μ) (F := F) (own := ownGH L a) (ownS := ownSH L) (c0 := c1) hcode hok hR hlo hhi hns
    (fun σ c hJ k hk s m hA he hn hs' => (hQ σ c hJ k hk s m hA he hn hs').1)
    (fun σ c hJ k hk s m hA he hn hs' => (hP σ c hJ k hk s m hA he hn hs').1) (fun _ => ownSH_disj hs ha)
  have h2 := blkW_appOk (μ := μ) (F := F) (own := ownGHX L a) (ownS := ownSWH L) (c0 := c2) hcode hok hR hlo hhi
    hns (fun σ c hJ k hk s m hA he hn hs' => (hQ σ c hJ k hk s m hA he hn hs').2)
    (fun σ c hJ k hk s m hA he hn hs' => (hP σ c hJ k hk s m hA he hn hs').2) (fun _ => ownSWH_disj hW)
  exact Spike.Lib.X64.AllocG.BlkW.imp h1 h2 fun _ _ a1 a2 => ⟨a1, a2⟩

/-- **`CstOkH` at a node**: `CstH` at its states and their successors (`hq`), its instruction writing none of the
words (`hw`). -/
theorem nodeW_cstOkH {n : ND} {c1 c2 : List (Loc × Val)} (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a)
    (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hq : ∀ s c, At exe endPc R F n s c → CstH L c1 c2 s ∧ ∀ s', StSucc μ s s' → CstH L c1 c2 s')
    (hw : ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (fun s _ => CstOkH μ L a s) (fun _ _ => False) exe endPc R F n := fun s c hAt =>
  ⟨cstOkH_of hs ha hW (hq s c hAt).1 (hq s c hAt).2 (hw s c hAt), fun _ h => h⟩

/-- **`CstOkH` on a covered block** from the class `hcls` at its pcs (`h1`, in `P`) with its prefixes' static
`%rsp` offsets in `[slo, shi]` (`hso`), and `CstH` where its run ends (`hfin`). -/
theorem blkW_cstOkHB {n : ND} {blk : List (Directive × Nat)} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (h1 : ∀ k < blk.length, P (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat)
    (hso : ∀ k ≤ blk.length, slo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      CstH L c1 c2 s) :
    BlkW (fun s _ => CstOkH μ L a s) (fun _ _ => False) exe endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → CstH L c1 c2 s := by
    intro σ c _ k hk s m hA _ _ hs'
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hcls s (by unfold pcOf; rw [hs']; exact h1 k hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA
  refine blkW_cstOkH hs ha hW hcode hok hR hlo hhi hns hQ ?_
  intro σ c hJ k hk s m hA he hn hs'
  rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
  · rw [Spike.Lib.X64.arun_pc _ hok hk1] at hs'
    exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs'
  · rw [List.take_of_length_le (by omega)] at hA hs'
    exact hfin σ c hJ s m hA he hn hs'

/-- **`CstOkH` at a node** whose successors keep `%rsp` and `%rbp` `sz` bytes on (`hk`): the class at its pc and
the next (`hpc`), its static `%rsp` offset in `[slo, shi]` (`hso`), its write condition (`hw`). -/
theorem nodeW_cstOkHK {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (fun s _ => CstOkH μ L a s) (fun _ _ => False) exe endPc R F n := by
  refine nodeW_cstOkH hs ha hW (fun s c hAt => ?_) hw
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.rsp.toBitVec = R.addr n.o.sp := rsp_of_abs hA
  refine ⟨hcls s (by unfold pcOf; rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact hcls s' (by unfold pcOf; rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

end Nodes

/-! ## The classes as `hcls` -/

/-- **No range**: none of `InAH`, `InTH`, `InCH`, `InAbH`. -/
def NoHH (p : Nat) : Prop := ¬ InAH p ∧ ¬ InTH p ∧ ¬ InCH p ∧ ¬ InAbH p

instance (p : Nat) : Decidable (NoHH p) := by unfold NoHH; infer_instance

section Cls

variable {R : Spike.Lib.Region} (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **Neither word** at a state in no range with `%rsp` in a band off the pool. -/
theorem cls_offH {slo shi : Int} (hb : BandOffP L R slo shi) :
    ∀ s : State, NoHH (pcOf s) → SpAt R slo shi s → CstH L [] [] s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cstH_off hlab ?_ hp
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- **Main's word only** at a state from `.x1` on, in neither `InTH` nor `InCH` (nor `InAbH`), with `%rsp` in a
band on the pool. -/
theorem cls_poolH {slo shi : Int} (hb : BandOnP L R slo shi) :
    ∀ s : State, (4198500 ≤ pcOf s ∧ ¬ InTH (pcOf s) ∧ ¬ InCH (pcOf s) ∧ ¬ InAbH (pcOf s)) →
      SpAt R slo shi s → CstH L (tM L) [] s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cstH_pool hlab ?_ hp.1 hp.2
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- **Both words** at a state in `InTH` or `InCH` (not `InAbH`) with `%rsp` in a band on the pool. -/
theorem cls_poolWH {slo shi : Int} (hb : BandOnP L R slo shi) :
    ∀ s : State, ((InTH (pcOf s) ∨ InCH (pcOf s)) ∧ ¬ InAbH (pcOf s)) → SpAt R slo shi s →
      CstH L (tM L) (tWH L) s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cstH_poolW hlab ?_ hp
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- **Main's word only** at a state in `InAH` or `InTH` (not `InCH`, `InAbH`) with `%rsp` in a band off the
pool. -/
theorem cls_offMH {slo shi : Int} (hb : BandOffP L R slo shi) :
    ∀ s : State, ((InAH (pcOf s) ∨ InTH (pcOf s)) ∧ ¬ InCH (pcOf s) ∧ ¬ InAbH (pcOf s)) → SpAt R slo shi s →
      CstH L (tM L) [] s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cstH_offM hlab ?_ hp
  unfold spPool; rw [hk]; exact hb k h1 h2

end Cls

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.selfOwnH_iffC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.selfOwnH_iffC

/-- info: 'Spike.Lib.X64.HelloPh.cstH_poolW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.cstH_poolW

/-- info: 'Spike.Lib.X64.HelloPh.cstOkH_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.cstOkH_of

/-- info: 'Spike.Lib.X64.WakeWf.W0.liftHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.W0.liftHX

/-- info: 'Spike.Lib.X64.HelloPh.blkW_cstOkHB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.blkW_cstOkHB

/-- info: 'Spike.Lib.X64.HelloPh.nodeW_cstOkHK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.nodeW_cstOkHK

/-- info: 'Spike.Lib.X64.HelloPh.cls_poolWH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.cls_poolWH

/-- info: 'Spike.Lib.X64.HelloPh.cstH_lowS' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.cstH_lowS
