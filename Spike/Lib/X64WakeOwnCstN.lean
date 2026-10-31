/-
**`CstOk` at a block or a node from the pcs and the static `%rsp`
offsets** (x86-64; X64-OwnW lift): the shape of the ownG
converters' premises (`StartTcb.blkT_own` / `nodeT_own`: a block's pcs and
its prefixes' static `%rsp` offsets, `Cst` where its run ends; a node's
successors keeping `%rsp` and `%rbp` `sz` bytes on), with the class of a
state given as a pc predicate `P` and a band of `%rsp` offsets (`hcls`).

- `blkW_cstOkB`: a covered block.
- `nodeW_cstOkK`: a node whose successors keep `%rsp`/`%rbp` (`Keep`).
- `NoH`, `BandOffP`, `BandOnP`, `cls_off`, `cls_pool`: the classes
  "no range, off the pool" (neither word) and "no `InT`/`InC`, on the pool"
  (main's word) as `hcls`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnCst
import Spike.Lib.X64WakeTcb2WLib
import Spike.Lib.X64WakeOwnGNode

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open SccCode (wakeCells)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)

variable {L : RuntimeLayout} {a : BitVec 64} {μ : Marks}
  {exe : _root_.Executable} {endPc : Int64} {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`CstOk` on a covered block**: the class `hcls` at its pcs (`h1`, in
`P`) with its prefixes' static `%rsp` offsets in `[slo, shi]` (`hso`), and
`Cst` where its run ends (`hfin`). -/
theorem blkW_cstOkB {n : ND} {blk : List (Directive × Nat)} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc blk)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hns : ∀ a, μ.site .take = some a → ∀ k < blk.length, (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat ≠ a)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (h1 : ∀ k < blk.length, P (n.pc + Int64.ofNat (cellOff blk k)).toBitVec.toNat)
    (hso : ∀ k ≤ blk.length, slo ≤ (soRun (blk.take k) n.o).sp ∧ (soRun (blk.take k) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, (arun (_root_.Executable.labels exe).label blk ⟨n.pc, n.o, σ⟩).pc) →
      Cst L c1 c2 s) :
    BlkW (fun s _ => CstOk μ L a s) (fun _ _ => False) exe endPc R F n blk := by
  have hQ : ∀ σ c, n.J σ c → ∀ k < blk.length, ∀ (s : State) m,
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so m
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      s.exe = exe → s.endPc = endPc → s.st = (m, n.pc + Int64.ofNat (cellOff blk k)) → Cst L c1 c2 s := by
    intro σ c _ k hk s m hA _ _ hs'
    have ho := hso k (Nat.le_of_lt hk)
    rw [← arun_so (_root_.Executable.labels exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hcls s (by unfold pcOf; rw [hs']; exact h1 k hk) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA
  refine blkW_cstOk hs ha hW hcode hok hR hlo hhi hns hQ ?_
  intro σ c hJ k hk s m hA he hn hs'
  rcases Nat.lt_or_ge (k + 1) blk.length with hk1 | hk1
  · rw [Spike.Lib.X64.arun_pc _ hok hk1] at hs'
    exact hQ σ c hJ (k + 1) hk1 s m hA he hn hs'
  · rw [List.take_of_length_le (by omega)] at hA hs'
    exact hfin σ c hJ s m hA he hn hs'

/-- **`CstOk` at a node** whose successors keep `%rsp` and `%rbp` `sz`
bytes on (`hk`): the class at its pc and the next (`hpc`), its static
`%rsp` offset in `[slo, shi]` (`hso`), its write condition (`hw`). -/
theorem nodeW_cstOkK {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hk : ∀ s c, At exe endPc R F n s c → ∀ s', StSucc μ s s' → Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (fun s _ => CstOk μ L a s) (fun _ _ => False) exe endPc R F n := by
  refine nodeW_cstOk hs ha hW (fun s c hAt => ?_) hw
  obtain ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ := hAt
  have hsp : s.st.1.regs.rsp.toBitVec = R.addr n.o.sp := rsp_of_abs hA
  refine ⟨hcls s (by unfold pcOf; rw [hp]; exact hpc.1) ⟨_, hso.1, hso.2, hsp⟩, fun s' h => ?_⟩
  obtain ⟨⟨h1, -, -⟩, h3⟩ := hk s c ⟨he, hn, hd, hp, σ, hA, hF, hJ⟩ s' h
  exact hcls s' (by unfold pcOf; rw [h3]; exact hpc.2) ⟨_, hso.1, hso.2, by rw [h1]; exact hsp⟩

/-! ## Two classes -/

/-- **No range**: none of `InA`, `InT`, `InC`, `InAb`. -/
def NoH (p : Nat) : Prop := ¬ InA p ∧ ¬ InT p ∧ ¬ InC p ∧ ¬ InAb p

instance (p : Nat) : Decidable (NoH p) := by unfold NoH; infer_instance

/-- **A band of `R` off the pool.** -/
def BandOffP (L : RuntimeLayout) (R : Spike.Lib.Region) (slo shi : Int) : Prop :=
  ∀ k, slo ≤ k → k ≤ shi → ¬ (L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size)

/-- **A band of `R` on the pool.** -/
def BandOnP (L : RuntimeLayout) (R : Spike.Lib.Region) (slo shi : Int) : Prop :=
  ∀ k, slo ≤ k → k ≤ shi → L.Λ.stackPool.lo < (R.addr k).toNat ∧
    (R.addr k).toNat ≤ L.Λ.stackPool.lo + L.Λ.stackPool.size

section Cls

variable (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
include hlab

/-- **Neither word** at a state in no range with `%rsp` in a band off the
pool. -/
theorem cls_off {slo shi : Int} (hb : BandOffP L R slo shi) :
    ∀ s : State, NoH (pcOf s) → SpAt R slo shi s → Cst L [] [] s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cst_off hlab ?_ hp
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- **Main's word only** at a state from `.x1` on, in neither `InT` nor
`InC` (nor `InAb`), with `%rsp` in a band on the pool. -/
theorem cls_pool {slo shi : Int} (hb : BandOnP L R slo shi) :
    ∀ s : State, (4198500 ≤ pcOf s ∧ ¬ InT (pcOf s) ∧ ¬ InC (pcOf s) ∧ ¬ InAb (pcOf s)) → SpAt R slo shi s →
      Cst L (tM L) [] s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cst_pool hlab ?_ hp.1 hp.2
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- **Both words** at a state in `InT` or `InC` (not `InAb`) with `%rsp`
in a band on the pool. -/
theorem cls_poolW {slo shi : Int} (hb : BandOnP L R slo shi) :
    ∀ s : State, ((InT (pcOf s) ∨ InC (pcOf s)) ∧ ¬ InAb (pcOf s)) → SpAt R slo shi s →
      Cst L (tM L) (tW L) s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cst_poolW hlab ?_ hp
  unfold spPool; rw [hk]; exact hb k h1 h2

/-- **Main's word only** at a state in `InA` or `InT` (not `InC`, `InAb`)
with `%rsp` in a band off the pool. -/
theorem cls_offM {slo shi : Int} (hb : BandOffP L R slo shi) :
    ∀ s : State, ((InA (pcOf s) ∨ InT (pcOf s)) ∧ ¬ InC (pcOf s) ∧ ¬ InAb (pcOf s)) → SpAt R slo shi s →
      Cst L (tM L) [] s := by
  intro s hp ⟨k, h1, h2, hk⟩
  refine cst_offM hlab ?_ hp
  unfold spPool; rw [hk]; exact hb k h1 h2

end Cls

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.blkW_cstOkB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkW_cstOkB

/-- info: 'Spike.Lib.X64.WakePh.nodeW_cstOkK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeW_cstOkK

/-- info: 'Spike.Lib.X64.WakePh.cls_off' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.cls_off
