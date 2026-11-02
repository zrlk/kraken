/-
**`ownGH` to `ownGHXW` for the held-predicate state facts** (x86-64 only; the hello counterpart of
`X64WakeOwnLft2`, the lift layer for main after the start): `SFactsSt2` at `ownGH` moved to `ownGHXW` where both
appended maps may be appended (`CstOkH`), as `W0.liftHX` does for the start's `W0`, and the per-state lift
predicate `Lft2H` with its block and node producers, the shape of `X64HelloOwnLftCX`'s `blkLH`/`nodeLH`, so that
main's `ownGH` producers are mirrored node for node.

- `SFactsSt2.liftHX`: `SFactsSt2` at `ownGH` and `CstOkH` give it at `ownGHXW`.
- `Lft2H`: a state of `SFactsSt2` at `ownGH` is one at `ownGHXW`; `BlkW.lft2H`, `NodeW.lft2H` (from `CstOkH`).
- `QPH`, `PPH`: the pc classes of main's states on a pool stack holding `tcbM` only (from `.x1` on, in none of
  `InTH`, `InCH`, `InAbH`; `PPH` also off the take site).
- `blkL2H`, `nodeL2H`: `Lft2H` on a covered block / at a node of helloCells from the class of its states.

The write conditions of a flag-only instruction, a `leaq` and a `lock xaddq` off `tcbM` (`hw_fi`, `hw_lea`,
`hw_rmwM`) and `TcbWG.imp` are x86-64 wake's (`X64WakeOwnLft2`), generic in the layout and the code.

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there. Against x86-64 wake's `Lft2`/`QP`/`PP`/`blkL2`/`nodeL2`:
the code is helloCells, the classes are `CstH` with hello's ranges (`InTH`, `InCH`, `InAbH`,
`Spike/Lib/X64HelloOwnCstX.lean`), the take site is at `4200314` (wake `4200277`) and `hW` is about the worker's
word `tcbWH L` (`pinA + 112`; wake's `tcb2 L`).
-/
import Spike.Lib.X64HelloOwnLftCX
import Spike.Lib.X64SFactsACH
import Spike.Lib.X64WakeOwnLft2

namespace Spike.Lib.X64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB code_field)
open SccCode (helloCells)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs SFactsSt2)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM Keep)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64HelloOwnLift (tcbWH)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`SFactsSt2` at `ownGH` is `SFactsSt2` at `ownGHXW`** where both maps may be appended. -/
theorem _root_.Spike.Lib.X64ConsumerA.SFactsSt2.liftHX {μ : Marks} {s : State}
    (h : SFactsSt2 Λ μ (ownGH L a) s Dt) (hc : CstOkH μ L a s) : SFactsSt2 Λ μ (ownGHXW L a) s Dt :=
  (h.appendS hc.1).appendS (ownS := ownSWH L) hc.2

/-- **A state of `SFactsSt2` at `ownGH` is one at `ownGHXW`.** -/
def Lft2H (Λ : Scc.Sem.Layout) (L : RuntimeLayout) (a : BitVec 64) (Dt : State → Prop) : Spike.Lib.Frag isa :=
  fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s Dt →
    SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGHXW L a) s Dt

/-- `Lft2H` at a block from `CstOkH` there. -/
theorem BlkW.lft2H {exe : _root_.Executable} {endPc : Int64} {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hD hJ k hk m hA' hD' =>
    ⟨fun h' => h'.liftHX (h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- `Lft2H` at a node from `CstOkH` there. -/
theorem NodeW.lft2H {exe : _root_.Executable} {endPc : Int64} {n : ND}
    (h : NodeW (fun s _ => CstOkH (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨fun h' => h'.liftHX (h s c hA).1, fun _ h => h⟩

/-! ## The pool classes -/

/-- **Main's states on a pool stack holding `tcbM` only**: from `.x1` on, in none of `InTH`, `InCH`, `InAbH`
(`cls_poolH`'s class). -/
def QPH (q : Nat) : Prop := 4198500 ≤ q ∧ ¬ InTH q ∧ ¬ InCH q ∧ ¬ InAbH q

instance (q : Nat) : Decidable (QPH q) := by unfold QPH InTH InCH InAbH; infer_instance

/-- `QPH` off the take site. -/
def PPH (q : Nat) : Prop := QPH q ∧ q ≠ 4200314

instance (q : Nat) : Decidable (PPH q) := by unfold PPH; infer_instance

/-! ## Blocks and nodes -/

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hs ha hW

/-- **`Lft2H` on a covered block of helloCells** (`blkLH` at `Lft2H`). -/
theorem blkL2H {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P Q : Nat → Prop}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200314)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (hclsQ : ∀ s : State, Q (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (h1 : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hso : ∀ j ≤ blk.length, slo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → Q (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat) :
    BlkW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lft2H (blkW_cstOkHB hs ha hW (fun s hs' hn => code_field L.lays rfl (hp ▸ hb) he s hs' hn) hok hR hlo
    hhi ?_ hcls h1 hso ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteVH hlab]; exact hP _ (h1 j hj)
  · intro σ c hJ s m hA _ _ hs'
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hclsQ s (by unfold pcOf; rw [hs']; exact hfin σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA

omit hp hlab hsite in
/-- **`Lft2H` at a node** whose successors keep `%rsp` and `%rbp` `sz` bytes on (`nodeLH` at `Lft2H`). -/
theorem nodeL2H {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (Lft2H Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n :=
  NodeW.lft2H (nodeW_cstOkHK hs ha hW hcls hk hpc hso hw)

end L

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64ConsumerA.SFactsSt2.liftHX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SFactsSt2.liftHX

/-- info: 'Spike.Lib.X64.HelloPh.blkL2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.blkL2H

/-- info: 'Spike.Lib.X64.HelloPh.nodeL2H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.nodeL2H

/-- `QPH` and `PPH` are not vacuous: `wc_main`'s entry (`4203623`) is in both, the take site in `QPH` only. -/
example : Spike.Lib.X64.HelloPh.PPH 4203623 ∧ Spike.Lib.X64.HelloPh.QPH 4200314 ∧
    ¬ Spike.Lib.X64.HelloPh.PPH 4200314 := by
  decide
