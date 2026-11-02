/-
**`LftH` at a block or a node of helloCells** (x86-64 only; the hello counterpart of `X64WakeOwnLftC`): the
start's level lifted to `ownGHXW` (`LftH`, `WSHX`, `Spike/Lib/X64HelloOwnImpX.lean`) at a block or a node of
hello's code, from the class of its states (a pc predicate `P` and a band of static `%rsp` offsets), so that the
start's assemblies at `ownGH` are mirrored node for node.

- `siteVH`: the take site's pc at the canonical base (`4200314`).
- `blkLH`: a covered block of helloCells (`blockAtB`), its pcs in `P` (off the take site, `hP`), its prefixes'
  offsets in the band, `Q` where its run ends.
- `nodeLH`: a node whose successors keep `%rsp`/`%rbp` (`Keep`) `sz` bytes on, its write condition `hw`.
- `nodeL0H`: `nodeLH` at the words empty (no write condition).

## Differences from the AArch64 version

AArch64 has no counterpart: main owns no TCB word there (its thread pointer is a register). Against x86-64 wake's
`blkL`/`nodeL`/`nodeL0`: the code is helloCells, the take site is at `4200314` (wake `4200277`), the classes are
`CstH` (`Spike/Lib/X64HelloOwnCstX.lean`) and the separation premise `hW` is about the worker's word `tcbWH L`
(`pinA + 112`; wake's `tcb2 L`).
-/
import Spike.Lib.X64HelloOwnImpX

namespace Spike.Lib.X64.HelloPh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB code_field)
open SccCode (helloCells)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh (tcbM Keep hw_nil)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib.X64HelloOwnLift (tcbWH)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

variable {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The take site's pc** at the canonical base. -/
theorem siteVH (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab "scc_rt_take_site").toBitVec.toNat = 4200314 := by
  rw [hlab _ 4200314 (by rw [← codeT_eq]; decide +kernel)]; decide

section L

variable (hp : L.prog = helloCells)
  (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hs : Spike.Lib.X64.PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcbWH L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hs ha hW

/-- **`LftH` on a covered block of helloCells**: the class `hcls` at its pcs (`h1`, in `P`, off the take site by
`hP`) with its prefixes' static `%rsp` offsets in `[slo, shi]` (`hso`), `Q` (class `hclsQ`) where its run ends
(`hfin`). -/
theorem blkLH {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P Q : Nat → Prop}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200314)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (hclsQ : ∀ s : State, Q (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (h1 : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hso : ∀ j ≤ blk.length, slo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → Q (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat) :
    BlkW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lftH (blkW_cstOkHB hs ha hW (fun s hs' hn => code_field L.lays rfl (hp ▸ hb) he s hs' hn) hok hR hlo
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
/-- **`LftH` at a node** whose successors keep `%rsp` and `%rbp` `sz` bytes on (`hk`): the class at its pc and
the next (`hpc`), its static `%rsp` offset in `[slo, shi]` (`hso`), its write condition (`hw`). -/
theorem nodeLH {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L c1 c2 s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n :=
  NodeW.lftH (nodeW_cstOkHK hs ha hW hcls hk hpc hso hw)

omit hp hlab hsite in
/-- `nodeLH` at the words empty. -/
theorem nodeL0H {n : ND} {sz : Nat} {slo shi : Int} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → CstH L [] [] s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi) :
    NodeW (LftH L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n :=
  nodeLH hs ha hW hcls hk hpc hso hw_nil

end L

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.blkLH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.blkLH

/-- info: 'Spike.Lib.X64.HelloPh.nodeL0H' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.nodeL0H
