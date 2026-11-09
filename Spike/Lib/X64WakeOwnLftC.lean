/-
**`Lft` at a block or a node of wakeCells** (x86-64; X64-OwnW lift layer): the start's level lifted
to `ownGXW` (`Lft`, `WSX`) at a
block or a node of wake's code, from the class of its states (a pc
predicate `P` and a band of static `%rsp` offsets), the shape of
`StartTi.blkI_WS` / `nodeI_WS`'s premises so the start's assemblies are
mirrored node for node.

- `siteV`: the take site's pc at the canonical base (`4200277`).
- `blkL`: a covered block of wakeCells (`blockAtB`), its pcs in `P` (off
  the take site, `hP`), its prefixes' offsets in the band, `P` where its run
  ends.
- `nodeL`: a node whose successors keep `%rsp`/`%rbp` (`Keep`) `sz` bytes on,
  its write condition `hw`.
- `nodeL0`: `nodeL` at the words empty (no write condition).

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnImp

namespace Spike.Lib.X64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB code_field)
open SccCode (wakeCells)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Spike.Lib (Arena FragS)
open Spike.Lib.X64Consumer (Lbl Lsize)

variable {L : RuntimeLayout} {a : BitVec 64} {ar : Arena} {p : Prog} {Dt Cl : State → Prop}
  {Ctx : FragS isa} {lbl : Lbl} {lsize : Lsize} {frM : TermRun.Frame} {X0 : State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **The take site's pc** at the canonical base. -/
theorem siteV (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) :
    (L.lab "scc_rt_take_site").toBitVec.toNat = 4200277 := by
  rw [hlab _ 4200277 (by rw [← codeT_eq]; decide +kernel)]; decide

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hs ha hW

/-- **`Lft` on a covered block of wakeCells**: the class `hcls` at its pcs
(`h1`, in `P`, off the take site by `hP`) with its prefixes' static `%rsp`
offsets in `[slo, shi]` (`hso`), `Q` (class `hclsQ`) where its run ends
(`hfin`). -/
theorem blkL {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P Q : Nat → Prop}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200277)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hclsQ : ∀ s : State, Q (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (h1 : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hso : ∀ j ≤ blk.length, slo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → Q (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat) :
    BlkW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lft (blkW_cstOkB hs ha hW (fun s hs' hn => code_field L.lays rfl (hp ▸ hb) he s hs' hn) hok hR hlo
    hhi ?_ hcls h1 hso ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteV hlab]; exact hP _ (h1 j hj)
  · intro σ c hJ s m hA _ _ hs'
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hclsQ s (by unfold pcOf; rw [hs']; exact hfin σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA

/-- **`blkL` on a block split by a return label** (`m`, after its first
`jA` rows; `blockAcrossB`). -/
theorem blkLA {n : ND} {blk : List (Directive × Nat)} {l m : Label} {k jA : Nat} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P Q : Nat → Prop}
    (hb : Scc.Cert.Rt.X64.blockAcrossB wakeCells l k (blk.take jA) m (blk.drop jA) = true)
    (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200277)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hclsQ : ∀ s : State, Q (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (h1 : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hso : ∀ j ≤ blk.length, slo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → Q (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat) :
    BlkW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lft (blkW_cstOkB hs ha hW (fun s hs' hn =>
    Spike.Lib.X64.code_field_blockAcrossB L.lays rfl (hp ▸ hb) (List.take_append_drop jA blk) he s hs' hn) hok hR
    hlo hhi ?_ hcls h1 hso ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteV hlab]; exact hP _ (h1 j hj)
  · intro σ c hJ s m hA _ _ hs'
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hclsQ s (by unfold pcOf; rw [hs']; exact hfin σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA

omit hp hsite in
/-- **`Lft` at a node** whose successors keep `%rsp` and `%rbp` `sz` bytes
on (`hk`): the class at its pc and the next (`hpc`), its static `%rsp`
offset in `[slo, shi]` (`hso`), its write condition (`hw`). -/
theorem nodeL {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n :=
  NodeW.lft (nodeW_cstOkK hs ha hW hcls hk hpc hso hw)

omit hp hsite in
/-- `nodeL` at the words empty. -/
theorem nodeL0 {n : ND} {sz : Nat} {slo shi : Int} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L [] [] s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi) :
    NodeW (Lft L a ar p Dt Cl Ctx lbl lsize frM X0) (fun _ _ => False) L.exe L.endPc R F n :=
  nodeL hlab hs ha hW hcls hk hpc hso hw_nil

end L

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.blkL' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkL

/-- info: 'Spike.Lib.X64.WakePh.nodeL0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeL0
