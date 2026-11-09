/-
**`ownG` to `ownGXW` for the held-predicate state facts** (x86-64; X64-OwnW
lift layer for main after the start): `SFactsSt2` at `ownG`
moved to `ownGXW` where both appended maps may be appended (`CstOk`), as
`W0.liftX` does for the start's `W0`, and the per-state lift predicate
`Lft2` with its block and node producers, the shape of `X64WakeOwnLftC`'s
`blkL` / `nodeL` so main's `ownG` producers are mirrored node for node.

- `SFactsSt2.liftX`: `SFactsSt2` at `ownG` and `CstOk` give it at `ownGXW`.
- `Lft2`: a state of `SFactsSt2` at `ownG` is one at `ownGXW`;
  `BlkW.lft2`, `NodeW.lft2` (from `CstOk`).
- `blkL2`, `nodeL2`: `Lft2` on a covered block / at a node of wakeCells
  from the class of its states.
- `TcbWG.imp`: `scc_rt_alloc_tcb`'s generic node obligations from two.
- `PP`, `QP`: the pc classes of main's states on a pool stack holding
  `tcbM` only (from `.x1` on, in none of `InT`, `InC`, `InAb`; `PP` also
  off the take site).
- `hw_fi`, `hw_lea`, `hw_rmwM`: the write conditions of a flag-only
  instruction, a `leaq`, and a `lock xaddq` off `tcbM`.

**Deviations.** None: new lemmas.
-/
import Spike.Lib.X64WakeOwnStartE
import Spike.Lib.X64SFactsACH
import Spike.Lib.X64WakeOwnS2

namespace Spike.Lib.X64.WakePh

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB code_field)
open SccCode (wakeCells)
open Spike.Lib.X64ConsumerA (StSucc SpAt rsp_of_abs SFactsSt2)
open Spike.Lib.X64 (BlkW NodeW ND CodeAt okBlk arun cellOff Abs At FI SI)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64.WakePh.Tcb2W (soRun arun_so)
open Kraken.Promising.Lower.X64 (CellAt)

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {Dt : State → Prop}
  {R : Spike.Lib.Region} {F : MachineData → Prop}

/-- **`SFactsSt2` at `ownG` is `SFactsSt2` at `ownGXW`** where both maps may
be appended. -/
theorem _root_.Spike.Lib.X64ConsumerA.SFactsSt2.liftX {μ : Marks} {s : State}
    (h : SFactsSt2 Λ μ (ownG L a) s Dt) (hc : CstOk μ L a s) : SFactsSt2 Λ μ (ownGXW L a) s Dt :=
  (h.appendS hc.1).appendS (ownS := ownSW L) hc.2

/-- **A state of `SFactsSt2` at `ownG` is one at `ownGXW`.** -/
def Lft2 (Λ : Scc.Sem.Layout) (L : RuntimeLayout) (a : BitVec 64) (Dt : State → Prop) : Spike.Lib.Frag isa :=
  fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s Dt →
    SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGXW L a) s Dt

/-- `Lft2` at a block from `CstOk` there. -/
theorem BlkW.lft2 {exe : _root_.Executable} {endPc : Int64} {n : ND} {blk : List (Directive × Nat)}
    (h : BlkW (fun s _ => CstOk (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n blk) :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) exe endPc R F n blk :=
  fun s σ c he hn hdc hpc hA hD hJ k hk m hA' hD' =>
    ⟨fun h' => h'.liftX (h s σ c he hn hdc hpc hA hD hJ k hk m hA' hD').1, fun _ h => h⟩

/-- `Lft2` at a node from `CstOk` there. -/
theorem NodeW.lft2 {exe : _root_.Executable} {endPc : Int64} {n : ND}
    (h : NodeW (fun s _ => CstOk (Spike.Lib.X64.PhRec.μ L) L a s) (fun _ _ => False) exe endPc R F n) :
    NodeW (Lft2 Λ L a Dt) (fun _ _ => False) exe endPc R F n :=
  fun s c hA => ⟨fun h' => h'.liftX (h s c hA).1, fun _ h => h⟩

/-- `scc_rt_alloc_tcb`'s generic node obligations from two. -/
theorem TcbWG.imp {W W1 W2 : Spike.Lib.Frag isa} {K : State → State → Prop} {exe : _root_.Executable}
    {endPc : Int64} {q : Spike.Lib.X64.Rt.TcbGG} {i : Spike.Lib.X64.Flow.Ret0.TN}
    (h1 : Spike.Lib.X64.Rt.TcbWG W1 K exe endPc R F q i)
    (h2 : Spike.Lib.X64.Rt.TcbWG W2 (fun _ _ => False) exe endPc R F q i)
    (hw : ∀ s c, W1 s c → W2 s c → W s c) : Spike.Lib.X64.Rt.TcbWG W K exe endPc R F q i := by
  cases i <;> dsimp only [Spike.Lib.X64.Rt.TcbWG] at h1 h2 ⊢
  all_goals first
    | exact Spike.Lib.X64.AllocG.BlkW.imp h1 h2 hw
    | exact Spike.Lib.X64.AllocG.NodeW.imp h1 h2 hw

/-! ## The pool classes -/

/-- **Main's states on a pool stack holding `tcbM` only**: from `.x1` on, in
none of `InT`, `InC`, `InAb`. -/
def QP (q : Nat) : Prop := 4198500 ≤ q ∧ ¬ InT q ∧ ¬ InC q ∧ ¬ InAb q

instance (q : Nat) : Decidable (QP q) := by unfold QP InT InC InAb; infer_instance

/-- `QP` off the take site. -/
def PP (q : Nat) : Prop := QP q ∧ q ≠ 4200277

instance (q : Nat) : Decidable (PP q) := by unfold PP; infer_instance

/-! ## Write conditions -/

/-- **A flag-only instruction writes nothing.** -/
theorem hw_fi {exe : _root_.Executable} {endPc : Int64} {n : ND} {c1 c2 : List (Loc × Val)} {fi : FI} {z : Nat}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s fi.toDir z) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  obtain ⟨t, ht, hsil⟩ := Spike.Lib.X64.exec_fi (h s c hAt)
  rw [ht] at he; cases he
  exact OwnSt.writeTree_silent hsil

/-- **A `leaq` writes nothing.** -/
theorem hw_lea {exe : _root_.Executable} {endPc : Int64} {n : ND} {c1 c2 : List (Loc × Val)} {si : SI} {z : Nat}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s si.toDir z) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree := by
  intro s c hAt _ tree he
  rw [Spike.Lib.X64.exec_si (h s c hAt)] at he; cases he
  trivial

/-- **A `lock xaddq %rax, (%rcx)` off `tcbM` writes no word of `tM`.** -/
theorem hw_rmwM {exe : _root_.Executable} {endPc : Int64} {n : ND} {z : Nat} {A : BitVec 64}
    (h : ∀ s c, At exe endPc R F n s c → CellAt s (Spike.Lib.X64.xaddDir .rcx 0 .rax) z ∧
      Kraken.Promising.Lower.X64.eaddr s z (Spike.Lib.X64.mB .rcx 0) = A ∧
      Mem.loadInt s.st.1.dmem A 8 = none ∧ s.decls = {})
    (hA : A ≠ tcbM L) :
    ∀ s c, At exe endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ tM L) ∧ ∀ w, (l, w) ∉ ([] : List (Loc × Val))) tree := by
  intro s c hAt _ tree he
  obtain ⟨hc, ha, hd, hdc⟩ := h s c hAt
  rw [Kraken.Promising.Lower.X64.exec_xaddG_agrees (w := .W64) hc ha hd
    (Spike.Lib.X64.agrees_of_decls hdc _ _)] at he
  cases he
  refine ⟨fun _ _ _ => ⟨fun w hw => ?_, fun w hw => by simp at hw⟩, fun _ => trivial⟩
  simp only [tM, List.mem_singleton, Prod.mk.injEq] at hw
  obtain ⟨hl, -⟩ := hw
  injection hl with h1
  exact hA h1

/-! ## Blocks and nodes -/

section L

variable (hp : L.prog = wakeCells)
  (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take = some (L.lab "scc_rt_take_site").toBitVec.toNat)
  (hs : PhRec.TcbSep L) (ha : tcbM L ≠ a) (hW : tcb2 L ∉ [L.pnA, L.lockA, L.freeNA, L.nextA, a])
include hp hlab hsite hs ha hW

/-- **`Lft2` on a covered block of wakeCells** (`blkL` at `Lft2`). -/
theorem blkL2 {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi slo shi : Int}
    {c1 c2 : List (Loc × Val)} {P Q : Nat → Prop}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hP : ∀ q, P q → q ≠ 4200277)
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hclsQ : ∀ s : State, Q (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (h1 : ∀ j < blk.length, P (n.pc + Int64.ofNat (cellOff blk j)).toBitVec.toNat)
    (hso : ∀ j ≤ blk.length, slo ≤ (soRun (blk.take j) n.o).sp ∧ (soRun (blk.take j) n.o).sp ≤ shi)
    (hfin : ∀ σ c, n.J σ c → Q (arun (_root_.Executable.labels L.exe).label blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat) :
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lft2 (blkW_cstOkB hs ha hW (fun s hs' hn => code_field L.lays rfl (hp ▸ hb) he s hs' hn) hok hR hlo
    hhi ?_ hcls h1 hso ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteV hlab]; exact hP _ (h1 j hj)
  · intro σ c hJ s m hA _ _ hs'
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hclsQ s (by unfold pcOf; rw [hs']; exact hfin σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA

/-- **`Lft2` along a covered block split by a return label** (`m`, after its
first `jA` rows; `blockAcrossB`): as `blkL2`. -/
theorem blkL2A {n : ND} {blk : List (Directive × Nat)} {l m : Label} {k jA : Nat} {blo bhi slo shi : Int}
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
    BlkW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n blk := by
  refine BlkW.lft2 (blkW_cstOkB hs ha hW
    (Spike.Lib.X64.code_field_blockAcrossB L.lays rfl (hp ▸ hb) (List.take_append_drop jA blk) he) hok hR hlo
    hhi ?_ hcls h1 hso ?_)
  · intro a' ha' j hj
    rw [hsite] at ha'; cases ha'
    rw [siteV hlab]; exact hP _ (h1 j hj)
  · intro σ c hJ s m hA _ _ hs'
    have ho := hso blk.length (Nat.le_refl _)
    rw [List.take_length, ← arun_so (_root_.Executable.labels L.exe).label _ ⟨n.pc, n.o, σ⟩] at ho
    refine hclsQ s (by unfold pcOf; rw [hs']; exact hfin σ c hJ) ⟨_, ho.1, ho.2, ?_⟩
    rw [hs']; exact rsp_of_abs hA

omit hp hsite in
/-- **`Lft2` at a node** whose successors keep `%rsp` and `%rbp` `sz` bytes
on (`nodeL` at `Lft2`). -/
theorem nodeL2 {n : ND} {sz : Nat} {slo shi : Int} {c1 c2 : List (Loc × Val)} {P : Nat → Prop}
    (hcls : ∀ s : State, P (pcOf s) → SpAt R slo shi s → Cst L c1 c2 s)
    (hk : ∀ s c, At L.exe L.endPc R F n s c → ∀ s', StSucc (Spike.Lib.X64.PhRec.μ L) s s' →
      Keep s s' ∧ s'.st.2 = n.pc + Int64.ofNat sz)
    (hpc : P n.pc.toBitVec.toNat ∧ P (n.pc + Int64.ofNat sz).toBitVec.toNat) (hso : slo ≤ n.o.sp ∧ n.o.sp ≤ shi)
    (hw : ∀ s c, At L.exe L.endPc R F n s c → abi.atSys s = false → ∀ tree, isa.exec s = some tree →
      WriteTree (fun l _ => (∀ w, (l, w) ∉ c1) ∧ ∀ w, (l, w) ∉ c2) tree) :
    NodeW (Lft2 Λ L a Dt) (fun _ _ => False) L.exe L.endPc R F n :=
  NodeW.lft2 (nodeW_cstOkK hs ha hW hcls hk hpc hso hw)

end L

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64ConsumerA.SFactsSt2.liftX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.SFactsSt2.liftX

/-- info: 'Spike.Lib.X64.WakePh.blkL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkL2

/-- info: 'Spike.Lib.X64.WakePh.blkL2A' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkL2A

/-- info: 'Spike.Lib.X64.WakePh.nodeL2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeL2

/-- info: 'Spike.Lib.X64.WakePh.hw_rmwM' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hw_rmwM
