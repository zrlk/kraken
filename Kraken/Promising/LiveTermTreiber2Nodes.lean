/-
**Stage 4: termination of `treiber2_nodes.kl` on the
semantic machine, under every schedule** (`TermBoundSem`, no fairness).

`treiber2NImage` (`EnvG/A64WholeTreiber2Nodes.lean`, the `.kl`'s `code`
block) is `treiber2DWorker` without the data store `STR W9,[X1]` and the data
load `LDR W11,[X2]`, so its cells sit at shifted positions:

```
 0 worker:                  10   CBZ X2,done
 1 push:                    11   LDR X4,[X2,#8]
 2   LDAR X2,[X0]           12   MOV X3,X2
 3   STR X2,[X1,#8]         13   CASAL X3,X4,[X0]
 4   MOV X3,X2              14   CMP X3,X2
 5   CASAL X3,X1,[X0]       15   B.NE pop
 6   CMP X3,X2              16   MOV X10,X2
 7   B.NE push              17   B done
 8 pop:                     18 done:
 9   LDAR X2,[X0]
```

The position map `sigN` sends `treiber2DWorker`'s positions `3..17` to
`2..16`, `19` to `17` and the end `21` to `19`. This file proves the cells
(`cellsN : Cells treiber2NImage sigN false`) and instantiates the
position-parametric termination theorem `TermTreiber2P.term_sem_genP`
(`LiveTermTreiber2P.lean`; the rank is `treiber2`'s, unchanged).
-/
import Kraken.Promising.LiveTermTreiber2P
import Kraken.Promising.SLR.EnvG.A64WholeTreiber2Nodes

namespace Kraken.Promising.Live.TermTreiber2Nodes

open Kraken Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Live.Term Kraken.Promising.Live.TermTreiber2P
open Kraken.Promising.SLR.EnvG.Treiber2 (treiber2NImage treiber2NImage_wf StartWN labN labN_worker labN_done)
open Kraken.Promising.SLR.A64Trees (At goto)

/-- `treiber2DWorker`'s positions in `treiber2NImage`. -/
def sigN (i : Nat) : Nat := if i = 21 then 19 else if i = 19 then 17 else i - 1

/-- The pc positions of `treiber2NImage`. -/
def nPcs : List Nat := [2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 13, 14, 15, 16, 17, 19]

/-- The address-distinct representative of a position: the label before it. -/
def canonN (i : Nat) : Nat := if i = 9 then 8 else if i = 19 then 18 else i

theorem sigN_mem : ∀ k ∈ pcsD false, sigN k ∈ nPcs := by decide

theorem sigN_inj : ∀ a ∈ pcsD false, ∀ b ∈ pcsD false, sigN a = sigN b → a = b := by decide

section Cells

variable [layout : _root_.Layout] [hv : Executable.ValidLayout (layout treiber2NImage)]

set_option hygiene false in
local notation "pcN" => (layout treiber2NImage).addrOf

theorem addrOf_1 : pcN 1 = pcN 2 := (SLR.A64Trees.addrOf_label (i := 1) (l := "push") rfl).symm
theorem addrOf_8 : pcN 8 = pcN 9 := (SLR.A64Trees.addrOf_label (i := 8) (l := "pop") rfl).symm
theorem addrOf_18 : pcN 18 = pcN 19 := (SLR.A64Trees.addrOf_label (i := 18) (l := "done") rfl).symm

set_option maxRecDepth 8192 in
theorem label_push : (_root_.Executable.labels (layout treiber2NImage)).label "push" = pcN 2 := by
  rw [Program.label_addrOf_drop (i := 1) treiber2NImage_wf.nodup (by decide) (by decide)]
  exact addrOf_1

set_option maxRecDepth 8192 in
theorem label_pop : (_root_.Executable.labels (layout treiber2NImage)).label "pop" = pcN 9 := by
  rw [Program.label_addrOf_drop (i := 8) treiber2NImage_wf.nodup (by decide) (by decide)]
  exact addrOf_8

theorem label_done : (_root_.Executable.labels (layout treiber2NImage)).label "done" = pcN 19 :=
  labN_done.trans rfl

theorem addrOf_canonN (i : Nat) : pcN (canonN i) = pcN i := by
  unfold canonN
  split
  · subst_vars; exact addrOf_8
  split
  · subst_vars; exact addrOf_18
  rfl

/-- **The pc positions have distinct addresses.** -/
theorem addrOf_injN {i j : Nat} (hi : i ∈ nPcs) (hj : j ∈ nPcs) (h : pcN i = pcN j) : i = j :=
  SLR.A64Trees.addrOf_inj_gen _ TermTreiber2.isInstr (fun _ => rfl) nPcs canonN (fun i _ => addrOf_canonN i)
    (by decide) hi hj h

/-- Normalise the positions (`sigN`), then read the cell at position `i`. -/
local macro "ncell" h:ident i:num "[" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  a64cell $h $i treiber2NImage [treiber2NImage] [label_push, label_pop, label_done] [goto, $ts,*])

local macro "npos" h:ident : tactic => `(tactic|
  simp (config := { decide := true }) only [pcS, sigN, Bool.false_eq_true, ↓reduceIte, Nat.reduceSub,
    Nat.reduceAdd] at $h:ident ⊢)

/-- **The cells of `treiber2NImage`** at `sigN`, without data cells. -/
theorem cellsN : Cells treiber2NImage sigN false where
  inj hi hj h := sigN_inj _ hi _ hj (addrOf_injN (sigN_mem _ hi) (sigN_mem _ hj) h)
  str_d h := absurd h (by decide)
  ldar i hi st h t hx0 hdm := by
    rcases hi with rfl | rfl
    · npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 2 [hx0, hdm]
    · npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 9 [hx0, hdm]
  str_n st h n hx1 hdm := by
    npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 3 [hx1, TermTreiber2Trees.ofInt_add8, hdm]
  mov i hi st h := by
    rcases hi with rfl | rfl
    · npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 4 []
    · npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 12 []
  casal6 st h t hx0 hdm := by npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 5 [hx0, hdm]
  cmp i hi st h := by
    rcases hi with rfl | rfl
    · refine ⟨?s, ?e, ?z⟩
      case e => npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 6 []; rfl
      case z =>
        simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
        exact iff_of_eq (congrArg _ (BitVec.zero_add _))
    · refine ⟨?s, ?e, ?z⟩
      case e => npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 14 []
      case z =>
        simp only [beq_iff_eq, BitVec.sub_eq_iff_eq_add]
        exact iff_of_eq (congrArg _ (BitVec.zero_add _))
  bne8 st h := by
    npos h; rw [← addrOf_8, SLR.A64Trees.next_pc h (by decide)]
    by_cases hz : st.st.1.status.z = true <;> ncell h 7 [hz]
  cbz11 st h := by
    npos h; rw [SLR.A64Trees.next_pc h (by decide)]
    by_cases hz : st.st.1.regs.X2.toBitVec = 0#64 <;> ncell h 10 [hz]
  ldr12 st h a hx2 hdm := by
    npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 11 [hx2, TermTreiber2Trees.ofInt_add8, hdm]
  casal14 st h t hx0 hdm := by npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 13 [hx0, hdm]
  bne16 st h := by
    npos h; rw [SLR.A64Trees.next_pc h (by decide)]
    by_cases hz : st.st.1.status.z = true <;> ncell h 15 [hz]
  mov17 st h := by npos h; rw [SLR.A64Trees.next_pc h (by decide)]; ncell h 16 []
  ldr18 h := absurd h (by decide)
  b19 st h := by npos h; ncell h 17 []

/-- A `StartWN` worker whose node's link word is not `top` is at its start
(`push`) with `Static`. -/
theorem start_of_startWN {t n : BitVec 64} {s : isa.State} (h : StartWN t n s) (hn : t ≠ n + 8) :
    Static treiber2NImage sigN false t s ∧ s.st.2 = pcS treiber2NImage sigN (startPos false) :=
  ⟨⟨h.exe, h.decls, h.endPc.trans labN_done, h.x0, by rw [h.x1]; exact fun e => hn e.symm, h.d8,
    fun e => absurd e (by decide)⟩, h.pc.trans (labN_worker.trans label_push)⟩

end Cells

/-! ## Termination -/

/-- **The `treiber2_nodes.kl` workers terminate on the semantic machine under
every schedule** (no fairness): any number of threads running
`treiber2NImage` on one valid layout from `worker` to `done`, sharing `top`,
each with its own node whose link word is not `top` (`StartWN`). At every
fuel, one bound `K` (depending on `fuel` and on the number of threads) on
every semantic trace. -/
theorem treiber2_nodes_term_sem_all {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    (t : BitVec 64) {states : List isa.State} {initMem : List (Loc × Val)}
    (hs : ∀ s ∈ states, ∃ n, StartWN (layout := l) t n s ∧ t ≠ n + 8) :
    TermBoundSem Arch.armv8 fuel (Config.init states initMem : Config isa) :=
  term_sem_genP (layout := l) cellsN t fun s hs' =>
    let ⟨_, h, hn⟩ := hs s hs'
    start_of_startWN h hn

/-- **The two-thread Treiber stack `treiber2_nodes.kl` terminates on the
semantic machine under every schedule** (no fairness): at the hypotheses of
`Treiber2.treiber2_nodes_envG_whole` without its reachability and finality
premises (`hn`, `hn0`, `hn1`, `hT0` are not needed). At every fuel, one bound
`K` on every semantic trace from the start configuration. -/
theorem treiber2_nodes_term_sem {fuel : Nat} (l : _root_.Layout) [Executable.ValidLayout (l treiber2NImage)]
    (t n0 n1 : BitVec 64) (ht0 : t ≠ n0 + 8) (ht1 : t ≠ n1 + 8) (_hn : n0 ≠ n1) (_hn0 : n0 ≠ 0) (_hn1 : n1 ≠ 0)
    {s0 s1 : isa.State} {initMem : List (Loc × Val)}
    (h0 : StartWN (layout := l) t n0 s0) (h1 : StartWN (layout := l) t n1 s1)
    (_hT0 : (Config.init [s0, s1] initMem).mem.initVal ⟨t, 8⟩ = 0) :
    TermBoundSem Arch.armv8 fuel (Config.init [s0, s1] initMem : Config isa) :=
  treiber2_nodes_term_sem_all l t fun s hs => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · exact ⟨n0, h0, ht0⟩
    · exact ⟨n1, h1, ht1⟩

section
open Kraken.Promising.SLR.EnvG.Treiber2 (wLayout2N wNWorker0 wNWorker1 wNWorker0_start wNWorker1_start)
open Kraken.Promising.SLR.EnvG.ConcreteTreiber2 (topAddr n1Addr n2Addr treiber2InitMem)
attribute [local instance] Kraken.Promising.SLR.EnvG.Treiber2.wLayout2N

/-- **`treiber2_nodes.kl` at the runner's layout and threads terminates on
the semantic machine under every schedule**: concrete instance of
`treiber2_nodes_term_sem` (the start configuration of
`Treiber2.treiber2_nodes_envG_whole_concrete`). -/
theorem treiber2_nodes_term_sem_concrete {fuel : Nat} :
    TermBoundSem Arch.armv8 fuel (Config.init [wNWorker0, wNWorker1] treiber2InitMem : Config isa) :=
  treiber2_nodes_term_sem wLayout2N topAddr n1Addr n2Addr (by decide) (by decide) (by decide) (by decide)
    (by decide) wNWorker0_start wNWorker1_start (by simp only [Config.init]; decide)

end

end Kraken.Promising.Live.TermTreiber2Nodes
