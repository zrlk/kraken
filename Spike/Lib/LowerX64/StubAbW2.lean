/-
**The abort paths' states keep the write abort's phase** (x86-64): the
per-node bundles `StubOAb` and `StubHAb` (`Spike/Lib/LowerX64/AbortW2.lean`)
at `Ab := WriteAb.Ab lab`, for any executable with `InstOk`, its cells
holding the runtime's code (`printIn`, `abortIn`) and passing the paths'
phase checks (`abortPhOk`, `abortPhHeapOk`). The twin of
`Spike/Lib/LowerA64/StubAbW2.lean`.

The write abort's pcs are label-relative positions (`AllocRa.abPos`), and
positions that differ sit at different pcs (`pc_ne_of_inRunB`): a block's
every target is a position (`tgt_pos`), decided on the concrete block. The
stubs' targets are all off `abPos`. The dispatcher's are in it: its
prologue is in the phase only at `%rdi = 4` and its tests only at
`-8(%rbp) = 4`, so there the data the nodes carry (the code 1 or 2) keeps
the phase out (`not_ab_pos`).

- `tgtL`, `posOf`, `posTgts`, `wfChk`, `extPos`, `offChk`, `tgt_pos`: a
  block's targets by position (as `Spike/Lib/A64PrintGAb.lean`'s, the
  positions byte offsets).
- `dispEPos`, `dispTPos`, `nvPos`, `nvPcs`, `pos_of_mem`, `notAb_of_pos`,
  `not_ab_pos`: a position's state off the phase, from its data at the
  dispatcher's positions.
- `bp_slot`: the word at `-8(%rbp)` from the abstract state.
- `blkW_abPos`, `blkW_abOff`: a block keeping the phase, the targets in
  `abPos` by their data (`hdat`), or none (`offChk`).
- `nodeW_ab_sys`, `nodeW_ab_exit`: a `syscall` resuming off the phase, and
  the exit call (`exit_group`, no successor).
- `stubOAb`, `stubHAb`: the bundles.
-/
import Spike.Lib.LowerX64.AbortW2
import Spike.Lib.X64StubWA
import Spike.Lib.X64AllocGAb
import Spike.Lib.X64Dead

namespace Spike.Lib.LowerX64

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem (Marks)
open Scc.Sem.X64 (pcOf abi atSyscall_of_cellAt mem_certSuccs_syscall certSuccs_archSetFs)
open Spike.Lib (Region)
open Spike.Lib.X64Consumer
open Spike.Lib.X64ConsumerA (AbSt)
open Spike.Lib.X64 (NodeW BlkW ND AS SO AI Abs classify okBlk arun dstep cellOff)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAt blockAtB blockAt_of_blockAtB InRunB inRunB_of_blockAt pc_ne_of_inRunB Lays)
open Spike.Lib.X64.WriteAb (Ab abPcs not_ab_of_pc bpLoad)
open Kraken.Promising.Lower.X64 (op64)

/-! ## A block's targets by position -/

section Tgt

/-- An instruction's targets: a label's start (`some L`) or the next
instruction (`none`); none for a `ret`. -/
def tgtL : AI → List (Option Label)
  | .jmp L | .call L => [some L]
  | .jcc _ L => [some L, none]
  | .ret => []
  | _ => [none]

/-- A target's position, for the instruction `k` of a block at `(L, off0)`;
past the block, the position `nxt`. -/
def posOf (L : Label) (off0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) (k : Nat) :
    Option Label → Option (Label × Nat)
  | some L' => some (L', 0)
  | none => if k + 1 < blk.length then some (L, off0 + cellOff blk (k + 1)) else nxt

/-- The instruction `k`'s targets' positions. -/
def posTgts (L : Label) (off0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) (k : Nat) :
    List (Label × Nat) :=
  match blk[k]? with
  | some dz => match classify dz.1 with
    | some a => (tgtL a).filterMap (posOf L off0 blk nxt k)
    | none => []
  | none => []

/-- **Every instruction classified, every target with a position.** -/
def wfChk (L : Label) (off0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some dz => match classify dz.1 with
      | some a => (tgtL a).all fun o => (posOf L off0 blk nxt k o).isSome
      | none => false
    | none => false

/-- The block's branch targets' positions: the labels' starts. -/
def jmpPos (blk : List (Directive × Nat)) : List (Label × Nat) :=
  blk.flatMap fun dz => match classify dz.1 with
    | some a => (tgtL a).filterMap fun o => o.map fun L => (L, 0)
    | none => []

/-- The positions outside the block: `nxt` and the labels' starts. -/
def extPos (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : List (Label × Nat) :=
  nxt.toList ++ jmpPos blk

/-- A block without branches reaches outside only `nxt`. -/
theorem extPos_of_nil {blk : List (Directive × Nat)} (h : jmpPos blk = []) (q : Label × Nat) :
    extPos blk (some q) = [q] := by
  simp [extPos, h]

/-- **Every target's position is off the write abort's.** -/
def offChk (L : Label) (off0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k => (posTgts L off0 blk nxt k).all fun q => !abPos.contains q

theorem cellOff_succ {blk : List (Directive × Nat)} {k : Nat} (hk : k < blk.length) :
    cellOff blk (k + 1) = cellOff blk k + blk[k].2 := by
  unfold cellOff
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.map_append, List.sum_append]
  simp

/-- **A block's cells are in its label's run** (`blockAtB`). -/
theorem inRunB_of_blockAtB {cells : List (Directive × Nat)} {L : Label} {off : Nat} {b : List (Directive × Nat)}
    (h : blockAtB cells L off b = true) {i : Nat} (hi : i < b.length) : InRunB cells L (off + cellOff b i) := by
  obtain ⟨k, hk⟩ := blockAt_of_blockAtB h
  exact inRunB_of_blockAt hk hi

/-- **An instruction's target is at one of its positions** (a `ret`
aside): in a block at `(L, off0)` of the cells, past it at `nxt` (`hnx`),
every position outside in the cells (`hIn`). -/
theorem tgt_pos {cells : List (Directive × Nat)} {lab : Label → Int64} {L : Label} {off0 : Nat}
    {blk : List (Directive × Nat)} {nxt : Option (Label × Nat)} (hb : blockAtB cells L off0 blk = true)
    (hwf : wfChk L off0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (off0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2) {k : Nat} (hk : k < blk.length) {a : AI}
    (hca : classify blk[k].1 = some a) (o : SO) (σ : AS) :
    a = .ret ∨ ∃ q ∈ posTgts L off0 blk nxt k, InRunB cells q.1 q.2 ∧
      a.tgt lab o (lab L + Int64.ofNat off0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) σ =
        lab q.1 + Int64.ofNat q.2 := by
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hw := List.all_eq_true.mp hwf k (List.mem_range.mpr hk)
  simp only [hd, hca] at hw
  have hpt : posTgts L off0 blk nxt k = (tgtL a).filterMap (posOf L off0 blk nxt k) := by
    simp only [posTgts, hd, hca]
  have hext : ∀ L', some L' ∈ tgtL a → InRunB cells L' 0 := fun L' hL' =>
    hIn (L', 0) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨blk[k], List.getElem_mem hk, by
      rw [hca]; exact List.mem_filterMap.mpr ⟨some L', hL', rfl⟩⟩))
  have hlab : ∀ L', some L' ∈ tgtL a → ∃ q ∈ posTgts L off0 blk nxt k, InRunB cells q.1 q.2 ∧
      lab L' = lab q.1 + Int64.ofNat q.2 := fun L' hL' =>
    ⟨(L', 0), by rw [hpt]; exact List.mem_filterMap.mpr ⟨some L', hL', rfl⟩, hext L' hL', by
      show lab L' = lab L' + Int64.ofNat 0; rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]⟩
  have he : lab L + Int64.ofNat off0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 =
      lab L + Int64.ofNat (off0 + cellOff blk (k + 1)) := by
    rw [cellOff_succ hk, Int64.ofNat_add, Int64.ofNat_add, Int64.add_assoc, Int64.add_assoc]
  have hfall : none ∈ tgtL a → ∃ q ∈ posTgts L off0 blk nxt k, InRunB cells q.1 q.2 ∧
      lab L + Int64.ofNat off0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 =
        lab q.1 + Int64.ofNat q.2 := by
    intro hn
    by_cases hlt : k + 1 < blk.length
    · refine ⟨(L, off0 + cellOff blk (k + 1)), ?_, inRunB_of_blockAtB hb hlt, he⟩
      rw [hpt]; exact List.mem_filterMap.mpr ⟨none, hn, by simp [posOf, hlt]⟩
    · have hs := List.all_eq_true.mp hw none hn
      simp only [posOf, hlt, ite_false] at hs
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
      refine ⟨q, ?_, hIn q (List.mem_append_left _ (by simp [hq])), ?_⟩
      · rw [hpt]; exact List.mem_filterMap.mpr ⟨none, hn, by simp [posOf, hlt, hq]⟩
      · rw [he, ← hnx q hq, show k + 1 = blk.length by omega]
  cases a with
  | ret => exact .inl rfl
  | jmp L' => exact .inr (hlab L' (by simp [tgtL]))
  | call L' => exact .inr (hlab L' (by simp [tgtL]))
  | jcc cc L' =>
    refine .inr ?_
    simp only [AI.tgt]
    split
    · exact hlab L' (by simp [tgtL])
    · exact hfall (by simp [tgtL])
  | ld r b n => exact .inr (hfall (by simp [tgtL]))
  | st b n r => exact .inr (hfall (by simp [tgtL]))
  | push r => exact .inr (hfall (by simp [tgtL]))
  | pop r => exact .inr (hfall (by simp [tgtL]))
  | reg w op => exact .inr (hfall (by simp [tgtL]))

end Tgt

/-! ## A position's state off the phase -/

section Pos

open Spike.Lib.X64.WriteAb (pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)

/-- The dispatcher's prologue's positions (`WriteAb.dispEPcs`). -/
def dispEPos : List (Label × Nat) := (abPos.drop 17).take 4

/-- The dispatcher's tests' positions (`WriteAb.dispTPcs`). -/
def dispTPos : List (Label × Nat) := (abPos.drop 21).take 19

/-- The write abort's positions with no data condition but the stored
length and result's (all but the dispatcher's). -/
def nvPos : List (Label × Nat) := abPos.take 17 ++ abPos.drop 40

/-- `nvPos`'s pcs. -/
def nvPcs (lab : Label → Int64) : List Int64 :=
  pcRet lab :: tailPcs lab ++ failPcs lab ++ g4Pcs lab ++ stubPcs lab

theorem dispEPcs_eq (lab : Label → Int64) : dispEPcs lab = dispEPos.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [dispEPcs, dispEPos, abPos, List.drop, List.take, List.map_cons, List.map_nil,
    show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

theorem dispTPcs_eq (lab : Label → Int64) : dispTPcs lab = dispTPos.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [dispTPcs, dispTPos, abPos, List.drop, List.take, List.map_cons, List.map_nil,
    show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

theorem nvPcs_eq (lab : Label → Int64) : nvPcs lab = nvPos.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [nvPcs, nvPos, abPos, pcRet, tailPcs, failPcs, g4Pcs, stubPcs, List.drop, List.take, List.map_cons,
    List.map_nil, List.cons_append, List.nil_append,
    show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

theorem dispEPos_sub : dispEPos.all abPos.contains = true := by decide
theorem dispTPos_sub : dispTPos.all abPos.contains = true := by decide
theorem nvPos_sub : nvPos.all abPos.contains = true := by decide

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **A position at one of a list of the write abort's positions' pcs is
in the list**, in a layout of cells with the runtime's code. -/
theorem pos_of_mem (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {lab : Label → Int64}
    (hl : (_root_.Executable.labels exe).label = lab) {P : List (Label × Nat)} (hP : P.all abPos.contains = true)
    {q : Label × Nat} (hr : InRunB cells q.1 q.2)
    (h : lab q.1 + Int64.ofNat q.2 ∈ P.map fun p => lab p.1 + Int64.ofNat p.2) : q ∈ P := by
  subst hl
  obtain ⟨p, hp', he⟩ := List.mem_map.mp h
  by_cases hq : p = q
  · exact hq ▸ hp'
  · have hpa := List.all_eq_true.mp hP p hp'
    rw [List.contains_iff_mem] at hpa
    exact absurd he (pc_ne_of_inRunB hp (abPos_inRunB hpr hab p hpa) hr hq)

/-- **A position off the write abort's is off its pcs.** -/
theorem notAbPc_of_pos (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {lab : Label → Int64}
    (hl : (_root_.Executable.labels exe).label = lab) {q : Label × Nat} (hr : InRunB cells q.1 q.2)
    (hn : abPos.contains q = false) {t : Int64} (ht : t = lab q.1 + Int64.ofNat q.2) : t ∉ abPcs lab := by
  intro hm
  rw [ht, abPcs_eq] at hm
  have := pos_of_mem hp hpr hab hl (List.all_eq_true.mpr fun p h => List.contains_iff_mem.mpr h) hr hm
  rw [← List.contains_iff_mem, hn] at this
  cases this

/-- **A state at a position off the write abort's is off its phase.** -/
theorem notAb_of_pos (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {lab : Label → Int64}
    (hl : (_root_.Executable.labels exe).label = lab) {q : Label × Nat} (hr : InRunB cells q.1 q.2)
    (hn : abPos.contains q = false) {s : State} (hs : s.st.2 = lab q.1 + Int64.ofNat q.2) : ¬ Ab lab s :=
  not_ab_of_pc (notAbPc_of_pos hp hpr hab hl hr hn hs)

/-- **A state at a position is off the phase** when the position is none
of those without a data condition (`hn`), and at the dispatcher's
prologue `%rdi ≠ 4` (`hE`), at its tests `-8(%rbp) ≠ 4` (`hT`). -/
theorem not_ab_pos (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {lab : Label → Int64}
    (hl : (_root_.Executable.labels exe).label = lab) {q : Label × Nat} (hr : InRunB cells q.1 q.2) {s : State}
    (hs : s.st.2 = lab q.1 + Int64.ofNat q.2)
    (hn : nvPos.contains q = false) (hE : dispEPos.contains q = true → s.st.1.regs.get64 .rdi ≠ 4#64)
    (hT : dispTPos.contains q = true → bpLoad s (-8) ≠ some 4#64) : ¬ Ab lab s := by
  have hnv : s.st.2 ∉ nvPcs lab := by
    rw [hs, nvPcs_eq]
    intro hm
    have := pos_of_mem hp hpr hab hl nvPos_sub hr hm
    rw [← List.contains_iff_mem, hn] at this
    cases this
  rintro (⟨h, -⟩ | ⟨h, -⟩ | h | ⟨h, h4⟩ | ⟨h, h4⟩ | h | h)
  · exact hnv (by simp [nvPcs, h])
  · exact hnv (by simp [nvPcs, h])
  · exact hnv (by simp [nvPcs, h])
  · rw [hs, dispEPcs_eq] at h
    exact hE (List.contains_iff_mem.mpr (pos_of_mem hp hpr hab hl dispEPos_sub hr h)) h4
  · rw [hs, dispTPcs_eq] at h
    exact hT (List.contains_iff_mem.mpr (pos_of_mem hp hpr hab hl dispTPos_sub hr h)) h4
  · exact hnv (by simp [nvPcs, h])
  · exact hnv (by simp [nvPcs, h])

omit [Kraken.Executable.ValidLayout exe] in
/-- **The word at `-8(%rbp)` from the abstract state**, `%rbp` at the
frame's base. -/
theorem bp_slot {R : Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ) (ho : o.get .rbp = some 0)
    (hoff : R.Off (-8)) : bpLoad s (-8) = some (σ.slot (-8)) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot (-8) hoff
  have hbp := hA.so .rbp 0 ho
  rw [← hA.regs] at hbp
  simp only [Reg64s.get64] at hbp
  simp only [bpLoad, Scc.Sem.X64.privLoad, hbp]
  rw [show R.addr 0 + (-8) = R.addr (-8) by simp only [Spike.Lib.Region.addr]; rw [BitVec.add_assoc]; rfl,
    hj, Option.map_some, hjv]

end Pos

/-! ## Blocks and single instructions keeping the phase -/

section Nodes

/-- **An instruction's next static offsets and abstract state are the
abstract run's past it.** -/
theorem arun_succ_eq (lab : Label → Int64) {lo hi : Int} {blk : List (Directive × Nat)} {am : Spike.Lib.X64.AM}
    (h : okBlk lo hi am.so blk = true) {k : Nat} (hk : k < blk.length) {a : AI} (hca : classify blk[k].1 = some a) :
    a.so (arun lab (blk.take k) am).so = (arun lab (blk.take (k + 1)) am).so ∧
      a.step (arun lab (blk.take k) am).so (am.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun lab (blk.take k) am).σ = (arun lab (blk.take (k + 1)) am).σ := by
  have hpc := Spike.Lib.X64.arun_pc lab h hk
  rw [Spike.Lib.X64.arun_take_succ lab hk, ← hpc]
  generalize blk[k] = dz at hca ⊢
  obtain ⟨d, z⟩ := dz
  simp [dstep, hca]

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block keeps the write abort's phase**: at a block of the
cells at `(L, off0)` (`hb`) passing its phase check (`hph`), with no `ret`
(`hnr`), every target a position (`hwf`, `hnx`, `hIn`) off `abPos` or, if in
it, off the phase by the data past the instruction (`hdat`). -/
theorem blkW_abPos {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {L : Label} {off0 : Nat} {nxt : Option (Label × Nat)}
    (hb : blockAtB cells L off0 blk = true) (he : lab L + Int64.ofNat off0 = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat off0) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L off0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (off0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2)
    (hdat : ∀ σ c, n.J σ c → ∀ k, k < blk.length → ∀ q ∈ posTgts L off0 blk nxt k, abPos.contains q = true →
      InRunB cells q.1 q.2 → ∀ s' : State, s'.st.2 = lab q.1 + Int64.ofNat q.2 →
      Abs R (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1 (arun lab (blk.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine Spike.Lib.X64.AllocG.blkW_abG hI hb he hok hR hlo hhi hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    fun σ c hJ k hk a hca s' _ _ hpc' hA' => ?_
  obtain ⟨hso, hst⟩ := arun_succ_eq lab (am := ⟨n.pc, n.o, σ⟩) hok hk hca
  rw [hso, hst] at hA'
  rcases tgt_pos (lab := lab) hb hwf hnx hIn hk hca (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ with rfl | ⟨q, hq, hqr, hqe⟩
  · exact (noRet_false hnr k hk hca).elim
  rw [he] at hqe
  have hs' : s'.st.2 = lab q.1 + Int64.ofNat q.2 := hpc'.trans hqe
  by_cases hqa : abPos.contains q = true
  · exact hdat σ c hJ k hk q hq hqa hqr s' hs' hA'
  · exact notAb_of_pos hI.lays hpr hab hI.labOk hqr (Bool.eq_false_iff.mpr hqa) hs'

/-- **A covered block whose every target is off the write abort keeps its
phase** (`blkW_abPos`, every target's position off `abPos`: `offChk`). -/
theorem blkW_abOff {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {L : Label} {off0 : Nat} {nxt : Option (Label × Nat)}
    (hb : blockAtB cells L off0 blk = true) (he : lab L + Int64.ofNat off0 = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat off0) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L off0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (off0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2) (hoff : offChk L off0 blk nxt = true) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk :=
  blkW_abPos hI hpr hab hb he hok hR hlo hhi hph hnr hwf hnx hIn fun _ _ _ k hk q hq hqa => by
    have hc := List.all_eq_true.mp (List.all_eq_true.mp hoff k (List.mem_range.mpr hk)) q hq
    rw [hqa] at hc
    cases hc

/-- **A `syscall` resuming off the write abort's pcs keeps its phase**: at
`p` off the sites (`hok`), `p + 2` off `abPcs` (`hnx`), every state the
kernel resumes in is at `p + 2`. -/
theorem nodeW_ab_sys {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {off : Nat} {p : Int64} (hb : blockAtB cells l off [(op64 .syscall, 2)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p) (hok : okPc p.toBitVec.toNat = true)
    (hnx : p + Int64.ofNat 2 ∉ abPcs lab) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, -⟩
  rw [hp] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSyscall_of_cellAt hc]; decide),
    fun _ _ call _ s' hs' hab' => ?_,
    fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩, fun _ h => h⟩
  exfalso
  have hpc' : s'.st.2 = p + Int64.ofNat 2 := by
    by_cases ha : ∃ a, call = .archSetFs a
    · obtain ⟨a, rfl⟩ := ha
      rw [certSuccs_archSetFs hc a] at hs'
      cases hs' with
      | tail _ h => cases h
      | head => ?_
      show s.st.2 + Int64.ofNat 2 = _
      rw [hpc]
    · obtain ⟨r, -, rfl⟩ := (mem_certSuccs_syscall hc fun a he => ha ⟨a, he⟩).1 hs'
      show s.st.2 + Int64.ofNat 2 = _
      rw [hpc]
  exact not_ab_of_pc (hpc' ▸ hnx) hab'

/-- **An exit call keeps the write abort's phase**: at `%rax = 231`
(`hx`) the call is `exit_group`, which resumes in no state; its pc off the
take site (`htk`). -/
theorem nodeW_ab_exit {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND} {l : Label}
    {off : Nat} {p : Int64} (hb : blockAtB cells l off [(op64 .syscall, 2)] = true)
    (he : lab l + Int64.ofNat off = p) (hp : n.pc = p)
    (htk : ∀ a, μ.site .take = some a → p.toBitVec.toNat ≠ a) (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rax = 231#64) :
    NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hp] at hpc
  have hc := Spike.Lib.X64.Rt.cellOf hI hb he hs hn hpc
  refine ⟨⟨fun _ h => absurd h (by rw [show abi.atSys s = true from atSyscall_of_cellAt hc]; decide),
    fun _ _ call hd s' hs' _ => ?_,
    fun _ a ha hpc' => (htk a ha (by rw [← hpc']; unfold pcOf; rw [hpc])).elim⟩, fun _ h => h⟩
  have hr : s.st.1.regs.rax.toNat = 231 := by
    have h231 := hx σ c hJ
    rw [← hA.regs] at h231
    simp only [Reg64s.get64] at h231
    rw [← UInt64.toNat_toBitVec, h231]; rfl
  have hd' : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) := by
    rw [← Spike.Lib.X64.syscallCall_exitGroup hr]; rfl
  obtain rfl := Option.some.inj (hd'.symm.trans hd)
  rw [Spike.Lib.X64.certSuccs_exitGroup] at hs'
  cases hs'

end Nodes

/-! ## The dispatcher's data -/

section Disp

open Spike.Lib.X64

/-- The abstract run's simp set over the dispatcher's blocks
(`BlockSpec.unfolds` with `AI.step` through its non-`rfl` equations). -/
local macro "arun_simp" : tactic =>
  `(tactic| simp [arun, dstep, classify, RegOnly, AI.so, soReg, regDst, regRes, Operation.interp,
    Operand.interp, RegOrMem.interp, MachineData.set, MachineData.setReg, Reg64s.set, ConstExpr.interp,
    AddrExpr.interp, SO.get, SO.set, SO.kill, SO.write, Spike.Lib.lk, Spike.Lib.rm, Reg.base,
    Spike.Lib.upd_apply, Reg64s.get_low64, BlockSpec.AI.step_ld', BlockSpec.AI.step_st',
    BlockSpec.AI.step_push', BlockSpec.AI.step_pop', BlockSpec.AI.step_reg', BlockSpec.AI.step_jmp',
    BlockSpec.AI.step_jcc'])

/-- **The dispatcher's prologue stores `%rdi` at `-8(%rbp)`**, `%rbp` at
the frame's base. -/
theorem d0_end (lab : Label → Int64) (pc : Int64) (σ : AS) :
    (arun lab (Abort.Disp.d0.take 4) ⟨pc, Abort.oE, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (Abort.Disp.d0.take 4) ⟨pc, Abort.oE, σ⟩).σ.slot (-8) = σ.regs.get64 .rdi := by
  simp only [Abort.Disp.d0]
  arun_simp

/-- **The dispatcher's tests and jumps keep `%rbp` at the frame's base and
`-8(%rbp)`.** -/
theorem tj_keep (lab : Label → Int64) {blk : List (Directive × Nat)}
    (hb : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1) (pc : Int64) (σ : AS) {j : Nat}
    (hj : j ≤ blk.length) :
    (arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).so.get .rbp = some 0 ∧
      (arun lab (blk.take j) ⟨pc, Abort.Disp.oD, σ⟩).σ.slot (-8) = σ.slot (-8) := by
  rcases hb with rfl | rfl | rfl <;>
    simp only [Abort.Disp.t1, Abort.Disp.t2, Abort.Disp.j1, List.length_zip, List.length_cons,
      List.length_nil] at hj ⊢ <;>
    rcases j with _|_|_|_|_|j <;> (try omega) <;> arun_simp

/-- **Every target in the write abort is one of the dispatcher's tests'.** -/
def dispTChk (L : Label) (off0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k => (posTgts L off0 blk nxt k).all fun q =>
    !abPos.contains q || (dispTPos.contains q && !nvPos.contains q && !dispEPos.contains q)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A test or jump of the dispatcher keeps the write abort's phase** at a
code `≠ 4` at `-8(%rbp)` (`hJ`): its targets in the write abort are tests
(`dispTChk`), where the code is still the node's (`tj_keep`). -/
theorem blkW_abDispT {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {L : Label} {off0 : Nat} {nxt : Option (Label × Nat)}
    (hblk : blk = Abort.Disp.t1 ∨ blk = Abort.Disp.t2 ∨ blk = Abort.Disp.j1)
    (hb : blockAtB cells L off0 blk = true) (he : lab L + Int64.ofNat off0 = n.pc) (hno : n.o = Abort.Disp.oD)
    (hok : okBlk (-8) 16 n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat off0) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L off0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (off0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2) (hchk : dispTChk L off0 blk nxt = true)
    (hJ : ∀ σ c, n.J σ c → σ.slot (-8) ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abPos hI hpr hab hb he hok hR (by omega) (by omega) hph hnr hwf hnx hIn
    fun σ c hj k hk q hq hqa hqr s' hs' hA' => ?_
  have hc := List.all_eq_true.mp (List.all_eq_true.mp hchk k (List.mem_range.mpr hk)) q hq
  simp only [hqa, Bool.not_true, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at hc
  obtain ⟨⟨hT, hnv⟩, hE⟩ := hc
  rw [hno] at hA'
  obtain ⟨hbp, hsl⟩ := tj_keep lab hblk n.pc σ (j := k + 1) (by omega)
  refine not_ab_pos hI.lays hpr hab hI.labOk hqr hs' hnv (fun h => by rw [hE] at h; cases h) fun _ => ?_
  rw [bp_slot hA' hbp ⟨by decide, by omega, by omega⟩, hsl]
  exact fun h => hJ σ c hj (Option.some.inj h)

/-- **The dispatcher's prologue keeps the write abort's phase** at a code
`≠ 4` in `%rdi` (`hJ`): its targets are the prologue's, where `%rdi` is
kept (`d0_rdi`), and the first test, where the code is stored at
`-8(%rbp)` (`d0_end`). -/
theorem blkW_abD0 {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} (hpc : n.pc = lab "scc_rt_abort") (hno : n.o = Abort.oE) (hR : R.OK) (hlo : R.lo ≤ -24)
    (hhi : 16 ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab "scc_rt_abort" + Int64.ofNat 0) 0 Abort.Disp.d0 = true)
    (hJ : ∀ σ c, n.J σ c → σ.regs.get64 .rdi ≠ 4#64) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n Abort.Disp.d0 := by
  have hsd := hab
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hg⟩ := hdi
  have hent := Scc.Cert.Rt.X64.label_labelGapB hI.lays hg
  rw [hI.labOk] at hent
  refine blkW_abPos hI hpr hab (nxt := some (".Lscc_rt_abort.entry", 0)) hd0
    (by rw [hpc]; exact Spike.Lib.X64.Flow.ofNat_zero' _) (hno ▸ Abort.Disp.d0_ok) hR (by omega) hhi hph
    (by decide) (by decide) (fun q hq => by
      cases hq
      rw [show 0 + cellOff Abort.Disp.d0 Abort.Disp.d0.length = 12 by decide, hent,
        show ((".Lscc_rt_abort.entry", 0) : Label × Nat).2 = 0 from rfl, Spike.Lib.X64.Flow.ofNat_zero']) ?_ ?_
  · intro q hq
    have hx : extPos Abort.Disp.d0 (some (".Lscc_rt_abort.entry", 0)) = [(".Lscc_rt_abort.entry", 0)] := by
      decide
    rw [hx, List.mem_singleton] at hq
    subst hq
    exact abPos_inRunB hpr hab _ (by decide)
  intro σ c hj k hk q hq hqa hqr s' hs' hA'
  rw [hno, hpc] at hA'
  -- the prologue's own pcs, `%rdi` kept
  have hE : k < 3 → s'.st.1.regs.get64 .rdi ≠ 4#64 := fun h3 => by
    have hr := Spike.Lib.X64.StubW.d0_rdi (lab := lab) (lab "scc_rt_abort") σ (k := k + 1)
      (by simp [Abort.Disp.d0]; omega)
    rw [hA'.regs, hr]
    exact hJ σ c hj
  rcases k with _|_|_|_|k
  · have hq' : q = ("scc_rt_abort", 1) := by
      have : posTgts "scc_rt_abort" 0 Abort.Disp.d0 (some (".Lscc_rt_abort.entry", 0)) 0 = [("scc_rt_abort", 1)] :=
        by decide
      rw [this, List.mem_singleton] at hq; exact hq
    subst hq'
    exact not_ab_pos hI.lays hpr hab hI.labOk hqr hs' (by decide) (fun _ => hE (by omega)) (fun h => by cases h)
  · have hq' : q = ("scc_rt_abort", 4) := by
      have : posTgts "scc_rt_abort" 0 Abort.Disp.d0 (some (".Lscc_rt_abort.entry", 0)) 1 = [("scc_rt_abort", 4)] :=
        by decide
      rw [this, List.mem_singleton] at hq; exact hq
    subst hq'
    exact not_ab_pos hI.lays hpr hab hI.labOk hqr hs' (by decide) (fun _ => hE (by omega)) (fun h => by cases h)
  · have hq' : q = ("scc_rt_abort", 8) := by
      have : posTgts "scc_rt_abort" 0 Abort.Disp.d0 (some (".Lscc_rt_abort.entry", 0)) 2 = [("scc_rt_abort", 8)] :=
        by decide
      rw [this, List.mem_singleton] at hq; exact hq
    subst hq'
    exact not_ab_pos hI.lays hpr hab hI.labOk hqr hs' (by decide) (fun _ => hE (by omega)) (fun h => by cases h)
  · have hq' : q = (".Lscc_rt_abort.entry", 0) := by
      have : posTgts "scc_rt_abort" 0 Abort.Disp.d0 (some (".Lscc_rt_abort.entry", 0)) 3 =
          [(".Lscc_rt_abort.entry", 0)] := by decide
      rw [this, List.mem_singleton] at hq; exact hq
    subst hq'
    obtain ⟨hbp, hsl⟩ := d0_end lab (lab "scc_rt_abort") σ
    refine not_ab_pos hI.lays hpr hab hI.labOk hqr hs' (by decide) (fun h => by cases h) fun _ => ?_
    rw [bp_slot hA' hbp ⟨by decide, by omega, by omega⟩, hsl]
    exact fun h => hJ σ c hj (Option.some.inj h)
  · simp only [Abort.Disp.d0, List.length_zip, List.length_cons, List.length_nil] at hk
    omega

end Disp

/-! ## The bundles -/

section Bundles

open Spike.Lib.X64
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.X64.StubW (abortPhOk abortPhHeapOk phOne)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}
  {c0 : Ctl}

omit [Kraken.Executable.ValidLayout exe] in
/-- The first cell of a block is in its label's run. -/
theorem inRunB_first {L : Label} {off : Nat} {b : List (Directive × Nat)} (h : blockAtB cells L off b = true)
    (hne : 0 < b.length) : InRunB cells L off := by
  simpa [cellOff] using inRunB_of_blockAtB h hne

/-- **A stub's nodes keep the write abort's phase**: the stub `st` with the
argument block `x1` in the cells (`hst`), its blocks passing their phase
checks (`hp0`, `hp1`, `hp2`) and the single instructions theirs (`ho1`,
`ho5`), the exit call off the take site (`htk`), every position the stub
reaches off the write abort's (the decided `hw*`, `hf*`, `h7`, `h36`). -/
theorem stubAb_nodes {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi) {st : Abort.Stub} {x1 : List (Directive × Nat)}
    (hst : Scc.Cert.Rt.X64.Abort.stubIn cells st x1 = true)
    (hp0 : blkPh okPc ph (fun _ => false) lab (lab st.fn + Int64.ofNat 0) 0 Abort.x0 = true)
    (ho1 : okPc (lab st.entry + Int64.ofNat 0).toBitVec.toNat = true)
    (hp1 : blkPh okPc ph (fun _ => false) lab (lab st.entry + Int64.ofNat 7) 0 x1 = true)
    (ho5 : okPc (lab st.entry + Int64.ofNat 34).toBitVec.toNat = true)
    (hp2 : blkPh okPc ph (fun _ => false) lab (lab st.entry + Int64.ofNat 36) 0 Abort.x2 = true)
    (htk : ∀ a, μ.site .take = some a → (lab st.exit).toBitVec.toNat ≠ a)
    (hw0 : wfChk st.fn 0 Abort.x0 (some (st.entry, 0)) = true)
    (hf0 : offChk st.fn 0 Abort.x0 (some (st.entry, 0)) = true)
    (hok1 : okBlk (-24) 16 Abort.oI x1 = true) (hnr1 : noRetBlk x1 = true) (hz1 : 7 + cellOff x1 x1.length = 34)
    (hx1 : 0 < x1.length) (hj1 : jmpPos x1 = []) (hw1 : wfChk st.entry 7 x1 (some (st.entry, 34)) = true)
    (hf1 : offChk st.entry 7 x1 (some (st.entry, 34)) = true)
    (hw2 : wfChk st.entry 36 Abort.x2 (some (st.exit, 0)) = true)
    (hf2 : offChk st.entry 36 Abort.x2 (some (st.exit, 0)) = true)
    (h7 : abPos.contains (st.entry, 7) = false) (h36 : abPos.contains (st.entry, 36) = false) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (Abort.N (_root_.Executable.labels exe).label st c0 .e) Abort.x0 ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (Abort.N (_root_.Executable.labels exe).label st c0 .n1) ∧
      BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (Abort.N (_root_.Executable.labels exe).label st c0 .n2) x1 ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (Abort.N (_root_.Executable.labels exe).label st c0 .sys) ∧
      BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (Abort.N (_root_.Executable.labels exe).label st c0 .n5) Abort.x2 ∧
      NodeW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F
        (Abort.N (_root_.Executable.labels exe).label st c0 .ex) := by
  have hl := hI.labOk
  subst hl
  have hst' := hst
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst'
  obtain ⟨hb0, hn1, hb1, hsysIn, hb2, hx, hg, hg'⟩ := hst'
  have hent := Scc.Cert.Rt.X64.label_labelGapB hI.lays hg
  have hext := Scc.Cert.Rt.X64.label_labelGapB hI.lays hg'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine blkW_abOff hI hpr hab hb0 (ofNat_zero' _) Abort.x0_ok hR hlo hhi hp0 (by decide) hw0
      (fun q hq => by
        cases hq
        rw [show 0 + cellOff Abort.x0 Abort.x0.length = 8 by decide, hent,
          show ((st.entry, 0) : Label × Nat).2 = 0 from rfl, ofNat_zero']) ?_ hf0
    intro q hq
    rw [extPos_of_nil (by decide)] at hq
    rw [List.mem_singleton.mp hq]
    exact inRunB_first hn1 (by simp)
  · rw [ofNat_zero'] at ho1
    exact Spike.Lib.X64.AllocG.nodeW_ab_si hI hn1 (ofNat_zero' _) rfl ho1
      (notAbPc_of_pos hI.lays hpr hab rfl (q := (st.entry, 7)) (inRunB_first hb1 hx1) h7 rfl)
  · refine blkW_abOff hI hpr hab hb1 rfl hok1 hR hlo hhi hp1 hnr1 hw1
      (fun q hq => by cases hq; rw [hz1]) ?_ hf1
    intro q hq
    rw [extPos_of_nil hj1] at hq
    rw [List.mem_singleton.mp hq]
    exact inRunB_first hsysIn (by decide)
  · exact nodeW_ab_sys hI hsysIn rfl rfl ho5
      (notAbPc_of_pos hI.lays hpr hab rfl (q := (st.entry, 36)) (inRunB_first hb2 (by decide)) h36
        (by rw [Int64.add_assoc, ← Int64.ofNat_add]))
  · refine blkW_abOff hI hpr hab hb2 rfl Abort.x2_ok hR hlo hhi hp2 (by decide) hw2
      (fun q hq => by
        cases hq
        rw [show 36 + cellOff Abort.x2 Abort.x2.length = 52 by decide, hext,
          show ((st.exit, 0) : Label × Nat).2 = 0 from rfl, ofNat_zero'])
      ?_ hf2
    intro q hq
    rw [extPos_of_nil (by decide)] at hq
    rw [List.mem_singleton.mp hq]
    exact inRunB_first hx (by decide)
  · exact nodeW_ab_exit hI hx (ofNat_zero' _) rfl htk fun _ _ h => h.2.1

/-- **`StubOAb` at the write abort's phase**: the overflow abort path's
nodes keep it, for an executable with `InstOk` (`hI`), the runtime's code in
its cells (`hpr`, `hab`) and the path's phase check (`hphs`), the stub's
frame in the region (`hlo`, `hhi`) and its exit call off the take site
(`htk`). -/
theorem stubOAb {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhOk okPc ph lab = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.overflow.exit).toBitVec.toNat ≠ a) :
    StubOAb μ (Ab lab) exe endPc R F c0 := by
  have hsd := hab
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨-, ht1, -, hg1, -⟩ := hdi
  simp only [abortPhOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pg1, pb0, o1, -, pb1, o5, -, pb2, -⟩ := hphs
  obtain ⟨se, sn1, sn2, hsys, sn5, sex⟩ := stubAb_nodes (c0 := c0) (F := F) hI hpr hab hR hlo hhi hsd.1.1.1.1.1
    pb0 o1 pb1 o5 pb2 htk (by decide) (by decide) Abort.x1Overflow_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hl := hI.labOk
  subst hl
  refine ⟨?_, ?_, ?_, se, sn1, sn2, hsys, sn5, sex⟩
  · exact blkW_abD0 hI hpr hab rfl rfl hR hlo hhi pd0 fun _ _ h => by rw [h.2]; decide
  · refine blkW_abDispT hI hpr hab (nxt := some (".Lscc_rt_abort.entry", 16)) (.inl rfl) ht1 (ofNat_zero' _) rfl
      Abort.Disp.t1_ok hR hlo hhi pt1 (by decide) (by decide)
      (fun q hq => by cases hq; rw [show 0 + cellOff Abort.Disp.t1 Abort.Disp.t1.length = 16 by decide])
      ?_ (by decide) fun _ _ h => by rw [h.2]; decide
    intro q hq
    rw [show extPos Abort.Disp.t1 (some (".Lscc_rt_abort.entry", 16)) =
      [(".Lscc_rt_abort.entry", 16), (".Lscc_rt_abort.is0", 0)] by decide] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact abPos_inRunB hpr hab _ (by decide)
    · rw [List.mem_singleton.mp hq]
      exact inRunB_first hg1 (by decide)
  · refine blkW_abOff hI hpr hab (nxt := none) hg1 (ofNat_zero' _) Abort.Disp.g1_ok hR (by omega) hhi pg1
      (by decide) (by decide) (fun _ h => by cases h) ?_ (by decide)
    intro q hq
    rw [show extPos Abort.Disp.g1 none = [(Abort.overflow.fn, 0)] by decide] at hq
    rw [List.mem_singleton.mp hq]
    have hst := hsd.1.1.1.1.1
    simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
    exact inRunB_first hst.1 (by decide)

/-- **`StubHAb` at the write abort's phase**: the heap abort path's nodes
keep it, as `stubOAb` with the path's phase check `abortPhHeapOk`. -/
theorem stubHAb {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hphs : abortPhHeapOk okPc ph lab = true) (hR : R.OK) (hlo : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (htk : ∀ a, μ.site .take = some a → (lab Abort.heap.exit).toBitVec.toNat ≠ a) :
    StubHAb μ (Ab lab) exe endPc R F c0 := by
  have hsd := hab
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨-, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, -, pb1, o5, -, pb2, -⟩ := hphs
  obtain ⟨se, sn1, sn2, hsys, sn5, sex⟩ := stubAb_nodes (c0 := c0) (F := F) hI hpr hab hR hlo hhi hsd.1.1.1.1.2
    pb0 o1 pb1 o5 pb2 htk (by decide) (by decide) Abort.x1Heap_ok (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have hl := hI.labOk
  subst hl
  refine ⟨?_, ?_, ?_, ?_, ?_, se, sn1, sn2, hsys, sn5, sex⟩
  · exact blkW_abD0 hI hpr hab rfl rfl hR hlo hhi pd0 fun _ _ h => by rw [h.2]; decide
  · refine blkW_abDispT hI hpr hab (nxt := some (".Lscc_rt_abort.entry", 16)) (.inl rfl) ht1 (ofNat_zero' _) rfl
      Abort.Disp.t1_ok hR hlo hhi pt1 (by decide) (by decide)
      (fun q hq => by cases hq; rw [show 0 + cellOff Abort.Disp.t1 Abort.Disp.t1.length = 16 by decide])
      ?_ (by decide) fun _ _ h => by rw [h.2]; decide
    intro q hq
    rw [show extPos Abort.Disp.t1 (some (".Lscc_rt_abort.entry", 16)) =
      [(".Lscc_rt_abort.entry", 16), (".Lscc_rt_abort.is0", 0)] by decide] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact abPos_inRunB hpr hab _ (by decide)
    · rw [List.mem_singleton.mp hq]
      have hdi := hsd.2
      simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
      exact inRunB_first hdi.2.2.2.1 (by decide)
  · refine blkW_abDispT hI hpr hab (nxt := none) (.inr (.inr rfl)) hj1 rfl rfl
      Abort.Disp.j1_ok hR hlo hhi pj1 (by decide) (by decide) (fun _ h => by cases h) ?_ (by decide)
      fun _ _ h => by rw [h.2]; decide
    intro q hq
    rw [show extPos Abort.Disp.j1 none = [(".Lscc_rt_abort.next1", 0)] by decide] at hq
    rw [List.mem_singleton.mp hq]
    exact abPos_inRunB hpr hab _ (by decide)
  · refine blkW_abDispT hI hpr hab (nxt := some (".Lscc_rt_abort.next1", 16)) (.inr (.inl rfl)) ht2
      (ofNat_zero' _) rfl Abort.Disp.t2_ok hR hlo hhi pt2 (by decide) (by decide)
      (fun q hq => by cases hq; rw [show 0 + cellOff Abort.Disp.t2 Abort.Disp.t2.length = 16 by decide])
      ?_ (by decide) fun _ _ h => by rw [h.2]; decide
    intro q hq
    rw [show extPos Abort.Disp.t2 (some (".Lscc_rt_abort.next1", 16)) =
      [(".Lscc_rt_abort.next1", 16), (".Lscc_rt_abort.is2", 0)] by decide] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact abPos_inRunB hpr hab _ (by decide)
    · rw [List.mem_singleton.mp hq]
      exact inRunB_first hg2 (by decide)
  · refine blkW_abOff hI hpr hab (nxt := none) hg2 (ofNat_zero' _) Abort.Disp.g2_ok hR (by omega) hhi pg2
      (by decide) (by decide) (fun _ h => by cases h) ?_ (by decide)
    intro q hq
    rw [show extPos Abort.Disp.g2 none = [(Abort.heap.fn, 0)] by decide] at hq
    rw [List.mem_singleton.mp hq]
    have hst := hsd.1.1.1.1.2
    simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
    exact inRunB_first hst.1 (by decide)

end Bundles

/-- info: 'Spike.Lib.LowerX64.tgt_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms tgt_pos

/-- info: 'Spike.Lib.LowerX64.not_ab_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms not_ab_pos

/-- info: 'Spike.Lib.LowerX64.blkW_abPos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abPos

/-- info: 'Spike.Lib.LowerX64.blkW_abOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abOff

/-- info: 'Spike.Lib.LowerX64.nodeW_ab_sys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_sys

/-- info: 'Spike.Lib.LowerX64.nodeW_ab_exit' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms nodeW_ab_exit

/-- info: 'Spike.Lib.LowerX64.blkW_abDispT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abDispT

/-- info: 'Spike.Lib.LowerX64.blkW_abD0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abD0

/-- info: 'Spike.Lib.LowerX64.stubAb_nodes' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubAb_nodes

/-- info: 'Spike.Lib.LowerX64.stubOAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubOAb

/-- info: 'Spike.Lib.LowerX64.stubHAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms stubHAb

end Spike.Lib.LowerX64
