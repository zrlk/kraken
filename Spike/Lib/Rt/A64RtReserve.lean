/-
**`scc_rt_thread_reserve` inside `W`** (AArch64): the node and segment
level of `Spike/Lib/A64Reserve.lean`'s walks, as `scc_rt_alloc_tcb`'s
(`tcbN`/`TcbW`/`allocTcb_segW`/`tcbW_gen`):

    entry  sp, x29, x30 the ghosts' (`Pre`)
    exit   x0 = n + 1 (`Post`)
    words  scc_rt_nthreads: n → n + 1 (owned at the add, `n + 1 ≤ 1023`)

- `ResG`, `rvN`, `rvX`: the ghosts and the nodes of the one feasible path.
- `ResOk`: the counter's add's memory-side facts (`TcbOk`'s form).
- `ReserveW`, `reserve_segW`: the node obligations and the callee segment.
- `ResPh`, `reserveW_gen`: the phase facts and the node obligations from them.
- `reserveIn_of`, `reserveIn_of_a13code`: the code check from A13's groups
  (`Scc.Cert.Spawn.A64.reserveGrps`).
-/
import Spike.Lib.A64Reserve
import Spike.Lib.Rt.A64Segs
import Spike.Lib.Rt.A64RtTcb
import Scc.Cert.SpawnA64

namespace Spike.Lib.A64.Rt.Reserve

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib.A64.Flow Spike.Lib.A64.Flow.Ret0
open Spike.Lib.A64.Flow.Reserve
open Scc.Cert.Rt.A64 (Lays endOf blockAt labelGap label_labelGap RtAll BsOk GapAt rtIn_sound)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer

set_option linter.unusedSimpArgs false

/-! ## The nodes -/

/-- `scc_rt_nthreads`' address. -/
abbrev ntA (lab : Label → Int64) : BitVec 64 := (lab "scc_rt_nthreads").toBitVec

/-- **The ghosts of a call**: the frame's, the counter's old value `n`
(the own map's, not the state's), the source control. -/
structure ResG where
  g : G
  n : BitVec 64
  c0 : Ctl

/-- `scc_rt_thread_reserve`'s internal nodes: one per block or single
instruction of its feasible path. -/
inductive RN where
  | e | entry | add | arg | rmw | bnd | j | ok

section Nodes

variable (lab : Label → Int64) (q : ResG)

/-- **The nodes.** -/
def rvN : RN → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Flow.Reserve.Pre q.g σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ⟩
  | .add => ⟨lab entryL + Int64.ofNat (4 * 1), oI, fun σ c => c = q.c0 ∧
      ∃ σ0, Fr0 q.g σ0 ∧ σ = (SI.adrp .X9 "scc_rt_nthreads").step lab σ0⟩
  | .arg => ⟨lab entryL + Int64.ofNat (4 * 2), oI, fun σ c => c = q.c0 ∧ Fr0 q.g σ ∧ σ.regs.X9.toBitVec = ntA lab⟩
  | .rmw => ⟨rmwPc lab, oI, fun σ c => c = q.c0 ∧
      Fr1 q.g (ntA lab) σ ∧ σ.regs.X9.toBitVec = 1#64 ∧ σ.regs.X10.toBitVec = ntA lab⟩
  | .bnd => ⟨lab entryL + Int64.ofNat (4 * 6), oI, fun σ c => c = q.c0 ∧
      Fr1 q.g (ntA lab) σ ∧ σ.regs.X11.toBitVec = q.n⟩
  | .j => ⟨lab entryL + Int64.ofNat (4 * 15), oI, fun σ c => c = q.c0 ∧ Fr2 q.g (ntA lab) q.n σ⟩
  | .ok => ⟨lab okL, oI, fun σ c => c = q.c0 ∧ Fr2 q.g (ntA lab) q.n σ⟩

/-- **The exit**: at the return address, `Post`. -/
def rvX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, oE, fun σ c => c = q.c0 ∧ Flow.Reserve.Post q.g q.n σ⟩

/-- `Post`'s `x0` is the new thread's id `n + 1`. -/
theorem post_x0 {g : G} {n : BitVec 64} {σ : Flow.AS} (hP : Flow.Reserve.Post g n σ) : σ.regs.X0.toBitVec = n + 1#64 := hP.2.2.2

end Nodes

/-- **The counter's add** `ldaddal` on `scc_rt_nthreads`: the word holds
`n` at the add (`own`) and runtime memory may hold `n + 1` there (`next`). -/
structure ResOk (ms : MemSide isaLSE2) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (n : BitVec 64) : Prop where
  next : StOk ms F exe endPc (ntA (_root_.Executable.labels exe).label) (n + 1#64)
  own : OwnAt ms exe endPc (rmwPc (_root_.Executable.labels exe).label) (ntA (_root_.Executable.labels exe).label) n

theorem ResOk.mono {ms : MemSide isaLSE2} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {n : BitVec 64} (h : ResOk ms F exe endPc n) (hFF : ∀ m, F' m → F m) : ResOk ms F' exe endPc n :=
  ⟨h.next.mono hFF, h.own⟩

/-- **The node obligations inside `W`**: the block nodes' states (`BlkW`)
and the single instructions' (`NodeW`). -/
def ReserveW (W : Frag isaLSE2) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (q : ResG) : RN → Prop
  | .e => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .e) rPro
  | .entry => NodeW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .entry)
  | .add => NodeW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .add)
  | .arg => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .arg) rArg
  | .rmw => NodeW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .rmw)
  | .bnd => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .bnd) rBnd
  | .j => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .j) rJ
  | .ok => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .ok) rRet

/-! ## The callee segment -/

section SegProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {R : Spike.Lib.Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_reserve` inside `W`: the block, its
`okBlk`, its code, its obligation; the edge is left. -/
local macro "rnodeW " b:ident ok:ident hb:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hal hlo hhi
    (code_of hp hend $hb (by first | rfl | exact ofNat4_zero _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_reserve` is one segment inside `W`**: in any valid
layout of any program with its code (`hin`), from its entry to its return,
for any region holding its frame of 48 and any frame condition implying
`F0`, given the bound's room (`hn`) and the counter's add's facts (`hres`). -/
theorem reserve_segW {W : Frag isaLSE2} {K : State → State → Prop} {prog : List Directive} {kp : Nat}
    (hp : Lays exe prog kp) (hend : endPc = endOf exe prog kp) (hin : reserveIn prog = true)
    (hF : FStable R F) (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : ResG) (hn : q.n.toNat + 1 ≤ 1023)
    (hres : ResOk ms F0 exe endPc q.n) (hW : ∀ i, ReserveW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (rvN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (rvX q x) s c) := by
  have h := hin
  simp only [reserveIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have eEntry := label_labelGap hp hg
  refine fn_segW (N := rvN _ q) (E := rvX q) (fun i => ?_) RN.e
  cases i
  case e =>
    rnodeW rPro rPro_ok bE (hW RN.e)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨RN.entry, by rw [h1, ← eEntry]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine si_ndW (si := .adrp .X9 "scc_rt_nthreads") hF
      (code_of hp hend bA (ofNat4_zero _)) (hW RN.entry) fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.add, ?_, rfl,
        hJ.1, σ, hJ.2, rfl⟩⟩
    rfl
  case add =>
    refine si_ndW (si := .addLo12 .X9 .X9 "scc_rt_nthreads") hF
      (code_of hp hend bA1 rfl) (hW RN.add) fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.arg, ?_, rfl, ?_⟩⟩
    · exact (ofNat4_succ' _ 1).symm
    · obtain ⟨rfl, σ0, h0, rfl⟩ := hJ
      exact ⟨rfl, labStep_fr0 _ _ h0, (AllocTcb.labStep_spec _ _ σ0).1⟩
  case arg =>
    rnodeW rArg rArg_ok bArg (hW RN.arg)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, h9⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := rArg_walk (_root_.Executable.labels exe).label _ hJ h9
    exact .inl ⟨RN.rmw, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownLdop_ndW hF (code_of hp hend bRmw rfl) hres.own (hW RN.rmw) fun _ σ c _ _ hJ => ?_
    dsimp only [rvN] at hJ ⊢
    obtain ⟨rfl, hJ, h9, h10⟩ := hJ
    refine ⟨h10, ?_, .inl ⟨RN.bnd, (ofNat4_succ' _ 5).symm, rfl, rfl, ?_, ?_⟩⟩
    · rw [add_apply, getRegOrZr_x9, h9]; exact hres.next.mono hFF
    · simpa [ldStep, Fr1, Fr0] using hJ
    · simp [ldStep]
  case bnd =>
    rnodeW rBnd rBnd_ok bBnd (hW RN.bnd)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, h11⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rBnd_walk (_root_.Executable.labels exe).label _ hJ h11 hn
    exact .inl ⟨RN.j, by rw [h1, ← ofNat4_add]; rfl, by rw [h2]; rfl, rfl, h3⟩
  case j =>
    rnodeW rJ rJ_ok bJ (hW RN.j)
    dsimp only [rvN, rvX] at hJ ⊢
    rw [rJ_run]
    exact .inl ⟨RN.ok, rfl, rfl, hJ⟩
  case ok =>
    rnodeW rRet rRet_ok bOk (hW RN.ok)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end SegProof

/-! ## The node obligations from the phase facts -/

/-- The pcs of the single instructions without an event: the label pair's. -/
def siPcs (lab : Label → Int64) : List Int64 :=
  [lab entryL + Int64.ofNat (4 * 0), lab entryL + Int64.ofNat (4 * 1)]

/-- The nodes' pcs and the pc after the counter's add. -/
def resPcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat (4 * 0), lab entryL + Int64.ofNat (4 * 2), rmwPc lab, rmwPc lab + Int64.ofNat 4,
    lab entryL + Int64.ofNat (4 * 6), lab entryL + Int64.ofNat (4 * 15), lab okL + Int64.ofNat (4 * 0)] ++ siPcs lab

/-- **`scc_rt_thread_reserve`'s phase facts** at labels `lab`, phase index
`ph`, off-site pcs `okPc`, owned words by phase `ownOf`, returning to `ra`:
each block's phase check with no dead target (the bound's abort in the
phase too, as A13's table checks it), each single instruction off the
sites in its next pc's phase, no node in the take's phase, the counter
owned at its add and updated by `+ 1`. -/
structure ResPh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab : Label → Int64) (ra : Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat (4 * 0)) ra rPro = true
  arg : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 2)) ra rArg = true
  bnd : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 6)) ra rBnd = true
  j : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat (4 * 15)) ra rJ = true
  ok : blkPh okPc ph (fun _ => false) lab (lab okL + Int64.ofNat (4 * 0)) ra rRet = true
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 4).toBitVec.toNat))
    ⟨ntA lab, 8⟩ (fun old => (AtomicOp.ADD.apply (old.setWidth 64) 1#64).setWidth 128) = true

theorem rPro_noRet : noRetBlk rPro = true := by rfl
theorem rArg_noRet : noRetBlk rArg = true := by rfl
theorem rBnd_noRet : noRetBlk rBnd = true := by rfl
theorem rJ_noRet : noRetBlk rJ = true := by rfl

/-- **`scc_rt_thread_reserve`'s states are inside `SFacts`**, for any
program with its code (`hin`), in any region holding its frame, with the
source control `c0` (`hC0`), returning to `ra` (`hra`), its phase facts
(`hph`) and its counter mapped (`hmN`) and unmapped in private memory under
the frame condition (`hunN`). -/
theorem reserveW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {prog : List Directive} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : reserveIn prog = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (q : ResG)
    (hq : q.c0 = c0) (hra : q.g.ra = ra.toBitVec) (hph : ResPh okPc ph Tk ownOf lab ra)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨ntA lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA lab) 8 = none) :
    ∀ i, ReserveW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F q i := by
  have h := hin
  simp only [reserveIn, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bA1⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hsi : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧
      ph (p + Int64.ofNat 4).toBitVec.toNat = ph p.toBitVec.toNat := hph.si
  have hnr : ∀ {blk : List Directive}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length) r, Flow.classify blk[k] = some (Flow.AI.ret r) →
      Int64.ofInt ((Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra' :=
    fun hb _ _ _ _ _ k hk r hr => (noRet_false hb k hk r hr).elim
  intro i
  cases i
  case e =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bE (ofNat4_zero _) rPro_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr rPro_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case entry =>
    dsimp only [ReserveW]; rw [hI.labOk]
    have := hsi (lab entryL + Int64.ofNat (4 * 0)) (by simp [siPcs])
    exact nodeW_si_pre hI bA rfl (ofNat4_zero _).symm (hC _ fun _ _ hJ => hJ.1) this.1
      (hT _ (by simp [resPcs, siPcs])) this.2
  case add =>
    dsimp only [ReserveW]; rw [hI.labOk]
    have := hsi (lab entryL + Int64.ofNat (4 * 1)) (by simp [siPcs])
    exact nodeW_si_pre hI bA1 rfl rfl (hC _ fun _ _ hJ => hJ.1) this.1 (hT _ (by simp [resPcs, siPcs])) this.2
  case arg =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bArg rfl rArg_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr rArg_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case rmw =>
    dsimp only [ReserveW]; rw [hI.labOk]
    refine nodeW_ldop_pre hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk (hT _ (by simp [resPcs]))
      (hT _ (by simp [resPcs])) (fun σ _ hJ => hJ.2.2.2) hmN hunN hph.rmwIn fun σ _ hJ => ?_
    rw [Spike.Lib.A64.Alloc.getRegOrZr_x]
    simp only [Reg64s.getXReg]
    rw [hJ.2.2.1]
    exact hph.rmwUpd
  case bnd =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bBnd rfl rBnd_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr rBnd_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case j =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bJ rfl rJ_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j
      (hnr rJ_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case ok =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bOk (ofNat4_zero _) rRet_ok hR hal (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok
      (hret_of_run rRet_ok fun _ _ hJ => by
        dsimp only [rvN] at hJ ⊢
        rw [(rRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))

/-! ## The code check from A13's groups -/

/-- **`reserveIn` from A13's groups** (`reserveGrps`, its blocks the hand ones). -/
theorem reserveIn_of {prog : List Directive} (h : RtAll prog Scc.Cert.Spawn.A64.reserveGrps) :
    reserveIn prog = true := by
  have e : Scc.Cert.Spawn.A64.reserveGrps = [
      ⟨fnL, [(0, rPro)], some (4, entryL)⟩,
      ⟨entryL, Spike.Lib.A64.Rt.labPair 0 "scc_rt_nthreads" ++ [(2, rArg), (5, [rmwDir]), (6, rBnd), (15, rJ)],
        none⟩,
      ⟨fullL, [(0, parseAArch64("movz x0, #5
bl scc_rt_abort"))], none⟩,
      ⟨okL, [(0, rRet)], none⟩] := rfl
  rw [e] at h
  simp only [Spike.Lib.A64.Rt.labPair, List.cons_append, List.nil_append, Nat.reduceAdd, RtAll, BsOk, GapAt,
    and_true] at h
  simp only [reserveIn, h, Bool.and_self]

/-- **`reserveIn` from A13's code part** (`spawnGrps` in the program). -/
theorem reserveIn_of_a13code {lo : Nat} {prog : List Directive} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.Spawn.A64.a13code lo prog Λ = true) : reserveIn prog = true := by
  simp only [Scc.Cert.Spawn.A64.a13code, Bool.and_eq_true] at h
  have := rtIn_sound h.1
  unfold Scc.Cert.Spawn.A64.spawnGrps at this
  exact reserveIn_of (RtAll.append (RtAll.append this).1).1

end Spike.Lib.A64.Rt.Reserve
