/-
**`scc_rt_thread_reserve` inside `W`** (x86-64): the node and segment
level of `Spike/Lib/X64Reserve.lean`'s walks, as `scc_rt_alloc_tcb`'s
(`tcbN`/`TcbW`/`allocTcb_segW`/`tcbW_gen`). The x86-64 twin of
`Spike/Lib/Rt/A64RtReserve.lean`.

    entry  %rsp, %rbp, the return address the ghosts' (`Pre`)
    exit   %rax = n + 1 (`Post`)
    words  scc_rt_nthreads: n → n + 1 (owned at the add, `n + 1 ≤ 1023`)

- `ResG`, `rvN`, `rvX`: the ghosts and the nodes of the one feasible path.
- `ResOk`: the counter's add's memory-side facts (`TcbOk`'s form).
- `ReserveW`, `reserve_segW`: the node obligations and the callee segment.
- `ResPh`, `reserveW_gen`: the phase facts and the node obligations from them.
- `reserveIn_of`, `reserveIn_of_a13code`: the code check from A13's groups
  (`Scc.Cert.Spawn.X64.reserveGrps`).

Where x86-64 differs from AArch64: one `leaq` node (`entry`) where AArch64
has the `adrp`/`add` pair (`entry`, `add`); the add is `lock xadd`
(`ownXadd_ndW`, `nodeW_xadd_pre`).
-/
import Spike.Lib.X64Reserve
import Spike.Lib.Rt.X64Segs
import Spike.Lib.Rt.X64RtTcb
import Scc.Cert.SpawnX64

namespace Spike.Lib.X64.Rt.Reserve

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower Kraken.Promising.Lower.X64
open Kraken.X64.Parser Spike.Lib.X64 Spike.Lib.X64.Flow Spike.Lib.X64.Flow.Ret0
open Spike.Lib.X64.Flow.Reserve
open Spike.Lib.X64.Flow.Ret0.AllocTcb (G siAt)
open Scc.Cert.Rt.X64 (Lays endOf blockAtB labelGapB code_field label_labelGapB RtAll BsOk GapAt rtIn_sound)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (pcOf)
open Spike.Lib.X64Consumer
open Spike.Lib.X64.Rt

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
  | e | entry | arg | rmw | bnd | j | ok

section Nodes

variable (lab : Label → Int64) (q : ResG)

/-- **The nodes.** -/
def rvN : RN → ND
  | .e => ⟨lab fnL, oE, fun σ c => c = q.c0 ∧ Flow.Reserve.Pre q.g σ⟩
  | .entry => ⟨lab entryL, oI, fun σ c => c = q.c0 ∧ Flow.Reserve.Fr q.g (s0 q.g) σ⟩
  | .arg => ⟨lab entryL + Int64.ofNat 7, oI, fun σ c => c = q.c0 ∧ Flow.Reserve.Fr q.g (s0 q.g) σ ∧
      σ.regs.rax.toBitVec = ntA lab⟩
  | .rmw => ⟨rmwPc lab, oI, fun σ c => c = q.c0 ∧
      Flow.Reserve.Fr q.g (s1 q.g (ntA lab)) σ ∧ σ.regs.rax.toBitVec = 1#64 ∧ σ.regs.rcx.toBitVec = ntA lab⟩
  | .bnd => ⟨lab entryL + Int64.ofNat 27, oI, fun σ c => c = q.c0 ∧
      Flow.Reserve.Fr q.g (s1 q.g (ntA lab)) σ ∧ σ.regs.rax.toBitVec = q.n⟩
  | .j => ⟨lab entryL + Int64.ofNat 65, oI, fun σ c => c = q.c0 ∧ Flow.Reserve.Fr q.g (s2 q.g (ntA lab) q.n) σ⟩
  | .ok => ⟨lab okL, oI, fun σ c => c = q.c0 ∧ Flow.Reserve.Fr q.g (s2 q.g (ntA lab) q.n) σ⟩

/-- **The exit**: at the return address, `Post`. -/
def rvX : Unit → ND
  | () => ⟨Int64.ofBitVec q.g.ra, Flow.Reserve.oR, fun σ c => c = q.c0 ∧ Flow.Reserve.Post q.g q.n σ⟩

/-- `Post`'s `%rax` is the new thread's id `n + 1`. -/
theorem post_rax {g : G} {n : BitVec 64} {σ : AS} (hP : Flow.Reserve.Post g n σ) :
    σ.regs.rax.toBitVec = n + 1#64 := hP.2.2

end Nodes

/-- **The counter's add** `lock xadd` on `scc_rt_nthreads`: the word holds
`n` at the add (`own`) and runtime memory may hold `n + 1` there (`next`). -/
structure ResOk (ms : MemSide isa) (F : MachineData → Prop) (exe : _root_.Executable) (endPc : Int64)
    (n : BitVec 64) : Prop where
  next : StOk ms F (ntA (_root_.Executable.labels exe).label) (n + 1#64)
  own : OwnAt ms exe endPc (rmwPc (_root_.Executable.labels exe).label) (ntA (_root_.Executable.labels exe).label) n

theorem ResOk.mono {ms : MemSide isa} {F F' : MachineData → Prop} {exe : _root_.Executable} {endPc : Int64}
    {n : BitVec 64} (h : ResOk ms F exe endPc n) (hFF : ∀ m, F' m → F m) : ResOk ms F' exe endPc n :=
  ⟨h.next.mono hFF, h.own⟩

/-- **The node obligations inside `W`**: the block nodes' states (`BlkW`)
and the single instructions' (`NodeW`). -/
def ReserveW (W : Frag isa) (K : State → State → Prop) (exe : _root_.Executable) (endPc : Int64) (R : Region)
    (F : MachineData → Prop) (q : ResG) : RN → Prop
  | .e => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .e) rPro
  | .entry => NodeW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .entry)
  | .arg => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .arg) rArg
  | .rmw => NodeW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .rmw)
  | .bnd => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .bnd) rBnd
  | .j => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .j) rJ
  | .ok => BlkW W K exe endPc R F (rvN (_root_.Executable.labels exe).label q .ok) rRet

/-! ## The callee segment -/

section SegProof

variable {p : Prog} {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa}
  {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {cells : List (Directive × Nat)}
  {R : Region} {F F0 : MachineData → Prop}

set_option hygiene false in
/-- A block node of `scc_rt_thread_reserve` inside `W`: the block, its
`okBlk`, its code, its obligation; the edge is left. -/
local macro "rnodeW " b:ident ok:ident hb:term:max w:term:max : tactic =>
  `(tactic| refine seg_ndW (by simp [$b:ident]) $ok hF hR hlo hhi
    (code_field hp hend $hb (by first | rfl | exact ofNat_zero' _)) $w fun σ c hJ => ⟨c, .refl c, ?_⟩)

/-- **`scc_rt_thread_reserve` is one segment inside `W`**: in any valid
layout of any cells with its code (`hin`), from its entry to its return,
for any region holding its frame of 32, the saved `%rbp` and the return
address, and any frame condition implying `F0`, given the bound's room
(`hn`) and the counter's add's facts (`hres`). -/
theorem reserve_segW {W : Frag isa} {K : State → State → Prop} {kp : Nat}
    (hp : Lays exe cells kp) (hend : endPc = endOf exe cells kp) (hin : reserveIn cells = true)
    (hF : FStable R F) (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi)
    (hFF : ∀ m, F m → F0 m) (q : ResG) (hn : q.n.toNat + 1 ≤ 1023)
    (hres : ResOk ms F0 exe endPc q.n) (hW : ∀ i, ReserveW W K exe endPc R F q i) :
    SegW W K p lbl ms (At exe endPc R F (rvN (_root_.Executable.labels exe).label q .e))
      (fun s c => ∃ x, At exe endPc R F (rvX q x) s c) := by
  have h := hin
  simp only [reserveIn, siAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hg, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have eEntry := label_labelGapB hp hg
  refine fn_segW (N := rvN _ q) (E := rvX q) (fun i => ?_) RN.e
  cases i
  case e =>
    rnodeW rPro rPro_ok bE (hW RN.e)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rPro_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨RN.entry, by rw [h1]; exact eEntry, by rw [h2]; rfl, rfl, h3⟩
  case entry =>
    refine si_ndW (si := .leaRip .rax "scc_rt_nthreads") (z := 7) rfl hF
      (code_field hp hend bA (ofNat_zero' _)) (hW RN.entry)
      fun σ c hJ => ⟨c, .refl c, .inl ⟨RN.arg, rfl, rfl, ?_⟩⟩
    obtain ⟨rfl, hJ⟩ := hJ
    exact ⟨rfl, si_fr _ _ hJ, si_rax _ _ σ⟩
  case arg =>
    rnodeW rArg rArg_ok bArg (hW RN.arg)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3, h4, h5⟩ := rArg_walk (_root_.Executable.labels exe).label _ hJ ha
    exact .inl ⟨RN.rmw, by rw [h1]; exact ofNat_add' _ 7 15, by rw [h2]; rfl, rfl, h3, h4, h5⟩
  case rmw =>
    refine ownXadd_ndW (b := .rcx) (k := 0) (r := .rax) (z := 5) (by decide) hF
      (code_field hp hend bRmw rfl) hres.own (hW RN.rmw) fun m σ c _ hD hJ => ?_
    dsimp only [rvN] at hJ ⊢
    obtain ⟨rfl, hJ, ha, hc⟩ := hJ
    have hb : bAddr σ.regs .rcx 0 = ntA (_root_.Executable.labels exe).label := by
      rw [← hc]; simp [bAddr, Reg64s.get64]
    have hv : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
    rw [hb, hv]
    exact ⟨rfl, hres.next.rt, hres.next.mp, hres.next.G, hres.next.unmapped m (hFF m hD),
      q.c0, .refl q.c0, fun fl =>
        .inl ⟨RN.bnd, ofNat_add' _ 22 5, rfl, rfl, by simpa [ownStep, Flow.Reserve.Fr, Reg64s.set64] using hJ,
          by simp [ownStep, Reg64s.set64]⟩⟩
  case bnd =>
    rnodeW rBnd rBnd_ok bBnd (hW RN.bnd)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ, ha⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rBnd_walk (_root_.Executable.labels exe).label _ hJ ha hn
    exact .inl ⟨RN.j, by rw [h1]; exact ofNat_add' _ 27 38, by rw [h2]; rfl, rfl, h3⟩
  case j =>
    rnodeW rJ rJ_ok bJ (hW RN.j)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rJ_walk (_root_.Executable.labels exe).label _ hJ
    exact .inl ⟨RN.ok, h1.symm, by rw [h2]; rfl, rfl, h3⟩
  case ok =>
    rnodeW rRet rRet_ok bOk (hW RN.ok)
    dsimp only [rvN, rvX] at hJ ⊢
    obtain ⟨rfl, hJ⟩ := hJ
    obtain ⟨h1, h2, h3⟩ := rRet_walk (_root_.Executable.labels exe).label _ hJ
    exact .inr ⟨(), h1.symm, by rw [h2]; rfl, rfl, h3⟩

end SegProof

/-! ## The node obligations from the phase facts -/

/-- The pcs of the single instructions without an event: the `leaq`'s. -/
def siPcs (lab : Label → Int64) : List Int64 := [lab entryL + Int64.ofNat 0]

/-- The nodes' pcs and the pc after the counter's add. -/
def resPcs (lab : Label → Int64) : List Int64 :=
  [lab fnL + Int64.ofNat 0, lab entryL + Int64.ofNat 7, rmwPc lab, rmwPc lab + Int64.ofNat 5,
    lab entryL + Int64.ofNat 27, lab entryL + Int64.ofNat 65, lab okL + Int64.ofNat 0] ++ siPcs lab

/-- **`scc_rt_thread_reserve`'s phase facts** at labels `lab`, phase index
`ph`, off-site pcs `okPc`, owned words by phase `ownOf`, returning to `ra`:
each block's phase check with no dead target (the bound's abort in the
phase too, as A13's table checks it), the `leaq` off the sites in its next
pc's phase, no node in the take's phase, the counter owned at its add and
updated by `+ 1`. -/
structure ResPh (okPc : Nat → Bool) (ph : Nat → Nat) (Tk : State → Prop) (ownOf : Nat → List (Loc × Val))
    (lab : Label → Int64) (ra : Int64) : Prop where
  e : blkPh okPc ph (fun _ => false) lab (lab fnL + Int64.ofNat 0) ra rPro = true
  arg : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 7) ra rArg = true
  bnd : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 27) ra rBnd = true
  j : blkPh okPc ph (fun _ => false) lab (lab entryL + Int64.ofNat 65) ra rJ = true
  ok : blkPh okPc ph (fun _ => false) lab (lab okL + Int64.ofNat 0) ra rRet = true
  si : ∀ p ∈ siPcs lab, okPc p.toBitVec.toNat = true ∧ ph (p + Int64.ofNat 7).toBitVec.toNat = ph p.toBitVec.toNat
  rmwOk : okPc (rmwPc lab).toBitVec.toNat = true
  noTk : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s
  rmwIn : ∃ v, (⟨ntA lab, 8⟩, v) ∈ ownOf (ph (rmwPc lab).toBitVec.toNat)
  rmwUpd : ownUpdB (ownOf (ph (rmwPc lab).toBitVec.toNat)) (ownOf (ph (rmwPc lab + Int64.ofNat 5).toBitVec.toNat))
    ⟨ntA lab, 8⟩ (fun old => (old.setWidth 64 + 1#64).setWidth 128) = true

theorem rPro_noRet : noRetBlk rPro = true := by rfl
theorem rArg_noRet : noRetBlk rArg = true := by rfl
theorem rBnd_noRet : noRetBlk rBnd = true := by rfl
theorem rJ_noRet : noRetBlk rJ = true := by rfl

/-- **`scc_rt_thread_reserve`'s states are inside `SFacts`**, for any
cells with its code (`hin`), in any region holding its frame, with the
source control `c0` (`hC0`), returning to `ra` (`hra`), its phase facts
(`hph`) and its counter mapped (`hmN`) and unmapped in private memory under
the frame condition (`hunN`). -/
theorem reserveW_gen {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
    {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
    {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {Λ : Scc.Sem.Layout} {rS : Range} {lbl : Lbl}
    {ownOf : Nat → List (Loc × Val)} {ra : Int64} {c0 : Ctl} {F : MachineData → Prop}
    {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) (hown : ∀ s, own s = ownOf (ph (pcOf s)))
    (hin : reserveIn cells = true) (hC0 : CFacts Λ lbl c0)
    {R : Region} (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 8 ≤ R.hi) (q : ResG)
    (hq : q.c0 = c0) (hra : q.g.ra = ra.toBitVec) (hph : ResPh okPc ph Tk ownOf lab ra)
    (hmN : Scc.Sem.Kernel.mapped (K0 Λ) true ⟨ntA lab, 8⟩ = true)
    (hunN : ∀ m, F m → Mem.loadInt m.dmem (ntA lab) 8 = none) :
    ∀ i, ReserveW (fun s c => SFacts Λ μ own rS Tk lbl s c) K exe endPc R F q i := by
  have h := hin
  simp only [reserveIn, siAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨-, bE⟩, bA⟩, bArg⟩, bRmw⟩, bBnd⟩, bJ⟩, bOk⟩ := h
  have hC : ∀ (n : ND), (∀ σ c, n.J σ c → c = q.c0) → ∀ σ c, n.J σ c → CFacts Λ lbl c :=
    fun _ hn σ c hJ => (hn σ c hJ).trans hq ▸ hC0
  have hT : ∀ p ∈ resPcs lab, ∀ s : State, pcOf s = p.toBitVec.toNat → ¬ Tk s := hph.noTk
  have hnr : ∀ {blk : List (Directive × Nat)}, noRetBlk blk = true → ∀ {n : ND} {ra' : Int64}, ∀ σ c, n.J σ c →
      ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra' :=
    fun hb _ _ _ _ _ k hk hr => (noRet_false hb k hk hr).elim
  intro i
  cases i
  case e =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bE (ofNat_zero' _) rPro_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.e
      (hnr rPro_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case entry =>
    dsimp only [ReserveW]; rw [hI.labOk]
    have := hph.si (lab entryL + Int64.ofNat 0) (by simp [siPcs])
    exact nodeW_si_pre hI bA rfl (ofNat_zero' _).symm (hC _ fun _ _ hJ => hJ.1) this.1
      (hT _ (by simp [resPcs, siPcs])) this.2
  case arg =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bArg rfl rArg_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.arg
      (hnr rArg_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case rmw =>
    dsimp only [ReserveW]; rw [hI.labOk]
    refine nodeW_xadd_pre (p := rmwPc lab) hI hown bRmw rfl rfl (hC _ fun _ _ hJ => hJ.1) hph.rmwOk
      (hT _ (by simp [resPcs])) (hT _ (by simp [resPcs])) (fun σ _ hJ => ?_) hmN hunN hph.rmwIn
      fun σ _ hJ => ?_
    · obtain ⟨-, -, -, hc⟩ := hJ
      rw [← hc]
      simp [bAddr, Reg64s.get64]
    · obtain ⟨-, -, ha, -⟩ := hJ
      have he : σ.regs.get64 .rax = 1#64 := by rw [← ha]; rfl
      rw [he]
      exact hph.rmwUpd
  case bnd =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bBnd rfl rBnd_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.bnd
      (hnr rBnd_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case j =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bJ rfl rJ_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.j
      (hnr rJ_noRet) (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))
  case ok =>
    dsimp only [ReserveW]; rw [hI.labOk]
    exact blkW_pre hI bOk (ofNat_zero' _) rRet_ok hR (by omega) (by omega) (hC _ fun _ _ hJ => hJ.1) hph.ok
      (hret_of_run rRet_ok fun _ _ hJ => by
        dsimp only [rvN] at hJ ⊢
        rw [(rRet_walk lab _ hJ.2).1, hra]; exact Int64.ofBitVec_toBitVec _)
      (fun _ _ _ => rfl) (hT _ (by simp [resPcs]))

/-! ## The code check from A13's groups -/

/-- **`reserveIn` from A13's groups** (`reserveGrps`, its blocks the hand ones). -/
theorem reserveIn_of {cells : List (Directive × Nat)} (h : RtAll cells Scc.Cert.Spawn.X64.reserveGrps) :
    reserveIn cells = true := by
  have e : Scc.Cert.Spawn.X64.reserveGrps = [
      ⟨fnL, [(0, rPro)], some (8, entryL)⟩,
      ⟨entryL, [(0, [((SI.leaRip .rax "scc_rt_nthreads").toDir, 7)]), (7, rArg), (22, rmwBlk), (27, rBnd),
        (65, rJ)], none⟩,
      ⟨fullL, [(0, (parse("movq $5, %rdi
call scc_rt_abort")).zip [7, 5])], none⟩,
      ⟨okL, [(0, rRet)], none⟩] := rfl
  rw [e] at h
  simp only [RtAll, BsOk, GapAt, and_true] at h
  simp only [reserveIn, siAt, h, Bool.and_self]

/-- **`reserveIn` from A13's code part** (`spawnGrps` in the cells). -/
theorem reserveIn_of_a13code {lo : Nat} {cells : List (Directive × Nat)} {Λ : Scc.Sem.Layout}
    (h : Scc.Cert.Spawn.X64.a13code lo cells Λ = true) : reserveIn cells = true := by
  simp only [Scc.Cert.Spawn.X64.a13code, Bool.and_eq_true] at h
  have := rtIn_sound h.1
  unfold Scc.Cert.Spawn.X64.spawnGrps at this
  exact reserveIn_of (RtAll.append (RtAll.append this).1).1

end Spike.Lib.X64.Rt.Reserve

/-- info: 'Spike.Lib.X64.Rt.Reserve.post_rax' does not depend on any axioms -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.post_rax

/-- info: 'Spike.Lib.X64.Rt.Reserve.ResOk.mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.ResOk.mono

/-- info: 'Spike.Lib.X64.Rt.Reserve.reserve_segW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.reserve_segW

/-- info: 'Spike.Lib.X64.Rt.Reserve.rPro_noRet' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.rPro_noRet

/-- info: 'Spike.Lib.X64.Rt.Reserve.rArg_noRet' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.rArg_noRet

/-- info: 'Spike.Lib.X64.Rt.Reserve.rBnd_noRet' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.rBnd_noRet

/-- info: 'Spike.Lib.X64.Rt.Reserve.rJ_noRet' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.rJ_noRet

/-- info: 'Spike.Lib.X64.Rt.Reserve.reserveW_gen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.reserveW_gen

/-- info: 'Spike.Lib.X64.Rt.Reserve.reserveIn_of' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.reserveIn_of

/-- info: 'Spike.Lib.X64.Rt.Reserve.reserveIn_of_a13code' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.Rt.Reserve.reserveIn_of_a13code
