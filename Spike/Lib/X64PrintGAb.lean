/-
**`scc_rt_print`'s block states keep the write abort's phase at any
instance** (x86-64): `PrintAW` (`Spike/Lib/X64PrintA.lean`) inside
`AbSt μ (WriteAb.Ab lab)`, none moved, for any executable with `InstOk`,
its cells holding the routine's and the abort's code (`printIn`,
`abortIn`), passing the phase check `printPhOk`, the length below `2^63`:
the twin of `Spike/Lib/A64PrintGAb.lean`, name for name. `print`'s tests of
the stored result are themselves in the phase (`WriteAb.tailPcs`), exactly
when the stored result `-24(%rbp)` refuses the stored length `-16(%rbp)`:
the phase is kept there by the data, and the jump to `.fail` is taken only
at a refusal. No pc table: the pcs are told apart by their positions, a
label and a byte offset (`pc_ne_of_inRunB`).

- `blkW_abStN`, `blkW_abN`: `blkW_abSt`, `AllocG.blkW_abG` with the state's
  own phase: every next state out of `Ab` when the state is.
- `tailPos`, `ntPos`, `tailPcs_eq`, `ntPcs_eq`: the tests' and the other
  pcs of the phase as positions.
- `notAbPc_of_pos`, `notAb_of_pos`: a position off `abPos` is off `abPcs`,
  off the phase.
- `refusal_of_ab`, `ab_of_refusal`: at a test's position the phase is the
  stored result's refusal of the stored length.
- `bpLoad2_of_abs`: the stored length and result are the frame's cells
  `-16`, `-24` (`%rbp` at `0`).
- `tail_keep`, `tail_ret`: a test's step keeping the stored data, the store
  of the result, keep the phase out.
- `tgtL`, `posOf`, `posTgts`, `wfChk`, `extPos`, `offChk`, `tgt_pos`: a
  block's targets by position, decided on the concrete block.
- `blkW_abOff`: a block whose targets are off the phase.
- `soRun`, `arun_so`, `keepChk`, `blkW_abKeep`: a block of the tests, but
  for listed instructions (the store of the result, the `jle .fail`).
- `inRunB_at`, `inRun0`, `x9h`, `x9_take`, `printAb`.

Where x86-64 differs from AArch64: positions are byte offsets
(`cellOff`), the stored data is read at `%rbp` (static offset `0`), not at
`%sp`, and the system call is not a block node (its block `x4` falls
through to the call's position `.write + 20`, off the phase).
-/
import Spike.Lib.X64PrintGSvc
import Spike.Lib.X64AllocGAb
import Spike.Lib.LowerX64.PlacedBlk

namespace Spike.Lib.X64.PrintG

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer
open Spike.Lib.X64 (NodeW BlkW ND AS AI AM SO Abs cellOff okBlk arun dstep classify cellOff_succ)
open Spike.Lib.X64.Rt (InstOk codeOf)
open Scc.Cert.Rt.X64 (blockAt blockAtB InRunB pc_ne_of_inRunB inRunB_of_blockAt blockAt_of_blockAtB Lays
  label_labelGapB)
open Spike.Lib.X64ConsumerA (AbSt)
open Spike.Lib.X64.WriteAb (Ab abPcs bpLoad)
open Spike.Lib.LowerX64 (abPos abPcs_eq abPos_inRunB)

/-! ## A block keeping the phase from its states' -/

section Gen

/-- **A covered block's states keep the abort phase** (`blkW_abSt`), every
instruction's next state, at the abstract run's next pc and registers, out
of `Ab` when the state at the instruction is (`htgt`). -/
theorem blkW_abStN {μ : Marks} {Ab : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List (Directive × Nat)} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff blk k) → PcOff μ s)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (cellOff blk k) →
      Abs R (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ → ¬ Ab s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
        (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab s') :
    BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  have hP := hpc k hk { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } he hn rfl
  obtain ⟨a, hca, haok, -⟩ :=
    Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.X64.classify_sound hca
  have hd : blk[k]? = some (a.toDir, blk[k].2) := by rw [List.getElem?_eq_getElem hk, ← hdir]
  have hc : Kraken.Promising.Lower.X64.CellAt { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) }
      a.toDir blk[k].2 :=
    (hcode s he hn).cell hd rfl rfl rfl
  have hl : Kraken.Promising.Lower.X64.labelAddr { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } =
      (_root_.Executable.labels exe).label := by
    funext L; show (_root_.Executable.labels s.exe).label L = _; rw [he]
  obtain ⟨m', hex, hA'', -⟩ := Spike.Lib.X64.exec_ai haok hR hlo hhi hc hreg hA'
  rw [hl] at hex
  have hsys : abi.atSys { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } = false :=
    atSyscall_false_of_cellAt hc (Spike.Lib.X64Consumer.AI.not_syscall hreg)
  refine ⟨fun hnab _ t ht => ?_, fun _ h => (by rw [hsys] at h; cases h),
    fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩
  rw [hex] at ht
  cases ht
  exact htgt σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (cellOff blk k)) } he hn rfl hA' hnab _ he hn
    rfl hA''

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block keeps the write abort's phase**, as
`AllocG.blkW_abG`, every instruction's next state out of `Ab` when the
state at the instruction is (`htgt`, `blkW_abStN`'s at the labels `lab`). -/
theorem blkW_abN {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp) {n : ND}
    {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {off : Nat}
    (hb : blockAtB cells l off blk = true) (he : lab l + Int64.ofNat off = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat off) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, classify blk[k].1 = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (cellOff blk k) →
      Abs R (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1 (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Ab lab s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt lab (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  have hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.X64.CodeAt s n.pc blk := fun s hs hn =>
    he ▸ codeOf hI hb hs hn
  rw [← hI.labOk] at hph hret hdead htgt ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  exact blkW_abStN hcode hok hR hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) htgt

end Gen

/-! ## The phase by position -/

section Pos

open Spike.Lib.X64.WriteAb (pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)

/-- `print`'s tests of the stored result (`WriteAb.tailPcs`) as positions. -/
def tailPos : List (Label × Nat) :=
  [(".Lscc_rt_print.write", 26), (".Lscc_rt_print.write", 30), (".Lscc_rt_print.write", 37),
   (".Lscc_rt_print.write", 40), (".Lscc_rt_print.write", 42),
   (".Lscc_rt_print.chk2", 0), (".Lscc_rt_print.chk2", 4), (".Lscc_rt_print.chk2", 11),
   (".Lscc_rt_print.chk2", 14), (".Lscc_rt_print.chk2", 16),
   (".Lscc_rt_print.chk3", 0), (".Lscc_rt_print.chk3", 4), (".Lscc_rt_print.chk3", 11),
   (".Lscc_rt_print.chk3", 14)]

/-- The write abort's other positions (`abPos` but `tailPos`). -/
def ntPos : List (Label × Nat) :=
  [(".Lscc_rt_print.write", 22)] ++ abPos.drop 15

theorem ntPos_sub : ntPos.all (fun p => abPos.contains p && !tailPos.contains p) = true := by decide

/-- **The tests' pcs are `tailPos`'s positions' addresses.** -/
theorem tailPcs_eq (lab : Label → Int64) : tailPcs lab = tailPos.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [tailPcs, tailPos, List.map_cons, List.map_nil, show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

/-- **The write abort's other pcs are `ntPos`'s positions' addresses.** -/
theorem ntPcs_eq (lab : Label → Int64) :
    pcRet lab :: failPcs lab ++ dispEPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab =
      ntPos.map fun p => lab p.1 + Int64.ofNat p.2 := by
  simp only [ntPos, abPos, List.drop_succ_cons, List.drop_zero, pcRet, failPcs, dispEPcs, dispTPcs, g4Pcs,
    stubPcs, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    show Int64.ofNat 0 = 0 by decide, Int64.add_zero]
  rfl

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}

/-- **A position off the write abort's is off its pcs**, in a layout of
cells with the runtime's code. -/
theorem notAbPc_of_pos (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {L : Label} {j : Nat} (hr : InRunB cells L j)
    (hn : abPos.contains (L, j) = false) {t : Int64}
    (ht : t = (_root_.Executable.labels exe).label L + Int64.ofNat j) :
    t ∉ abPcs (_root_.Executable.labels exe).label := by
  rw [ht, abPcs_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  refine pc_ne_of_inRunB hp (abPos_inRunB hpr hab p hp') hr ?_ he
  intro h
  rw [← h] at hn
  simp [hp'] at hn

/-- **A state at a position off the write abort's is off its phase.** -/
theorem notAb_of_pos (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {L : Label} {j : Nat} (hr : InRunB cells L j)
    (hn : abPos.contains (L, j) = false) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels exe).label L + Int64.ofNat j) :
    ¬ Ab (_root_.Executable.labels exe).label s :=
  Spike.Lib.X64.WriteAb.not_ab_of_pc (notAbPc_of_pos hp hpr hab hr hn hs)

/-- **At a test's position the phase is a refusal** of the stored length
`-16(%rbp)` by the stored result `-24(%rbp)`. -/
theorem refusal_of_ab (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) {L : Label} {j : Nat} (hr : InRunB cells L j)
    (ht : tailPos.contains (L, j) = true) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels exe).label L + Int64.ofNat j)
    (h : Ab (_root_.Executable.labels exe).label s) :
    ∃ l r, bpLoad s (-16) = some l ∧ bpLoad s (-24) = some r ∧ Refusal l.toNat r := by
  have hne : s.st.2 ∉ pcRet (_root_.Executable.labels exe).label ::
      failPcs (_root_.Executable.labels exe).label ++ dispEPcs (_root_.Executable.labels exe).label ++
      dispTPcs (_root_.Executable.labels exe).label ++ g4Pcs (_root_.Executable.labels exe).label ++
      stubPcs (_root_.Executable.labels exe).label := by
    rw [hs, ntPcs_eq, List.mem_map]
    rintro ⟨p, hp', he⟩
    have hc := List.all_eq_true.mp ntPos_sub p hp'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hc
    refine pc_ne_of_inRunB hp (abPos_inRunB hpr hab p (by simpa using hc.1)) hr ?_ he
    intro hq
    have hq' : p = (L, j) := hq
    rw [hq'] at hc
    rw [hc.2] at ht; cases ht
  rcases h with ⟨h, -⟩ | ⟨-, h⟩ | h | ⟨h, -⟩ | ⟨h, -⟩ | h | h
  · exact (hne (by simp [h])).elim
  · exact h
  all_goals exact (hne (by simp [h])).elim

/-- **At a test's pc a refusal is in the phase.** -/
theorem ab_of_refusal {lab : Label → Int64} {s : State} (hs : s.st.2 ∈ tailPcs lab) {l r : BitVec 64}
    (h16 : bpLoad s (-16) = some l) (h24 : bpLoad s (-24) = some r) (h : Refusal l.toNat r) : Ab lab s :=
  .inr (.inl ⟨hs, l, r, h16, h24, h⟩)

end Pos

/-! ## The stored length and result -/

/-- **The stored length and result are the frame's cells** `-16`, `-24`
(`%rbp` at `0`). -/
theorem bpLoad2_of_abs {R : Region} {o : SO} {s : State} {σ : AS}
    (hA : Abs R o s.st.1 σ) (ho : o.get .rbp = some 0) (hlo : R.lo ≤ -24) (hhi : -8 ≤ R.hi) :
    bpLoad s (-16) = some (σ.slot (-16)) ∧ bpLoad s (-24) = some (σ.slot (-24)) := by
  refine ⟨bpLoad_of_abs hA ho (by omega) hhi, ?_⟩
  have hbp : s.st.1.regs.get64 .rbp = R.addr 0 := by rw [hA.regs]; exact hA.so .rbp 0 ho
  obtain ⟨j, hj, ej⟩ := hA.slot (-24) ⟨by decide, by omega, by omega⟩
  have a24 : R.addr 0 + (-24 : BitVec 64) = R.addr (-24) := by
    rw [show (-24 : Int) = 0 + -24 by rfl, Region.addr_add]; rfl
  simp only [Reg64s.get64] at hbp
  simp only [bpLoad, privLoad, hbp, a24, hj, Option.map_some, ej]

/-! ## The phase kept along the tests -/

section Keep

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {cells : List (Directive × Nat)} {kp : Nat}
  {R : Region} {o0 o' : SO} {σ0 σ' : AS} {s0 s' : State}

/-- **A test's step keeps the phase out**: from a test's pc to a test's
position (`hq`), the stored length and result kept. -/
theorem tail_keep (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hlo : R.lo ≤ -24) (hhi : -8 ≤ R.hi)
    (h0 : s0.st.2 ∈ Spike.Lib.X64.WriteAb.tailPcs (_root_.Executable.labels exe).label)
    (hA0 : Abs R o0 s0.st.1 σ0) (ho0 : o0.get .rbp = some 0)
    (hn0 : ¬ Ab (_root_.Executable.labels exe).label s0)
    {q : Label × Nat} (hqr : InRunB cells q.1 q.2) (hqt : tailPos.contains q = true)
    (hs' : s'.st.2 = (_root_.Executable.labels exe).label q.1 + Int64.ofNat q.2)
    (hA' : Abs R o' s'.st.1 σ') (ho' : o'.get .rbp = some 0)
    (h16 : σ'.slot (-16) = σ0.slot (-16)) (h24 : σ'.slot (-24) = σ0.slot (-24)) :
    ¬ Ab (_root_.Executable.labels exe).label s' := by
  intro h
  obtain ⟨l, r, e1, e2, hr⟩ := refusal_of_ab hp hpr hab hqr hqt hs' h
  obtain ⟨f1, f2⟩ := bpLoad2_of_abs hA' ho' hlo hhi
  obtain ⟨g1, g2⟩ := bpLoad2_of_abs hA0 ho0 hlo hhi
  rw [f1, Option.some_inj, h16] at e1
  rw [f2, Option.some_inj, h24] at e2
  exact hn0 (ab_of_refusal h0 g1 g2 (e1 ▸ e2 ▸ hr))

/-- **The store of the result keeps the phase out**: from the pc after the
system call (`pcRet`), the result in `%rax`, to a test's position, the
result stored at `-24`. -/
theorem tail_ret (hp : Lays exe cells kp) (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true)
    (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true) (hlo : R.lo ≤ -24) (hhi : -8 ≤ R.hi)
    (h0 : s0.st.2 = Spike.Lib.X64.WriteAb.pcRet (_root_.Executable.labels exe).label)
    (hA0 : Abs R o0 s0.st.1 σ0) (ho0 : o0.get .rbp = some 0)
    (hn0 : ¬ Ab (_root_.Executable.labels exe).label s0)
    {q : Label × Nat} (hqr : InRunB cells q.1 q.2) (hqt : tailPos.contains q = true)
    (hs' : s'.st.2 = (_root_.Executable.labels exe).label q.1 + Int64.ofNat q.2)
    (hA' : Abs R o' s'.st.1 σ') (ho' : o'.get .rbp = some 0)
    (h16 : σ'.slot (-16) = σ0.slot (-16)) (h24 : σ'.slot (-24) = σ0.regs.get64 .rax) :
    ¬ Ab (_root_.Executable.labels exe).label s' := by
  intro h
  obtain ⟨l, r, e1, e2, hr⟩ := refusal_of_ab hp hpr hab hqr hqt hs' h
  obtain ⟨f1, f2⟩ := bpLoad2_of_abs hA' ho' hlo hhi
  obtain ⟨g1, -⟩ := bpLoad2_of_abs hA0 ho0 hlo hhi
  rw [f1, Option.some_inj, h16] at e1
  rw [f2, Option.some_inj, h24] at e2
  refine hn0 (.inl ⟨h0, l, e1 ▸ g1, ?_⟩)
  rw [hA0.regs, e2]
  exact hr

end Keep

/-! ## A block's targets by position -/

section Tgt

/-- An instruction's targets: a label's start (`some L`) or the next
instruction (`none`); none for a `ret`. -/
def tgtL : AI → List (Option Label)
  | .jmp L | .call L => [some L]
  | .jcc _ L => [some L, none]
  | .ret => []
  | _ => [none]

/-- A target's position, for the instruction `k` of a block at `(L, j0)`;
past the block, the position `nxt`. -/
def posOf (L : Label) (j0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) (k : Nat) :
    Option Label → Option (Label × Nat)
  | some L' => some (L', 0)
  | none => if k + 1 < blk.length then some (L, j0 + cellOff blk (k + 1)) else nxt

/-- The instruction `k`'s targets' positions. -/
def posTgts (L : Label) (j0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) (k : Nat) :
    List (Label × Nat) :=
  match blk[k]? with
  | some d => match classify d.1 with
    | some a => (tgtL a).filterMap (posOf L j0 blk nxt k)
    | none => []
  | none => []

/-- **Every instruction classified, every target with a position.** -/
def wfChk (L : Label) (j0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match classify d.1 with
      | some a => (tgtL a).all fun o => (posOf L j0 blk nxt k o).isSome
      | none => false
    | none => false

/-- The positions outside the block: `nxt` and the labels' starts. -/
def extPos (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : List (Label × Nat) :=
  nxt.toList ++ blk.flatMap fun d => match classify d.1 with
    | some a => (tgtL a).filterMap fun o => o.map fun L => (L, 0)
    | none => []

/-- **Every target's position is off the write abort's.** -/
def offChk (L : Label) (j0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k => (posTgts L j0 blk nxt k).all fun q => !abPos.contains q

/-- **An instruction's target is at one of its positions** (a `ret`'s
aside): in a block at `(L, j0)` of the cells, past it at `nxt` (`hnx`),
every position outside in the cells (`hIn`). -/
theorem tgt_pos {cells : List (Directive × Nat)} {lab : Label → Int64} {L : Label} {j0 : Nat}
    {blk : List (Directive × Nat)} {nxt : Option (Label × Nat)} (hb : blockAtB cells L j0 blk = true)
    (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (j0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2) {k : Nat} (hk : k < blk.length) {a : AI}
    (hca : classify blk[k].1 = some a) (o : SO) (σ : AS) :
    a = .ret ∨ ∃ q ∈ posTgts L j0 blk nxt k, InRunB cells q.1 q.2 ∧
      a.tgt lab o (lab L + Int64.ofNat j0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) σ =
        lab q.1 + Int64.ofNat q.2 := by
  obtain ⟨kb, hbk⟩ := blockAt_of_blockAtB hb
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hw := List.all_eq_true.mp hwf k (List.mem_range.mpr hk)
  simp only [hd, hca] at hw
  have hpt : posTgts L j0 blk nxt k = (tgtL a).filterMap (posOf L j0 blk nxt k) := by
    simp only [posTgts, hd, hca]
  have hext : ∀ L', some L' ∈ tgtL a → InRunB cells L' 0 := fun L' hL' =>
    hIn (L', 0) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨blk[k], List.getElem_mem hk, by
      rw [hca]; exact List.mem_filterMap.mpr ⟨some L', hL', rfl⟩⟩))
  -- the label case
  have hlab : ∀ L', some L' ∈ tgtL a → ∃ q ∈ posTgts L j0 blk nxt k, InRunB cells q.1 q.2 ∧
      lab L' = lab q.1 + Int64.ofNat q.2 := fun L' hL' =>
    ⟨(L', 0), by rw [hpt]; exact List.mem_filterMap.mpr ⟨some L', hL', rfl⟩, hext L' hL', by
      show lab L' = lab L' + Int64.ofNat 0; rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]⟩
  -- the fall-through case
  have hfall : none ∈ tgtL a → ∃ q ∈ posTgts L j0 blk nxt k, InRunB cells q.1 q.2 ∧
      lab L + Int64.ofNat j0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 =
        lab q.1 + Int64.ofNat q.2 := by
    intro hn
    have he : lab L + Int64.ofNat j0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2 =
        lab L + Int64.ofNat (j0 + cellOff blk (k + 1)) := by
      rw [cellOff_succ hk, Int64.ofNat_add, Int64.ofNat_add, Int64.add_assoc, Int64.add_assoc]
    by_cases hlt : k + 1 < blk.length
    · refine ⟨(L, j0 + cellOff blk (k + 1)), ?_, inRunB_of_blockAt hbk hlt, he⟩
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

/-! ## Blocks off the write abort -/

section Off

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A block whose every target is off the write abort keeps its phase**
(`AllocG.blkW_abG`): every target at a position off `abPos` (`offChk`,
`tgt_pos`), a `ret`'s return address `ra` off `abPcs`. -/
theorem blkW_abOff {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {L : Label}
    {j0 : Nat} {nxt : Option (Label × Nat)}
    (hb : blockAtB cells L j0 blk = true) (he : lab L + Int64.ofNat j0 = n.pc)
    (hok : okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab L + Int64.ofNat j0) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret →
      Int64.ofBitVec ((arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.slot (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so.sp)
        = ra)
    (hdead : ∀ σ c, n.J σ c → dead (arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (j0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2) (hoff : offChk L j0 blk nxt = true)
    (hraAb : ∀ k (hk : k < blk.length), classify blk[k].1 = some .ret → ra ∉ abPcs lab) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine Spike.Lib.X64.AllocG.blkW_abG hI hb he hok hR hlo hhi hph hret hdead
    fun σ c hJ k hk a hca s' _ _ hpc' _ => ?_
  replace hpc' : s'.st.2 = a.tgt lab (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (lab L + Int64.ofNat j0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
      (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ := by rw [hpc', he]
  rcases tgt_pos (lab := lab) hb hwf hnx hIn hk hca (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ with rfl | ⟨q, hq, hqr, hqe⟩
  · refine Spike.Lib.X64.WriteAb.not_ab_of_pc ?_
    rw [hpc']
    simp only [AI.tgt]
    rw [hret σ c hJ k hk hca]
    exact hraAb k hk hca
  · have hc := List.all_eq_true.mp (List.all_eq_true.mp hoff k (List.mem_range.mpr hk)) q hq
    rw [Bool.not_eq_true'] at hc
    rw [← hI.labOk] at hpc' hqe ⊢
    exact notAb_of_pos hI.lays hpr hab hqr hc (hpc'.trans hqe)

end Off

/-! ## Blocks of the tests -/

section KeepBlk

/-- The static offsets after sized cells (`arun`'s, `arun_so`). -/
def soRun (ds : List (Directive × Nat)) (o : SO) : SO :=
  ds.foldl (fun o d => match classify d.1 with | some a => a.so o | none => o) o

theorem arun_so (lab : Label → Int64) :
    ∀ (ds : List (Directive × Nat)) (am : AM), (arun lab ds am).so = soRun ds am.so
  | [], _ => rfl
  | (d, z) :: ds, am => by
    show (arun lab ds (dstep lab am (d, z))).so = soRun ds _
    rw [arun_so lab ds]
    simp only [dstep]
    cases classify d <;> rfl

/-- **Every instruction a test keeping the stored data** (but `exc`'s): at a
test's position, `%rbp` at `0` before and after, writing no slot, every
target off the write abort or a test. -/
def keepChk (L : Label) (j0 : Nat) (blk : List (Directive × Nat)) (nxt : Option (Label × Nat)) (exc : List Nat) :
    Bool :=
  (List.range blk.length).all fun k => exc.contains k ||
    (tailPos.contains (L, j0 + cellOff blk k) &&
      (soRun (blk.take k) Spike.Lib.X64.Print.oI).get .rbp == some 0 &&
      (match blk[k]? with
        | some d => match classify d.1 with
          | some a => !a.slotWr && (a.so (soRun (blk.take k) Spike.Lib.X64.Print.oI)).get .rbp == some 0
          | none => false
        | none => false) &&
      (posTgts L j0 blk nxt k).all fun q => !abPos.contains q || tailPos.contains q)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A block of the tests keeps the write abort's phase**: every
instruction but `exc`'s keeps the stored length and result (`keepChk`,
`tail_keep`), `exc`'s by `hexc`. -/
theorem blkW_abKeep {kp : Nat} (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {L : Label} {j0 : Nat} {nxt : Option (Label × Nat)}
    {exc : List Nat}
    (hb : blockAtB cells L j0 blk = true) (he : lab L + Int64.ofNat j0 = n.pc)
    (hno : n.o = Spike.Lib.X64.Print.oI) (hok : okBlk lo hi n.o blk = true)
    (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi) (hlo' : R.lo ≤ -24) (hhi' : -8 ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat j0) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (j0 + cellOff blk blk.length) = lab q.1 + Int64.ofNat q.2)
    (hIn : ∀ q ∈ extPos blk nxt, InRunB cells q.1 q.2) (hkc : keepChk L j0 blk nxt exc = true)
    (hexc : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), exc.contains k = true →
      ∀ a, classify blk[k].1 = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (cellOff blk k) →
      Abs R (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1 (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Ab lab s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt lab (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2) (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Abs R (a.so (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so (n.pc + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
          (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abN hI hb he hok hR hlo hhi hph
    (fun _ _ _ k hk hr => (noRet_false hnr k hk hr).elim) (fun _ _ _ => rfl)
    fun σ c hJ k hk a hca s0 h1 h2 hs0 hA0 hn0 s' h1' h2' hpc' hA' => ?_
  by_cases hx : exc.contains k = true
  · exact hexc σ c hJ k hk hx a hca s0 h1 h2 hs0 hA0 hn0 s' h1' h2' hpc' hA'
  have hc := List.all_eq_true.mp hkc k (List.mem_range.mpr hk)
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  simp only [hx, Bool.false_or, hd, hca, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨ht0, hsp0⟩, hsw, hsp'⟩, hq⟩ := hc
  replace hpc' : s'.st.2 = a.tgt lab (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (lab L + Int64.ofNat j0 + Int64.ofNat (cellOff blk k) + Int64.ofNat blk[k].2)
      (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ := by rw [hpc', he]
  have hso : (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so = soRun (blk.take k) Spike.Lib.X64.Print.oI := by
    rw [arun_so]; exact congrArg _ hno
  rcases tgt_pos (lab := lab) hb hwf hnx hIn hk hca (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
      (arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ with rfl | ⟨q, hqm, hqr, hqe⟩
  · exact (noRet_false hnr k hk hca).elim
  have hq' := List.all_eq_true.mp hq q hqm
  rw [← hI.labOk] at hpc' hqe he hn0 ⊢
  by_cases hqa : abPos.contains q = true
  · simp only [hqa, Bool.not_true, Bool.false_or] at hq'
    have h0 : s0.st.2 ∈ Spike.Lib.X64.WriteAb.tailPcs (_root_.Executable.labels exe).label := by
      rw [tailPcs_eq, List.mem_map]
      refine ⟨(L, j0 + cellOff blk k), List.contains_iff_mem.mp ht0, ?_⟩
      rw [hs0, ← he, Int64.ofNat_add, Int64.add_assoc]
    refine tail_keep hI.lays hpr hab hlo' hhi' h0 hA0 (by rw [hso]; exact hsp0) hn0 hqr hq' (hpc'.trans hqe) hA'
      (by rw [hso]; exact hsp') ?_ ?_
    · rw [AI.step_slot hsw]
    · rw [AI.step_slot hsw]
  · exact notAb_of_pos hI.lays hpr hab hqr (by simpa using hqa) (hpc'.trans hqe)

end KeepBlk

/-! ## `scc_rt_print`'s states -/

open Kraken.X64.Parser in
/-- `.chk3`'s block but its `jle`: the stored result compared with 0. -/
def x9h : List (Directive × Nat) := (parse("movq -24(%rbp), %rax
movq $0, %rcx
cmpq %rcx, %rax")).zip [4, 7, 3]

theorem x9_take : Spike.Lib.X64.Print.x9.take 3 = x9h := by decide

block_spec x9h (-40) 16 Spike.Lib.X64.Print.oI x9h

section Print

open Spike.Lib.X64.Print (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 oI
  x0_ok x1_ok x2_ok x3_ok x4_ok x5_ok x6_ok x7_ok x8_ok x9_ok x10_ok x11_ok x12_ok x13_ok x13_run)
open Spike.Lib.X64.PrintA (PrintAW N)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region}
  {F : MachineData → Prop} {rbp0 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- A cell of a block is in its label's run (`inRunB_of_blockAt` at a
block of the cells). -/
theorem inRunB_at {L : Label} {off j : Nat} {blk : List (Directive × Nat)} (h : blockAtB cells L off blk = true)
    {i : Nat} (hi : i < blk.length) (e : off + cellOff blk i = j) : InRunB cells L j := by
  obtain ⟨k, hk⟩ := blockAt_of_blockAtB h
  exact e ▸ inRunB_of_blockAt hk hi

/-- A block's start is in its label's run. -/
theorem inRun0 {L : Label} {off : Nat} {blk : List (Directive × Nat)} (h : blockAtB cells L off blk = true)
    (hl : 0 < blk.length) : InRunB cells L off :=
  inRunB_at h hl (by simp)

set_option hygiene false in
/-- A block of `scc_rt_print` off the write abort, no `ret`. -/
local macro "poff " hb:term:max ok:term:max hp:term:max nx:term:max hnx:term:max hin:term:max : tactic =>
  `(tactic| exact blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0) (nxt := $nx) $hb (by pc_tac) $ok hR
    (by omega) (by omega) $hp (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl)
    (by decide) $hnx $hin (by decide) (fun k hk hr => (noRet_false (by decide) k hk hr).elim))

set_option hygiene false in
/-- A block of `scc_rt_print`'s tests. -/
local macro "pkeep " hb:term:max ok:term:max hp:term:max nx:term:max ex:term:max hnx:term:max hin:term:max
    hx:term:max : tactic =>
  `(tactic| refine blkW_abKeep hI hpr hab (nxt := $nx) (exc := $ex) $hb (by pc_tac) rfl $ok hR
    (by omega) (by omega) (by omega) (by omega) $hp (by decide) (by decide) $hnx $hin (by decide) $hx)

/-- **`scc_rt_print`'s states keep the write abort's phase**, none moved,
its and the abort's code in the cells (`hpr`, `hab`) passing the phase
check (`hph`), the length below `2^63` (`hlen`: a positive count is then
no `jle`, a refused one a `Refusal` of the length), the return address in
the epilogue's phase (`hra`) and off the phase's pcs (`hraAb`), in a region
of the routine's frame. -/
theorem printAb (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.X64.Print.printIn cells = true) (hab : Scc.Cert.Rt.X64.Abort.abortIn cells = true)
    (hph : printPhOk okPc ph lab = true)
    (hR : R.OK) (hlo : R.lo ≤ -40) (hhi : 16 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hra : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".Lscc_rt_print.done").toBitVec.toNat)
    (hraAb : Int64.ofBitVec ra ∉ abPcs lab) :
    PrintAW rbp0 ra buf0 len0 P Q (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F := by
  have hl := hI.labOk
  subst hl
  obtain ⟨h0, h1, h2, h3, h4, h4s, h5, h6, h7, h8, h9, h10, h11, h12, h13, hg⟩ := printIn_spec hpr
  obtain ⟨p0, p1, p2, p3, p4, -, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14⟩ := printPhOk_spec hph
  have rE := inRun0 h1 (by decide)
  have rL := inRun0 h2 (by decide)
  have rL20 := inRun0 h3 (by decide)
  have rW := inRun0 h4 (by decide)
  have rW20 := inRun0 h4s (by decide)
  have rW42 := inRun0 h6 (by decide)
  have rC2 := inRun0 h7 (by decide)
  have rC216 := inRun0 h8 (by decide)
  have rC3 := inRun0 h9 (by decide)
  have rC316 := inRun0 h10 (by decide)
  have rA := inRun0 h11 (by decide)
  have rF := inRun0 h12 (by decide)
  have rD := inRun0 h13 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · poff h0 x0_ok p0 (some (".Lscc_rt_print.entry", 0))
      (fun q hq => by
        cases hq
        rw [label_labelGapB hI.lays hg, show 0 + cellOff x0 x0.length = 16 by decide,
          show Int64.ofNat (".Lscc_rt_print.entry", 0).snd = 0 from rfl, Int64.add_zero])
      (fun q hq => by
        rw [show extPos x0 (some (".Lscc_rt_print.entry", 0)) = [(".Lscc_rt_print.entry", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rE)
  · poff h1 x1_ok p1 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos x1 none = [(".Lscc_rt_print.loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rL)
  · poff h2 x2_ok p2 (some (".Lscc_rt_print.loop", 20)) (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos x2 (some (".Lscc_rt_print.loop", 20)) =
            [(".Lscc_rt_print.loop", 20), (".Lscc_rt_print.done", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
  · poff h3 x3_ok p3 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos x3 none = [(".Lscc_rt_print.write", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rW)
  · poff h4 x4_ok p4 (some (".Lscc_rt_print.write", 20)) (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos x4 (some (".Lscc_rt_print.write", 20)) = [(".Lscc_rt_print.write", 20)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rW20)
  · pkeep h5 x5_ok p5 (some (".Lscc_rt_print.write", 42)) [0] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos x5 (some (".Lscc_rt_print.write", 42)) =
            [(".Lscc_rt_print.write", 42), (".Lscc_rt_print.loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
      ?_
    intro σ c hJ k hk hx a hca s0 _ _ hs0 hA0 hn0 s' _ _ hpc' hA'
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hx
    subst hx
    simp [x5, classify] at hca
    subst hca
    refine tail_ret hI.lays hpr hab (by omega) (by omega) ?_ hA0 rfl hn0 (q := (".Lscc_rt_print.write", 26))
      (inRunB_at h5 (i := 1) (by decide) (by decide)) (by decide) ?_ hA' rfl ?_ ?_
    · rw [hs0, cellOff_zero, show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]; rfl
    · rw [hpc']; show _ + _ + _ = _; dsimp only [N]; simp only [Int64.add_assoc]; rfl
    · have hg : oI.get .rbp = some 0 := rfl
      simp [arun, AI.step, Spike.Lib.upd_apply, N, hg]
    · have hg : oI.get .rbp = some 0 := rfl
      simp [arun, AI.step, Spike.Lib.upd_apply, N, hg]
  · pkeep h6 x6_ok p6 none [] (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos x6 none = [(".Lscc_rt_print.chk2", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rC2)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h7 x7_ok p7 (some (".Lscc_rt_print.chk2", 16)) [] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos x7 (some (".Lscc_rt_print.chk2", 16)) =
            [(".Lscc_rt_print.chk2", 16), (".Lscc_rt_print.loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h8 x8_ok p8 none [] (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos x8 none = [(".Lscc_rt_print.chk3", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rC3)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h9 x9_ok p9 (some (".Lscc_rt_print.chk3", 16)) [3] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos x9 (some (".Lscc_rt_print.chk3", 16)) =
            [(".Lscc_rt_print.chk3", 16), (".Lscc_rt_print.fail", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
      ?_
    intro σ c hJ k hk hx a hca s0 _ _ hs0 hA0 hn0 s' _ _ hpc' hA'
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hx
    subst hx
    simp [x9, classify] at hca
    subst hca
    have hr3 : arun (_root_.Executable.labels exe).label (x9.take 3)
        ⟨(N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .chk3).pc,
          (N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .chk3).o, σ⟩ =
        arun (_root_.Executable.labels exe).label x9h
          ⟨(N (_root_.Executable.labels exe).label rbp0 ra buf0 len0 P Q .chk3).pc, oI, σ⟩ := by
      rw [x9_take]; rfl
    have c93 : cellOff x9 3 = 14 := by decide
    rw [hr3, x9h_run] at hA0 hpc'
    simp only [AI.tgt] at hpc'
    split at hpc'
    · rename_i hc
      exfalso
      refine hn0 (ab_of_refusal (l := σ.slot (-16)) (r := σ.slot (-24)) ?_ ?_ ?_ ?_)
      · rw [tailPcs_eq, hs0, c93]; exact List.mem_map.mpr ⟨(".Lscc_rt_print.chk3", 14), by decide, rfl⟩
      · exact (bpLoad2_of_abs hA0 rfl (by omega) (by omega)).1
      · exact (bpLoad2_of_abs hA0 rfl (by omega) (by omega)).2
      obtain ⟨k', ⟨-, -, -, h16, hk'⟩, hr⟩ := hJ
      have hc' : σ.slot (-24) = 0#64 ∨ (σ.slot (-24)).msb = true := by
        simp [CondCode.interp, StatusFlags.from_result] at hc
        rcases hc with h | h
        · exact .inr h
        · exact .inl h
      rw [h16, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rcases hr with ⟨h0', hle, -⟩ | ⟨hw, -⟩
      · exact absurd hc' (Spike.Lib.X64.PrintA.pos_not_le h0' (by omega))
      · exact Spike.Lib.X64.PrintAb.refusal_of_refused (by omega) hw
    · exact notAb_of_pos hI.lays hpr hab rC316 (by decide)
        (by rw [hpc', c93]; dsimp only [N]; simp only [Int64.add_assoc]; rfl)
  · poff h10 x10_ok p10 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos x10 none = [(".Lscc_rt_print.adv", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rA)
  · poff h11 x11_ok p11 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos x11 none = [(".Lscc_rt_print.loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rL)
  · refine blkW_abN hI h12 (by pc_tac) x12_ok hR (by omega) (by omega) p12 (dead := fun _ => false) (ra := 0)
      (fun _ _ _ k hk hr => (noRet_false (by decide) k hk hr).elim) (fun _ _ _ => rfl)
      fun σ c hJ k hk a hca s0 _ _ hs0 hA0 hn0 s' _ _ hpc' hA' => (hn0 (Spike.Lib.X64.WriteAb.ab_fail ?_)).elim
    have hk2 : k < 2 := by simpa [x12] using hk
    rw [hs0]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp [Spike.Lib.X64.WriteAb.failPcs, N]
    · simp only [Spike.Lib.X64.WriteAb.failPcs, List.mem_cons]; right; left; rfl
  · refine blkW_abOff hI hpr hab (dead := fun _ => false) (ra := Int64.ofBitVec ra) (nxt := none) h13 (by pc_tac)
      x13_ok hR (by omega) (by omega)
      (blkPh_x13 p13 (by simpa [Spike.Lib.X64.Flow.ofNat_zero'] using p14)
        (by simpa [Spike.Lib.X64.Flow.ofNat_zero'] using hra))
      (hret_of_run x13_ok fun σ c hJ => ?_) (fun _ _ _ => rfl) (by decide) (fun q hq => by cases hq)
      (fun q hq => by rw [show extPos x13 none = [] by decide] at hq; cases hq) (by decide)
      (fun _ _ _ => hraAb)
    obtain ⟨-, h8, -⟩ := hJ
    simp only [N]
    rw [x13_run, h8]

end Print

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64.PrintG.blkW_abOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abOff

/-- info: 'Spike.Lib.X64.PrintG.blkW_abKeep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abKeep

/-- info: 'Spike.Lib.X64.PrintG.printAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printAb

end Spike.Lib.X64.PrintG
