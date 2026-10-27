/-
**`scc_rt_print`'s block states keep the write abort's phase at any
instance** (AArch64): `PrintAW` (`Spike/Lib/A64PrintA.lean`) inside
`AbSt μ (WriteAb.Ab lab)`, none moved, for any executable with `InstOk`, its
program holding the routine's and the abort's code (`printIn`, `abortIn`),
passing the phase check `printPhOk`, the length below `2^63`. Unlike
`scc_rt_alloc`'s (`Spike/Lib/A64AllocGAb.lean`), `print`'s tests of the
stored result are themselves in the phase (`WriteAb.tailPcs`), exactly when
the stored result refuses the stored length: the phase is kept there by
the data, and the jump to `.6_fail` is taken only at a refusal. No pc
table: the pcs are told apart by their positions (`pc_ne_of_inRun`).

- `blkW_abStN`, `blkW_abN`: `blkW_abSt`, `AllocG.blkW_abG` with the state's
  own phase: every next state out of `Ab` when the state is.
- `tailPos`, `ntPos`, `tailPcs_eq`, `ntPcs_eq`: the tests' and the other
  pcs of the phase as positions.
- `notAbPc_of_pos`, `notAbC_of_pos`, `notAb_of_pos`: a position off `abPos`
  is off `abPcs`, off the phase.
- `refusal_of_ab`, `ab_of_refusal`: at a test's position the phase is the
  stored result's refusal of the stored length.
- `spLoad_of_abs`: the stored length and result, `[sp + 8]`, `[sp + 16]`,
  are the frame's cells `-40`, `-32`.
- `tail_keep`, `tail_ret`: a test's step keeping the stored data, the store
  of the result, keep the phase out.
- `tgtL`, `posOf`, `posTgts`, `wfChk`, `extPos`, `offChk`, `tgt_pos`: a
  block's targets by position, decided on the concrete block.
- `blkW_abOff`: a block whose targets are off the phase.
- `soRun`, `arun_so`, `keepChk`, `blkW_abKeep`: a block of the tests, but
  for listed instructions (the store of the result, the jump to
  `.6_fail`).
- `b11h`, `b11_take`, `inRun0`, `printAb`.
-/
import Spike.Lib.A64PrintG
import Spike.Lib.A64AllocGAb
import Spike.Lib.A64PrintAb
import Spike.Lib.LowerA64.AllocRa
import Spike.Lib.LowerA64.PlacedBlk

namespace Spike.Lib.A64.PrintG

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer
open Spike.Lib.A64.Flow (NodeW BlkW ND AS)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (blockAt InRun pc_ne_of_inRun inRun_of_blockAt Lays label_labelGap)
open Spike.Lib.A64ConsumerA (AbSt)
open Spike.Lib.A64.WriteAb (Ab abPcs spLoad)
open Spike.Lib.LowerA64 (abPos abPcs_eq abPos_inRun)

/-! ## A block keeping the phase from its states' -/

section Gen

/-- **A covered block's states keep the abort phase** (`blkW_abSt`), every
instruction's next state, at the abstract run's next pc and registers, out
of `Ab` when the state at the instruction is (`htgt`). -/
theorem blkW_abStN {μ : Marks} {Ab : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
    {F : MachineData → Prop} {n : ND} {blk : List Directive} {lo hi : Int}
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc blk)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hpc : ∀ k < blk.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * k) →
      PcOff μ s)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, Spike.Lib.A64.Flow.classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (4 * k) →
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ → ¬ Ab s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R
        (a.so (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab s') :
    BlkW (fun s _ => AbSt μ Ab s) (fun _ _ => False) exe endPc R F n blk := by
  intro s σ c he hn _ _ _ _ hJ k hk m hA' _
  refine ⟨?_, fun _ h => h⟩
  have hP := hpc k hk { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl
  obtain ⟨a, hca, haok, -⟩ :=
    Spike.Lib.A64.Flow.okBlk_get (_root_.Executable.labels exe).label (am := ⟨n.pc, n.o, σ⟩) hok hk
  obtain ⟨hdir, hreg⟩ := Spike.Lib.A64.Flow.classify_sound hca
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hc : Kraken.Promising.Lower.A64.CellAt { s with st := (m, n.pc + Int64.ofNat (4 * k)) } a.toDir 4 :=
    (hcode s he hn).cell (j := k) (hdir ▸ hd) rfl rfl rfl
  have hl : Spike.Lib.A64.Flow.labA { s with st := (m, n.pc + Int64.ofNat (4 * k)) } =
      (_root_.Executable.labels exe).label := by
    show (_root_.Executable.labels s.exe).label = _; rw [he]
  obtain ⟨m', hex, hA'', -⟩ := Spike.Lib.A64.Flow.exec_ai haok hR hal hlo hhi hc hreg hA'
  rw [hl] at hex
  have hsys : abi.atSys { s with st := (m, n.pc + Int64.ofNat (4 * k)) } = false :=
    Scc.Sem.A64.atSvc_false_of_cellAt hc (Spike.Lib.A64Consumer.AI.not_svc hreg)
  refine ⟨fun hnab _ t ht => ?_, fun _ h => (by rw [hsys] at h; cases h),
    fun _ a ha hpc' => (hP.noTake a ha hpc').elim⟩
  rw [hex] at ht
  cases ht
  exact htgt σ c hJ k hk a hca { s with st := (m, n.pc + Int64.ofNat (4 * k)) } he hn rfl hA' hnab _ he hn rfl
    hA''

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A covered block keeps the write abort's phase**, as
`AllocG.blkW_abG`, every instruction's next state out of `Ab` when the
state at the instruction is (`htgt`, `blkW_abStN`'s at the labels `lab`). -/
theorem blkW_abN {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp) {n : ND} {blk : List Directive}
    {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {l : Label} {k : Nat}
    (hb : blockAt prog l k blk = true) (he : lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab l + Int64.ofNat (4 * k)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[k] = some (Spike.Lib.A64.Flow.AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (htgt : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), ∀ a, Spike.Lib.A64.Flow.classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (4 * k) →
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Ab lab s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R (a.so (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
          (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  have hcode := Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb (q := n.pc) (by rw [hI.labOk]; exact he)
  rw [← hI.labOk] at hph hret hdead htgt ⊢
  obtain ⟨hpc, -, -⟩ := blkPh_sound (μ := μ) (endPc := endPc) hI.same hI.off hok hph hret hdead
  exact blkW_abStN hcode hok hR hal hlo hhi (fun k hk s h1 h2 h3 => (hpc k hk s h1 h2 h3).1) htgt

end Gen

/-! ## The phase by position -/

section Pos

open Spike.Lib.A64.WriteAb (pcRet tailPcs failPcs dispEPcs dispTPcs g4Pcs stubPcs)

/-- `print`'s tests of the stored result (`WriteAb.tailPcs`) as positions. -/
def tailPos : List (Label × Nat) :=
  ((List.range 8).map fun j => (".L9_scc_rt_print.2_write", j + 6)) ++
  ((List.range 8).map fun j => (".L9_scc_rt_print.3_chk2", j)) ++
  ((List.range 4).map fun j => (".L9_scc_rt_print.4_chk3", j))

/-- The write abort's other positions (`abPos` but `tailPos`). -/
def ntPos : List (Label × Nat) :=
  [(".L9_scc_rt_print.2_write", 5)] ++ abPos.drop 21

theorem ntPos_sub : ntPos.all (fun p => abPos.contains p && !tailPos.contains p) = true := by decide

/-- **The tests' pcs are `tailPos`'s positions' addresses.** -/
theorem tailPcs_eq (lab : Label → Int64) : tailPcs lab = tailPos.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [tailPcs, tailPos, Spike.Lib.A64.Print.pcSvc, List.range_succ, Int64.add_assoc]

/-- **The write abort's other pcs are `ntPos`'s positions' addresses.** -/
theorem ntPcs_eq (lab : Label → Int64) :
    pcRet lab :: failPcs lab ++ dispEPcs lab ++ dispTPcs lab ++ g4Pcs lab ++ stubPcs lab =
      ntPos.map fun p => lab p.1 + Int64.ofNat (4 * p.2) := by
  simp [ntPos, abPos, pcRet, failPcs, dispEPcs, dispTPcs, g4Pcs, stubPcs, Spike.Lib.A64.Print.pcSvc,
    List.range_succ, Int64.add_assoc]

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}

/-- **A position off the write abort's is off its pcs**, in a layout of a
program with the runtime's code. -/
theorem notAbPc_of_pos (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {L : Label} {j : Nat} (hr : InRun prog L j)
    (hn : abPos.contains (L, j) = false) {t : Int64}
    (ht : t = (_root_.Executable.labels exe).label L + Int64.ofNat (4 * j)) :
    t ∉ abPcs (_root_.Executable.labels exe).label := by
  rw [ht, abPcs_eq, List.mem_map]
  rintro ⟨p, hp', he⟩
  refine pc_ne_of_inRun hp (abPos_inRun hpr hab p hp') hr ?_ he
  intro h
  rw [← h] at hn
  simp [hp'] at hn

/-- `notAbPc_of_pos` as `blkAb`'s test. -/
theorem notAbC_of_pos (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {L : Label} {j : Nat} (hr : InRun prog L j)
    (hn : abPos.contains (L, j) = false) {t : Int64}
    (ht : t = (_root_.Executable.labels exe).label L + Int64.ofNat (4 * j)) :
    (abPcs (_root_.Executable.labels exe).label).contains t = false := by
  rw [Bool.eq_false_iff, Ne, List.contains_iff_mem]
  exact notAbPc_of_pos hp hpr hab hr hn ht

/-- **A state at a position off the write abort's is off its phase.** -/
theorem notAb_of_pos (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {L : Label} {j : Nat} (hr : InRun prog L j)
    (hn : abPos.contains (L, j) = false) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels exe).label L + Int64.ofNat (4 * j)) :
    ¬ Ab (_root_.Executable.labels exe).label s :=
  Spike.Lib.A64.WriteAb.not_ab_of_pc (notAbPc_of_pos hp hpr hab hr hn hs)

/-- **At a test's position the phase is a refusal** of the stored length
`[sp + 8]` by the stored result `[sp + 16]`. -/
theorem refusal_of_ab (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) {L : Label} {j : Nat} (hr : InRun prog L j)
    (ht : tailPos.contains (L, j) = true) {s : State}
    (hs : s.st.2 = (_root_.Executable.labels exe).label L + Int64.ofNat (4 * j))
    (h : Ab (_root_.Executable.labels exe).label s) :
    ∃ l r, spLoad s 8 = some l ∧ spLoad s 16 = some r ∧ Refusal l.toNat r := by
  have hne : s.st.2 ∉ pcRet (_root_.Executable.labels exe).label ::
      failPcs (_root_.Executable.labels exe).label ++ dispEPcs (_root_.Executable.labels exe).label ++
      dispTPcs (_root_.Executable.labels exe).label ++ g4Pcs (_root_.Executable.labels exe).label ++
      stubPcs (_root_.Executable.labels exe).label := by
    rw [hs, ntPcs_eq, List.mem_map]
    rintro ⟨p, hp', he⟩
    have hc := List.all_eq_true.mp ntPos_sub p hp'
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_iff_mem] at hc
    refine pc_ne_of_inRun hp (abPos_inRun hpr hab p (by simpa using hc.1)) hr ?_ he
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
    (h8 : spLoad s 8 = some l) (h16 : spLoad s 16 = some r) (h : Refusal l.toNat r) : Ab lab s :=
  .inr (.inl ⟨hs, l, r, h8, h16, h⟩)

end Pos

/-! ## The stored length and result -/

/-- **The stored length and result are the frame's cells** `-40`, `-32`
(`sp` at `-48`). -/
theorem spLoad_of_abs {R : Region} {o : Spike.Lib.A64.Flow.SO} {s : State} {σ : Spike.Lib.A64.Flow.AS}
    (hA : Spike.Lib.A64.Flow.Abs R o s.st.1 σ) (ho : o.sp = -48) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    spLoad s 8 = some (σ.slot (-40)) ∧ spLoad s 16 = some (σ.slot (-32)) := by
  have hsp : s.st.1.regs.SP.toBitVec = R.addr (-48) := by rw [hA.regs, ← ho]; exact hA.so.sp
  obtain ⟨j8, h8, e8⟩ := hA.slot (-40) ⟨by decide, by omega, by omega⟩
  obtain ⟨j16, h16, e16⟩ := hA.slot (-32) ⟨by decide, by omega, by omega⟩
  have a8 : R.addr (-48) + 8 = R.addr (-40) := by
    rw [show (-40 : Int) = -48 + 8 by rfl, Region.addr_add]; rfl
  have a16 : R.addr (-48) + 16 = R.addr (-32) := by
    rw [show (-32 : Int) = -48 + 16 by rfl, Region.addr_add]; rfl
  refine ⟨?_, ?_⟩
  · simp only [spLoad, privLoad, hsp, a8, h8, Option.map_some, e8]
  · simp only [spLoad, privLoad, hsp, a16, h16, Option.map_some, e16]

/-! ## The phase kept along the tests -/

section Keep

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {prog : List Directive} {kp : Nat}
  {R : Region} {o0 o' : Spike.Lib.A64.Flow.SO} {σ0 σ' : Spike.Lib.A64.Flow.AS} {s0 s' : State}

/-- **A test's step keeps the phase out**: from a test's pc to a test's
position (`hq`), the stored length and result kept. -/
theorem tail_keep (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (h0 : s0.st.2 ∈ Spike.Lib.A64.WriteAb.tailPcs (_root_.Executable.labels exe).label)
    (hA0 : Spike.Lib.A64.Flow.Abs R o0 s0.st.1 σ0) (ho0 : o0.sp = -48)
    (hn0 : ¬ Ab (_root_.Executable.labels exe).label s0)
    {q : Label × Nat} (hqr : InRun prog q.1 q.2) (hqt : tailPos.contains q = true)
    (hs' : s'.st.2 = (_root_.Executable.labels exe).label q.1 + Int64.ofNat (4 * q.2))
    (hA' : Spike.Lib.A64.Flow.Abs R o' s'.st.1 σ') (ho' : o'.sp = -48)
    (h40 : σ'.slot (-40) = σ0.slot (-40)) (h32 : σ'.slot (-32) = σ0.slot (-32)) :
    ¬ Ab (_root_.Executable.labels exe).label s' := by
  intro h
  obtain ⟨l, r, h8, h16, hr⟩ := refusal_of_ab hp hpr hab hqr hqt hs' h
  obtain ⟨e8, e16⟩ := spLoad_of_abs hA' ho' hlo hhi
  obtain ⟨f8, f16⟩ := spLoad_of_abs hA0 ho0 hlo hhi
  rw [e8, Option.some_inj, h40] at h8
  rw [e16, Option.some_inj, h32] at h16
  exact hn0 (ab_of_refusal h0 f8 f16 (h8 ▸ h16 ▸ hr))

/-- **The store of the result keeps the phase out**: from the pc after the
system call (`pcRet`), the result in `x0`, to a test's position, the result
stored at `-32`. -/
theorem tail_ret (hp : Lays exe prog kp) (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true)
    (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (h0 : s0.st.2 = Spike.Lib.A64.WriteAb.pcRet (_root_.Executable.labels exe).label)
    (hA0 : Spike.Lib.A64.Flow.Abs R o0 s0.st.1 σ0) (ho0 : o0.sp = -48)
    (hn0 : ¬ Ab (_root_.Executable.labels exe).label s0)
    {q : Label × Nat} (hqr : InRun prog q.1 q.2) (hqt : tailPos.contains q = true)
    (hs' : s'.st.2 = (_root_.Executable.labels exe).label q.1 + Int64.ofNat (4 * q.2))
    (hA' : Spike.Lib.A64.Flow.Abs R o' s'.st.1 σ') (ho' : o'.sp = -48)
    (h40 : σ'.slot (-40) = σ0.slot (-40)) (h32 : σ'.slot (-32) = σ0.regs.X0.toBitVec) :
    ¬ Ab (_root_.Executable.labels exe).label s' := by
  intro h
  obtain ⟨l, r, h8, h16, hr⟩ := refusal_of_ab hp hpr hab hqr hqt hs' h
  obtain ⟨e8, e16⟩ := spLoad_of_abs hA' ho' hlo hhi
  obtain ⟨f8, -⟩ := spLoad_of_abs hA0 ho0 hlo hhi
  rw [e8, Option.some_inj, h40] at h8
  rw [e16, Option.some_inj, h32] at h16
  refine hn0 (.inl ⟨h0, l, h8 ▸ f8, ?_⟩)
  rw [hA0.regs, h16]
  exact hr

end Keep

/-! ## A block's targets by position -/

section Tgt


/-- An instruction's targets: a label's start (`some L`) or the next
instruction (`none`); none for a `ret`. -/
def tgtL : Spike.Lib.A64.Flow.AI → List (Option Label)
  | .b L | .bl L => [some L]
  | .bcond _ L | .cbz _ L | .cbnz _ L => [some L, none]
  | .ret _ => []
  | _ => [none]

/-- A target's position, for the instruction `k` of a block of `len`
instructions at `(L, j0)`; past the block, the position `nxt`. -/
def posOf (L : Label) (j0 len : Nat) (nxt : Option (Label × Nat)) (k : Nat) : Option Label → Option (Label × Nat)
  | some L' => some (L', 0)
  | none => if k + 1 < len then some (L, j0 + k + 1) else nxt

/-- The instruction `k`'s targets' positions. -/
def posTgts (L : Label) (j0 : Nat) (blk : List Directive) (nxt : Option (Label × Nat)) (k : Nat) :
    List (Label × Nat) :=
  match blk[k]? with
  | some d => match Spike.Lib.A64.Flow.classify d with
    | some a => (tgtL a).filterMap (posOf L j0 blk.length nxt k)
    | none => []
  | none => []

/-- **Every instruction classified, every target with a position.** -/
def wfChk (L : Label) (j0 : Nat) (blk : List Directive) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k =>
    match blk[k]? with
    | some d => match Spike.Lib.A64.Flow.classify d with
      | some a => (tgtL a).all fun o => (posOf L j0 blk.length nxt k o).isSome
      | none => false
    | none => false

/-- The positions outside the block: `nxt` and the labels' starts. -/
def extPos (blk : List Directive) (nxt : Option (Label × Nat)) : List (Label × Nat) :=
  nxt.toList ++ blk.flatMap fun d => match Spike.Lib.A64.Flow.classify d with
    | some a => (tgtL a).filterMap fun o => o.map fun L => (L, 0)
    | none => []

/-- **Every target's position is off the write abort's.** -/
def offChk (L : Label) (j0 : Nat) (blk : List Directive) (nxt : Option (Label × Nat)) : Bool :=
  (List.range blk.length).all fun k => (posTgts L j0 blk nxt k).all fun q => !abPos.contains q

/-- The position after `k` instructions of a block at `(L, j)`. -/
theorem pos_succ (lab : Label → Int64) (L : Label) (j k : Nat) :
    lab L + Int64.ofNat (4 * j) + Int64.ofNat (4 * k) + Int64.ofNat 4 = lab L + Int64.ofNat (4 * (j + k + 1)) := by
  rw [Nat.mul_add, Nat.mul_add, Int64.ofNat_add, Int64.ofNat_add, Int64.add_assoc, Int64.add_assoc,
    Int64.add_assoc]

theorem ofNat4_add (a b : Nat) : Int64.ofNat (4 * (a + b)) = Int64.ofNat (4 * a) + Int64.ofNat (4 * b) := by
  rw [Nat.mul_add, Int64.ofNat_add]

/-- **An instruction's target is at one of its positions** (a `ret`'s
aside): in a block at `(L, j0)` of a program, past it at `nxt` (`hnx`),
every position outside in the program (`hIn`). -/
theorem tgt_pos {prog : List Directive} {lab : Label → Int64} {L : Label} {j0 : Nat} {blk : List Directive}
    {nxt : Option (Label × Nat)} (hb : blockAt prog L j0 blk = true) (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (4 * (j0 + blk.length)) = lab q.1 + Int64.ofNat (4 * q.2))
    (hIn : ∀ q ∈ extPos blk nxt, InRun prog q.1 q.2) {k : Nat} (hk : k < blk.length) {a : Spike.Lib.A64.Flow.AI}
    (hca : Spike.Lib.A64.Flow.classify blk[k] = some a) (σ : Spike.Lib.A64.Flow.AS) :
    (∃ r, a = .ret r) ∨ ∃ q ∈ posTgts L j0 blk nxt k, InRun prog q.1 q.2 ∧
      a.tgt lab (lab L + Int64.ofNat (4 * j0) + Int64.ofNat (4 * k) + Int64.ofNat 4) σ =
        lab q.1 + Int64.ofNat (4 * q.2) := by
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  have hw := List.all_eq_true.mp hwf k (List.mem_range.mpr hk)
  simp only [hd, hca] at hw
  have hpt : posTgts L j0 blk nxt k = (tgtL a).filterMap (posOf L j0 blk.length nxt k) := by
    simp only [posTgts, hd, hca]
  have hext : ∀ L', some L' ∈ tgtL a → InRun prog L' 0 := fun L' hL' =>
    hIn (L', 0) (List.mem_append_right _ (List.mem_flatMap.mpr ⟨blk[k], List.getElem_mem hk, by
      rw [hca]; exact List.mem_filterMap.mpr ⟨some L', hL', rfl⟩⟩))
  -- the label case
  have hlab : ∀ L', some L' ∈ tgtL a → ∃ q ∈ posTgts L j0 blk nxt k, InRun prog q.1 q.2 ∧
      lab L' = lab q.1 + Int64.ofNat (4 * q.2) := fun L' hL' =>
    ⟨(L', 0), by rw [hpt]; exact List.mem_filterMap.mpr ⟨some L', hL', rfl⟩, hext L' hL', by
      show lab L' = lab L' + Int64.ofNat 0; rw [show Int64.ofNat 0 = 0 from rfl, Int64.add_zero]⟩
  -- the fall-through case
  have hfall : none ∈ tgtL a → ∃ q ∈ posTgts L j0 blk nxt k, InRun prog q.1 q.2 ∧
      lab L + Int64.ofNat (4 * j0) + Int64.ofNat (4 * k) + Int64.ofNat 4 = lab q.1 + Int64.ofNat (4 * q.2) := by
    intro hn
    have he : lab L + Int64.ofNat (4 * j0) + Int64.ofNat (4 * k) + Int64.ofNat 4 =
        lab L + Int64.ofNat (4 * (j0 + k + 1)) := by
      rw [ofNat4_add, ofNat4_add, Int64.add_assoc, Int64.add_assoc, Int64.add_assoc]
    by_cases hlt : k + 1 < blk.length
    · refine ⟨(L, j0 + k + 1), ?_, ?_, he⟩
      · rw [hpt]; exact List.mem_filterMap.mpr ⟨none, hn, by simp [posOf, hlt]⟩
      · have := inRun_of_blockAt hb (i := k + 1) hlt
        rwa [← Nat.add_assoc] at this
    · have hs := List.all_eq_true.mp hw none hn
      simp only [posOf, hlt, ite_false] at hs
      obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp hs
      refine ⟨q, ?_, hIn q (List.mem_append_left _ (by simp [hq])), ?_⟩
      · rw [hpt]; exact List.mem_filterMap.mpr ⟨none, hn, by simp [posOf, hlt, hq]⟩
      · rw [he, ← hnx q hq]
        congr 3; omega
  cases a with
  | ret r => exact .inl ⟨r, rfl⟩
  | b L' => exact .inr (hlab L' (by simp [tgtL]))
  | bl L' => exact .inr (hlab L' (by simp [tgtL]))
  | bcond c L' =>
    refine .inr ?_
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    split
    · exact hlab L' (by simp [tgtL])
    · exact hfall (by simp [tgtL])
  | cbz t L' =>
    refine .inr ?_
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    split
    · exact hlab L' (by simp [tgtL])
    · exact hfall (by simp [tgtL])
  | cbnz t L' =>
    refine .inr ?_
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    split
    · exact hlab L' (by simp [tgtL])
    · exact hfall (by simp [tgtL])
  | ldr t n => exact .inr (hfall (by simp [tgtL]))
  | str t n => exact .inr (hfall (by simp [tgtL]))
  | reg w op => exact .inr (hfall (by simp [tgtL]))

end Tgt

/-! ## Blocks off the write abort -/

section Off

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A block whose every target is off the write abort keeps its phase**
(`AllocG.blkW_abG`): every target at a position off `abPos` (`offChk`,
`tgt_pos`), a `ret`'s return address `ra` off `abPcs`. -/
theorem blkW_abOff {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {dead : Nat → Bool} {ra : Int64} {L : Label} {j0 : Nat}
    {nxt : Option (Label × Nat)}
    (hb : blockAt prog L j0 blk = true) (he : lab L + Int64.ofNat (4 * j0) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph dead lab (lab L + Int64.ofNat (4 * j0)) ra blk = true)
    (hret : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[k] = some (Spike.Lib.A64.Flow.AI.ret r) →
      Int64.ofInt ((Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ.regs.getRegOrZr r).signed = ra)
    (hdead : ∀ σ c, n.J σ c → dead (Spike.Lib.A64.Flow.arun lab blk ⟨n.pc, n.o, σ⟩).pc.toBitVec.toNat = false)
    (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (4 * (j0 + blk.length)) = lab q.1 + Int64.ofNat (4 * q.2))
    (hIn : ∀ q ∈ extPos blk nxt, InRun prog q.1 q.2) (hoff : offChk L j0 blk nxt = true)
    (hraAb : ∀ k (hk : k < blk.length) r,
      Spike.Lib.A64.Flow.classify blk[k] = some (Spike.Lib.A64.Flow.AI.ret r) → ra ∉ abPcs lab) :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine Spike.Lib.A64.AllocG.blkW_abG hI hb he hok hR hal hlo hhi hph hret hdead
    fun σ c hJ k hk a hca s' _ _ hpc' _ => ?_
  replace hpc' : s'.st.2 = a.tgt lab (lab L + Int64.ofNat (4 * j0) + Int64.ofNat (4 * k) + Int64.ofNat 4)
      (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ := by rw [hpc', he]
  rcases tgt_pos (lab := lab) hb hwf hnx hIn hk hca
      (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ with ⟨r, rfl⟩ | ⟨q, hq, hqr, hqe⟩
  · refine Spike.Lib.A64.WriteAb.not_ab_of_pc ?_
    rw [hpc']
    simp only [Spike.Lib.A64.Flow.AI.tgt]
    rw [hret σ c hJ k hk r hca]
    exact hraAb k hk r hca
  · have hc := List.all_eq_true.mp (List.all_eq_true.mp hoff k (List.mem_range.mpr hk)) q hq
    rw [Bool.not_eq_true'] at hc
    rw [← hI.labOk] at hpc' hqe ⊢
    exact notAb_of_pos hI.lays hpr hab hqr hc (hpc'.trans hqe)

end Off

/-! ## Blocks of the tests -/

section KeepBlk

/-- The static offsets after directives (`arun`'s, `arun_so`). -/
def soRun (ds : List Directive) (o : Spike.Lib.A64.Flow.SO) : Spike.Lib.A64.Flow.SO :=
  ds.foldl (fun o d => match Spike.Lib.A64.Flow.classify d with | some a => a.so o | none => o) o

theorem arun_so (lab : Label → Int64) :
    ∀ (ds : List Directive) (am : Spike.Lib.A64.Flow.AM), (Spike.Lib.A64.Flow.arun lab ds am).so = soRun ds am.so
  | [], _ => rfl
  | d :: ds, am => by
    show (Spike.Lib.A64.Flow.arun lab ds (Spike.Lib.A64.Flow.dstep lab am d)).so = soRun ds _
    rw [arun_so lab ds]
    simp only [Spike.Lib.A64.Flow.dstep]
    split <;> simp_all

/-- **Every instruction a test keeping the stored data** (but `exc`'s): at a
test's position, `sp` at `-48` before and after, writing no slot, every
target off the write abort or a test. -/
def keepChk (L : Label) (j0 : Nat) (blk : List Directive) (nxt : Option (Label × Nat)) (exc : List Nat) : Bool :=
  (List.range blk.length).all fun k => exc.contains k ||
    (tailPos.contains (L, j0 + k) && (soRun (blk.take k) Spike.Lib.A64.Print.oI).sp == -48 &&
      (match blk[k]? with
        | some d => match Spike.Lib.A64.Flow.classify d with
          | some a => !a.slotWr && (a.so (soRun (blk.take k) Spike.Lib.A64.Print.oI)).sp == -48
          | none => false
        | none => false) &&
      (posTgts L j0 blk nxt k).all fun q => !abPos.contains q || tailPos.contains q)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {R : Region} {F : MachineData → Prop}

/-- **A block of the tests keeps the write abort's phase**: every
instruction but `exc`'s keeps the stored length and result (`keepChk`,
`tail_keep`), `exc`'s by `hexc`. -/
theorem blkW_abKeep {kp : Nat} (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    {n : ND} {blk : List Directive} {lo hi : Int} {L : Label} {j0 : Nat} {nxt : Option (Label × Nat)}
    {exc : List Nat}
    (hb : blockAt prog L j0 blk = true) (he : lab L + Int64.ofNat (4 * j0) = n.pc)
    (hno : n.o = Spike.Lib.A64.Print.oI) (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hlo' : R.lo ≤ -48) (hhi' : 0 ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) lab (lab L + Int64.ofNat (4 * j0)) 0 blk = true)
    (hnr : noRetBlk blk = true) (hwf : wfChk L j0 blk nxt = true)
    (hnx : ∀ q, nxt = some q → lab L + Int64.ofNat (4 * (j0 + blk.length)) = lab q.1 + Int64.ofNat (4 * q.2))
    (hIn : ∀ q ∈ extPos blk nxt, InRun prog q.1 q.2) (hkc : keepChk L j0 blk nxt exc = true)
    (hexc : ∀ σ c, n.J σ c → ∀ k (hk : k < blk.length), exc.contains k = true →
      ∀ a, Spike.Lib.A64.Flow.classify blk[k] = some a → ∀ s0 : State,
      s0.exe = exe → s0.endPc = endPc → s0.st.2 = n.pc + Int64.ofNat (4 * k) →
      Spike.Lib.A64.Flow.Abs R (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so s0.st.1
        (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Ab lab s0 →
      ∀ s' : State, s'.exe = exe → s'.endPc = endPc →
      s'.st.2 = a.tgt lab (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R (a.so (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so) s'.st.1
        (a.step (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so
          (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4) (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ) →
      ¬ Ab lab s') :
    BlkW (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F n blk := by
  refine blkW_abN hI hb he hok hR hal hlo hhi hph
    (fun _ _ _ k hk r hr => (noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    fun σ c hJ k hk a hca s0 h1 h2 hs0 hA0 hn0 s' h1' h2' hpc' hA' => ?_
  by_cases hx : exc.contains k = true
  · exact hexc σ c hJ k hk hx a hca s0 h1 h2 hs0 hA0 hn0 s' h1' h2' hpc' hA'
  have hc := List.all_eq_true.mp hkc k (List.mem_range.mpr hk)
  have hd : blk[k]? = some blk[k] := List.getElem?_eq_getElem hk
  simp only [hx, Bool.false_or, hd, hca, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hc
  obtain ⟨⟨⟨ht0, hsp0⟩, hsw, hsp'⟩, hq⟩ := hc
  replace hpc' : s'.st.2 = a.tgt lab (lab L + Int64.ofNat (4 * j0) + Int64.ofNat (4 * k) + Int64.ofNat 4)
      (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ := by rw [hpc', he]
  have hso : (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).so = soRun (blk.take k) Spike.Lib.A64.Print.oI :=
    by rw [arun_so]; exact congrArg _ hno
  rcases tgt_pos (lab := lab) hb hwf hnx hIn hk hca
      (Spike.Lib.A64.Flow.arun lab (blk.take k) ⟨n.pc, n.o, σ⟩).σ with ⟨r, rfl⟩ | ⟨q, hqm, hqr, hqe⟩
  · exact (noRet_false hnr k hk r hca).elim
  have hq' := List.all_eq_true.mp hq q hqm
  rw [← hI.labOk] at hpc' hqe he hn0 ⊢
  by_cases hqa : abPos.contains q = true
  · simp only [hqa, Bool.not_true, Bool.false_or] at hq'
    have h0 : s0.st.2 ∈ Spike.Lib.A64.WriteAb.tailPcs (_root_.Executable.labels exe).label := by
      rw [tailPcs_eq, List.mem_map]
      refine ⟨(L, j0 + k), List.contains_iff_mem.mp ht0, ?_⟩
      rw [hs0, ← he, ofNat4_add, Int64.add_assoc]
    refine tail_keep hI.lays hpr hab hlo' hhi' h0 hA0 (by rw [hso]; exact hsp0) hn0 hqr hq' (hpc'.trans hqe) hA'
      (by rw [hso]; exact hsp') ?_ ?_
    · rw [Spike.Lib.A64.Flow.AI.step_slot hsw]
    · rw [Spike.Lib.A64.Flow.AI.step_slot hsw]
  · exact notAb_of_pos hI.lays hpr hab hqr (by simpa using hqa) (hpc'.trans hqe)

end KeepBlk

/-! ## `scc_rt_print`'s states -/

open Kraken Kraken.AArch64.Parser in
/-- `.4_chk3`'s block but its `b.le`: the stored result compared with 0. -/
def b11h : List Directive := parseAArch64("ldr x9, [sp, #16]
movz x10, #0
subs xzr, x9, x10")

theorem b11_take : Spike.Lib.A64.Print.b11.take 3 = b11h := by decide

block_spec b11h (-48) 0 Spike.Lib.A64.Print.oI b11h

section Print

open Spike.Lib.A64.Print (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b16 oI
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b8_ok b9_ok b10_ok b11_ok b12_ok b13_ok b14_ok b16_ok)
open Spike.Lib.A64.PrintA (PrintAW N)
open Spike.Lib.A64.StubW (printPhOk)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {R : Region} {F : MachineData → Prop}
  {x29 ra buf0 : BitVec 64} {len0 : Nat} {P Q : Nat → Ctl → Prop}

/-- An instruction position of a block (`inRun_of_blockAt` at its start). -/
theorem inRun0 {L : Label} {j : Nat} {blk : List Directive} (h : blockAt prog L j blk = true)
    (hl : 0 < blk.length) : InRun prog L j := by
  simpa using inRun_of_blockAt h hl

set_option hygiene false in
/-- A block of `scc_rt_print` off the write abort, no `ret`. -/
local macro "poff " hb:term:max ok:term:max hp:term:max nx:term:max hnx:term:max hin:term:max : tactic =>
  `(tactic| exact blkW_abOff hI hpr hab (dead := fun _ => false) (ra := 0) (nxt := $nx) $hb (by ppc_tac) $ok hR hal
    (by omega) (by omega) $hp (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl)
    (by decide) $hnx $hin (by decide) (fun k hk r hr => (noRet_false (by decide) k hk r hr).elim))

set_option hygiene false in
/-- A block of `scc_rt_print`'s tests. -/
local macro "pkeep " hb:term:max ok:term:max hp:term:max nx:term:max ex:term:max hnx:term:max hin:term:max
    hx:term:max : tactic =>
  `(tactic| refine blkW_abKeep hI hpr hab (nxt := $nx) (exc := $ex) $hb (by ppc_tac) rfl $ok hR hal
    (by omega) (by omega) hlo hhi $hp (by decide) (by decide) $hnx $hin (by decide) $hx)

/-- **`scc_rt_print`'s states keep the write abort's phase**, none moved,
its and the abort's code in the program (`hpr`, `hab`) passing the phase
check (`hph`), the length below `2^63` (`hlen`: a positive count is then
no `b.le`, a refused one a `Refusal` of the length), the return address in
the epilogue's phase (`hra`) and off the phase's pcs (`hraAb`), in a region
of the routine's frame. -/
theorem printAb (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hpr : Scc.Cert.Rt.A64.Print.printIn prog = true) (hab : Scc.Cert.Rt.A64.Abort.abortIn prog = true)
    (hph : printPhOk okPc ph lab = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -48) (hhi : 0 ≤ R.hi) (hlen : len0 < 2 ^ 63)
    (hra : ph (Int64.ofBitVec ra).toBitVec.toNat = ph (lab ".L9_scc_rt_print.7_done").toBitVec.toNat)
    (hraAb : Int64.ofBitVec ra ∉ abPcs lab) :
    PrintAW x29 ra buf0 len0 P Q (fun s _ => AbSt μ (Ab lab) s) (fun _ _ => False) exe endPc R F := by
  have hl := hI.labOk
  subst hl
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩ := printIn_spec hpr
  obtain ⟨p0, p1, p2, p3, p4, -, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17⟩ :=
    printPhOk_spec hph
  have rE := inRun0 h1 (by decide)
  have rL := inRun0 h2 (by decide)
  have rL4 := inRun0 h3 (by decide)
  have rW := inRun0 h4 (by decide)
  have rW4 := inRun0 h5 (by decide)
  have rW12 := inRun0 h7 (by decide)
  have rW13 := inRun0 h8 (by decide)
  have rC2 := inRun0 h9 (by decide)
  have rC26 := inRun0 h10 (by decide)
  have rC27 := inRun0 h11 (by decide)
  have rC3 := inRun0 h12 (by decide)
  have rC34 := inRun0 h13 (by decide)
  have rA := inRun0 h14 (by decide)
  have rF := inRun0 h15 (by decide)
  have rD := inRun0 h16 (by decide)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · poff h0 b0_ok p0 (some (".L9_scc_rt_print.0_entry", 0))
      (fun q hq => by
        cases hq
        rw [label_labelGap hI.lays h17, show Int64.ofNat (4 * (".L9_scc_rt_print.0_entry", 0).snd) = 0 from rfl,
          Int64.add_zero]
        rfl)
      (fun q hq => by
        rw [show extPos b0 _ = [(".L9_scc_rt_print.0_entry", 0)] by decide] at hq
        simp at hq; subst hq; exact rE)
  · poff h1 b1_ok p1 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos b1 none = [(".L9_scc_rt_print.1_loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rL)
  · poff h2 b2_ok p2 (some (".L9_scc_rt_print.1_loop", 4)) (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b2 (some (".L9_scc_rt_print.1_loop", 4)) =
            [(".L9_scc_rt_print.1_loop", 4), (".L9_scc_rt_print.7_done", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
  · poff h3 b3_ok p3 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos b3 none = [(".L9_scc_rt_print.2_write", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rW)
  · poff h4 b4_ok p4 (some (".L9_scc_rt_print.2_write", 4)) (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b4 (some (".L9_scc_rt_print.2_write", 4)) = [(".L9_scc_rt_print.2_write", 4)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rW4)
  · pkeep h6 b5_ok p6 (some (".L9_scc_rt_print.2_write", 12)) [0] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b5 (some (".L9_scc_rt_print.2_write", 12)) = [(".L9_scc_rt_print.2_write", 12)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rW12)
      ?_
    intro σ c hJ k hk hx a hca s0 _ _ hs0 hA0 hn0 s' _ _ hpc' hA'
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hx
    subst hx
    simp [b5, Spike.Lib.A64.Flow.classify] at hca
    subst hca
    refine tail_ret hI.lays hpr hab hlo hhi ?_ hA0 rfl hn0 (q := (".L9_scc_rt_print.2_write", 6))
      (by simpa using inRun_of_blockAt h6 (i := 1) (by decide)) (by decide) ?_ hA' rfl ?_ ?_
    · rw [hs0, show Int64.ofNat (4 * 0) = 0 from rfl, Int64.add_zero]; rfl
    · rw [hpc']; show _ + _ + _ = _; dsimp only [N]; simp only [Int64.add_assoc]; rfl
    · simp [Spike.Lib.A64.Flow.arun, Spike.Lib.A64.Flow.AI.step, Spike.Lib.upd_apply, N]
    · simp [Spike.Lib.A64.Flow.arun, Spike.Lib.A64.Flow.AI.step, Spike.Lib.upd_apply, N]
  · pkeep h7 b6_ok p7 (some (".L9_scc_rt_print.2_write", 13)) [] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b6 (some (".L9_scc_rt_print.2_write", 13)) =
            [(".L9_scc_rt_print.2_write", 13), (".L9_scc_rt_print.1_loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h8 b7_ok p8 none [] (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos b7 none = [(".L9_scc_rt_print.3_chk2", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rC2)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h9 b8_ok p9 (some (".L9_scc_rt_print.3_chk2", 6)) [] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b8 (some (".L9_scc_rt_print.3_chk2", 6)) = [(".L9_scc_rt_print.3_chk2", 6)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rC26)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h10 b9_ok p10 (some (".L9_scc_rt_print.3_chk2", 7)) [] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b9 (some (".L9_scc_rt_print.3_chk2", 7)) =
            [(".L9_scc_rt_print.3_chk2", 7), (".L9_scc_rt_print.1_loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h11 b10_ok p11 none [] (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos b10 none = [(".L9_scc_rt_print.4_chk3", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rC3)
      (fun _ _ _ _ _ hx => by cases hx)
  · pkeep h12 b11_ok p12 (some (".L9_scc_rt_print.4_chk3", 4)) [3] (fun q hq => by cases hq; rfl)
      (fun q hq => by
        rw [show extPos b11 (some (".L9_scc_rt_print.4_chk3", 4)) =
            [(".L9_scc_rt_print.4_chk3", 4), (".L9_scc_rt_print.6_fail", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; rcases hq with rfl | rfl <;> assumption)
      ?_
    intro σ c hJ k hk hx a hca s0 _ _ hs0 hA0 hn0 s' _ _ hpc' hA'
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, beq_iff_eq] at hx
    subst hx
    simp [b11, Spike.Lib.A64.Flow.classify] at hca
    subst hca
    have hr3 : Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b11.take 3)
        ⟨(N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .chk3).pc,
          (N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .chk3).o, σ⟩ =
        Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label b11h
          ⟨(N (_root_.Executable.labels exe).label x29 ra buf0 len0 P Q .chk3).pc, oI, σ⟩ := by
      rw [b11_take]; rfl
    rw [hr3, b11h_run] at hA0 hpc'
    simp only [Spike.Lib.A64.Flow.AI.tgt] at hpc'
    split at hpc'
    · rename_i hc
      exfalso
      refine hn0 (ab_of_refusal (l := σ.slot (-40)) (r := σ.slot (-32)) ?_ ?_ ?_ ?_)
      · rw [tailPcs_eq]; exact List.mem_map.mpr ⟨(".L9_scc_rt_print.4_chk3", 3), by decide, hs0.symm⟩
      · exact (spLoad_of_abs hA0 rfl hlo hhi).1
      · exact (spLoad_of_abs hA0 rfl hlo hhi).2
      obtain ⟨k', ⟨-, -, -, h40, hk'⟩, hr⟩ := hJ
      have hc' := (Spike.Lib.A64.PrintA.subs0_le (σ.slot (-32))).mp (by simpa using hc)
      rw [h40, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      rcases hr with ⟨h0', hle, -⟩ | ⟨hw, -⟩
      · exact absurd hc' (Spike.Lib.A64.PrintA.pos_not_le h0' (by omega))
      · exact Spike.Lib.A64.PrintAb.refusal_of_refused (by omega) hw
    · exact notAb_of_pos hI.lays hpr hab rC34 (by decide)
        (by rw [hpc']; dsimp only [N]; simp only [Int64.add_assoc]; rfl)
  · poff h13 b12_ok p13 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos b12 none = [(".L9_scc_rt_print.5_adv", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rA)
  · poff h14 b13_ok p14 none (fun q hq => by cases hq)
      (fun q hq => by
        rw [show extPos b13 none = [(".L9_scc_rt_print.1_loop", 0)] by decide] at hq
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hq; subst hq; exact rL)
  · refine blkW_abN hI h15 (by ppc_tac) b14_ok hR hal (by omega) (by omega) p15 (dead := fun _ => false) (ra := 0)
      (fun _ _ _ k hk r hr => (noRet_false (by decide) k hk r hr).elim) (fun _ _ _ => rfl)
      fun σ c hJ k hk a hca s0 _ _ hs0 hA0 hn0 s' _ _ hpc' hA' => (hn0 (Spike.Lib.A64.WriteAb.ab_fail ?_)).elim
    have hk2 : k < 2 := by simpa [b14] using hk
    rw [hs0]
    rcases (by omega : k = 0 ∨ k = 1) with rfl | rfl
    · simp [Spike.Lib.A64.WriteAb.failPcs, N]
    · simp only [Spike.Lib.A64.WriteAb.failPcs, List.mem_cons]; right; left; rfl
  · exact blkW_abOff hI hpr hab (dead := fun _ => false) (ra := Int64.ofBitVec ra) (nxt := none) h16 (by ppc_tac)
      b16_ok hR hal (by omega) (by omega)
      (blkPh_b16 p16 (by simpa [show Int64.ofNat (4 * 0) = 0 from rfl] using p17) (by simpa using hra))
      (fun σ _ hJ => b16_ret _ _ σ hJ.2.1) (fun _ _ _ => rfl) (by decide) (fun q hq => by cases hq)
      (fun q hq => by rw [show extPos b16 none = [] by decide] at hq; cases hq) (by decide)
      (fun _ _ _ _ => hraAb)

end Print

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.A64.PrintG.blkW_abOff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abOff

/-- info: 'Spike.Lib.A64.PrintG.blkW_abKeep' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms blkW_abKeep

/-- info: 'Spike.Lib.A64.PrintG.printAb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms printAb

end Spike.Lib.A64.PrintG
