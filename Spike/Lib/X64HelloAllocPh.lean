/-
**`scc_rt_alloc` keeps both abort phases in hello.w** (`Wf`'s `AbSt`/`AcSt`, x86-64; the twin of
`Spike/Lib/A64HelloAllocPh.lean`): `allocAbAcH`, every node of `AllocW` at
`AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (Hello.ThreadsAb.AcH lab ".Lwc_main")`, none moved, for an executable with
`InstOk`, its cells holding the allocator's code (`allocIn`) and passing its phase check (`allocPhOk`), its labels
hello's code labels where they resolve (`hlab`), for a call returning to one of the two allocation sites
(`HelloPh.WcW.AllocRetH`: `.Lwc_rodata.x0`, `.Lwc_main.x0`).

Every block's and single instruction's targets are off both phases' pcs (`blkW_phIH`, `nodeW_siIH`,
`nodeW_stepIH`; the `ret`'s is the caller's return point). The heap abort's `movq $2, %rdi; call scc_rt_abort`
(`.full`) enters the dispatcher's prologue with `%rdi = 2` (out of the write abort, `AllocG.not_ab_abort`) and the
return address it pushes past itself at `0(%rsp)` (not `raT`, out of the threads abort, `Hello.ThreadsAb.ac_x30`);
the label facts are one decided check (`fullChkH`, `chAH_full`). Each check is decided at hello's code labels.

- `chAH_*`: the checks.
- `spPcsH`, `spPcsH_congr`, `fullChkH`, `fullLabsH`, `fullChkH_congr`, `chAH_full`, `fullChkH_sound`: the heap
  abort's call's label facts.
- `blkW_fullPhH`, `blkW_phIH`, `nodeW_siIH`, `nodeW_stepIH`, `allocAbAcH`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- the allocator is x86-64's (31 nodes, `X64Alloc`): eighteen blocks and eleven single instructions (seven with
  undefined flags, `nodeW_stepIH` with `fi_step`; the counter's `lock xaddq` and the header's store through
  `%rcx`, `xadd_step`, `st_step`), offsets in bytes;
- the return points are `.Lwc_rodata.x0` and `.Lwc_main.x0` (A64's `.L19_wc_rodata.sp0`, `.L22_wc_main.sp0`);
- the call's return address is the word it pushes at `slot (-160)`, read by `ThreadsAb.RaW` at `0(%rsp)` at the
  dispatcher's entry (`WakeWf.sp0_slotG`), not `x30`: `fullChkH` also puts `scc_rt_abort` off `RaW`'s other pcs
  (`raPPcs`, `raBPcs`), and the spawn's own pcs include the `je` after the `testq` (`pcJe`);
- no alignment premise; the region is `[-160, 8)`.
-/
import Spike.Lib.X64HelloWfPh
import Spike.Lib.X64HelloAllocWI
import Spike.Lib.X64WakeAllocPhC

namespace Spike.Lib.X64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun classify SI)
open Spike.Lib.X64.Rt (InstOk)
open Scc.Cert.Rt.X64 (blockAtB)
open Spike.Lib.X64.Flow (ofNat_zero')
open Spike.Lib.LowerX64 (labC arun_succ_eq)
open Scc.Sem.X64 (codeLabel)
open SccCode (helloCells)
open Spike.Lib.X64.WakeWf (hpcOf si_step fi_step xadd_step st_step sp0_slotG raLabs raPcs_congr)
open Spike.Lib.X64.AllocG (allocPhOk allocPhOk_spec allocIn_spec phOne_spec ctr_addrS hdr_addrS abLabs abNoDispE
  abNoDispE_congr)
open Spike.Lib.X64.Alloc (Call AllocW N iRet fnL entryL cntL slowL fullL okL bPro bChk bJ1 bC1 bC2 bJ2 bSlow bJ3
  bFull bO0 bO1 bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9 bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok bSlow_ok bJ3_ok
  bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)

/-! ## The checks at hello's code labels -/

local macro "ph_dec" : tactic => `(tactic| (unfold phOffW; decide +kernel))
local macro "si_dec" : tactic => `(tactic| (unfold siOffW; decide +kernel))

theorem chAH_pro : phOffW ".Lwc_main" fnL 0 fnL bPro = true := by ph_dec
theorem chAH_chk : phOffW ".Lwc_main" entryL 0 entryL bChk = true := by ph_dec
theorem chAH_j1 : phOffW ".Lwc_main" entryL 16 entryL bJ1 = true := by ph_dec
theorem chAH_cnt : siOffW ".Lwc_main" cntL 0 7 = true := by si_dec
theorem chAH_c1 : phOffW ".Lwc_main" cntL 7 cntL bC1 = true := by ph_dec
theorem chAH_rmw : siOffW ".Lwc_main" cntL 19 5 = true := by si_dec
theorem chAH_c2 : phOffW ".Lwc_main" cntL 24 cntL bC2 = true := by ph_dec
theorem chAH_j2 : phOffW ".Lwc_main" cntL 59 cntL bJ2 = true := by ph_dec
theorem chAH_slow : phOffW ".Lwc_main" slowL 0 slowL bSlow = true := by ph_dec
theorem chAH_j3 : phOffW ".Lwc_main" slowL 16 slowL bJ3 = true := by ph_dec
/-- The heap abort's `movq $2, %rdi`. -/
theorem chAH_f0 : siOffW ".Lwc_main" fullL 0 7 = true := by si_dec
theorem chAH_o0 : phOffW ".Lwc_main" okL 0 okL bO0 = true := by ph_dec
theorem chAH_f1 : siOffW ".Lwc_main" okL 11 3 = true := by si_dec
theorem chAH_o1 : phOffW ".Lwc_main" okL 14 okL bO1 = true := by ph_dec
theorem chAH_f2 : siOffW ".Lwc_main" okL 29 3 = true := by si_dec
theorem chAH_o2 : phOffW ".Lwc_main" okL 32 okL bO2 = true := by ph_dec
theorem chAH_s2 : siOffW ".Lwc_main" okL 36 7 = true := by si_dec
theorem chAH_o3 : phOffW ".Lwc_main" okL 43 okL bO3 = true := by ph_dec
theorem chAH_f3 : siOffW ".Lwc_main" okL 58 3 = true := by si_dec
theorem chAH_o4 : phOffW ".Lwc_main" okL 61 okL bO4 = true := by ph_dec
theorem chAH_f4 : siOffW ".Lwc_main" okL 88 4 = true := by si_dec
theorem chAH_o5 : phOffW ".Lwc_main" okL 92 okL bO5 = true := by ph_dec
theorem chAH_f5 : siOffW ".Lwc_main" okL 107 3 = true := by si_dec
theorem chAH_o6 : phOffW ".Lwc_main" okL 110 okL bO6 = true := by ph_dec
theorem chAH_f6 : siOffW ".Lwc_main" okL 125 3 = true := by si_dec
theorem chAH_o7 : phOffW ".Lwc_main" okL 128 okL bO7 = true := by ph_dec
theorem chAH_f7 : siOffW ".Lwc_main" okL 140 3 = true := by si_dec
theorem chAH_o8 : phOffW ".Lwc_main" okL 143 okL bO8 = true := by ph_dec
theorem chAH_hdr : siOffW ".Lwc_main" okL 170 3 = true := by si_dec
theorem chAH_o9 : phOffW ".Lwc_main" okL 173 okL bO9 = true := by ph_dec
/-- The `ret` to rodata's `.x15`. -/
theorem chAH_retR : phOffW ".Lwc_main" okL 226 ".Lwc_rodata.x0" [(iRet.toDir, 1)] = true := by ph_dec
/-- The `ret` to `wc_main`'s `.x22`. -/
theorem chAH_retM : phOffW ".Lwc_main" okL 226 ".Lwc_main.x0" [(iRet.toDir, 1)] = true := by ph_dec

/-! ## The heap abort's call's label facts -/

/-- The spawn's own pcs of hello's threads abort (`Hello.ThreadsAb.ac_x30`'s). -/
def spPcsH (lab : Label → Int64) (pfx : String) : List Int64 :=
  Hello.ThreadsAb.pcRet lab pfx ".x3" 94 :: Hello.ThreadsAb.pcJe lab pfx ".x3" 94 ::
    Hello.ThreadsAb.pcSt lab pfx ".x4" :: Hello.ThreadsAb.tailPcs lab pfx ".x4" ++ ThreadsAb.failPcs lab pfx

theorem spPcsH_congr {lab lab' : Label → Int64} {pfx : String} (h : ∀ l ∈ acLabs pfx, lab l = lab' l) :
    spPcsH lab pfx = spPcsH lab' pfx := by
  simp only [spPcsH, Hello.ThreadsAb.pcRet, Hello.ThreadsAb.pcJe, Hello.ThreadsAb.cloneAt, Hello.ThreadsAb.pcSt,
    Hello.ThreadsAb.tailPcs, ThreadsAb.failPcs]
  rw [h _ (by simp [acLabs] : pfx ++ ".x3" ∈ acLabs pfx), h _ (by simp [acLabs] : pfx ++ ".x4" ∈ acLabs pfx),
    h _ (by simp [acLabs] : pfx ++ ".spawnfail5" ∈ acLabs pfx)]

/-- **The heap abort's call's label facts**: its target off the write abort's pcs but the dispatcher's prologue,
off the spawn's own pcs and off `RaW`'s pcs but `0(%rsp)`'s, its return address not `raT`. -/
def fullChkH (lab : Label → Int64) (pfx : String) : Bool :=
  !(abNoDispE lab).contains (lab "scc_rt_abort") && !(spPcsH lab pfx).contains (lab "scc_rt_abort") &&
    !(ThreadsAb.raPPcs lab).contains (lab "scc_rt_abort") && !(ThreadsAb.raBPcs lab).contains (lab "scc_rt_abort") &&
    ((lab fullL + 12).toBitVec != ThreadsAb.raT lab pfx)

/-- The labels `fullChkH` reads. -/
def fullLabsH (pfx : String) : List String := fullL :: abLabs ++ acLabs pfx ++ raLabs

theorem fullChkH_congr {lab lab' : Label → Int64} {pfx : String} (h : ∀ x ∈ fullLabsH pfx, lab x = lab' x) :
    fullChkH lab pfx = fullChkH lab' pfx := by
  have ha : ∀ x ∈ abLabs, lab x = lab' x := fun x hx => h x (by simp [fullLabsH, hx])
  have hc : ∀ x ∈ acLabs pfx, lab x = lab' x := fun x hx => h x (by simp [fullLabsH, hx])
  have hr : ∀ x ∈ raLabs, lab x = lab' x := fun x hx => h x (by simp [fullLabsH, hx])
  obtain ⟨-, h2, h3⟩ := raPcs_congr hr
  unfold fullChkH
  rw [abNoDispE_congr ha, spPcsH_congr hc, h2, h3, ha "scc_rt_abort" (by simp [abLabs]),
    h fullL (by simp [fullLabsH])]
  simp only [ThreadsAb.raT]
  rw [hc (pfx ++ ".spawnfail5") (by simp [acLabs])]

theorem chAH_full : ((fullLabsH ".Lwc_main").all
    (fun x => (codeLabel Spike.Lib.X64.HelloPh.lo helloCells x).isSome) &&
    fullChkH (labC Spike.Lib.X64.HelloPh.lo helloCells) ".Lwc_main") = true := by
  decide +kernel

/-- **`fullChkH` at any labels agreeing with the code labels.** -/
theorem fullChkH_sound {lab : Label → Int64}
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a) :
    lab "scc_rt_abort" ∉ abNoDispE lab ∧ lab "scc_rt_abort" ∉ spPcsH lab ".Lwc_main" ∧
      lab "scc_rt_abort" ∉ ThreadsAb.raPPcs lab ∧ lab "scc_rt_abort" ∉ ThreadsAb.raBPcs lab ∧
      (lab fullL + 12).toBitVec ≠ ThreadsAb.raT lab ".Lwc_main" := by
  have h := chAH_full
  simp only [Bool.and_eq_true] at h
  have e := fullChkH_congr (lab_labC hlab h.1)
  have h2 := h.2
  rw [← e] at h2
  simpa only [fullChkH, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, and_assoc] using h2

/-! ## The heap abort's call -/

section Full

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **`.full`'s `movq $2, %rdi; call scc_rt_abort` keeps both phases**: its pcs off the marks' sites (`hpc`), the
`movq`'s next pc off both phases' (`chAH_f0`), the call's target off both phases' pcs but the dispatcher's
prologue, entered at `%rdi = 2` with the return address pushed past the call (`fullChkH_sound`). -/
theorem blkW_fullPhH {n : ND}
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a →
      (_root_.Executable.labels exe).label l = Int64.ofNat a)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc bFull)
    (hnp : n.pc = (_root_.Executable.labels exe).label fullL) (hno : n.o = Spike.Lib.X64.Alloc.oI)
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hpc : ∀ j < bFull.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff bFull j) → PcOff μ s) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label ".Lwc_main") s)
      (fun _ _ => False) exe endPc R F n bFull := by
  have hok : Spike.Lib.X64.okBlk (-160) 8 n.o bFull = true := by rw [hno]; exact Spike.Lib.X64.Alloc.bFull_ok
  have hsi := siOffW_sound (lab := (_root_.Executable.labels exe).label) hlab chAH_f0
  simp only [siOff, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hsi
  obtain ⟨hnE, hnS, hnP, hnB, hraT⟩ := fullChkH_sound hlab
  have hrun : ∀ σ, arun (_root_.Executable.labels exe).label (bFull.take (1 + 1)) ⟨n.pc, n.o, σ⟩ =
      arun (_root_.Executable.labels exe).label bFull ⟨n.pc, Spike.Lib.X64.Alloc.oI, σ⟩ := fun σ => by
    rw [hno]; rfl
  have key : ∀ σ c, n.J σ c → ∀ k (hk : k < bFull.length) a, classify bFull[k].1 = some a →
      ∀ s' : State, s'.st.2 = a.tgt (_root_.Executable.labels exe).label
        (arun (_root_.Executable.labels exe).label (bFull.take k) ⟨n.pc, n.o, σ⟩).so
        (n.pc + Int64.ofNat (cellOff bFull k) + Int64.ofNat bFull[k].2)
        (arun (_root_.Executable.labels exe).label (bFull.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.X64.Abs R (arun (_root_.Executable.labels exe).label (bFull.take (k + 1)) ⟨n.pc, n.o, σ⟩).so
        s'.st.1 (arun (_root_.Executable.labels exe).label (bFull.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label s' ∧
        ¬ Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label ".Lwc_main" s' := by
    intro σ c hJ k hk a ha s' hpc' hA'
    match k, hk with
    | 0, _ =>
      obtain ⟨a', ha', -, hterm⟩ := Spike.Lib.X64.okBlk_get (_root_.Executable.labels exe).label
        (am := ⟨n.pc, n.o, σ⟩) hok (k := 0) (by decide)
      rw [ha] at ha'
      cases ha'
      rw [Spike.Lib.X64.AI.tgt_of_not_term (hterm (by decide))] at hpc'
      have ht : s'.st.2 = (_root_.Executable.labels exe).label fullL + Int64.ofNat 0 + Int64.ofNat 7 := by
        rw [hpc', hnp]; rfl
      exact ⟨Spike.Lib.X64.WriteAb.not_ab_of_pc (by rw [ht]; exact hsi.1),
        Hello.ThreadsAb.not_ac_of_pc (by rw [ht]; exact hsi.2)⟩
    | 1, _ =>
      have hc1 : classify (bFull[1]'(by decide)).1 = some (.call "scc_rt_abort") := rfl
      rw [hc1] at ha
      cases ha
      have ht : s'.st.2 = (_root_.Executable.labels exe).label "scc_rt_abort" := by
        rw [hpc', Spike.Lib.X64.BlockSpec.AI.tgt_call']
      refine ⟨Spike.Lib.X64.AllocG.not_ab_abort ht (fun h4 => ?_) hnE, fun hac => ?_⟩
      · rw [hA'.regs, hrun, Spike.Lib.X64.Alloc.bFull_run] at h4
        simp [Reg64s.set64, Reg64s.get64] at h4
      · have hx := Hello.ThreadsAb.ac_x30 hac (by rw [ht]; exact hnS)
        rcases hx with ⟨-, hl⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
        · rw [hrun, Spike.Lib.X64.Alloc.bFull_run] at hA'
          rw [sp0_slotG hA' (show R.Off (-160) from ⟨by decide, by omega, by omega⟩)] at hl
          simp only [Spike.Lib.upd_apply, ite_true, Option.some.injEq] at hl
          exact hraT (by rw [← hnp]; exact hl)
        · exact hnP (by rw [← ht]; exact hm)
        · exact hnB (by rw [← ht]; exact hm)
  refine BlkW.and (blkW_abSt hcode hok hR hlo hhi hpc ?_) (blkW_acStN hcode hok hR hlo hhi hpc ?_)
  · intro σ c hJ k hk a ha s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').1
  · intro σ c hJ k hk a ha _ _ _ _ _ _ s' _ _ hpc' hA'
    obtain ⟨hso, hst⟩ := arun_succ_eq _ (am := ⟨n.pc, n.o, σ⟩) hok hk ha
    rw [hso, hst] at hA'
    exact (key σ c hJ k hk a ha s' hpc' hA').2

end Full

/-! ## At the program's blocks -/

section Prog

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {pfx : String}

/-- **`blkW_phSt` at a block of the program** without a `ret` (`WakeWf.blkW_phI` at `AcH`). -/
theorem blkW_phIH (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List (Directive × Nat)} {lo hi : Int} {l rl : Label} {k : Nat}
    (hb : blockAtB cells l k blk = true) (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : Spike.Lib.X64.okBlk lo hi n.o blk = true) (hR : R.OK) (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat k) 0 blk = true)
    (hnr : noRetBlk blk = true) (h : phOff (_root_.Executable.labels exe).label pfx l k rl blk = true) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  exact blkW_phSt (fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI hb hs hn) hok hR hlo hhi
    (hpcOf hI hok hph hnr) he h fun _ _ _ j hj r => (noRet_false hnr j hj r).elim

omit [Kraken.Executable.ValidLayout exe] in
/-- **`nodeW_phSt` at an instruction of the program** of size `z`, from its step (`hstep`), its pc off the sites
(`hok`). -/
theorem nodeW_stepIH (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k z : Nat} (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat k).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k z = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.X64.CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  exact nodeW_phSt he h (fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq)) hstep s c hA

/-- **`nodeW_phSt` at a single instruction of the program** (`WakeWf.nodeW_siI` at `AcH`). -/
theorem nodeW_siIH (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {si : SI} {z : Nat} {l : Label} {k : Nat} (hb : blockAtB cells l k [(si.toDir, z)] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat k).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k z = true) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n :=
  nodeW_stepIH hI he hok h (si_step hI hb he)

end Prog

/-! ## The allocator -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call}

set_option hygiene false in
/-- A `ret`-free block of `scc_rt_alloc` off both phases' pcs. -/
local macro "pblk " hb:term:max ok:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact blkW_phIH hI $hb (by pc_tac) $ok hR (by omega) (by omega) $hp (by decide)
    (phOffW_sound hlab $ch))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "psi " hb:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact nodeW_siIH hI $hb (by pc_tac) (phOne_spec $hp).1 (siOffW_sound hlab $ch))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "pfi " hb:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact nodeW_stepIH hI (by pc_tac) (phOne_spec $hp).1 (siOffW_sound hlab $ch)
    (fi_step hI $hb (by pc_tac)))

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc`'s states keep both abort phases** in hello.w, none moved: its code passing the phase check
(`hph`), its labels hello's code labels (`hlab`), for a call `q` at any allocation site (`hq`) returning to one of
the two calls' return points (`hrl`, `hra`), in a region of the allocator's frame, the counter and every header
the code may store unmapped in private memory (`hmem`). -/
theorem allocAbAcH (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.HelloPh.lo helloCells l = some a → lab l = Int64.ofNat a)
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab) {rl : Label} (hrl : Spike.Lib.X64.HelloPh.WcW.AllocRetH rl)
    (hra : q.ra = (lab rl).toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ (Spike.Lib.X64.WriteAb.Ab lab) s ∧
      AcSt μ Cl (Hello.ThreadsAb.AcH lab ".Lwc_main") s) (fun _ _ => False) exe endPc R F := by
  have hl := hI.labOk
  subst hl
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31⟩ := allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · pblk h0 bPro_ok p0 chAH_pro
  · pblk h1 bChk_ok p1 chAH_chk
  · pblk h2 bJ1_ok p2 chAH_j1
  · psi h3 p3 chAH_cnt
  · pblk h4 bC1_ok p4 chAH_c1
  · refine nodeW_stepIH hI (by pc_tac) (phOne_spec p5).1 (siOffW_sound hlab chAH_rmw)
      (xadd_step hI (b := .rcx) (i := 0) (r := .rax) h5 (by pc_tac) fun σ c m hJ hF => ?_)
    obtain ⟨-, hcx, -⟩ := hJ
    rw [ctr_addrS (hq m hF) hcx]
    exact hmem _ (.inl rfl) m hF
  · pblk h6 bC2_ok p6 chAH_c2
  · pblk h7 bJ2_ok p7 chAH_j2
  · pblk h8 bSlow_ok p8 chAH_slow
  · pblk h9 bJ3_ok p9 chAH_j3
  · -- the heap abort's `movq $2, %rdi; call scc_rt_abort`
    have he : (_root_.Executable.labels exe).label fullL + Int64.ofNat 0 =
        (N (_root_.Executable.labels exe).label ms q .full).pc := by pc_tac
    have hph10 := p10
    simp only [Spike.Lib.X64.AllocG.aBlk] at hph10
    rw [he] at hph10
    exact blkW_fullPhH hlab (fun s hs hn => he ▸ Spike.Lib.X64.Rt.codeOf hI h10 hs hn) rfl rfl hR hlo hhi
      (hpcOf hI Spike.Lib.X64.Alloc.bFull_ok hph10 (by decide))
  · pblk h11 bO0_ok p11 chAH_o0
  · pfi h12 p12 chAH_f1
  · pblk h13 bO1_ok p13 chAH_o1
  · pfi h14 p14 chAH_f2
  · pblk h15 bO2_ok p15 chAH_o2
  · psi h16 p16 chAH_s2
  · pblk h17 bO3_ok p17 chAH_o3
  · pfi h18 p18 chAH_f3
  · pblk h19 bO4_ok p19 chAH_o4
  · pfi h20 p20 chAH_f4
  · pblk h21 bO5_ok p21 chAH_o5
  · pfi h22 p22 chAH_f5
  · pblk h23 bO6_ok p23 chAH_o6
  · pfi h24 p24 chAH_f6
  · pblk h25 bO7_ok p25 chAH_o7
  · pfi h26 p26 chAH_f7
  · pblk h27 bO8_ok p27 chAH_o8
  · refine nodeW_stepIH hI (by pc_tac) (phOne_spec p28).1 (siOffW_sound hlab chAH_hdr)
      (st_step hI (b := .rcx) (i := 0) (r := .rax) h28 (by pc_tac) fun σ c m hJ hF => ?_)
    obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
    exact hmem _ (.inr ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 hcx⟩) m hF
  · pblk h29 bO9_ok p29 chAH_o9
  · have he : (_root_.Executable.labels exe).label okL + Int64.ofNat 226 =
        (N (_root_.Executable.labels exe).label ms q .ret).pc := by pc_tac
    have hok : Spike.Lib.X64.okBlk (-160) 8 (N (_root_.Executable.labels exe).label ms q .ret).o
        [(iRet.toDir, 1)] = true := by dsimp only [N]; decide
    have hch : phOff (_root_.Executable.labels exe).label ".Lwc_main" okL 226 rl [(iRet.toDir, 1)] = true := by
      rcases hrl with rfl | rfl
      · exact phOffW_sound hlab chAH_retR
      · exact phOffW_sound hlab chAH_retM
    refine Spike.Lib.LowerX64.BlkW.nodeW (blkW_phSt (fun s hs hn => by
        rw [← he, ← (show (_root_.Executable.labels exe).label Spike.Lib.X64.Alloc.retL + Int64.ofNat 0 =
          (_root_.Executable.labels exe).label Spike.Lib.X64.Alloc.okL + Int64.ofNat 226 by
            rw [Spike.Lib.X64.Flow.ofNat_zero']; exact Scc.Cert.Rt.X64.label_labelGapB hI.lays h30.1)]
        exact Spike.Lib.X64.Rt.codeOf hI h30.2 hs hn) hok
      hR (by omega) (by omega) (fun j hj s h1 h2 h3 => ?_) he hch
      (hret_of_run hok fun σ c hJ => ?_)) (List.cons_ne_nil _ _)
    · obtain rfl : j = 0 := by simpa using hj
      rw [Spike.Lib.X64.cellOff_zero, ofNat_zero', ← he] at h3
      exact (hI.off s (by unfold pcOf; rw [h3]; exact p30)).1
    · obtain ⟨o, -, -, -, -, -, h0, -⟩ := hJ
      have hc : Spike.Lib.X64.classify iRet.toDir = some iRet := rfl
      simp only [arun, List.foldl, Spike.Lib.X64.dstep, hc]
      simp only [iRet, Spike.Lib.X64.AI.tgt, N, Spike.Lib.X64.Alloc.oE]
      rw [h0, hra]
      exact Int64.ofBitVec_toBitVec _

end Spike.Lib.X64.HelloWf

/-- info: 'Spike.Lib.X64.HelloWf.chAH_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.chAH_full

/-- info: 'Spike.Lib.X64.HelloWf.blkW_fullPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.blkW_fullPhH

/-- info: 'Spike.Lib.X64.HelloWf.allocAbAcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloWf.allocAbAcH
