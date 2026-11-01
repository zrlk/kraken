/-
**`scc_rt_alloc` keeps both abort phases in hello.w** (`Wf`'s `AbSt`/`AcSt`,
AArch64; hello twin of `A64WakeAllocPh`): `allocAbAcH`, every node of `AllocW` at
`AbSt μ (WriteAb.Ab lab) ∧ AcSt μ Cl (HelloWf.AcH lab pfxM)`, none moved, for an
executable with `InstOk`, its program holding the allocator's code (`allocIn`) and
passing its phase check (`allocPhOk`), its labels hello's code labels where they
resolve (`hlab`), for a call returning to one of the two allocation sites' `.sp0`
(`HelloPh.WcW.AllocRetH`).

Every block's and single instruction's targets are off both phases' pcs
(`blkW_phIH`, `nodeW_siIH`, `nodeW_phStH`; the `ret`'s is the caller's `.sp0`). The
heap abort's `bl scc_rt_abort` (`.4_full`) enters the dispatcher's prologue with
`x0 = 2` (out of the write abort, `AllocG.not_ab_abort`) and `x30` past itself
(not `raT`, out of the threads abort, `Hello.ThreadsAb.ac_x30`); the label facts are
one decided check (`fullChkH`, `chAH_full`). Each check is decided at hello's code
labels.

- `chAH_*`: the checks.
- `fullLabsH`, `fullChkH`, `fullChkH_congr`, `fullChkHC`, `fullChkH_sound`: the heap
  abort's call's label facts.
- `blkW_fullPhH`, `blkW_phIH`, `nodeW_siIH`, `allocAbAcH`.
-/
import Spike.Lib.A64HelloWfPh
import Spike.Lib.A64HelloChild
import Spike.Lib.A64WakeWfHP
import Spike.Lib.A64WakeWfW
import Spike.Lib.A64AllocGS
import Spike.Lib.A64HelloAllocWI

namespace Spike.Lib.A64.HelloWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib (Region MemSide)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA
open Spike.Lib.A64.Flow (NodeW BlkW ND At)
open Spike.Lib.A64.Rt (InstOk)
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt)
open Scc.Cert.Link.A64 (codeOf)
open Spike.Lib.LowerA64 (labC arun_succ_eq)
open Spike.Lib.A64.Flow (ofNat4_zero)
open Spike.Lib.A64.Flow.Worker.Hello.Child (pfxM)
open Spike.Lib.A64.AllocG (allocPhOk allocPhOk_spec allocIn_spec phOne_spec hdr_addrS abLabs abNoDispE)
open Spike.Lib.A64.Alloc (Call AllocW N iRet b0 b1 b2 b3 b4 b5 b6 b7 b9 b11 b12 b13
  b0_ok b1_ok b2_ok b3_ok b4_ok b5_ok b6_ok b7_ok b9_ok b11_ok b12_ok b13_ok)

/-! ## The checks at hello's code labels -/

local macro "ph_dec" : tactic => `(tactic| (simp only [phOffHC, ← codeT_eq]; decide +kernel))
local macro "si_dec" : tactic => `(tactic| (simp only [siOffHC, ← codeT_eq]; decide +kernel))

theorem chAH_b0 : phOffHC pfxM "scc_rt_alloc" 0 "scc_rt_alloc" b0 = true := by ph_dec
theorem chAH_b1 : phOffHC pfxM ".L2_scc_rt_alloc.0_entry" 0 ".L2_scc_rt_alloc.0_entry" b1 = true := by ph_dec
theorem chAH_b2 : phOffHC pfxM ".L2_scc_rt_alloc.0_entry" 4 ".L2_scc_rt_alloc.0_entry" b2 = true := by ph_dec
theorem chAH_c0 : siOffHC pfxM ".L2_scc_rt_alloc.1_cnt" 0 = true := by si_dec
theorem chAH_c1 : siOffHC pfxM ".L2_scc_rt_alloc.1_cnt" 1 = true := by si_dec
theorem chAH_b3 : phOffHC pfxM ".L2_scc_rt_alloc.1_cnt" 2 ".L2_scc_rt_alloc.1_cnt" b3 = true := by ph_dec
theorem chAH_c5 : siOffHC pfxM ".L2_scc_rt_alloc.1_cnt" 5 = true := by si_dec
theorem chAH_b4 : phOffHC pfxM ".L2_scc_rt_alloc.1_cnt" 6 ".L2_scc_rt_alloc.1_cnt" b4 = true := by ph_dec
theorem chAH_b5 : phOffHC pfxM ".L2_scc_rt_alloc.1_cnt" 15 ".L2_scc_rt_alloc.1_cnt" b5 = true := by ph_dec
theorem chAH_b6 : phOffHC pfxM ".L2_scc_rt_alloc.2_slow" 0 ".L2_scc_rt_alloc.2_slow" b6 = true := by ph_dec
theorem chAH_b7 : phOffHC pfxM ".L2_scc_rt_alloc.2_slow" 4 ".L2_scc_rt_alloc.2_slow" b7 = true := by ph_dec
theorem chAH_f0 : siOffHC pfxM ".L2_scc_rt_alloc.4_full" 0 = true := by si_dec
theorem chAH_b11 : phOffHC pfxM ".L2_scc_rt_alloc.5_ok" 0 ".L2_scc_rt_alloc.5_ok" b11 = true := by ph_dec
theorem chAH_o8 : siOffHC pfxM ".L2_scc_rt_alloc.5_ok" 8 = true := by si_dec
theorem chAH_o9 : siOffHC pfxM ".L2_scc_rt_alloc.5_ok" 9 = true := by si_dec
theorem chAH_b12 : phOffHC pfxM ".L2_scc_rt_alloc.5_ok" 10 ".L2_scc_rt_alloc.5_ok" b12 = true := by ph_dec
theorem chAH_o41 : siOffHC pfxM ".L2_scc_rt_alloc.5_ok" 41 = true := by si_dec
theorem chAH_b13 : phOffHC pfxM ".L2_scc_rt_alloc.5_ok" 42 ".L2_scc_rt_alloc.5_ok" b13 = true := by ph_dec
/-- The `ret` to rodata's `.sp0`. -/
theorem chAH_retR : phOffHC pfxM ".L2_scc_rt_alloc.5_ok" 54 ".L19_wc_rodata.sp0" [iRet.toDir] = true := by ph_dec
/-- The `ret` to `wc_main`'s `.sp0`. -/
theorem chAH_retM : phOffHC pfxM ".L2_scc_rt_alloc.5_ok" 54 ".L22_wc_main.sp0" [iRet.toDir] = true := by ph_dec

/-! ## The heap abort's call's label facts -/

/-- The spawn's own pcs of hello's threads abort (`Hello.ThreadsAb.ac_x30`'s). -/
def spPcsH (lab : Label → Int64) (pfx : String) : List Int64 :=
  Hello.ThreadsAb.pcRet lab pfx 25 :: Hello.ThreadsAb.pcSt lab pfx ".clone13" ::
    Hello.ThreadsAb.tailPcs lab pfx ".clone13" ++ ThreadsAb.failPcs lab pfx

/-- **The heap abort's call's label facts**: its target off the write abort's pcs but
the dispatcher's prologue and off the spawn's own pcs, its return address not `raT`. -/
def fullChkH (lab : Label → Int64) : Bool :=
  !(abNoDispE lab).contains (lab "scc_rt_abort") && !(spPcsH lab pfxM).contains (lab "scc_rt_abort") &&
    ((lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec != ThreadsAb.raT lab pfxM)

/-- The labels `fullChkH` reads. -/
def fullLabsH : List String := ".L2_scc_rt_alloc.4_full" :: abLabs ++ acLabsH pfxM

theorem fullChkH_congr {lab lab' : Label → Int64} (h : ∀ x ∈ fullLabsH, lab x = lab' x) :
    fullChkH lab = fullChkH lab' := by
  have ha : ∀ x ∈ abLabs, lab x = lab' x := fun x hx => h x (by simp [fullLabsH, hx])
  have e1 : abNoDispE lab = abNoDispE lab' := by
    simp (disch := decide) only [abNoDispE, WriteAb.pcRet, Spike.Lib.A64.PrintD.pcSvc, WriteAb.tailPcs,
      WriteAb.failPcs, WriteAb.dispTPcs, WriteAb.g4Pcs, WriteAb.stubPcs, ha]
  simp only [fullChkH, spPcsH, Hello.ThreadsAb.pcRet, Hello.ThreadsAb.pcSt, Hello.ThreadsAb.tailPcs,
    ThreadsAb.failPcs, ThreadsAb.raT]
  rw [e1, ha "scc_rt_abort" (by decide), h ".L2_scc_rt_alloc.4_full" (by simp [fullLabsH]),
    h (pfxM ++ ".sp6") (by simp [fullLabsH, acLabsH]), h (pfxM ++ ".clone13") (by simp [fullLabsH, acLabsH]),
    h (pfxM ++ ".1_spawnfail5") (by simp [fullLabsH, acLabsH])]

theorem chAH_full : (fullLabsH.all (fun x => (codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg x).isSome) &&
    fullChkH (labC Spike.Lib.A64.HelloPh.lo SccCode.helloProg)) = true := by
  simp only [← codeT_eq]; decide +kernel

/-- **`fullChkH` at any labels agreeing with the code labels.** -/
theorem fullChkH_sound {lab : Label → Int64}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x) :
    lab "scc_rt_abort" ∉ abNoDispE lab ∧ lab "scc_rt_abort" ∉ spPcsH lab pfxM ∧
      (lab ".L2_scc_rt_alloc.4_full" + 8).toBitVec ≠ ThreadsAb.raT lab pfxM := by
  have h := chAH_full
  simp only [Bool.and_eq_true] at h
  have e := fullChkH_congr (lab_labCH hlab h.1)
  have h2 := h.2
  rw [← e] at h2
  simpa only [fullChkH, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    bne_iff_ne, ne_eq, and_assoc] using h2

/-! ## The heap abort's call -/

section Full

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **`.4_full`'s `movz x0, #2; bl scc_rt_abort` keeps both phases**: its pcs off
the marks' sites (`hpc`), the `movz`'s next pc off both phases' (`chAH_f0`), the
call's target off both phases' pcs but the dispatcher's prologue, entered at
`x0 = 2` and `x30` past the call (`fullChkH_sound`). -/
theorem blkW_fullPhH {n : ND}
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x →
      (_root_.Executable.labels exe).label l = Int64.ofNat x)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → Spike.Lib.A64.CodeAt s n.pc b9)
    (hnp : n.pc = (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full")
    (hno : n.o = Spike.Lib.A64.Alloc.oI)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hpc : ∀ j < b9.length, ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc + Int64.ofNat (4 * j) →
      PcOff μ s) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfxM) s)
      (fun _ _ => False) exe endPc R F n b9 := by
  have hok : Spike.Lib.A64.Flow.okBlk (-160) 0 n.o b9 = true := by rw [hno]; exact b9_ok
  have hsi := siOffHC_sound (lab := (_root_.Executable.labels exe).label) hlab chAH_f0
  simp only [siOffH, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not] at hsi
  obtain ⟨hnE, hnS, hraT⟩ := fullChkH_sound hlab
  have hrun : ∀ σ, Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take (1 + 1))
      ⟨n.pc, n.o, σ⟩ = Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label b9
      ⟨n.pc, Spike.Lib.A64.Alloc.oI, σ⟩ := fun σ => by rw [hno]; rfl
  have key : ∀ σ c, n.J σ c → ∀ k (hk : k < b9.length) a, Spike.Lib.A64.Flow.classify b9[k] = some a →
      ∀ s' : State, s'.st.2 = a.tgt (_root_.Executable.labels exe).label (n.pc + Int64.ofNat (4 * k) + Int64.ofNat 4)
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take k) ⟨n.pc, n.o, σ⟩).σ →
      Spike.Lib.A64.Flow.Abs R
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take (k + 1)) ⟨n.pc, n.o, σ⟩).so s'.st.1
        (Spike.Lib.A64.Flow.arun (_root_.Executable.labels exe).label (b9.take (k + 1)) ⟨n.pc, n.o, σ⟩).σ →
      ¬ Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label s' ∧
        ¬ AcH (_root_.Executable.labels exe).label pfxM s' := by
    intro σ c hJ k hk a ha s' hpc' hA'
    match k, hk with
    | 0, _ =>
      simp [b9, Spike.Lib.A64.Flow.classify] at ha
      obtain ⟨-, rfl⟩ := ha
      have ht : s'.st.2 = (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) +
          Int64.ofNat 4 := by
        rw [hpc']; dsimp only [Spike.Lib.A64.Flow.AI.tgt]; rw [hnp]
      exact ⟨Spike.Lib.A64.WriteAb.not_ab_of_pc (by rw [ht]; exact hsi.1),
        Spike.Lib.A64.Hello.ThreadsAb.not_ac_of_pc (by rw [ht]; exact hsi.2)⟩
    | 1, _ =>
      simp [b9, Spike.Lib.A64.Flow.classify] at ha
      subst ha
      have ht : s'.st.2 = (_root_.Executable.labels exe).label "scc_rt_abort" := by
        rw [hpc']; rfl
      refine ⟨Spike.Lib.A64.AllocG.not_ab_abort ht (fun h4 => ?_) hnE, fun hac => ?_⟩
      · rw [hA'.regs, hrun, Spike.Lib.A64.Alloc.b9_run] at h4
        revert h4; dsimp only; decide
      · have hx := Spike.Lib.A64.Hello.ThreadsAb.ac_x30 hac (by rw [ht]; exact hnS)
        rw [hA'.regs, hrun, Spike.Lib.A64.Alloc.b9_run] at hx
        dsimp only at hx
        rw [Spike.Lib.A64.Alloc.b9_x30, hnp] at hx
        exact hraT hx
  refine BlkW.and (blkW_abSt hcode hok hR hal (by omega) (by omega) hpc ?_)
    (blkW_acStN hcode hok hR hal (by omega) (by omega) hpc ?_)
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

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop} {okPc : Nat → Bool}
  {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop} {pfx : String}

/-- **`blkW_phStH` at a block of the program** without a `ret` (`WakeWf.blkW_phI` at `AcH`). -/
theorem blkW_phIH (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {blk : List Directive} {lo hi : Int} {l : Label} {k : Nat} (hb : blockAt prog l k blk = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk lo hi n.o blk = true) (hR : R.OK) (hal : R.base.toNat % 16 = 0)
    (hlo : R.lo ≤ lo) (hhi : hi ≤ R.hi)
    (hph : blkPh okPc ph (fun _ => false) (_root_.Executable.labels exe).label
      ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : noRetBlk blk = true) (h : phOffH (_root_.Executable.labels exe).label pfx l k l blk = true) :
    BlkW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n blk := by
  rw [he] at hph
  exact blkW_phStH (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk hb he) hok hR hal hlo hhi
    (Spike.Lib.A64.WakeWf.hpcOf hI hok hph hnr) he h fun _ _ _ j hj r hr => (noRet_false hnr j hj r hr).elim

/-- **`nodeW_phStH` at a single instruction of the program** (`WakeWf.nodeW_siI` at `AcH`). -/
theorem nodeW_siIH (hI : InstOk exe endPc prog (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {si : Spike.Lib.A64.Flow.SI} {l : Label} {k : Nat} (hb : blockAt prog l k [si.toDir] = true)
    (he : (_root_.Executable.labels exe).label l + Int64.ofNat (4 * k) = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat (4 * k)).toBitVec.toNat = true)
    (h : siOffH (_root_.Executable.labels exe).label pfx l k = true) :
    NodeW (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (AcH (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  exact nodeW_phStH he h (fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq))
    (Spike.Lib.A64.WakeWf.si_step hI hb he) s c hA

end Prog

/-! ## The allocator -/

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64} {prog : List Directive}
  {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop} {K : State → State → Prop}
  {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region} {F : MachineData → Prop}
  {ms : MemSide isaLSE2} {q : Call}

set_option hygiene false in
/-- A `ret`-free block of `scc_rt_alloc` off both phases' pcs. -/
local macro "pblk " hb:term:max ok:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact blkW_phIH hI $hb (by pc_tac) $ok hR hal (by omega) (by omega) $hp (by decide)
    (phOffHC_sound hlab $ch))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "psi " hb:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact nodeW_siIH hI $hb (by pc_tac) (phOne_spec $hp).1 (siOffHC_sound hlab $ch))

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc`'s states keep both abort phases** in hello.w, none moved: its
code passing the phase check (`hph`), its labels hello's code labels (`hlab`), for a
call `q` at any allocation site (`hq`) returning to one of the two calls' `.sp0`
(`hrl`, `hra`), in a region of the allocator's frame, the counter and every header
the code may store unmapped in private memory (`hmem`). -/
theorem allocAbAcH (hI : InstOk exe endPc prog lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.A64.Flow.allocIn prog = true) (hph : allocPhOk okPc ph lab = true)
    (hlab : ∀ l x, codeOf Spike.Lib.A64.HelloPh.lo SccCode.helloProg l = some x → lab l = Int64.ofNat x)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo : R.lo ≤ -160) (hhi : 0 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab) {rl : Label} (hrl : Spike.Lib.A64.HelloPh.WcW.AllocRetH rl)
    (hra : q.ra = (lab rl).toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ (Spike.Lib.A64.WriteAb.Ab lab) s ∧
      AcSt μ Cl (AcH lab pfxM) s) (fun _ _ => False) exe endPc R F := by
  have hl := hI.labOk
  subst hl
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, -⟩ :=
    allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19⟩ :=
    allocPhOk_spec hph
  have htkOf : ∀ {n : ND} {p : Int64}, okPc p.toBitVec.toNat = true → p = n.pc → ∀ s c,
      At exe endPc R F n s c → ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a := by
    intro n p hok hp s c hA' a ha heq
    obtain ⟨-, -, -, hpc, -⟩ := hA'
    exact (hI.off s (by unfold pcOf; rw [hpc, ← hp]; exact hok)).1.noTake a ha (by unfold pcOf; rw [hpc]; exact heq)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · pblk h0 b0_ok p0 chAH_b0
  · pblk h1 b1_ok p1 chAH_b1
  · pblk h2 b2_ok p2 chAH_b2
  · psi h3 p3 chAH_c0
  · psi h4 p4 chAH_c1
  · pblk h5 b3_ok p5 chAH_b3
  · intro s c hA'
    have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.1_cnt" + Int64.ofNat (4 * 5) =
        (N (_root_.Executable.labels exe).label ms q .rmw).pc := by pc_tac
    refine nodeW_phStH he (siOffHC_sound hlab chAH_c5) (htkOf (phOne_spec p6).1 he s c hA')
      (Spike.Lib.A64.WakeWf.ldop_step hI (op := .ADD) (kk := .acqRel) (rs := .X9) (rt := .X11) (b := .X10) h6 he
        fun σ c m hJ hF => ?_) s c hA'
    obtain ⟨-, h10, -⟩ := hJ
    have h10' : (σ.regs.getXReg .X10).toBitVec = BitVec.ofNat 64 ms.ctr := h10
    rw [h10']
    exact hmem _ (.inl rfl) m hF
  · pblk h7 b4_ok p7 chAH_b4
  · pblk h8 b5_ok p8 chAH_b5
  · pblk h9 b6_ok p9 chAH_b6
  · pblk h10 b7_ok p10 chAH_b7
  · -- the heap abort's `movz x0, #2; bl scc_rt_abort`
    have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.4_full" + Int64.ofNat (4 * 0) =
        (N (_root_.Executable.labels exe).label ms q .full).pc := by pc_tac
    have hph11 := p11
    rw [he] at hph11
    exact blkW_fullPhH hlab (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk h11 he) rfl rfl hR hal hlo hhi
      (Spike.Lib.A64.WakeWf.hpcOf hI b9_ok hph11 (by decide))
  · pblk h12 b11_ok p12 chAH_b11
  · psi h13 p13 chAH_o8
  · psi h14 p14 chAH_o9
  · pblk h15 b12_ok p15 chAH_b12
  · intro s c hA'
    have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 41) =
        (N (_root_.Executable.labels exe).label ms q .hdr).pc := by pc_tac
    refine nodeW_phStH he (siOffHC_sound hlab chAH_o41) (htkOf (phOne_spec p16).1 he s c hA')
      (Spike.Lib.A64.WakeWf.st_step hI (t := .X9) (b := .X10) (i := 0) h16 he fun σ c m hJ hF => ?_) s c hA'
    obtain ⟨o, ⟨-, hle, -, hn28, -, -⟩, -, -, h10⟩ := hJ
    exact hmem _ (.inr ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 h10⟩) m hF
  · pblk h17 b13_ok p17 chAH_b13
  · have he : (_root_.Executable.labels exe).label ".L2_scc_rt_alloc.5_ok" + Int64.ofNat (4 * 54) =
        (N (_root_.Executable.labels exe).label ms q .ret).pc := by pc_tac
    have hok : Spike.Lib.A64.Flow.okBlk (-160) 0 (N (_root_.Executable.labels exe).label ms q .ret).o
        [iRet.toDir] = true := by dsimp only [N]; decide
    have hch : phOffH (_root_.Executable.labels exe).label pfxM ".L2_scc_rt_alloc.5_ok" 54 rl [iRet.toDir] = true := by
      rcases hrl with rfl | rfl
      · exact phOffHC_sound hlab chAH_retR
      · exact phOffHC_sound hlab chAH_retM
    refine Spike.Lib.LowerA64.BlkW.nodeW (blkW_phStH (Spike.Lib.A64.Flow.code_of hI.lays hI.endOk h18 he) hok
      hR hal (by omega) (by omega) (fun j hj s h1 h2 h3 => ?_) he hch
      (hret_of_run hok fun σ c hJ => ?_)) (List.cons_ne_nil _ _)
    · obtain rfl : j = 0 := by simpa using hj
      rw [Spike.Lib.A64.Flow.ofNat4_zero, ← he] at h3
      exact (hI.off s (by unfold pcOf; rw [h3]; exact p18)).1
    · obtain ⟨o, -, -, -, -, -, h30⟩ := hJ
      have hc : Spike.Lib.A64.Flow.classify iRet.toDir = some iRet := rfl
      simp only [Spike.Lib.A64.Flow.arun, List.foldl, Spike.Lib.A64.Flow.dstep, hc]
      simp [iRet, Spike.Lib.A64.Flow.AI.tgt, Reg64s.getRegOrZr, Reg64s.getRegOrZr64, RegOrZr.base,
        Reg64s.getXReg, h30, hra]

end Spike.Lib.A64.HelloWf

/-- info: 'Spike.Lib.A64.HelloWf.blkW_fullPhH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.blkW_fullPhH

/-- info: 'Spike.Lib.A64.HelloWf.allocAbAcH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloWf.allocAbAcH
