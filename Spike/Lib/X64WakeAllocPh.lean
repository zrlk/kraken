/-
**`scc_rt_alloc` keeps both abort phases in wake.w** (`Wf`'s `AbSt`/`AcSt`,
x86-64; the twin of `Spike/Lib/A64WakeAllocPh.lean`): `allocAbAcW`, every
node of `AllocW` at `AbSt μ (WriteAb.Ab lab) ∧
AcSt μ Cl (ThreadsAb.Ac lab pfxM)`, none moved, for an executable with
`InstOk`, its cells holding the allocator's code (`allocIn`) and passing
its phase check (`allocPhOk`), its labels wake's code labels where they
resolve (`hlab`), for a call returning to `wc_main`'s `.x18` (`hra`).

Every block's and single instruction's targets are off both phases' pcs
(`blkW_phI`, `nodeW_siI`, `nodeW_stepI`; the `ret`'s is `.x18`). The heap
abort's call is `blkW_fullPh` (`Spike/Lib/X64WakeAllocPhC.lean`, with the
checks).

- `nodeW_stepI`: `nodeW_phSt` at an instruction of the program from its
  step (`fi_step`, `xadd_step`, `st_step`).
- `allocAbAcW`.

**Where this differs from AArch64** (forced by the x86-64 shape): the
allocator is x86-64's (31 nodes: the counter's add a `lock xaddq`
through `%rcx`, `ctr_addrS`; the header's store through `%rcx`,
`hdr_addrS`; seven instructions with undefined flags, `fi_step`), so
`nodeW_stepI` stands for A64's inline `nodeW_phSt` uses; offsets are bytes;
the return point is `.Lwc_main.x18` (A64's `.L21_wc_main.sp0`), the return
address at `slot 0` of the `ret`'s node; the region is `[-160, 8)`, no
alignment premise; the checks are in `X64WakeAllocPhC`.
-/
import Spike.Lib.X64WakeAllocPhC

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region MemSide)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At arun)
open Spike.Lib.X64.Rt (InstOk codeOf)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Flow (ofNat_zero')
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.AllocG (allocPhOk allocPhOk_spec allocIn_spec phOne_spec ctr_addrS hdr_addrS)
open Spike.Lib.X64.Alloc (Call AllocW N iRet bPro_ok bChk_ok bJ1_ok bC1_ok bC2_ok bJ2_ok bSlow_ok bJ3_ok
  bO0_ok bO1_ok bO2_ok bO3_ok bO4_ok bO5_ok bO6_ok bO7_ok bO8_ok bO9_ok)

variable {exe : _root_.Executable} [Kraken.Executable.ValidLayout exe] {endPc : Int64}
  {cells : List (Directive × Nat)} {lab : Label → Int64} {μ : Marks} {own : Own} {Tk : State → Prop}
  {K : State → State → Prop} {okPc : Nat → Bool} {ph : Nat → Nat} {kp : Nat} {Cl : State → Prop} {R : Region}
  {F : MachineData → Prop} {ms : MemSide isa} {q : Call} {pfx : String}

omit [Kraken.Executable.ValidLayout exe] in
/-- **`nodeW_phSt` at an instruction of the program** of size `z`, from its
step (`hstep`), its pc off the sites (`hok`). -/
theorem nodeW_stepI (hI : InstOk exe endPc cells (_root_.Executable.labels exe).label μ own Tk K okPc ph kp)
    {n : ND} {l : Label} {k z : Nat} (he : (_root_.Executable.labels exe).label l + Int64.ofNat k = n.pc)
    (hok : okPc ((_root_.Executable.labels exe).label l + Int64.ofNat k).toBitVec.toNat = true)
    (h : siOff (_root_.Executable.labels exe).label pfx l k z = true)
    (hstep : ∀ s c, At exe endPc R F n s c → ∃ d tree, Kraken.Promising.Lower.X64.CellAt s d z ∧
      (∀ w w', d ≠ .instr (.regular w w' .syscall)) ∧ isa.exec s = some tree ∧
      ∀ s', TreeLeaf tree s' → s'.st.2 = s.st.2 + Int64.ofNat z) :
    NodeW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfx) s)
      (fun _ _ => False) exe endPc R F n := by
  intro s c hA
  obtain ⟨-, -, -, hpc, -⟩ := id hA
  have hP := (hI.off s (by unfold pcOf; rw [hpc, ← he]; exact hok)).1
  exact nodeW_phSt he h (fun a ha heq => hP.noTake a ha (by unfold pcOf; rw [hpc]; exact heq)) hstep s c hA

set_option hygiene false in
/-- A `ret`-free block of `scc_rt_alloc` off both phases' pcs. -/
local macro "pblk " hb:term:max ok:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact blkW_phI hI $hb (by pc_tac) $ok hR (by omega) (by omega) $hp (by decide)
    (phOffW_sound hlab $ch))

set_option hygiene false in
/-- A single instruction of `scc_rt_alloc` without an event. -/
local macro "psi " hb:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact nodeW_siI hI $hb (by pc_tac) (phOne_spec $hp).1 (siOffW_sound hlab $ch))

set_option hygiene false in
/-- An instruction of `scc_rt_alloc` with undefined flags. -/
local macro "pfi " hb:term:max hp:term:max ch:term:max : tactic =>
  `(tactic| exact nodeW_stepI hI (by pc_tac) (phOne_spec $hp).1 (siOffW_sound hlab $ch)
    (fi_step hI $hb (by pc_tac)))

set_option maxHeartbeats 800000 in
/-- **`scc_rt_alloc`'s states keep both abort phases** in wake.w, none
moved: its code passing the phase check (`hph`), its labels wake's code
labels (`hlab`), for a call `q` at any allocation site (`hq`) returning to
`wc_main`'s `.x18` (`hra`), in a region of the allocator's frame, the
counter and every header the code may store unmapped in private memory
(`hmem`). -/
theorem allocAbAcW (hI : InstOk exe endPc cells lab μ own Tk K okPc ph kp)
    (hA : Spike.Lib.X64.Alloc.allocIn cells = true) (hph : allocPhOk okPc ph lab = true)
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a → lab l = Int64.ofNat a)
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hq : ∀ m, F m → q.OKS ms lab) (hra : q.ra = (lab (pfxM ++ ".x18")).toBitVec)
    (hmem : ∀ a : BitVec 64,
      (a = BitVec.ofNat 64 ms.ctr ∨ ∃ o, o + ms.units q.n q.τ ≤ ms.cells ∧ a.toNat = q.hdrAt ms o) →
      ∀ m, F m → Mem.loadInt m.dmem a 8 = none) :
    AllocW ms q (fun s _ => AbSt μ (WriteAb.Ab lab) s ∧
      AcSt μ Cl (ThreadsAb.Ac lab pfxM) s) (fun _ _ => False) exe endPc R F := by
  have hl := hI.labOk
  subst hl
  obtain ⟨-, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21,
    h22, h23, h24, h25, h26, h27, h28, h29, h30⟩ := allocIn_spec hA
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16, p17, p18, p19, p20, p21,
    p22, p23, p24, p25, p26, p27, p28, p29, p30, p31⟩ := allocPhOk_spec hph
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · pblk h0 bPro_ok p0 chA_pro
  · pblk h1 bChk_ok p1 chA_chk
  · pblk h2 bJ1_ok p2 chA_j1
  · psi h3 p3 chA_cnt
  · pblk h4 bC1_ok p4 chA_c1
  · refine nodeW_stepI hI (by pc_tac) (phOne_spec p5).1 (siOffW_sound hlab chA_rmw)
      (xadd_step hI (b := .rcx) (i := 0) (r := .rax) h5 (by pc_tac) fun σ c m hJ hF => ?_)
    obtain ⟨-, hcx, -⟩ := hJ
    rw [ctr_addrS (hq m hF) hcx]
    exact hmem _ (.inl rfl) m hF
  · pblk h6 bC2_ok p6 chA_c2
  · pblk h7 bJ2_ok p7 chA_j2
  · pblk h8 bSlow_ok p8 chA_slow
  · pblk h9 bJ3_ok p9 chA_j3
  · -- the heap abort's `movq $2, %rdi; call scc_rt_abort`
    have he : (_root_.Executable.labels exe).label Spike.Lib.X64.Alloc.fullL + Int64.ofNat 0 =
        (N (_root_.Executable.labels exe).label ms q .full).pc := by pc_tac
    have hph10 := p10
    simp only [Spike.Lib.X64.AllocG.aBlk] at hph10
    rw [he] at hph10
    exact blkW_fullPh hlab (fun s hs hn => he ▸ codeOf hI h10 hs hn) rfl rfl hR hlo hhi
      (hpcOf hI Spike.Lib.X64.Alloc.bFull_ok hph10 (by decide))
  · pblk h11 bO0_ok p11 chA_o0
  · pfi h12 p12 chA_f1
  · pblk h13 bO1_ok p13 chA_o1
  · pfi h14 p14 chA_f2
  · pblk h15 bO2_ok p15 chA_o2
  · psi h16 p16 chA_s2
  · pblk h17 bO3_ok p17 chA_o3
  · pfi h18 p18 chA_f3
  · pblk h19 bO4_ok p19 chA_o4
  · pfi h20 p20 chA_f4
  · pblk h21 bO5_ok p21 chA_o5
  · pfi h22 p22 chA_f5
  · pblk h23 bO6_ok p23 chA_o6
  · pfi h24 p24 chA_f6
  · pblk h25 bO7_ok p25 chA_o7
  · pfi h26 p26 chA_f7
  · pblk h27 bO8_ok p27 chA_o8
  · refine nodeW_stepI hI (by pc_tac) (phOne_spec p28).1 (siOffW_sound hlab chA_hdr)
      (st_step hI (b := .rcx) (i := 0) (r := .rax) h28 (by pc_tac) fun σ c m hJ hF => ?_)
    obtain ⟨o, ⟨-, hle, -, hn28, -⟩, -, -, hcx⟩ := hJ
    exact hmem _ (.inr ⟨o.toNat, hle, hdr_addrS (hq m hF) hle hn28 hcx⟩) m hF
  · pblk h29 bO9_ok p29 chA_o9
  · have he : (_root_.Executable.labels exe).label Spike.Lib.X64.Alloc.okL + Int64.ofNat 226 =
        (N (_root_.Executable.labels exe).label ms q .ret).pc := by pc_tac
    have hok : Spike.Lib.X64.okBlk (-160) 8 (N (_root_.Executable.labels exe).label ms q .ret).o
        [(iRet.toDir, 1)] = true := by dsimp only [N]; decide
    refine Spike.Lib.LowerX64.BlkW.nodeW (blkW_phSt (fun s hs hn => he ▸ codeOf hI h30 hs hn) hok
      hR (by omega) (by omega) (fun j hj s h1 h2 h3 => ?_) he (phOffW_sound hlab chA_ret)
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

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.allocAbAcW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.allocAbAcW
