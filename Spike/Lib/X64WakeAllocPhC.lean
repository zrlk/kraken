/-
**`scc_rt_alloc`'s phase checks in wake.w and the heap abort's call**
(`Wf`'s `AbSt`/`AcSt`, x86-64; the checks and `blkW_fullPh` of
`Spike/Lib/A64WakeAllocPh.lean`, whose `allocAbAcW` is
`Spike/Lib/X64WakeAllocPh.lean`'s): every block's and single instruction's
targets off both phases' pcs (`phOffW`, `siOffW`; the `ret`'s is
`wc_main`'s `.x18`), each decided at wake's code labels. The heap abort's
`movq $2, %rdi; call scc_rt_abort` (`.full`) enters the dispatcher's
prologue with `%rdi = 2` (out of the write abort's `4` and the threads
abort's `5`) and the return address it pushes past itself (not `raT`,
`hra_alloc`); its targets are off both phases' other pcs (`dChk`,
`chA_full`), and read the pushed word only at the dispatcher's entry
(`rChk`, `rA_full`).

- `chA_*`, `rA_full`: the checks.
- `sp0_slotG`: `0(%rsp)` is the abstract state's slot at `%rsp`'s offset.
- `blkW_fullPh`.

**Where this differs from AArch64** (forced by the x86-64 shape):
- the allocator is x86-64's (31 nodes, `X64Alloc`): eighteen blocks and
  eleven single instructions (seven with undefined flags, the counter's
  `lock xaddq`, the header's store, two moves), offsets in bytes;
- the return point is `.Lwc_main.x18` (A64's `.L21_wc_main.sp0`);
- the call's return address is the word it pushes at `slot (-160)`, read by
  `ThreadsAb.RaW` at `0(%rsp)` (`sp0_slotG`, `rA_full`), not `x30`
  (A64's `ac_x30`, `b9_x30`); the target is out of the threads abort's
  dispatcher clause by `%rdi = 2 ≠ 5` and of its stub clauses by `RaW`;
- the checks are split from `allocAbAcW` (`X64WakeAllocPh`) to keep each
  file's kernel decisions apart; no alignment premise; the region is
  `[-160, 8)`.
-/
import Spike.Lib.X64WakeWfHPA
import Spike.Lib.X64WakeWfW
import Spike.Lib.X64AllocGS

namespace Spike.Lib.X64.WakeWf

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib (Region)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Spike.Lib.X64 (NodeW BlkW ND At CodeAt cellOff arun classify AS SO Abs)
open Spike.Lib.X64.WakePh.StartWf (pfxM)
open Spike.Lib.X64.Flow (ofNat_zero')
open Scc.Sem.X64 (codeLabel)
open SccCode (wakeCells)
open Spike.Lib.X64.Alloc (iRet fnL entryL cntL slowL fullL okL bPro bChk bJ1 bC1 bC2 bJ2 bSlow bJ3 bFull bO0 bO1
  bO2 bO3 bO4 bO5 bO6 bO7 bO8 bO9)

/-! ## The checks at wake's code labels -/

local macro "ph_dec" : tactic => `(tactic| (unfold phOffW; decide +kernel))
local macro "si_dec" : tactic => `(tactic| (unfold siOffW; decide +kernel))

theorem chA_pro : phOffW pfxM fnL 0 fnL bPro = true := by ph_dec
theorem chA_chk : phOffW pfxM entryL 0 entryL bChk = true := by ph_dec
theorem chA_j1 : phOffW pfxM entryL 16 entryL bJ1 = true := by ph_dec
theorem chA_cnt : siOffW pfxM cntL 0 7 = true := by si_dec
theorem chA_c1 : phOffW pfxM cntL 7 cntL bC1 = true := by ph_dec
theorem chA_rmw : siOffW pfxM cntL 19 5 = true := by si_dec
theorem chA_c2 : phOffW pfxM cntL 24 cntL bC2 = true := by ph_dec
theorem chA_j2 : phOffW pfxM cntL 59 cntL bJ2 = true := by ph_dec
theorem chA_slow : phOffW pfxM slowL 0 slowL bSlow = true := by ph_dec
theorem chA_j3 : phOffW pfxM slowL 16 slowL bJ3 = true := by ph_dec
theorem chA_full : dChkW pfxM fullL 0 [1] [] bFull = true := by
  unfold dChkW; decide +kernel
theorem rA_full : rChkW fullL 0 [1] [] [] bFull = true := by
  unfold rChkW; decide +kernel
theorem chA_o0 : phOffW pfxM okL 0 okL bO0 = true := by ph_dec
theorem chA_f1 : siOffW pfxM okL 11 3 = true := by si_dec
theorem chA_o1 : phOffW pfxM okL 14 okL bO1 = true := by ph_dec
theorem chA_f2 : siOffW pfxM okL 29 3 = true := by si_dec
theorem chA_o2 : phOffW pfxM okL 32 okL bO2 = true := by ph_dec
theorem chA_s2 : siOffW pfxM okL 36 7 = true := by si_dec
theorem chA_o3 : phOffW pfxM okL 43 okL bO3 = true := by ph_dec
theorem chA_f3 : siOffW pfxM okL 58 3 = true := by si_dec
theorem chA_o4 : phOffW pfxM okL 61 okL bO4 = true := by ph_dec
theorem chA_f4 : siOffW pfxM okL 88 4 = true := by si_dec
theorem chA_o5 : phOffW pfxM okL 92 okL bO5 = true := by ph_dec
theorem chA_f5 : siOffW pfxM okL 107 3 = true := by si_dec
theorem chA_o6 : phOffW pfxM okL 110 okL bO6 = true := by ph_dec
theorem chA_f6 : siOffW pfxM okL 125 3 = true := by si_dec
theorem chA_o7 : phOffW pfxM okL 128 okL bO7 = true := by ph_dec
theorem chA_f7 : siOffW pfxM okL 140 3 = true := by si_dec
theorem chA_o8 : phOffW pfxM okL 143 okL bO8 = true := by ph_dec
theorem chA_hdr : siOffW pfxM okL 170 3 = true := by si_dec
theorem chA_o9 : phOffW pfxM okL 173 okL bO9 = true := by ph_dec
theorem chA_ret : phOffW pfxM okL 226 (pfxM ++ ".x18") [(iRet.toDir, 1)] = true := by ph_dec

/-! ## The heap abort's call -/

/-- **`0(%rsp)` is the slot at `%rsp`'s offset.** -/
theorem sp0_slotG {R : Region} {o : SO} {s : State} {σ : AS} (hA : Abs R o s.st.1 σ) (hoff : R.Off o.sp) :
    ThreadsAb.spLoad s 0 = some (σ.slot o.sp) := by
  obtain ⟨j, hj, hjv⟩ := hA.slot o.sp hoff
  have hsp := hA.so .rsp o.sp (by simp [SO.get])
  rw [← hA.regs] at hsp
  simp only [Reg64s.get64] at hsp
  have a0 : R.addr o.sp + (0 : BitVec 64) = R.addr o.sp := BitVec.add_zero _
  simp only [ThreadsAb.spLoad, Scc.Sem.X64.privLoad, hsp, a0, hj, Option.map_some, hjv]

section Full

variable {μ : Marks} {Cl : State → Prop} {exe : _root_.Executable} {endPc : Int64} {R : Region}
  {F : MachineData → Prop}

set_option maxHeartbeats 800000 in
/-- **`.full`'s `movq $2, %rdi; call scc_rt_abort` keeps both phases**:
its pcs off the marks' sites (`hpc`), its targets off both phases' pcs but
the dispatcher's prologue (`chA_full`), entered at `%rdi = 2` with the
return address pushed past the call (`rA_full`, `hra_alloc`). -/
theorem blkW_fullPh {n : ND}
    (hlab : ∀ l a, codeLabel Spike.Lib.X64.WakePh.lo wakeCells l = some a →
      (_root_.Executable.labels exe).label l = Int64.ofNat a)
    (hcode : ∀ s : State, s.exe = exe → s.endPc = endPc → CodeAt s n.pc bFull)
    (hnp : n.pc = (_root_.Executable.labels exe).label fullL) (hno : n.o = Spike.Lib.X64.Alloc.oI)
    (hR : R.OK) (hlo : R.lo ≤ -160) (hhi : 8 ≤ R.hi)
    (hpc : ∀ j < bFull.length, ∀ s : State, s.exe = exe → s.endPc = endPc →
      s.st.2 = n.pc + Int64.ofNat (cellOff bFull j) → PcOff μ s) :
    BlkW (fun s _ => AbSt μ (WriteAb.Ab (_root_.Executable.labels exe).label) s ∧
      AcSt μ Cl (ThreadsAb.Ac (_root_.Executable.labels exe).label pfxM) s)
      (fun _ _ => False) exe endPc R F n bFull := by
  have hok : Spike.Lib.X64.okBlk (-160) 8 n.o bFull = true := by rw [hno]; exact Spike.Lib.X64.Alloc.bFull_ok
  have hd := dChkW_sound (lab := (_root_.Executable.labels exe).label) hlab chA_full
  rw [ofNat_zero', ← hnp] at hd
  have hr := rChkW_sound (lab := (_root_.Executable.labels exe).label) hlab rA_full
  rw [ofNat_zero', ← hnp] at hr
  have hrun : ∀ σ, arun (_root_.Executable.labels exe).label (bFull.take (1 + 1)) ⟨n.pc, n.o, σ⟩ =
      arun (_root_.Executable.labels exe).label bFull ⟨n.pc, Spike.Lib.X64.Alloc.oI, σ⟩ := fun σ => by
    rw [hno]; rfl
  refine blkW_dispPh hcode hok hR hlo hhi ⟨by decide, by omega, by omega⟩ hpc (by decide) hd
    (fun σ c _ k hk hkE => ?_) (fun _ _ _ _ _ h => by simp at h) (fun σ c _ k hk a ha s' hs' hA hW => ?_)
  · obtain rfl : k = 1 := by simpa using hkE
    rw [hrun, Spike.Lib.X64.Alloc.bFull_run]
    simp [Reg64s.set64, Reg64s.get64]
  · have hk' := List.all_eq_true.mp hr k (List.mem_range.mpr hk)
    simp only [List.getElem?_eq_getElem hk, ha] at hk'
    have h' := List.all_eq_true.mp hk' _ hs'
    simp only [rOk, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not, decide_eq_true_eq] at h'
    obtain ⟨⟨h1, h2⟩, h3⟩ := h'
    rcases hW with ⟨hm, hl⟩ | ⟨hm, -⟩ | ⟨hm, -⟩
    · obtain rfl : k = 1 := by simpa using h1.resolve_left fun hn => hn hm
      rw [hrun, Spike.Lib.X64.Alloc.bFull_run] at hA
      rw [sp0_slotG hA (show R.Off (-160) from ⟨by decide, by omega, by omega⟩)] at hl
      simp only [Spike.Lib.upd_apply, ite_true, Option.some.injEq] at hl
      refine hra_alloc hlab ?_
      rw [← hnp]
      exact hl
    · exact absurd (h2.resolve_left fun hn => hn hm) (by simp)
    · exact absurd (h3.resolve_left fun hn => hn hm) (by simp)

end Full

end Spike.Lib.X64.WakeWf

/-- info: 'Spike.Lib.X64.WakeWf.chA_full' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.chA_full

/-- info: 'Spike.Lib.X64.WakeWf.blkW_fullPh' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakeWf.blkW_fullPh
