/-
**wake.w's heap abort path inside `SFactsSt2` at `ownG`** (x86-64; the twin
of `Spike/Lib/A64WakeHAbWf.lean`): the state's facts (`SFactsSt2`, write
tail `WakeWf.DtW`) at every node of `Abort.Disp.HPathW`, at the first
instance (`instOkW`, owned words `ownW L a`, no take phase) and moved to
`ownG` by `abHAgreeW` (`Spike/Lib/X64WakeHAbW.lean`). The path's phases are
`abortPhHW`'s.

- `abortHTabW`, `abortHFactsW`, `abortPhHW`: the heap abort path's phase
  check (`StubW.abortPhHeapOk`) at `phW`, from the certificate's table.
- `blkW_habSt`, `nodeW_habSi`: a block and a single instruction without an
  event of the path at the instance (`Rt.blkW_pre`, `Rt.nodeW_si_pre` at
  `WcW.c0N`).
- `nodeW_habWr`: the stub's `write` (`sfacts_syscallAt` off the sites, the
  tail `dtW_of_fd2`).
- `nodeW_habEx`: the exit call (`exit_group`, off the release and take
  sites).
- `hpathW_habSt`: `HPathW` inside `SFactsSt2 … DtW` at `ownW`;
  `hpathW_habG`: at `ownG`.

**Where this differs from AArch64** (forced by the x86-64 shape): the
labels are `wakeCells`' (`codeLabel`, byte offsets: `j1` at `.entry + 16`,
the stub's `leaq` at `entry + 0` (7 bytes), its block at `+ 7`, the
`syscall` at `+ 34` (2 bytes), the last block at `+ 36`); the stub's `leaq`
is one node (A64's `adrp`/`add`, so no `nodeW_habSi` at `n1b`); the `write`
and exit calls are `syscall`s (`%rdi = 2`, `%rax = 1`; `%rax = 231`), the
exit's cell from the instance (`Rt.cellOf`); the region is `[-24, 16)`, no
alignment premise; the table's exit-call phase equation is decided on the
resolved exit label (A64's two `.ph` facts); the instance's take phase
index is `fun _ => False` as A64's; `hpathW_habG`'s two return points are
`.Lscc_rt_alloc_tcb.x5`, `.Lwc_main.x23` (A64's `.sp13`, `.sp11`).
-/
import Spike.Lib.X64WakeHAbW
import Spike.Lib.X64WakeWcPreWN
import Spike.Lib.X64WakeWfHPA
import Spike.Lib.X64WakeCode

namespace Spike.Lib.X64.WakePh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB PhFact factOk deadN okPcOf)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (wakeCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At SI okBlk)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN)
open Spike.Lib.X64.WakeWf (DtW dtW_of_fd2)
open Spike.Lib.X64.StubW (abortPhHeapOk phOne)
open Spike.Lib.X64.Rt.PhOfTab (blkPh_of_factOk step_of_factOk)
open Spike.Lib.X64.WakePh.WcW (c0N c0N_cfacts)
open Spike.Lib.X64.Flow (ofNat_zero')
open Kraken.Promising.Lower.X64 (CellAt op64)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {R : Region} {F : MachineData → Prop}

/-! ## The path's phase check at `phW` -/

/-- **The heap abort path's facts** (`abortPhHeapOk`'s but the exit
call's), as the certificate's table. -/
def abortHTabW : List PhFact :=
  [.blk "scc_rt_abort" 0 Abort.Disp.d0 none none, .blk ".Lscc_rt_abort.entry" 0 Abort.Disp.t1 none none,
   .blk ".Lscc_rt_abort.entry" 16 Abort.Disp.j1 none none,
   .blk ".Lscc_rt_abort.next1" 0 Abort.Disp.t2 none none,
   .blk ".Lscc_rt_abort.is2" 0 Abort.Disp.g2 none none, .blk "scc_rt_abort_heap" 0 Abort.x0 none none,
   .step ".Lscc_rt_abort_heap.entry" 0 7, .blk ".Lscc_rt_abort_heap.entry" 7 Abort.x1Heap none none,
   .step ".Lscc_rt_abort_heap.entry" 34 2, .blk ".Lscc_rt_abort_heap.entry" 36 Abort.x2 none none]

/-- The table's facts hold at the resolved phases. -/
theorem abortHFactsW : abortHTabW.all (factOk (codeT lo wakeCells) okC phC) = true := by
  decide +kernel

/-- **`abortPhHeapOk` at `phW`** with the certificate's labels. -/
theorem abortPhHW {lab : Label → Int64} (hΛ : Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → lab l = Int64.ofNat x) :
    abortPhHeapOk (okPcOf lo wakeCells Λ) phW lab = true := by
  have h := abortHFactsW
  rw [codeT_eq, ← okPc_eq hΛ, ← phW_eq] at h
  simp only [abortHTabW, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨f0, f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := h
  have hr : ∀ r o', (none : Option (String × Nat)) = some (r, o') → (0 : Int64) = lab r + Int64.ofNat o' :=
    fun _ _ h => by cases h
  have hn : ∀ t, deadN (codeLabel lo wakeCells) none t = true → (fun _ => false) t = true :=
    fun _ h => by simp [deadN] at h
  have so : ∀ {l : String} {o z : Nat},
      factOk (codeLabel lo wakeCells) (okPcOf lo wakeCells Λ) phW (.step l o z) = true →
      phOne (okPcOf lo wakeCells Λ) phW (lab l + Int64.ofNat o) z = true := fun h => by
    obtain ⟨h1, h2⟩ := step_of_factOk hlab h
    simp only [phOne, h1, h2, beq_self_eq_true, Bool.and_self]
  have hex : lab "scc_rt_abort_heap_exit" = Int64.ofNat 4202723 := hlab _ _ (by rw [← codeT_eq]; decide +kernel)
  unfold abortPhHeapOk
  simp only [Abort.heap]
  rw [blkPh_of_factOk hlab hr hn f0, blkPh_of_factOk hlab hr hn f1, blkPh_of_factOk hlab hr hn f2,
    blkPh_of_factOk hlab hr hn f3, blkPh_of_factOk hlab hr hn f4, blkPh_of_factOk hlab hr hn f5, so f6,
    blkPh_of_factOk hlab hr hn f7, so f8, blkPh_of_factOk hlab hr hn f9, hex, phW_eq]
  decide +kernel

section Inst

variable (hp : L.prog = wakeCells) (hlo : L.Λ.code.lo = lo)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hsite

/-- **A block of the path inside `SFactsSt2 … DtW` at `ownW`**:
`Rt.blkW_pre` at the first instance with no take phase, at `c0N n`, its
phase check `hph` (`abortPhHW`'s), no `ret`. -/
theorem blkW_habSt (a : BitVec 64) {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB wakeCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hph : Spike.Lib.X64Consumer.blkPh (okPcOf lo wakeCells L.Λ) phW (fun _ => false) L.lab
      (L.lab l + Int64.ofNat k) 0 blk = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hW := Spike.Lib.X64.Rt.blkW_pre (instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (Λ := Λ)
    (lbl := fun _ => none) (rS := ⟨0, 0⟩) (F := F) (n := c0N n) (by rw [hp]; exact hb) he hok hR hlo' hhi
    c0N_cfacts hph (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim)
    (fun _ _ _ => rfl) (fun _ _ h => h)
  intro s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
  exact ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt
    (hW s σ Spike.Lib.X64Consumer.c0 a1 a2 a3 a4 a5 a6 ⟨rfl, c, a7⟩ k hk m a8 a9).1.toSt.toSt2
    (fun h => (h : False).elim), fun _ h => h⟩

/-- **A single instruction without an event of the path** inside
`SFactsSt2 … DtW` at `ownW` (`Rt.nodeW_si_pre` at `c0N n`). -/
theorem nodeW_habSi (a : BitVec 64) {n : ND} {si : SI} {z : Nat} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAtB wakeCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = q) (hq : n.pc = q)
    (hok : okPcOf lo wakeCells L.Λ q.toBitVec.toNat = true)
    (hph : phW (q + Int64.ofNat z).toBitVec.toNat = phW q.toBitVec.toNat) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n := by
  have hW := Spike.Lib.X64.Rt.nodeW_si_pre (instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (Λ := Λ)
    (lbl := fun _ => none) (rS := ⟨0, 0⟩) (R := R) (F := F) (n := c0N n) (by rw [hp]; exact hb) he hq c0N_cfacts
    hok (fun _ _ h => h) hph
  rintro s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩
  exact ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt
    (hW s Spike.Lib.X64Consumer.c0 ⟨h1, h2, h3, h4, σ, hA, hF, rfl, c, hJ⟩).1.toSt.toSt2
    (fun h => (h : False).elim), fun _ h => h⟩

/-- **The stub's `write`** (`%rdi = 2`, `%rax = 1`, `hx`) inside
`SFactsSt2 … DtW` at `ownW`: `sfacts_syscallAt` off the sites, its tail
`dtW_of_fd2`. -/
theorem nodeW_habWr (a : BitVec 64) {n : ND} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAtB wakeCells l k [(op64 .syscall, 2)] = true) (he : L.lab l + Int64.ofNat k = q) (hq : n.pc = q)
    (hok : okPcOf lo wakeCells L.Λ q.toBitVec.toNat = true)
    (hph : phW (q + Int64.ofNat 2).toBitVec.toNat = phW q.toBitVec.toNat)
    (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rdi = 2#64 ∧ σ.regs.get64 .rax = 1#64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hq] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI (by rw [hp]; exact hb) he hs hn hpc
  have hnx := Spike.Lib.X64.Rt.next_same hI hpc hph
  obtain ⟨h0, h1⟩ := hx σ c hJ
  rw [← hA.regs] at h0 h1
  have hS := Spike.Lib.X64Consumer.sfacts_syscallAt (Λ := Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.X64.PhRec.μ L) (own := fun s => ownW L a (phW (pcOf s)))
    (Tk := fun s => (fun _ => False) (phW (pcOf s))) (Dt := DtW) (c := Spike.Lib.X64Consumer.c0) (s := s)
    Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hP.noSite hP.noTake hc hnx (fun h => h.elim)
    (fun k a ha e => (hP.noAbort k a ha e).elim)
    (fun _ _ _ _ => dtW_of_fd2 (UInt64.toBitVec_inj.mp h0) (UInt64.toBitVec_inj.mp h1))
  exact ⟨hS.toSt.toSt2, fun _ h => h⟩

omit hp hlo hsite in
/-- **The exit call** (`%rax = 231`, `hx`) inside `SFactsSt2 … DtW` at any
owned words: an `exit_group` (no resumed state, no `write`), off the
release and take sites (`hrel`, `htk`). -/
theorem nodeW_habEx {μ : Marks} {own : Spike.Lib.X64Consumer.Own} {exe : _root_.Executable} {endPc : Int64}
    {n : ND} (hc : ∀ s : State, s.exe = exe → s.endPc = endPc → s.st.2 = n.pc → CellAt s (op64 .syscall) 2)
    (hrel : ∀ a, μ.site .release = some a → n.pc.toBitVec.toNat ≠ a)
    (htk : ∀ a, μ.site .take = some a → n.pc.toBitVec.toNat ≠ a)
    (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rax = 231#64) :
    NodeW (fun s _ => SFactsSt2 Λ μ own s DtW) (fun _ _ => False) exe endPc R F n := by
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  have hcell := hc s hs hn hpc
  have hsys : abi.atSys s = true := Scc.Sem.X64.atSyscall_of_cellAt hcell
  have hpcN : pcOf s = n.pc.toBitVec.toNat := by unfold pcOf; rw [hpc]
  have hr : s.st.1.regs.rax.toNat = 231 := by
    have h231 := hx σ c hJ
    rw [← hA.regs] at h231
    simp only [Reg64s.get64] at h231
    rw [← UInt64.toNat_toBitVec, h231]; rfl
  have hd : Scc.Sem.Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.exitGroup s.st.1.regs.rdi.toNat) := by
    rw [← Spike.Lib.X64.syscallCall_exitGroup hr]; rfl
  refine ⟨⟨fun a ha => by rw [hpcN]; exact hrel a ha, fun h => (by rw [hsys] at h; cases h),
    fun _ => ⟨2, hcell⟩, fun h => (by rw [hsys] at h; cases h), fun _ call hd' s' hs' => ?_,
    fun a ha hp => (htk a ha (hpcN ▸ hp)).elim, fun a ha hp => (htk a ha (hpcN ▸ hp)).elim,
    fun _ fd buf k hw => ?_⟩, fun _ h => h⟩
  · rw [hd] at hd'; cases hd'
    rw [Spike.Lib.X64.certSuccs_exitGroup] at hs'; cases hs'
  · rw [hd] at hw; cases hw

/-- **The heap path at `ownW`** inside `SFactsSt2 … DtW`: the abort code of
wake's cells (`wake_abort`), the path's phases (`abortPhHW`), the
dispatcher's region `R` holding the stub's frame `[-24, 16)`. -/
theorem hpathW_habSt (a : BitVec 64) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    Abort.Disp.HPathW
      (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownW L a (phW (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkW hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hsd := SccCode.wake_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  have hphs := abortPhHW (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, px0, o1, q1, px1, o34, q34, px2, -⟩ := hphs
  obtain ⟨-, h2⟩ := abH_labs hlab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_habSt hp hlo hsite a hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR (by omega) (by omega) pd0 (by decide)
  · exact blkW_habSt hp hlo hsite a ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR (by omega) (by omega) pt1 (by decide)
  · exact blkW_habSt hp hlo hsite a hj1 rfl Abort.Disp.j1_ok hR (by omega) (by omega) pj1 (by decide)
  · exact blkW_habSt hp hlo hsite a ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega) pt2 (by decide)
  · exact blkW_habSt hp hlo hsite a hg2 (ofNat_zero' _) Abort.Disp.g2_ok hR (by omega) (by omega) pg2 (by decide)
  · exact blkW_habSt hp hlo hsite a hx0 (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega) px0 (by decide)
  · exact nodeW_habSi hp hlo hsite a hn1 rfl (ofNat_zero' _).symm o1 q1
  · exact blkW_habSt hp hlo hsite a hx1 rfl Abort.x1Heap_ok hR (by omega) (by omega) px1 (by decide)
  · exact nodeW_habWr hp hlo hsite a hsysIn rfl rfl o34 q34 fun _ _ hJ => ⟨hJ.2.1, hJ.2.2⟩
  · exact blkW_habSt hp hlo hsite a hx2 rfl Abort.x2_ok hR (by omega) (by omega) px2 (by decide)
  · refine nodeW_habEx (fun s hs hn hpc => Spike.Lib.X64.Rt.cellOf hI (by rw [hp]; exact hx) (ofNat_zero' _) hs hn
      hpc) (fun a' ha => ?_) (fun a' ha => ?_) fun _ _ hJ => hJ.2.1
    · have e : (Spike.Lib.X64.PhRec.μ L).site .release = some 4200317 := by
        show codeLabel L.Λ.code.lo L.prog "scc_rt_release_site" = _; rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha
      simp only [NT, Abort.heap, h2]; decide
    · have e : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
        hlab _ _ (by rw [← codeT_eq]; decide +kernel)
      rw [hsite] at ha; cases ha
      simp only [NT, Abort.heap, h2, e]; decide

/-- **The heap path at `ownG`** inside `SFactsSt2 … DtW`: `hpathW_habSt`
moved by `abHAgreeW`, from a caller other than the two return points
`ownG` reads on it (`h5`, `h23`). -/
theorem hpathW_habG (a : BitVec 64) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo wakeCells l = some x → L.lab l = Int64.ofNat x) {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (h5 : ra = (L.lab ".Lscc_rt_alloc_tcb.x5").toBitVec → BandOut L R)
    (h23 : ra ≠ (L.lab ".Lwc_main.x23").toBitVec) :
    Abort.Disp.HPathW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownG L a) s DtW)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hsd := SccCode.wake_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -⟩ := ab_labs hlab
  have hP := abPH (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hlab hR hlo' hhi
    (fun a' ha => by
      have e : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200277 :=
        hlab _ _ (by rw [← codeT_eq]; decide +kernel)
      rw [hsite] at ha; cases ha
      rw [e, e1, e2]; decide)
    (Scc.Cert.Rt.X64.Abort.code_disp L.lays rfl (by rw [hp]; exact hsd.2))
    (Scc.Cert.Rt.X64.Abort.code_stub L.lays rfl (by rw [hp]; exact hsd.1.1.1.1.2))
  have hg := abHAgreeW hlab (a := a) hP h5 h23
  have hw := hpathW_habSt hp hlo hsite (Λ := Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hlo' hhi
  exact ⟨Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.de hg.de, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dt1 hg.dt1,
    Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dj1 hg.dj1, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dt2 hg.dt2,
    Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dg2 hg.dg2, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.se hg.se,
    Tcb2W.nodeW_ownCongr2 hw.sn1 hg.sn1, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.sn2 hg.sn2,
    Tcb2W.nodeW_ownCongr2 hw.ssys hg.ssvc, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.sn5 hg.sn5,
    Tcb2W.nodeW_ownCongr2 hw.sex hg.sex⟩

end Inst

end Spike.Lib.X64.WakePh

/-- info: 'Spike.Lib.X64.WakePh.abortPhHW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.abortPhHW

/-- info: 'Spike.Lib.X64.WakePh.blkW_habSt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.blkW_habSt

/-- info: 'Spike.Lib.X64.WakePh.nodeW_habWr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeW_habWr

/-- info: 'Spike.Lib.X64.WakePh.nodeW_habEx' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.nodeW_habEx

/-- info: 'Spike.Lib.X64.WakePh.hpathW_habG' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.WakePh.hpathW_habG
