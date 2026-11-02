/-
**hello.w's heap abort path inside `SFactsSt2` at `ownGH`** (x86-64; the
twin of `Spike/Lib/A64HelloHAbWf.lean`, at the template of
`Spike/Lib/X64WakeHAbWf.lean`): the state's facts (`SFactsSt2`, write tail
`WakeWf.DtW`) at every node of `Abort.Disp.HPathW`, at the first instance
(`instOkH`, owned words `ownH L a`, no take phase) and moved to `ownGH` by
`abHAgreeWH` (`Spike/Lib/X64HelloHAbW.lean`). The path's phases are
`abortPhHH`'s. Wake's `WakePh.nodeW_habEx` (the exit call), `WcW.c0N`,
`c0N_cfacts`, `SFactsSt2.mono_dt`, `BlkW.ownCongr2` and
`Tcb2W.nodeW_ownCongr2` are program independent and reused; only the
instance (`instOkW` at `phW`) and the program's cells differ, so the three
node lemmas below are wake's at `instOkH`/`phH`.

- `blkW_habStH`, `nodeW_habSiH`: a block and a single instruction without an
  event of the path at the instance (`Rt.blkW_pre`, `Rt.nodeW_si_pre` at
  `c0N`).
- `nodeW_habWrH`: the stub's `write` (`sfacts_syscallAt` off the sites, the
  tail `dtW_of_fd2`).
- `hpathW_habStH`: `HPathW` inside `SFactsSt2 … DtW` at `ownH`;
  `hpathW_habGH`: at `ownGH`.

**Deviation from the A64 file.** As in `X64WakeHAbWf`: the labels are
`helloCells'` (`codeLabel`, byte offsets); the stub's `leaq` is one node (no
`n1b`); the `write` and exit calls are `syscall`s (`%rdi = 2`, `%rax = 1`;
`%rax = 231`), the exit's cell from the instance (`Rt.cellOf`); the region
is `[-24, 16)`, no alignment premise; `hpathW_habGH`'s two return points are
`.Lscc_rt_alloc_tcb.x6`, `.Lwc_main.x27` (A64's `.sp13`, `.sp15`).
-/
import Spike.Lib.X64HelloHAbW
import Spike.Lib.X64WakeHAbWf

namespace Spike.Lib.X64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.X64
open Scc.Cert.Rt.X64 (codeT codeT_eq blockAtB okPcOf)
open Scc.Sem (Marks Range)
open Scc.Sem.X64 (codeLabel pcOf abi)
open SccCode (helloCells)
open Spike.Lib.X64.Rt (RuntimeLayout)
open Spike.Lib.X64ConsumerA (StSucc SFactsSt2)
open Spike.Lib.X64 (ND BlkW NodeW At SI okBlk)
open Spike.Lib.X64.Abort (NT)
open Spike.Lib.X64.Abort.Disp (DN)
open Spike.Lib.X64.WakeWf (DtW dtW_of_fd2)
open Spike.Lib.X64.StubW (abortPhHeapOk phOne)
open Spike.Lib.X64.WakePh (BandOut nodeW_habEx)
open Spike.Lib.X64.WakePh.WcW (c0N c0N_cfacts)
open Spike.Lib.X64.Flow (ofNat_zero')
open Kraken.Promising.Lower.X64 (CellAt op64)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {R : Region} {F : MachineData → Prop}

section Inst

variable (hp : L.prog = helloCells) (hlo : L.Λ.code.lo = lo)
  (hsite : (Spike.Lib.X64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hsite

/-- **A block of the path inside `SFactsSt2 … DtW` at `ownH`**:
`Rt.blkW_pre` at the first instance with no take phase, at `c0N n`, its
phase check `hph` (`abortPhHH`'s), no `ret`. -/
theorem blkW_habStH (a : BitVec 64) {n : ND} {blk : List (Directive × Nat)} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAtB helloCells l k blk = true) (he : L.lab l + Int64.ofNat k = n.pc)
    (hok : okBlk blo bhi n.o blk = true) (hR : R.OK) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hph : Spike.Lib.X64Consumer.blkPh (okPcOf lo helloCells L.Λ) phH (fun _ => false) L.lab
      (L.lab l + Int64.ofNat k) 0 blk = true)
    (hnr : Spike.Lib.X64Consumer.noRetBlk blk = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hW := Spike.Lib.X64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (Λ := Λ)
    (lbl := fun _ => none) (rS := ⟨0, 0⟩) (F := F) (n := c0N n) (by rw [hp]; exact hb) he hok hR hlo' hhi
    c0N_cfacts hph (fun _ _ _ k hk hr => (Spike.Lib.X64Consumer.noRet_false hnr k hk hr).elim)
    (fun _ _ _ => rfl) (fun _ _ h => h)
  intro s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9
  exact ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt
    (hW s σ Spike.Lib.X64Consumer.c0 a1 a2 a3 a4 a5 a6 ⟨rfl, c, a7⟩ k hk m a8 a9).1.toSt.toSt2
    (fun h => (h : False).elim), fun _ h => h⟩

/-- **A single instruction without an event of the path** inside
`SFactsSt2 … DtW` at `ownH` (`Rt.nodeW_si_pre` at `c0N n`). -/
theorem nodeW_habSiH (a : BitVec 64) {n : ND} {si : SI} {z : Nat} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAtB helloCells l k [(si.toDir, z)] = true) (he : L.lab l + Int64.ofNat k = q) (hq : n.pc = q)
    (hok : okPcOf lo helloCells L.Λ q.toBitVec.toNat = true)
    (hph : phH (q + Int64.ofNat z).toBitVec.toNat = phH q.toBitVec.toNat) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n := by
  have hW := Spike.Lib.X64.Rt.nodeW_si_pre (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (Λ := Λ)
    (lbl := fun _ => none) (rS := ⟨0, 0⟩) (R := R) (F := F) (n := c0N n) (by rw [hp]; exact hb) he hq c0N_cfacts
    hok (fun _ _ h => h) hph
  rintro s c ⟨h1, h2, h3, h4, σ, hA, hF, hJ⟩
  exact ⟨Spike.Lib.X64.WakeWf.SFactsSt2.mono_dt
    (hW s Spike.Lib.X64Consumer.c0 ⟨h1, h2, h3, h4, σ, hA, hF, rfl, c, hJ⟩).1.toSt.toSt2
    (fun h => (h : False).elim), fun _ h => h⟩

/-- **The stub's `write`** (`%rdi = 2`, `%rax = 1`, `hx`) inside
`SFactsSt2 … DtW` at `ownH`: `sfacts_syscallAt` off the sites, its tail
`dtW_of_fd2`. -/
theorem nodeW_habWrH (a : BitVec 64) {n : ND} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAtB helloCells l k [(op64 .syscall, 2)] = true) (he : L.lab l + Int64.ofNat k = q) (hq : n.pc = q)
    (hok : okPcOf lo helloCells L.Λ q.toBitVec.toNat = true)
    (hph : phH (q + Int64.ofNat 2).toBitVec.toNat = phH q.toBitVec.toNat)
    (hx : ∀ σ c, n.J σ c → σ.regs.get64 .rdi = 2#64 ∧ σ.regs.get64 .rax = 1#64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hq] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.X64.Rt.cellOf hI (by rw [hp]; exact hb) he hs hn hpc
  have hnx := Spike.Lib.X64.Rt.next_same hI hpc hph
  obtain ⟨h0, h1⟩ := hx σ c hJ
  rw [← hA.regs] at h0 h1
  have hS := Spike.Lib.X64Consumer.sfacts_syscallAt (Λ := Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.X64.PhRec.μ L) (own := fun s => ownH L a (phH (pcOf s)))
    (Tk := fun s => (fun _ => False) (phH (pcOf s))) (Dt := DtW) (c := Spike.Lib.X64Consumer.c0) (s := s)
    Spike.Lib.X64.Flow.Ret0.Inst.cfacts_c0 hP.noSite hP.noTake hc hnx (fun h => h.elim)
    (fun k a ha e => (hP.noAbort k a ha e).elim)
    (fun _ _ _ _ => dtW_of_fd2 (UInt64.toBitVec_inj.mp h0) (UInt64.toBitVec_inj.mp h1))
  exact ⟨hS.toSt.toSt2, fun _ h => h⟩

/-- **The heap path at `ownH`** inside `SFactsSt2 … DtW`: the abort code of
hello's cells (`hello_abort`), the path's phases (`abortPhHH`), the
dispatcher's region `R` holding the stub's frame `[-24, 16)`. -/
theorem hpathW_habStH (a : BitVec 64) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi) :
    Abort.Disp.HPathW
      (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.X64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hst := hsd.1.1.1.1.2
  simp only [Scc.Cert.Rt.X64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hx0, hn1, hx1, hsysIn, hx2, hx, -, -⟩ := hst
  have hphs := abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [abortPhHeapOk, phOne, Bool.and_eq_true, beq_iff_eq, and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, px0, o1, q1, px1, o34, q34, px2, -⟩ := hphs
  obtain ⟨-, h2⟩ := abH_labsH hlab
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_habStH hp hlo hsite a hd0 (ofNat_zero' _) Abort.Disp.d0_ok hR (by omega) (by omega) pd0 (by decide)
  · exact blkW_habStH hp hlo hsite a ht1 (ofNat_zero' _) Abort.Disp.t1_ok hR (by omega) (by omega) pt1 (by decide)
  · exact blkW_habStH hp hlo hsite a hj1 rfl Abort.Disp.j1_ok hR (by omega) (by omega) pj1 (by decide)
  · exact blkW_habStH hp hlo hsite a ht2 (ofNat_zero' _) Abort.Disp.t2_ok hR (by omega) (by omega) pt2 (by decide)
  · exact blkW_habStH hp hlo hsite a hg2 (ofNat_zero' _) Abort.Disp.g2_ok hR (by omega) (by omega) pg2 (by decide)
  · exact blkW_habStH hp hlo hsite a hx0 (ofNat_zero' _) Abort.x0_ok hR (by omega) (by omega) px0 (by decide)
  · exact nodeW_habSiH hp hlo hsite a hn1 rfl (ofNat_zero' _).symm o1 q1
  · exact blkW_habStH hp hlo hsite a hx1 rfl Abort.x1Heap_ok hR (by omega) (by omega) px1 (by decide)
  · exact nodeW_habWrH hp hlo hsite a hsysIn rfl rfl o34 q34 fun _ _ hJ => ⟨hJ.2.1, hJ.2.2⟩
  · exact blkW_habStH hp hlo hsite a hx2 rfl Abort.x2_ok hR (by omega) (by omega) px2 (by decide)
  · refine nodeW_habEx (fun s hs hn hpc => Spike.Lib.X64.Rt.cellOf hI (by rw [hp]; exact hx) (ofNat_zero' _) hs hn
      hpc) (fun a' ha => ?_) (fun a' ha => ?_) fun _ _ hJ => hJ.2.1
    · have e : (Spike.Lib.X64.PhRec.μ L).site .release = some 4200354 := by
        show codeLabel L.Λ.code.lo L.prog "scc_rt_release_site" = _; rw [hp, hlo, ← codeT_eq]; decide +kernel
      rw [e] at ha; cases ha
      simp only [NT, Abort.heap, h2]; decide
    · have e : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
        hlab _ _ (by rw [← codeT_eq]; decide +kernel)
      rw [hsite] at ha; cases ha
      simp only [NT, Abort.heap, h2, e]; decide

/-- **The heap path at `ownGH`** inside `SFactsSt2 … DtW`: `hpathW_habStH`
moved by `abHAgreeWH`, from a caller other than the two return points
`ownGH` reads on it (`h6`, `h27`). -/
theorem hpathW_habGH (a : BitVec 64) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeLabel lo helloCells l = some x → L.lab l = Int64.ofNat x) {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hlo' : R.lo ≤ -24) (hhi : 16 ≤ R.hi)
    (h6 : ra = (L.lab ".Lscc_rt_alloc_tcb.x6").toBitVec → BandOut L R)
    (h27 : ra ≠ (L.lab ".Lwc_main.x27").toBitVec) :
    Abort.Disp.HPathW (fun s _ => SFactsSt2 Λ (Spike.Lib.X64.PhRec.μ L) (ownGH L a) s DtW)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.X64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -⟩ := ab_labsH hlab
  have hP := abPHH (μ := Spike.Lib.X64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hlab hR hlo' hhi
    (fun a' ha => by
      have e : L.lab Spike.Lib.X64.Flow.Ret0.StackTake.siteL = Int64.ofNat 4200314 :=
        hlab _ _ (by rw [← codeT_eq]; decide +kernel)
      rw [hsite] at ha; cases ha
      rw [e, e1, e2]; decide)
    (Scc.Cert.Rt.X64.Abort.code_disp L.lays rfl (by rw [hp]; exact hsd.2))
    (Scc.Cert.Rt.X64.Abort.code_stub L.lays rfl (by rw [hp]; exact hsd.1.1.1.1.2))
  have hg := abHAgreeWH hlab (a := a) hP h6 h27
  have hw := hpathW_habStH hp hlo hsite (Λ := Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hlo' hhi
  exact ⟨Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.de hg.de, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dt1 hg.dt1,
    Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dj1 hg.dj1, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dt2 hg.dt2,
    Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.dg2 hg.dg2, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.se hg.se,
    Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 hw.sn1 hg.sn1, Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.sn2 hg.sn2,
    Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 hw.ssys hg.ssvc,
    Spike.Lib.X64ConsumerA.BlkW.ownCongr2 hw.sn5 hg.sn5, Spike.Lib.X64.WakePh.Tcb2W.nodeW_ownCongr2 hw.sex hg.sex⟩

end Inst

end Spike.Lib.X64.HelloPh

/-- info: 'Spike.Lib.X64.HelloPh.blkW_habStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.blkW_habStH

/-- info: 'Spike.Lib.X64.HelloPh.nodeW_habSiH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.nodeW_habSiH

/-- info: 'Spike.Lib.X64.HelloPh.nodeW_habWrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.nodeW_habWrH

/-- info: 'Spike.Lib.X64.HelloPh.hpathW_habStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hpathW_habStH

/-- info: 'Spike.Lib.X64.HelloPh.hpathW_habGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64.HelloPh.hpathW_habGH
