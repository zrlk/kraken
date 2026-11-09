/-
**hello.w's heap abort path inside `SFactsSt2` at `ownGH`** (AArch64; the twin
of `A64WakeHAbWf` at `SccCode.helloProg`): the state's facts (`SFactsSt2`, write tail `WakeWf.DtW`) at every node
of `Abort.Disp.HPathW`, at the first instance (`instOkH`, owned words `ownH L a`, no take phase) and moved to
`ownGH` by `abHAgreeWH` (`Spike/Lib/A64HelloHAbW.lean`). The path's phases are `abortPhHH`'s.

wake's `WakePh.nodeW_habEx` (the exit call), `WcW.c0N`, `c0N_cfacts`, `blkW_mapC`, `nodeW_mapC`,
`BlkW.ownCongr2` and `Tcb2W.nodeW_ownCongr2` are program independent and reused; only the instance (`instOkW` at
`phW`) and the program's blocks differ, so the three node lemmas below are wake's at `instOkH`/`phH`.

- `blkW_habStH`, `nodeW_habSiH`: a block and a single instruction without an event of the path at the instance
  (`blkW_pre`, `nodeW_si_pre` at `c0N`).
- `nodeW_habWrH`: the stub's `write` (`sfacts_svcAt`, the tail `dtW_of_fd2`).
- `hpathW_habStH`: `HPathW` inside `SFactsSt2 … DtW` at `ownH`; `hpathW_habGH`: at `ownGH`.
-/
import Spike.Lib.A64HelloHAbW
import Spike.Lib.A64WakeHAbWf

namespace Spike.Lib.A64.HelloPh

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Cert.Rt.A64 (codeT codeT_eq blockAt okPcOf)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64.Print (add4 add0)
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf abi)
open Spike.Lib.A64.Rt (RuntimeLayout)
open Spike.Lib.A64ConsumerA (StSucc SFactsSt2 BlkW.ownCongr2)
open Spike.Lib.A64.Flow (ND BlkW NodeW At SI svcDir)
open Spike.Lib.A64.Abort (NT)
open Spike.Lib.A64.Abort.Disp (DN)
open Spike.Lib.A64.WakeWf (DtW dtW_of_fd2)
open Spike.Lib.A64.WakePh.WcW (c0N c0N_cfacts blkW_mapC nodeW_mapC)
open Spike.Lib.A64.WakePh (AbPH BandOut nodeW_habEx)

set_option linter.unusedSimpArgs false

variable {L : RuntimeLayout} {a : BitVec 64} {Λ : Scc.Sem.Layout} {R : Region} {F : MachineData → Prop}

section Inst

variable (hp : L.prog = SccCode.helloProg) (hlo : L.Λ.code.lo = lo)
  (hsite : (Spike.Lib.A64.PhRec.μ L).site .take =
    some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat)
include hp hlo hsite

/-- **A block of the path inside `SFactsSt2 … DtW` at `ownH`**: `blkW_pre` at the first instance with no take
phase, at `c0N n`, its phase check `hph` (`abortPhHH`'s), no `ret`. -/
theorem blkW_habStH (a : BitVec 64) {n : ND} {blk : List Directive} {l : Label} {k : Nat} {blo bhi : Int}
    (hb : blockAt SccCode.helloProg l k blk = true) (he : L.lab l + Int64.ofNat (4 * k) = n.pc)
    (hok : Spike.Lib.A64.Flow.okBlk blo bhi n.o blk = true)
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ blo) (hhi : bhi ≤ R.hi)
    (hph : Spike.Lib.A64Consumer.blkPh (okPcOf lo SccCode.helloProg L.Λ) phH (fun _ => false) L.lab
      (L.lab l + Int64.ofNat (4 * k)) 0 blk = true)
    (hnr : Spike.Lib.A64Consumer.noRetBlk blk = true) :
    BlkW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n blk := by
  have hW := Spike.Lib.A64.Rt.blkW_pre (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (Λ := Λ)
    (lbl := fun _ => none) (rS := ⟨0, 0⟩) (F := F) (n := c0N n) (hp ▸ hb) he hok hR hal hlo' hhi c0N_cfacts hph
    (fun _ _ _ k hk r hr => (Spike.Lib.A64Consumer.noRet_false hnr k hk r hr).elim) (fun _ _ _ => rfl)
    (fun _ _ h => h)
  refine blkW_mapC (W := fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
    (n' := c0N n) rfl rfl (fun s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9 => ?_) fun σ c hJ =>
    ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩
  exact ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hW s σ c a1 a2 a3 a4 a5 a6 a7 k hk m a8 a9).1.toSt.toSt2
    (fun h => (h : False).elim), fun _ h => h⟩

/-- **A single instruction without an event of the path** inside `SFactsSt2 … DtW` at `ownH` (`nodeW_si_pre` at
`c0N n`). -/
theorem nodeW_habSiH (a : BitVec 64) {n : ND} {si : SI} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAt SccCode.helloProg l k [si.toDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = q) (hq : n.pc = q)
    (hok : okPcOf lo SccCode.helloProg L.Λ q.toBitVec.toNat = true)
    (hph : phH (q + Int64.ofNat 4).toBitVec.toNat = phH q.toBitVec.toNat) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n := by
  have hW := Spike.Lib.A64.Rt.nodeW_si_pre (instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)) (Λ := Λ)
    (lbl := fun _ => none) (rS := ⟨0, 0⟩) (R := R) (F := F) (n := c0N n) (hp ▸ hb) he hq c0N_cfacts hok
    (fun _ _ h => h) hph
  exact nodeW_mapC (W := fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
    (n' := c0N n) rfl rfl (fun s c hA => ⟨Spike.Lib.A64.WakeWf.SFactsSt2.mono_dt (hW s c hA).1.toSt.toSt2
      (fun h => (h : False).elim), fun _ h => h⟩)
    fun σ c hJ => ⟨Spike.Lib.A64Consumer.c0, show _ ∧ _ from ⟨rfl, c, hJ⟩, fun _ h => h⟩

/-- **The stub's `write`** (`x0 = 2`, `x8 = 64`, `hx`) inside `SFactsSt2 … DtW` at `ownH`: `sfacts_svcAt` off
the sites, its tail `dtW_of_fd2`. -/
theorem nodeW_habWrH (a : BitVec 64) {n : ND} {l : Label} {k : Nat} {q : Int64}
    (hb : blockAt SccCode.helloProg l k [svcDir] = true) (he : L.lab l + Int64.ofNat (4 * k) = q) (hq : n.pc = q)
    (hok : okPcOf lo SccCode.helloProg L.Λ q.toBitVec.toNat = true)
    (hph : phH (q + Int64.ofNat 4).toBitVec.toNat = phH q.toBitVec.toNat)
    (hx : ∀ σ c, n.J σ c → σ.regs.X0 = 2 ∧ σ.regs.X8 = 64) :
    NodeW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F n := by
  have hI := instOkH hp hlo a (fun _ => False) hsite (rS := ⟨0, 0⟩)
  rintro s c ⟨hs, hn, -, hpc, σ, hA, -, hJ⟩
  rw [hq] at hpc
  have hP := (hI.off s (by unfold pcOf; rw [hpc]; exact hok)).1
  have hc := Spike.Lib.A64.Rt.cellOf hI (hp ▸ hb) he hs hn hpc
  have h02 := hx σ c hJ
  have hnx := Spike.Lib.A64.Rt.next_same hI hpc hph
  have hrl := hP.noSite
  have htk := hP.noTake
  have hab := hP.noAbort
  have hS := Spike.Lib.A64Consumer.sfacts_svcAt (Λ := Λ) (lbl := fun _ => none) (rS := ⟨0, 0⟩)
    (μ := Spike.Lib.A64.PhRec.μ L) (own := fun s => ownH L a (phH (pcOf s)))
    (Tk := fun s => (fun _ => False) (phH (pcOf s))) (Dt := DtW) (c := Spike.Lib.A64Consumer.c0) (s := s)
    Spike.Lib.A64.Flow.Ret0.Inst.cfacts_c0 hrl htk hc hnx (fun h => h.elim) (fun k a ha e => (hab k a ha e).elim)
    (fun _ _ _ _ => dtW_of_fd2 (by rw [hA.regs]; exact h02.1) (by rw [hA.regs]; exact h02.2))
  exact ⟨hS.toSt.toSt2, fun _ h => h⟩

/-- **The heap path at `ownH`** inside `SFactsSt2 … DtW`: the abort code of hello.w's program (`hello_abort`),
the path's phases (`abortPhHH`), the dispatcher's region `R` holding the stub's frame. -/
theorem hpathW_habStH (a : BitVec 64) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi) :
    Abort.Disp.HPathW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (fun s => ownH L a (phH (pcOf s))) s DtW)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  have hst0 : Scc.Cert.Rt.A64.Abort.stubIn L.prog Abort.heap Abort.b1Heap = true := hp ▸ hsd.1.1.1.1.2
  have hcode := Scc.Cert.Rt.A64.Abort.code_stub (c0 := c0) L.lays rfl hst0
  have hst := hsd.1.1.1.1.2
  have hdi := hsd.2
  simp only [Scc.Cert.Rt.A64.Abort.stubIn, Bool.and_eq_true, and_assoc] at hst
  obtain ⟨hb0, hn1, hn1b, hb1, hsvcIn, hb2, -, -, -⟩ := hst
  simp only [Scc.Cert.Rt.A64.Abort.dispIn, Bool.and_eq_true, and_assoc] at hdi
  obtain ⟨hd0, ht1, hj1, -, ht2, -, hg2, -⟩ := hdi
  have hphs := abortPhHH (Λ := L.Λ) (lab := L.lab) hΛ hlab
  simp only [Spike.Lib.A64.StubW.abortPhHeapOk, Spike.Lib.A64.StubW.phOne, Bool.and_eq_true, beq_iff_eq,
    and_assoc] at hphs
  obtain ⟨pd0, pt1, pj1, pt2, pg2, pb0, o1, q1, o1b, q1b, pb1, o7, q7, pb2, -⟩ := hphs
  obtain ⟨-, -, -, -, -, -, -, -, e9, e10, e11, -, -, -, -⟩ := abH_labsH hlab
  have hoff : ∀ (k : Scc.Sem.XferKind) a' x, codeOf lo SccCode.helloProg k.label = some x →
      (Spike.Lib.A64.PhRec.μ L).site k = some a' → a' = x := fun k a' x hx ha => by
    have h' : codeOf L.Λ.code.lo L.prog k.label = some a' := ha
    rw [hp, hlo, hx] at h'
    exact (Option.some.inj h').symm
  have hex : (NT L.lab Abort.heap c0 ra .ex).pc.toBitVec.toNat = 2168400 := by
    simp only [NT, Abort.heap, e9]; decide
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact blkW_habStH hp hlo hsite a hd0 (by simp only [DN.nd2R, add0]) Abort.Disp.d0_ok hR hal (by omega)
      (by omega) pd0 rfl
  · exact blkW_habStH hp hlo hsite a ht1 (by simp only [DN.nd2R, add0]) Abort.Disp.t1_ok hR hal (by omega)
      (by omega) pt1 rfl
  · exact blkW_habStH hp hlo hsite a hj1 (by simp only [DN.nd2R, add4, add0]) Abort.Disp.j1_ok hR hal (by omega)
      (by omega) pj1 rfl
  · exact blkW_habStH hp hlo hsite a ht2 (by simp only [DN.nd2R, add0]) Abort.Disp.t2_ok hR hal (by omega)
      (by omega) pt2 rfl
  · exact blkW_habStH hp hlo hsite a hg2 (by simp only [DN.nd2R, add0]) Abort.Disp.g2_ok hR hal (by omega)
      (by omega) pg2 rfl
  · exact blkW_habStH hp hlo hsite a hb0 (by simp only [NT, add0]) Abort.b0_ok hR hal (by omega) (by omega) pb0
      rfl
  · exact nodeW_habSiH hp hlo hsite a (si := .adrp .X9 Abort.heap.msg) hn1 rfl (by simp only [NT, add0]) o1 q1
  · exact nodeW_habSiH hp hlo hsite a (si := .addLo12 .X9 .X9 Abort.heap.msg) hn1b rfl
      (by simp only [NT, add4, add0]) o1b q1b
  · exact blkW_habStH hp hlo hsite a hb1 (by simp only [NT, add4, add0]) Abort.b1Heap_ok hR hal (by omega)
      (by omega) pb1 rfl
  · exact nodeW_habWrH hp hlo hsite a hsvcIn rfl (by simp only [NT, Abort.pcSvc, add4, add0]) o7 q7
      fun _ _ hJ => ⟨hJ.2.1, hJ.2.2⟩
  · exact blkW_habStH hp hlo hsite a hb2 (by simp only [NT, Abort.pcSvc, add4, add0]) Abort.b2_ok hR hal
      (by omega) (by omega) pb2 rfl
  · refine nodeW_habEx (fun s hs hn => by rw [Abort.NT_pc]; exact hcode.ex s hs hn) (fun a' ha => ?_)
      (fun a' ha => ?_) fun _ _ hJ => hJ.2.1
    · rw [hex, hoff .release a' _ e11 ha]; decide
    · rw [hex, hoff .take a' _ e10 ha]; decide

/-- **The heap path at `ownGH`** inside `SFactsSt2 … DtW`: `hpathW_habStH` moved by `abHAgreeWH`, from a caller
other than the two return points `ownGH` reads on it (`h13`, `h15`). -/
theorem hpathW_habGH (a : BitVec 64) (hΛ : L.Λ.abortLbl = Scc.Cert.Link.abortName)
    (hlab : ∀ l x, codeOf lo SccCode.helloProg l = some x → L.lab l = Int64.ofNat x) {c0 : Ctl} {ra : BitVec 64}
    (hR : R.OK) (hal : R.base.toNat % 16 = 0) (hlo' : R.lo ≤ -48) (hhi : 0 ≤ R.hi)
    (h13 : ra = (L.lab ".L3_scc_rt_alloc_tcb.sp13").toBitVec → BandOut L R)
    (h15 : ra ≠ (L.lab ".L22_wc_main.sp15").toBitVec) :
    Abort.Disp.HPathW (fun s _ => SFactsSt2 Λ (Spike.Lib.A64.PhRec.μ L) (ownGH L a) s DtW)
      (fun _ _ => False) L.exe L.endPc R F c0 ra := by
  have hsd := SccCode.hello_abort
  simp only [Scc.Cert.Rt.A64.Abort.abortIn, Bool.and_eq_true] at hsd
  obtain ⟨e1, e2, -, -, -, -, -, -, -, e10, -, -, -, -, -⟩ := abH_labsH hlab
  have hP := abPHH (μ := Spike.Lib.A64.PhRec.μ L) (F := F) (c0 := c0) (ra := ra) hlab hR hal hlo' hhi
    (fun a' ha => by
      have h' : codeOf L.Λ.code.lo L.prog "scc_rt_take_site" = some a' := ha
      rw [hp, hlo, e10] at h'
      cases h'
      rw [e1, e2]; decide)
    (Scc.Cert.Rt.A64.Abort.code_disp L.lays rfl (hp ▸ hsd.2))
    (Scc.Cert.Rt.A64.Abort.code_stub L.lays rfl (hp ▸ hsd.1.1.1.1.2))
  have hg := abHAgreeWH hlab (a := a) hP h13 h15
  have hw := hpathW_habStH hp hlo hsite (Λ := Λ) (F := F) (c0 := c0) (ra := ra) a hΛ hlab hR hal hlo' hhi
  exact ⟨BlkW.ownCongr2 hw.de hg.de, BlkW.ownCongr2 hw.dt1 hg.dt1, BlkW.ownCongr2 hw.dj1 hg.dj1,
    BlkW.ownCongr2 hw.dt2 hg.dt2, BlkW.ownCongr2 hw.dg2 hg.dg2, BlkW.ownCongr2 hw.se hg.se,
    Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 hw.sn1 hg.sn1,
    Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 hw.sn1b hg.sn1b, BlkW.ownCongr2 hw.sn2 hg.sn2,
    Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 hw.ssvc hg.ssvc, BlkW.ownCongr2 hw.sn5 hg.sn5,
    Spike.Lib.A64.WakePh.Tcb2W.nodeW_ownCongr2 hw.sex hg.sex⟩

end Inst

end Spike.Lib.A64.HelloPh

/-- info: 'Spike.Lib.A64.HelloPh.blkW_habStH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.blkW_habStH

/-- info: 'Spike.Lib.A64.HelloPh.nodeW_habWrH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.nodeW_habWrH

/-- info: 'Spike.Lib.A64.HelloPh.hpathW_habGH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64.HelloPh.hpathW_habGH
