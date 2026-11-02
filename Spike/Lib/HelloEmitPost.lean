/-
**hello.w on AArch64: `Post` after a byte of `print`'s `write`** (C4, row
design (a′)). The worker mid-`write(1, …)` is at
`HelloEmitPh.PartsE`; a byte keeps the target state and memory, moves the
source worker through one byte of the published loop (its views grown by
the buffer word's load, `HelloW1.VB`) and lands at `PartsE` again.

- `PartsC`: the parts of `Post` common to `PartsH` in the print phase and
  `PartsE` (all but the worker's invariant); `PartsH.toC`, `PartsE.toC`.
- `PartsC.certified`: the source worker in the print phase is certified
  (`HelloW1.certified_printPh` with the protocol's G1–G3 at its own views,
  `fulfil_ok`).
- `partsE_byte`: after a byte with no promise, `PartsE` (the kernel relation
  given).
-/
import Spike.Lib.HelloEmitSrc
import Spike.Lib.HelloEmitPh
import Spike.Lib.HelloW1Print

namespace Spike.Lib.HelloEmitPost

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.HelloSrc (helloSrc helloS)
open Spike.Lib.HelloW1 (WSideH PT1h PartsH PrintPh StorePh BufV PTermH WCompatH VBuf vbuf_of_bufV
  certified_printPh printPh_not_pass storePh_not_printPh VB vb_refl vb_ld vb_storeMview vb_storeOb ldVs)
open Spike.Lib.HelloEmitPh (EmitPh PartsE)
open Spike.Lib.HelloEmitSrc (emitTh emitCfg)
open Spike.Lib.WakeW1 (withThread1)
open Spike.Lib.WorkerSrcStep (certified_nil)
open Scc.Sem.MemRel (SLatest)

/-! ## The common parts -/

/-- **`Post`'s parts in the print phase, but the worker's invariant**: the
parts of `PartsH` (in the print phase) and of `PartsE`. -/
structure PartsC (Q : WakeRel) (D : WSideH Q.ι) (Λ : Scc.Sem.Layout) (w : Q.ι) (t : Cfg) (s : TermRun.Cfg)
    (t0 t1 : Thread isaLSE2) (s0 s1 : TermRun.TTh) (ts : Nat → Option Nat) (tp sp : List Nat)
    (oc : Option (Nat × Nat)) : Prop where
  th : t.1.threads = #[t0, t1]
  ths : s.ths = #[s0, s1]
  core : Inv2Core Λ (Q.SR w) (Q.P w) (Q.G w)
    (fun i => if i = 0 then Q.own w 0 t0.st s0.stack else Q.own w 1 t1.st s1.stack) t.1.mem t0 t1 s.mem s0 s1 ts
    tp sp
  preC : PreC (Q.SR w) (Q.C w).cT t.1.mem t0.views
  pt0 : Q.PT0 w t.1.mem s.mem t0 s0
  prot : CProt (Q.SR w) (Q.C w) oc t.1.mem t1 s.mem s1 ts tp sp
  kr : Q.KR w t s
  σs : s1.σs = []
  ph : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1
  bufV : BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem
  term : PTermH s1
  noEm : s1.promises = [] ∨ HelloW1.NoEmit (D.cw w) s1
  plen : s1.promises.length ≤ 1
  pprom : ∀ k ∈ s1.promises, D.S w ≤ k ∧ ∃ m : WeakMem.Msg, s.mem[k]? = some m ∧ (D.cw w).val = .loc m.loc 0
  nodup : t1.prom.Nodup

variable {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {AbW : isaLSE2.State → Prop}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isaLSE2} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)}

/-- **`PartsH` in the print phase gives the common parts.** -/
theorem PartsH.toC (hC : WCompatH Q D μ Λ arch AbW) (h : PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hP : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1) : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc := by
  obtain ⟨-, hσ, hph, hl, hk, hn⟩ := h.pt1
  obtain ⟨-, hB, hT, hN⟩ : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) s1 ∧
      BufV (D.bufL w) (D.mB w) (D.S w) (D.cw w) s.mem ∧ PTermH s1 ∧
      (s1.promises = [] ∨ HelloW1.NoEmit (D.cw w) s1) := by
    rcases hph with h' | hS
    · exact h'
    · exact absurd hP (storePh_not_printPh hS (hC.cwv w))
  exact ⟨h.th, h.ths, h.core, h.preC, h.pt0, h.prot, h.kr, hσ, hP, hB, hT, hN, hl, hk, hn⟩

/-- **`PartsE` gives the common parts.** -/
theorem PartsE.toC (h : PartsE Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc := by
  obtain ⟨-, -, -, hσ, ⟨hP, hB, hT, hN⟩, hl, hk, hn, -, -⟩ := h.pt1
  exact ⟨h.th, h.ths, h.core, h.preC, h.pt0, h.prot, h.kr, hσ, hP, hB, hT, hN, hl, hk, hn⟩

/-- `helloC`'s store view at a source thread. -/
theorem mviewS_eq (hC : WCompatH Q D μ Λ arch AbW) (x : TermRun.TTh) :
    (Q.C w).mviewS x = Promises.storeMview (wTh x.vs (D.cw w)) (TermRun.dataE 1 one) [0] true := by
  rw [hC.C w]; rfl

/-- `helloC`'s ordering bound at a source thread. -/
theorem obS_eq (hC : WCompatH Q D μ Λ arch AbW) (x : TermRun.TTh) :
    (Q.C w).obS x = Promises.storeOb Promises.Knobs.all arch (wTh x.vs (D.cw w)) (Q.C w).cS (TermRun.dataE 1 one)
      [0] := by
  rw [hC.C w]; rfl

/-- **The source worker in the print phase is certified** (as
`HelloW1.PartsH.certified_phase`'s print case, at the worker's own views):
with no promise trivially; with the flag's promise by the frame run to
`print`'s return (`certified_printPh` on `noEm`: no `emit` ahead), then the
store, G1–G3 from `CProtS` at the worker (`fulfil_ok`). -/
theorem PartsC.certified (hC : WCompatH Q D μ Λ arch AbW) (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) :
    TermRun.Certified helloSrc Promises.Knobs.all arch s 1 := by
  have hi : s.ths[1]? = some s1 := by rw [h.ths]; rfl
  have hcw := hC.cwv w
  obtain hp | ⟨k, ks, hp⟩ : s1.promises = [] ∨ ∃ k ks, s1.promises = k :: ks := by
    cases s1.promises <;> simp
  · exact certified_nil hi hp
  · have hk : k ∈ s1.promises := by rw [hp]; exact List.mem_cons_self
    have hks : ks = [] := by
      have := h.plen; rw [hp] at this; simpa using this
    subst hks
    obtain ⟨Tc, rfl⟩ : ∃ Tc, oc = some (Tc, k) := by
      obtain ⟨hS, m, hm, hl⟩ := h.pprom k hk
      rw [hcw] at hl
      injection hl with hl1
      rw [hC.S w] at hS
      exact h.prot.smsg k m hm hS (by first | exact hl1 | exact hl1.symm)
    have hnpS : ¬ (Q.C w).passS s1 := fun hps =>
      printPh_not_pass h.ph ((HelloW1.PartsH.passS_iff (w := w) hC s1).mp hps)
    have hS := ((cProt_iff _ _ _).mp h.prot).2.1
    obtain ⟨-, m, hm, hml, hmv⟩ := hS.some_msg Tc k rfl
    have hksp : k ∈ sp := (h.core.sp_prom k).mpr (.inr hk)
    obtain ⟨hmv', hob⟩ := fulfil_ok hS hnpS hksp hm
    rw [mviewS_eq hC] at hmv'
    rw [obS_eq hC] at hob
    have hm' : s.mem[k]? = some ⟨(Q.C w).cS, .num 1, m.view⟩ := by
      rw [hm, ← hml, ← hmv]
    have hN := h.noEm.resolve_left (by rw [hp]; exact List.cons_ne_nil _ _)
    exact certified_printPh hN hi h.σs hp hm' hcw hmv' hob

/-! ## After a byte -/

/-- **After a byte, `PartsE`**: from the common parts with the target
worker at a system call decoding to `write(1, …)` in its invariant at some
control, the target worker replaced by `t1'` (same state and promises, its
bound and cover at the memory), the source worker by `emitTh` (one byte of
the published loop: the buffer word `k / 8`'s latest message `jm` loaded,
in the print phase at a print-phase term), with no source promise (the
byte's certification, `HelloNoCert`), the byte appended to the source
trace, memory kept on both sides, the kernel relation given; the source
frames `EmitFrS` (kept by the byte) and the landing at a term of `print`'s
or `printL`'s body (`PTermE`). -/
theorem partsE_byte (hC : WCompatH Q D μ Λ arch AbW) (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hW : ∃ c fs, D.Wi w t1.st c fs) (hat : abi.atSys t1.st = true)
    (hd : ∃ buf n, decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n))
    {t1' : Thread isaLSE2} (hst : t1'.st = t1.st) (hp : t1'.prom = t1.prom) (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    {k jm : Nat} {msg : WeakMem.Msg} {c2 : Ctl} {bt : Nat} (hk8 : k / 8 < D.mB w)
    (hcell : SLatest s.mem ⟨D.bufL w, k / 8⟩ jm) (hm : s.mem[jm]? = some msg)
    (hP' : PrintPh (D.bufL w) (D.nB w) (D.mB w) (D.cw w) (emitTh s1 s.pairs (D.bufL w) k jm msg c2))
    (hT' : PTermH (emitTh s1 s.pairs (D.bufL w) k jm msg c2)) (hpr : s1.promises = [])
    (hF : HelloEmitPh.EmitFrS D w t1.st s1.stack) (hTE : HelloEmitPh.PTermE c2.term) {k' : KState}
    (hkr : Q.KR w (t.1.withThread 1 t1' t.1.mem, k') (emitCfg s (emitTh s1 s.pairs (D.bufL w) k jm msg c2) bt)) :
    PartsE Q D Λ w (t.1.withThread 1 t1' t.1.mem, k') (emitCfg s (emitTh s1 s.pairs (D.bufL w) k jm msg c2) bt)
      t0 t1' s0 (emitTh s1 s.pairs (D.bufL w) k jm msg c2) ts tp sp oc := by
  obtain ⟨-, -, hRd, hne⟩ := vbuf_of_bufV h.bufV (hC.cwv w)
  obtain ⟨hpair, hview⟩ := hRd (k / 8) hk8 jm msg hcell hm
  rw [hC.S w] at hpair hview
  have hvb : VB (Q.SR w).S (Q.C w).cS s1.vs (emitTh s1 s.pairs (D.bufL w) k jm msg c2).vs :=
    vb_ld (vb_refl _ _ _) (hne _ hk8) hpair hview
  have hstk : (emitTh s1 s.pairs (D.bufL w) k jm msg c2).stack = s1.stack := rfl
  have hnp1 : ¬ WPass s1 := printPh_not_pass h.ph
  have hnp1' : ¬ WPass (emitTh s1 s.pairs (D.bufL w) k jm msg c2) := printPh_not_pass hP'
  obtain ⟨hT, hS, hl⟩ := (cProt_iff _ _ _).mp h.prot
  refine ⟨withThread1 h.th, ?_, ?_, h.preC, h.pt0, ?_, ?_, hkr⟩
  · show s.ths.set! 1 (emitTh s1 s.pairs (D.bufL w) k jm msg c2) = _
    rw [h.ths]; rfl
  · refine core1_same h.core (by simp) hp rfl hb hcov ?_ ?_ ?_ ?_ ?_
    · intro k0 m0 hk0 hf
      have := h.core.scov1 k0 m0 hk0 hf
      show k0 ≤ (ldVs s1.vs s.pairs ⟨D.bufL w, k / 8⟩ jm msg.view).coh m0.loc
      simp only [ldVs]
      split
      · next he => rw [← he]; exact Nat.le_trans this (Nat.le_max_left _ _)
      · exact this
    · simpa only [Nat.one_ne_zero, ite_false, hst, hp, hstk] using h.core.own1
    · intro L v v' h0 h1
      simp only [ite_true] at h0
      simp only [Nat.one_ne_zero, ite_false, hst, hstk] at h1
      exact h.core.own_disj L v v' (by simpa using h0) (by simpa using h1)
    · intro L v h1
      simp only [Nat.one_ne_zero, ite_false, hst, hstk] at h1
      exact h.core.own_cov 1 L v (by decide) (by simpa using h1)
    · intro hn
      rw [hst] at hn
      rw [hp]
      exact h.core.noProm1 hn
  · exact ⟨hst ▸ hW, hst ▸ hat, hst ▸ hd, h.σs, ⟨hP', h.bufV, hT', .inl hpr⟩, h.plen, h.pprom, hp ▸ h.nodup,
      hst ▸ hF, hTE⟩
  · refine (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg, fun Tc kc hoc htp => hp ▸ hT.prom_worker Tc kc hoc htp,
      fun hq => hT.pass_done (by rwa [hst] at hq), fun hq => hT.pass_prom (by rwa [hst] at hq)⟩,
      ⟨hS.smsg, hS.some_msg, hS.prom_worker, fun _ => ?_, hS.prom_view⟩, ?_⟩
    · have hnpS : ¬ (Q.C w).passS s1 := fun hps => hnp1 ((HelloW1.PartsH.passS_iff (w := w) hC s1).mp hps)
      obtain ⟨h1, h2⟩ := hS.pre_lt hnpS
      rw [mviewS_eq hC] at h1 ⊢
      rw [obS_eq hC] at h2 ⊢
      have e1 := vb_storeMview hvb (D.cw w)
      have e2 := vb_storeOb hvb Promises.Knobs.all arch (D.cw w)
      exact ⟨Nat.lt_of_le_of_lt e1 (Nat.max_lt.mpr ⟨h1, by omega⟩),
        Nat.lt_of_le_of_lt e2 (Nat.max_lt.mpr ⟨h2, by omega⟩)⟩
    · rw [HelloW1.PartsH.passS_iff (w := w) hC (emitTh s1 s.pairs (D.bufL w) k jm msg c2), hst, hl,
        HelloW1.PartsH.passS_iff (w := w) hC s1]
      exact ⟨fun h' => absurd h' hnp1, fun h' => absurd h' hnp1'⟩

/-- info: 'Spike.Lib.HelloEmitPost.partsE_byte' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms partsE_byte

end Spike.Lib.HelloEmitPost
