/-
**wake.w on AArch64: the `WakeObligations` assembly skeleton** (the checklist for the final assembly). Every field of
`WakeObligations` is instantiated, from a proved lemma where one exists,
otherwise from an explicit named hypothesis.
No proof is deferred: the open pieces are exactly the hypotheses.

The relation's data is fixed where a proved instance exists: main's `PT0`
is `WakeM0.PT0 M` (`hPT0`), the kernel relation is `WakeKR.KR r0 r1`
(`hKR`), the owned words are `WakeOwn.wakeOwn` (`hown`); the trace invariant
is `WakePreTi.TiPre Ab Ac`, the pre-spawn half is one `WakePreTi.Pre1T`.

- `wCompatX_of`: `WCompatX`; open: `Gc`. `own1`, `sp0`, `pt0p`, `krp`
  are proved (`WakeOwn.own1`, `WakeM0.PT0.promises_nil`,
  `WakeM0.pt0_permit`, `WakeKR.kr_permit`).
- `wCompat_of`: `WCompat`; proved: `own`-family (`WakeOwn`), `pt0`/`tid0`
  (`WakeM0`), `kr` (`kr_frame1`), `mainLive` (`WakeM0.mainLive_of`), `pass`
  (`WakeWorkerSide.pass_of`); the rest open, by name.
- `texitFacts_of`: `worker_done`'s facts (`WakeKR.kr_exit1`).
- `Pre1T.ti_step`'s `hpost`: `WakePostAb.post_last_kr` (`Post`'s last slot
  is not dormant).
- `wake_obligations`: the assembly.

**Open hypotheses of `wake_obligations`**:
- `hW1` (the worker's writes are `RelW1`; `hconv` is
  `WakeConv1.hconv_of'`, `henv` is `WakeEnv.henv_of`).
- `hhalt0`, `hmapM`, `hMμ`; at the instance `M := WakeInst.wakeM …`
  by `WakeInst.hhalt0_I`, `WakeInst.hmapM_I` (`Λ := (ofPlaceOK hp i).Λ`) and
  `WakeInst.hMμ_I` (and `WCompat0.relW0` by `WakeInst.relW0_I`).
- `hhalt1`, `hmapW` (planned with `hW1` through one `hW`, `A64WakeZX`).
- `post_wit`.
- `hC0`, `O`, `spawn`, `hstart`.
- Instance data (`rfl`/proved lemmas at `WakeQ.wakeQ`, `RuntimeLayout.ofPlaceW`):
  `hwf`, `hPT0`, `hKR`, `hown`, `hpl`/`hpa` (the parse of `SccCertificate.asm`).
-/
import Spike.Lib.WakeW1Unpk
import Spike.Lib.WakePost1
import Spike.Lib.WakePreTi
import Spike.Lib.WakeM0Post
import Spike.Lib.WakePostAb
import Spike.Lib.WakeKRP
import Spike.Lib.WakeOwn
import Spike.Lib.WakeWorkerSide
import Spike.Lib.WakeSideFields
import Spike.Lib.WakeNoAbort
import Spike.Lib.WakeProgress
import Spike.Lib.WakeMapped
import Spike.Lib.WakeCert
import Spike.Lib.WakeWide
import Spike.Lib.WakeEnv
import Spike.Lib.WakeConv1
import Spike.Lib.PlaceWRt

namespace Spike.Lib.WakeAssembly

open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1 Spike.Lib.WakeW1 Spike.Lib.WakePost1
open Spike.Lib.WakePreTi Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.Inv2Read Spike.Lib.Handover
open Spike.Lib.TwoSlot Spike.Lib.A64TwoSlot Spike.Lib.WorkerSrc

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : String} {Q : WakeRel} {E : Entry}
  {D : WSide Q.ι} {M : WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range}

/-! ## `WCompatX` -/

/-- **`WCompatX`**: only `Gc` is open. -/
theorem wCompatX_of (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    (hown : Q.own = WakeOwn.wakeOwn)
    /- OPEN: the worker's flag store value `1` is a `G` value at `cT` -/
    (Gc : ∀ w, Q.G w (Q.C w).cT 1) :
    WCompatX Q D where
  Gc := Gc
  own1 w s := by rw [hown]; exact WakeOwn.own1 w s
  sp0 w _ _ _ _ h := by rw [hPT0] at h; exact WakeM0.PT0.promises_nil h
  pt0p w _ _ _ _ _ _ p h _ := by rw [hPT0] at h ⊢; exact WakeM0.pt0_permit p h
  krp := by
    rw [hKR]
    exact fun w t t' s s' s0 p h a b c d e => WakeKR.kr_permit w t t' s s' s0 p h a b c d
      (by simp only [SrcSem.traceOf, e])

/-! ## `WCompat` -/

/-- **`WCompat`**: the fields fixed by the relation's data are
proved; every other field is a hypothesis of the same name (as in
`WCompat`'s docstrings). -/
theorem wCompat_of {μ : Marks} (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1)
    (hown : Q.own = WakeOwn.wakeOwn)
    /- (`rfl` at `WakeQ.wakeQ`: `WakeQ.pt1`, `WakeQ.atUnpk`, `WakeQ.atTexit`) -/
    (pt1 : Q.PT1 = PT1 D) (atUnpk : Q.atUnpk = WakeW1.atUnpk) (atTexit : Q.atTexit = WakeW1.atTexit)
    /- (`WorkerSide.sideF_of`, at `D := side …`:
    `lbl`, `K`, `wide`, `noSite`, `sysExec`, `sysOk`, `cwv`, `S` and `pass`'s
    `hZ`) -/ (F : WorkerSide.SideF Q D μ)
    (G : ∀ w, (D.ms w).G = Q.G w)
    /- (at `hown`, the rows' owned words are none) -/ (own : ∀ w s, (D.ms w).own s = [])
    (mpW : ∀ w L, (D.ms w).mp L true →
      (Q.P w).foot 1 L ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize L ∧ Consumer1.LocIn Λ.shared L)
    /- (`rfl` at `WakeQ.wakeQ`: `WakeQ.hC`) -/
    (C : ∀ w, Q.C w = helloC (Q.C w).cT (Q.C w).cS (Q.C w).passT Promises.Knobs.all arch (D.cw w))
    (cT : ∀ w, ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
      (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label)
    (cTin : ∀ w, Consumer1.LocIn Λ.shared (Q.C w).cT) (cTfoot : ∀ w, (Q.P w).foot 1 (Q.C w).cT)
    (cSfrz : ∀ w, ¬ (Q.P w).frzS (Q.C w).cS)
    (Spos : ∀ w, 0 < (Q.SR w).S)
    /- (`WakeLocs.OK`) -/
    (footLab : ∀ w L, (Q.P w).foot 1 L → InLabel (Q.SR w).lbl (Q.SR w).lsize L → L = (Q.C w).cT)
    /- (`rfl` at `WakeQ.wakeQ`: `WakeQ.hpT`; `pass` by
    `WakeWorkerSide.pass_of` with `F.hZ`) -/
    (hpT : ∀ w, (Q.C w).passT = Spike.Lib.A64.Flow.Worker.Wake.Pass.wakePassT)
    /- (`WakeP.noProm_prom`) -/
    (noProm : ∀ w x (t : Thread isaLSE2) mem, (Q.P w).noProm t.st →
      CertOkC Arch.armv8 (certSem abi Arch.armv8 μ x 1) 1 t mem → t.prom = []) :
    WCompat Q D μ Λ arch where
  pt1 := pt1
  atUnpk := atUnpk
  atTexit := atTexit
  lbl := F.lbl
  K := F.K
  G := G
  own w s := by rw [own, hown]; rfl
  mpW := mpW
  wide := F.wide
  noSite := F.noSite
  sysExec := F.sysExec
  sysOk := F.sysOk
  ownInstr w s _ tree _ _ _ := by rw [hown]; exact WakeOwn.ownInstr w s tree
  ownSys w s _ _ _ _ _ s' _ := by rw [hown]; exact WakeOwn.ownSys w s s'
  ownCov w s L v h := by rw [hown] at h; exact WakeOwn.ownCov w 1 s [] L v h
  ownDisj w s0 fs s L v v' h h' := by rw [hown] at h h'; exact WakeOwn.ownDisj w 0 1 s0 s fs [] L v v' h h'
  C := C
  cwv := F.cwv
  S := F.S
  cT := cT
  cTin := cTin
  cTfoot := cTfoot
  cSfrz := cSfrz
  Spos := Spos
  footLab := footLab
  pass := WorkerSide.pass_of F.hZ hpT
  noProm := noProm
  mainLive _ _ h hx := WakeM0.mainLive_of hPT0 (fun w t s hk => by rw [hKR] at hk; exact WakeKR.kr_live hk) h hx
  tid0 w _ _ _ _ h := by rw [hPT0] at h; exact WakeM0.tid0_of h
  pt0 w _ _ _ _ _ _ h _ := by rw [hPT0] at h ⊢; exact WakeM0.pt0_mem h
  kr := by
    rw [hKR]
    exact fun w t t' s s' h a b c d => WakeKR.kr_frame1 w t t' s s' h a b c (by simp only [SrcSem.traceOf, d])

/-! ## `worker_done` and the trace invariant -/

/-- **`worker_done`'s facts**: the call by `WCompat.atTexit`, the kernel
relation by `WakeKR.kr_exit1`. -/
theorem texitFacts_of {μ : Marks} (hC : WCompat Q D μ Λ arch) (hKR : Q.KR = WakeKR.KR r0 r1) :
    TexitFacts Q where
  call t s h := by rw [hC.atTexit] at h; exact h
  kr_exit1 w t s h hx := by
    rw [hKR] at h ⊢; exact WakeKR.kr_exit1 (P := fun _ _ => True) w t s h trivial

/-! ## The assembly -/

set_option linter.unusedVariables false in
/-- **The assembly**: `WakeObligations` at `Ti := TiPre Ab Ac`.
- Pre-spawn (`pre_init`, `pre_step`, `pre_progress`, `pre_abort`, `pre_wit`,
  `ti_load`, `ti_step`): one `Pre1T`, OPEN.
- `spawn`: OPEN (the spawn/stub rows, the `own` split,
  `main_closed_wake` for main's `MSide.Mi` at `cP = spawnPar …`;
  `WakeStart.post_startW` assembles `Inv2`).
- `post_step1`, `unpark_src`, `worker_done`: PROVED (`post_step1_of`,
  `unpark_src_of`, `WakePost1.worker_done`) from `WCompat` (`wCompat_of`)
  and `WCompatX` (`wCompatX_of`).
- `post_step0`: PROVED (`WakeM0.post_step0_of`) from `WCompat`, main's
  `WCompat0` (`hC0`, field by field in `WakeM0Compat`)
  and `hown`.
- `post_abort`: PROVED (`WakeNoAbort.post_abort_of`, vacuous: no abort step
  from `Post`) from `MSide.off` at `hMμ`, `kr_live` and `WCompat.sysOk`.
- `post_progress`: PROVED (`WakeProgress.post_progress_of`) from `WCompat`,
  `WCompat0`, `MSide.off`, the invariants `RunInv` and `CertAll` and the
  named facts `hhalt0`, `hhalt1`, `hmapM`, `hmapW` 
  (`WakeMapped.hmapped_of`).
- `cert_step`: PROVED (`WakeCert.certAll_step_of`) from `WCompat`, `WCompat0`,
  `KR`, the transport `WakeEnv.henv_of` and the conversion `hconv`.
- `hconv`: PROVED (`WakeConv1.hconv_of'`) from `WCompat`, `WCompat0` (its
  `relW0`), `WCompatX`, `hwf` and the worker's write fact `hW1`: OPEN.
- `hwide`: PROVED (`WakeWide.hwide_of_placeOKAt`) from `placeOKAt` and
  the parse `hpa`.
- `post_wit`: OPEN. -/
theorem wake_obligations {Ab Ac : State → Prop}
    /- (at `Λ := (RuntimeLayout.ofPlaceW hp i).Λ`: `WakeQ.hwf_ofPlaceOK`) -/ (hwf : Λ.WF)
    /- (the relation's data, `rfl` at `WakeQ.wakeQ`: `WakeQ.hPT0`,
    `WakeQ.hKR`, `WakeQ.hown`) -/
    (hPT0 : Q.PT0 = WakeM0.PT0 M) (hKR : Q.KR = WakeKR.KR r0 r1) (hown : Q.own = WakeOwn.wakeOwn)
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
    (hC : WCompat Q D ((target (kernel 2) E).marks asm Λ) Λ arch) (hx : WCompatX Q D)
    /- (main's side; 16 fields (16th `relW0`), field by field in
    `Spike/Lib/WakeM0Compat.lean`) OPEN -/
    (hC0 : WakeM0.WCompat0 Q M ((target (kernel 2) E).marks asm Λ) Λ)
    /- OPEN -/ (hstart : ∃ d, (target (kernel 1) E).load asm Λ = some d)
    /- OPEN: the pre-spawn half (see
    `WakePreAsm.pre1T_of_seg` and `wake_init`) -/ (O : Pre1T arch Λ B asm E Q.R1 Ab Ac)
    /- (consumes `main_closed_wake` (its `hS` by
    `WakeHS.hS_ofPlaceOK`), `post_startW`) OPEN -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), Q.R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.armv8 ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s')
    /- `post_progress`'s named facts (`WakeProgress.post_progress_of`):
    OPEN: at a system call main's state has an instruction -/
    (hhalt0 : ∀ w s c, M.Mi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    /- OPEN: at a system call the worker's state has an instruction -/
    (hhalt1 : ∀ w s c, D.Wi w s c → abi.atSys s = true → (isaLSE2.exec s).isSome)
    /- `hmapped` by `WakeMapped.hmapped_of` from the per-node facts:
    OPEN: main's instructions touch only locations mapped at the load -/
    (hmapM : ∀ w s c, M.Mi w s c → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (A64Consumer.K0 Λ) w l = false) e)
    /- OPEN: the worker's instructions touch only locations mapped at the load -/
    (hmapW : ∀ w s c, D.Wi w s c → abi.atSys s = false → ∀ e, isaLSE2.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (A64Consumer.K0 Λ) w l = false) e)
    /- (`rfl`-like at the instance, `WakeWorkerSide.wake_hμ`) main's side's
    marks are the loaded program's, so `WakeM0.MSide.off` (every abort kind)
    puts main's invariant at no abort site; with `kr_live` and the worker's
    `WCompat.sysOk`, `WakeNoAbort.post_abort_of` proves `post_abort`
    vacuously -/
    (hMμ : M.μ = (target (kernel 2) E).marks asm Λ)
    /- `hwide` (`runInv_load`) by `WakeWide.hwide_of_placeOKAt` from the
    placement check and the loader's parse of the listing (the trust boundary;
    at `asm := SccCertificate.asm`, `o := RuntimeLayout.ofPlaceW hp i`) -/
    {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.A64.Out}
    (hpl : PlaceW pcfg Λ po) (hpa : textProgram asm = .ok po.prog)
    /- `hconv` by `WakeConv1.hconv_of'` (main by `WCompat0.relW0`, the
    worker by `WakeW1.CInv`) from the worker's write fact: (with the
    worker facts, `ZX.hW1_ofX`) OPEN: every write of the worker's
    instructions is a release write, at most one per path -/
    (hW1 : ∀ w s c e, D.Wi w s c → isaLSE2.exec s = some e → EvTree.RelW1 Arch.armv8 e)
    /- (`WakePostWit.post_wit_of`) OPEN -/
    (post_wit : ∀ t s, Q.Post Λ t s → WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    WakeObligations arch Λ B asm Q E (TiPre Ab Ac) where
  hwf := hwf
  hstart := hstart
  pre_init := O.init
  pre_step := O.step
  spawn := spawn
  post_step0 _ _ _ _ hP hs := WakeM0.post_step0_of hC hC0 hPT0 hKR hown hwf hP hs
  post_step1 _ _ _ _ hP hnu hnt hs := post_step1_of hC hx hwf hP hnu hnt hs
  unpark_src _ _ _ _ hP hu hs := unpark_src_of hC hx hwf hP hu hs
  worker_done := worker_done (texitFacts_of hC hKR)
  pre_progress := O.pre_progress
  post_progress t s hP hri hca := WakeProgress.post_progress_of hC hC0 hPT0 hKR (hMμ ▸ M.off) hhalt0 hhalt1 hP
    hca (WakeMapped.hmapped_of hPT0 hC.pt1 hKR hmapM hmapW t s hP hri)
  hwide := WakeWide.hwide_of_placeOKAt hpl hpa
  cert_step := WakeCert.certAll_step_of hC hC0 hPT0 hKR (WakeEnv.henv_of hC hC0 hPT0 hKR)
    (WakeConv1.hconv_of' hC hC0 hx hwf hPT0 hKR hW1)
  hconv := WakeConv1.hconv_of' hC hC0 hx hwf hPT0 hKR hW1
  ti_load := O.ti_load
  ti_step := O.ti_step rfl (hpost_of fun _ _ hP =>
    WakePostAb.post_last_kr (fun _ _ _ h => by rw [hKR] at h; exact h) hP)
  pre_abort := O.pre_abort (fun _ _ h => h)
  post_abort := WakeNoAbort.post_abort_of (fun w t s hk => by rw [hKR] at hk; exact WakeKR.kr_live hk)
    (fun w _ _ t0 s0 h hl => by rw [hPT0] at h; exact hMμ ▸ M.off w _ _ (h.1.resolve_right hl))
    (WakeNoAbort.sys1_of hC)
  pre_wit := O.pre_wit
  post_wit := post_wit

/-- info: 'Spike.Lib.WakeAssembly.wake_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wake_obligations

/-- info: 'Spike.Lib.WakeAssembly.wCompat_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wCompat_of

/-- info: 'Spike.Lib.WakeAssembly.wCompatX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms wCompatX_of

end Spike.Lib.WakeAssembly
