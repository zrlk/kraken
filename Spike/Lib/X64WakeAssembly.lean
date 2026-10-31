/-
**wake.w on x86-64: the `WakeObligations` assembly skeleton** (hello plan
1.6; the final assembly), the x86-64 twin of
`Spike/Lib/WakeAssembly.lean` (names and premise order kept; module names
with the `X64` prefix). Every field of
`WakeObligations` is instantiated, from a proved lemma where one exists,
otherwise from an explicit named hypothesis whose comment says what it states.
No proof is deferred: the open pieces are exactly the hypotheses.

The relation's data is fixed where a proved instance exists: main's `PT0`
is `WakeM0.PT0 M` (`hPT0`), the kernel relation is `WakeKR.KR r0 r1`
(`hKR`), the owned words are `X64WakeOwnX.wakeOwnXW T W` (`hown`); the trace invariant
is `WakePreTi.TiPre Ab Ac`, the pre-spawn half is one `WakePreTi.Pre1T`.

- `wCompatX_of`: `WCompatX`; open: `Gc`. `ownConst1`, `ownMp1`, `sp0`,
  `pt0p`, `krp` are proved (`X64WakeOwnX.ownConst1XW`, `ownMp1XW` at `hms`,
  `WakeM0.PT0.promises_nil`, `WakeM0.pt0_permit`, `WakeKR.kr_permit`).
- `wCompat_of`: `WCompat`; proved: `own`, `ownSys`, `ownDisj` (`wakeOwnXW`
  at `hms`, `hTW`), `ownCov` (from `hcovW`), `pt0`/`tid0`
  (`WakeM0`), `kr` (`kr_frame1`), `mainLive` (`WakeM0.mainLive_of`); the
  rest open, by name.
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

**Unlike AArch64**:
- `wCompat_of` takes the worker side's fields `lbl`, `K`, `wide`, `noSite`,
  `sysExec`, `sysOk`, `cwv`, `S` and `pass` as separate hypotheses (A64:
  one `F : WorkerSide.SideF Q D μ` and `hpT : ∀ w, (Q.C w).passT =
  wakePassT`, `pass` by `WakeWorkerSide.pass_of F.hZ hpT`), the x86-64
  `WakeWorkerSide`/`WakeSideFields` (and `wakePassT`) not being twinned yet;
  this file imports neither. Re-bundle when they land.
- `post_step0` by `X64WakeM0.post_step0_of` without `hown` (the x86-64
  lemma does not take it).
- The owned words are `X64WakeOwnX.wakeOwnXW T W` (A64: `WakeOwn.wakeOwn`,
  none): the worker owns its TCB self word `⟨W, 8⟩ ↦ W` (X64-OwnW). So the
  worker side's memory side is `msXW (msW w) W T W` (`hms`; A64: `own : ∀ w
  s, (D.ms w).own s = []`), `WCompat.ownInstr` is a hypothesis (the rows
  write no owned word; A64: `OwnTree.nil`), and `ownCov`, `ownDisj` take the
  self word's cover `hcovW` and `hTW : ⟨T, 8⟩ ≠ ⟨W, 8⟩`.
- `hpl : PlaceWX pcfg Λ po` at an `Scc.Cert.PlaceOK.X64.Out`, `hpa : cellsOf
  asm = some po.prog` (A64: `PlaceW`, `textProgram asm = .ok po.prog`);
  `Arch.tso`, `isa`, `X64Consumer.K0`.
-/
import Spike.Lib.X64WakeW1Unpk
import Spike.Lib.X64WakePost1
import Spike.Lib.X64WakePreTi
import Spike.Lib.X64WakeM0Post
import Spike.Lib.X64WakePostAb
import Spike.Lib.X64WakeKRP
import Spike.Lib.X64WakeOwn
import Spike.Lib.X64WakeOwnXW
import Spike.Lib.X64WakeNoAbort
import Spike.Lib.X64WakeProgress
import Spike.Lib.X64WakeMapped
import Spike.Lib.X64WakeCert
import Spike.Lib.X64WakeWide
import Spike.Lib.X64WakeEnv
import Spike.Lib.X64WakeConv1
import Spike.Lib.X64PlaceWRt

namespace Spike.Lib.X64WakeAssembly

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1 Spike.Lib.X64WakeW1 Spike.Lib.X64WakePost1
open Spike.Lib.X64WakePreTi Spike.Lib.Inv2Core Spike.Lib.HelloProt Spike.Lib.Inv2Read Spike.Lib.Handover
open Spike.Lib.TwoSlot Spike.Lib.X64TwoSlot Spike.Lib.WorkerSrc

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel} {E : Entry}
  {D : WSide Q.ι} {M : X64WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {T W : BitVec 64}

/-! ## `WCompatX` -/

/-- **`WCompatX`**: only `Gc` is open. -/
theorem wCompatX_of (hPT0 : Q.PT0 = X64WakeM0.PT0 M) (hKR : Q.KR = X64WakeKR.KR r0 r1)
    (hown : Q.own = X64WakeOwnX.wakeOwnXW T W)
    /- (worker side; `rfl` at `D.ms w := msXW …`) the worker's memory
    side owns its self word and writes neither self word as the runtime's -/
    {msW : Q.ι → MemSide isa} (hms : ∀ w, D.ms w = X64WakeOwnX.msXW (msW w) W T W)
    /- OPEN: the worker's flag store value `1` is a `G` value at `cT` -/
    (Gc : ∀ w, Q.G w (Q.C w).cT 1) :
    WCompatX Q D where
  Gc := Gc
  ownConst1 w s s' := by rw [hown]; exact X64WakeOwnX.ownConst1XW T W w s s'
  ownMp1 w s L v h := by
    rw [hown] at h; rw [hms]; exact X64WakeOwnX.ownMp1XW (msW w) T W w s L v h
  sp0 w _ _ _ _ h := by rw [hPT0] at h; exact X64WakeM0.PT0.promises_nil h
  pt0p w _ _ _ _ _ _ p h _ := by rw [hPT0] at h ⊢; exact X64WakeM0.pt0_permit p h
  krp := by
    rw [hKR]
    exact fun w t t' s s' s0 p h a b c d e => X64WakeKR.kr_permit w t t' s s' s0 p h a b c d
      (by simp only [SrcSem.traceOf, e])

/-! ## `WCompat` -/

/-- **`WCompat`**: the fields fixed by the relation's data are
proved; every other field is a hypothesis of the same name, described in its
comment (as in `WCompat`'s docstrings). -/
theorem wCompat_of {μ : Marks} (hPT0 : Q.PT0 = X64WakeM0.PT0 M) (hKR : Q.KR = X64WakeKR.KR r0 r1)
    (hown : Q.own = X64WakeOwnX.wakeOwnXW T W)
    /- (`rfl` at `WakeQ.wakeQ`: `WakeQ.pt1`, `WakeQ.atUnpk`, `WakeQ.atTexit`) -/
    (pt1 : Q.PT1 = PT1 D) (atUnpk : Q.atUnpk = X64WakeW1.atUnpk) (atTexit : Q.atTexit = X64WakeW1.atTexit)
    /- (A64 bundles these as `WorkerSide.SideF` (`sideF_of`, at
    `D := side …`); here unbundled, the x86-64 `SideF` not being twinned yet) -/
    (lbl : ∀ w, D.lbl w = (Q.SR w).lbl) (K : ∀ w, (D.ms w).K = some abi)
    (wide : ∀ w s c, D.Wi w s c → Scc.Cert.WideX64.WideSt s)
    (noSite : ∀ w s c, D.Wi w s c → siteAt abi μ s = none)
    (sysExec : ∀ w s c t, D.Wi w s c → abi.atSys s = true → isa.exec s = some t → ∃ m, t = .fault m)
    (sysOk : ∀ w s c call, D.Wi w s c → abi.atSys s = true → decode abi.nrs (abi.nr s) (abi.arg s) = some call →
      call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v))
    (cwv : ∀ w, (D.cw w).val = .loc (Q.C w).cS 0) (S : ∀ w, D.S w = (Q.SR w).S)
    /- -/ (G : ∀ w, (D.ms w).G = Q.G w)
    /- (worker side; `rfl` at `D.ms w := msXW …`; A64: the rows' owned
    words are none) -/
    {msW : Q.ι → MemSide isa} (hms : ∀ w, D.ms w = X64WakeOwnX.msXW (msW w) W T W)
    /- -/
    (mpW : ∀ w L, (D.ms w).mp L true →
      (Q.P w).foot 1 L ∧ ¬ InLabel (Q.SR w).lbl (Q.SR w).lsize L ∧ Consumer1.LocIn Λ.shared L)
    /- (`rfl` at `WakeQ.wakeQ`: `WakeQ.hC`) -/
    (C : ∀ w, Q.C w = helloC (Q.C w).cT (Q.C w).cS (Q.C w).passT Promises.Knobs.all arch (D.cw w))
    /- -/
    (cT : ∀ w, ∃ a, (Q.C w).cT = wordLoc a ∧ wordAddr (Q.SR w).lbl (Q.C w).cS = some a ∧
      (Q.C w).cS.offset < (Q.SR w).lsize (Q.C w).cS.label)
    (cTin : ∀ w, Consumer1.LocIn Λ.shared (Q.C w).cT) (cTfoot : ∀ w, (Q.P w).foot 1 (Q.C w).cT)
    (cSfrz : ∀ w, ¬ (Q.P w).frzS (Q.C w).cS)
    /- -/ (Spos : ∀ w, 0 < (Q.SR w).S)
    /- (`WakeLocs.OK`) -/
    (footLab : ∀ w L, (Q.P w).foot 1 L → InLabel (Q.SR w).lbl (Q.SR w).lsize L → L = (Q.C w).cT)
    /- (A64 derives it by `WakeWorkerSide.pass_of` from `SideF.hZ` and
    `hpT : ∀ w, (Q.C w).passT = wakePassT`; here given directly) -/
    (pass : ∀ w s c, D.Wi w s c → ((Q.C w).passT s ↔ (c.term = wkUnpark ∨ c.term = .ret .unit)))
    /- (worker rows; A64 `OwnTree.nil`) the worker's instructions keep
    its self word: none writes `⟨W, 8⟩` -/
    (ownInstr : ∀ w s c tree, D.Wi w s c → abi.atSys s = false → isa.exec s = some tree →
      Consumer1.OwnTree (fun s => Q.own w 1 s []) (Q.own w 1 s []) tree)
    /- (`X64WakeOwnX.ownCov1XW` at `P := wakeP … (wakeLocsXW …)`) the self
    word is in the worker's cover set -/
    (hcovW : ∀ w, (Q.P w).cov 1 ⟨W, 8⟩)
    /- (`post_startOXW`'s `hTW`) the two self words differ -/ (hTW : (⟨T, 8⟩ : Loc) ≠ ⟨W, 8⟩)
    /- (`WakeP.noProm_prom`) -/
    (noProm : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso μ x 1) 1 t mem → t.prom = []) :
    WCompat Q D μ Λ arch where
  pt1 := pt1
  atUnpk := atUnpk
  atTexit := atTexit
  lbl := lbl
  K := K
  G := G
  own w s := by rw [hms, hown]; rfl
  mpW := mpW
  wide := wide
  noSite := noSite
  sysExec := sysExec
  sysOk := sysOk
  ownInstr := ownInstr
  ownSys w s _ _ _ _ _ s' _ := by rw [hown]; exact X64WakeOwnX.ownConst1XW T W w s s'
  ownCov w s L v h := by
    rw [hown] at h; simp only [X64WakeOwnX.wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h; exact hcovW w
  ownDisj w s0 fs s L v v' h h' := by
    rw [hown] at h h'
    simp only [X64WakeOwnX.wakeOwnXW_zero, X64WakeOwnX.wakeOwnXW_one, List.mem_singleton, Prod.mk.injEq] at h h'
    exact hTW (h.1.symm.trans h'.1)
  C := C
  cwv := cwv
  S := S
  cT := cT
  cTin := cTin
  cTfoot := cTfoot
  cSfrz := cSfrz
  Spos := Spos
  footLab := footLab
  pass := pass
  noProm := noProm
  mainLive _ _ h hx := X64WakeM0.mainLive_of hPT0 (fun w t s hk => by rw [hKR] at hk; exact X64WakeKR.kr_live hk) h hx
  tid0 w _ _ _ _ h := by rw [hPT0] at h; exact X64WakeM0.tid0_of h
  pt0 w _ _ _ _ _ _ h _ := by rw [hPT0] at h ⊢; exact X64WakeM0.pt0_mem h
  kr := by
    rw [hKR]
    exact fun w t t' s s' h a b c d => X64WakeKR.kr_frame1 w t t' s s' h a b c (by simp only [SrcSem.traceOf, d])

/-! ## `worker_done` and the trace invariant -/

/-- **`worker_done`'s facts**: the call by `WCompat.atTexit`, the kernel
relation by `X64WakeKR.kr_exit1`. -/
theorem texitFacts_of {μ : Marks} (hC : WCompat Q D μ Λ arch) (hKR : Q.KR = X64WakeKR.KR r0 r1) :
    TexitFacts Q where
  call t s h := by rw [hC.atTexit] at h; exact h
  kr_exit1 w t s h hx := by
    rw [hKR] at h ⊢; exact X64WakeKR.kr_exit1 (P := fun _ _ => True) w t s h trivial

/-! ## The assembly -/

set_option linter.unusedVariables false in
/-- **The assembly**: `WakeObligations` at `Ti := TiPre Ab Ac`.
- Pre-spawn (`pre_init`, `pre_step`, `pre_progress`, `pre_abort`, `pre_wit`,
  `ti_load`, `ti_step`): one `Pre1T`, OPEN.
- `spawn`: OPEN (spawn/stub rows, own split,
  `main_closed_wake` for main's `MSide.Mi` at `cP = spawnPar …`;
  `WakeStart.post_startW` assembles `Inv2`).
- `post_step1`, `unpark_src`, `worker_done`: PROVED (`post_step1_of`,
  `unpark_src_of`, `X64WakePost1.worker_done`) from `WCompat` (`wCompat_of`)
  and `WCompatX` (`wCompatX_of`).
- `post_step0`: PROVED (`X64WakeM0.post_step0_of`) from `WCompat`, main's
  `WCompat0` (`hC0`, fields in `WakeM0Compat`; main rows)
  and `hown`.
- `post_abort`: PROVED (`X64WakeNoAbort.post_abort_of`, vacuous: no abort step
  from `Post`) from `MSide.off` at `hMμ`, `kr_live` and `WCompat.sysOk`.
- `post_progress`: PROVED (`X64WakeProgress.post_progress_of`) from `WCompat`,
  `WCompat0`, `MSide.off`, the invariants `RunInv` and `CertAll` and the
  named facts `hhalt0`, `hhalt1`, `hmapM`, `hmapW`
  (`X64WakeMapped.hmapped_of`).
- `cert_step`: PROVED (`X64WakeCert.certAll_step_of`) from `WCompat`, `WCompat0`,
  `KR`, the transport `X64WakeEnv.henv_of` and the conversion `hconv`.
- `hconv`: PROVED (`X64WakeConv1.hconv_of'`) from `WCompat`, `WCompat0` (its
  `relW0`), `WCompatX`, `hwf` and the worker's write fact `hW1`: OPEN.
- `hwide`: PROVED (`X64WakeWide.hwide_of_placeOKAt`) from `placeOKAt` and
  the parse `hpa`.
- `post_wit`: OPEN. -/
theorem wake_obligations {Ab Ac : State → Prop}
    /- (at `Λ := (RuntimeLayout.ofPlaceW hp i).Λ`: `WakeQ.hwf_ofPlaceOK`) -/ (hwf : Λ.WF)
    /- (the relation's data, `rfl` at `WakeQ.wakeQ`: `WakeQ.hPT0`,
    `WakeQ.hKR`, `WakeQ.hown`) -/
    (hPT0 : Q.PT0 = X64WakeM0.PT0 M) (hKR : Q.KR = X64WakeKR.KR r0 r1)
    (hown : Q.own = X64WakeOwnX.wakeOwnXW T W)
    /- (worker side; `wCompat_of` / `wCompatX_of`) -/
    (hC : WCompat Q D ((target (kernel 2) E).marks asm Λ) Λ arch) (hx : WCompatX Q D)
    /- (main's side; 16 fields (16th `relW0`), as in
    `Spike/Lib/WakeM0Compat.lean`) OPEN -/
    (hC0 : X64WakeM0.WCompat0 Q M ((target (kernel 2) E).marks asm Λ) Λ)
    /- OPEN -/ (hstart : ∃ d, (target (kernel 1) E).load asm Λ = some d)
    /- OPEN: the pre-spawn half; planned discharge
    `WakePreAsm.pre1T_of_seg` (wake-pre 19bdf3d3) with `wake_init` (6136751f) -/ (O : Pre1T arch Λ B asm E Q.R1 Ab Ac)
    /- (consumes `main_closed_wake` (its `hS` by
    `WakeHS.hS_ofPlaceOK`, hello-rt 22e6d5a5), `post_startW`) OPEN -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), Q.R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (wakeS arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s')
    /- `post_progress`'s named facts (`X64WakeProgress.post_progress_of`):
 OPEN: at a system call main's state has an instruction -/
    (hhalt0 : ∀ w s c, M.Mi w s c → abi.atSys s = true → (isa.exec s).isSome)
    /- OPEN: at a system call the worker's state has an instruction -/
    (hhalt1 : ∀ w s c, D.Wi w s c → abi.atSys s = true → (isa.exec s).isSome)
    /- `hmapped` by `X64WakeMapped.hmapped_of` from the per-node facts:
 OPEN: main's instructions touch only locations mapped at the load -/
    (hmapM : ∀ w s c, M.Mi w s c → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (X64Consumer.K0 Λ) w l = false) e)
    /- OPEN: the worker's instructions touch only locations mapped at the load -/
    (hmapW : ∀ w s c, D.Wi w s c → abi.atSys s = false → ∀ e, isa.exec s = some e →
      ¬ Touches (fun l w => Kernel.mapped (X64Consumer.K0 Λ) w l = false) e)
    /- (`rfl`-like at the instance, `WakeWorkerSide.wake_hμ`) main's side's
    marks are the loaded program's, so `X64WakeM0.MSide.off` (every abort kind)
    puts main's invariant at no abort site; with `kr_live` and the worker's
    `WCompat.sysOk`, `X64WakeNoAbort.post_abort_of` proves `post_abort`
    vacuously -/
    (hMμ : M.μ = (target (kernel 2) E).marks asm Λ)
    /- `hwide` (`runInv_load`) by `X64WakeWide.hwide_of_placeOKAt` from the
    placement check and the loader's parse of the listing (the trust boundary;
    at `asm := SccCertificate.asm`, `o := RuntimeLayout.ofPlaceW hp i`) -/
    {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg Λ po) (hpa : cellsOf asm = some po.prog)
    /- `hconv` by `X64WakeConv1.hconv_of'` (main by `WCompat0.relW0`, the
    worker by `X64WakeW1.CInv`) from the worker's write fact: (with the
    worker facts, `ZX.hW1_ofX`) OPEN: every write of the worker's
    instructions is a release write, at most one per path -/
    (hW1 : ∀ w s c e, D.Wi w s c → isa.exec s = some e → EvTree.RelW1 Arch.tso e)
    /- (own/PhRec2; `WakePostWit.post_wit_of`) OPEN -/
    (post_wit : ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s) :
    WakeObligations arch Λ B asm Q E (TiPre Ab Ac) where
  hwf := hwf
  hstart := hstart
  pre_init := O.init
  pre_step := O.step
  spawn := spawn
  post_step0 _ _ _ _ hP hs := X64WakeM0.post_step0_of hC hC0 hPT0 hKR hwf hP hs
  post_step1 _ _ _ _ hP hnu hnt hs := post_step1_of hC hx hwf hP hnu hnt hs
  unpark_src _ _ _ _ hP hu hs := unpark_src_of hC hx hwf hP hu hs
  worker_done := worker_done (texitFacts_of hC hKR)
  pre_progress := O.pre_progress
  post_progress t s hP hri hca := X64WakeProgress.post_progress_of hC hC0 hPT0 hKR (hMμ ▸ M.off) hhalt0 hhalt1 hP
    hca (X64WakeMapped.hmapped_of hPT0 hC.pt1 hKR hmapM hmapW t s hP hri)
  hwide := X64WakeWide.hwide_of_placeOKAt hpl hpa
  cert_step := X64WakeCert.certAll_step_of hC hC0 hPT0 hKR (X64WakeEnv.henv_of hC hC0 hPT0 hKR)
    (X64WakeConv1.hconv_of' hC hC0 hx hwf hPT0 hKR hW1)
  hconv := X64WakeConv1.hconv_of' hC hC0 hx hwf hPT0 hKR hW1
  ti_load := O.ti_load
  ti_step := O.ti_step rfl (hpost_of fun _ _ hP =>
    X64WakePostAb.post_last_kr (fun _ _ _ h => by rw [hKR] at h; exact h) hP)
  pre_abort := O.pre_abort (fun _ _ h => h)
  post_abort := X64WakeNoAbort.post_abort_of (fun w t s hk => by rw [hKR] at hk; exact X64WakeKR.kr_live hk)
    (fun w _ _ t0 s0 h hl => by rw [hPT0] at h; exact hMμ ▸ M.off w _ _ (h.1.resolve_right hl))
    (X64WakeNoAbort.sys1_of hC)
  pre_wit := O.pre_wit
  post_wit := post_wit

end Spike.Lib.X64WakeAssembly

/-- info: 'Spike.Lib.X64WakeAssembly.wCompatX_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeAssembly.wCompatX_of

/-- info: 'Spike.Lib.X64WakeAssembly.wCompat_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeAssembly.wCompat_of

/-- info: 'Spike.Lib.X64WakeAssembly.texitFacts_of' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeAssembly.texitFacts_of

/-- info: 'Spike.Lib.X64WakeAssembly.wake_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeAssembly.wake_obligations
