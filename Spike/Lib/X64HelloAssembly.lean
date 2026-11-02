/-
**hello.w on x86-64: the `WakeObligations` assembly skeleton** (the twin of
`Spike.Lib.X64WakeAssembly.wake_obligations` at hello's source program
`helloSrc`, worker data `X64HelloEmitPh.PT1hE` and kernel relation
`X64HelloWriteK.KRH`). Every field of `WakeObligations … helloSrc` is
instantiated, from a proved lemma where one exists, otherwise from an
explicit named hypothesis whose comment names the lemma that discharges it.
No proof is deferred: the open pieces are exactly the hypotheses.

The relation's data is fixed as at `X64HelloQ.helloQ`: main's `PT0` is
`X64WakeM0.PT0 M` (`hPT0`), the kernel relation is `KRHE D r0 r1` (`hKR`; `KRH` and the worker's `write` link), the
worker's exit point is wake's (`hTx`); the trace invariant is
`X64WakePreTi.TiPre Ab Ac ∧ Tw` for a further trace invariant `Tw` (the
post-spawn abort obligations read it: `TiPre` is vacuous after the spawn), the
pre-spawn half one `X64WakePreTi.Pre1T … helloSrc`. The worker's data is hello's `PT1hE D` (`PT1h D` in the print
or store phase, or mid-`write`; `WCompatH.pt1`), not wake's: `X64HelloW1Store.relW`'s wake `PT1` covers
the store phase only (`post_ofW_store`), so the obligations are stated at
`Q`, and the store-phase bridge `X64WakeW1.WCompat (relW Q D hcw hem) …` is an
input of the post-spawn obligations (`HelloCompat`).

Proved here (the lemmas are generic in the source program, and read only
`KRH`'s slot conjuncts):
- `pre_init`, `pre_step`, `pre_progress`, `pre_abort`, `pre_wit`: `Pre1T`'s;
- `ti_load`: `Pre1T.ti_load` and `Tw`'s at the load (`tw_load`);
- `worker_done`: `X64WakePost1.worker_done` with `HelloInst.texitFactsH`;
- `ti_step`: `Pre1T.ti_step` with `hpost` by `X64WakePostAb.post_last_of`
  (`KRH`'s two slots, the second not dormant), and `Tw`'s step (`tw_step`);
- `hwide`: `X64WakeWide.hwide_of_placeOKAt`.

Open, collected in `HelloRows` (each the field given the compatibility
facts `HelloCompat`):
`post_step0` (`KRH` twin of `X64WakeM0Post.post_step0_of`),
`post_step1` (under the run invariant: the print phase's lemmas
`X64HelloW1Print.post_*P`, the store phase's through `relW`), `unpark_src` (through
`relW`), `post_progress`, `cert_step`,
`hconv`, `post_abort` (the print phase's refused
write and `exit_group`, from `Tw`); `post_wit`; `tw_load`,
`tw_step`. Further premises: `hstart`, `O`, `spawn`.

- `HelloCompat`: hello's compatibility facts at `Q`: `WCompatH`, wake's
  `WCompat` at `relW` (the store phase), `WCompatXH`, `WCompat0`.
- `HelloRowsW`, `HelloRows`: the open obligations, one field each (`HelloRowsW`
  without main's step, the worker's unpark, `post_progress` and
  `cert_step`).
- `hello_obligations`: the assembly, as `X64HelloObligR.WakeObligationsR`
  (`WakeObligations` with the run invariant at the worker's steps:
  `post_step1` reads `RunInv` for the worker's `write`'s private keys,
  `X64HelloStep1.privAt_of_runInv`; `hello_correctE_R` concludes as
  `wake_correctE`).

x86-64 twin of `Spike/Lib/HelloAssembly.lean` (same names, namespaces with the `X64` prefix).
Unlike AArch64, the program is an `asm : Asm` whose cells are the placement
output's (`cellsOf asm = some po.prog`, not `textProgram`), the placement
check is `PlaceWX` at `Scc.Cert.PlaceOK.X64.Out`, the certification
architecture is `Arch.tso`, and the worker's facts after the freeze
(`WCompatXH`) come from `X64HelloWorkerRRC`.
-/
import Spike.Lib.X64WakeAssembly
import Spike.Lib.X64HelloW1StoreC
import Spike.Lib.X64HelloWorkerRRC
import Spike.Lib.X64HelloObligR

namespace Spike.Lib.X64HelloAssembly

open Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakePreTi Spike.Lib.Handover
open Spike.Lib.X64HelloSrc (helloSrc)
open Spike.Lib.X64HelloW1 (WSideH PT1h WCompatH)
open Spike.Lib.X64HelloW1Store (relW wsideW NoWrite)
open Spike.Lib.X64HelloWorkerRR (WCompatXH)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64HelloWriteK (KRH)

/-- **`worker_done`'s facts at `KRHE`** (`X64HelloInst.texitFactsH` with the
`write` link): the worker's slot exited has no byte out (`wr_set_exited`),
and the worker, at its `exit` call, is in `Wi`: off it, `Lk` would put it
mid-`write` (`EmitR`/`WrOth`), not at `exit`. -/
theorem texitFactsHE {Q : WakeRel} {D : WSideH Q.ι} {r0 r1 : Q.ι → Range} (hx : Q.atTexit = X64WakeW1.atTexit)
    (hKR : Q.KR = KRHE D r0 r1) : X64WakePost1.TexitFacts Q :=
  X64WakeW1.texitFacts hx fun w t s h hX => by
    rw [hKR] at h ⊢
    rw [hx] at hX
    obtain ⟨t1, ht1, -, hc⟩ := hX
    refine ⟨X64HelloWriteK.krh_exit1 w t s h.1,
      X64HelloKRE.lk_wr0 (X64HelloKRE.wr_set_exited _ _) fun t1' s1 ht hs => ?_⟩
    have ht' : t.1.threads[1]? = some t1' := ht
    rw [ht1] at ht'
    cases ht'
    refine Classical.byContradiction fun hW => ?_
    obtain ⟨t1'', s1', h1, -, hE⟩ := h.2.1 (h.2.2 t1 s1 ht1 hs hW)
    rw [ht1] at h1
    cases h1
    have hc' : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some .exit := hc
    rcases hE with ⟨_, _, _, _, -, hd, -⟩ | ⟨_, _, _, -, -, hd, -⟩ <;> rw [hc'] at hd <;> cases hd

/-- **hello's compatibility facts at `Q`**: hello's worker facts
(`WCompatH`), wake's at the store-phase bridge `relW` (`X64WakeW1.WCompat`),
the worker's facts after the freeze (`WCompatXH`) and main's (`WCompat0`). -/
def HelloCompat (Q : WakeRel) (D : WSideH Q.ι) (M : X64WakeM0.MSide Q.ι) (μ : Marks) (Λ : Scc.Sem.Layout)
    (arch : WeakMem.Arch) (AbW : isa.State → Prop) (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0)
    (hem : NoWrite D) : Prop :=
  WCompatH Q D μ Λ arch AbW ∧ X64WakeW1.WCompat (relW Q D hcw hem) (wsideW D hcw hem) μ Λ arch ∧
    WCompatXH Q D ∧ X64WakeM0.WCompat0 Q M μ Λ

variable {arch : WeakMem.Arch} {Λ : Scc.Sem.Layout} {B : Budget} {asm : Asm} {Q : WakeRel} {E : Entry}
  {D : WSideH Q.ι} {M : X64WakeM0.MSide Q.ι} {r0 r1 : Q.ι → Range} {AbW : isa.State → Prop}
  {hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0} {hem : NoWrite D}

/-- **The open obligations of the assembly at hello's source other than main's
step, the worker's unpark, progress and the steps' keeping `CertAll`**
(`X64HelloM0Post.post_step0H`, `X64HelloUnpk.unpark_srcH`,
`X64HelloProgress.post_progressH` and `X64HelloCert.cert_stepH` prove those): one field per
`WakeObligations` field not proved here, each read under the compatibility
facts `HelloCompat` where its twin reads wake's (the field comments name
the lemmas that discharge them). Consumed by `HelloRows`, hence by
`hello_obligations`. -/
structure HelloRowsW (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : Asm) (Q : WakeRel)
    (E : Entry) (D : WSideH Q.ι) (M : X64WakeM0.MSide Q.ι) (AbW : isa.State → Prop)
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) (Ab Ac : State → Prop)
    (Tw : Cfg → List Ev → Prop) : Prop where
  /-- (The print phase by `X64HelloW1Print.post_setP` /
  `post_keepP` / `post_callP` / `post_retP`, the store phase by
  `X64WakeW1.post_step1_of` at `relW` with `post_toW` / `post_ofW`). A step
  of the worker other than its unpark and exit steps keeps `Post`. -/
  post_step1 : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t es t' s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ¬ Q.atUnpk t s → ¬ Q.atTexit t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (`KRH` twin of `X64WakeConv1.hconv_of'`, with the
  worker's `hW1`). At `Post` a running thread's certification is
  append-free. -/
  hconv : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t s, Q.Post Λ t s → CertConv ((target (kernel 2) E).marks asm Λ) t
  /-- (The print phase's refused write and `exit_group
  abortStatus` justified, `WCompatH.sysOkH`'s `AbW` branch). An abort step
  after the spawn is justified. -/
  post_abort : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tr t s tid es t' k, (srcS helloSrc arch).Reach (obs tr) s → Q.Post Λ t s →
      TiPre Ab Ac t tr ∧ Tw t tr →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Ev.abort k ∈ es →
      ∃ w i, Components (machine (kernel 2)) Λ w t s ∧ w.thr i = some tid ∧
        AbortJustified B (srcS helloSrc arch) tr s i k
  /-- (Twin of `X64WakePostWit.post_wit_of`). The
  explicit witness after the spawn. -/
  post_wit : ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → ∃ w, Components (machine (kernel 2)) Λ w t s
  /-- (`X64HelloPostAb`.) The further trace invariant holds at
  the load ... -/
  tw_load : ∀ t0, (target (kernel 2) E).load asm Λ = some t0 → Tw t0 []
  /-- (`X64HelloPostAb`.) ... and a related step extends it by its
  events. -/
  tw_step : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tid t es t' s pre, Q.Rw Λ t s →
    (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Tw t pre → Tw t' (pre ++ es)

/-- **The open obligations of the assembly at hello's source**: `HelloRowsW`,
main's step, the worker's unpark, progress and the steps' keeping
`CertAll`. Consumed by `hello_obligations`. -/
structure HelloRows (arch : WeakMem.Arch) (Λ : Scc.Sem.Layout) (B : Budget) (asm : Asm) (Q : WakeRel)
    (E : Entry) (D : WSideH Q.ι) (M : X64WakeM0.MSide Q.ι) (AbW : isa.State → Prop)
    (hcw : ∀ w, ∃ cS, (D.cw w).val = .loc cS 0) (hem : NoWrite D) (Ab Ac : State → Prop)
    (Tw : Cfg → List Ev → Prop) : Prop extends HelloRowsW arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw where
  /-- (`KRH` twin of `X64WakeM0Post.post_step0_of`). A step
  of main keeps `Post`. -/
  post_step0 : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t es t' s, Q.Post Λ t s → (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 0 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (`X64WakeW1.unpark_src_of` at `relW`, the unpark in
  the store phase). The worker's unpark is the source unpark. -/
  unpark_src : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t es t' s, Q.Post Λ t s → Q.atUnpk t s →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) 1 t es t' →
      ∃ s', (srcS helloSrc arch).Run s (obs es) s' ∧ Q.Post Λ t' s'
  /-- (`X64HelloProgress.post_progressH`, the `KRH` twin of
  `X64WakeProgress.post_progress_of`, given `hhalt0`/`hhalt1`/`hmapM`/`hmapW`). Progress and layout after the
  spawn. -/
  post_progress : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ t s, Q.Post Λ t s → X64WakeRunInv.RunInv Λ E t → CertAll ((target (kernel 2) E).marks asm Λ) t →
      (machine (kernel 2)).Progress ((target (kernel 2) E).marks asm Λ) t ∧
        InLayout (M := machine (kernel 2)) Λ t
  /-- (`KRH` twins of `X64WakeCert.certAll_step_of` and
  `X64WakeEnv.henv_of`). A step from `Post` to `Post` keeps `CertAll`. -/
  cert_step : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem →
    ∀ tid t es t' s s', Q.Post Λ t s → CertAll ((target (kernel 2) E).marks asm Λ) t →
      (machine (kernel 2)).Step ((target (kernel 2) E).marks asm Λ) tid t es t' → Q.Post Λ t' s' →
      CertAll ((target (kernel 2) E).marks asm Λ) t'

/-- **The assembly at hello's source, worker data and kernel relation** (see
the module doc). -/
theorem hello_obligations {Ab Ac : State → Prop} {Tw : Cfg → List Ev → Prop}
    /- (instance; `PlaceWX`) -/ (hwf : Λ.WF)
    /- (instance; `rfl` at `X64HelloQ.helloQ`) -/
    (hKR : Q.KR = KRHE D r0 r1) (hTx : Q.atTexit = X64WakeW1.atTexit)
    /- (instance; `X64HelloWorkerRR.hC_IR`, `X64HelloW1Store.wcompat_relW_IR`,
    `X64HelloWorkerRR.hx_IR`, `X64HelloMs.hC0Ms`) -/
    (hC : HelloCompat Q D M ((target (kernel 2) E).marks asm Λ) Λ arch AbW hcw hem)
    /- The program loads at one slot. -/
    (hstart : ∃ d, (target (kernel 1) E).load asm Λ = some d)
    /- (`hbuf` in `R1`.) The pre-spawn half. -/
    (O : Pre1T arch Λ B asm E Q.R1 Ab Ac helloSrc)
    /- (The instance; `X64HelloSpawnR.spawn_RH`.) -/
    (spawn : ∀ tid d s th stack tls (r : BitVec 64), Q.R1 d s → d.1.threads.size = d.2.slots.size →
      d.1.threads[tid]? = some th → abi.atSys th.st = true → d.2.runs tid = true → d.2.exited = none →
      callOf abi th = some (.clone stack tls) → 0 < r.toNat → r.toNat < pidMax →
      CertAfter abi Arch.tso ((target (kernel 2) E).marks asm Λ) tid (afterClone abi d tid th stack tls r) →
      ∃ s', (srcS helloSrc arch).Run s [] s' ∧ Q.Post Λ (afterClone abi d tid th stack tls r) s')
    /- The post-spawn obligations; see `HelloRows`' fields. -/
    (R : HelloRows arch Λ B asm Q E D M AbW hcw hem Ab Ac Tw)
    /- the placement check at the layout and the loader's parse (the trust
    boundary) -/
    {pcfg : Scc.Cert.PlaceOK.Config} {po : Scc.Cert.PlaceOK.X64.Out}
    (hpl : PlaceWX pcfg Λ po) (hpa : cellsOf asm = some po.prog) :
    WakeObligationsR arch Λ B asm Q E (fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) helloSrc where
  hwf := hwf
  hstart := hstart
  pre_init := O.init
  pre_step := O.step
  spawn := spawn
  post_step0 := R.post_step0 hC
  post_step1 := R.post_step1 hC
  unpark_src := R.unpark_src hC
  worker_done := X64WakePost1.worker_done (texitFactsHE hTx hKR)
  pre_progress := O.pre_progress
  post_progress := R.post_progress hC
  hwide := X64WakeWide.hwide_of_placeOKAt hpl hpa
  cert_step := R.cert_step hC
  hconv := R.hconv hC
  ti_load t0 h := ⟨O.ti_load t0 h, R.tw_load t0 h⟩
  ti_step tid t es t' s pre hR hs hT :=
    ⟨O.ti_step rfl (hpost_of fun _ _ hP =>
      X64WakePostAb.post_last_of (fun w t s h => by rw [hKR] at h; exact ⟨h.1.1, h.1.2.2.1⟩) hP)
      tid t es t' s pre hR hs hT.1, R.tw_step hC tid t es t' s pre hR hs hT.2⟩
  pre_abort := O.pre_abort (Ti := fun t tr => TiPre Ab Ac t tr ∧ Tw t tr) (fun _ _ h => h.1)
  post_abort := R.post_abort hC
  pre_wit := O.pre_wit
  post_wit := R.post_wit

end Spike.Lib.X64HelloAssembly

/-- info: 'Spike.Lib.X64HelloAssembly.texitFactsHE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssembly.texitFactsHE

/-- info: 'Spike.Lib.X64HelloAssembly.hello_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloAssembly.hello_obligations
