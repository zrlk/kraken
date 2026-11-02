/-
**hello.w on x86-64: the return of `print`'s `write(1, …)`** (the twin of `Spike/Lib/HelloEmitRet.lean`). The kernel's
return of the worker's `write(1, buf, n)` with `j = wr 1` bytes out (`X64HelloPostAb.write_ret_cases`) keeps `Post`,
landing at `PT1h`, from the common parts (`PartsC`: `PartsH` in the print phase or `PartsE`):
- `j > 0` (`r = j`): the link (`X64HelloKRE.Lk`) puts the source worker at the emit row's `Pw j` (`EmitR`; a `write`
  to another descriptor contradicts the decode), whose return clause (`EmitCl`'s second) puts the returned state in
  `D.Wi` at the source worker's control; the source stutters; the kernel sets the slot running at 0, so the link
  holds again (`lk_wr0`);
- `j = 0` (`-EINTR`, `-EAGAIN` or a refusal): the worker is in `D.Wi` at the source worker's control (`hWi0`), the
  emit row (`X64HelloEmitShapeF.EmitShapeF`) gives a frame run of the source into `Pw 0` (possibly entering or
  leaving `print`), whose return clause puts the returned state in `D.Wi` at the frames reached
  (`post_frameRunH`, at any frame run). A refusal's `writeErr` is not observed (`obs`), so the source runs no abort.

- `PartsC.toH`: the common parts with `D.Wi` at the source worker's control are `PartsH`.
- `krW_run0`: `KrW` with the worker's slot set running at 0 (`KRHE`, the link from `lk_wr0`).
- `post_stutC`: from the common parts, thread 1 replaced by `t1'` in `D.Wi` at the unchanged source worker, the
  source stuttering, `Post` (`X64HelloW1.post_frameH`).
- `post_retC`: the return.

## Differences from the AArch64 version

- The target threads are over `X64.isa` and the kernel's architecture is `Arch.tso` (AArch64: `isaLSE2`,
  `Arch.armv8`); the runtime facts are `X64WakeA64`'s and the source, worker side, phases and kernel relation are
  the x86-64 twins (`X64HelloSrc`, `X64HelloW1`, `X64HelloEmitPh`, `X64HelloEmitPost`, `X64HelloKRE`,
  `X64HelloWriteK`, `X64HelloPostAb`). The statements and proofs are otherwise the AArch64 ones.
-/
import Spike.Lib.X64HelloEmitPost
import Spike.Lib.X64HelloStep1P
import Spike.Lib.X64HelloPostAb
import Spike.Lib.X64HelloEmitShapeF
import Spike.Lib.X64HelloOwn1

namespace Spike.Lib.X64HelloEmitRet

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Scc.Sem Scc.Sem.X64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.WorkerSrc
open Spike.Lib.Inv2Core Spike.Lib.Inv2Read Spike.Lib.HelloProt
open Spike.Lib.X64HelloSrc (helloSrc helloS)
open Spike.Lib.X64HelloW1 (WSideH PT1h PartsH PrintPh WCompatH KrW krW_of printPh_not_pass)
open Spike.Lib.X64HelloStep1P (post_frameRunH)
open Spike.Lib.X64HelloEmitPh (PT1hE)
open Spike.Lib.X64HelloEmitPost (PartsC)
open Spike.Lib.X64HelloWriteK (KRH krh_set1_run krh_frame1)
open Spike.Lib.X64HelloKRE (KRHE)
open Spike.Lib.X64WakeW1 (withThread1)

variable {Q : WakeRel} {D : WSideH Q.ι} {μ : Marks} {Λ : Scc.Sem.Layout} {arch : WeakMem.Arch}
  {AbW : isa.State → Prop}
  {w : Q.ι} {t : Cfg} {s : TermRun.Cfg} {t0 t1 : Thread isa} {s0 s1 : TermRun.TTh}
  {ts : Nat → Option Nat} {tp sp : List Nat} {oc : Option (Nat × Nat)} {r0 r1 : Q.ι → Range}

/-- **The common parts with `D.Wi` at the source worker's control are `PartsH`.** -/
theorem PartsC.toH (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hwi : D.Wi w t1.st (Ctl.of s1) s1.stack) :
    PartsH Q D Λ w t s t0 t1 s0 s1 ts tp sp oc :=
  ⟨h.th, h.ths, h.core, h.preC, h.pt0, ⟨hwi, h.σs, .inl ⟨h.ph, h.bufV, h.term, h.noEm⟩, h.plen, h.pprom, h.nodup⟩,
    h.prot, h.kr⟩

/-- **`KrW` with the worker's slot set running at 0** (`KRHE`): `KRH` kept (`krh_frame1`, `krh_set1_run`), the
link from no byte out with the worker in `D.Wi` (`lk_wr0`). -/
theorem krW_run0 (hKR : Q.KR = KRHE D r0 r1) (hk0 : Q.KR w t s) (hth : t.1.threads = #[t0, t1])
    {t1' : Thread isa} {mem' : Memory} {s1' : TermRun.TTh} :
    KrW Q D w t s t1' mem' s1' (t.2.set 1 (.run 0)) := by
  intro s' hs0 hs1' htr hW
  rw [hKR] at hk0 ⊢
  have hf : KRH r0 r1 w (t.1.withThread 1 t1' mem', t.2) s' :=
    krh_frame1 w t _ s s' hk0.1 rfl hs0 (fun _ hx => by simpa only [SrcSem.traceOf, htr] using hx)
  refine ⟨krh_set1_run 0 hf _, X64HelloKRE.lk_wr0 (X64HelloKRE.wr_set_run0_self _ _) fun u1 v1 h1 h2 => ?_⟩
  have e1 : (t.1.withThread 1 t1' mem').threads[1]? = some t1' := by rw [withThread1 hth]; rfl
  obtain rfl : u1 = t1' := Option.some.inj (h1.symm.trans e1)
  obtain rfl : v1 = s1' := Option.some.inj (h2.symm.trans hs1')
  exact hW

/-- **The source stuttering, thread 1 replaced keeps `Post`** (from the common parts): `t1'` with `t1`'s
promises, its bound, cover and no-promise fact at the memory, in `D.Wi` at the unchanged source worker (so before
the store point, as the print phase is: `WCompatH.pass`), the kernel relation by `hkr`. -/
theorem post_stutC (hC : WCompatH Q D μ Λ arch AbW) (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc)
    (hown : X64HelloOwn1.Own1H Q D Λ) {t1' : Thread isa} {k' : KState} (hkr : KrW Q D w t s t1' t.1.mem s1 k')
    (hp : t1'.prom = t1.prom) (hb : t1'.Bnd t.1.mem.last)
    (hcov : CohCoversL t1'.views t1'.prom t.1.mem ((Q.P w).cov 1))
    (hnp : (Q.P w).noProm t1'.st → t1'.prom = []) (hwi : D.Wi w t1'.st (Ctl.of s1) s1.stack) :
    Q.Post Λ (t.1.withThread 1 t1' t.1.mem, k') s := by
  have hnp1 : ¬ WPass s1 := printPh_not_pass h.ph
  have hpT' : (Q.C w).passT t1'.st ↔ WPass s1 := hC.pass w _ s1 hwi (.inl h.ph)
  have hpS := X64HelloW1.PartsH.passS_iff (w := w) hC s1
  obtain ⟨hT, hS, hl⟩ := (cProt_iff _ _ _).mp h.prot
  have hpT : ¬ (Q.C w).passT t1.st := fun hq => hnp1 (hpS.mp (hl.mp hq))
  have ho : ExtRows.OwnOk (Q.own w 1 t1'.st s1.stack) t.1.mem t1'.prom := by
    have h1 : ExtRows.OwnOk (Q.own w 1 t1.st s1.stack) t.1.mem t1.prom := by simpa using h.core.own1
    rw [hp, hown.const w t1.st s1.stack t1'.st s1.stack]; exact h1
  refine X64HelloW1.post_frameH (ts' := ts) (tp' := tp) (sp' := sp) hC h.th h.ths h.ths h.preC h.pt0 hkr
    h.core.T_le ⟨.inl rfl, .inl rfl⟩ ?_ ⟨hwi, h.σs, .inl ⟨h.ph, h.bufV, h.term, h.noEm⟩, h.plen, h.pprom, hp ▸ h.nodup⟩
    ⟨oc, (cProt_iff _ _ _).mpr ⟨⟨hT.tmsg, hT.some_msg, fun Tc kc hoc htp => hp ▸ hT.prom_worker Tc kc hoc htp,
      fun hq => absurd (hpT'.mp hq) hnp1, fun _ => hT.pass_prom hpT⟩, hS, hpT'.trans hpS.symm⟩⟩ rfl
  refine core1_same h.core (by simp) hp rfl hb hcov h.core.scov1 ?_ ?_ ?_ hnp
  · simpa only [Nat.one_ne_zero, ite_false] using ho
  · intro L v v' h0 h1
    simp only [ite_true] at h0
    simp only [Nat.one_ne_zero, ite_false] at h1
    exact hC.ownDisj w _ _ _ _ L v v' h0 h1
  · intro L v h1
    simp only [Nat.one_ne_zero, ite_false] at h1
    exact hC.ownCov w _ _ L v h1

/-- **The return of `print`'s `write(1, …)` keeps `Post`** (the twin of
`X64HelloEmitStep.post_byteC` at a return pick), landing at `PT1h`: after `j = wr 1 > 0` bytes (`r = j`) the
link's `EmitR` at `Pw j` and its return clause, the source stuttering, the slot running at 0 (`post_stutC`,
`krW_run0`); with none (`-EINTR`, `-EAGAIN` or a refusal, `WriteRetOk 0`), the emit row's frame run into `Pw 0`
(`EmitShapeF`, at `D.Wi` by `hWi0`) and its return clause at the frames reached (`post_frameRunH`). `hNP` is
`X64WakeW1.WCompat.noProm` (`HelloCompat`'s second part). -/
theorem post_retC (hC : WCompatH Q D μ Λ arch AbW) (hKR : Q.KR = KRHE D r0 r1) (_hpt1 : Q.PT1 = PT1hE D)
    (hES : X64HelloEmitShapeF.EmitShapeF D) (hown : X64HelloOwn1.Own1H Q D Λ)
    (hNP : ∀ w x (t : Thread isa) mem, (Q.P w).noProm t.st →
      CertOkC Arch.tso (certSem abi Arch.tso μ x 1) 1 t mem → t.prom = [])
    (h : PartsC Q D Λ w t s t0 t1 s0 s1 ts tp sp oc) (hex : SrcSem.mainExit s = [])
    (_hW : ∃ c fs, D.Wi w t1.st c fs) (hat : abi.atSys t1.st = true)
    (hWi0 : t.2.wr 1 = 0 → D.Wi w t1.st (Ctl.of s1) s1.stack)
    {buf n : Nat} (hd : decode abi.nrs (abi.nr t1.st) (abi.arg t1.st) = some (.write 1 buf n))
    {r : BitVec 64} {es : List Ev} {t' : Cfg} (hs : sysStep abi Arch.tso 1 t (.ret r) = some (es, t'))
    (hca : CertAfter abi Arch.tso μ 1 t') :
    ∃ s', (helloS arch).Run s (obs es) s' ∧ Q.Post Λ t' s' := by
  have ht1 : t.1.threads[1]? = some t1 := by rw [h.th]; rfl
  have hs1 : s.ths[1]? = some s1 := by rw [h.ths]; rfl
  have hc : callOf abi t1 = some (.write 1 buf n) := hd
  have hget : (t.1.withThread 1 (retThread abi t1 r) t.1.mem).threads[1]? = some (retThread abi t1 r) :=
    Live.Sem.withThread_get_self ht1
  have hb := ExtThread.bnd_retThread abi h.core.bnd1 r
  have hcov : CohCoversL (retThread abi t1 r).views (retThread abi t1 r).prom t.1.mem ((Q.P w).cov 1) := by
    rw [retThread_views abi t1 r, retThread_prom]; exact h.core.cov1
  have zero : t.2.wr 1 = 0 → (r = neg eintr ∨ r = neg eagain ∨ writeRefused r = true) →
      t' = (t.1.withThread 1 (retThread abi t1 r) t.1.mem, t.2) →
      ∃ s', (helloS arch).Run s [] s' ∧ Q.Post Λ t' s' := by
    rintro h0 hok rfl
    have hres := (Kernel.sysStep_ret_shape ht1 hc hs (fun _ _ _ e => by cases e; omega) nofun nofun).1
    have hH := PartsC.toH h (hWi0 h0)
    obtain ⟨c', fs', Pw, Qw, hfr, hPw, hcl⟩ := hES w t1.st s1 buf n (hWi0 h0) hat hd
    obtain ⟨hwi, -⟩ := hcl.2.1 0 (Nat.zero_le _) c' hPw r hres ⟨fun h' => absurd h' (Nat.lt_irrefl 0), fun _ => hok⟩
    exact post_frameRunH hC hH hown hex (krW_of hC h.kr h0 h.th) (q' := (c', fs')) (by rw [retThread_prom])
      hb hcov (fun hn => hNP w _ _ _ hn (hca _ hget)) hfr (by rw [retThread_st]; exact hwi)
  rcases X64HelloPostAb.write_ret_cases ht1 hc hs with ⟨hpos, hr, rfl, rfl⟩ | ⟨h0, hr, rfl, e⟩ | ⟨h0, hr, rfl, e⟩
  · -- `j > 0` bytes out: the link's `EmitR` at `Pw j`, the source stuttering
    have hk := h.kr
    rw [hKR] at hk
    obtain ⟨u1, v1, h1, h2, hE⟩ := hk.2.1 hpos
    obtain rfl : u1 = t1 := Option.some.inj (h1.symm.trans ht1)
    obtain rfl : v1 = s1 := Option.some.inj (h2.symm.trans hs1)
    rcases hE with ⟨buf', n', Pw, Qw, -, hd', hcl, hjn, hPw⟩ | ⟨fd, buf', n', hfd, -, hd', -⟩
    · have e := Option.some.inj (hd.symm.trans hd')
      cases e
      have hres : r ∈ results (.write 1 buf n) := by
        rw [hr]
        exact List.mem_append_left _ (List.mem_map.mpr ⟨_, List.mem_range.mpr (Nat.lt_succ_of_le hjn), rfl⟩)
      obtain ⟨hwi, -⟩ := hcl.2.1 _ hjn _ hPw r hres
        ⟨fun _ => hr, fun h0 => absurd h0 (Nat.pos_iff_ne_zero.mp hpos)⟩
      exact ⟨s, .refl _, post_stutC hC h hown (krW_run0 hKR h.kr h.th) (by rw [retThread_prom]) hb hcov
        (fun hn => hNP w _ _ _ hn (hca _ hget)) (by rw [retThread_st]; exact hwi)⟩
    · have e := Option.some.inj (hd.symm.trans hd')
      cases e
      exact absurd rfl hfd
  · exact zero h0 (hr.elim .inl (.inr ∘ .inl)) e
  · -- a refusal: its `writeErr` is not observed
    obtain ⟨s', hr', hp⟩ := zero h0 (.inr (.inr hr)) e
    exact ⟨s', hr', hp⟩

end Spike.Lib.X64HelloEmitRet

/-- info: 'Spike.Lib.X64HelloEmitRet.PartsC.toH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloEmitRet.PartsC.toH

/-- info: 'Spike.Lib.X64HelloEmitRet.krW_run0' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloEmitRet.krW_run0

/-- info: 'Spike.Lib.X64HelloEmitRet.post_stutC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloEmitRet.post_stutC

/-- info: 'Spike.Lib.X64HelloEmitRet.post_retC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64HelloEmitRet.post_retC
