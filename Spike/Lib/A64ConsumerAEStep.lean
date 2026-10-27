/-
**A step of the consumer through `print`'s `write`**
(`Spike/Lib/A64ConsumerAE.lean`): every step from `RSAE` is matched by a
source run landing in `RSAE` (`r_stepAE`).

- `noExit_trace`: under WeakCore's output hook, no exit in the hook's trace
  is no exit event in the source's trace.
- `sysStep_write_retOk`: a return of the kernel's `write` after `j` bytes is
  one `WriteRetOk j` allows, of `results`, to `retThread`.
- `allocInvAt_hold`: `AllocInvAt` reads the control's hold only.
- `pre_emitA`: at a `write(1, …)` from `PreSA` with no byte out, the source
  enters the emit row (`EmitSA` at 0).
- `emit_stepAE`: every step from `EmitSA`: a byte, the source emitting it
  (`byteOut_emit_ld`) into `EmitSA` at `j + 1`; a return, the row's return
  clause into `PreSA`; a promise, stuttering (`PromSharedAE`).
- `wr1Zero_step`: off the output `write`, every step from `PreSA` lands with
  `Wr1Zero`.
- `pre_stepAE`, `r_stepAE`: the step from `RSAE`.
-/
import Spike.Lib.A64ConsumerAE
import Spike.Lib.A64ConsumerAStep
import Spike.Lib.ByteOutLd

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS
open Spike.Lib.ByteOut (ByteOut byteOut_emit_ld)
open Spike.Lib.DmemPriv (PrivInv PrivKeys)
open Spike.Lib.LowerNode (SrcNumSP PrintLd)

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {Top : Ctl → Prop} {Ent : Entry}

/-- **No exit event in the source's trace** from none in WeakCore's output
hook's (the converse of `PrintSrc.noExit_hook`). -/
theorem noExit_trace (hW : SrcOutProto.UsesWc P p) {s : TermRun.Cfg} (h : ∀ c, Ev.exit c ∉ P.hooks.trace s) :
    ∀ x, TermRun.Event.exit x ∉ s.trace := fun x hx => by
  apply h ⟨x % 256, Nat.mod_lt _ (by decide)⟩
  rw [hW]
  exact List.mem_filterMap.mpr ⟨_, hx, rfl⟩

/-- **A return of the kernel's `write`** after `j = wr 0 ≤ n` bytes: a
result `WriteRetOk j` allows, one of `results`, to `retThread`. -/
theorem sysStep_write_retOk {A : Arch} {c c' : Config isaLSE2 × Kernel.KState} {th : Thread isaLSE2}
    {fd buf n : Nat} {r : BitVec 64} {es : List Ev} (ht : c.1.threads[0]? = some th)
    (hc : Kernel.callOf abi th = some (.write fd buf n)) (hwr : c.2.wr 0 ≤ n)
    (h : Kernel.sysStep abi A 0 c (.ret r) = some (es, c')) :
    WriteRetOk (c.2.wr 0) r ∧ r ∈ Kernel.results (.write fd buf n) ∧
      c'.1.threads[0]? = some (Kernel.retThread abi th r) := by
  obtain ⟨hres, s0, ht', hs0⟩ := Kernel.sysStep_ret_shape ht hc h (fun _ _ _ e => by cases e; exact hwr) nofun nofun
  rcases hs0 with ⟨-, rfl⟩ | ⟨a, ha, -⟩
  · refine ⟨?_, hres, ht'⟩
    unfold Kernel.sysStep at h
    rw [ht] at h
    simp only at h
    split at h
    · cases h
    rw [hc] at h
    simp only at h
    refine ⟨fun hj => ?_, fun hj => ?_⟩
    · simp only [hj, ↓reduceIte] at h
      split at h
      · assumption
      · cases h
    · simp only [show ¬ 0 < c.2.wr 0 by omega, ↓reduceIte] at h
      split at h
      · rename_i hr; rcases hr with hr | hr
        · exact .inl hr
        · exact .inr (.inl hr)
      · split at h
        · rename_i hr; exact .inr (.inr hr)
        · cases h
  · cases ha

/-- **`AllocInvAt` at a control with no hold** is `AllocInvAt` at any
other with none (the allocation idle). -/
theorem allocInvAt_hold {lbl : Lbl} {lsize : Lsize} {th : Thread isaLSE2} {tm : Memory} {hu : Nat} {c c' : Ctl}
    (h : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c) (h0 : c.hold = none)
    (h0' : c'.hold = none) : AllocInvAt Λ lbl lsize th tm ar.heap ar.cells ar.ctr ar.units ar.off hu c' := by
  rcases h with ⟨hh, -⟩ | ⟨-, hc, ha⟩
  · rw [h0] at hh; cases hh
  · exact .inr ⟨fun w hw => (by rw [h0'] at hw; cases hw), hc, ha⟩

/-- **Into the output `write`**: at a pair of the fragment at a `write(1,
buf, n)` with no byte out (`wr 0 = 0`), the source takes the emit row's
frame run and local run to `Pw 0` (`EmitA.row`), landing in `EmitSA`. -/
theorem pre_emitA {ab : Option (State → Prop)} (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hE : EmitA Λ p I Top) {rS : Range} {Tk : State → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PreSA Λ P p G own I rS Tk μ ar t s) (hwz : Wr1Zero t) {th : Thread isaLSE2} {buf n : Nat}
    (hth : t.1.threads = #[th]) (hsys : abi.atSys th.st = true) (hc : Kernel.callOf abi th = some (.write 1 buf n)) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ EmitSA Λ P p G own I Top rS Tk μ ar t s' := by
  obtain ⟨th', th0, j, lbl, lsize, ts, hl, pm, hd, hth', ⟨E, hk⟩, hz, hh, -, hcert, hs0, hσ, hp, hI, hhi, hw,
    hb, hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  rw [hth] at hth'
  cases (Array.mk.injEq _ _).mp hth' |> List.cons.inj |>.1
  have hj : j = 0 := (wr_one hk).symm.trans (hwz th buf n hth hc)
  subst hj
  obtain ⟨c₁, fs₁, Pw, hr, hne, hpl, ⟨c', hlr, hpw⟩, hbody, htop⟩ := hE.row _ _ _ _ _ hI hsys buf n hc
  have hr' := hr.trans (FrameRun.ofLocal hlr fs₁)
  have hJ : EmitJ Λ p I Top (t.2.wr 0) lbl lsize th.st c' fs₁ := by
    rw [wr_one hk]
    exact ⟨(htop 0 (Nat.zero_le _) c' hpw).1, (htop 0 (Nat.zero_le _) c' hpw).2, hne, hpl, hsys, _, _, c₁, buf, n,
      Pw, hI, hr, hc, hbody, htop, Nat.zero_le _, hpw⟩
  exact pre_localJA (J := EmitJ Λ p I Top (t.2.wr 0)) hP hth hk hz hh hcert hs0 hσ hp hJ hw hb hinv hown hmi hfi
    hgi (by rw [hN.ownRun _ _ _ _ _ _ _ hr' (.inl hI)]; exact hoo) (allocInvAt_frameRun hai hr') hfr hco
    ⟨tr, hreach⟩ hhi (fun h0 => by rw [h0] at hI; exact hN.noRet _ _ _ _ hI) (fun h0 => absurd h0 hne) hr'

/-- **Every step from `EmitSA` is matched**: the thread is at the `svc` of
a `write(1, buf, n)` (no take, no instruction); a promise, the source
stuttering (`PromSharedAE`); a byte `j = wr 0`, the source's `print` byte
step emitting it (`byteOut_emit_ld`, `hpriv` from `PrivInv`), landing in
`EmitSA` at `j + 1`; a return, the row's return clause (`WriteRetOk`), its
frame run landing in `PreSA` at count 0. -/
theorem emit_stepAE {ab : Option (State → Prop)} (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) (hpsE : PromSharedAE Λ P p G own I Top rS Tk μ ar) (hwf : Λ.WF)
    (hEnt : Ent.clear Λ = true) {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev}
    (h : EmitSA Λ P p G own I Top rS Tk μ ar t s) (hpi : PrivInv abi WideSt Λ Ent t)
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSAE Λ P p G own I Top rS Tk μ ar Ent t' s' := by
  have hpre := h
  have hpi' : PrivInv abi WideSt Λ Ent t' := Spike.Lib.A64DmemPriv.privInv_step hpi hs
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, hz, hh, hwr, hcert0, hs0, hσ, hp, hJ, hhi, hw,
    hb, hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have h0 : s.ths[0]? = some th0 := by rw [hs0]; rfl
  have hJ0 := hJ
  obtain ⟨hh0, -, hfne, hpl, hsys, c₀, fs₀, c₁, buf, n, Pw, hI, hr0, hdc, hbody, htop, hjn, hpj⟩ := hJ
  obtain rfl : hd = none := hh0
  have hwj : t.2.wr 0 = j := wr_one hk
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => by
    obtain ⟨-, -, hsys', -⟩ := hT.site _ _ _ _ _ hI a ha hpc
    rw [hsys] at hsys'; cases hsys'
  have hsite := no_siteA hN ht1 hI hnt
  have hsp := no_spawnA (t' := t') hN hT ht1 hI
  have hwr' := wr_le hk hwr
  rcases A64Ext.step_cases_site ht1 hw hinv hs hsp hsite with
    ⟨-, hns, -⟩ | ⟨rfl, w, rfl, hinv', hc, hwt⟩ | ⟨pk, hsy, hcert, hi⟩
  · rw [hsys] at hns; cases hns
  · -- a promise: the source stutters
    have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
    have hsh := hpsE t s th w hpre hth hwt hc
    exact ⟨s, .refl _, .inl ⟨.inr ⟨_, th0, j, lbl, lsize, ts, hl, pm, none, withThread_one hth, ⟨E, hk⟩, hz, hh, hwr,
      hc, hs0, hσ, hp, hJ0, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩, hinv', ownMsgs_append hwt hown,
      memIn_append hsh.1 hmi,
      ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
      hgi.append hsh.2,
      ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hai.promise w rfl, hfr,
      hco, tr, hreach⟩, hpi'⟩⟩
  · -- a kernel step of the `write(1, buf, n)`
    obtain ⟨-, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsy hwr'
    obtain rfl : call = .write 1 buf n := Option.some.inj (hcall.symm.trans hdc)
    rcases hcases with ⟨fd, buf', n', rd', b, u, he, rfl, hlt, hrb, hust, hes, rfl⟩ |
      ⟨r, rfl, hx, hg, hev, hmem, u, hu, hsu, hpu⟩ | ⟨hex, -⟩ | ⟨v, hex, -⟩
    · -- a byte: `print`'s byte step
      obtain ⟨rfl, rfl, rfl⟩ : 1 = fd ∧ buf = buf' ∧ n = n' := by
        simp only [Kernel.Call.write.injEq] at he; exact he
      simp only [↓reduceIte] at hes
      subst hes
      obtain ⟨hinv', th', hrun, hQ, hσ', hstk, hp', hna⟩ := byteOut_emit_ld hW hnum
        (hbody.1 (t.2.wr 0) hlt _ hpj) hinv hwf hrb (hpi.dmemPriv 0 th ht1) hEnt hreach h0 rfl rfl hσ hfne hp
        (noExit_trace hW (hP.noExit hreach))
      have hwj' : (t.2.set 0 (.run (t.2.wr 0 + 1))).wr 0 = t.2.wr 0 + 1 := by rw [hk]; rfl
      refine ⟨_, hrun, .inl ⟨.inr ⟨u, th', j + 1, lbl, lsize, ts, hl, pm, none, withThread_one hth,
        ⟨E, by rw [hk]; rfl⟩, hz, hust ▸ hh, ?_, hcert u (by rw [withThread_one hth]; rfl), set_one hs0, hσ', hp', ?_,
        hhi, hust ▸ hw, ExtThread.bnd_readByte abi hb hrb, hinv', hown, hmi, hfi, hgi, ?_, ?_, ?_, hco, _,
        reach_run hreach hrun⟩, hpi'⟩⟩
      · refine .inr ⟨hust ▸ hsys, 1, buf, n, ?_, by omega⟩
        show Kernel.decode _ (abi.nr u.st) (abi.arg u.st) = _
        rw [hust]; exact hcall
      · show EmitJ Λ p I Top ((t.2.set 0 (.run (t.2.wr 0 + 1))).wr 0) lbl lsize u.st _ th'.stack
        rw [hwj', hust, hstk]
        exact ⟨rfl, (htop _ (by omega) _ hQ).2, hfne, hpl, hsys, c₀, fs₀, c₁, buf, n, Pw, hI, hr0, hdc, hbody, htop,
          by omega, hQ⟩
      · show ExtRows.OwnOk (own u.st th'.stack) t.1.mem u.prom
        rw [hust, hstk, Kernel.readByte_prom hrb]; exact hoo
      · rw [Spike.Lib.HeapPres.heapUse_set (s' := { s with ths := s.ths.set! 0 th', trace := s.trace ++ [.out b.val] })
          h0 rfl rfl hna]
        exact allocInvAt_prom (allocInvAt_hold hai rfl rfl) (Kernel.readByte_prom hrb)
      · rw [hna]; unfold TermRun.Cfg.n at hfr ⊢; rw [hs0] at hfr; simp only [set_one hs0]; exact hfr
    · -- a return: the row's return clause, its frame run
      obtain ⟨hok, hres, ht'⟩ := sysStep_write_retOk ht1 hcall (hwr' 1 buf n hcall) hsy
      obtain rfl : u = Kernel.retThread abi th r := Option.some.inj (hu.symm.trans ht')
      obtain ⟨c', fs', hlr, hI'⟩ := hbody.2 (t.2.wr 0) hjn _ hpj r hres hok
      rw [← Kernel.retThread_st (K := abi) th r] at hI'
      have hsys' : abi.atSys th.st = true := hsys
      have hbu : (Kernel.retThread abi th r).Bnd t'.1.mem.last := by
        rw [hmem]
        rcases ExtThread.bnd_sysStep abi ht1 hb hsy with he | ⟨u', he, hb'⟩
        · rw [he, hth] at hu
          obtain h' : th = Kernel.retThread abi th r := Option.some.inj hu
          rw [← h']; exact hb
        · rw [he] at hu
          obtain rfl : u' = Kernel.retThread abi th r := Option.some.inj ((show
            (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
              simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact hb'
      have hu1 : t'.1.threads = #[Kernel.retThread abi th r] ∧
          Inv1 Λ lbl lsize ts (Kernel.retThread abi th r) t'.1.mem s.mem := by
        rcases hi with he | ⟨u', he, hinv'⟩
        · rw [he] at hu ⊢; rw [hth] at hu
          obtain h' : th = Kernel.retThread abi th r := Option.some.inj hu
          rw [← h']; exact ⟨hth, hinv⟩
        · rw [he] at hu ⊢
          have h1 : (t.1.withThread 0 u' t.1.mem).threads = #[u'] := withThread_one hth
          obtain rfl : u' = Kernel.retThread abi th r := Option.some.inj ((show
            (t.1.withThread 0 u' t.1.mem).threads[0]? = some u' by
              simp only [Config.withThread, hth]; rfl).symm.trans hu)
          exact ⟨h1, hinv'⟩
      have hk' : t'.2 = KS E Λ 0 hl pm := by
        rcases ExtThread.sysStep_ret_kstate abi ht1 hsy (fun h => hx (Option.some.inj
          (hcall.symm.trans h))) (fun v h => hg v (Option.some.inj (hcall.symm.trans h))) with he | ⟨he, hw0⟩
        · rw [he, hk]; rfl
        · rw [he, hk]
          have := hw0 1 buf n hcall; rw [hwj] at this; subst this; rfl
      have hobs : obs es = [] := by
        rcases hev with rfl | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
      rw [hobs]
      have hsu' : (Kernel.retThread abi th r).st ∈ Kernel.certSuccs abi th.st (.write 1 buf n) := hsu
      obtain ⟨s', hrun, hpre'⟩ := pre_localJA (J := I) (own := own) hP hu1.1 hk' hz
        (hh.of_iff (hT.sys _ _ _ _ _ hI hsys' _ hcall _ hsu') (hT.owned _ _ _ _ _ hI')) (hcert _ hu) hs0 hσ hp hI'
        (ExtThread.sysStep_wideInv abi wideInv ht1 hw hsy hwr' hu) hbu hu1.2 (by rw [hmem]; exact hown)
        (by rw [hmem]; exact hmi) (by rw [hmem]; exact hfi) (by rw [hmem]; exact hgi)
        (by rw [hmem, hpu, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'),
              hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hsys' _ hcall _ hsu']
            exact hoo)
        (by rw [hmem]; exact allocInvAt_prom (allocInvAt_frameRun hai hlr) hpu) hfr hco ⟨tr, hreach⟩
        hhi (fun h0' => absurd h0' hfne) (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hlr
      exact ⟨s', hrun, .inl ⟨.inl ⟨hpre', fun _ _ _ _ _ => wr_one hk'⟩, hpi'⟩⟩
    · cases hex
    · cases hex

/-- **No byte of the output out after a step off the output `write`**: from
`PreSA` with thread 0 at no `write(1, …)` (`hne`), every step lands at a
pair with `Wr1Zero`: off a system call the count is 0 (`WrOk`) and the
kernel state's slots are kept (the take, an instruction, a promise); at one
the thread's state is kept (a byte of another `write`, a promise, an exit)
or the count reset (a return). -/
theorem wr1Zero_step {ab : Option (State → Prop)} (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat}
    {es : List Ev} (h : PreSA Λ P p G own I rS Tk μ ar t s)
    (hne : ∀ th buf n, t.1.threads = #[th] → abi.atSys th.st = true → Kernel.callOf abi th ≠ some (.write 1 buf n))
    (hs : T.M.Step μ tid t es t') : Wr1Zero t' := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, ⟨E, hk⟩, -, -, hwr, -, -, -, -, hI, -, hw, -, hinv, -⟩ := h
  obtain ⟨⟨t1, ht1⟩, -, -⟩ := hs.runs
  obtain ⟨rfl, rfl⟩ := get_one hth ht1
  have hj0 : abi.atSys th.st = false → t.2.wr 0 = 0 := fun hns => by
    rw [wr_one hk]
    rcases hwr with h | ⟨h, -⟩
    · exact h
    · rw [hns] at h; cases h
  have hone : ∀ {v u : Thread isaLSE2} {m : Memory}, (t.1.withThread 0 v m).threads = #[u] → v = u :=
    fun {v u m} hu => by
      have h1 := (withThread_one (u := v) (mem := m) hth).symm.trans hu
      exact (Array.mk.injEq _ _).mp h1 |> List.cons.inj |>.1
  intro u buf n hu hcu
  by_cases htk : ∃ a, μ.site .take = some a ∧ pcOf th.st = a
  · obtain ⟨a, ha, hpc⟩ := htk
    obtain ⟨-, -, hsys, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
    obtain ⟨-, rfl⟩ := step_takeA hN hT ht1 hI ha hpc hs
    exact hj0 hsys
  have hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a := fun a ha hpc => htk ⟨a, ha, hpc⟩
  have hsite := no_siteA hN ht1 hI hnt
  have hsp := no_spawnA (t' := t') hN hT ht1 hI
  rcases A64Ext.step_cases_site ht1 hw hinv hs hsp hsite with
    ⟨-, hns, -, -, -, -, rfl, -⟩ | ⟨-, w, rfl, -⟩ | ⟨pk, hsy, -, -⟩
  · exact hj0 hns
  · cases hone hu
    cases hsys : abi.atSys th.st
    · exact hj0 hsys
    · exact absurd hcu (hne th buf n hth hsys)
  · obtain ⟨hr, call, hcall, hcases⟩ := Kernel.sysStep_cases (K := abi) ht1 hsy (wr_le hk hwr)
    have hsys := atSys_of_ready hr
    rcases hcases with ⟨fd, buf', n', rd', b, u', -, rfl, -, -, hust, -, rfl⟩ |
      ⟨r, rfl, hx, hg, -, -, -, -, -, -⟩ | ⟨-, -, -, rfl⟩ | ⟨v, -, ⟨-, -, rfl⟩ | ⟨k, -, -, -, rfl⟩⟩
    · cases hone hu
      exact absurd (show Kernel.callOf abi th = _ by
        show Kernel.decode _ (abi.nr th.st) (abi.arg th.st) = _; rw [← hust]; exact hcu) (hne th buf n hth hsys)
    · rcases ExtThread.sysStep_ret_kstate abi ht1 hsy (fun h => hx (Option.some.inj
        (hcall.symm.trans h))) (fun v h => hg v (Option.some.inj (hcall.symm.trans h))) with he | ⟨he, hw0⟩
      · rw [he, hk]; rfl
      · rw [he]
        rcases hwr with rfl | ⟨-, fd, b, n', hc', -⟩
        · exact wr_one hk
        · exact hw0 fd b n' hc'
    all_goals
      rw [hth] at hu
      cases (Array.mk.injEq _ _).mp hu |> List.cons.inj |>.1
      exact absurd hcu (hne th buf n hth hsys)

/-- **Every step from `PreSA` with `Wr1Zero` is matched**: at a `write(1,
…)` the source first enters the output `write` (`pre_emitA`) and the step is
`EmitSA`'s (`emit_stepAE`); off it, `pre_stepAX`, landing with `Wr1Zero`
(`wr1Zero_step`). The private-memory invariant is kept (`privInv_step`). -/
theorem pre_stepAE {ab : Option (State → Prop)} (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hN : NodesA Λ p μ rd G own ar I ab) (hsafe : SrcSafeS P p I)
    (hE : EmitA Λ p I Top) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedA Λ P p G own I rS Tk μ ar) (hpsE : PromSharedAE Λ P p G own I Top rS Tk μ ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    (hok : ar.OK) (hEnt : Ent.clear Λ = true) {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev}
    (h : PreSA Λ P p G own I rS Tk μ ar t s) (hwz : Wr1Zero t) (hpi : PrivInv abi WideSt Λ Ent t)
    (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSAE Λ P p G own I Top rS Tk μ ar Ent t' s' := by
  by_cases hw1 : ∃ th buf n, t.1.threads = #[th] ∧ abi.atSys th.st = true ∧
      Kernel.callOf abi th = some (.write 1 buf n)
  · obtain ⟨th, buf, n, hth, hsys, hc⟩ := hw1
    obtain ⟨s₁, hr₁, he₁⟩ := pre_emitA hP hN hE h hwz hth hsys hc
    obtain ⟨s', hr', hR⟩ := emit_stepAE hP hW hnum hN hT hpsE hwf hEnt he₁ hpi hs
    exact ⟨s', Scc.Sem.LRun.trans hr₁ hr', hR⟩
  · have hne : ∀ th buf n, t.1.threads = #[th] → abi.atSys th.st = true →
        Kernel.callOf abi th ≠ some (.write 1 buf n) := fun th buf n hth hsys hc => hw1 ⟨th, buf, n, hth, hsys, hc⟩
    have hpi' : PrivInv abi WideSt Λ Ent t' := Spike.Lib.A64DmemPriv.privInv_step hpi hs
    obtain ⟨s', hr, hR⟩ := pre_stepAX hP hN hsafe hT hps hrd hwf hGpl hok h hne hs
    rcases hR with hpre | hpost
    · exact ⟨s', hr, .inl ⟨.inl ⟨hpre, wr1Zero_step hN hT h hne hs⟩, hpi'⟩⟩
    · exact ⟨s', hr, .inr hpost⟩

/-- **Every step from `RSAE` is matched**: from `PreSA` with `Wr1Zero` by
`pre_stepAE`, from `EmitSA` by `emit_stepAE`; after the exit no thread
steps. -/
theorem r_stepAE {ab : Option (State → Prop)} (hP : HookOK P p) (hW : SrcOutProto.UsesWc P p)
    (hnum : SrcNumSP P p PrintLd) (hN : NodesA Λ p μ rd G own ar I ab) (hsafe : SrcSafeS P p I)
    (hE : EmitA Λ p I Top) {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hps : PromSharedA Λ P p G own I rS Tk μ ar) (hpsE : PromSharedAE Λ P p G own I Top rS Tk μ ar)
    (hrd : SrcRd P p rd) (hwf : Λ.WF) (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v)
    (hok : ar.OK) (hEnt : Ent.clear Λ = true) {t t' : T.M.Cfg} {s : TermRun.Cfg} {tid : Nat} {es : List Ev}
    (h : RSAE Λ P p G own I Top rS Tk μ ar Ent t s) (hs : T.M.Step μ tid t es t') :
    ∃ s', (SrcSem.source P p).Run s (obs es) s' ∧ RSAE Λ P p G own I Top rS Tk μ ar Ent t' s' := by
  rcases h with ⟨⟨hpre, hwz⟩ | hem, hpi⟩ | ⟨_, _, _, _, _, _, _, _, o, _, ⟨_, hk⟩, _⟩
  · exact pre_stepAE hP hW hnum hN hsafe hE hT hps hpsE hrd hwf hGpl hok hEnt hpre hwz hpi hs
  · exact emit_stepAE hP hW hnum hN hT hpsE hwf hEnt hem hpi hs
  · exact (Kernel.exited_no_step abi (o := o) (by rw [hk]) hs).elim

end Spike.Lib.A64ConsumerA
