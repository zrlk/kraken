/-
**The x86-64 arena consumer's certification core with the `clone` path and
over a held predicate**: the x86-64 side of
`Spike/Lib/A64ConsumerASys.lean`'s `NodesA.sysRowXCT`, `NodesA.sysOkXCT`,
`no_spawnACT` and `Spike/Lib/A64ConsumerACore.lean`'s `core_sysAXC`,
`promSharedAXC`, `pre_coreAH`, `pre_core_promiseAH`, `core_sysAXT`,
`core_sysAXCT`, `core_sysAT`, `core_siteAT`, `promSharedAXH`,
`promSharedAXCH`, `promSharedAH`, which
`Spike/Lib/X64ConsumerACore.lean` and `Spike/Lib/X64ConsumerASysH.lean`
lack (consumer upgrade). Same names, same namespace
(`X64ConsumerA`); the proofs are AArch64's with `Arch.tso` and the x86-64
`nop` cell.

- `NodesA.sysRowXCT`, `NodesA.sysOkXCT`, `no_spawnACT`: the system-call row
  and support off `Cl`, and no spawn off `Cl`, over `TakeSiteS`.
- `core_sysAXC`: a certification step at a system call off the output
  `write` and off `Cl` keeps `PreCoreJA`.
- `promSharedAXC`: `PromSharedA` under `NodesA … Cl`, every `Cl` state at a
  `clone` (`certSem_step_clone_none`).
- `pre_coreAH`, `pre_core_promiseAH`, `core_sysAXT`, `core_sysAXCT`,
  `core_sysAT`, `core_siteAT`, `promSharedAXH`, `promSharedAXCH`,
  `promSharedAH`: the same over `HeldPathS` / `TakeSiteS`.
-/
import Spike.Lib.X64ConsumerACore
import Spike.Lib.X64ConsumerASysH
import Spike.Lib.X64ConsumerAClone

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS
open Spike.Lib.CtrRows (CtrW)

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)} {Cl : State → Prop}

/-- **The row at a system call other than the output `write`, off `Cl`**,
for rows under any `msOfAX … ab` (`NodesA.sysRow`; `Out.unBW`). Over `TakeSiteS`. -/
theorem NodesA.sysRowXCT (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)) (hcl : ¬ Cl s) :
    ∃ c₁ fs₁ call, FrameRun p (c, fs) (c₁, fs₁) ∧
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      SysOk p (msOfA Λ μ rd G own ar I lbl lsize fs₁) s c₁ call ∧
      ∀ s' ∈ Kernel.certSuccs abi s call, ∃ c' fs', FrameRun p (c₁, fs₁) (c', fs') ∧ I lbl lsize s' c' fs' := by
  obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  obtain ⟨c₁, fs₁, hr, -, h⟩ := hN.rowXC hI (hT.off_sys hI hs) (fun _ => hnw) fun _ => hcl
  obtain ⟨K, call, hK, -, hd, hok, hx⟩ := out_sys hc h (fun _ h => False.elim h)
  cases hK
  refine ⟨c₁, fs₁, call, hr, hd, hok, fun s' hs' => ?_⟩
  obtain ⟨c', hlr, h'⟩ := hx s' hs'
  obtain ⟨-, c'', fs'', hr', h''⟩ := h'
  exact ⟨c'', fs'', (FrameRun.ofLocal hlr fs₁).trans hr', h''⟩

/-- **A system call of the fragment off `Cl` is supported** for rows under
any `msOfAX … ab` (`NodesA.sysOk` without its "not to the output"): the
output `write` is neither `exit` nor `clone`. Over `TakeSiteS`. -/
theorem NodesA.sysOkXCT (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) (hcl' : ¬ Cl s) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      ∀ st tl, call ≠ .clone st tl := by
  by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 buf n)
  · obtain ⟨buf, n, hd⟩ := hw
    exact ⟨_, hd, nofun, nofun⟩
  · obtain ⟨c₁, fs₁, call, -, hd, ⟨hnx, hcl, -, -⟩, -⟩ :=
      hN.sysRowXCT hT hI hs (fun buf n h => hw ⟨buf, n, h⟩) hcl'
    exact ⟨call, hd, hnx, hcl⟩

/-- A pair of the fragment off `Cl` does not spawn (`no_spawnS` over
`NodesA`). Over `TakeSiteS`. -/
theorem no_spawnACT (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {t t' : T.M.Cfg} {th : Thread isa} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    {fs : List TermRun.Frame} (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) (hcl' : ¬ Cl th.st) :
    ¬ (X64.kernel 1).spawn μ 0 t t' := by
  rintro ⟨jj, r, h, -⟩
  unfold Kernel.spawnStep at h
  erw [ht] at h
  simp only at h
  cases hr : Kernel.ready abi 0 t th
  · simp [hr] at h
  · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXCT hT hI (atSys_of_ready hr) hcl'
    simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false] at h
    rw [show Kernel.callOf abi th = some call from hd] at h
    cases call with
    | clone st tl => exact hcl st tl rfl
    | _ => cases h


/-- **A certification step at a system call off the output `write` and off
`Cl` keeps `PreCoreJA`**, for rows under any `msOfAX … ab` and `NodesA … Cl`
(`core_sysAX` with `NodesA.sysRowXC`). -/
theorem core_sysAXC (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl) {rS : Range}
    {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hcl' : ¬ Cl th.st)
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowXC hT hI hs hnw hcl'
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **`PromSharedA` from the node obligations under `NodesA … ab Cl`**
(`promSharedAX`), every `Cl` state at a `clone` (`hClc`): there the
certification step has no outcome (`certSem_step_clone_none`); elsewhere
`core_sysAXC`. -/
theorem promSharedAXC (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.tso μ k 0).step Arch.tso th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedA Λ P p G own I rS Tk μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (X64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · by_cases hcl : Cl th.st
          · obtain ⟨st, tl, hd⟩ := hClc _ hcl
            exact absurd ho (certSem_step_clone_none hsi hs hd hso)
          · exact (core_sysAXC hP hN hT h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hcl hso ho).imp
              fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteA hP hN hT h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseA hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PreJA` gives `PreCoreJA`** of its one thread and the memory. Over `HeldPathS`. -/
theorem pre_coreAH {J : InvS} {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    {th : Thread isa} (h : PreJAH Λ P p G own J H μ ar t s) (hth : t.1.threads = #[th]) :
    PreCoreJA Λ P p G own J ar th t.1.mem s := by
  obtain ⟨th', th0, -, lbl, lsize, ts, -, -, hd, hth', -, -, -, -, -, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown,
    hmi, hfi, hgi, hoo, hai, hfr, hco, hre⟩ := h
  obtain rfl : th = th' := (get_one hth (show t.1.threads[0]? = some th' by rw [hth']; rfl)).2
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, MsgsExcept.of_all hmi.1 _, hmi.2,
    hfi, MemInv.msgsExcept hgi _, hgi.1, hoo, hai, hfr, hco, hre⟩

/-- **`PreSA` followed by a certified promise gives `PreCoreJA`** of the
promising thread and the memory with the promise (`pre_core_promiseS` with
the arena, `AllocInvAt.promise`). Over `HeldPathS`. -/
theorem pre_core_promiseAH {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg} {th : Thread isa}
    {w : Msg} (h : PreSAH Λ P p G own I H μ ar t s) (hth : t.1.threads = #[th]) (hwt : w.tid = 0)
    (hc : CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1) :
    PreCoreJA Λ P p G own I ar (Live.Sem.promThread th t.1.mem w) (t.1.mem.append w).1 s := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := pre_coreAH h hth
  have hlast : t.1.mem.last ≤ (t.1.mem.append w).1.last := by rw [Memory.last_append]; exact Nat.le_succ _
  exact ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, ⟨hb.views.mono hlast, hb.regs.mono hlast⟩,
    hinv.promise_cert_on (soloWide8CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc, ownMsgs_append hwt hown,
    msgsExcept_promise hsh w, hini,
    ⟨fits_promise_cert_on (soloFit64CodeOn μ t.2 0) (soloWideInv μ t.2 0) hw hc hfi.1, initFits_append hfi.2 w⟩,
    msgsExcept_promise hgm w,
    hgi, ownOk_promise hinv.coh hinv.mem.tq_nodup (fun p hp => (hinv.mem.tq_le p hp).2) hoo w, hai.promise w rfl,
    hfr, hco, hre⟩

/-- **A certification step at a system call other than the output `write`
keeps `PreCoreJA`**, for rows under any `msOfAX … ab` (`core_sysA`;
`NodesA.sysRowX`): the row's frame run, then the local run to the
successor, the promises and the memory kept. Over `TakeSiteS`. -/
theorem core_sysAXT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hT : TakeSiteS p μ I) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowXT hT hI hs hnw
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **A certification step at a system call off the output `write` and off
`Cl` keeps `PreCoreJA`**, for rows under any `msOfAX … ab` and `NodesA … Cl`
(`core_sysAX` with `NodesA.sysRowXC`). Over `TakeSiteS`. -/
theorem core_sysAXCT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) ≠ some (.write 1 buf n))
    (hcl' : ¬ Cl th.st)
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowXCT hT hI hs hnw hcl'
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **A certification step at a system call keeps `PreCoreJA`**
(`core_sysS` with the arena): the row's frame run, then the local run to the
successor, the promises and the memory kept. Over `TakeSiteS`. -/
theorem core_sysAT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I)
    (hT : TakeSiteS p μ I) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st = none)
    (hs : abi.atSys th.st = true)
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  obtain ⟨c₁, fs₁, call, hr0, hdc, ⟨-, hcl, -, -⟩, hx⟩ := hN.sysRowT hT hI hs
  obtain ⟨hm, hpr, hsu, hinv'⟩ := hinv.certSysSolo hsi hs hdc hcl hso ho
  obtain ⟨c', fs', hlr, hI'⟩ := hx _ hsu
  have hr1 := hr0.trans hlr
  have hw' : WideSt o.thread.st := wideSt_soloLeaf hw (Kernel.certSuccs_soloLeaf hsu)
  exact core_localA (J := I) (u := o.thread) (mem := o.mem) hP hs0 hσ hp hI' hw' (stepOneWith_bnd _ hso ho hb).1
    hinv' (by rw [hm]; exact hown) (by rw [hm, hpr]; exact hsh) (by rw [hm]; exact hini) (by rw [hm]; exact hfi)
    (by rw [hm, hpr]; exact hgm) (by rw [hm]; exact hgi)
    (by rw [hm, hpr, hN.ownRun _ _ _ _ _ _ _ hlr (.inr hI'), hN.ownSys _ _ _ _ _ (IRun.trans hI hr0) hs _ hdc _ hsu,
          hN.ownRun _ _ _ _ _ _ _ hr0 (.inl hI)]
        exact hoo)
    (by rw [hm]; exact allocInvAt_prom (allocInvAt_frameRun hai hr1) hpr) hfr hco hre hhi hcr
    (fun h0' => by rw [h0'] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **The certification step at a transfer site keeps `PreCoreJA`**
(`core_siteS` with the arena; the take's local run keeps the promises and
the memory). Over `TakeSiteS`. -/
theorem core_siteAT (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hT : TakeSiteS p μ I) {th : Thread isa} {mem : Memory} {s : TermRun.Cfg}
    {outs : List (Except String (Outcome isa))} {o : Outcome isa} {x : Kernel.KState}
    (h : PreCoreJA Λ P p G own I ar th mem s) (hsi : Kernel.siteAt abi μ th.st ≠ none)
    (hso : (Kernel.certSem abi Arch.tso μ x 0).step Arch.tso th 0 mem = some outs) (ho : .ok o ∈ outs) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreCoreJA Λ P p G own I ar o.thread o.mem s' := by
  obtain ⟨th0, lbl, lsize, ts, hd, hs0, hσ, hp, hI, hhi, hw, hb, hinv, hown, hsh, hini, hfi, hgm, hgi, hoo,
    hai, hfr, hco, hre⟩ := h
  have hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a := fun h0' => by
    rw [h0'] at hI; exact hN.noRet _ _ _ _ hI
  have ha : μ.site .take = some (pcOf th.st) := Classical.byContradiction fun hne =>
    hsi (Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hne h, fun h => hN.noSite _ _ _ _ _ hI _ h rfl⟩)
  have hsa : Kernel.siteAt abi μ th.st = some .take := by
    unfold Kernel.siteAt; exact ite_eq_left ha
  obtain ⟨⟨_, sz, hcn⟩, hsys, hrun⟩ := hT.site _ _ _ _ _ hI _ ha rfl
  obtain ⟨hot, hom⟩ := Kernel.certSem_step_take_out hsa hsys (X64.deps_of_atNop (atNop_of_cellAt hcn)) hso ho
  rw [hot, hom]
  obtain ⟨c', fs', hr1, hI'⟩ := hrun x.pmem
  exact core_localA (J := I) hP hs0 hσ hp hI' hw ⟨hb.1, hb.2⟩ ⟨hinv.1, hinv.2, hinv.3⟩ hown hsh hini hfi hgm hgi
    (by show ExtRows.OwnOk (own (abi.skip _) fs') _ _
        rw [hN.ownRun _ _ _ _ _ _ _ hr1 (.inr hI'), hN.ownTake _ _ _ _ _ hI _ ha rfl]; exact hoo)
    (allocInvAt_prom (allocInvAt_frameRun hai hr1) rfl) hfr hco hre hhi hcr
    (fun h0' => by
      have h0'' : fs' = [] := h0'
      rw [h0''] at hI'; exact hN.noRet _ _ _ _ hI') hr1

/-- **`PromSharedA` from the node obligations**, for rows under any
`msOfAX … ab` (`promSharedS` with the arena), the certification steps at the
output `write` keeping the core by `hwr`: `PreCoreJA` is the certification
run's invariant (`X64PromShared.stepG_of`), and a certified promise from `PreSA` lands in it
(`pre_core_promiseA`). Over `HeldPathS`. -/
theorem promSharedAXH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.tso μ k 0).step Arch.tso th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedAH Λ P p G own I H μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (X64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · exact (core_sysAXT hP hN hT.toTakeSiteS h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hso ho).imp fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteAT hP hN hT.toTakeSiteS h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseAH hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PromSharedA` from the node obligations under `NodesA … ab Cl`**
(`promSharedAX`), every `Cl` state at a `clone` (`hClc`): there the
certification step has no outcome (`certSem_step_clone_none`); elsewhere
`core_sysAXC`. Over `HeldPathS`. -/
theorem promSharedAXCH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H)
    (hClc : ∀ s, Cl s → ∃ st tl, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.clone st tl))
    (hwr : ∀ k th mem s outs o, PreCoreJA Λ P p G own I ar th mem s → Kernel.siteAt abi μ th.st = none →
      abi.atSys th.st = true →
      (∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)) →
      (Kernel.certSem abi Arch.tso μ k 0).step Arch.tso th 0 mem = some outs → .ok o ∈ outs →
        ∃ s', PreCoreJA Λ P p G own I ar o.thread o.mem s') :
    PromSharedAH Λ P p G own I H μ ar := by
  intro t s th w hpre hth hw hc
  exact certOkC_prom_good_cfg
    (X64PromShared.stepG_of (Core := PreCoreJA Λ P p G own I ar) (fun _ _ _ h => h.msgs)
      (core_insA hP hN hsafe hrd hwf hGpl hok)
      (fun k th _ _ _ _ h hsi hs hso ho => by
        by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr th.st) (abi.arg th.st) = some (.write 1 buf n)
        · exact hwr k th _ _ _ _ h hsi hs hw hso ho
        · by_cases hcl : Cl th.st
          · obtain ⟨st, tl, hd⟩ := hClc _ hcl
            exact absurd ho (certSem_step_clone_none hsi hs hd hso)
          · exact (core_sysAXCT hP hN hT.toTakeSiteS h hsi hs (fun buf n hd => hw ⟨buf, n, hd⟩) hcl hso ho).imp
              fun _ h => h.2)
      (fun _ _ _ _ _ _ h hsi hso ho => (core_siteAT hP hN hT.toTakeSiteS h hsi hso ho).imp fun _ h => h.2) t.2)
    ⟨s, pre_core_promiseAH hpre hth hw hc⟩ hc
    (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (Memory.get?_append_new (m := t.1.mem))

/-- **`PromSharedA` from the node obligations** (`promSharedS` with the
arena): `promSharedAX` at `ab = none`, every system call's row by
`core_sysA`. Over `HeldPathS`. -/
theorem promSharedAH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I)
    (hsafe : SrcSafeS P p I) (hrd : SrcRd P p rd) (hwf : Λ.WF)
    (hGpl : ∀ a v, Λ.heap.contains a ∨ Λ.data.contains a → G (wordLoc a) v) (hok : ar.OK)
    {H : State → List (Nat × Range) → Prop} (hT : HeldPathS Λ p μ I H) :
    PromSharedAH Λ P p G own I H μ ar :=
  promSharedAXH hP hN hsafe hrd hwf hGpl hok hT fun _ _ _ _ _ _ h hsi hs _ hso ho =>
    (core_sysAT hP hN hT.toTakeSiteS h hsi hs hso ho).imp fun _ h => h.2



end Spike.Lib.X64ConsumerA

/-- info: 'Spike.Lib.X64ConsumerA.NodesA.sysRowXCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.NodesA.sysRowXCT

/-- info: 'Spike.Lib.X64ConsumerA.NodesA.sysOkXCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.NodesA.sysOkXCT

/-- info: 'Spike.Lib.X64ConsumerA.no_spawnACT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.no_spawnACT

/-- info: 'Spike.Lib.X64ConsumerA.core_sysAXC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.core_sysAXC

/-- info: 'Spike.Lib.X64ConsumerA.promSharedAXC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.promSharedAXC

/-- info: 'Spike.Lib.X64ConsumerA.pre_coreAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_coreAH

/-- info: 'Spike.Lib.X64ConsumerA.pre_core_promiseAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_core_promiseAH

/-- info: 'Spike.Lib.X64ConsumerA.core_sysAXT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.core_sysAXT

/-- info: 'Spike.Lib.X64ConsumerA.core_sysAXCT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.core_sysAXCT

/-- info: 'Spike.Lib.X64ConsumerA.core_sysAT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.core_sysAT

/-- info: 'Spike.Lib.X64ConsumerA.core_siteAT' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.core_siteAT

/-- info: 'Spike.Lib.X64ConsumerA.promSharedAXH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.promSharedAXH

/-- info: 'Spike.Lib.X64ConsumerA.promSharedAXCH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.promSharedAXCH

/-- info: 'Spike.Lib.X64ConsumerA.promSharedAH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.promSharedAH
