/-
**The allocation-capable consumer's node facts off the rows**
(`Spike/Lib/A64ConsumerA.lean`): `A64ConsumerS`'s system-call, transfer-site
and spawn facts restated over `NodesA` (they use only its `out`, `svc`,
`noSite` fields, which `NodesS` has alike), and `PromSharedS` over `PreSA`.

- `NodesA.sysRow`, `NodesA.sysOk`: the row at a system call (`NodesS.sysRow`,
  `NodesS.sysOk`); `NodesA.sysRowX`, `NodesA.sysOkX`: for rows under any
  `msOfAX … ab`, off the output `write` (`Out.unBW`).
- `no_siteA`, `siteAt_noneA`, `step_takeA`, `no_spawnA`: `no_siteS`,
  `siteAt_noneS`, `step_takeS`, `no_spawnS`.
- `PromSharedA`: promises are to shared regions, over `PreSA`.
-/
import Spike.Lib.A64ConsumerA

namespace Spike.Lib.A64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64 Scc.Cert.WideA64
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)}

/-- **The row at a system call** (`NodesS.sysRow` over `NodesA`). -/
theorem NodesA.sysRow (hN : NodesA Λ p μ rd G own ar I) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∃ c₁ fs₁ call, FrameRun p (c, fs) (c₁, fs₁) ∧
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      SysOk p (msOfA Λ μ rd G own ar I lbl lsize fs₁) s c₁ call ∧
      ∀ s' ∈ Kernel.certSuccs abi s call, ∃ c' fs', FrameRun p (c₁, fs₁) (c', fs') ∧ I lbl lsize s' c' fs' := by
  obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  cases hN.out _ _ _ _ _ hI (hT.off_sys hI hs) with
  | pre c₁ fs₁ hr h =>
    obtain ⟨K, call, hK, -, hd, hok, hx⟩ := out_sys hc h (fun _ h => False.elim h)
    cases hK
    refine ⟨c₁, fs₁, call, hr, hd, hok, fun s' hs' => ?_⟩
    obtain ⟨c', hlr, c'', fs'', hr', h'⟩ := hx s' hs'
    exact ⟨c'', fs'', (FrameRun.ofLocal hlr fs₁).trans hr', h'⟩
  | frame s' c' fs' he _ _ =>
    rw [Kraken.Promising.Lower.A64.exec_svc hc] at he; cases he

/-- **A system call of the fragment is supported** (`NodesS.sysOk` over
`NodesA`). -/
theorem NodesA.sysOk (hN : NodesA Λ p μ rd G own ar I) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      (∀ st tl, call ≠ .clone st tl) ∧ ∀ fd buf n, call = .write fd buf n → fd ≠ 1 := by
  obtain ⟨c₁, fs₁, call, -, hd, ⟨hnx, hcl, hfd, -⟩, -⟩ := hN.sysRow hT hI hs
  exact ⟨call, hd, hnx, hcl, hfd⟩

/-- **The row at a system call other than the output `write`**, for rows
under any `msOfAX … ab` (`NodesA.sysRow`; `Out.unBW`). -/
theorem NodesA.sysRowX (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)) :
    ∃ c₁ fs₁ call, FrameRun p (c, fs) (c₁, fs₁) ∧
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      SysOk p (msOfA Λ μ rd G own ar I lbl lsize fs₁) s c₁ call ∧
      ∀ s' ∈ Kernel.certSuccs abi s call, ∃ c' fs', FrameRun p (c₁, fs₁) (c', fs') ∧ I lbl lsize s' c' fs' := by
  obtain ⟨imm, sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  obtain ⟨c₁, fs₁, hr, -, h⟩ := hN.rowX hI (hT.off_sys hI hs) fun _ => hnw
  obtain ⟨K, call, hK, -, hd, hok, hx⟩ := out_sys hc h (fun _ h => False.elim h)
  cases hK
  refine ⟨c₁, fs₁, call, hr, hd, hok, fun s' hs' => ?_⟩
  obtain ⟨c', hlr, h'⟩ := hx s' hs'
  obtain ⟨-, c'', fs'', hr', h''⟩ := h'
  exact ⟨c'', fs'', (FrameRun.ofLocal hlr fs₁).trans hr', h''⟩

/-- **A system call of the fragment is supported** for rows under any
`msOfAX … ab` (`NodesA.sysOk` without its "not to the output"): the output
`write` is neither `exit` nor `clone`. -/
theorem NodesA.sysOkX (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      ∀ st tl, call ≠ .clone st tl := by
  by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 buf n)
  · obtain ⟨buf, n, hd⟩ := hw
    exact ⟨_, hd, nofun, nofun⟩
  · obtain ⟨c₁, fs₁, call, -, hd, ⟨hnx, hcl, -, -⟩, -⟩ :=
      hN.sysRowX hT hI hs fun buf n h => hw ⟨buf, n, h⟩
    exact ⟨call, hd, hnx, hcl⟩

/-- A pair of the fragment off the take site is at no transfer site
(`no_siteS` over `NodesA`). -/
theorem no_siteA (hN : NodesA Λ p μ rd G own ar I ab) {t : T.M.Cfg} {th : Thread isaLSE2} {lbl : Lbl}
    {lsize : Lsize} {c : Ctl} {fs : List TermRun.Frame} (ht : t.1.threads[0]? = some th)
    (hI : I lbl lsize th.st c fs) (hnt : ∀ a, μ.site .take = some a → pcOf th.st ≠ a) :
    ∀ k, ¬ T.M.AtSite μ k t 0 := by
  rintro k ⟨a, ha, t2, ht2, hpc⟩
  cases (show some t2 = some th from ht2.symm.trans ht)
  cases k
  · exact hnt a ha hpc
  · exact hN.noSite _ _ _ _ _ hI a ha hpc

/-- A pair of the fragment off the take site is off the certification
semantics' transfer sites (`siteAt_noneS` over `NodesA`). -/
theorem siteAt_noneA (hN : NodesA Λ p μ rd G own ar I ab) {s : State} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    {fs : List TermRun.Frame} (hI : I lbl lsize s c fs) (hnt : ∀ a, μ.site .take = some a → pcOf s ≠ a) :
    Kernel.siteAt abi μ s = none :=
  Kernel.siteAt_eq_none_iff.mpr ⟨fun h => hnt _ h rfl, fun h => hN.noSite _ _ _ _ _ hI _ h rfl⟩

/-- **The step at the take site is the take** (`step_takeS` over
`NodesA`). -/
theorem step_takeA (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg} {th : Thread isaLSE2} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    {fs : List TermRun.Frame} {es : List Ev} {a : Nat}
    (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) (ha : μ.site .take = some a)
    (hpc : pcOf th.st = a) (hs : T.M.Step μ 0 t es t') :
    es = [] ∧ t' = (t.1.withThread 0
        { th with st := abi.skip (abi.setDmem th.st (Kernel.copyRange t.2.pmem (abi.dmem th.st) rS)) } t.1.mem,
      { t.2 with held := (0, rS) :: t.2.held, pmem := Kernel.eraseRange t.2.pmem rS }) := by
  obtain ⟨-, -, hsys, hsr, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
  have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht, hpc⟩
  have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
    cases (show some t2 = some th from ht2.symm.trans ht)
    exact hN.noSite _ _ _ _ _ hI a' ha' hpc'
  obtain ⟨hes, hx⟩ := Kernel.step_at_take ht hsys hat hnr hs
  refine ⟨hes, ?_⟩
  subst hsr
  unfold Kernel.takeStep at hx
  erw [ht] at hx
  simp only at hx
  split at hx
  · exact (Option.some.inj hx).symm
  · cases hx

/-- A pair of the fragment does not spawn (`no_spawnS` over `NodesA`). -/
theorem no_spawnA (hN : NodesA Λ p μ rd G own ar I ab) {rS : Range} {Tk : State → Prop}
    (hT : TakePathS Λ p μ I rS Tk) {t t' : T.M.Cfg} {th : Thread isaLSE2} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    {fs : List TermRun.Frame} (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) :
    ¬ (A64.kernel 1).spawn μ 0 t t' := by
  rintro ⟨jj, r, h, -⟩
  unfold Kernel.spawnStep at h
  erw [ht] at h
  simp only at h
  cases hr : Kernel.ready abi 0 t th
  · simp [hr] at h
  · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkX hT hI (atSys_of_ready hr)
    simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false] at h
    rw [show Kernel.callOf abi th = some call from hd] at h
    cases call with
    | clone st tl => exact hcl st tl rfl
    | _ => cases h

/-- **Promises are to shared regions** with the arena (`PromSharedS` over
`PreSA`). -/
def PromSharedA (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (rS : Range) (Tk : State → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th w, PreSA Λ P p G own I rS Tk μ ar t s → t.1.threads = #[th] → w.tid = 0 →
    CertOkC Arch.armv8 (Kernel.certSem abi Arch.armv8 μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1 →
    LocIn Λ.shared w.loc ∧ G w.loc w.val

end Spike.Lib.A64ConsumerA
