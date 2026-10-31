/-
**The x86-64 arena consumer's node facts over `TakeSiteS`**: the x86-64
side of `Spike/Lib/A64ConsumerASys.lean`'s `…T` lemmas and `PromSharedAH`,
which `Spike/Lib/X64ConsumerASys.lean` lacks
(consumer upgrade). Same names, same namespace
(`X64ConsumerA`). The `Cl` versions (`NodesA.sysRowXCT`, `NodesA.sysOkXCT`,
`no_spawnACT`) wait for `NodesA`'s `Cl` parameter.

- `NodesA.sysRowT`, `NodesA.sysOkT`, `NodesA.sysRowXT`, `NodesA.sysOkXT`,
  `no_spawnAT`, `step_takeAT`: `NodesA.sysRow` … `step_takeA` over
  `TakeSiteS` (the take site's range `Kernel.siteRange` in place of `rS`).
- `PromSharedAH`: `PromSharedA` over `PreSAH`.
-/
import Spike.Lib.X64ConsumerASys
import Spike.Lib.X64ConsumerAH

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {Λ : Scc.Sem.Layout} {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop}
  {G : Loc → Val → Prop} {own : OwnS} {ar : Arena} {ab : Option (State → Prop)} {Cl : State → Prop}

/-- **The row at a system call** (`NodesS.sysRow` over `NodesA`). Over `TakeSiteS`. -/
theorem NodesA.sysRowT (hN : NodesA Λ p μ rd G own ar I)
    (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∃ c₁ fs₁ call, FrameRun p (c, fs) (c₁, fs₁) ∧
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      SysOk p (msOfA Λ μ rd G own ar I lbl lsize fs₁) s c₁ call ∧
      ∀ s' ∈ Kernel.certSuccs abi s call, ∃ c' fs', FrameRun p (c₁, fs₁) (c', fs') ∧ I lbl lsize s' c' fs' := by
  obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  cases hN.out _ _ _ _ _ hI (hT.off_sys hI hs) (fun _ h => h) with
  | pre c₁ fs₁ hr h =>
    obtain ⟨K, call, hK, -, hd, hok, hx⟩ := out_sys hc h (fun _ h => False.elim h)
    cases hK
    refine ⟨c₁, fs₁, call, hr, hd, hok, fun s' hs' => ?_⟩
    obtain ⟨c', hlr, c'', fs'', hr', h'⟩ := hx s' hs'
    exact ⟨c'', fs'', (FrameRun.ofLocal hlr fs₁).trans hr', h'⟩
  | frame s' c' fs' he _ _ =>
    rw [Kraken.Promising.Lower.X64.exec_syscall hc] at he; cases he

/-- **A system call of the fragment is supported** (`NodesS.sysOk` over
`NodesA`). Over `TakeSiteS`. -/
theorem NodesA.sysOkT (hN : NodesA Λ p μ rd G own ar I)
    (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      (∀ st tl, call ≠ .clone st tl) ∧ ∀ fd buf n, call = .write fd buf n → fd ≠ 1 := by
  obtain ⟨c₁, fs₁, call, -, hd, ⟨hnx, hcl, hfd, -⟩, -⟩ := hN.sysRowT hT hI hs
  exact ⟨call, hd, hnx, hcl, hfd⟩

/-- **The row at a system call other than the output `write`**, for rows
under any `msOfAX … ab` (`NodesA.sysRowX`). Over `TakeSiteS`. -/
theorem NodesA.sysRowXT (hN : NodesA Λ p μ rd G own ar I ab)
    (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true)
    (hnw : ∀ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) ≠ some (.write 1 buf n)) :
    ∃ c₁ fs₁ call, FrameRun p (c, fs) (c₁, fs₁) ∧
      Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧
      SysOk p (msOfA Λ μ rd G own ar I lbl lsize fs₁) s c₁ call ∧
      ∀ s' ∈ Kernel.certSuccs abi s call, ∃ c' fs', FrameRun p (c₁, fs₁) (c', fs') ∧ I lbl lsize s' c' fs' := by
  obtain ⟨sz, hc⟩ := hN.svc _ _ _ _ _ hI hs
  obtain ⟨c₁, fs₁, hr, -, h⟩ := hN.rowX hI (hT.off_sys hI hs) fun _ => hnw
  obtain ⟨K, call, hK, -, hd, hok, hx⟩ := out_sys hc h (fun _ h => False.elim h)
  cases hK
  refine ⟨c₁, fs₁, call, hr, hd, hok, fun s' hs' => ?_⟩
  obtain ⟨c', hlr, h'⟩ := hx s' hs'
  obtain ⟨-, c'', fs'', hr', h''⟩ := h'
  exact ⟨c'', fs'', (FrameRun.ofLocal hlr fs₁).trans hr', h''⟩

/-- **A system call of the fragment is supported** for rows under any
`msOfAX … ab` (`NodesA.sysOkX`). Over `TakeSiteS`. -/
theorem NodesA.sysOkXT (hN : NodesA Λ p μ rd G own ar I ab)
    (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl} {fs : List TermRun.Frame}
    (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∃ call, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call ∧ call ≠ .exit ∧
      ∀ st tl, call ≠ .clone st tl := by
  by_cases hw : ∃ buf n, Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some (.write 1 buf n)
  · obtain ⟨buf, n, hd⟩ := hw
    exact ⟨_, hd, nofun, nofun⟩
  · obtain ⟨c₁, fs₁, call, -, hd, ⟨hnx, hcl, -, -⟩, -⟩ :=
      hN.sysRowXT hT hI hs fun buf n h => hw ⟨buf, n, h⟩
    exact ⟨call, hd, hnx, hcl⟩

/-- A pair of the fragment does not spawn (`no_spawnA`). Over `TakeSiteS`. -/
theorem no_spawnAT (hN : NodesA Λ p μ rd G own ar I ab)
    (hT : TakeSiteS p μ I) {t t' : T.M.Cfg} {th : Thread isa} {lbl : Lbl} {lsize : Lsize} {c : Ctl}
    {fs : List TermRun.Frame} (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) :
    ¬ (X64.kernel 1).spawn μ 0 t t' := by
  rintro ⟨jj, r, h, -⟩
  unfold Kernel.spawnStep at h
  erw [ht] at h
  simp only at h
  cases hr : Kernel.ready abi 0 t th
  · simp [hr] at h
  · obtain ⟨call, hd, -, hcl⟩ := hN.sysOkXT hT hI (atSys_of_ready hr)
    simp only [hr, Bool.not_true, Bool.false_eq_true, ite_false] at h
    rw [show Kernel.callOf abi th = some call from hd] at h
    cases call with
    | clone st tl => exact hcl st tl rfl
    | _ => cases h

/-- **The step at the take site is the take**, the range the site's
(`step_takeA` over `TakeSiteS`: `Kernel.siteRange` in place of `rS`). -/
theorem step_takeAT (hN : NodesA Λ p μ rd G own ar I ab Cl) (hT : TakeSiteS p μ I) {t t' : T.M.Cfg}
    {th : Thread isa} {lbl : Lbl} {lsize : Lsize} {c : Ctl} {fs : List TermRun.Frame} {es : List Ev} {a : Nat}
    (ht : t.1.threads[0]? = some th) (hI : I lbl lsize th.st c fs) (ha : μ.site .take = some a)
    (hpc : pcOf th.st = a) (hs : T.M.Step μ 0 t es t') :
    es = [] ∧ t' = (t.1.withThread 0
        { th with st := abi.skip (abi.setDmem th.st
          (Kernel.copyRange t.2.pmem (abi.dmem th.st) (Kernel.siteRange abi th.st))) } t.1.mem,
      { t.2 with
        held := (0, Kernel.siteRange abi th.st) :: t.2.held,
        pmem := Kernel.eraseRange t.2.pmem (Kernel.siteRange abi th.st) }) := by
  obtain ⟨-, hsys, -⟩ := hT.site _ _ _ _ _ hI a ha hpc
  have hat : T.M.AtSite μ .take t 0 := ⟨a, ha, th, ht, hpc⟩
  have hnr : ¬ T.M.AtSite μ .release t 0 := fun ⟨a', ha', t2, ht2, hpc'⟩ => by
    cases (show some t2 = some th from ht2.symm.trans ht)
    exact hN.noSite _ _ _ _ _ hI a' ha' hpc'
  obtain ⟨hes, hx⟩ := Kernel.step_at_take ht hsys hat hnr hs
  refine ⟨hes, ?_⟩
  unfold Kernel.takeStep at hx
  erw [ht] at hx
  simp only at hx
  split at hx
  · exact (Option.some.inj hx).symm
  · cases hx

/-- **Promises are to shared regions**, the ranges held by `H`
(`PromSharedA` over `PreSAH`). -/
def PromSharedAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS)
    (I : InvS) (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) : Prop :=
  ∀ t s th w, PreSAH Λ P p G own I H μ ar t s → t.1.threads = #[th] → w.tid = 0 →
    CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 (Live.Sem.promThread th t.1.mem w)
      (t.1.mem.append w).1 →
    LocIn Λ.shared w.loc ∧ G w.loc w.val

/-- `PromSharedA` is `PromSharedAH` at `HeldOk`. -/
theorem PromSharedA_eq {rS : Range} {Tk : State → Prop} :
    PromSharedA Λ P p G own I rS Tk μ ar = PromSharedAH Λ P p G own I (HeldOk Λ rS Tk) μ ar := rfl

end Spike.Lib.X64ConsumerA

/-! ## Axiom guards -/

/--
info: 'Spike.Lib.X64ConsumerA.NodesA.sysRowT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.NodesA.sysRowT

/--
info: 'Spike.Lib.X64ConsumerA.NodesA.sysOkT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.NodesA.sysOkT

/--
info: 'Spike.Lib.X64ConsumerA.NodesA.sysRowXT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.NodesA.sysRowXT

/--
info: 'Spike.Lib.X64ConsumerA.NodesA.sysOkXT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.NodesA.sysOkXT

/--
info: 'Spike.Lib.X64ConsumerA.no_spawnAT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.no_spawnAT

/--
info: 'Spike.Lib.X64ConsumerA.step_takeAT' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.step_takeAT

/--
info: 'Spike.Lib.X64ConsumerA.PromSharedA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.PromSharedA_eq
