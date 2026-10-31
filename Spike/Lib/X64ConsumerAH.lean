/-
**The held-range (`H`) relation of the x86-64 arena consumer**: the x86-64
side of `Spike/Lib/A64ConsumerS.lean`'s `TakeSiteS`/`HeldPathS` and
`Spike/Lib/A64ConsumerA.lean`'s `PreJAH`/`RSAH`,
which `Spike/Lib/X64ConsumerS.lean` and `Spike/Lib/X64ConsumerA.lean` lack
(consumer upgrade). Same names, same namespaces as AArch64's
(`X64ConsumerS`, `X64ConsumerA`), so a later move into those files is a cut
and paste. The take site is at a `nop` cell of any length (as
`TakePathS.site`'s).

- `TakeSiteS`, `HeldPathS`: the take path over a held predicate `H`;
  `TakeSiteS.off_sys`, `HeldOk.held_own`, `TakePathS.toH`.
- `PreJAH`, `PreSAH`, `RSAH`: `PreJA`, `PreSA`, `RSA` over `H`
  (`PreJA_eq`, `RSA_eq`, `PostSA_eq`: the old ones at `HeldOk`, by `rfl`).
- `pend_runAH`, `pre_localJAH`, `pend_landAH`: as `pend_runA`,
  `pre_localJA`, `pend_landA`.
-/
import Spike.Lib.X64ConsumerA
import Spike.Lib.X64PlacedSEH

namespace Spike.Lib.X64ConsumerS

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer

/-- **The take site at any depth**, the range the site's registers name
(`Kernel.siteRange`): a pair at the resolved take site is at a `nop` cell
off a system call, and for every pool image `pm` a frame run reaches the
fragment at the state with the range's bytes copied in, past the `nop`.
`TakePathS` without the phase and the fixed range; the part of
`HeldPathS` the system-call and take-step facts use (`TakeSiteS.off_sys`). -/
structure TakeSiteS (p : Prog) (μ : Marks) (I : InvS) : Prop where
  site : ∀ lbl lsize s c fs, I lbl lsize s c fs → ∀ a, μ.site .take = some a → pcOf s = a →
    (∃ n sz, Kraken.Promising.Lower.X64.CellAt s (Kraken.Promising.Lower.X64.op64 (.nop n)) sz) ∧
      abi.atSys s = false ∧
      ∀ pm, ∃ c' fs', FrameRun p (c, fs) (c', fs') ∧
        I lbl lsize (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) (Kernel.siteRange abi s)))) c' fs'

/-- **The take path over a held predicate `H`** (`TakePathS` with the
ranges held a predicate of the thread state and the held list, in place of
`HeldOk`'s one range `rS` and phase `Tk`; `TakePathS.toH`): `TakeSiteS`,
and `own`, every range `H` holds is thread 0's and owned; `held`, at the
take site the named range is in the pool, nonempty, off every held range,
the `.rodata` image off the pool, and after the take `H` holds with the
range pushed (given the fragment there); `instr`, `sys`, an instruction
off the transfer sites (from a wide state) and a system call keep `H` at
every successor in the fragment. -/
structure HeldPathS (Λ : Scc.Sem.Layout) (p : Prog) (μ : Marks) (I : InvS) (H : State → List (Nat × Range) → Prop) :
    Prop extends TakeSiteS p μ I where
  own : ∀ s hl, H s hl → ∀ h ∈ hl, h.1 = 0 ∧ Owned Λ h.2 s
  held : ∀ lbl lsize s c fs hl, I lbl lsize s c fs → H s hl → ∀ a, μ.site .take = some a → pcOf s = a →
    (Kernel.siteRange abi s).Sub Λ.stackPool ∧ 0 < (Kernel.siteRange abi s).size ∧
      Λ.rodata.Disjoint Λ.stackPool ∧ (∀ h ∈ hl, (Kernel.siteRange abi s).Disjoint h.2) ∧
      ∀ pm c' fs', I lbl lsize (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) (Kernel.siteRange abi s))))
          c' fs' →
        H (abi.skip (abi.setDmem s (Kernel.copyRange pm (abi.dmem s) (Kernel.siteRange abi s))))
          ((0, Kernel.siteRange abi s) :: hl)
  instr : ∀ lbl lsize s c fs hl, I lbl lsize s c fs → H s hl → WideSt s → Kernel.siteAt abi μ s = none →
    abi.atSys s = false → ∀ tree, isa.exec s = some tree →
    tree.AllInv (fun _ _ => True) (fun s' => ∀ lbl' lsize' c' fs', I lbl' lsize' s' c' fs' → H s' hl)
  sys : ∀ lbl lsize s c fs hl, I lbl lsize s c fs → H s hl → abi.atSys s = true → ∀ call,
    Kernel.decode abi.nrs (abi.nr s) (abi.arg s) = some call → ∀ s' ∈ Kernel.certSuccs abi s call,
    ∀ lbl' lsize' c' fs', I lbl' lsize' s' c' fs' → H s' hl

variable {Λ : Scc.Sem.Layout} {p : Prog} {μ : Marks} {I : InvS}

/-- A pair at a system call is off the take site (`TakePathS.off_sys` over
`TakeSiteS`). -/
theorem TakeSiteS.off_sys (hT : TakeSiteS p μ I) {lbl : Lbl} {lsize : Lsize} {s : State} {c : Ctl}
    {fs : List TermRun.Frame} (hI : I lbl lsize s c fs) (hs : abi.atSys s = true) :
    ∀ a, μ.site .take = some a → pcOf s ≠ a := fun a ha hpc => by
  have h := (hT.site _ _ _ _ _ hI a ha hpc).2.1
  rw [hs] at h; cases h

/-- **Every range `HeldOk` holds is thread 0's and owned.** -/
theorem _root_.Spike.Lib.X64Consumer.HeldOk.held_own {rS : Range} {Tk : State → Prop} {s : State}
    {hl : List (Nat × Range)} (h : HeldOk Λ rS Tk s hl) : ∀ x ∈ hl, x.1 = 0 ∧ Owned Λ x.2 s := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -, ho⟩
  · intro x hx; cases hx
  · intro x hx
    rw [List.mem_singleton] at hx; subst hx; exact ⟨rfl, ho⟩

/-- **`TakePathS` is a `HeldPathS` over `HeldOk`**: before the take none is
held (`site`'s `¬ Tk`), so the named range `rS` is off every held one; the
phase and ownership after it by `site` and `owned`; `instr`, `sys` by
`HeldOk.of_iff`. -/
theorem TakePathS.toH {rS : Range} {Tk : State → Prop} (hT : TakePathS Λ p μ I rS Tk) :
    HeldPathS Λ p μ I (HeldOk Λ rS Tk) where
  site lbl lsize s c fs hI a ha hpc := by
    obtain ⟨-, hcn, hsys, hsr, -, -, -, hrun⟩ := hT.site _ _ _ _ _ hI a ha hpc
    refine ⟨hcn, hsys, fun pm => ?_⟩
    obtain ⟨c', fs', hr, hI', -⟩ := hrun pm
    exact ⟨c', fs', hr, by rw [hsr]; exact hI'⟩
  own _ _ h := h.held_own
  held lbl lsize s c fs hl hI hh a ha hpc := by
    obtain ⟨hntk, -, -, hsr, hsub, hpos, hrod, hrun⟩ := hT.site _ _ _ _ _ hI a ha hpc
    obtain rfl : hl = [] := by
      rcases hh with ⟨h, -⟩ | ⟨-, h, -⟩
      · exact h
      · exact absurd h hntk
    rw [hsr]
    refine ⟨hsub, hpos, hrod, ?_, ?_⟩
    · intro x hx; cases hx
    · intro pm c' fs' hI'
      obtain ⟨-, -, -, -, htk⟩ := hrun pm
      exact .inr ⟨rfl, htk, hT.owned _ _ _ _ _ hI' htk⟩
  instr lbl lsize s c fs hl hI hh _ hsn hns tree he :=
    (hT.instr _ _ _ _ _ hI hsn hns tree he).mono fun _ hi _ _ _ _ hI' =>
      hh.of_iff hi (hT.owned _ _ _ _ _ hI')
  sys lbl lsize s c fs hl hI hh hs call hd s' hs' _ _ _ _ hI' :=
    hh.of_iff (hT.sys _ _ _ _ _ hI hs call hd s' hs') (hT.owned _ _ _ _ _ hI')

/-- `PostSA` is `PostSAH` at `HeldOk`. -/
theorem PostSA_eq {P : SrcSem.SrcParams} {rS : Range} {Tk : State → Prop} {t : T.M.Cfg}
    {s : TermRun.Cfg} : PostSA Λ P p rS Tk t s = PostSAH Λ P p (HeldOk Λ rS Tk) t s := rfl

end Spike.Lib.X64ConsumerS

namespace Spike.Lib.X64ConsumerA

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64
open Scc.Sem.SrcSem (mainExit)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS

variable {P : SrcSem.SrcParams} {p : Prog} {E : Entry}

/-- **Before the exit, over a fragment `J`, with the arena, the ranges held
by `H`** (`PreJ` with the heap clause the allocation invariant at the
source's heap use, the hold an exchange's or the counter's, `HoldInvA`, and
the counter off every placed label, `CtrOff`; the held list by a predicate
`H` of the thread state, `HeldPathS`). -/
def PreJAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (J : InvS)
    (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  ∃ (th : Thread isa) (th0 : TermRun.TTh) (j : Nat) (lbl : Lbl) (lsize : Lsize) (ts : Nat → Option Nat)
    (hl : List (Nat × Range)) (pm : _root_.Mem 64) (hd : Option (Nat × TermRun.Word)),
    t.1.threads = #[th] ∧ (∃ E : Entry, t.2 = KS E Λ j hl pm) ∧ (∀ a, Kernel.byte pm a = 0) ∧ H th.st hl ∧
    WrOk th j ∧
    CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t.2 0) 0 th t.1.mem ∧
    s.ths = #[th0] ∧ th0.σs = [] ∧ th0.promises = [] ∧
    J lbl lsize th.st ⟨th0.term, th0.env, hd⟩ th0.stack ∧ HoldInvA ar lbl lsize s.mem hd ∧ WideSt th.st ∧
    th.Bnd t.1.mem.last ∧ Inv1 Λ lbl lsize ts th t.1.mem s.mem ∧
    OwnMsgs t.1.mem ∧ MemIn Λ t.1.mem ∧ MemFits t.1.mem ∧ MemInv G t.1.mem ∧
    ExtRows.OwnOk (own th.st th0.stack) t.1.mem th.prom ∧
    AllocInvAt Λ lbl lsize th t.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) ⟨th0.term, th0.env, hd⟩ ∧
    AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc ∧ CtrOff ar lbl lsize ∧ ∃ tr, (SrcSem.source P p).Reach tr s

/-- **Before the exit**, the ranges held by `H` (`PreSA` over `H`):
`PreJAH` over the fragment. -/
abbrev PreSAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreJAH Λ P p G own I H μ ar t s

/-- **The relation**, the ranges held by `H` (`RSA` over `H`). -/
def RSAH (Λ : Scc.Sem.Layout) (P : SrcSem.SrcParams) (p : Prog) (G : Loc → Val → Prop) (own : OwnS) (I : InvS)
    (H : State → List (Nat × Range) → Prop) (μ : Marks) (ar : Arena) (t : T.M.Cfg) (s : TermRun.Cfg) : Prop :=
  PreSAH Λ P p G own I H μ ar t s ∨ PostSAH Λ P p H t s

/-- `PreJA` is `PreJAH` at `HeldOk`. -/
theorem PreJA_eq {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS}
    {J : InvS} {rS : Range} {Tk : State → Prop} {μ : Marks} {ar : Arena} {t : T.M.Cfg} {s : TermRun.Cfg} :
    PreJA Λ P p G own J rS Tk μ ar t s = PreJAH Λ P p G own J (HeldOk Λ rS Tk) μ ar t s := rfl

/-- `RSA` is `RSAH` at `HeldOk`. -/
theorem RSA_eq {Λ : Scc.Sem.Layout} {G : Loc → Val → Prop} {own : OwnS}
    {I : InvS} {rS : Range} {Tk : State → Prop} {μ : Marks} {ar : Arena} {t : T.M.Cfg} {s : TermRun.Cfg} :
    RSA Λ P p G own I rS Tk μ ar t s = RSAH Λ P p G own I (HeldOk Λ rS Tk) μ ar t s := rfl

variable {Λ : Scc.Sem.Layout} {lbl : Lbl} {lsize : Lsize} {ar : Arena}
variable {I : InvS} {μ : Marks} {rd : TermRun.Word → Prop} {G : Loc → Val → Prop} {own : OwnS}
  {ab : Option (State → Prop)} {Cl : State → Prop}

/-- **A pending frame run is taken**, the ranges held by `H` (`pend_runA`
over `H`). -/
theorem pend_runAH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s : TermRun.Cfg}
    (h : PreJAH Λ P p G own (PendA p I) H μ ar t s) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreSAH Λ P p G own I H μ ar t s' := by
  obtain ⟨th, th0, j, lbl, lsize, ts, hl, pm, hd, hth, hk, hz, hh, hwr, hcert, hs0, hσ, hp,
    ⟨hnr, c₂, fs₂, hr, hI⟩, hhi, hw, hb, hinv, hown, hmi, hfi, hgi, hoo, hai, hfr, hco, tr, hreach⟩ := h
  have hrun := frun_one (q := (⟨th0.term, th0.env, hd⟩, th0.stack)) hP hr hs0 rfl rfl hσ rfl hp hnr
    (fun h0 => hN.noRet _ _ _ _ (by simp only at h0; subst h0; exact hI))
  refine ⟨_, hrun, th, { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }, j, lbl, lsize, ts, hl, pm, c₂.hold,
    hth, hk, hz, hh, hwr, hcert, rfl, hσ, hp, hI, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi, ?_,
    ?_, (by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr), hco, _, reach_run hreach hrun⟩
  · show ExtRows.OwnOk (own th.st fs₂) _ _
    rw [hN.ownRun _ _ _ _ _ _ _ hr (.inr hI)]; exact hoo
  · rw [heapUse_one (th' := { th0 with term := c₂.term, env := c₂.env, stack := fs₂ }) hs0 rfl rfl]
    exact allocInvAt_frameRun hai hr

/-- **A frame run lands in `PreJAH`** over any fragment `J` (`pre_localJA`
over `H`). -/
theorem pre_localJAH (hP : HookOK P p) {J : InvS} {H : State → List (Nat × Range) → Prop} {t' : T.M.Cfg}
    {s : TermRun.Cfg} {u : Thread isa} {th0 : TermRun.TTh} {ts : Nat → Option Nat} {c' : Ctl}
    {fs' : List TermRun.Frame} {hl : List (Nat × Range)} {pm : _root_.Mem 64}
    {hd : Option (Nat × TermRun.Word)}
    (hth : t'.1.threads = #[u]) (hk : t'.2 = KS E Λ 0 hl pm) (hz : ∀ a, Kernel.byte pm a = 0)
    (hh : H u.st hl)
    (hc : CertOkC Arch.tso (Kernel.certSem abi Arch.tso μ t'.2 0) 0 u t'.1.mem) (hs0 : s.ths = #[th0])
    (hσ : th0.σs = []) (hp : th0.promises = []) (hJ : J lbl lsize u.st c' fs') (hw : WideSt u.st)
    (hb : u.Bnd t'.1.mem.last) (hinv : Inv1 Λ lbl lsize ts u t'.1.mem s.mem) (hown : OwnMsgs t'.1.mem)
    (hmi : MemIn Λ t'.1.mem) (hfi : MemFits t'.1.mem) (hgi : MemInv G t'.1.mem)
    (hoo : ExtRows.OwnOk (own u.st fs') t'.1.mem u.prom)
    (hai : AllocInvAt Λ lbl lsize u t'.1.mem ar.heap ar.cells ar.ctr ar.units ar.off (heapUse s) c')
    (hfr : AllocInv.FreshInv lbl s.lbase s.n 0 th0.nalloc) (hco : CtrOff ar lbl lsize)
    (hre : ∃ tr, (SrcSem.source P p).Reach tr s)
    (hhi : HoldInvA ar lbl lsize s.mem hd) (hcr : th0.stack = [] → ∀ a, th0.term ≠ .ret a)
    (hcr' : fs' = [] → ∀ a, c'.term ≠ .ret a) (hr : FrameRun p (⟨th0.term, th0.env, hd⟩, th0.stack) (c', fs')) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ PreJAH Λ P p G own J H μ ar t' s' := by
  have hrun := frun_one hP hr hs0 rfl rfl hσ rfl hp hcr hcr'
  obtain ⟨tr, hre⟩ := hre
  exact ⟨_, hrun, u, { th0 with term := c'.term, env := c'.env, stack := fs' }, 0, lbl, lsize, ts, hl, pm, c'.hold,
    hth, ⟨E, hk⟩, hz, hh, .inl rfl, hc, rfl, hσ, hp, hJ, holdInvA_frameRun hr hhi, hw, hb, hinv, hown, hmi, hfi, hgi,
    hoo, by rw [heapUse_one (th' := { th0 with term := c'.term, env := c'.env, stack := fs' }) hs0 rfl rfl]; exact hai,
    by rw [TermRun.Cfg.n, hs0] at hfr; exact hfr, hco, _, reach_run hre hrun⟩

/-- **A landing over `PendA` is a step of the relation**, the ranges held by
`H` (`pend_landA` over `H`). -/
theorem pend_landAH (hP : HookOK P p) (hN : NodesA Λ p μ rd G own ar I ab Cl)
    {H : State → List (Nat × Range) → Prop} {t : T.M.Cfg} {s s₂ : TermRun.Cfg}
    (hrun : (SrcSem.source P p).Run s [] s₂) (h : PreJAH Λ P p G own (PendA p I) H μ ar t s₂) :
    ∃ s', (SrcSem.source P p).Run s [] s' ∧ RSAH Λ P p G own I H μ ar t s' := by
  obtain ⟨s', hr, hpre⟩ := pend_runAH hP hN h
  exact ⟨s', run_trans0 hrun hr, .inl hpre⟩

end Spike.Lib.X64ConsumerA

/-! ## Axiom guards -/

/--
info: 'Spike.Lib.X64ConsumerS.TakeSiteS.off_sys' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerS.TakeSiteS.off_sys

/--
info: 'Spike.Lib.X64Consumer.HeldOk.held_own' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64Consumer.HeldOk.held_own

/--
info: 'Spike.Lib.X64ConsumerS.TakePathS.toH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerS.TakePathS.toH

/--
info: 'Spike.Lib.X64ConsumerS.PostSA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerS.PostSA_eq

/--
info: 'Spike.Lib.X64ConsumerA.PreJA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.PreJA_eq

/--
info: 'Spike.Lib.X64ConsumerA.RSA_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.RSA_eq

/--
info: 'Spike.Lib.X64ConsumerA.pend_runAH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pend_runAH

/--
info: 'Spike.Lib.X64ConsumerA.pre_localJAH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pre_localJAH

/--
info: 'Spike.Lib.X64ConsumerA.pend_landAH' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Spike.Lib.X64ConsumerA.pend_landAH
