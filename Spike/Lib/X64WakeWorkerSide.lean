/-
**wake.w's worker side on x86-64 and its fields of `WCompat`** (in the
manner of `Spike/Lib/WakeWorkerSide.lean`). The worker's `WSide` comes from
its segment off the transfer sites, keeping a fragment `Z`
(`SegTC (NNZ exe endPc Z)`, `Spike/Lib/X64WakeChildNN.lean`), cut down to the
wide fragment (`SegTC.closed_conjS` with `WideX exe`). The file also gives
the fields of `Spike.Lib.X64WakeW1.WCompat` that follow from the invariant
lying inside `NN exe endPc ∧ Z ∧ WideX exe`.

- `wi_exists`: the closed invariant inside `NN ∧ Z ∧ WideX` of a worker
  segment to the empty fragment.
- `side`: the worker's `WSide` from a family of such segments (given the
  placement `lbl`, the memory sides `ms`, the pointer words `cw` and the
  spawn sizes `S`). Its invariant lies inside `NN ∧ Z ∧ WideX`
  (`side_inv`, `side_nnw`, `side_z`); `side_entry` puts the entries in it.
- Fields, for any `WSide` whose invariant lies inside `NN ∧ WideX` (`hD`):
  - `wide_of` (`WCompat.wide`);
  - `noSite_of` (`WCompat.noSite`, at marks linked to the labels: `hμ`);
  - `noSite_ofPlaceWX` (the same at `PhRec.μ` of `ofPlaceWX`, with no link
    premise);
  - `sysExec_of` (`WCompat.sysExec`) and `sysOk_of` (`WCompat.sysOk`).
- At `side`: `side_lbl`, `side_K`, `side_S` (`WCompat.lbl`, `K`, `S`, given
  the matching data).
- `pass_of` (`WCompat.pass`), for an invariant inside `Z := wakePass`
  (`Spike/Lib/X64WakePass.lean`), at the target store point `wakePassT`.
- `ownInstr_ofZX` (`WCompat.ownInstr`, X64-OwnInstrW), for an invariant
  inside `Z := wakeZX … W …` (`OwnInstrW.ownInstr_of`).
- `wideX_childAfter`, `wideX_of`, `wake_wideIn`, `wake_exeWide`,
  `clonePre_childWide`: the spawned child's entry is `WideX exe`
  (`side_entry`'s `hW`).
- `side_cwv`, `clonePre_cw`, `clonePre_me`: `WCompat.cwv` at the spawn's
  constant pointer words, and the words `c` and `me` are bound to at the
  clone.

**Unlike AArch64** (forced by the x64 shape):
- There is no `wake_hμ`. The x86-64 runtime's marks are `PhRec.μ L`, whose
  sites are `codeLabel`s of the placed program, so `noSite_ofPlaceWX`
  closes `noSite` at `ofPlaceWX` through `PlaceWX.lab_toNat` instead.
- The stub's registers are `%r12` (`c`) and `%rbx` (`me`); AArch64 uses
  `x9` and `x10`.
- `ClonePre` has no prefix argument.
- The worker owns its TCB self word, so `ownInstr` is a field here
  (AArch64: `OwnTree.nil` in the assembly).
- The listing's fragment check is over the byte-sized cells
  (`wideIn (wakeCells.map (·.1))`).
-/
import Spike.Lib.X64WakeChildNN
import Spike.Lib.X64WakeSites
import Spike.Lib.X64WideKeep
import Spike.Lib.X64SvcFault
import Spike.Lib.X64Handover
import Spike.Lib.X64AbOffL
import Spike.Lib.X64WakeOwnInstrW

namespace Spike.Lib.X64WakeW1.WorkerSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Spike.Lib Spike.Lib.X64WakeA64 Spike.Lib.X64WakeT1
open Spike.Lib.X64.Flow.Worker (NN NNZ siteAt_none_of_nn nn_ne_site)
open Spike.Lib.X64.Flow.Worker.Wake.Pass (wakePass wakePassT)
open Spike.Lib.X64.WideKeep (WideX wideX_exec wideX_kern)
open Scc.Cert.Rt.X64 (Lays endOf)

variable {exe : _root_.Executable} {endPc : Int64}

/-! ## The invariant -/

/-- **The worker's closed invariant inside `NN ∧ Z ∧ WideX`** of its segment
off the transfer sites to the empty fragment, from its entry's `P` states
in `WideX exe`. -/
theorem wi_exists {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isa} {P Z : Frag isa}
    (hK : ms.K = some Scc.Sem.X64.abi) (h : SegTC (NNZ exe endPc Z) wakeSrc lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag isa, (∀ s c, P s c → WideX exe s → inv s c) ∧
      (∀ s c, inv s c → NNZ exe endPc Z s c ∧ WideX exe s) ∧ ∀ s c, inv s c → OutT wakeSrc lbl ms inv s c :=
  h.closed_conjS (wideX_exec exe) (wideX_kern hK exe)

/-- **The worker's side** from a family of segments off the transfer sites
(`h`, under the kernel model `hK`): the invariant `wi_exists` chooses. -/
noncomputable def side {ι : Type} (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → MemSide isa)
    (P : ι → Frag isa) {Z : Frag isa} (hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi)
    (h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False))
    (cw : ι → TermRun.Word) (S : ι → Nat) : WSide ι where
  lbl := lbl
  ms := ms
  Wi w := Classical.choose (wi_exists (hK w) (h w))
  closed w := (Classical.choose_spec (wi_exists (hK w) (h w))).2.2
  cw := cw
  S := S

section Side

variable {ι : Type} {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → MemSide isa}
  {P : ι → Frag isa} {Z : Frag isa} {hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi}
  {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
  {cw : ι → TermRun.Word} {S : ι → Nat}

/-- `side`'s invariant holds the segments' entries in `WideX exe`. -/
theorem side_entry (w : ι) (s : State) (c : Ctl) (hP : P w s c) (hW : WideX exe s) :
    (side lbl ms P hK h cw S).Wi w s c :=
  (Classical.choose_spec (wi_exists (hK w) (h w))).1 s c hP hW

/-- **`side`'s invariant lies inside `NN ∧ Z ∧ WideX`.** -/
theorem side_inv : ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → NNZ exe endPc Z s c ∧ WideX exe s :=
  fun w => (Classical.choose_spec (wi_exists (hK w) (h w))).2.1

/-- `side`'s invariant lies inside `NN ∧ WideX` (the fields' `hD`). -/
theorem side_nnw : ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → NN exe endPc s ∧ WideX exe s :=
  fun w s c hw => ⟨(side_inv w s c hw).1.1, (side_inv w s c hw).2⟩

/-- `side`'s invariant lies inside `Z`. -/
theorem side_z : ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → Z s c :=
  fun w s c hw => (side_inv w s c hw).1.2

/-- `side`'s invariant lies inside `NNZ exe endPc Z`. -/
theorem side_nnz : ∀ w s c, (side lbl ms P hK h cw S).Wi w s c → NNZ exe endPc Z s c :=
  fun w s c hw => (side_inv w s c hw).1

/-- (`WCompat.K`) -/
theorem side_K : ∀ w, ((side lbl ms P hK h cw S).ms w).K = some Scc.Sem.X64.abi := hK

end Side

/-- (`WCompat.lbl`) at the spawn's placement. -/
theorem side_lbl {Q : WakeRel} {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isa}
    {P : Q.ι → Frag isa} {Z : Frag isa} {hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat} (hl : ∀ w, lbl w = (Q.SR w).lbl) :
    ∀ w, (side lbl ms P hK h cw S).lbl w = (Q.SR w).lbl := hl

/-- (`WCompat.S`) at the spawn records' sizes. -/
theorem side_S {Q : WakeRel} {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isa}
    {P : Q.ι → Frag isa} {Z : Frag isa} {hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat} (hS : ∀ w, S w = (Q.SR w).S) :
    ∀ w, (side lbl ms P hK h cw S).S w = (Q.SR w).S := hS

/-- (`WCompat.cwv`) at the spawn's constant pointer words: `cw w` the
untagged locative to the flag's source address (the word `c` is bound to at
the clone, `clonePre_cw`). -/
theorem side_cwv {Q : WakeRel} {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isa}
    {P : Q.ι → Frag isa} {Z : Frag isa} {hK : ∀ w, (ms w).K = some Scc.Sem.X64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat} (hc : ∀ w, cw w = TermRun.cst (.loc (Q.C w).cS 0)) :
    ∀ w, ((side lbl ms P hK h cw S).cw w).val = .loc (Q.C w).cS 0 := fun w => by
  show (cw w).val = _
  rw [hc w]; rfl

/-- **The pointer word at the clone**: main's `c` is bound to the constant
untagged locative `cst (.loc ⟨l, 0⟩ 0)`, which `cA` (`%r12`) represents
(`side_cwv`'s `hc` with `(Q.C w).cS = ⟨l, 0⟩`; `seg_childPreNN`'s `w1` with
its `htag`). -/
theorem clonePre_cw {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isa) (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), t.1.threads = #[th] ∧
      s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc ⟨l, 0⟩ 0 ∧
      Scc.Sem.ValRep lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val (th.st.st.1.regs.get64 .r12).toNat := by
  obtain ⟨th, th0, -, cA, -, l, hth, hs, -, -, -, -, -, -, h12, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, hv, -⟩ :=
    h
  exact ⟨th, th0, l, hth, hs, hc, rfl, h12 ▸ hv⟩

/-- **Main's `ThreadId` word at the clone**: main's `me` is bound to the
locative of its tid label `mainTidLbl 2`, which `meW` (`%rbx`) represents
(the word `w2` of the worker's argument). -/
theorem clonePre_me {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isa) (th0 : TermRun.TTh), t.1.threads = #[th] ∧ s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "me") =
        some (.tid, [TermRun.cst (.loc ⟨Spike.Lib.X64WakeSrcDefs.mainTidLbl 2, 0⟩ 0)]) ∧
      Scc.Sem.ValRep lbl (.loc ⟨Spike.Lib.X64WakeSrcDefs.mainTidLbl 2, 0⟩ 0) (th.st.st.1.regs.get64 .rbx).toNat := by
  obtain ⟨th, th0, -, -, meW, -, hth, hs, -, -, -, -, -, -, -, hbx, -, -, -, -, -, -, -, -, -, -, -, hme, -, -, hv⟩ :=
    h
  exact ⟨th, th0, hth, hs, hme, hbx ▸ hv⟩

/-! ## The fields from the invariant -/

section Fields

variable {ι : Type} {D : WSide ι} (hD : ∀ w s c, D.Wi w s c → NN exe endPc s ∧ WideX exe s)
include hD

/-- (`WCompat.wide`) -/
theorem wide_of : ∀ w s c, D.Wi w s c → Scc.Cert.WideX64.WideSt s :=
  fun w s c hw => (hD w s c hw).2.1

/-- (`WCompat.noSite`) at marks whose sites are the labels' addresses
(`hμ`). -/
theorem noSite_of [Kraken.Executable.ValidLayout exe] {kp : Nat} {μ : Scc.Sem.Marks}
    (hp : Lays exe SccCode.wakeCells kp) (hend : endPc = endOf exe SccCode.wakeCells kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat) :
    ∀ w s c, D.Wi w s c → Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi μ s = none :=
  fun w s c hw => siteAt_none_of_nn hp hend hμ (hD w s c hw).1

/-- (`WCompat.sysExec`) -/
theorem sysExec_of [Kraken.Executable.ValidLayout exe] :
    ∀ w s c t, D.Wi w s c → Scc.Sem.X64.abi.atSys s = true → isa.exec s = some t → ∃ m, t = .fault m :=
  Spike.Lib.X64.SvcFault.sysExec_of_exe fun w s c hw => (hD w s c hw).1.1

/-- (`WCompat.sysOk`) -/
theorem sysOk_of : ∀ w s c call, D.Wi w s c → Scc.Sem.X64.abi.atSys s = true →
    Scc.Sem.Kernel.decode Scc.Sem.X64.abi.nrs (Scc.Sem.X64.abi.nr s) (Scc.Sem.X64.abi.arg s) = some call →
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v) :=
  fun w s c call hw ha hd => (hD w s c hw).1.2.2.2 ha call hd

end Fields

section Place

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.X64.Out} {Λ : Scc.Sem.Layout}
  (hpl : PlaceWX pcfg Λ o) (i : CoreTerm.Expr → String → Nat → Option Nat)

set_option hygiene false in
/-- The layout of `ofPlaceWX`. -/
local notation "Ly" => Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceWX hpl i

/-- (`WCompat.noSite`) at the runtime's marks `PhRec.μ` of `ofPlaceWX`, for
a side whose invariant lies inside `NN (Ly).exe endPc ∧ WideX`, the listing
laid out in `(Ly).exe` (`hp`, `hend`): the sites are the `codeLabel`s of
the two labels (`PlaceWX.lab_toNat`), neither an `NN` state's pc
(`nn_ne_site`). -/
theorem noSite_ofPlaceWX {ι : Type} {D : WSide ι} {kp : Nat}
    (hD : ∀ w s c, D.Wi w s c → NN (Ly).exe endPc s ∧ WideX (Ly).exe s)
    (hp : Lays (Ly).exe SccCode.wakeCells kp) (hend : endPc = endOf (Ly).exe SccCode.wakeCells kp) :
    ∀ w s c, D.Wi w s c → Scc.Sem.Kernel.siteAt Scc.Sem.X64.abi (Spike.Lib.X64.PhRec.μ (Ly)) s = none := by
  intro w s c hw
  have : Kraken.Executable.ValidLayout (Ly).exe := (Ly).valid
  obtain ⟨ht, hr⟩ := nn_ne_site hp hend (hD w s c hw).1
  refine Scc.Sem.Kernel.siteAt_eq_none_iff.mpr ⟨fun he => ?_, fun he => ?_⟩
  · change Scc.Sem.X64.codeLabel Λ.code.lo o.prog "scc_rt_take_site" = some (Scc.Sem.X64.pcOf s) at he
    exact ht (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (PlaceWX.lab_toNat hpl i he).symm))
  · change Scc.Sem.X64.codeLabel Λ.code.lo o.prog "scc_rt_release_site" = some (Scc.Sem.X64.pcOf s) at he
    exact hr (Int64.toBitVec_inj.mp (BitVec.eq_of_toNat_eq (PlaceWX.lab_toNat hpl i he).symm))

end Place

/-- (`WCompat.pass`) for a `WSide` whose invariant lies inside `wakePass`
(`side_z` at a `Z` inside `wakePass`, from `seg_childPreNN` with
`Pass.childThrZ`, `cZ_pass`), the flag records' target store point
`wakePassT`. -/
theorem pass_of {Q : WakeRel} {D : WSide Q.ι} (hZ : ∀ w s c, D.Wi w s c → wakePass s c)
    (hpT : ∀ w, (Q.C w).passT = wakePassT) :
    ∀ w s c, D.Wi w s c → ((Q.C w).passT s ↔ (c.term = Spike.Lib.WorkerSrc.wkUnpark ∨ c.term = .ret .unit)) :=
  fun w s c hw => by rw [hpT w]; exact hZ w s c hw

/-- (`WCompat.ownInstr`, X64-OwnInstrW) for a `WSide` whose invariant lies
inside `NNZ exe endPc (wakeZX Λ lbl cS W exe kp)` (`side_nnz`), at the owned
words `wakeOwnXW T W`. -/
theorem ownInstr_ofZX {Q : WakeRel} {D : WSide Q.ι} {T W : BitVec 64} {kp : Nat} {Λ : Scc.Sem.Layout}
    {lbl : WeakMem.AllocLabel → Option Nat} {cS : WeakMem.Address}
    (hown : Q.own = X64WakeOwnX.wakeOwnXW T W)
    (hD : ∀ w s c, D.Wi w s c → NNZ exe endPc (Spike.Lib.X64.Flow.Worker.Wake.ZX.wakeZX Λ lbl cS W exe kp) s c) :
    ∀ w s c tree, D.Wi w s c → Scc.Sem.X64.abi.atSys s = false → isa.exec s = some tree →
      Consumer1.OwnTree (fun s => Q.own w 1 s []) (Q.own w 1 s []) tree :=
  OwnInstrW.ownInstr_ofX hown hD

/-! ## The child's entry in the fragment -/

/-- **The child after the handover is `WideX exe`** when its parent is: the
handover changes the machine state only (`X64Handover.child_st`). -/
theorem wideX_childAfter {x : Scc.Sem.Kernel.KState} {tid : Nat} {th : Thread isa} {stack tls : Nat}
    (h : WideX exe th.st) : WideX exe (Spike.Lib.Handover.childAfter Scc.Sem.X64.abi x tid th stack tls).st := by
  obtain ⟨m, hc, -⟩ := Spike.Lib.X64Handover.child_st (x := x) (tid := tid) (t := th) (stack := stack) (tls := tls)
  rw [hc]; exact h

/-- A state at a fragment executable `exe` with no declarations is `WideX exe`. -/
theorem wideX_of {st : State} (hw : Scc.Cert.WideX64.ExeWide exe) (he : st.exe = exe) (hd : st.decls = {}) :
    WideX exe st :=
  ⟨⟨hd ▸ Scc.Cert.WideX64.declsWide_empty, he ▸ hw⟩, he⟩

/-- **wake's listing is in the fragment.** -/
theorem wake_wideIn : Scc.Cert.WideX64.wideIn (SccCode.wakeCells.map (·.1)) = true := by decide +kernel

/-- **The canonical thread's executable of wake's listing is in the
fragment** (`wideSt_threadAt`). -/
theorem wake_exeWide (E : Scc.Sem.Entry) (base : Nat) (syms : List (String × Nat)) :
    Scc.Cert.WideX64.ExeWide (Scc.Sem.X64.threadAt E base SccCode.wakeCells syms).exe :=
  (Scc.Cert.WideX64.wideSt_threadAt wake_wideIn E base syms).2

/-- **The spawned child's entry is `WideX exe`** (`side_entry`'s `hW` for
`seg_childPreNN`'s child): from the clone's precondition with `hX` (as
`seg_childPreNN`) and a fragment executable `hw` (`wake_exeWide`). -/
theorem clonePre_childWide {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.X64WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.X64WakePreA.ClonePre Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (hw : Scc.Cert.WideX64.ExeWide exe) :
    ∃ th : Thread isa, t.1.threads = #[th] ∧
      ∀ tid stack tls, WideX exe (Spike.Lib.Handover.childAfter Scc.Sem.X64.abi t.2 tid th stack tls).st := by
  obtain ⟨th, -, -, -, -, -, hth, -, -, -, -, -, -, -, -, -, -, -, -, -, hXs, -⟩ := h
  obtain ⟨he, -, hd⟩ := hX _ hXs
  exact ⟨th, hth, fun _ _ _ => wideX_childAfter (wideX_of hw he hd)⟩

end Spike.Lib.X64WakeW1.WorkerSide

/-- info: 'Spike.Lib.X64WakeW1.WorkerSide.noSite_ofPlaceWX' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64WakeW1.WorkerSide.noSite_ofPlaceWX
