/-
**wake.w's worker side on AArch64 and its fields of `WCompat`**: the worker's `WSide` from its segment off the transfer sites
keeping a fragment `Z` (`SegTC (NNZ exe endPc Z)`,
`Spike/Lib/A64WakeChildNN.lean`) cut down to the wide fragment
(`SegTC.closed_conjS` with `WideX exe`), and the fields of
`Spike.Lib.WakeW1.WCompat` that follow from the invariant lying inside
`NN exe endPc ∧ Z ∧ WideX exe`. The listing is wake.w's certificate
(`Spike/Test/Cert/A64WakeCert.s`).

- `wi_exists`: the closed invariant inside `NN ∧ Z ∧ WideX` of a worker
  segment to the empty fragment.
- `side`: the worker's `WSide` from a family of such segments (the
  placement `lbl`, the memory sides `ms`, the pointer words `cw`, the
  spawn sizes `S` given), its invariant `side_inv` inside `NN ∧ Z ∧ WideX`
  (`side_nnw`, `side_z`).
- Fields, for any `WSide` whose invariant lies inside `NN ∧ WideX`
  (`hD`): `wide_of` (`WCompat.wide`), `noSite_of` (`WCompat.noSite`, at
  marks linked to the labels: `hμ`), `sysExec_of` (`WCompat.sysExec`),
  `sysOk_of` (`WCompat.sysOk`); at `side`: `side_lbl`, `side_K`, `side_S`
  (`WCompat.lbl`, `K`, `S`, given the matching data); `pass_of`
  (`WCompat.pass`) for an invariant inside `Z := wakePass`
  (`Spike/Lib/A64WakePass.lean`) at the target store point `wakePassT`.
- `wake_hμ`: the link `hμ` of the canonical target's marks of wake's
  listing to the labels of its loaded thread (`resolve_of_parsed`, the
  loader's parse `hpa` the trust boundary, as `ret0_marks`).
- `wideX_childAfter`, `wideX_of`, `wake_wideIn`, `wake_exeWide`,
  `clonePre_childWide`: the spawned child's entry is `WideX exe`
  (`side_entry`'s `hW`).
- `side_cwv`, `clonePre_cw`: `WCompat.cwv` at the spawn's constant pointer
  words, and the word `c` is bound to at the clone.
-/
import Spike.Lib.A64WakeChildNN
import Spike.Lib.A64WakePass
import Spike.Lib.A64WakeSites
import Spike.Lib.A64WideKeep
import Spike.Lib.A64SvcFault
import Spike.Lib.A64PhRec
import Spike.Lib.WakeW1Compat

namespace Spike.Lib.WakeW1.WorkerSide

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.WakeT1
open Spike.Lib.A64.Flow.Worker (NN NNZ siteAt_none_of_nn)
open Spike.Lib.A64.Flow.Worker.Wake.Pass (wakePass wakePassT)
open Spike.Lib.A64.WideKeep (WideX wideX_exec wideX_kern)
open Spike.Lib.A64.WakeLabels (wakeProg)
open Scc.Cert.Rt.A64 (Lays endOf)

variable {exe : _root_.Executable} {endPc : Int64}

/-! ## The invariant -/

/-- **The worker's closed invariant inside `NN ∧ Z ∧ WideX`** of its segment
off the transfer sites to the empty fragment, from its entry's `P` states
in `WideX exe`. -/
theorem wi_exists {lbl : WeakMem.AllocLabel → Option Nat} {ms : MemSide isaLSE2} {P Z : Frag isaLSE2}
    (hK : ms.K = some Scc.Sem.A64.abi) (h : SegTC (NNZ exe endPc Z) wakeSrc lbl ms P (fun _ _ => False)) :
    ∃ inv : Frag isaLSE2, (∀ s c, P s c → WideX exe s → inv s c) ∧
      (∀ s c, inv s c → NNZ exe endPc Z s c ∧ WideX exe s) ∧ ∀ s c, inv s c → OutT wakeSrc lbl ms inv s c :=
  h.closed_conjS (wideX_exec exe) (wideX_kern hK exe)

/-- **The worker's side** from a family of segments off the transfer sites
(`h`, under the kernel model `hK`): the invariant `wi_exists` chooses. -/
noncomputable def side {ι : Type} (lbl : ι → WeakMem.AllocLabel → Option Nat) (ms : ι → MemSide isaLSE2)
    (P : ι → Frag isaLSE2) {Z : Frag isaLSE2} (hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi)
    (h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False))
    (cw : ι → TermRun.Word) (S : ι → Nat) : WSide ι where
  lbl := lbl
  ms := ms
  Wi w := Classical.choose (wi_exists (hK w) (h w))
  closed w := (Classical.choose_spec (wi_exists (hK w) (h w))).2.2
  cw := cw
  S := S

section Side

variable {ι : Type} {lbl : ι → WeakMem.AllocLabel → Option Nat} {ms : ι → MemSide isaLSE2}
  {P : ι → Frag isaLSE2} {Z : Frag isaLSE2} {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
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


/-- (`WCompat.K`) -/
theorem side_K : ∀ w, ((side lbl ms P hK h cw S).ms w).K = some Scc.Sem.A64.abi := hK


end Side

/-- (`WCompat.lbl`) at the spawn's placement. -/
theorem side_lbl {Q : WakeRel} {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isaLSE2}
    {P : Q.ι → Frag isaLSE2} {Z : Frag isaLSE2} {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat} (hl : ∀ w, lbl w = (Q.SR w).lbl) :
    ∀ w, (side lbl ms P hK h cw S).lbl w = (Q.SR w).lbl := hl

/-- (`WCompat.S`) at the spawn records' sizes. -/
theorem side_S {Q : WakeRel} {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isaLSE2}
    {P : Q.ι → Frag isaLSE2} {Z : Frag isaLSE2} {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat} (hS : ∀ w, S w = (Q.SR w).S) :
    ∀ w, (side lbl ms P hK h cw S).S w = (Q.SR w).S := hS

/-- (`WCompat.cwv`) at the spawn's constant pointer words: `cw w` the
untagged locative to the flag's source address (the word `c` is bound to at
the clone, `clonePre_cw`). -/
theorem side_cwv {Q : WakeRel} {lbl : Q.ι → WeakMem.AllocLabel → Option Nat} {ms : Q.ι → MemSide isaLSE2}
    {P : Q.ι → Frag isaLSE2} {Z : Frag isaLSE2} {hK : ∀ w, (ms w).K = some Scc.Sem.A64.abi}
    {h : ∀ w, SegTC (NNZ exe endPc Z) wakeSrc (lbl w) (ms w) (P w) (fun _ _ => False)}
    {cw : Q.ι → TermRun.Word} {S : Q.ι → Nat} (hc : ∀ w, cw w = TermRun.cst (.loc (Q.C w).cS 0)) :
    ∀ w, ((side lbl ms P hK h cw S).cw w).val = .loc (Q.C w).cS 0 := fun w => by
  show (cw w).val = _
  rw [hc w]; rfl

/-- **The pointer word at the clone**: main's `c` is bound to the constant
untagged locative `cst (.loc ⟨l, 0⟩ 0)`, which `cA` (`x9`) represents
(`side_cwv`'s `hc` with `(Q.C w).cS = ⟨l, 0⟩`; `seg_childPreNN`'s `w1` with
its `htag`). -/
theorem clonePre_cw {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfx Λ r0 r1 X lbl t s) :
    ∃ (th : Thread isaLSE2) (th0 : TermRun.TTh) (l : WeakMem.AllocLabel), t.1.threads = #[th] ∧
      s.ths = #[th0] ∧
      TermRun.evalAt th0.env (.var "c") = some (.ptr .pub .int, [TermRun.cst (.loc ⟨l, 0⟩ 0)]) ∧
      (TermRun.cst (.loc ⟨l, 0⟩ 0)).val = .loc ⟨l, 0⟩ 0 ∧
      Scc.Sem.ValRep lbl (TermRun.cst (.loc ⟨l, 0⟩ 0)).val (th.st.st.1.regs.getXReg .X9).toNat := by
  obtain ⟨th, th0, -, cA, -, l, hth, hs, -, -, -, -, -, -, h9, -, -, -, -, -, -, -, -, -, -, -, hc, -, -, hv, -⟩ := h
  exact ⟨th, th0, l, hth, hs, hc, rfl, h9 ▸ hv⟩

/-! ## The fields from the invariant -/

section Fields

variable {ι : Type} {D : WSide ι} (hD : ∀ w s c, D.Wi w s c → NN exe endPc s ∧ WideX exe s)
include hD

/-- (`WCompat.wide`) -/
theorem wide_of : ∀ w s c, D.Wi w s c → Scc.Cert.WideA64.WideSt s :=
  fun w s c hw => (hD w s c hw).2.1

/-- (`WCompat.noSite`) at marks whose sites are the labels' addresses
(`hμ`; `wake_hμ` for the canonical target). -/
theorem noSite_of [Kraken.Executable.ValidLayout exe] {kp : Nat} {μ : Scc.Sem.Marks}
    (hp : Lays exe wakeProg kp) (hend : endPc = endOf exe wakeProg kp)
    (hμ : μ.site .take = some ((_root_.Executable.labels exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      μ.site .release = some ((_root_.Executable.labels exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat) :
    ∀ w s c, D.Wi w s c → Scc.Sem.Kernel.siteAt Scc.Sem.A64.abi μ s = none :=
  fun w s c hw => siteAt_none_of_nn hp hend hμ (hD w s c hw).1

/-- (`WCompat.sysExec`) -/
theorem sysExec_of [Kraken.Executable.ValidLayout exe] :
    ∀ w s c t, D.Wi w s c → Scc.Sem.A64.abi.atSys s = true → isaLSE2.exec s = some t → ∃ m, t = .fault m :=
  Spike.Lib.A64.SvcFault.sysExec_of_exe fun w s c hw => (hD w s c hw).1.1

/-- (`WCompat.sysOk`) -/
theorem sysOk_of : ∀ w s c call, D.Wi w s c → Scc.Sem.A64.abi.atSys s = true →
    Scc.Sem.Kernel.decode Scc.Sem.A64.abi.nrs (Scc.Sem.A64.abi.nr s) (Scc.Sem.A64.abi.arg s) = some call →
    call = .exit ∨ ((∀ fd buf n, call ≠ .write fd buf n) ∧ ∀ v, call ≠ .exitGroup v) :=
  fun w s c call hw ha hd => (hD w s c hw).1.2.2.2 ha call hd

end Fields

/-- (`WCompat.pass`) for a `WSide` whose invariant lies inside `wakePass`
(`side_z` at `Z := wakePass`, from `seg_childPreNN` with `childThrZ`,
`cZ_pass`), the flag records' target store point `wakePassT`. -/
theorem pass_of {Q : WakeRel} {D : WSide Q.ι} (hZ : ∀ w s c, D.Wi w s c → wakePass s c)
    (hpT : ∀ w, (Q.C w).passT = wakePassT) :
    ∀ w s c, D.Wi w s c → ((Q.C w).passT s ↔ (c.term = Spike.Lib.WorkerSrc.wkUnpark ∨ c.term = .ret .unit)) :=
  fun w s c hw => by rw [hpT w]; exact hZ w s c hw

/-! ## The marks' link to the labels -/

/-- A label the program has (by `labelName`) is a cell of it. -/
private theorem mem_of_any {l : String} {prog : Program}
    (h : prog.any (fun d => Scc.Sem.A64.labelName d == some l) = true) : Directive.label l ∈ prog := by
  obtain ⟨d, hd, he⟩ := List.any_eq_true.mp h
  have : d = .label l := by cases d <;> simp_all [Scc.Sem.A64.labelName]
  exact this ▸ hd

/-- Both transfer sites are labels of wake's program. -/
theorem wake_siteLabels : Directive.label "scc_rt_take_site" ∈ wakeProg ∧
    Directive.label "scc_rt_release_site" ∈ wakeProg :=
  have h : wakeProg.any (fun d => Scc.Sem.A64.labelName d == some "scc_rt_take_site") = true ∧
      wakeProg.any (fun d => Scc.Sem.A64.labelName d == some "scc_rt_release_site") = true := by decide +kernel
  ⟨mem_of_any h.1, mem_of_any h.2⟩

/-- A label of the program, at its `codeOf` address in the canonical
loader's thread, is below `2 ^ 64` and the marks' resolution of it. -/
private theorem site_eq {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout}
    {secs : Scc.Sem.DataSecs} (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hl : Scc.Cert.Link.A64.loadOk Λ wakeProg secs = true) {l : String} (hin : Directive.label l ∈ wakeProg) :
    (Scc.Sem.A64.target H E).resolve SccCertificate.asm Λ l =
      some ((_root_.Executable.labels
        (Scc.Sem.A64.threadAt E Λ.code.lo wakeProg (Scc.Sem.loadSyms Λ secs.rodata)).exe).label l).toBitVec.toNat := by
  rw [Scc.Sem.A64.resolve_of_parsed H E Λ hpa]
  cases ha : Scc.Cert.Link.A64.codeOf Λ.code.lo wakeProg l with
  | none => exact absurd rfl (Scc.Cert.Link.A64.ne_label_of_codeOf ha _ hin)
  | some a =>
    have ha' : Scc.Sem.labelAddr Scc.Sem.A64.labelName Directive.fakeSize Λ.code.lo l wakeProg = some a := ha
    rw [ha', Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (Scc.Cert.Link.A64.below_ne_of_loadOk hl ha) ha]
    have hlt : a < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (Spike.Lib.A64.PhRec.le_codeEnd_of_codeOf ha) (Scc.Cert.Link.A64.codeEnd_lt_of_loadOk hl)
    simp [Nat.mod_eq_of_lt hlt]

/-- **The canonical target's marks of wake's listing are its labels'
addresses** in the loaded thread (`hμ` of `noSite_of`), given the loader's
parse of the listing (`hpa`, the trust boundary) and the loader's checks
(`hl`). -/
theorem wake_hμ {H : Scc.Sem.Hooks isaLSE2} {E : Scc.Sem.Entry} {Λ : Scc.Sem.Layout} {secs : Scc.Sem.DataSecs}
    (hpa : Scc.Sem.A64.textProgram SccCertificate.asm = .ok wakeProg)
    (hl : Scc.Cert.Link.A64.loadOk Λ wakeProg secs = true) :
    ((Scc.Sem.A64.target H E).marks SccCertificate.asm Λ).site .take =
        some ((_root_.Executable.labels (Scc.Sem.A64.threadAt E Λ.code.lo wakeProg
          (Scc.Sem.loadSyms Λ secs.rodata)).exe).label Scc.Lower.Names.takeSite).toBitVec.toNat ∧
      ((Scc.Sem.A64.target H E).marks SccCertificate.asm Λ).site .release =
        some ((_root_.Executable.labels (Scc.Sem.A64.threadAt E Λ.code.lo wakeProg
          (Scc.Sem.loadSyms Λ secs.rodata)).exe).label Scc.Lower.Names.releaseSite).toBitVec.toNat :=
  ⟨site_eq (H := H) (E := E) hpa hl wake_siteLabels.1, site_eq (H := H) (E := E) hpa hl wake_siteLabels.2⟩

/-! ## The child's entry in the fragment -/

/-- **The child after the handover is `WideX exe`** when its parent is: the
handover changes the machine state only (`A64Handover.child_st`). -/
theorem wideX_childAfter {x : Scc.Sem.Kernel.KState} {tid : Nat} {th : Thread isaLSE2} {stack tls : Nat}
    (h : WideX exe th.st) : WideX exe (Spike.Lib.Handover.childAfter Scc.Sem.A64.abi x tid th stack tls).st := by
  obtain ⟨m, hc, -⟩ := Spike.Lib.A64Handover.child_st (x := x) (tid := tid) (t := th) (stack := stack) (tls := tls)
  rw [hc]; exact h

/-- A state at a fragment executable `exe` with no declarations is `WideX exe`. -/
theorem wideX_of {st : State} (hw : Scc.Cert.WideA64.ExeWide exe) (he : st.exe = exe) (hd : st.decls = {}) :
    WideX exe st :=
  ⟨⟨hd ▸ Scc.Cert.WideA64.declsWide_empty, he ▸ hw⟩, he⟩

/-- **wake's listing is in the fragment.** -/
theorem wake_wideIn : Scc.Cert.WideA64.wideIn wakeProg = true := by decide +kernel

/-- **The canonical thread's executable of wake's listing is in the
fragment** (`wideSt_threadAt`). -/
theorem wake_exeWide (E : Scc.Sem.Entry) (base : Nat) (syms : List (String × Nat)) :
    Scc.Cert.WideA64.ExeWide (Scc.Sem.A64.threadAt E base wakeProg syms).exe :=
  (Scc.Cert.WideA64.wideSt_threadAt wake_wideIn E base syms).2

/-- **The spawned child's entry is `WideX exe`** (`side_entry`'s `hW` for
`seg_childPreNN`'s child): from the clone's precondition with `hX` (as
`seg_childPreNN`) and a fragment executable `hw` (`wake_exeWide`). -/
theorem clonePre_childWide {pfx : String} {Λ : Scc.Sem.Layout} {r0 r1 : Scc.Sem.Range} {X : State → Prop}
    {lbl : WeakMem.AllocLabel → Option Nat} {t : Spike.Lib.WakeA64.Cfg} {s : TermRun.Cfg}
    (h : Spike.Lib.WakePreA.ClonePre pfx Λ r0 r1 X lbl t s)
    (hX : ∀ st, X st → st.exe = exe ∧ st.endPc = endPc ∧ st.decls = {})
    (hw : Scc.Cert.WideA64.ExeWide exe) :
    ∃ th : Thread isaLSE2, t.1.threads = #[th] ∧
      ∀ tid stack tls, WideX exe (Spike.Lib.Handover.childAfter Scc.Sem.A64.abi t.2 tid th stack tls).st := by
  obtain ⟨th, -, -, -, -, -, hth, -, -, -, -, -, -, -, -, -, -, -, -, -, hXs, -⟩ := h
  obtain ⟨he, -, hd⟩ := hX _ hXs
  exact ⟨th, hth, fun _ _ _ => wideX_childAfter (wideX_of hw he hd)⟩

end Spike.Lib.WakeW1.WorkerSide
