/-
**hello.w on AArch64: the record at the clone** (`HelloHPre.hpre_ofH`'s
`hrec` at hello's root records `ι := {g : Gh // HelloOkHR.okHR Λ lB g}`,
`SR w := WakeInst.wakeSR w.1`): the record is `WakeOkW.recW` at the
spawn's own placement and `c`'s label (`HelloOkHR.okHR_recW`, as wake's
`WakeWorkerR.ghOK_of_clone`), so no family-wide placement or flag enters
the record's type.

- `hrec_okHR`: `hrec` from the instance's field choices (`cS`, `cT`, the
  pointer words, the buffer's label and lengths the record's or the
  instance's constants), the data's guarantee below every record's
  (`hG`), the layout well formed, and `hpin`: at main's source thread at
  the spawn under `VBufR`, the slice's buffer label is `lB` and is not
  `c`'s label (`HelloNewBuf.rodata_newBuf_label` with `lB := lBH`, and
  `lBH_ne_box`).
- `hrec_okHRc`: `hrec_okHR` at `lB := HelloOkW.lBH`, `hpin` discharged by
  `HelloNewBuf.rodata_newBuf_label` and `lBH_ne_box`.
-/
import Spike.Lib.HelloHPre
import Spike.Lib.HelloOkHR
import Spike.Lib.HelloNewBuf

namespace Spike.Lib.HelloRec

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64 Scc.Sem Scc.Sem.A64 Scc.Sem.Kernel
open Spike.Lib Spike.Lib.WakeA64 Spike.Lib.Inv2Core Spike.Lib.WakeInst Spike.Lib.WakeOkW
open Spike.Lib.HelloW1 (WSideH)
open Spike.Lib.HelloO (ODataH)
open Spike.Lib.HelloMainPreSrc (SpawnSrcH)
open Spike.Lib.HelloOkHR (okHR okHR_recW)

/-- **`hpre_ofH`'s `hrec` at hello's root records** (see the module
doc). The record's park permit word is `pT0`. -/
theorem hrec_okHR {Λ : Scc.Sem.Layout} {lB : WeakMem.AllocLabel} {Dd : ODataH}
    {SR : {g : Gh // okHR Λ lB g} → SpawnRec} {cT : {g : Gh // okHR Λ lB g} → Loc}
    {cS : {g : Gh // okHR Λ lB g} → WeakMem.Address} {G : {g : Gh // okHR Λ lB g} → Loc → Val → Prop}
    {M : WakeM0.MSide {g : Gh // okHR Λ lB g}} {D : WSideH {g : Gh // okHR Λ lB g}} (pT0 : Loc)
    /- (the instance's field choices) -/
    (hSR : ∀ w, SR w = wakeSR w.1) (hcS : ∀ w, cS w = w.1.cS) (hcT : ∀ w, cT w = w.1.cT)
    (hDcw : ∀ w, D.cw w = w.1.cwW) (hMcw : ∀ w, M.cw w = w.1.cwM)
    (hbL : ∀ w, D.bufL w = lB) (hmB : ∀ w, D.mB w = 2) (hnB : ∀ w, D.nB w = 13)
    /- (the instance) the data's guarantee is below every record's -/
    (hG : ∀ w m, MemInv Dd.G m → MemInv (G w) m)
    (hwf : Λ.WF)
    /- (row 4c, `HelloNewBuf.rodata_newBuf_label` / `lBH_ne_box`) the slice's
    buffer label is `lB`, off `c`'s -/
    (hpin : ∀ (s : TermRun.Cfg) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (l lb : WeakMem.AllocLabel)
      (ws : List TermRun.Word), HelloVBuf.VBufR s → s.ths = #[th0] → SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ →
      ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0)) → lb = lB ∧ lB ≠ l) :
    ∀ (d : Cfg) (s' : TermRun.Cfg) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (l lb : WeakMem.AllocLabel) (cw : TermRun.Word),
      cw.val = .loc ⟨l, 0⟩ 0 → MemInv Dd.G d.1.mem →
      (∃ ts, MemRelP Λ lbl lsize ts d.1.mem s'.mem [] [] []) → (∃ cA, ValRep lbl (.loc ⟨l, 0⟩ 0) cA) →
      0 < lsize l → 0 < s'.mem.size → (∃ b0, lbl lb = some b0) → 2 ≤ lsize lb →
      (∃ (s : TermRun.Cfg) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (ws : List TermRun.Word),
        HelloVBuf.VBufR s ∧ s.ths = #[th0] ∧ SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧
        ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0))) →
      ∃ w : {g : Gh // okHR Λ lB g}, SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ ∧ cS w = ⟨l, 0⟩ ∧
        cT w = wordLoc ((lbl l).getD 0 + 8 * 0) ∧ D.cw w = cw ∧ M.cw w = TermRun.cst (.loc ⟨l, 0⟩ 0) ∧
        D.bufL w = lb ∧ D.mB w = 2 ∧ D.nB w = 13 ∧ MemInv (G w) d.1.mem ∧ lb ≠ l := by
  intro d s' lbl lsize l lb cw hcw hMI ⟨ts, hm⟩ ⟨cA, hv⟩ hin hS ⟨b0, hb⟩ hlb2 ⟨s, th0, hd, ws, hVB, hs, hSS, hh⟩
  obtain ⟨hlb, hne⟩ := hpin s th0 hd l lb ws hVB hs hSS hh
  subst hlb
  let w : {g : Gh // okHR Λ lb g} :=
    ⟨recW d.1.mem.last s'.mem.size lbl lsize l pT0 cw, okHR_recW hm hwf hv hcw hin hS ⟨hb, hlb2, hne⟩⟩
  exact ⟨w, by rw [hSR]; rfl, by rw [hcS]; rfl, by rw [hcT]; rfl, by rw [hDcw]; rfl, by rw [hMcw]; rfl,
    hbL w, hmB w, hnB w, hG w _ hMI, hne⟩

/-- **`hrec_okHR` at rodata's buffer label `lBH`**, `hpin` from row 4c
(`HelloNewBuf.rodata_newBuf_label`, `lBH_ne_box`). -/
theorem hrec_okHRc {Λ : Scc.Sem.Layout} {Dd : ODataH}
    {SR : {g : Gh // okHR Λ HelloOkW.lBH g} → SpawnRec} {cT : {g : Gh // okHR Λ HelloOkW.lBH g} → Loc}
    {cS : {g : Gh // okHR Λ HelloOkW.lBH g} → WeakMem.Address}
    {G : {g : Gh // okHR Λ HelloOkW.lBH g} → Loc → Val → Prop}
    {M : WakeM0.MSide {g : Gh // okHR Λ HelloOkW.lBH g}} {D : WSideH {g : Gh // okHR Λ HelloOkW.lBH g}}
    (pT0 : Loc)
    (hSR : ∀ w, SR w = wakeSR w.1) (hcS : ∀ w, cS w = w.1.cS) (hcT : ∀ w, cT w = w.1.cT)
    (hDcw : ∀ w, D.cw w = w.1.cwW) (hMcw : ∀ w, M.cw w = w.1.cwM)
    (hbL : ∀ w, D.bufL w = HelloOkW.lBH) (hmB : ∀ w, D.mB w = 2) (hnB : ∀ w, D.nB w = 13)
    (hG : ∀ w m, MemInv Dd.G m → MemInv (G w) m) (hwf : Λ.WF) :
    ∀ (d : Cfg) (s' : TermRun.Cfg) (lbl : WeakMem.AllocLabel → Option Nat)
      (lsize : WeakMem.AllocLabel → Nat) (l lb : WeakMem.AllocLabel) (cw : TermRun.Word),
      cw.val = .loc ⟨l, 0⟩ 0 → MemInv Dd.G d.1.mem →
      (∃ ts, MemRelP Λ lbl lsize ts d.1.mem s'.mem [] [] []) → (∃ cA, ValRep lbl (.loc ⟨l, 0⟩ 0) cA) →
      0 < lsize l → 0 < s'.mem.size → (∃ b0, lbl lb = some b0) → 2 ≤ lsize lb →
      (∃ (s : TermRun.Cfg) (th0 : TermRun.TTh) (hd : Option (Nat × TermRun.Word)) (ws : List TermRun.Word),
        HelloVBuf.VBufR s ∧ s.ths = #[th0] ∧ SpawnSrcH l ws ⟨th0.term, th0.env, hd⟩ ∧
        ws.head? = some (TermRun.cst (.loc ⟨lb, 0⟩ 0))) →
      ∃ w : {g : Gh // okHR Λ HelloOkW.lBH g}, SR w = ⟨d.1.mem.last, s'.mem.size, lbl, lsize⟩ ∧
        cS w = ⟨l, 0⟩ ∧ cT w = wordLoc ((lbl l).getD 0 + 8 * 0) ∧ D.cw w = cw ∧
        M.cw w = TermRun.cst (.loc ⟨l, 0⟩ 0) ∧ D.bufL w = lb ∧ D.mB w = 2 ∧ D.nB w = 13 ∧
        MemInv (G w) d.1.mem ∧ lb ≠ l :=
  hrec_okHR pT0 hSR hcS hcT hDcw hMcw hbL hmB hnB hG hwf fun _ _ _ _ _ _ hv hs hS hh =>
    let ⟨h1, h2⟩ := HelloNewBuf.rodata_newBuf_label hv hs hS hh
    ⟨h1, h2 ▸ HelloNewBuf.lBH_ne_box⟩

end Spike.Lib.HelloRec

/-- info: 'Spike.Lib.HelloRec.hrec_okHR' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRec.hrec_okHR

/-- info: 'Spike.Lib.HelloRec.hrec_okHRc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.HelloRec.hrec_okHRc
