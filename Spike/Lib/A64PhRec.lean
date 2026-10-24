/-
**The phase record of an AArch64 output** (`Spike/Lib/Rt/A64RtW.lean`'s
`InstOk` and the runtime's phase facts from the runtime's layout): every
field a function of the runtime's layout `L` (`RuntimeLayout`), so no data
beyond the placement check's.

- **The phases and sites** (`ph`, `okPc`): A6's `Rt.A64.phOf` and
  `Rt.A64.okPcOf` of the program at the code base.
- **The marks** (`μ`): each transfer site at its fixed label, each abort
  site at its layout's label, resolved in the program at the code base; the
  canonical target's marks of a text parsing to the program
  (`marks_eq`).
- **The owned words and the take's phase** (`ownOf`, `own`, `Tk`): `ret0`'s
  hand ones (`Spike/Lib/A64Ret0I.lean`) over the layout's counters, by the
  four bits of the phase index.
- **The outside move** (`K`): the take at the take site's label.
- **The instance's facts** (`instOk`): the layout, the labels, `same` and
  `off` (a pc off the sites is off `μ`'s, with no take there, given the
  take site at its label, `hsite`).
- **From the placement check** (`site_ofPlaceOK`, `instOk_ofPlaceOK`): at
  `RuntimeLayout.ofPlaceOK`, the take site at its label (A6 resolves it; the
  code's end below `2 ^ 64`, `codeEnd_lt`, from A1/A2/A8).
- **Oracle**: at `ret0`'s layout the phases, the sites and the owned words
  are the hand ones (`Spike/Test/A64PhRec.lean`).
-/
import Spike.Lib.Rt.A64RtW
import Spike.Lib.Rt.A64Layout
import Spike.Lib.Rt.A64LayoutOfPlaceOK
import Scc.Sem.LoadA64
import Scc.Cert.Rt.PhasesA64

namespace Spike.Lib.A64.PhRec

open Kraken Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem (Marks Range)
open Scc.Sem.A64 (pcOf)
open Spike.Lib.A64Consumer
open Spike.Lib.A64.Rt (RuntimeLayout InstOk)
open Spike.Lib.A64.Flow.Ret0 (TakeK)
open Scc.Cert.Link.A64 (codeOf)

/-! ## The sites -/

/-- **A value of a mapped list**: `f x` is in `l.mapM f` for `x ∈ l`. -/
theorem mem_of_mapM {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {ss : List β}, l.mapM f = some ss → ∀ x ∈ l, ∀ b, f x = some b → b ∈ ss
  | [], _, _, x, hx, _, _ => by cases hx
  | y :: ys, ss, h, x, hx, b, hb => by
    rw [List.mapM_cons] at h
    cases hy : f y with
    | none => rw [hy] at h; cases h
    | some c =>
      cases hys : ys.mapM f with
      | none => rw [hy, hys] at h; cases h
      | some cs =>
        rw [hy, hys] at h
        cases h
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [hy] at hb; cases hb; exact List.mem_cons_self ..
        · exact List.mem_cons_of_mem _ (mem_of_mapM hys x hx b hb)

/-- **A site label's address is a site** of the program. -/
theorem site_mem {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {ss : List Nat}
    (hs : Scc.Cert.Rt.A64.sitesOf lo prog Λ = some ss) {l : String} (hl : l ∈ Scc.Cert.Rt.A64.siteLabels Λ)
    {a : Nat} (ha : codeOf lo prog l = some a) : a ∈ ss :=
  mem_of_mapM hs l hl a ha

/-- **A pc off the sites** is none of the sites' label addresses. -/
theorem ne_of_okPcOf {lo : Nat} {prog : Program} {Λ : Scc.Sem.Layout} {pc : Nat}
    (h : Scc.Cert.Rt.A64.okPcOf lo prog Λ pc = true) {l : String} (hl : l ∈ Scc.Cert.Rt.A64.siteLabels Λ)
    {a : Nat} (ha : codeOf lo prog l = some a) : pc ≠ a := by
  unfold Scc.Cert.Rt.A64.okPcOf at h
  split at h
  · next ss hs =>
    rintro rfl
    have hm := site_mem hs hl ha
    simp only [Bool.not_eq_true', List.contains_eq_any_beq, List.any_eq_false, beq_iff_eq] at h
    exact h _ hm rfl
  · cases h

section Rec

variable (L : RuntimeLayout)

/-! ## The record -/

/-- **The phase index of a pc** (A6's `phOf`). -/
def ph : Nat → Nat := Scc.Cert.Rt.A64.phOf L.Λ.code.lo L.prog

/-- **The pcs off the sites** (A6's `okPcOf`). -/
def okPc : Nat → Bool := Scc.Cert.Rt.A64.okPcOf L.Λ.code.lo L.prog L.Λ

/-- **The program's marks**: the transfer sites at their fixed labels, the
abort sites at the layout's labels, resolved in the program. -/
def μ : Marks where
  site k := codeOf L.Λ.code.lo L.prog k.label
  abortAt k := codeOf L.Λ.code.lo L.prog (L.Λ.abortLbl k)

/-- **The owned words at a phase index**: the four counters
`scc_rt_pinned_next`, `scc_rt_stack_lock`, `scc_rt_stack_free_n`,
`scc_rt_stack_next` with their values by the index's bits. -/
def ownOf (i : Nat) : List (Loc × Val) :=
  [(⟨L.pnA, 8⟩, (if i % 2 = 1 then 0#64 else Spike.Lib.A64.Flow.Ret0.AllocTcb.tcbLen).setWidth 128),
    (⟨L.lockA, 8⟩, (if i / 2 % 2 = 1 then 1#64 else 0#64).setWidth 128),
    (⟨L.freeNA, 8⟩, (0#64).setWidth 128),
    (⟨L.nextA, 8⟩, (if i / 4 % 2 = 1 then 0#64 else Spike.Lib.A64.Flow.Ret0.StackTake.size0).setWidth 128)]

/-- **The words a state owns**, by its pc's phase. -/
def own (s : State) : List (Loc × Val) := ownOf L (ph L (pcOf s))

/-- **The take's phase**: past the take site. -/
def Tk (s : State) : Prop := ph L (pcOf s) / 8 % 2 = 0

/-- **The outside move**: the take at the take site's label. -/
abbrev K (rS : Range) : State → State → Prop := TakeK (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL) rS

/-! ## The instance's facts -/

/-- The owned words and the take's phase factor through `ph` of the pc. -/
theorem same : ∀ s s' : State, ph L (pcOf s') = ph L (pcOf s) → own L s' = own L s ∧ (Tk L s' ↔ Tk L s) := by
  intro s s' h
  unfold own Tk
  rw [h]
  exact ⟨rfl, Iff.rfl⟩

/-- **A pc off the sites** is off the marks' sites, with no take there,
given the take site at its label (`hsite`). -/
theorem off {rS : Range}
    (hsite : (μ L).site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    ∀ s : State, okPc L (pcOf s) = true → PcOff (μ L) s ∧ ∀ s', ¬ K L rS s s' := by
  intro s h
  have hp : PcOff (μ L) s :=
    ⟨fun a ha => ne_of_okPcOf h (by simp [Scc.Cert.Rt.A64.siteLabels, Scc.Sem.XferKind.label]) ha,
      fun a ha => ne_of_okPcOf h (by simp [Scc.Cert.Rt.A64.siteLabels, Scc.Sem.XferKind.label]) ha,
      fun k a ha => ne_of_okPcOf h (by cases k <;> simp [Scc.Cert.Rt.A64.siteLabels]) ha⟩
  exact ⟨hp, hp.not_take hsite⟩

/-- **The instance's facts of the record**: the layout's executable, end
and labels, `same` and `off`. -/
theorem instOk {rS : Range}
    (hsite : (μ L).site .take = some (L.lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat) :
    InstOk L.exe L.endPc L.prog L.lab (μ L) (own L) (Tk L) (K L rS) (okPc L) (ph L) L.pfx :=
  ⟨L.lays, rfl, rfl, same L, off L hsite⟩

/-- **The canonical target's marks** of a text parsing to the layout's
program (`hpa`, the loader's parse) are the record's. -/
theorem marks_eq {asm : String} (hpa : Scc.Sem.A64.textProgram asm = .ok L.prog) :
    Scc.Sem.Target.marks (Scc.Sem.A64.canonical 1) asm L.Λ = μ L := by
  have hr := Scc.Sem.A64.resolve_of_parsed (Scc.Sem.A64.kernel 1) Scc.Sem.Entry.linux L.Λ hpa
  unfold Scc.Sem.Target.marks μ
  congr 1
  · funext k; exact hr _
  · funext k; exact hr _

/-! ## The frame condition's words -/

variable {L}

/-- `scc_rt_pinned_next` is unmapped under the entry frame condition. -/
theorem rtF_pn {m : MachineData} (h : Spike.Lib.A64.Rt.rtF L m) : Mem.loadInt m.dmem L.pnA 8 = none := h _ L.pn_mem

/-- `scc_rt_stack_lock` is unmapped under the entry frame condition. -/
theorem rtF_lock {m : MachineData} (h : Spike.Lib.A64.Rt.rtF L m) : Mem.loadInt m.dmem L.lockA 8 = none :=
  h _ L.lock_mem

/-- `scc_rt_stack_free_n` is unmapped under the entry frame condition. -/
theorem rtF_freeN {m : MachineData} (h : Spike.Lib.A64.Rt.rtF L m) : Mem.loadInt m.dmem L.freeNA 8 = none :=
  h _ L.freeN_mem

/-- `scc_rt_stack_next` is unmapped under the entry frame condition. -/
theorem rtF_next {m : MachineData} (h : Spike.Lib.A64.Rt.rtF L m) : Mem.loadInt m.dmem L.nextA 8 = none :=
  h _ L.next_mem

/-- The first TCB's header (`n0 = 0`) is unmapped under the entry frame
condition. -/
theorem rtF_hdr0 {m : MachineData} (h : Spike.Lib.A64.Rt.rtF L m) :
    Mem.loadInt m.dmem (L.pinA + 0#64) 8 = none := by
  rw [BitVec.add_zero]; exact h _ L.pin_mem

/-! ## The first TCB's words

The first TCB's header `pinA` and its six fields `pinA + 8 (j + 1)` are
words of `rtWords`: mapped for writing, unmapped under the entry frame
condition. They are owned at no phase when they are none of the four
counters (`TcbSep`, a separation the record's layout does not state). -/

/-- **The first TCB's words are off the counters.** -/
def TcbSep (L : RuntimeLayout) : Prop :=
  ∀ j < 7, L.pinA + BitVec.ofNat 64 (8 * j) ∉ [L.pnA, L.lockA, L.freeNA, L.nextA]

/-- A word of the first TCB: its header or one of its six fields. -/
theorem tcb_mem {a : BitVec 64} (ha : ∃ j < 7, a = L.pinA + BitVec.ofNat 64 (8 * j)) : a ∈ L.rtWords := by
  obtain ⟨j, hj, rfl⟩ := ha
  cases j with
  | zero => simpa using L.pin_mem
  | succ j => exact L.fld_mem (by omega)

/-- **A TCB word is unmapped** under the entry frame condition. -/
theorem rtF_tcb {m : MachineData} (h : Spike.Lib.A64.Rt.rtF L m) {a : BitVec 64}
    (ha : ∃ j < 7, a = L.pinA + BitVec.ofNat 64 (8 * j)) : Mem.loadInt m.dmem a 8 = none :=
  h _ (tcb_mem ha)

/-- **A TCB word is mapped for writing** in the loaded kernel state. -/
theorem mapped_tcb {a : BitVec 64} (ha : ∃ j < 7, a = L.pinA + BitVec.ofNat 64 (8 * j)) :
    Scc.Sem.Kernel.mapped (K0 L.Λ) true ⟨a, 8⟩ = true :=
  (L.words_mapped a (tcb_mem ha)).1

/-- **A TCB word is owned at no phase**, the TCB off the counters. -/
theorem tcb_not_own (hs : TcbSep L) {a : BitVec 64} (ha : ∃ j < 7, a = L.pinA + BitVec.ofNat 64 (8 * j)) :
    ∀ i w, (⟨a, 8⟩, w) ∉ ownOf L i := by
  obtain ⟨j, hj, rfl⟩ := ha
  intro i w hm
  apply hs j hj
  simp only [ownOf, List.mem_cons, Prod.mk.injEq, Loc.mk.injEq, List.not_mem_nil, or_false] at hm
  rcases hm with ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ | ⟨⟨h, -⟩, -⟩ <;> simp [h]

end Rec

/-! ## The take site at its label, from the placement check

A code label's address is below the code's end (`le_codeEnd_of_codeOf`),
which every data symbol the loader places lies above (`symsOk`); a runtime
word's symbol lies in a region of the link or in `.rodata`, both in the
address space, so the code's end is in it (`codeEnd_lt`), and the take
site's label is its `codeOf` address unwrapped. -/

section Place

open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Scc.Cert.Link.A64 (linkOf)

/-- A code label's address is at most the code's end. -/
theorem le_codeEnd_of_codeOf {l : String} : ∀ {base : Nat} {prog : Program} {a : Nat},
    codeOf base prog l = some a → a ≤ Scc.Sem.A64.codeEnd base prog
  | _, [], _, h => by cases h
  | base, d :: ds, a, h => by
    simp only [codeOf, Scc.Sem.labelAddr] at h
    split at h
    · cases h; simp [Scc.Sem.A64.codeEnd]
    · have := le_codeEnd_of_codeOf (l := l) (base := base + d.fakeSize) (prog := ds) h
      simp only [Scc.Sem.A64.codeEnd, List.map_cons, List.sum_cons] at this ⊢
      omega

/-- A data label's address is at most the section's end. -/
theorem le_endAddr_of_labelsFrom {l : String} {a : Nat} (items : List Kraken.DataImage.Item) : ∀ {cur : Nat},
    (l, a) ∈ Kraken.DataImage.labelsFrom cur items → a ≤ Kraken.DataImage.endAddr cur items := by
  induction items with
  | nil => intro _ h; cases h
  | cons it is ih =>
    intro cur h
    cases it with
    | label l' =>
      simp only [Kraken.DataImage.labelsFrom, List.mem_cons, Prod.mk.injEq] at h
      have he : Kraken.DataImage.endAddr cur (.label l' :: is) = Kraken.DataImage.endAddr cur is := by
        simp [Kraken.DataImage.endAddr, Kraken.DataImage.addrAt, Kraken.DataImage.size]
      rw [he]
      rcases h with ⟨-, rfl⟩ | h
      · exact Kraken.DataImage.le_addrAt _ _ _
      · exact ih h
    | _ =>
      simp only [Kraken.DataImage.labelsFrom] at h
      have := ih h
      simpa [Kraken.DataImage.endAddr, Kraken.DataImage.addrAt] using this

/-- **A placed symbol is in the address space**: a symbol of the link (in
a region, `WF`) or of `.rodata` (in the image, `rodataFits`). -/
theorem sym_le {Λ : Scc.Sem.Layout} {ro : List Kraken.DataImage.Item} (hwf : Λ.WF)
    (hro : Scc.Sem.rodataFits Λ ro = true) {p : String × Nat} (hp : p ∈ Scc.Sem.loadSyms Λ ro) :
    p.2 ≤ 2 ^ 64 := by
  rcases List.mem_append.mp hp with hp | hp
  · have hin := hwf.symIn p (List.mem_filter.mp hp).1
    have hsp : ∀ r ∈ Λ.regions, r.contains p.2 → p.2 ≤ 2 ^ 64 := fun r hr hc => by
      have := (hwf.inSpace r hr).2; simp only [Scc.Sem.Range.contains] at hc; omega
    rcases hin with h | h | h | h
    · exact hsp _ (by simp [Scc.Sem.Layout.regions]) h
    · exact hsp _ (by simp [Scc.Sem.Layout.regions]) h
    · exact hsp _ (by simp [Scc.Sem.Layout.regions]) h
    · exact hsp _ (by simp [Scc.Sem.Layout.regions]) h
  · have hle := le_endAddr_of_labelsFrom (l := p.1) (a := p.2) ro hp
    have hne : ro.isEmpty = false := by
      cases ro with
      | nil => simp [Scc.Sem.rodataSyms, Kraken.DataImage.labelsFrom] at hp
      | cons _ _ => rfl
    simp only [Scc.Sem.rodataFits, hne, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq] at hro
    omega

variable {pcfg : Scc.Cert.PlaceOK.Config} {o : Scc.Cert.PlaceOK.A64.Out} {Λ : Scc.Sem.Layout}
    (h : placeOKAt pcfg Λ o = true)
  (i : CoreTerm.Expr → String → Nat → Option Nat)
include h

/-- **The code's end is in the address space** of an output passing
`placeOK`. -/
theorem codeEnd_lt : Scc.Sem.A64.codeEnd (RuntimeLayout.ofPlaceOK h i).Λ.code.lo o.prog < 2 ^ 64 :=
  Scc.Cert.Link.A64.codeEnd_lt_of_loadOk (loadOk_link_of_placeOKAt i h)

/-- **The take site at its label** in the loaded thread of an output
passing `placeOK`. -/
theorem site_ofPlaceOK :
    (μ (RuntimeLayout.ofPlaceOK h i)).site .take =
      some ((RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL).toBitVec.toNat := by
  have h6 := phasesOk_of_placeOKAt h
  unfold Scc.Cert.Rt.A64.phasesOk Scc.Cert.Rt.A64.phasesOkBy at h6
  rw [Scc.Cert.Rt.A64.codeT_eq] at h6
  split at h6
  · next T ss hT hs =>
    have hl : "scc_rt_take_site" ∈ Scc.Cert.Rt.A64.siteLabels Λ := by
      simp [Scc.Cert.Rt.A64.siteLabels]
    obtain ⟨a, ha⟩ : ∃ a, codeOf Λ.code.lo o.prog "scc_rt_take_site" = some a := by
      unfold Scc.Cert.Rt.A64.sitesBy at hs
      have : ∀ {l : List String} {ss : List Nat}, l.mapM (codeOf Λ.code.lo o.prog) = some ss →
          ∀ x ∈ l, ∃ a, codeOf Λ.code.lo o.prog x = some a := by
        intro l
        induction l with
        | nil => intro _ _ x hx; cases hx
        | cons y ys ih =>
          intro ss hm x hx
          rw [List.mapM_cons] at hm
          cases hy : codeOf Λ.code.lo o.prog y with
          | none => rw [hy] at hm; cases hm
          | some c =>
            cases hys : ys.mapM (codeOf Λ.code.lo o.prog) with
            | none => rw [hy, hys] at hm; cases hm
            | some cs =>
              rcases List.mem_cons.mp hx with rfl | hx
              · exact ⟨c, hy⟩
              · exact ih hys x hx
      exact this hs _ hl
    have hlab := Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
      (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha
    have hlt : a < 2 ^ 64 :=
      Nat.lt_of_le_of_lt (le_codeEnd_of_codeOf ha) (codeEnd_lt h i)
    show codeOf Λ.code.lo o.prog "scc_rt_take_site" = _
    rw [ha]
    have hlab' : (RuntimeLayout.ofPlaceOK h i).lab Spike.Lib.A64.Flow.Ret0.StackTake.siteL = Int64.ofNat a := hlab
    rw [hlab']
    simp [Nat.mod_eq_of_lt hlt]
  · cases h6

/-- **The overflow abort path's phase check** at the record's
`okPc`/`ph` and labels of an output passing `placeOK` (A7's `abortPhC`, every
label it reads at its `codeOf` address in the loaded thread). -/
theorem abortPhOk_ofPlaceOK :
    Spike.Lib.A64.StubW.abortPhOk (okPc (RuntimeLayout.ofPlaceOK h i)) (ph (RuntimeLayout.ofPlaceOK h i))
      (RuntimeLayout.ofPlaceOK h i).lab = true :=
  Spike.Lib.A64.StubW.abortPhOk_of_abortPhC (abortPh_of_placeOKAt h) fun _ _ ha =>
    Scc.Cert.Rt.A64.label_threadAt_of_codeOf_below (E := Scc.Sem.Entry.linux)
      (syms := Scc.Sem.loadSyms (RuntimeLayout.ofPlaceOK h i).Λ o.secs.rodata)
      (Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK_below h i ha) ha

/-- **The record's instance's facts** of an output passing `placeOK`. -/
theorem instOk_ofPlaceOK {rS : Range} :
    InstOk (RuntimeLayout.ofPlaceOK h i).exe (RuntimeLayout.ofPlaceOK h i).endPc o.prog
      (RuntimeLayout.ofPlaceOK h i).lab (μ (RuntimeLayout.ofPlaceOK h i)) (own (RuntimeLayout.ofPlaceOK h i))
      (Tk (RuntimeLayout.ofPlaceOK h i)) (K (RuntimeLayout.ofPlaceOK h i) rS) (okPc (RuntimeLayout.ofPlaceOK h i))
      (ph (RuntimeLayout.ofPlaceOK h i)) (RuntimeLayout.ofPlaceOK h i).pfx :=
  instOk _ (site_ofPlaceOK h i)

end Place

end Spike.Lib.A64.PhRec
