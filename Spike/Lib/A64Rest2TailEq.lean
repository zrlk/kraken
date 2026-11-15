/-
**The agreements `rest2A_tail` asks for, from the text** (the AArch64
outputs before and after a post-pass appends a tail to the text, with the
same data sections): the code labels off the labels `B` (the end label
`te` and the tail's) agree, hence the marks, the runtime's words, `me`'s
word, the value invariant and the owned words.

- `codeOf_tail`: the code labels off `B` of `P` followed by the tail `T`
  are those of `P` closed by `te`;
- `marks_tail`, `rtA_tail`, `meW2_tail`, `G2_tail`, `own2_tail`: the
  premises of `rest2A_tail` other than `TailOK`, from code labels agreeing
  off `B`;
- `rest2A_tail_text`: `Rest2A` from the text closed by `te` to the text
  with the tail.
-/
import Spike.Lib.A64Rest2Tail
import Spike.Lib.A64TextTail

namespace Spike.Lib.A64Rest2Tail

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.AArch64
open Scc.Sem Scc.Sem.A64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.A64
open Spike.Lib.A64ConsumerS (OwnS)
open Spike.Lib.LowerA64 (Rest2A G2 own2 meW2 asm2)
open Spike.Lib.A64RestTail (relab)
open Scc.Cert.Link.A64 (codeOf)
open Scc.Cert.Rt.A64 (PhRange phTabBy phOf rtA rtNames bPR bLR bNR bTR)

/-! ## Code labels -/

/-- A text whose labels are all in `B` has no code label off `B`. -/
theorem codeOf_none_of_labels {B : List _root_.Label} {l : String} (hl : l ∉ B) :
    ∀ {Q : Program}, (∀ d ∈ Q, ∀ l', d = .label l' → l' ∈ B) → ∀ b, codeOf b Q l = none
  | [], _, _ => rfl
  | d :: Q, hQ, b => by
    have hd : labelName d ≠ some l := by
      intro he
      cases d <;> simp only [labelName, reduceCtorEq, Option.some.injEq] at he
      subst he
      exact hl (hQ _ (List.mem_cons_self ..) _ rfl)
    show (if labelName d = some l then some b else codeOf (b + d.fakeSize) Q l) = none
    split
    · exact absurd ‹_› hd
    exact codeOf_none_of_labels hl (fun d' hd' => hQ d' (List.mem_cons_of_mem d hd')) _

/-- **The code labels off `B` with the tail are those of the text closed by
its end label**, every label of the tail `T` and the end label `te` in
`B`. -/
theorem codeOf_tail {lo : Nat} {P T : Program} {te : _root_.Label} {B : List _root_.Label}
    (hte : te ∈ B) (hT : ∀ d ∈ T, ∀ l, d = .label l → l ∈ B) :
    ∀ l, l ∉ B → codeOf lo (P ++ T) l = codeOf lo (P ++ [.label te]) l := by
  intro l hl
  cases h : codeOf lo P l with
  | some a => rw [A64TextTail.codeOf_append_of T h, A64TextTail.codeOf_append_of _ h]
  | none =>
    rw [A64TextTail.codeOf_append_none T h, A64TextTail.codeOf_append_none _ h,
      codeOf_none_of_labels hl hT, codeOf_none_of_labels hl _]
    intro d hd l' he
    rw [List.mem_singleton.mp hd] at he
    cases he
    exact hte

variable {pcfg : Scc.Cert.PlaceOK.Config} {Λ : Scc.Sem.Layout} {oE oF : Scc.Cert.PlaceOK.A64.Out}
  {B : List _root_.Label} {p : Prog}

/-! ## The premises of `rest2A_tail` -/

/-- **The marks agree**, the transfer sites and abort stubs off `B`. -/
theorem marks_tail {E : Entry}
    (hc : ∀ l, l ∉ B → codeOf Λ.code.lo oF.prog l = codeOf Λ.code.lo oE.prog l)
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) :
    (Spike.Lib.A64Consumer.TParE E).marks (asm2 oF) Λ = (Spike.Lib.A64Consumer.TParE E).marks (asm2 oE) Λ := by
  show ({ site := fun k => codeOf Λ.code.lo oF.prog k.label
          abortAt := fun k => codeOf Λ.code.lo oF.prog (Λ.abortLbl k) } : Marks) =
    { site := fun k => codeOf Λ.code.lo oE.prog k.label
      abortAt := fun k => codeOf Λ.code.lo oE.prog (Λ.abortLbl k) }
  congr 1
  · funext k; exact hc _ (hs k)
  · funext k; exact hc _ (ha k)

/-- **A runtime word's address agrees**, its name off `B`. -/
theorem rtA_tail (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeOf Λ.code.lo oF.prog l = codeOf Λ.code.lo oE.prog l) {x : String} (hx : x ∉ B) :
    rtA Λ oF.prog oF.secs x = rtA Λ oE.prog oE.secs x := by
  unfold rtA Scc.Cert.Rt.A64.symLab
  rw [hsecs, hc x hx]

/-- **`me`'s word agrees**, `scc_rt_pinned` off `B`. -/
theorem meW2_tail (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeOf Λ.code.lo oF.prog l = codeOf Λ.code.lo oE.prog l)
    (hpin : "scc_rt_pinned" ∉ B) : meW2 Λ oF = meW2 Λ oE := by
  unfold meW2
  rw [rtA_tail hsecs hc hpin]

/-- The layout of the lowering's immediates. -/
private abbrev Λi (Λ : Scc.Sem.Layout) (p : Prog) : Scc.Sem.Layout := { Λ with imms := LowerNode.imms2Me Λ p }

/-- **The value invariant, explicitly**: at the first TCB's limit word, the
limit or `0` (the word's initial value, `rtInit_of_placeOKAt`). -/
theorem G2_iff {o : Scc.Cert.PlaceOK.A64.Out} (h : placeOKAt pcfg Λ o = true) (l : Loc) (v : Val) :
    G2 h p l v ↔ (l = ⟨rtA (Λi Λ p) o.prog o.secs "scc_rt_pinned" + 16#64, 8⟩ →
      v = (rtA (Λi Λ p) o.prog o.secs "scc_rt_stacks" + 4096#64).setWidth 128 ∨ v = 0) := by
  have h0 : (Spike.Lib.A64.PhRec.m0Of (Λi Λ p) o.prog o.secs).initVal
      ⟨rtA (Λi Λ p) o.prog o.secs "scc_rt_pinned" + 16#64, 8⟩ = 0 :=
    Scc.Cert.Rt.A64.initVal_rt_of_rtInitOk (Λ := Λi Λ p) (rtInit_of_placeOKAt h) rfl
      (List.mem_append_right _ (List.mem_map.mpr ⟨1, by simp, rfl⟩))
  show Scc.Sem.FixG [((rtA (Λi Λ p) o.prog o.secs "scc_rt_pinned" + 16#64).toNat,
      (rtA (Λi Λ p) o.prog o.secs "scc_rt_stacks" + 4096#64).setWidth 128)]
      (Spike.Lib.A64.PhRec.m0Of (Λi Λ p) o.prog o.secs) l v ↔ _
  constructor
  · intro hG hl
    rcases hG _ _ (List.mem_singleton_self _) (by rw [hl, BitVec.ofNat_toNat, BitVec.setWidth_eq]) with h | h
    · exact .inl h
    · exact .inr (h.trans (by rw [hl]; exact h0))
  · intro hG a w haw hl
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp haw)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at hl
    rcases hG hl with h | h
    · exact .inl h
    · exact .inr (h.trans (by rw [hl]; exact h0.symm))

/-- **The value invariant agrees**, the runtime's names off `B`. -/
theorem G2_tail {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true}
    (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeOf Λ.code.lo oF.prog l = codeOf Λ.code.lo oE.prog l)
    (hn : ∀ x ∈ rtNames, x ∉ B) : G2 hF p = G2 hE p := by
  funext l v
  apply propext
  rw [G2_iff, G2_iff, rtA_tail (Λ := Λi Λ p) hsecs hc (hn _ (by decide)),
    rtA_tail (Λ := Λi Λ p) hsecs hc (hn _ (by decide))]

/-- `mapM` of functions agreeing on the list. -/
theorem mapM_congr {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.mapM_cons, List.mapM_cons, h x (List.mem_cons_self ..),
      mapM_congr fun y hy => h y (List.mem_cons_of_mem x hy)]

/-- **The phase table agrees** under resolvers agreeing on the rows' labels. -/
theorem phTabBy_congr {code code' : String → Option Nat}
    (hc : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, code r.l1 = code' r.l1 ∧ code r.l2 = code' r.l2) :
    phTabBy code = phTabBy code' := by
  have hr : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, PhRange.resolve code r = PhRange.resolve code' r := by
    intro r hr
    unfold PhRange.resolve
    rw [(hc r hr).1, (hc r hr).2]
  unfold phTabBy
  rw [mapM_congr fun r h => hr r (by simp [h]), mapM_congr fun r h => hr r (by simp [h]),
    mapM_congr fun r h => hr r (by simp [h]), mapM_congr fun r h => hr r (by simp [h])]

/-- **The phases agree**, the rows' labels off `B`. -/
theorem phOf_tail {lo : Nat} {P Q : Program} (hc : ∀ l, l ∉ B → codeOf lo P l = codeOf lo Q l)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B) : phOf lo P = phOf lo Q := by
  unfold phOf Scc.Cert.Rt.A64.phTabOf
  rw [phTabBy_congr fun r hr => ⟨hc _ (hrow r hr).1, hc _ (hrow r hr).2⟩]

/-- **The owned words agree along the relabelling**, the runtime's names and
the rows' labels off `B`. -/
theorem own2_tail {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true}
    (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeOf Λ.code.lo oF.prog l = codeOf Λ.code.lo oE.prog l)
    (hn : ∀ x ∈ rtNames, x ∉ B) (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    (exe : _root_.Executable) (endPc : Int64) :
    ∀ s fs, own2 hF p (relab exe endPc s) fs = own2 hE p s fs := by
  intro s fs
  let LF := Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK hF (LowerNode.imms2Me Λ p)
  let LE := Spike.Lib.A64.Rt.RuntimeLayout.ofPlaceOK hE (LowerNode.imms2Me Λ p)
  have hA : ∀ x ∈ rtNames, rtA (Λi Λ p) oF.prog oF.secs x = rtA (Λi Λ p) oE.prog oE.secs x :=
    fun x hx => rtA_tail hsecs hc (hn x hx)
  have hph : Spike.Lib.A64.PhRec.ph LF = Spike.Lib.A64.PhRec.ph LE := phOf_tail hc hrow
  have hpn : LF.pnA = LE.pnA := hA _ (by decide)
  have hlock : LF.lockA = LE.lockA := hA _ (by decide)
  have hfree : LF.freeNA = LE.freeNA := hA _ (by decide)
  have hnext : LF.nextA = LE.nextA := hA _ (by decide)
  show Spike.Lib.A64.PhRec.ownOf LF (Spike.Lib.A64.PhRec.ph LF (pcOf (relab exe endPc s))) =
    Spike.Lib.A64.PhRec.ownOf LE (Spike.Lib.A64.PhRec.ph LE (pcOf s))
  unfold Spike.Lib.A64.PhRec.ownOf
  rw [hph, hpn, hlock, hfree, hnext]
  rfl

/-! ## `Rest2A` along the tail -/

/-- Two members of a list with the same image under a map whose image list
has no duplicates are equal. -/
theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {L : List α}, (L.map f).Nodup → ∀ {a b : α}, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: L, h, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with hax | haL <;> rcases List.mem_cons.mp hb with hbx | hbL
    · exact hax.trans hbx.symm
    · subst hax; exact absurd (by rw [e]; exact List.mem_map_of_mem hbL) h.1
    · subst hbx; exact absurd (by rw [← e]; exact List.mem_map_of_mem haL) h.1
    · exact eq_of_nodup_map h.2 haL hbL e

open Spike.Lib.A64LabelCongr (Directive.Free) in
/-- **`Rest2A` from the text closed by its end label to the text with the
tail**: `oE`'s text is `P` closed by `te`, `oF`'s is `P` followed by `T`,
with the same data sections (`hsecs`); every label of `T` and `te` is in
`B` and `T` has no instruction; the instructions of `P` name none of `B`
(`hfree`); the transfer sites, abort stubs, runtime's names and phase rows'
labels are off `B`. The load facts come from `placeOKAt` on both sides. -/
theorem rest2A_tail_text {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true}
    {arch : WeakMem.Arch} {E : Entry} {P T : Program} {te : _root_.Label}
    (hsecs : oF.secs = oE.secs) (hPE : oE.prog = P ++ [.label te]) (hPF : oF.prog = P ++ T)
    (hte : te ∈ B) (hT : ∀ d ∈ T, ∀ l, d = .label l → l ∈ B) (hTi : ∀ d ∈ T, ∀ i, d ≠ .instr i)
    (hfree : ∀ i, Directive.instr i ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    (h : Rest2A Λ p hE arch E) : Rest2A Λ p hF arch E := by
  have hc : ∀ l, l ∉ B → codeOf Λ.code.lo oF.prog l = codeOf Λ.code.lo oE.prog l := by
    rw [hPF, hPE]; exact codeOf_tail hte hT
  have hlF := loadOk_of_placeOKAt hF
  have hlE := loadOk_of_placeOKAt hE
  rw [hsecs, hPF] at hlF
  rw [hPE] at hlE
  haveI := Scc.Cert.Link.A64.validLayout_of_loadOk hlF E
  have hO := tailOK_threadAt (E := E) (base := Λ.code.lo) (syms := loadSyms Λ oE.secs.rodata) hte hT hTi
    (fun q hq => by
      obtain ⟨hm, hge⟩ := List.mem_filter.mp hq
      exact (Scc.Cert.Rt.A64.out_of_symsAround (Scc.Cert.Link.A64.symsAround_of_loadOk hlF) q hm).resolve_left
        (by simp only [decide_eq_true_eq] at hge; omega))
    (fun q hq r hr he => by
      rw [eq_of_nodup_map (Scc.Cert.Link.A64.names_nodup_of_loadOk hlE)
        (List.mem_filter.mp hq).1 (List.mem_filter.mp hr).1 he])
    hfree (Scc.Cert.Link.A64.codeEnd_lt_of_loadOk hlF) (Scc.Cert.Link.A64.validLayout_of_loadOk hlE E)
  rw [← hPE, ← hPF] at hO
  exact rest2A_tail hsecs hO (marks_tail hc hs ha) (meW2_tail hsecs hc (hn _ (by decide)))
    (G2_tail hsecs hc hn) (own2_tail hsecs hc hn hrow _ _) h

open Spike.Lib.LowerA64 (lay2 correct2_of) in
open Spike.Lib.A64LabelCongr (Directive.Free) in
/-- **`Correct` on the parsed text with the tail from the open premises at
the text closed by its end label**: `correct2_of` at `oF` (both outputs
passing `placeOKAt` at `Λ`), `Rest2A` by `rest2A_tail_text` from `oE`'s,
the counter's zero word read off the shared data sections. -/
theorem correct2_tail {p : Prog} (hp : Scc.Lower.Accepted2 p = true)
    {hE : placeOKAt pcfg (lay2 Λ p) oE = true} (hF : placeOKAt pcfg Λ oF = true)
    (hc : Spike.Lib.A64.Rt.CtrZ oE) {Bu : Budget} (hB : Bu.cells = allocCells) {arch : WeakMem.Arch}
    {E : Entry} (hEo : E.Ok (lay2 Λ p))
    (hnum : Spike.Lib.LowerNode.SrcNumSP (SrcSem.srcP1o arch p) p Spike.Lib.LowerNode.PrintLd)
    (hd : Scc.Lower.hasPrint p = true → p.find? (·.name == "printL") = some Spike.Lib.PrintSrc.printLD)
    (hrdN : Spike.Lib.Consumer1.SrcRd (SrcSem.srcP1o arch p) p Spike.Lib.LowerNode.IsNum)
    {P T : Program} {te : _root_.Label} {B : List _root_.Label}
    (hsecs : oF.secs = oE.secs) (hPE : oE.prog = P ++ [.label te]) (hPF : oF.prog = P ++ T)
    (hte : te ∈ B) (hT : ∀ d ∈ T, ∀ l, d = .label l → l ∈ B) (hTi : ∀ d ∈ T, ∀ i, d ≠ .instr i)
    (hfree : ∀ i, Directive.instr i ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    (R : Rest2A (lay2 Λ p) p hE arch E) :
    Correct (Spike.Lib.A64Consumer.TParE E) (SrcSem.source (SrcSem.srcP1o arch p) p) (lay2 Λ p) Bu
      (asm2 oF) := by
  have hcF : Spike.Lib.A64.Rt.CtrZ oF := by unfold Spike.Lib.A64.Rt.CtrZ; rw [hsecs]; exact hc
  have hF' : placeOKAt pcfg (lay2 Λ p) oF = true := hF
  exact correct2_of hp hF hcF hB hEo hnum hd hrdN
    (rest2A_tail_text (hF := hF') hsecs hPE hPF hte hT hTi hfree hs ha hn hrow R)

end Spike.Lib.A64Rest2Tail

/-- info: 'Spike.Lib.A64Rest2Tail.correct2_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.correct2_tail

/-- info: 'Spike.Lib.A64Rest2Tail.rest2A_tail_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.rest2A_tail_text

/-- info: 'Spike.Lib.A64Rest2Tail.codeOf_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.codeOf_tail

/-- info: 'Spike.Lib.A64Rest2Tail.marks_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.marks_tail

/-- info: 'Spike.Lib.A64Rest2Tail.meW2_tail' depends on axioms: [propext] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.meW2_tail

/-- info: 'Spike.Lib.A64Rest2Tail.G2_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.G2_tail

/-- info: 'Spike.Lib.A64Rest2Tail.own2_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.A64Rest2Tail.own2_tail
