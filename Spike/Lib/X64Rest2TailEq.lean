/-
**The four agreements `rest2X_tail` asks for, along a tail of the text**
(x86-64): from two outputs whose code labels agree off a set `B` of labels
(`hc`; e.g. the moved end label and the tail's, `codeLabel_off`) and with
the same data sections, the marks, `me`'s word, the value invariant and the
owned words agree, as long as the labels they read are off `B`. The
AArch64 twin is `Spike/Lib/A64Rest2TailEq.lean`.

- `codeLabel_off`: the cells closed by the end label and the cells with a
  tail agree off `B`;
- `rtA_tail`, `phTabBy_congr`, `phOf_tail`: the runtime's word addresses and
  the phase index read only labels;
- `marks_tail`, `meW2_tail`, `G2_tail`, `own2_tail`: the four agreements;
- `rest2X_tail_text`: `Rest2X` from the cells closed by the end label to
  the cells with a tail, the loader's facts from `placeOKAt` on both sides.
-/
import Spike.Lib.LowerX64.Closed2Of
import Spike.Lib.X64TextTail
import Spike.Lib.X64RestTail
import Spike.Lib.X64Rest2Tail

namespace Spike.Lib.X64Rest2TailEq

open CoreLang CoreTerm
open Kraken.Promising Kraken.Promising.X64
open Scc.Sem Scc.Sem.X64
open Scc.Cert.PlaceOK Scc.Cert.PlaceOK.X64
open Scc.Cert.Rt.X64 (rtA rtNames symLab PhRange PhTab phTabBy phTabOf phOf bPR bLR bNR bTR)
open Spike.Lib.LowerX64 (G2 own2 meW2 asm2)
open Spike.Lib.X64RestTail (relab)

/-- **The cells closed by the end label `te` and the cells followed by a
tail `T` agree on every code label off `B`**, when `te` and every label of
`T` are in `B`. -/
theorem codeLabel_off {lo : Nat} {P T : List (Directive × Nat)} {te : String} {B : List String}
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) :
    ∀ l, l ∉ B → codeLabel lo (P ++ T) l = codeLabel lo (P ++ [(.label te, 0)]) l := fun l hl =>
  (Spike.Lib.X64TextTail.codeLabel_tail (fun h => hl (by subst h; exact hte))
    (fun dz hdz h => hl (hT dz hdz l h))).symm

variable {B : List String}

/-- **A runtime word's address reads only its label**: off `B`, it is the
same in two cells agreeing off `B`. -/
theorem rtA_tail {Λ : Scc.Sem.Layout} {cE cF : List (Directive × Nat)} {secs : DataSecs}
    (hc : ∀ l, l ∉ B → codeLabel Λ.code.lo cF l = codeLabel Λ.code.lo cE l) {x : String} (hx : x ∉ B) :
    rtA Λ cF secs x = rtA Λ cE secs x := by
  simp only [rtA, symLab, hc x hx]

/-- `mapM` of two functions agreeing on the list. -/
private theorem mapM_congr {α β : Type} {f g : α → Option β} :
    ∀ {xs : List α}, (∀ x ∈ xs, f x = g x) → xs.mapM f = xs.mapM g
  | [], _ => rfl
  | x :: xs, h => by
    simp only [List.mapM_cons, h x List.mem_cons_self,
      mapM_congr (xs := xs) fun y hy => h y (List.mem_cons_of_mem _ hy)]

/-- **The phase table reads only its rows' labels.** -/
theorem phTabBy_congr {c1 c2 : String → Option Nat}
    (h : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, c1 r.l1 = c2 r.l1 ∧ c1 r.l2 = c2 r.l2) :
    phTabBy c1 = phTabBy c2 := by
  have hr : ∀ rs : List PhRange, (∀ r ∈ rs, r ∈ bPR ++ bLR ++ bNR ++ bTR) →
      rs.mapM (PhRange.resolve c1) = rs.mapM (PhRange.resolve c2) := fun rs hs =>
    mapM_congr fun r hm => by
      obtain ⟨h1, h2⟩ := h r (hs r hm)
      simp only [PhRange.resolve, h1, h2]
  unfold phTabBy
  rw [hr bPR (fun r hm => by simp [hm]), hr bLR (fun r hm => by simp [hm]), hr bNR (fun r hm => by simp [hm]),
    hr bTR (fun r hm => by simp [hm])]

/-- **The phase index of two cells agreeing off `B`** is the same, the phase
table's labels off `B`. -/
theorem phOf_tail {lo : Nat} {cE cF : List (Directive × Nat)}
    (hc : ∀ l, l ∉ B → codeLabel lo cF l = codeLabel lo cE l)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B) : phOf lo cF = phOf lo cE := by
  unfold phOf phTabOf
  rw [phTabBy_congr fun r hr => ⟨hc _ (hrow r hr).1, hc _ (hrow r hr).2⟩]

variable {Λ : Scc.Sem.Layout} {pcfg : Scc.Cert.PlaceOK.Config} {oE oF : Scc.Cert.PlaceOK.X64.Out}

/-- **The marks agree**, the transfer sites' and abort stubs' labels off `B`. -/
theorem marks_tail (E : Entry) (hc : ∀ l, l ∉ B → codeLabel Λ.code.lo oF.prog l = codeLabel Λ.code.lo oE.prog l)
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) :
    (Spike.Lib.X64Consumer.TParE E).marks (asm2 oF) Λ = (Spike.Lib.X64Consumer.TParE E).marks (asm2 oE) Λ := by
  unfold Target.marks
  congr 1
  · funext k; exact hc _ (hs k)
  · funext k; exact hc _ (ha k)

/-- **`me`'s word agrees**, `scc_rt_pinned` off `B`. -/
theorem meW2_tail (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeLabel Λ.code.lo oF.prog l = codeLabel Λ.code.lo oE.prog l)
    (hpin : "scc_rt_pinned" ∉ B) : meW2 Λ oF = meW2 Λ oE := by
  unfold meW2
  rw [hsecs, rtA_tail hc hpin]

/-- `FixG` at one fixed word reads the memory only at that word. -/
theorem fixG_one_congr {a : Nat} {w : Val} {m0 m0' : Memory}
    (h : m0.initVal ⟨BitVec.ofNat 64 a, 8⟩ = m0'.initVal ⟨BitVec.ofNat 64 a, 8⟩) :
    FixG [(a, w)] m0 = FixG [(a, w)] m0' := by
  funext l v
  apply propext
  unfold FixG
  constructor <;> intro hf a' w' hm hl <;> simp only [List.mem_singleton, Prod.mk.injEq] at hm <;>
    obtain ⟨rfl, rfl⟩ := hm <;> rcases hf a' w' (List.mem_singleton.2 rfl) hl with h1 | h1
  · exact .inl h1
  · exact .inr (by rw [h1, hl, h])
  · exact .inl h1
  · exact .inr (by rw [h1, hl, h])

/-- **The value invariant agrees**, the runtime's words off `B`: it reads
the first TCB's limit word and the first stack, and the load's initial
value at the limit word, `0` on both sides (`rtInit_of_placeOKAt`). -/
theorem G2_tail {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true} (p : Prog)
    (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeLabel Λ.code.lo oF.prog l = codeLabel Λ.code.lo oE.prog l)
    (hn : ∀ x ∈ rtNames, x ∉ B) : G2 hF p = G2 hE p := by
  have hA : ∀ x ∈ rtNames, rtA Λ oF.prog oF.secs x = rtA Λ oE.prog oE.secs x := fun x hx => by
    rw [hsecs]; exact rtA_tail hc (hn x hx)
  have hpin : rtA Λ oF.prog oF.secs "scc_rt_pinned" = rtA Λ oE.prog oE.secs "scc_rt_pinned" :=
    hA _ (by decide)
  have hstk : rtA Λ oF.prog oF.secs "scc_rt_stacks" = rtA Λ oE.prog oE.secs "scc_rt_stacks" :=
    hA _ (by decide)
  have h0 : ∀ {o : Scc.Cert.PlaceOK.X64.Out} (h : placeOKAt pcfg Λ o = true),
      (Spike.Lib.X64.PhRec.m0Of
          (Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK h (Spike.Lib.LowerNode.imms2Me Λ p)).Λ o.prog o.secs).initVal
        ⟨BitVec.ofNat 64 (rtA Λ o.prog o.secs "scc_rt_pinned" + 16#64).toNat, 8⟩ = 0 := fun h => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact Scc.Cert.Rt.X64.initVal_rt_of_rtInitOk (rtInit_of_placeOKAt h) rfl
      (List.mem_append_right _ (List.mem_map.2 ⟨1, by decide, rfl⟩))
  unfold G2 Spike.Lib.X64.PhRec.GOf
  show FixG [((rtA Λ oF.prog oF.secs "scc_rt_pinned" + 16#64).toNat,
      (rtA Λ oF.prog oF.secs "scc_rt_stacks" + 4096#64).setWidth 128)] _ =
    FixG [((rtA Λ oE.prog oE.secs "scc_rt_pinned" + 16#64).toNat,
      (rtA Λ oE.prog oE.secs "scc_rt_stacks" + 4096#64).setWidth 128)] _
  rw [hpin, hstk]
  apply fixG_one_congr
  rw [← hpin, h0 hF, hpin, h0 hE]

/-- **The owned words agree**, read through the relabelling: the phase
table's and the runtime's labels off `B`, the pc unchanged by `relab`. -/
theorem own2_tail {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true} (p : Prog)
    (hsecs : oF.secs = oE.secs)
    (hc : ∀ l, l ∉ B → codeLabel Λ.code.lo oF.prog l = codeLabel Λ.code.lo oE.prog l)
    (hn : ∀ x ∈ rtNames, x ∉ B) (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    (exeF : _root_.Executable) (endF : Int64) :
    ∀ s fs, own2 hF p (relab exeF endF s) fs = own2 hE p s fs := by
  have hA : ∀ x ∈ rtNames, rtA Λ oF.prog oF.secs x = rtA Λ oE.prog oE.secs x := fun x hx => by
    rw [hsecs]; exact rtA_tail hc (hn x hx)
  have hph : phOf Λ.code.lo oF.prog = phOf Λ.code.lo oE.prog := phOf_tail hc hrow
  intro s fs
  let LF := Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK hF (Spike.Lib.LowerNode.imms2Me Λ p)
  let LE := Spike.Lib.X64.Rt.RuntimeLayout.ofPlaceOK hE (Spike.Lib.LowerNode.imms2Me Λ p)
  have h1 : LF.pnA = LE.pnA := hA _ (by decide)
  have h2 : LF.lockA = LE.lockA := hA _ (by decide)
  have h3 : LF.freeNA = LE.freeNA := hA _ (by decide)
  have h4 : LF.nextA = LE.nextA := hA _ (by decide)
  have h5 : Spike.Lib.X64.PhRec.ph LF = Spike.Lib.X64.PhRec.ph LE := hph
  show Spike.Lib.X64.PhRec.ownOf LF (Spike.Lib.X64.PhRec.ph LF (pcOf s)) =
    Spike.Lib.X64.PhRec.ownOf LE (Spike.Lib.X64.PhRec.ph LE (pcOf s))
  simp only [Spike.Lib.X64.PhRec.ownOf, h1, h2, h3, h4, h5]

/-- Two members of a list with injective names under `f` and the same name
are equal. -/
private theorem eq_of_nodup_map {α β : Type} {f : α → β} :
    ∀ {L : List α}, (L.map f).Nodup → ∀ {a b : α}, a ∈ L → b ∈ L → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | x :: L, h, a, b, ha, hb, e => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with hax | haL <;> rcases List.mem_cons.mp hb with hbx | hbL
    · exact hax.trans hbx.symm
    · subst hax; exact absurd (e ▸ List.mem_map_of_mem hbL) h.1
    · subst hbx; exact absurd (e.symm ▸ List.mem_map_of_mem haL) h.1
    · exact eq_of_nodup_map h.2 haL hbL e

open Spike.Lib.X64LabelCongr (Directive.Free) in
/-- **`Rest2X` along a tail of the text**: from the cells `P` closed by the
end label `te` (`oE`) to `P` followed by an instruction-free tail `T`
(`oF`), the same data sections, `te` and the tail's labels in `B`, `P`'s
instructions naming none of `B`, and the labels the marks, the runtime's
words and the phase table read off `B`; the loader's facts (symbols above
the code, names once, the code's end in the address space, valid layouts)
from `placeOKAt` on both sides. -/
theorem rest2X_tail_text {hE : placeOKAt pcfg Λ oE = true} {hF : placeOKAt pcfg Λ oF = true}
    {p : Prog} {arch : WeakMem.Arch} {E : Entry} {P T : List (Directive × Nat)} {te : String}
    (hsecs : oF.secs = oE.secs) (hPE : oE.prog = P ++ [(.label te, 0)]) (hPF : oF.prog = P ++ T)
    (hte : te ∈ B) (hT : ∀ dz ∈ T, ∀ l, dz.1 = .label l → l ∈ B) (hTi : ∀ dz ∈ T, ∀ i, dz.1 ≠ .instr i)
    (hfree : ∀ i z, (Directive.instr i, z) ∈ P → Directive.Free B (.instr i))
    (hs : ∀ k : XferKind, k.label ∉ B) (ha : ∀ k, Λ.abortLbl k ∉ B) (hn : ∀ x ∈ rtNames, x ∉ B)
    (hrow : ∀ r ∈ bPR ++ bLR ++ bNR ++ bTR, r.l1 ∉ B ∧ r.l2 ∉ B)
    (h : Spike.Lib.LowerX64.Rest2X Λ p hE arch E) : Spike.Lib.LowerX64.Rest2X Λ p hF arch E := by
  have hc : ∀ l, l ∉ B → codeLabel Λ.code.lo oF.prog l = codeLabel Λ.code.lo oE.prog l := by
    rw [hPF, hPE]; exact codeLabel_off hte hT
  have hlF := loadOk_of_placeOKAt hF
  have hlE := loadOk_of_placeOKAt hE
  rw [hsecs, hPF] at hlF
  rw [hPE] at hlE
  haveI := Scc.Cert.Link.X64.validLayout_of_loadOk hlF E
  have hO := Spike.Lib.X64Rest2Tail.tailOK_threadAt (E := E) (base := Λ.code.lo)
    (syms := loadSyms Λ oE.secs.rodata) hte hT hTi
    (fun q hq => by
      obtain ⟨hm, hge⟩ := List.mem_filter.mp hq
      exact (Scc.Cert.Link.X64.out_of_symsAround (Scc.Cert.Link.X64.symsAround_of_loadOk hlF) q hm).resolve_left
        (by simp only [decide_eq_true_eq] at hge; omega))
    (fun q hq r hr he => by
      rw [eq_of_nodup_map (Scc.Cert.Link.X64.names_nodup_of_loadOk hlE)
        (List.mem_filter.mp hq).1 (List.mem_filter.mp hr).1 he])
    hfree (Scc.Cert.Link.X64.codeEnd_lt_of_loadOk hlF) (Scc.Cert.Link.X64.validLayout_of_loadOk hlE E)
  rw [← hPE, ← hPF] at hO
  exact Spike.Lib.X64Rest2Tail.rest2X_tail hsecs hO (marks_tail E hc hs ha)
    (meW2_tail hsecs hc (hn _ (by decide))) (G2_tail p hsecs hc hn) (own2_tail p hsecs hc hn hrow _ _) h

end Spike.Lib.X64Rest2TailEq

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.X64Rest2TailEq.marks_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2TailEq.marks_tail

/-- info: 'Spike.Lib.X64Rest2TailEq.meW2_tail' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2TailEq.meW2_tail

/-- info: 'Spike.Lib.X64Rest2TailEq.G2_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2TailEq.G2_tail

/-- info: 'Spike.Lib.X64Rest2TailEq.own2_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2TailEq.own2_tail

/-- info: 'Spike.Lib.X64Rest2TailEq.rest2X_tail_text' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.X64Rest2TailEq.rest2X_tail_text
