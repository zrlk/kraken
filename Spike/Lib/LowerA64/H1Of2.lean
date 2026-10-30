/-
**The landings' segments** (AArch64; h1's assembly): from an allocation's
landing with its suspended frames (`LandStk`) at a placement `L`, `ls` to
the bottom frames' exits, at the placement extended by the landing's label
`upd L l b`, `updN ls l w`.

- `nWords_of_elem2`: an `elem2` element type takes at least one word, so
  a landing's word count `w = q.n · nWords us` holds the count;
- `BodyPtW.newBufP`: at a resumption point at `let x = newBuf cn τ in e`,
  the allocation's call arguments (`lowerC2_newBuf_inv`), its resumption
  facts at the `let` (`PtC2`), its code (`InstsC2`) and the continuation's
  resumption point and walk facts, at one label counter;
- `segWS_of_points`: a segment from every state of `P` alone is one from `P`;
- `landStk_seg`: the landing's segment, generic in the world `W` and the
  memory side `ms` at each placement: the allocator's continuation and the
  returned base's store (`newBufC_tail`, `AllocStoreAt` at the landing's
  placement from the context, `hAW`), the allocating frame's body at the
  extended placement (`bodyAtPt2W`, its records moved up by `CxOkS.mono_lbl`
  at `lvlLe_upd`), its suspended frames resumed in turn (`resume_stk`, each
  context's `ResumeCx2` at the extended placement, `hres`), and the bottom
  frames' exits and the aborts on to `Q` (`hbot`, `hAbQ`).

The context premises (`hAW`, `hres`, `hAb`) are asked of every context
`CxOk` the landing may carry: `CxOk` is the instance the program's blocks'
specifications (`FnSpecC2`) are proved at, so these are facts about it.
-/
import Spike.Lib.LowerA64.LandStk2
import Spike.Lib.LowerA64.ResumeStk2
import Spike.Lib.LowerA64.StkMono2

namespace Spike.Lib.LowerA64

open CoreLang CoreTerm
open Kraken Kraken.AArch64.Parser Kraken.Promising Kraken.Promising.AArch64 Kraken.Promising.Lower.A64
open Spike.Lib Spike.Lib.A64.Flow
open Scc.Emit.A64 Scc.Lower.InvA64
open Spike.Lib.LowerNode
open Spike.Lib.Form (lookupS)
open Scc.Lower.Inv (atomV regName)
open Spike.Lib.LowerShape (newBufCall newBufTy unitsOf countsO lowerC2)
open Spike.Lib.A64.Alloc (Call Ea)
open Spike.Lib.A64.Flow.NewBuf (nbJc AllocCtx allocAbortDepth)
open Spike.Lib.A64.KeepTP (TP)
open Spike.Lib.Consumer1 Spike.Lib.A64Consumer Spike.Lib.A64ConsumerS Spike.Lib.A64ConsumerA

/-- **An `elem2` element takes a word.** -/
theorem nWords_of_elem2 {τ : Ty} (he : Scc.Lower.elem2 τ = true) {us : List TermRun.Acc}
    (h : TermRun.accs (TermRun.close [] τ) = some us) : 1 ≤ TermRun.nWords us := by
  cases τ <;> simp only [Scc.Lower.elem2, Bool.false_eq_true] at he <;>
    simp [TermRun.close, substTs, TermRun.accs] at h <;> subst h <;> simp [TermRun.nWords, TermRun.Acc.size]

/-- **A segment from each state alone.** -/
theorem segWS_of_points {I : ISA} {W : FragS I} {K : I.State → I.State → Prop} {p : Prog}
    {lbl : WeakMem.AllocLabel → Option Nat} {ms : List TermRun.Frame → MemSide I} {P Q : FragS I}
    (h : ∀ s c fs, P s c fs → SegWS W K p lbl ms (fun s' c' fs' => s' = s ∧ c' = c ∧ fs' = fs) Q) :
    SegWS W K p lbl ms P Q := by
  refine (SegWS.exists_pre (P := fun (x : {x : I.State × Ctl × List TermRun.Frame // P x.1 x.2.1 x.2.2}) =>
    fun s c fs => s = x.1.1 ∧ c = x.1.2.1 ∧ fs = x.1.2.2) fun x => h _ _ _ x.2).mono_pre ?_
  intro s c fs hp
  exact ⟨⟨(s, c, fs), hp⟩, rfl, rfl, rfl⟩

section NewBufP

variable {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Expr → Prop} {d : Decl}

/-- **Past a buffer allocation, at one label counter** (`BodyPtW.newBuf`
with the allocation's own resumption facts): at a resumption point at
`let x = newBuf cn τ in e`, `env` fresh at `n`, the term in `T`, the
allocation's arguments (`lowerC2_newBuf_inv`), its resumption facts
(`PtC2` at `RetLk`) and code (`InstsC2`) at the same counter `kk`, the
continuation's free variables bound, immediates and register bases at the
extended environment, and its resumption point at `pc'`. -/
theorem BodyPtW.newBufP {c : FnCode2 exe prog endPc RaOk Cd i T d} {ra : BitVec 64} {pc : Int64} {x : String}
    {cn : CoreTerm.At} {τ : Ty} {e : Expr} {env : Scc.Lower.Env} {n : Nat}
    {lits : List (String × Scc.Lower.LitV)} {cs bufs : List (String × Nat)}
    (h : BodyPtW c ra pc (.let_ x (.newBuf cn τ) e) env n lits cs bufs) :
    Fresh env n ∧ T (.let_ x (.newBuf cn τ) e) ∧
    ∃ (tk : Ty) (kv : UInt64) (en em hh kk : Nat) (pc' : Int64),
      atomV env cn = some (tk, [.imm kv]) ∧ countsO c.lcx.obj τ = some (en, em) ∧
      Scc.Obj.header0 c.lcx.obj .array en em = some hh ∧
      PtC2 c.lcx c.cx (Cd ra) (c.Bl ra) (_root_.Executable.labels exe).label i T (RetLk d.retTy) kk pc env n lits
        cs bufs (.let_ x (.newBuf cn τ) e) ∧
      InstsC2 c.cx (Cd ra) (c.Bl ra) kk pc
        [newBufCall (regName x n) hh kv (unitsOf ((Scc.Frontend.words τ).getD (en + em)) kv)] pc' ∧
      (∀ y ∈ Scc.Sem.exprFv e,
        (lookupS (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) y).isSome) ∧
      ImmIn i (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e ∧
      LocBaseRegAt (ofEnv2 ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)) e ∧
      BodyPtW c ra pc' e ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env) (n + 1)
        ((x, Scc.Lower.opLit c.lcx.prog lits (.newBuf cn τ)) :: lits) (Scc.Lower.csAfter x cs (.newBuf cn τ))
        (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) := by
  obtain ⟨l, k, r, kk, hr, hfr, hcode, hbl, hWs, hLs, hC, hX⟩ := h
  have hT := (walk2_head hWs).2.1
  have hpt : PtC2 c.lcx c.cx (Cd ra) (c.Bl ra) (_root_.Executable.labels exe).label i T (RetLk d.retTy) kk pc env
      n lits cs bufs (.let_ x (.newBuf cn τ) e) := ⟨l, k, r, hr, hcode, hbl, hWs, hLs, hC, hX⟩
  obtain ⟨tk, kv, en, em, hh, sc, hq, r', ha, hc, hhd, hw, hm, hr', rfl⟩ := Spike.Lib.LowerShape.lowerC2_newBuf_inv hr
  obtain ⟨pc', hi, hrest⟩ := (CodeC2_append r'.insts [_] kk pc).1 hcode
  have hC' := hC
  simp only [Scc.Lower.countsB, Bool.and_eq_true] at hC'
  have hW' := Spike.Lib.LowerShape.walk2_tail_newBuf ha hc hhd hw hm hWs
  have hh' := walk2_head hW'
  exact ⟨hfr, hT, tk, kv, en, em, hh, kk, pc', ha, hc, hhd, hpt, hi,
    fun y hy => isSome_lookupS_ofEnv2 (Spike.Lib.LowerShape.lowerC2_fv c.lcx e _ _ _ _ _ hr' y hy), hh'.1, hh'.2.2.2.2,
    l, k + 1, r', _, hr', hfr.newBuf x τ, hrest, hbl, hW',
    fun q hq => hLs q (by simp only [Scc.Lower.litWalk2]; exact List.mem_cons_of_mem _ hq), hC'.2,
    xchgsB_tail hX⟩

end NewBufP

section Land

variable {p : Prog} {exe : _root_.Executable} {prog : List Directive} {endPc : Int64}
  {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List Directive → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe prog endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
    (Ctl → Prop) → FragS isaLSE2 → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **A landing's segment** at the placement `L`, `ls` and a fresh label
`l` (unplaced, `hl`; no size, `hz`) at the base `b` with `w` words, generic
in the world `W` and the memory side `ms` at each placement, to `Q`: the
landing's continuation is the returned base's store (`newBufC_tail` at
the extended placement; the count held as the element takes a word,
`nWords_of_elem2`), the allocating frame's body to its exits
(`bodyAtPt2W`), its suspended frames resumed (`resume_stk`, the records
moved up by `CxOkS.mono_lbl`), the bottom frames' exits on to `Q` (`hbot`)
and the aborts (`hAbQ`). Each context `CxOk` the landing carries gives the
allocator's region and `AllocStoreAt` at `L`, `ls` (`hAW`), `ResumeCx2` at the
extended placement (`hres`) and its aborts inside `Ab₀` (`hAb`). -/
theorem landStk_seg {W : Lbl → Lsize → FragS isaLSE2} {K : State → State → Prop}
    {ms : Lbl → Lsize → List TermRun.Frame → MemSide isaLSE2} {Ab₀ Q : FragS isaLSE2}
    {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b w : Nat} (hl : L l = none) (hz : ls l = 0)
    (hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hAW : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      R.lo ≤ -allocAbortDepth ((hcode j d hd).cx.frame : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).cx (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => W L ls s c fs) K exe endPc R F (ms L ls fs) fp ra tp G0 i (T j) (RetLk d.retTy))
    (hres : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      ResumeCx2 (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b) (AllocReach.updN ls l w)
        (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
        (hcode j d hd) R F fs fp ra tp G0 Ab)
    (hAb : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → ∀ s c fs', Ab s c fs' → Ab₀ s c fs')
    (hbot : ∀ k fs, Bot k fs → SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
      (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
      (ExitStk p P (AllocReach.upd L l b) exe endPc k fs Ab₀) Q)
    (hAbQ : SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
      (ms (AllocReach.upd L l b) (AllocReach.updN ls l w)) Ab₀ Q) :
    SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
      (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
      (LandStk (p := p) hcode CxOk Bot ms L ls l b w) Q := by
  have hv := Spike.Lib.LowerNode.lvlLe_upd hl hz b w
  refine segWS_of_points fun s c fs hE => ?_
  obtain ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, pcB, x, cn, τ, e, env, n, lits, cs, bufs, h, kv, u, la, q,
    hcx, hra, hc0, hpt, hnb, hla, rfl, -, hF', hctx, hAt, htp⟩ := hE
  obtain ⟨hlo, hAWi⟩ := hAW j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  obtain ⟨-, hFs, hR, hal, hhi, hG0, W₀, hW₀, -, hW, hWp, hab, hcon⟩ :=
    hres j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  obtain ⟨hfr, hT, tk', kv', en, em, hh, kk, pc', hat', hco', hhd', hptc, hi, hIt, hIc, hlb, hpt'⟩ :=
    BodyPtW.newBufP hpt
  obtain ⟨tk, en0, em0, hat, hco, hhd, rfl⟩ := hnb
  rw [hat] at hat'
  simp only [Option.some.injEq, Prod.mk.injEq, List.cons.injEq, Scc.IR.Operand.imm.injEq, and_true] at hat'
  obtain ⟨rfl, rfl⟩ := hat'
  rw [hco] at hco'
  cases hco'
  rw [hhd] at hhd'
  cases hhd'
  have he2 := hTn j d hd x cn τ e hT
  -- the count held: the call's element type is the allocation's
  have hkz : q.1.n ≤ AllocReach.updN ls l w l := by
    obtain ⟨-, -, -, -, σ, -, hFm, hJ⟩ := id hAt
    obtain ⟨-, -, -, -, -, -, -, -, -, us, hus, hw⟩ := hJ
    obtain ⟨mC, σC, c1, -, ⟨σ0, hJ1, -⟩, hN, -⟩ := hctx _ hFm
    obtain ⟨-, -, -, -, -, -, Lx, sm, B, hNJ, -⟩ := hJ1
    have ht : q.1.c0.term = .let_ x (.newBuf cn τ) e := hN.1 ▸ hNJ.1
    rw [q.2.term] at ht
    simp only [Expr.let_.injEq, Op.newBuf.injEq] at ht
    obtain ⟨-, ⟨-, hτ⟩, -⟩ := ht
    rw [hτ] at hus
    have := nWords_of_elem2 he2 hus
    simp only [AllocReach.updN, ite_true]
    rw [hw]
    exact Nat.le_mul_of_pos_right _ this
  have hl' : AllocReach.upd L l b l = some b := by simp [AllocReach.upd]
  have s1 := newBufC_tail (W := W (AllocReach.upd L l b) (AllocReach.updN ls l w)) (K := K)
    (ms := ms L ls) (w := w) (Ab := Ab) (hcode j d hd).hf (hcode j d hd).h1 (hcode j d hd).h16 hFs hR hal hlo hhi
    ((hcode j d hd).hCd ra hra)
    (W₀ := fun L ls s c => W L ls s c fs) (hTn j d hd) (hcode j d hd).lcx hAWi hc0 hT hfr hat hco hhd hptc hi hIt hIc
    hlb hla q.2 hF' hctx hv.1 hl' hv.2 hkz (fun _ _ h => h)
    (ms' := ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
  refine (s1.mono_pre fun s' c' fs' ⟨h1, h2, h3⟩ => ⟨h1 ▸ h2 ▸ ⟨hAt, htp⟩, h3⟩).seq (SegWS.or_pre ?_ ?_)
  · -- the body at the extended placement, its frames resumed, the bottom's exits
    obtain ⟨-, st, hst⟩ := CxOkS.mono_lbl hv (fun _ _ _ _ _ _ _ _ _ h => h) hcx
    have hlo1 : R.lo ≤ -((hcode j d hd).cx.frame : Int) := by
      simp only [allocAbortDepth, Spike.Lib.A64.Flow.NewBuf.allocFrame] at hlo; omega
    refine (SegWS.exists_pre (P := fun c0' s' c' fs' => FrameRunM p (c0, fs) (c0', fs) ∧
      LetAt p (AllocReach.upd L l b) (AllocReach.updN ls l w) i (hcode j d hd).cx exe endPc R F fp ra tp c0' fs pc' e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit (hcode j d hd).lcx.prog lits (.newBuf cn τ)) :: lits)
        (Scc.Lower.csAfter x cs (.newBuf cn τ)) (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) s' c' fs')
      fun c0' => ?_).mono_pre fun s' c' fs' ⟨hfs, c0', hr, hA⟩ => ⟨c0', hr, hA, hfs⟩
    by_cases hr : FrameRunM p (c0, fs) (c0', fs)
    · have hg0 := hG0 _ _ hc0 hr
      have s2 := bodyAtPt2W (hcode j d hd) hra hFs hR hal hlo1 hhi hW₀ hG0 hW hWp hab hcon hpt' hg0
      have s3 := resume_stk (hcode := hcode) (Bot := Bot) hres hAb (k := ⟨j, R, F, fp, ra, tp, G0⟩) hst hg0
        ⟨d, hd, rfl⟩ (s2.mono_post fun s c fs h => h.imp_right (hAb _ _ _ _ _ _ _ _ _ hcx.1 s c fs))
      exact (s3.seq (hbot _ _ (StkOk.bot_drop hst))).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hr h.1
  · exact hAbQ.mono_pre fun s c fs h => hAb _ _ _ _ _ _ _ _ _ hcx.1 s c fs h

end Land

/-- info: 'Spike.Lib.LowerA64.nWords_of_elem2' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms nWords_of_elem2

/-- info: 'Spike.Lib.LowerA64.BodyPtW.newBufP' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms BodyPtW.newBufP

/-- info: 'Spike.Lib.LowerA64.landStk_seg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms landStk_seg

end Spike.Lib.LowerA64
