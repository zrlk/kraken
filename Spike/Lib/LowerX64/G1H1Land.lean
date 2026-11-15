/-
**A landing's segment at contexts without records, the allocating frame's
aborts at its own fragment** (x86-64; the twin of
`Spike/Lib/LowerA64/G1H1Land.lean`): `landStk_segT`
(`Spike/Lib/LowerX64/ResumeCx2T.lean`) for contexts `CxOk` at one frame
(`hone`; then no record sits below the allocating frame, so the records'
`ResumeCx2` is not asked), with the allocating frame resumed at some aborts'
fragment `Ab'` of its own (`hresL`: the context's own aborts' fragment
need not contain the aborts at the extended placement), every such
fragment inside `Ab₀`.

- `stkOk_nil_of_one`: at a context at one frame, the records are none;
- `landStk_segH`: the landing's segment from the allocating frame's
  `ResumeCx2T` at its own aborts, the bottom frames' exits (`hbot`) and
  `Ab₀` (`hAbQ`) ending nowhere.
-/
import Spike.Lib.LowerX64.ResumeCx2T

namespace Spike.Lib.LowerX64

open CoreLang CoreTerm
open Kraken Kraken.Promising Kraken.Promising.X64 Kraken.Promising.Lower.X64
open Spike.Lib Spike.Lib.X64 Spike.Lib.X64.Flow
open Scc.Emit.X64 (i64 rel)
open Scc.Lower.InvX64
open Spike.Lib.LowerNode
open Spike.Lib.LowerShape (newBufTy)
open Scc.Lower.Inv (regName)
open Spike.Lib.X64.Flow.NewBuf (allocAbortDepth)
open Spike.Lib.Consumer1 Spike.Lib.X64Consumer Spike.Lib.X64ConsumerS Spike.Lib.X64ConsumerA
open Scc.Sem Scc.Sem.X64 Scc.Cert.WideX64 A9NoSpawn

section LandH

variable {p : Prog} {exe : _root_.Executable} {cells : List (Directive × Nat)}
  {endPc : Int64} {RaOk : BitVec 64 → Prop} {Cd : BitVec 64 → Int64 → List (Directive × Nat) → Prop}
  {i : Expr → String → Nat → Option Nat} {T : Nat → Expr → Prop} {P : Prog}
  {hcode : ∀ (j : Nat) d, P[j]? = some d → FnCode2 exe cells endPc RaOk Cd i (T j) d}
  {CxOk : Nat → Region → (MachineData → Prop) → List TermRun.Frame → BitVec 64 → BitVec 64 → UInt64 →
    (Ctl → Prop) → FragS isa → Prop} {Bot : StkKey → List TermRun.Frame → Prop}

/-- **At a context at one frame, no records**: a record below the running
frame is a context at the frames below it (`StkFrOk.cx`), which have one
frame too, so the running frame would have two. -/
theorem stkOk_nil_of_one {lbl : WeakMem.AllocLabel → Option Nat} {lsize : WeakMem.AllocLabel → Nat}
    (hone : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → fs.length = 1) :
    ∀ {k : StkKey} {st : List StkFr} {fs : List TermRun.Frame}, fs.length = 1 →
      StkOk (p := p) (lbl := lbl) (lsize := lsize) hcode CxOk Bot k st fs → st = []
  | _, [], _, _, _ => rfl
  | _, _ :: _, [], _, h => absurd h stkOkB_cons_nil
  | _, _ :: _, _ :: fs, h1, h => by
    have h2 := hone _ _ _ _ _ _ _ _ _ (StkFrOk.cx (StkOk.uncons h).1).1
    simp only [List.length_cons] at h1
    omega

variable [Kraken.Executable.ValidLayout exe]

/-- **A landing's segment at contexts at one frame** (`landStk_segT` with
no records and the allocating frame's own aborts): the allocating frame's
`ResumeCx2T` at `Tr j` at some aborts' fragment `Ab'` inside `Ab₀`
(`hresL`), the continuation's walk inside `Tr j` (`hTr`); no record below
it (`hone`, `stkOk_nil_of_one`), so its exits are the bottom key's
(`hbot`); the allocation's own aborts at `Ab'`. -/
theorem landStk_segH {W : Lbl → Lsize → FragS isa} {K : State → State → Prop}
    {ms : Lbl → Lsize → List TermRun.Frame → MemSide isa} {Ab₀ Q : FragS isa}
    {L : Lbl} {ls : Lsize} {l : WeakMem.AllocLabel} {b w : Nat} (hl : L l = none) (hz : ls l = 0)
    {Tr : Nat → Expr → Prop}
    (hone : ∀ j R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → fs.length = 1)
    (hTn : ∀ j d, P[j]? = some d → ∀ x cn τ e, T j (.let_ x (.newBuf cn τ) e) → Scc.Lower.elem2 τ = true)
    (hAW : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab → RaOk ra →
      (rbR R).lo ≤ -allocAbortDepth ((hcode j d hd).fr.size : Int) ∧
      AllocStoreAt p L ls (hcode j d hd).lcx (hcode j d hd).fr (Cd ra) ((hcode j d hd).Bl ra)
        (fun L ls s c => W L ls s c fs) K exe endPc (rbR R) F (ms L ls fs) fp ra tp G0 i (T j) (RetLk d.retTy))
    (hTr : ∀ j d, P[j]? = some d → ∀ x cn τ e t, T j (.let_ x (.newBuf cn τ) e) → TailOf t e → Tr j t)
    (hresL : ∀ j d (hd : P[j]? = some d) R F fs fp ra tp G0 Ab, CxOk j R F fs fp ra tp G0 Ab →
      Bot ⟨j, R, F, fp, ra, tp, G0⟩ fs → RaOk ra →
      ∃ Ab' : FragS isa, (∀ s c fs', Ab' s c fs' → Ab₀ s c fs') ∧
        ResumeCx2T (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
          (AllocReach.updN ls l w) (ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
          (hcode j d hd) R F fs fp ra tp G0 Ab' (Tr j))
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
  obtain ⟨j, d, hd, R, F, F', fp, ra, tp, G0, Ab, c0, pc, pcB, x, cn, τ, e, env, n, lits, cs, bufs, h, kv, u, la,
    zs, zc, kk, q, hcx, hra, hc0, hpt, hnb, hla, hzs, hcla, hbl, hpcB, -, hF', hctx, hAt, htp⟩ := hE
  subst hpcB
  obtain ⟨hlo, hAWi⟩ := hAW j d hd R F fs fp ra tp G0 Ab hcx.1 hra
  -- no records below the allocating frame: its key is a bottom key
  have hB : Bot ⟨j, R, F, fp, ra, tp, G0⟩ fs := by
    obtain ⟨hc1, st, hst⟩ := hcx
    have hst0 : st = [] := stkOk_nil_of_one hone (hone _ _ _ _ _ _ _ _ _ hc1) hst
    subst hst0
    exact StkOk.bot_drop (st := []) hst
  obtain ⟨Ab', hAb', -, hFs, hR, hlo8, hhi8, hG0, hBl, W₀, hW₀, hW, hWp, hab, hcon⟩ :=
    hresL j d hd R F fs fp ra tp G0 Ab hcx.1 hB hra
  obtain ⟨hFr, hRr, -, hhir⟩ := rbR_facts hFs hR hlo8 hhi8
  obtain ⟨hfr, hT, tk', kv', en, em, hh, kk1, kk1', pc', hat', hco', hhd', hptc, hi, hIt, hIc, hlb, hpt'⟩ :=
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
  -- the landing's call is the allocation's: its loads, cell sizes and `callq`
  obtain ⟨lw, off, zs', zc', z, hlw, hoff, hz', hcla', hbl', hcls, -, hpc'⟩ := instsC2_newBuf hi
  rw [hla] at hlw
  cases hlw
  have hCd := (hcode j d hd).hCd ra hra
  have hzs' : zs = zs' := cdOf_zip_sizes s hAt.1 hAt.2.1 hzs hz' (hCd _ _ hcla) (hCd _ _ hcla')
  subst hzs'
  have hzc : [zc] = [zc'] :=
    cdOf_zip_sizes (ds := [_]) s hAt.1 hAt.2.1 rfl rfl (hBl _ _ _ _ hbl) (hBl _ _ _ _ hbl')
  cases hzc
  subst hpc'
  have hWls := (hAWi c0 pc kk1 x cn τ e env n lits cs bufs tk kv en em h hc0 hT hfr hat hco hhd hptc la off zs zc
    z kk hla hoff hzs hcla hbl hcls)
  -- the count held: the call's element type is the allocation's
  have hkz : q.1.n ≤ AllocReach.updN ls l w l := by
    obtain ⟨-, -, -, -, σ, -, hFm, hJ⟩ := id hAt
    obtain ⟨-, -, -, -, -, -, -, -, us, hus, hw⟩ := hJ
    obtain ⟨mC, σC, c1, -, ⟨σ0, hJ1, -⟩, hN, -⟩ := hctx _ hFm
    obtain ⟨-, -, -, -, -, -, -, Lx, sm, B, hNJ, -⟩ := hJ1
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
    (W₀ := fun s c => W (AllocReach.upd L l b) (AllocReach.updN ls l w) s c fs) (Ab := Ab') (w := w)
    (hcode j d hd).hf (hcode j d hd).h1 hFr hRr hlo hhir (fun _ _ h => h) (hcode j d hd).lcx.prog he2 hfr hoff
    (hCd _ _ hcls) (hWls _ _ hv.1 hv.2) hIt hIc hlb q.2 hF' hctx hv.1 hl' hv.2 hkz
    (ms' := ms (AllocReach.upd L l b) (AllocReach.updN ls l w))
  refine (s1.mono_pre fun s' c' fs' ⟨h1, h2, h3⟩ => ⟨h1 ▸ h2 ▸ ⟨hAt, htp⟩, h3⟩).seq (SegWS.or_pre ?_ ?_)
  · -- the body at the extended placement at `Tr j`, no records below it, the bottom's exits
    refine (SegWS.exists_pre (P := fun c0' s' c' fs' => FrameRunM p (c0, fs) (c0', fs) ∧
      LetAt p (AllocReach.upd L l b) (AllocReach.updN ls l w) i (hcode j d hd).fr exe endPc (rbR R) F fp ra tp
        c0' fs (pc + Int64.ofNat zs.sum + Int64.ofNat zc + Int64.ofNat z) e
        ((x, newBufTy τ, [.reg (regName x n), Scc.Lower.imm 0]) :: env)
        ((x, Scc.Lower.opLit (hcode j d hd).lcx.prog lits (.newBuf cn τ)) :: lits)
        (Scc.Lower.csAfter x cs (.newBuf cn τ)) (Scc.Lower.bufsAfter x cs bufs (.newBuf cn τ)) s' c' fs')
      fun c0' => ?_).mono_pre fun s' c' fs' ⟨hfs, c0', hr, hA⟩ => ⟨c0', hr, hA, hfs⟩
    by_cases hr : FrameRunM p (c0, fs) (c0', fs)
    · have hg0 := hG0 _ _ hc0 hr
      have s2 := bodyAtPt2WT (hcode j d hd) hra hFs hR hlo8 hhi8 hW₀ hG0 hW hWp hab hcon hpt' hg0
        fun q hq => hTr j d hd x cn τ e q.1 hT (lowerEnvs2_tail e _ _ q hq)
      have s3 : SegWS (W (AllocReach.upd L l b) (AllocReach.updN ls l w)) K p (AllocReach.upd L l b)
          (ms (AllocReach.upd L l b) (AllocReach.updN ls l w)) _
          (ExitStk p P (AllocReach.upd L l b) exe endPc ⟨j, R, F, fp, ra, tp, G0⟩ fs Ab₀) :=
        s2.mono_post fun s c fs' h' => ⟨c0', d.retTy, hg0, ⟨d, hd, rfl⟩, h'.imp_right (hAb' s c fs')⟩
      exact (s3.seq (hbot _ _ hB)).mono_pre fun _ _ _ h => h.2
    · exact SegWS.empty fun _ _ _ h => hr h.1
  · exact hAbQ.mono_pre fun s c fs h => hAb' s c fs h

end LandH

end Spike.Lib.LowerX64

-- No axioms beyond Lean's.

/-- info: 'Spike.Lib.LowerX64.stkOk_nil_of_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.stkOk_nil_of_one

/-- info: 'Spike.Lib.LowerX64.landStk_segH' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Spike.Lib.LowerX64.landStk_segH
