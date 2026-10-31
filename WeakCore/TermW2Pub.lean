import WeakCore.TermW2Core
import WeakCore.TermB5

namespace W2Pub

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (W2) **`PubWordWF`**: the stepper's promise at a newly shared cell, at a multi-word
segment initialised in the post-step environment `E'`.  `Inh E'` gives a value of the
segment in `E'` (its references name published cells or boxes of `E'`); the certificate's
`WordOK` value in `E2 ⊇ E'` is spliced into it at the promise's `.one` unit (`TearOK`,
`PromNoTwoOK`), and the result moves back to `E'` by `ValOf_monoK`. -/
theorem pubWordW_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrunT : CertRunT p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hagree : RunAgreeT p k arch Sp Init MintOK c0) (hbp : BufInitPubT p k arch Sp Init MintOK c0)
    (hbtr : BufInitPubTR p k arch Sp Init MintOK c0)
    (hclos : PubClosT p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PubWordWF p k arch Sp Init MintOK c0 := by
  intro c c' Eg Tot HP HS cr db i th r S ρ η cx Rf Rs E' Tot' HP' HS' C F cr' db' δ crS X Y Z hPub hPfrP hS l f hn0 hf t m ht hm hl cl hcl
    hI b S' us hseg hus h1 hb ho
  have hF := Z.1
  have hRE := Z.2.1
  have hmE := Z.2.2.1
  have hAP := TermXFO.anchPost (hV0 := hV0) X Y.1 (Z.toC Rf Rs (HP i + HS) (cr i) (db i)) hS hPfrP (hrunT X S hS).1
  have hCE : CE η = Cut Eg i S := Y.1
  have hg := TermTyped.gOf_thread X.hc'
  have hSC0 : StoClo (CE η) := by
    rw [hCE]; exact fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  have hst : stOf c'.mem c'.pairs r.2.2 = stOf r.1 r.2.1 r.2.2 := by rw [X.e1, X.e2]
  have h0X := TermXFO.InvAtXFO_ofA (hTy := (TermNoHold.TCtxX.tyPost X hCE hF (TermMain.TOut.newTy Z)).1) (hRc := (TermNoHold.TCtxX.tyPost X hCE hF (TermMain.TOut.newTy Z)).2) (p := p) (k := k) (arch := arch) (Ea := Cut Eg i S) X.e3 hRE.thInvE (by rw [hg, hst]; exact hmE)
    (StoClo_EFoot hF hSC0) (by rw [hg]; exact X.inv.bf) (by rw [hst]; exact hAP.1) (.inr hAP.2) (IniZTK Eg Tot HP i th) (TermTyped.WitP c'.mem r.2.2.promises)
  have hrlE : ∀ l, E'.rini l ≤ E'.ini l := hF.2.2.2.2.2.2.2.2.2.2.1 (fun l => by rw [hCE]; exact X.inv.rle l)
  have hHrT := TermTyped.witP_run (p := p) (k := k) (arch := arch) X.e3
    (fun t ht => by rw [X.e1]; exact hmE.2.2.1 t ht) (TermCert.winInv_refl X.e3)
  have hsc := fun c1 h1 h2 => ((hrunT X S hS).2 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => ((hrunT X S hS).2 c1 h1 h2).2
  have ht' : t ∈ TermFul.promsOf c' i := by rw [TermFul.promsOf_some X.e3]; exact ht
  obtain ⟨hnf, hCl, hcl'⟩ := TermPlantF.pubCell_of X Y Z hn0 hf hcl
  -- the step publishes `l`, so the stepper's credits are the thread's
  have hPl : TermOwnG0Defs.PubAt th l := hPfrP l (by rw [hCl]; exact Option.some_ne_none _)
    (by rw [hf, hCE]; show some f ≠ Eg.pfr l; rw [hn0]; exact Option.some_ne_none _)
  have hcrS : crS = cr i := funext (hPub l hPl)
  subst hcrS
  have ZC := Z.toC Rf Rs (HP i + HS) (cr i) (db i)
  have hlt : t < c'.mem.size := TermPlant.lt_size_of_some hm
  obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2, hIL2, hIH2, hPO2⟩ :=
    TermXFO.certified_promNotUndefXO (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin h0X (TermTyped.tidAt_mono hAP.2 (TermTyped.tidAt_thread X.hc' (TermMain.tidAt_cut X.inv i S))) X.cert hrlE
      (hbtr X Y Z hPfrP) ht' hm (hbp X) hHrT
  obtain ⟨-, hTr, -, hnT, hrT⟩ := hmE.2.2.2.2.2.2.2.2.1.2.2.1 l cl f hcl' hf
  have hnS := noOwn_seg hseg hnT
  have hrS := rgnFree_seg hseg hrT
  -- a value of the segment in `E'`
  have hIS : IniSeg E' cl l b := W2Core.iniSeg_of_initR hseg hus hb hI
  obtain ⟨wsE, hE, hlE⟩ := hmE.2.2.2.2.2.2.2.2.1.2.1 l cl b S' us hcl' hseg hus hIS
  -- no two-word unit at the promise
  have hsT : (EgT Eg (gOf p k arch c i) th.nalloc r.2.2.nalloc E' c').sto m.loc.label = some cl := by
    rw [hl]; simp [EgT, GEnv.withFp, GEnv.post, hnf, hcl]
  have hn := TermB5.promNoTwoOK_thread (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrunT X Y ZC hS hPfrP X.inv.promNoTwo i r.2.2 t m cl X.e3 ht hm hsT
  have hw2' := hw2 cl (by rw [hl]; exact hcl')
  obtain ⟨ws, w0, hV, hL, hget, hle, hmem⟩ := W2Core.rebuild hx2 hseg hus hb ho
    (hTr b S' hseg (by rw [hus]; exact Option.some_ne_none _)) hn hE hlE hw2'
  have hR := hagree X Y Z hPfrP c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2 hIL2 hIH2 hPO2
  have hbi := hm2.2.2.2.2.2.2.2.2.2.1
  have hpvl : m.view < t := by
    obtain ⟨m', hm', hvl⟩ := promViewLt_step (promViewLt_run h0 X.run) (Step.thread i X.hc' X.cert) i r.2.2 t X.e3 ht
    rw [hm] at hm'; cases hm'; exact hvl
  obtain ⟨n, hn1⟩ : ∃ n, c'.mem.size = n + 1 :=
    ⟨c'.mem.size - 1, (Nat.sub_add_cancel (Nat.lt_of_le_of_lt (Nat.zero_le _) hlt)).symm⟩
  have hfb2' : FrBound E' (n + 1) r.2.2.vs.vWr E2 := by rw [← hn1]; exact hfb2
  have hV1 : ValOf E' S' ws := by
    refine ValOf_monoK (G := PlantG E' (fun _ => False)) hnS hrS hus hL
      hx2.2.2.1 hx2.2.2.2.1 (fun l2 c0 hG hc0 => ?_) (fun l2 hG => ?_) (fun l2 f2 hG hf2 => ?_)
      (fun l2 B hG hB => ?_) hR.pay ?_ hV
    · rcases hG with ⟨c1, f1, h1', -⟩ | hF0 | ⟨B, hB⟩
      · rw [hx2.2.2.2.2.1 l2 c1 h1'] at hc0; rw [h1', hc0]
      · exact hF0.elim
      · have := (hbi.2.2 l2 B (hx2.2.2.2.2.2.2.2.2.1 l2 B hB)).1
        rw [hc0] at this; cases this
    · rcases hG with hG | hF0 | ⟨B, hB⟩
      · exact hR.ini l2 (.inl hG)
      · exact hF0.elim
      · rw [(hbi.2.2 l2 B (hx2.2.2.2.2.2.2.2.2.1 l2 B hB)).2.1]; exact Nat.zero_le _
    · rcases hG with ⟨c1, f0, h1', hf0⟩ | hF0 | hB
      · rw [hx2.2.2.2.2.2.2.1 l2 f0 hf0] at hf2
        cases hf2
        exact ⟨_, hf0, Nat.le_refl _⟩
      · exact hF0.elim
      · exact hR.pfr l2 f2 (.inr hB) hf2
    · rcases hG with ⟨c1, f1, h1', -⟩ | hF0 | ⟨B0, hB0⟩
      · have := (hbi.2.2 l2 B hB).1
        rw [hx2.2.2.2.2.1 l2 c1 h1'] at this; cases this
      · exact hF0.elim
      · rw [hx2.2.2.2.2.2.2.2.2.1 l2 B0 hB0] at hB; rw [hB0, hB]
    · intro w1 hw1 a' g hv'
      rcases hmem w1 hw1 with hwE | rfl
      · rcases noJunk_valOf hE hnS hrS hus hlE w1 hwE a' g hv' with ⟨c1, f1, h1', h2', -⟩ | ⟨B, hB, -⟩
        · exact .inl ⟨c1, f1, h1', h2'⟩
        · exact .inr (.inr ⟨B, hB⟩)
      · have hJ := noJunk_valOf hV hnS hrS hus hL w1 hw1 a' g hv'
        have hvm : w1.view ≤ m.view := hle.2 a' g hv'
        have hmv : m.val = .loc a' g := by rw [← hv']; exact hle.1.symm
        rcases FrBound_inspM hfb2' hJ (Nat.lt_of_le_of_lt hvm (Nat.lt_of_lt_of_le hpvl
            (Nat.le_of_lt_succ (show t < n + 1 by rw [← hn1]; exact hlt)))) with ⟨c1, hc1⟩ | ⟨B, hB⟩
        · rcases hpf : E'.pfr a'.label with _ | f1
          · exfalso
            have ho1 := post_own_of_nopfr Y ZC hc1 hpf
            obtain ⟨f', hf'⟩ := hclos X Y ZC hS hPfrP l f hn0 hf t m ht hm hl a' g hmv c1 hc1 ho1
            rw [hpf] at hf'; cases hf'
          · exact .inl ⟨c1, f1, hc1, hpf⟩
        · exact .inr (.inr ⟨B, hB⟩)
  have hV2 := ValOf_transferS (inclS_post (c' := c') Y ZC) (noOR_of S' [] hnS hrS) hV1
  exact ⟨b, S', ws, m.loc.offset - b, w0, hseg,
    ⟨hV2, fun us' hus' => by rw [hus] at hus'; cases hus'; exact hL⟩, hget, hle, by omega⟩

end

end W2Pub

#print axioms W2Pub.pubWordW_of
