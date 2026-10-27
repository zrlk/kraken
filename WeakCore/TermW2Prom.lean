import WeakCore.TermW2Core
import WeakCore.TermB5

namespace W2Prom

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (W2) **`PromWordWF` from its residual `PromWordNewF`**: a promise at a multi-word slot
already initialised at `Eg.ini` (`Inh` of the promiser's cut gives a value there, into which the
certificate's `WordOK` value is spliced at the promise's `.one` unit, `TearOK`/no two-word unit),
moved to the planted environment by `ValOf_monoK`; a slot not initialised at `Eg.ini` is at a
planted label (`plantG` raises `ini` only there) and is `PromWordNewF`. -/
theorem promWordW_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hNew : PromWordNewF p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromWordWF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X t m htm hmm cl hcl hsh hI hlab hpv b S us hseg hus h1 hb ho
  by_cases hIS : IniSegN (Eg.ini m.loc.label) cl b
  rotate_left
  · by_cases hPL : PlantL c Eg j th a v w m.loc.label
    · exact hNew X t m htm hmm cl hcl hPL hpv hI b S us hseg hus h1 hb ho hIS
    · exfalso
      have hI2 := W2Core.iniSeg_of_initR hseg hus hb hI
      have e : (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)).ini m.loc.label =
          Eg.ini m.loc.label := by
        show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini m.loc.label = _
        simp only [plantG, plantOf_none X.hth hPL]
      exact hIS (by have h := hI2; unfold IniSeg at h; rw [e] at h; exact h)
  obtain ⟨S0, hSS0⟩ := X.inv.thr j th X.hth
  obtain ⟨-, hTE, hm, -⟩ := id hSS0
  have hpi := promise_inv (a := a) (v := v) (w := w) X.hth
  have hSC : StoClo (Cut Eg j S0) := fun l cl hl => X.inv.clo l cl (cutSto_sub hl)
  obtain ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, -, -, -, hIH0⟩ := InvAtXF_of (p := p) (k := k) (arch := arch)
    hpi.2.1 hTE (by rw [gOf_promise, hpi.2.2]; exact MemInv_promSt hm) hSC (by rw [gOf_promise]; exact X.inv.bf)
    (by rw [hpi.2.2]; exact TermTyped.riniCoh_promSt (X.inv.riniCoh _ _ _ X.hth))
    (fun l cl f hs hp => Nat.le_trans (X.inv.frlt l cl f (cutSto_sub hs) hp)
      (Nat.sub_le_sub_right (by rw [hpi.1]; show c.mem.size ≤ (c.mem.push _).size; rw [Array.size_push]; exact Nat.le_succ _) 1))
  have hX : InvAtX p k arch j (Cut Eg j S0) _ _ (promise c j a v w) :=
    ⟨th0, E, hth0, hx, hTE0, hm0, hSC0, hbo0, hfb, hfr, fun _ _ _ h => h.elim, hIH0⟩
  have ht : t ∈ TermFul.promsOf (promise c j a v w) j := by
    rw [TermFul.promsOf_some hpi.2.1]; exact htm
  have hmt : (promise c j a v w).mem[t]? = some m := by
    rw [hpi.1]; exact hmm
  have hsc := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).2
  have hXH := TermIni.InvAtXHP_promOf (k := k) (arch := arch) (a0 := a) (vB := v) (w := w) X.hth hTE hm hSC X.inv.bf
    (fun l => X.inv.rle l) (X.inv.riniCoh _ _ _ X.hth)
    (fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp) (IniZK Eg Tot HP j) (TermTyped.WitP c.mem th.promises)
  obtain ⟨-, c2, th2, E2, h2, hc2, hth2, hx2, -, hm2, hw2, hfb2H, hB2, hIL2, hIH2, hPV2, hPO2⟩ :=
    TermIni.certified_promNotUndefXHP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hXH (TermMain.tidAt_cutP X.inv j S0) X.cert (fun l => X.inv.rle l) (hbr X S0) ht hmt (hbp X) (TermTyped.witP_run X.hth hm.2.2.1 (TermCert.winInv_prom (TermCert.winInv_refl X.hth)))
  have hfb2 : FrBound (Cut Eg j S0) (promise c j a v w).mem.size th.vs.vWr E2 := by
    have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
    rw [e]; exact hfb2H
  have hLc0 : ∀ l1, PlantL c Eg j th a v w l1 →
      ∃ cl1, cutSto Eg j l1 = some cl1 ∧ cl1.owner = some j ∧ Eg.pfr l1 = none := fun l1 h => by
    obtain ⟨-, -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, hn1⟩ := h
    subst hal
    exact ⟨cl1, hc1, ho1, hn1⟩
  -- the cell in the promiser's cut, and its type facts
  obtain ⟨hcl0, hTr, hnT, hrT⟩ : (Cut Eg j S0).sto m.loc.label = some cl ∧
      (∀ b S, SegOf cl.ty b S → accs S ≠ none → TearOK S) ∧ Ty.noOwnIn [] cl.ty = true ∧
      rgnFree cl.ty = true := by
    rcases hsh with ⟨f, hf⟩
    by_cases hL : PlantL c Eg j th a v w m.loc.label
    · obtain ⟨l', -, hR⟩ := id hL
      obtain ⟨cl2, hc2, ho2, -, -, hT2, -, h4, h5⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
      rw [hcl] at hc2; cases hc2
      exact ⟨cutSto_own hcl ho2, hT2, h4, h5⟩
    · have hn := plantOf_none X.hth hL
      have h : (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).pfr m.loc.label = some f := hf
      simp only [plantG, hn] at h
      have hc0 : (Cut Eg j S0).sto m.loc.label = some cl := cutSto_shared hcl ⟨f, h⟩
      obtain ⟨-, hT2, -, h4, h5⟩ := hm.2.2.2.2.2.2.2.2.1.2.2.1 m.loc.label cl f hc0 h
      exact ⟨hc0, hT2, h4, h5⟩
  have hnS := noOwn_seg hseg hnT
  have hrS := rgnFree_seg hseg hrT
  -- a value of the segment in the promiser's cut
  obtain ⟨wsE, hE, hlE⟩ := hm.2.2.2.2.2.2.2.2.1.2.1 m.loc.label cl b S us hcl0 hseg hus hIS
  -- no two-word unit at the promise
  have hn : ∀ x, TwoAtT cl.ty x → m.loc.offset ≠ x ∧ m.loc.offset ≠ x + 1 := by
    intro x hx'
    rw [Array.getElem?_push] at hmm
    by_cases et : t = c.mem.size
    · simp only [et, ↓reduceIte] at hmm; cases hmm
      exact promNoTwoP_of (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X cl hcl x hx'
    · simp only [et, ↓reduceIte] at hmm
      have ht0 : t ∈ th.promises := by
        rcases List.mem_append.1 htm with h | h
        · exact h
        · exact absurd (List.mem_singleton.1 h) et
      exact X.inv.promNoTwo j th t m cl X.hth ht0 hmm hcl x hx'
  obtain ⟨ws, w0, hV, hL, hget, hle, hmem⟩ := W2Core.rebuild hx2 hseg hus hb ho
    (hTr b S hseg (by rw [hus]; exact Option.some_ne_none _)) hn hE hlE (hw2 cl hcl0)
  have hR := TermIni.RunAgree_ofW (hagree X S0 c2 th2 E2 h2 hc2 hth2 hx2 hm2 hfb2H hIL2 hIH2 hPV2 hPO2) (TermIni.runAgree_pfrL hB2 (MemInv_promLt hm) (fun l c h => hx2.2.2.2.2.1 l c h)
      (fun l1 h => by obtain ⟨cl1, h1, -, -⟩ := hLc0 l1 h; exact ⟨cl1, h1⟩)
      (fun l1 h => by obtain ⟨-, -, -, hn1⟩ := hLc0 l1 h; exact hn1))
  have hbi := hm2.2.2.2.2.2.2.2.2.2.1
  -- planted labels are own private cells of the promiser
  have hLc : ∀ l1, PlantL c Eg j th a v w l1 →
      ∃ cl1, cutSto Eg j l1 = some cl1 ∧ cl1.owner = some j ∧ Eg.pfr l1 = none := fun l1 h => by
    obtain ⟨-, -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, hn1⟩ := h
    subst hal
    exact ⟨cl1, hc1, ho1, hn1⟩
  have hV1 : ValOf (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) S ws := by
    refine ValOf_monoK (G := PlantG (Cut Eg j S0) (PlantL c Eg j th a v w)) hnS hrS hus hL
      hx2.2.2.1 hx2.2.2.2.1 (fun l c0 hG hc0 => ?_) (fun l hG => ?_) (fun l f hG hf => ?_) (fun l B hG hB => ?_)
      hR.pay ?_ hV
    · show (Cut Eg j S0).sto l = some c0
      rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B, hB⟩
      · rw [hx2.2.2.2.2.1 l c1 h1'] at hc0; rw [h1', hc0]
      · obtain ⟨c1, h1', -⟩ := hLc l hLa
        have h1'' : (Cut Eg j S0).sto l = some c1 := h1'
        rw [hx2.2.2.2.2.1 l c1 h1''] at hc0; rw [h1'', hc0]
      · have := (hbi.2.2 l B (hx2.2.2.2.2.2.2.2.2.1 l B hB)).1
        rw [hc0] at this; cases this
    · rcases hG with hG | hLa | ⟨B, hB⟩
      · exact hR.ini l (.inl hG)
      · exact hR.ini l (.inr hLa)
      · rw [(hbi.2.2 l B (hx2.2.2.2.2.2.2.2.2.1 l B hB)).2.1]; exact Nat.zero_le _
    · rcases hG with ⟨c1, f0, h1', hf0⟩ | hLa | hB
      · have hnL : ¬ PlantL c Eg j th a v w l := fun hLa => by
          obtain ⟨-, -, -, hn1⟩ := hLc l hLa
          have : (Cut Eg j S0).pfr l = none := hn1
          rw [this] at hf0; cases hf0
        rw [hx2.2.2.2.2.2.2.1 l f0 hf0] at hf
        cases hf
        exact ⟨_, by rw [plantE_pfr_ne hnL]; exact hf0, Nat.le_refl _⟩
      · exact hR.pfr l f (.inl hLa) hf
      · exact hR.pfr l f (.inr hB) hf
    · show (Cut Eg j S0).box l = some B
      rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B0, hB0⟩
      · have := (hbi.2.2 l B hB).1
        rw [hx2.2.2.2.2.1 l c1 h1'] at this; cases this
      · obtain ⟨c1, h1', -⟩ := hLc l hLa
        have := (hbi.2.2 l B hB).1
        rw [hx2.2.2.2.2.1 l c1 h1'] at this; cases this
      · rw [hx2.2.2.2.2.2.2.2.2.1 l B0 hB0] at hB; rw [hB0, hB]
    · intro w1 hw1 a' g hv'
      rcases hmem w1 hw1 with hwE | rfl
      · rcases noJunk_valOf hE hnS hrS hus hlE w1 hwE a' g hv' with ⟨c1, f1, h1', h2', -⟩ | ⟨B, hB, -⟩
        · exact .inl ⟨c1, f1, h1', h2'⟩
        · exact .inr (.inr ⟨B, hB⟩)
      have hJ := noJunk_valOf hV hnS hrS hus hL w1 hw1 a' g hv'
      have hvm : w1.view ≤ m.view := hle.2 a' g hv'
      have hmv : m.val = .loc a' g := by rw [← hv']; exact hle.1.symm
      have hfb2' : FrBound (Cut Eg j S0) (c.mem.size + 1) th.vs.vWr E2 := by
        have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
        rw [e] at hfb2; exact hfb2
      rcases FrBound_inspM hfb2' hJ (Nat.lt_of_le_of_lt hvm hpv) with ⟨c1, hc1⟩ | ⟨B, hB⟩
      · rcases hpf : (Cut Eg j S0).pfr a'.label with _ | f
        · -- an own private unplanted cell named by the promise: a plant edge from `m.loc.label`
          have ho1 : c1.owner = some j := by
            rcases (cutSto_some.1 hc1).2 with h | ⟨f2, hf2⟩
            · exact h
            · have : Eg.pfr a'.label = none := hpf
              rw [this] at hf2; cases hf2
          have hroot : ClR (PlantR (cutP Eg j) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size])) a.label
              m.loc.label := by
            rcases hlab with h | ⟨l', h1', hR'⟩
            · rw [h]; exact ClR.base
            · exact ClR.step h1' hR'
          exact .inr (.inl ⟨m.loc.label, hroot, ⟨t, htm, m, hmm, rfl, ⟨cl, hcl0, hnT, hrT⟩, a', g, hmv, rfl, c1, hc1,
            ho1, hpf⟩⟩)
        · exact .inl ⟨c1, f, hc1, hpf⟩
      · exact .inr (.inr ⟨B, hB⟩)
  have hV2 := ValOf_transferS (InclS_cut_pub (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j S0)
    (noOR_of S [] hnS hrS) (ValOf_transferS (inclS_plantE X S0 j S0) (noOR_of S [] hnS hrS) hV1)
  exact ⟨b, S, ws, m.loc.offset - b, w0, hseg,
    ⟨hV2, fun us' hus' => by rw [hus] at hus'; cases hus'; exact hL⟩, hget, hle, by omega⟩

end

end W2Prom

#print axioms W2Prom.promWordW_of
