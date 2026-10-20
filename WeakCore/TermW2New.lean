import WeakCore.TermW2Prom
import WeakCore.TermLiveProps

/-!
# TermW2New (D2): the W2 residual `PromWordNewF`

A newly planted multi-word slot (above `Eg.ini`, below the planted count `NpZ`) carries an own
outstanding promise of the promiser at every word (`PrefixHeld_NpZ`); hence (`PromNoTwoOK`) all its
units are `.one`.  At the end `cF` of the promiser's certified completion run every one of these
promises is fulfilled, so `MemOKP` types all of them in the one environment `EF` (`WordOK`).  The
per-word values are assembled unit by unit (`TearOK`, `assembleSlot`) into one value whose words are
all promise words (views below the step: `PlantG` labels), which `ValOf_monoK` (`RunAgreeF` at `cF`)
moves to the planted environment.
-/

namespace W2New

open CoreLang CoreTerm CoreTyping TermRun TermClose TermTv TermSound TermMem TermStep TermCut TermSys
  TermStepper TermCert TermGlob TermTyped TermMain TermInterf TermNoHold TermPlantF
open WeakMem (Val Msg Memory Address VState Ts Arch AllocLabel)

/-- Memory only grows along a solo run. -/
theorem solo_mem {p : Prog} {k : Promises.Knobs} {arch : Arch} {i : Nat} {c c' : Cfg}
    (h : Solo p k arch i c c') {t : Nat} {m : Msg} (hm : c.mem[t]? = some m) : c'.mem[t]? = some m := by
  revert hm
  induction h with
  | refl => exact id
  | thread hs _ ih =>
    intro hm
    exact ih (by rw [(TermLiveProps.threadSteps_ext hs).get t (TermMem.lt_of_get hm)]; exact hm)
  | prom a v w _ _ ih =>
    intro hm
    exact ih (by rw [(TermLiveProps.promise_ext _ _ a v w).get t (TermMem.lt_of_get hm)]; exact hm)

/-- (slot-level) A `WordOK` word at an offset of a segment is a word of a value of that segment. -/
theorem wordOK_seg {E : TEnv} {T S : Ty} {b o : Nat} {us : List Acc} {w : Word}
    (hseg : SegOf T b S) (hu : accs S = some us) (hb : b ≤ o) (ho : o < b + nWords us) (hw : WordOK E T o w) :
    ∃ W w0, ValOf E S W ∧ W.length = nWords us ∧ W[o - b]? = some w0 ∧ WLe1 w0 w := by
  obtain ⟨b2, S2, ws2, o2, w0, hseg2, ⟨hv2, hsh2⟩, hw0, hle, hbo2⟩ := hw
  obtain ⟨us2, hus2⟩ : ∃ us2, accs S2 = some us2 := by
    rcases hseg2 with ⟨-, rfl, hA⟩ | ⟨N, us2, jj, -, hus2, -, -⟩
    · exact Option.ne_none_iff_exists'.1 hA
    · exact ⟨us2, hus2⟩
  have hl2 : ws2.length = nWords us2 := hsh2 us2 hus2
  have ho2 : o2 < ws2.length := (List.getElem?_eq_some_iff.1 hw0).1
  obtain ⟨rfl, rfl⟩ := W2Core.seg_uniq hseg hseg2 hu hus2 hb ho (by omega) (by omega)
  rw [hu] at hus2; cases hus2
  have eo : o2 = o - b := by omega
  subst eo
  exact ⟨ws2, w0, hv2, hl2, hw0, hle⟩

/-- (slot-level) **Unit-by-unit assembly**: at a segment type all of whose word positions start a
`.one` unit, values (in one environment) carrying a good word at each position assemble into one
value good at every position. -/
theorem assembleSlot {E : TEnv} {S : Ty} {us : List Acc} {Q : Nat → Word → Prop}
    (hT : TearOK S) (hu : accs S = some us) (hpos : 0 < nWords us)
    (hone : ∀ x, x < nWords us → ∃ i, us[i]? = some .one ∧ x = nWords (us.take i))
    (hW : ∀ x, x < nWords us → ∃ W, ValOf E S W ∧ W.length = nWords us ∧ ∃ w, W[x]? = some w ∧ Q x w) :
    ∃ V, ValOf E S V ∧ V.length = nWords us ∧ ∀ x w, V[x]? = some w → Q x w := by
  have key : ∀ n, n ≤ nWords us → ∃ V, ValOf E S V ∧ V.length = nWords us ∧
      ∀ x w, x < n → V[x]? = some w → Q x w := by
    intro n
    induction n with
    | zero =>
      intro _
      obtain ⟨W, hV, hl, -⟩ := hW 0 hpos
      exact ⟨W, hV, hl, fun x w hx => absurd hx (Nat.not_lt_zero _)⟩
    | succ n ih =>
      intro hn
      obtain ⟨V, hV, hl, hQ⟩ := ih (Nat.le_of_succ_le hn)
      obtain ⟨W, hW', hlW, w, hw, hQw⟩ := hW n hn
      obtain ⟨i, hi, e⟩ := hone n hn
      obtain ⟨hV2, hl2⟩ := W2Core.splice_unit hT hu hi hV hW' hl hlW
      rw [← e] at hV2 hl2
      refine ⟨_, hV2, hl2, fun x w' hx hx' => ?_⟩
      rcases W2Core.splice1_get (hl.trans hlW.symm) (by omega) x w' hx' with ⟨hxn, h⟩ | ⟨hne, h⟩
      · subst hxn; rw [hw] at h; cases h; exact hQw
      · exact hQ x w' (by omega) h
  obtain ⟨V, hV, hl, hQ⟩ := key _ (Nat.le_refl _)
  exact ⟨V, hV, hl, fun x w h => hQ x w (by rw [← hl]; exact (List.getElem?_eq_some_iff.1 h).1) h⟩

section
variable {p : Prog} {k : Promises.Knobs} {arch : Arch} {Init : Res} {MintOK : Res → Prop} {c0 : Cfg}
variable {Sp : TermRun.Cfg → TermRun.Cfg → Prop}

/-- (W2) **`PromWordNewF`**: a promise at a newly planted multi-word slot. -/
theorem promWordNew_of (hV0 : TermViewInv.ViewInvR p k arch Sp c0) [ProgRetIall p] [TermTyped.WrIniC] (hP : ProgT p) (hrun : CertRunP p k arch Sp Init MintOK c0)
    (h0 : TermPlantF.PromViewLtR p k arch Sp c0) (hagree : RunAgreeF p k arch Sp Init MintOK c0) (hbp : BufInitPubF p k arch Sp Init MintOK c0) (hbr : BufInitPubFR p k arch Sp Init MintOK c0) (hPS : PwSkel) (hSub : PwSubS) (hSig : PwSig) :
    PromWordNewF p k arch Sp Init MintOK c0 := by
  intro c Eg Tot HP HS cr db j th a v w X t m htm hmm cl hcl hPL hpv hI b S us hseg hus h1 hb ho hnIS
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
  have hsc := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).1
  have hwin := fun c1 h1 h2 => (hrun X S0 hSS0 c1 h1 h2).2
  -- the planted cell
  obtain ⟨l', -, hR⟩ := id hPL
  obtain ⟨cl2, hc2, ho2, -, -, hTr, -, hnT, hrT⟩ := plant_facts (hV0 := hV0) (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hrun X hR
  rw [hcl] at hc2; cases hc2
  have hcl0 : (Cut Eg j S0).sto m.loc.label = some cl := cutSto_own hcl ho2
  have hcP : (cutP Eg j).sto m.loc.label = some cl := by
    obtain ⟨-, -, t1, -, m1, -, -, -, a1, g1, -, hal, cl1, hc1, -, -⟩ := hPL
    have hc1' : (cutP Eg j).sto m.loc.label = some cl1 := hc1
    have e := cutSto_sub hc1'
    rw [hcl] at e; cases e; exact hc1'
  have hnS := noOwn_seg hseg hnT
  have hrS := rgnFree_seg hseg hrT
  have hseg0 := hseg
  -- the slot: above the start count, below the planted count
  rcases hseg with ⟨-, rfl, hA⟩ | ⟨N, us2, jj, hT, hus2, -, rfl⟩
  · exact absurd (fun N e hT => by rw [hT] at hA; simp [accs] at hA) hnIS
  rw [hus] at hus2; cases hus2
  have hb' : jj * nWords us ≤ m.loc.offset := hb
  have ho' : jj * nWords us + nWords us > m.loc.offset := ho
  have hpos : 0 < nWords us := by omega
  have hge : Eg.ini m.loc.label ≤ jj := Nat.le_of_not_lt fun hlt =>
    hnIS fun N' e' hT' => by
      rw [hT] at hT'
      simp only [Ty.array.injEq, Idx.lit.injEq] at hT'
      obtain ⟨-, rfl⟩ := hT'
      exact ⟨us, jj, hus, hlt, rfl⟩
  have hpl : plantOf c Eg j a v w m.loc.label =
      some (plantF (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label) := by
    unfold plantOf; rw [X.hth]; dsimp only; simp [hPL]
  have hjN : jj < NpZ (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label := by
    have hi : (PubE (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size)).ini m.loc.label =
        max (Eg.ini m.loc.label) (NpZ (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label) := by
      show (plantG Eg (plantOf c Eg j a v w) (plantN c Eg j a v w)).ini m.loc.label = _
      simp only [plantG, hpl, plantN, X.hth]
    have h2 := hI N S us hT hus
    rw [hi] at h2
    have h3 : jj * nWords us < max (Eg.ini m.loc.label) (NpZ (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label) *
        nWords us := Nat.lt_of_le_of_lt hb h2
    have h4 := Nat.lt_of_mul_lt_mul_right h3
    rcases Nat.le_total (Eg.ini m.loc.label) (NpZ (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label) with h | h
    · rw [Nat.max_eq_right h] at h4; exact h4
    · rw [Nat.max_eq_left h] at h4; omega
  -- every word of the slot carries an own outstanding promise
  have hheld : ∀ x, x < nWords us → ∃ u ∈ th.promises, ∃ mu, c.mem[u]? = some mu ∧
      mu.loc = ⟨m.loc.label, jj * nWords us + x⟩ := by
    intro x hx
    have hoN : jj * nWords us + x < NpZ (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label * nWords us := by
      have : (jj + 1) * nWords us ≤ NpZ (cutP Eg j) (stOf c.mem c.pairs th) m.loc.label * nWords us :=
        Nat.mul_le_mul_right _ hjN
      rw [Nat.succ_mul] at this; omega
    rcases PrefixHeld_NpZ hcP N S us hT hus _ hoN with hI0 | ⟨u, hu, mu, hmu, hloc⟩
    · have h5 : jj * nWords us + x < Eg.ini m.loc.label * nWords us := hI0 N S us hT hus
      have : Eg.ini m.loc.label * nWords us ≤ jj * nWords us := Nat.mul_le_mul_right _ hge
      omega
    · exact ⟨u, hu, mu, hmu, hloc⟩
  -- hence every unit of the slot is `.one`
  have hone : ∀ x, x < nWords us → ∃ i, us[i]? = some .one ∧ x = nWords (us.take i) := by
    intro x hx
    obtain ⟨u, hu, mu, hmu, hloc⟩ := hheld x hx
    have hcu : Eg.sto mu.loc.label = some cl := by rw [hloc]; exact hcl
    obtain ⟨i, hi, e⟩ := W2Core.oneAt_of_noTwoT (o := jj * nWords us + x) hseg0 hus (by omega) (by omega)
      (fun x' hx' => by
        have := X.inv.promNoTwo j th u mu cl X.hth hu hmu hcu x' hx'
        rw [hloc] at this; exact this)
    exact ⟨i, hi, by omega⟩
  -- the completion run and its environment
  obtain ⟨cF, hsF, hnpF⟩ := X.cert
  have hcF : Certified p k arch cF j := ⟨cF, .refl _, hnpF⟩
  have hXH := TermIni.InvAtXHP_promOf (k := k) (arch := arch) (a0 := a) (vB := v) (w := w) X.hth hTE hm hSC X.inv.bf
    (fun l => X.inv.rle l) (X.inv.riniCoh _ _ _ X.hth)
    (fun l cl f hs hp => X.inv.frlt l cl f (cutSto_sub hs) hp) (IniZK Eg Tot HP j) (TermTyped.WitP c.mem th.promises)
  obtain ⟨thF, EF, hthF, hxF, hTEF, hmF, hSCF, hboF, hfbFH, hfrF, hBF, hILF, hIHF, hPVF, hPOF⟩ :=
    TermIni.solo_typedXHP (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hXH hsF hcF (fun l => X.inv.rle l) (hbr X S0) (hbp X) (TermTyped.witP_run X.hth hm.2.2.1 (TermCert.winInv_prom (TermCert.winInv_refl X.hth)))
  have hfbF : FrBound (Cut Eg j S0) (promise c j a v w).mem.size th.vs.vWr EF := by
    have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
    rw [e]; exact hfbFH
  have hLc0 : ∀ l1, PlantL c Eg j th a v w l1 →
      ∃ cl1, cutSto Eg j l1 = some cl1 ∧ cl1.owner = some j ∧ Eg.pfr l1 = none := fun l1 h => by
    obtain ⟨-, -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, hn1⟩ := h
    subst hal
    exact ⟨cl1, hc1, ho1, hn1⟩
  have hnoP : thF.promises = [] := by
    simp only [noPromises, hthF, Option.map_some, Option.getD_some, List.isEmpty_iff] at hnpF
    exact hnpF
  have hWF : ∀ u mu, u ∈ th.promises ++ [c.mem.size] → (c.mem.push ⟨a, v, w⟩)[u]? = some mu →
      mu.loc.label = m.loc.label → WordOK EF cl.ty mu.loc.offset (mw mu) := by
    intro u mu hu hmu hL
    have hu' : u ∈ TermFul.promsOf (promise c j a v w) j := by rw [TermFul.promsOf_some hpi.2.1]; exact hu
    have hmu' : (promise c j a v w).mem[u]? = some mu := by rw [hpi.1]; exact hmu
    have hnu := (certified_promNotUndefX (hPS := hPS) (hSub := hSub) (hSig := hSig) hP hsc (by first | exact TermViewInv.viewInv_prom (TermViewInv.viewInv_run hV0 X.run) X.hw | exact TermViewInv.viewInv_run hV0 X.run | exact TermViewInv.viewInv_thread (TermViewInv.viewInv_run hV0 X.run) X.hc') hwin hX X.cert hu' hmu').1
    have hsto : EF.sto mu.loc.label = some cl := by rw [hL]; exact hxF.2.2.2.2.1 _ _ hcl0
    rcases hmF.1.1 u mu cl (by show u ∉ thF.promises; rw [hnoP]; exact List.not_mem_nil) (solo_mem hsF hmu')
      hsto with h | h
    · exact absurd h hnu
    · exact h
  have hfbF' : FrBound (Cut Eg j S0) (c.mem.size + 1) th.vs.vWr EF := by
    have e : (promise c j a v w).mem.size = c.mem.size + 1 := by rw [hpi.1, Array.size_push]
    rw [e] at hfbF; exact hfbF
  -- promise words name `PlantG` labels
  have hgood : ∀ u mu W w0, u ∈ th.promises ++ [c.mem.size] → (c.mem.push ⟨a, v, w⟩)[u]? = some mu →
      mu.loc.label = m.loc.label → mu.view < c.mem.size → ValOf EF S W → W.length = nWords us → w0 ∈ W →
      WLe1 w0 (mw mu) → ∀ (a' : Address) (g : Nat), w0.val = .loc a' g →
        PlantG (Cut Eg j S0) (PlantL c Eg j th a v w) a'.label := by
    intro u mu W w0 hu hmu hL hvu hV hlW hw0 hle a' g hv'
    have hJ := noJunk_valOf hV hnS hrS hus hlW w0 hw0 a' g hv'
    have hvm : w0.view ≤ mu.view := hle.2 a' g hv'
    have hmv : mu.val = .loc a' g := by rw [← hv']; exact hle.1.symm
    rcases FrBound_inspM hfbF' hJ (Nat.lt_of_le_of_lt hvm hvu) with ⟨c1, hc1⟩ | ⟨B, hB⟩
    · rcases hpf : (Cut Eg j S0).pfr a'.label with _ | f
      · have ho1 : c1.owner = some j := by
          rcases (cutSto_some.1 hc1).2 with h | ⟨f2, hf2⟩
          · exact h
          · have : Eg.pfr a'.label = none := hpf
            rw [this] at hf2; cases hf2
        have hroot : ClR (PlantR (cutP Eg j) (c.mem.push ⟨a, v, w⟩) (th.promises ++ [c.mem.size])) a.label
            mu.loc.label := by
          rw [hL]; obtain ⟨l1, h1', hR'⟩ := hPL; exact ClR.step h1' hR'
        have hclu : (Cut Eg j S0).sto mu.loc.label = some cl := by rw [hL]; exact hcl0
        exact .inr (.inl ⟨mu.loc.label, hroot, ⟨u, hu, mu, hmu, rfl, ⟨cl, hclu, hnT, hrT⟩, a', g, hmv, rfl, c1, hc1,
          ho1, hpf⟩⟩)
      · exact .inl ⟨c1, f, hc1, hpf⟩
    · exact .inr (.inr ⟨B, hB⟩)
  -- assemble the slot's value in `EF`
  let G := PlantG (Cut Eg j S0) (PlantL c Eg j th a v w)
  obtain ⟨V, hV, hlV, hQ⟩ := assembleSlot (E := EF) (S := S) (us := us)
    (Q := fun x w1 => (∀ (a' : Address) (g : Nat), w1.val = .loc a' g → G a'.label) ∧
      (x = m.loc.offset - jj * nWords us → WLe1 w1 (mw m)))
    (hTr _ S hseg0 (by rw [hus]; exact Option.some_ne_none _)) hus hpos hone (fun x hx => by
      by_cases hxo : x = m.loc.offset - jj * nWords us
      · obtain ⟨W, w0, hW, hlW, hget, hle⟩ := wordOK_seg hseg0 hus hb ho (hWF t m htm hmm rfl)
        refine ⟨W, hW, hlW, w0, by rw [hxo]; exact hget, fun a' g hv' => ?_, fun _ => hle⟩
        exact hgood t m W w0 htm hmm rfl hpv hW hlW (List.mem_of_getElem? hget) hle a' g hv'
      · obtain ⟨u, hu, mu, hmu, hloc⟩ := hheld x hx
        have hmu' : (c.mem.push ⟨a, v, w⟩)[u]? = some mu := by
          rw [Array.getElem?_push]; simp [Nat.ne_of_lt (TermMem.lt_of_get hmu), hmu]
        have huu : u ∈ th.promises ++ [c.mem.size] := List.mem_append_left _ hu
        have hL : mu.loc.label = m.loc.label := by rw [hloc]
        have hoff : mu.loc.offset = jj * nWords us + x := by rw [hloc]
        obtain ⟨vm, hvm, hvl⟩ := promViewLt_run h0 X.run j th u X.hth hu
        rw [hmu] at hvm; cases hvm
        have hvu : mu.view < c.mem.size := Nat.lt_trans hvl (TermMem.lt_of_get hmu)
        obtain ⟨W, w0, hW, hlW, hget, hle⟩ := wordOK_seg hseg0 hus (by rw [hoff]; omega) (by rw [hoff]; omega)
          (hWF u mu huu hmu' hL)
        rw [hoff, Nat.add_sub_cancel_left] at hget
        exact ⟨W, hW, hlW, w0, hget, fun a' g hv' =>
          hgood u mu W w0 huu hmu' hL hvu hW hlW (List.mem_of_getElem? hget) hle a' g hv',
          fun h => absurd h hxo⟩)
  have hlt : V.length > m.loc.offset - jj * nWords us := by rw [hlV]; omega
  obtain ⟨w0, hw0⟩ : ∃ w0, V[m.loc.offset - jj * nWords us]? = some w0 :=
    ⟨V[m.loc.offset - jj * nWords us]'hlt, List.getElem?_eq_getElem hlt⟩
  -- move it to the planted environment
  have hR := TermIni.RunAgree_ofW (hagree X S0 cF thF EF hsF hcF hthF hxF hmF hfbF' hILF hIHF hPVF hPOF) (TermIni.runAgree_pfrL hBF (MemInv_promLt hm) (fun l c h => hxF.2.2.2.2.1 l c h)
      (fun l1 h => by obtain ⟨cl1, h1, -, -⟩ := hLc0 l1 h; exact ⟨cl1, h1⟩)
      (fun l1 h => by obtain ⟨-, -, -, hn1⟩ := hLc0 l1 h; exact hn1))
  have hbi := hmF.2.2.2.2.2.2.2.2.2.1
  have hLc : ∀ l1, PlantL c Eg j th a v w l1 →
      ∃ cl1, cutSto Eg j l1 = some cl1 ∧ cl1.owner = some j ∧ Eg.pfr l1 = none := fun l1 h => by
    obtain ⟨-, -, t, -, m, -, -, -, a', g, -, hal, cl1, hc1, ho1, hn1⟩ := h
    subst hal
    exact ⟨cl1, hc1, ho1, hn1⟩
  have hV1 : ValOf (plantE (Cut Eg j S0) (stOf c.mem c.pairs th) (PlantL c Eg j th a v w)) S V := by
    refine ValOf_monoK (G := G) hnS hrS hus hlV
      hxF.2.2.1 hxF.2.2.2.1 (fun l c0 hG hc0 => ?_) (fun l hG => ?_) (fun l f hG hf => ?_) (fun l B hG hB => ?_)
      hR.pay ?_ hV
    · show (Cut Eg j S0).sto l = some c0
      rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B, hB⟩
      · rw [hxF.2.2.2.2.1 l c1 h1'] at hc0; rw [h1', hc0]
      · obtain ⟨c1, h1', -⟩ := hLc l hLa
        have h1'' : (Cut Eg j S0).sto l = some c1 := h1'
        rw [hxF.2.2.2.2.1 l c1 h1''] at hc0; rw [h1'', hc0]
      · have := (hbi.2.2 l B (hxF.2.2.2.2.2.2.2.2.1 l B hB)).1
        rw [hc0] at this; cases this
    · rcases hG with hG | hLa | ⟨B, hB⟩
      · exact hR.ini l (.inl hG)
      · exact hR.ini l (.inr hLa)
      · rw [(hbi.2.2 l B (hxF.2.2.2.2.2.2.2.2.1 l B hB)).2.1]; exact Nat.zero_le _
    · rcases hG with ⟨c1, f0, h1', hf0⟩ | hLa | hB
      · have hnL : ¬ PlantL c Eg j th a v w l := fun hLa => by
          obtain ⟨-, -, -, hn1⟩ := hLc l hLa
          have : (Cut Eg j S0).pfr l = none := hn1
          rw [this] at hf0; cases hf0
        rw [hxF.2.2.2.2.2.2.1 l f0 hf0] at hf
        cases hf
        exact ⟨_, by rw [plantE_pfr_ne hnL]; exact hf0, Nat.le_refl _⟩
      · exact hR.pfr l f (.inl hLa) hf
      · exact hR.pfr l f (.inr hB) hf
    · show (Cut Eg j S0).box l = some B
      rcases hG with ⟨c1, f, h1', -⟩ | hLa | ⟨B0, hB0⟩
      · have := (hbi.2.2 l B hB).1
        rw [hxF.2.2.2.2.1 l c1 h1'] at this; cases this
      · obtain ⟨c1, h1', -⟩ := hLc l hLa
        have := (hbi.2.2 l B hB).1
        rw [hxF.2.2.2.2.1 l c1 h1'] at this; cases this
      · rw [hxF.2.2.2.2.2.2.2.2.1 l B0 hB0] at hB; rw [hB0, hB]
    · intro w1 hw1 a' g hv'
      obtain ⟨x, hx, e⟩ := List.getElem_of_mem hw1
      exact (hQ x w1 (by rw [← e]; exact List.getElem?_eq_getElem hx)).1 a' g hv'
  have hV2 := ValOf_transferS (InclS_cut_pub (EgP Eg (plantOf c Eg j a v w) (plantN c Eg j a v w) j c.mem.size) j S0)
    (noOR_of S [] hnS hrS) (ValOf_transferS (inclS_plantE X S0 j S0) (noOR_of S [] hnS hrS) hV1)
  exact ⟨jj * nWords us, S, V, m.loc.offset - jj * nWords us, w0, hseg0,
    ⟨hV2, fun us' hus' => by rw [hus] at hus'; cases hus'; exact hlV⟩, hw0, (hQ _ w0 hw0).2 rfl, Nat.add_sub_of_le hb'⟩

end

end W2New

#print axioms W2New.solo_mem
#print axioms W2New.wordOK_seg
#print axioms W2New.assembleSlot
#print axioms W2New.promWordNew_of
